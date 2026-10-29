use std::sync::atomic::Ordering;
use std::sync::{OnceLock, mpsc};
use std::thread;
use std::time::{Duration, Instant};

use log::{info, trace, warn};
use rug::integer::IsPrime;
use rug::{Complete, Integer};

use crate::block_sieve::{
    Blocking, SIEVE_CALLS, SIEVE_LOOP_NANOS, SIEVE_SETUP_NANOS, SieveScratch, SievedPrimes,
    sieve_over_factorbase_blocked, skipped_logs,
};
use crate::constants::NUM_SKIP_PRIMES;
use crate::factorbase::*;
use crate::large_primes::PartialStore;
use crate::linalg::*;
use crate::machine::SIEVE_BLOCK_SIZE;
use crate::multiplier::*;
use crate::number_theory::*;
use crate::polynomial_generator::Roots;
use crate::relation::Relation;
use crate::siqs_generator::*;
use crate::trial_division::{TrialDivision, divisor_logs, dlp_bound};
use std::ops::Range;

/// A full or partial relation sent from a sieving thread to the collecting
/// thread, with the index of the sieving thread.
type RelationMsg = (Relation, usize);

/// The slack of the sieve threshold, in units of log2(`large_prime_multiplier` ·
/// p_max), the size of the largest admissible large prime: 1.0 admits every partial
/// with one large prime and 2.0 every cofactor of two, independent of the factor base
/// size and the large-prime multiplier.
///
/// The default is 0.75 without the double large prime variation, measured as the
/// optimum at 202 bits. With it, the optimum grows with n, since larger cofactors make
/// partials more valuable: 0.72 measured at 251 bits, and 1.15, not yet tuned, at 300
/// bits, interpolated linearly in between and clamped outside. `SIQS_LP_SLACK`
/// overrides it, e.g. `SIQS_LP_SLACK=1.5`, for parameter sweeps.
fn lp_slack_multiplier(use_dlp: bool, n_bits: u32) -> f64 {
    static OVERRIDE: OnceLock<Option<f64>> = OnceLock::new();
    OVERRIDE
        .get_or_init(|| {
            std::env::var("SIQS_LP_SLACK")
                .ok()
                .and_then(|s| s.parse().ok())
        })
        .unwrap_or_else(|| default_lp_slack_multiplier(use_dlp, n_bits))
}

/// The measured defaults of [`lp_slack_multiplier`], without the env override.
fn default_lp_slack_multiplier(use_dlp: bool, n_bits: u32) -> f64 {
    if !use_dlp {
        return 0.75;
    }
    // linear in n's bit size between the measured anchors (251, 0.72) and (300, 1.15)
    let t = ((n_bits as f64 - 251.0) / (300.0 - 251.0)).clamp(0.0, 1.0);
    0.72 + t * (1.15 - 0.72)
}

/// The sieve threshold's large-prime slack in bits:
/// `lp_slack_multiplier · log2(large_prime_multiplier · p_max)`.
fn lp_slack_bits(use_dlp: bool, n_bits: u32, largest_log: u32, large_prime_multiplier: u32) -> u32 {
    let lp_bound_log = largest_log as f64 + (large_prime_multiplier as f64).log2();
    (lp_slack_multiplier(use_dlp, n_bits) * lp_bound_log) as u32
}

/// The value of the environment variable `name`, if it is set and parses: the
/// overrides of the sieve parameters, for parameter sweeps.
fn env_override<T: std::str::FromStr>(name: &str) -> Option<T> {
    std::env::var(name)
        .ok()
        .and_then(|value| value.parse().ok())
}

/// Whether `SIQS_GLOBAL_THRESHOLD` is set, which replaces the per-block thresholds by
/// one for the whole interval, from log2(kn/a), to compare the two.
fn use_global_threshold() -> bool {
    static GLOBAL: OnceLock<bool> = OnceLock::new();
    *GLOBAL.get_or_init(|| std::env::var("SIQS_GLOBAL_THRESHOLD").is_ok())
}

/// The inputs of the sieving threads, computed once from n and shared read-only.
struct SieveParams {
    // the multiplier k, and kn
    k: u32,
    kn: Integer,
    // the factor base (including the primes dividing k), and the rounded logs, the
    // inverses 1/p and the square roots of kn modulo its primes
    factorbase: Vec<u32>,
    logs: Vec<u8>,
    inverses: Vec<f32>,
    square_roots: Vec<u32>,
    // the factor base without the primes dividing k, from which a is built
    factorbase_without_k: Vec<u32>,
    sieve_interval_length: usize,
    large_prime_multiplier: u32,
    use_dlp: bool,
    // with the double large prime variation, the bound of a cofactor with two large
    // primes
    dlp_bound: Option<u64>,
    // large-prime slack in bits: how much non-smooth cofactor a candidate may keep
    lp_slack: u32,
    // the sum of the logs of the factor-base entries the sieve skips
    skipped_logs: u32,
    // the index of the first factor-base prime sieved: with the small prime
    // variation, the primes from NUM_SKIP_PRIMES up to SIQS_SPV_BOUND are left to
    // the second stage of the scan
    first_sieved: usize,
    // the bits by which the first stage of the scan lowers the thresholds then
    spv_allowance: u8,
    // the sieve's blocks and sub-blocks
    blocking: Blocking,
}

impl SieveParams {
    fn new(n: &Integer) -> Result<SieveParams, NumberTheoryError> {
        let k = compute_multiplier(n)?;
        info!("k = {k}");
        let kn: Integer = n.clone() * k;
        // the parameters for the size of kn, or from the environment
        let log2_kn = (kn.significant_bits() + 1) as usize;
        let (factorbase_size, sieve_interval_length, large_prime_multiplier) =
            compute_sieve_parameters(log2_kn);
        let factorbase_size = env_override("SIQS_FB_SIZE").unwrap_or(factorbase_size);
        let sieve_interval_length = env_override("SIQS_M").unwrap_or(sieve_interval_length);
        let large_prime_multiplier = env_override("SIQS_LP_MULT").unwrap_or(large_prime_multiplier);
        let block_size =
            env_override::<usize>("SIQS_BLOCK_KIB").map_or(SIEVE_BLOCK_SIZE, |kib| kib << 10);
        // trial division reduces positions as f32, which are exact below 2^24
        assert!(
            (1..1 << 23).contains(&sieve_interval_length),
            "sieve interval half-length {sieve_interval_length} not in [1, 2^23)"
        );
        assert!(
            block_size.is_power_of_two(),
            "block size {block_size} is not a power of two"
        );
        info!(
            "factor base size: {factorbase_size}, sieve interval: 2 * {sieve_interval_length}, \
             large-prime multiplier: {large_prime_multiplier}, block size: {} KiB",
            block_size >> 10
        );
        let factorbase_without_k = make_factorbase(&kn, factorbase_size);
        // add prime factors of multiplier k to factor base
        let prime_divisors_of_multiplier = SMALL_PRIMES
            .iter()
            .filter(|&&p| k.is_multiple_of(p))
            .copied();
        let mut factorbase = factorbase_without_k.clone();
        factorbase.extend(prime_divisors_of_multiplier);
        factorbase.sort_unstable();
        factorbase.dedup();
        let square_roots = square_roots_mod_factorbase(&kn, &factorbase);
        let logs = compute_logs(&factorbase);
        // for trial division's reduction of a position modulo p
        let inverses = compute_inverses(&factorbase);
        // double large prime variation: only worthwhile for larger n, where non-smooth
        // cofactors are big enough that admitting two large primes pays for the extra
        // primality test / Pollard-rho split and the larger partial-relation graph.
        let n_bits = n.significant_bits();
        let use_dlp = env_override::<u8>("SIQS_DLP").map_or(n_bits > 250, |dlp| dlp != 0);
        info!("double large prime: {use_dlp}");
        // trial division keeps a large prime in a u32, and decides that a cofactor
        // below the bound is prime because it is below the largest prime squared
        let largest_prime = *factorbase.last().unwrap() as u64;
        assert!(
            (1..largest_prime).contains(&(large_prime_multiplier as u64))
                && largest_prime * large_prime_multiplier as u64 <= u32::MAX as u64,
            "large-prime multiplier {large_prime_multiplier} out of range"
        );
        // the bound of a cofactor with two large primes, lp_bound^SIQS_DLP_EXP
        let dlp_exponent = env_override("SIQS_DLP_EXP").unwrap_or(2.0);
        let dlp_bound =
            use_dlp.then(|| dlp_bound(largest_prime * large_prime_multiplier as u64, dlp_exponent));
        if use_dlp {
            info!("double large prime cofactors up to lp_bound^{dlp_exponent}");
        }
        let lp_slack = lp_slack_bits(
            use_dlp,
            n_bits,
            *logs.last().unwrap() as u32,
            large_prime_multiplier,
        );
        info!(
            "lp slack multiplier: {:.2} ({lp_slack} bits)",
            lp_slack_multiplier(use_dlp, n_bits),
        );
        let skipped = skipped_logs(&logs);
        // the small prime variation: the sieve leaves the primes up to the bound to
        // the second stage of the scan, for factor bases large enough that it pays
        // (msieve: from 800 primes). Up to 256, as in YAFU, measured: 301 bits
        // +13.5% polynomials per second, 251 bits +4.4%; up to 512: +2% more at 301
        // bits, within noise.
        let default_spv_bound = if factorbase.len() >= 1000 { 256 } else { 0 };
        let spv_bound: u32 = env_override("SIQS_SPV_BOUND").unwrap_or(default_spv_bound);
        let first_sieved = factorbase
            .partition_point(|&p| p <= spv_bound)
            .max(NUM_SKIP_PRIMES);
        let spv_allowance = env_override("SIQS_SPV_ALLOWANCE").unwrap_or(30);
        if first_sieved > NUM_SKIP_PRIMES {
            info!(
                "small prime variation: {} primes up to {spv_bound} not sieved, \
                 first-stage thresholds {spv_allowance} bits lower",
                first_sieved - NUM_SKIP_PRIMES
            );
        }
        Ok(SieveParams {
            k,
            kn,
            factorbase,
            logs,
            inverses,
            square_roots,
            factorbase_without_k,
            sieve_interval_length,
            large_prime_multiplier,
            use_dlp,
            dlp_bound,
            lp_slack,
            skipped_logs: skipped,
            first_sieved,
            spv_allowance,
            blocking: Blocking::with_size(block_size),
        })
    }

    /// One polynomial generator per sieving thread.
    fn polynomial_generators(&self, num_threads: usize) -> Vec<SIQSPolynomialData<'_>> {
        new_polynomial_generators(
            &self.kn,
            self.sieve_interval_length as u64,
            num_threads,
            &self.factorbase,
            &self.square_roots,
            &self.factorbase_without_k,
        )
    }
}

/// One sieving thread: repeatedly sieve a polynomial, scan for candidates, factor
/// each over the factor base, and send the resulting (partial) relations to the
/// collecting thread.
fn run_sieve_producer(
    index_thread: usize,
    polynomial_generator: &mut SIQSPolynomialData,
    params: &SieveParams,
    sender: &mpsc::SyncSender<RelationMsg>,
) {
    let sieve_interval_length = params.sieve_interval_length;
    let total_len = 2 * sieve_interval_length;
    let kn_bits = params.kn.significant_bits();
    // scratch reused across polynomials by the blocked sieve
    let mut sieve_scratch = SieveScratch::default();
    // the sieve thresholds of a polynomial, one per scan window, reused across
    // polynomials
    let mut thresholds = Vec::new();
    let sieved = SievedPrimes {
        primes: &params.factorbase,
        logs: &params.logs,
        first: params.first_sieved,
    };
    let unsieved = Unsieved {
        indices: NUM_SKIP_PRIMES.min(params.first_sieved)..params.first_sieved,
        allowance: params.spv_allowance,
        factorbase: &params.factorbase,
        logs: &params.logs,
        inverses: &params.inverses,
    };
    // positions of a polynomial's candidates, reused across polynomials
    let mut candidates = Vec::new();
    let mut trial_division = TrialDivision::new(
        &params.factorbase,
        &params.inverses,
        sieve_interval_length,
        params.k,
        params.large_prime_multiplier,
        params.dlp_bound,
    );
    // Q(x) of a candidate, reused across candidates; cloned out only on a hit
    let mut v = Integer::new();

    // SIQS_PROFILE: thread 0 periodically prints a per-phase time breakdown
    let profile = std::env::var("SIQS_PROFILE").is_ok() && index_thread == 0;
    let mut prof_polys = 0u64;
    let mut prof_poly = Duration::ZERO;
    let mut prof_sieve = Duration::ZERO;
    let mut prof_scan = Duration::ZERO;
    // candidates passed to trial division, and the relations found among them
    // with zero, one or two large primes
    let mut prof_candidates = 0u64;
    let mut prof_relations = [0u64; 3];
    let prof_start = Instant::now();

    // A sieving thread never decides on its own to stop: it runs until the
    // collecting thread drops the relation receiver, and the next `send` below then
    // fails and breaks `'outer_loop`.
    'outer_loop: loop {
        let prof_t0 = Instant::now();
        let (polynomial, roots) = polynomial_generator.next_polynomial();
        trace!("thread {index_thread}: next polynomial");
        // Per-window thresholds: log2|Q(x)| is not flat over the interval. It is
        // ≈ log2(kn/a) over most of it but dips near the two roots of Q at
        // x ≈ ±M/√2, where smooth values are both likelier and cheaper. A single
        // threshold derived from the maximum misses those, so evaluate |Q| at each
        // scan window's midpoint and give every window its own
        // threshold = log2|Q(mid)| − large-prime slack − sum of skipped small logs.
        // f64 is exact enough here: its absolute error ~2^(bits−52) is far below
        // |Q(x)| at any integer x.
        let log2_kn_over_a = kn_bits.saturating_sub(polynomial.a.significant_bits());
        let a_f = polynomial.a.to_f64();
        let b_f = polynomial.b.to_f64();
        let c_f = polynomial.c.to_f64();
        thresholds.clear();
        for window_start in (0..total_len).step_by(SCAN_WINDOW) {
            let window_end = (window_start + SCAN_WINDOW).min(total_len);
            let x_mid = (window_start + window_end) as f64 / 2.0 - sieve_interval_length as f64;
            let q_mid = (a_f * x_mid + 2.0 * b_f) * x_mid + c_f;
            // fall back to the global bound if SIQS_GLOBAL_THRESHOLD is set, if f64
            // overflowed (kn beyond ~2^1020), or if the midpoint sits implausibly
            // close to a root of Q
            let q_bits = if !use_global_threshold() && q_mid.is_finite() && q_mid.abs() >= 2.0 {
                q_mid.abs().log2() as u32
            } else {
                log2_kn_over_a
            };
            thresholds.push(
                q_bits
                    .saturating_sub(params.lp_slack)
                    .saturating_sub(params.skipped_logs)
                    .clamp(1, u8::MAX as u32) as u8,
            );
        }
        let prof_t1 = Instant::now();
        // sieve block by block, and scan each block for candidates while it is in
        // the cache
        candidates.clear();
        let mut prof_scan_blocks = Duration::ZERO;
        sieve_over_factorbase_blocked(
            sieve_interval_length,
            sieved,
            roots,
            &mut sieve_scratch,
            params.blocking,
            |block_start, sums| {
                let prof_t = profile.then(Instant::now);
                scan_block(
                    block_start,
                    sums,
                    &thresholds,
                    &unsieved,
                    roots,
                    &mut candidates,
                );
                if let Some(t) = prof_t {
                    prof_scan_blocks += t.elapsed();
                }
            },
        );
        let prof_t2 = Instant::now();
        prof_candidates += candidates.len() as u64;
        trial_division.find_divisors(&candidates, roots);
        for (candidate, &i) in candidates.iter().enumerate() {
            let x = (i as i32) - (sieve_interval_length as i32);
            polynomial.evaluate(x, &mut v);
            if let Some((factors, large_primes)) = trial_division.factor(candidate, &v) {
                prof_relations[large_primes.count()] += 1;
                let relation = Relation {
                    u: polynomial.sqrt_mod(x, &params.kn),
                    v: v.clone(),
                    factors,
                    large_primes,
                };
                if sender.send((relation, index_thread)).is_err() {
                    break 'outer_loop;
                }
            }
        }
        if profile {
            prof_polys += 1;
            prof_poly += prof_t1 - prof_t0;
            // the scans of the blocks count as scan+factor
            prof_sieve += prof_t2 - prof_t1 - prof_scan_blocks;
            prof_scan += prof_t2.elapsed() + prof_scan_blocks;
            if prof_polys.is_multiple_of(2000) {
                // sieve-internal split, averaged across all threads' calls
                let calls = SIEVE_CALLS.load(Ordering::Relaxed).max(1);
                let setup = SIEVE_SETUP_NANOS.load(Ordering::Relaxed) / calls / 1000;
                let bloop = SIEVE_LOOP_NANOS.load(Ordering::Relaxed) / calls / 1000;
                let polys = prof_polys as f64;
                // the throughput of all sieving threads together
                let rate = calls as f64 / prof_start.elapsed().as_secs_f64();
                eprintln!(
                    "[profile] {prof_polys} polys | per poly: poly {:.0}us \
                     sieve {:.0}us (setup {setup}us loop {bloop}us) scan+factor {:.0}us | \
                     candidates {:.2} relations: full {:.4} 1LP {:.4} 2LP {:.4} | \
                     {rate:.0} polys/s on all threads",
                    prof_poly.as_micros() as f64 / polys,
                    prof_sieve.as_micros() as f64 / polys,
                    prof_scan.as_micros() as f64 / polys,
                    prof_candidates as f64 / polys,
                    prof_relations[0] as f64 / polys,
                    prof_relations[1] as f64 / polys,
                    prof_relations[2] as f64 / polys,
                );
            }
        }
    }
}

/// The scan windows, each with its own threshold.
const SCAN_WINDOW: usize = 16384;

/// The primes the sieve leaves to the second stage of the scan, with the small prime
/// variation, and what the second stage needs to find which of them divide Q at a
/// position.
struct Unsieved<'a> {
    // the indices of the primes
    indices: Range<usize>,
    // the bits by which the first stage lowers the thresholds
    allowance: u8,
    factorbase: &'a [u32],
    logs: &'a [u8],
    inverses: &'a [f32],
}

/// Appends to `candidates` the positions of a sieved block, from `block_start` on,
/// whose sums reach the threshold of their window of [`SCAN_WINDOW`] positions,
/// `thresholds[w]` for window w of the interval. With primes left `unsieved`, the
/// first stage scans with thresholds lowered by the allowance, and the second keeps
/// a position only if its sum plus the logs of the unsieved primes that divide Q
/// there reaches the threshold: the positions that sieving all primes would give,
/// unless the unsieved primes add more than the allowance.
fn scan_block(
    block_start: usize,
    sums: &[u8],
    thresholds: &[u8],
    unsieved: &Unsieved,
    roots: &Roots,
    candidates: &mut Vec<u32>,
) {
    let second_stage = !unsieved.indices.is_empty();
    // the windows overlapping the block, cut at its ends
    let block_end = block_start + sums.len();
    let mut start = block_start;
    while start < block_end {
        let window = start / SCAN_WINDOW;
        let end = ((window + 1) * SCAN_WINDOW).min(block_end);
        let threshold = thresholds[window];
        let first_new = candidates.len();
        // with a lower threshold of 0, every position is a candidate of the first
        // stage, also one that no sieved prime divides
        let first_stage = if second_stage {
            threshold.saturating_sub(unsieved.allowance)
        } else {
            threshold
        };
        find_candidates(
            &sums[start - block_start..end - block_start],
            first_stage,
            start,
            candidates,
        );
        if second_stage {
            let mut kept = first_new;
            for k in first_new..candidates.len() {
                let pos = candidates[k];
                let sum = sums[pos as usize - block_start] as u32
                    + divisor_logs(
                        pos,
                        unsieved.indices.clone(),
                        unsieved.factorbase,
                        roots,
                        unsieved.inverses,
                        unsieved.logs,
                    );
                if sum >= threshold as u32 {
                    candidates[kept] = pos;
                    kept += 1;
                }
            }
            candidates.truncate(kept);
        }
        start = end;
    }
}

/// Appends `offset + i` to `candidates` for every position `i` whose sieve value
/// `logs[i]` reaches `threshold`, in increasing order.
#[cfg(target_feature = "avx2")]
fn find_candidates(logs: &[u8], threshold: u8, offset: usize, candidates: &mut Vec<u32>) {
    use std::arch::x86_64::*;
    let (chunks, tail) = logs.as_chunks::<32>();
    // SAFETY: AVX2 is enabled at compile time, and each load reads the 32 bytes of
    // its chunk
    unsafe {
        let thresholds = _mm256_set1_epi8(threshold as i8);
        for (c, chunk) in chunks.iter().enumerate() {
            let chunk = _mm256_loadu_si256(chunk.as_ptr().cast());
            // unsigned: chunk >= threshold  iff  max(chunk, threshold) == chunk
            let reached = _mm256_cmpeq_epi8(_mm256_max_epu8(chunk, thresholds), chunk);
            let mut mask = _mm256_movemask_epi8(reached) as u32;
            while mask != 0 {
                candidates.push((offset + 32 * c + mask.trailing_zeros() as usize) as u32);
                mask &= mask - 1;
            }
        }
    }
    find_candidates_scalar(
        tail,
        threshold,
        offset + logs.len() - tail.len(),
        candidates,
    );
}

#[cfg(not(target_feature = "avx2"))]
fn find_candidates(logs: &[u8], threshold: u8, offset: usize, candidates: &mut Vec<u32>) {
    find_candidates_scalar(logs, threshold, offset, candidates);
}

/// [`find_candidates`] without SIMD: for builds without AVX2, and for the tail.
fn find_candidates_scalar(logs: &[u8], threshold: u8, offset: usize, candidates: &mut Vec<u32>) {
    for (i, &log) in logs.iter().enumerate() {
        if log >= threshold {
            candidates.push((offset + i) as u32);
        }
    }
}

/// Relations that may wait in the channel before the sieving threads block: enough
/// to absorb bursts, few enough to bound the memory if the collecting thread falls
/// behind.
const CHANNEL_CAPACITY: usize = 1024;

/// Factors n with the self-initializing quadratic sieve. Returns a nontrivial factor,
/// or `None` if no dependency gives one.
///
/// Inputs that need no sieve come first: a prime factor below 1000, or the root m of
/// a perfect power n = m^k, is returned right away, and primes and n < 2 give
/// [`NumberTheoryError::NotComposite`].
///
/// `num_threads` threads (at least one) sieve and send their relations to the
/// calling thread, which combines the partial ones and collects the full ones until
/// there are 192 more than primes appearing in them. Then Block Lanczos
/// ([`SparseRelations::dependencies_lanczos`]) finds dependencies, on
/// `num_threads + 1` threads, and each is tried until one gives a factor. The
/// progress is logged with the `log` crate.
pub fn quadratic_sieve_lanczos(
    n: &Integer,
    num_threads: usize,
) -> Result<Option<Integer>, NumberTheoryError> {
    // fixed seed for the randomized starting block, for reproducible runs
    const LANCZOS_SEED: u64 = 0x5161_7A9F_2C3D_4E5F;

    if let Some(factor) = factor_without_sieve(n)? {
        return Ok(Some(factor));
    }
    let num_threads = num_threads.max(1);
    let params = SieveParams::new(n)?;
    let mut polynomial_generators = params.polynomial_generators(num_threads);
    let relations = thread::scope(|s| {
        let (sender, receiver) = mpsc::sync_channel(CHANNEL_CAPACITY);
        for (index_thread, polynomial_generator) in polynomial_generators.iter_mut().enumerate() {
            let (params, sender) = (&params, sender.clone());
            s.spawn(move || {
                run_sieve_producer(index_thread, polynomial_generator, params, &sender)
            });
        }
        // The sieving threads hold the only senders now. They run until the receiver
        // is dropped when collect_relations returns: then their next send fails.
        drop(sender);
        collect_relations(receiver, &params)
    });
    let lanczos_start = Instant::now();
    let dependencies = relations.dependencies_lanczos(LANCZOS_SEED, num_threads + 1);
    info!(
        "Block Lanczos on {} threads returned {} dependencies in {:.2?}",
        num_threads + 1,
        dependencies.len(),
        lanczos_start.elapsed()
    );
    let square_root_start = Instant::now();
    let mut tried = 0;
    let factor = dependencies.iter().find_map(|dependency| {
        tried += 1;
        relations.find_factor(dependency, n)
    });
    match &factor {
        Some(factor) => info!(
            "found factor {factor} with dependency {tried} in {:.2?}",
            square_root_start.elapsed()
        ),
        None => warn!("no factor found among the dependencies"),
    }
    Ok(factor)
}

/// A factor of n found without the sieve: a prime factor below 1000, or the root m
/// of a perfect power n = m^k. An error if n is prime or less than 2.
fn factor_without_sieve(n: &Integer) -> Result<Option<Integer>, NumberTheoryError> {
    if *n < 2 {
        return Err(NumberTheoryError::NotComposite(n.clone()));
    }
    for p in SMALL_PRIMES {
        if n.is_divisible_u(p) {
            return if *n == p {
                Err(NumberTheoryError::NotComposite(n.clone()))
            } else {
                Ok(Some(Integer::from(p)))
            };
        }
    }
    // the sieve finds only trivial factors of a prime power
    if n.is_perfect_power() {
        return Ok((2..).find_map(|k| {
            let (root, remainder) = n.root_rem_ref(k).complete();
            (remainder == 0).then_some(root)
        }));
    }
    if n.is_probably_prime(30) != IsPrime::No {
        return Err(NumberTheoryError::NotComposite(n.clone()));
    }
    Ok(None)
}

/// Receives the relations of the sieving threads and combines the partial ones,
/// until there are `RELATION_SURPLUS` more full relations than primes appearing in
/// them: then the kernel, hence the number of dependencies, is at least that big.
/// Relations with equal parity vectors are kept: together they form a dependency.
fn collect_relations(
    receiver: mpsc::Receiver<RelationMsg>,
    params: &SieveParams,
) -> SparseRelations {
    // Kept comfortably above the 64-wide Block Lanczos block so the kernel dimension
    // never sits exactly on the block boundary (the degenerate case where a single
    // block can fail to capture it).
    const RELATION_SURPLUS: usize = 192;

    let factorbase_size = params.factorbase.len();
    // combines partial relations into full ones: a single-prime hash map without the
    // double large prime variation, the cycle graph with it
    let mut partial_relations = PartialStore::new(params.use_dlp);
    // full relations collected sparsely for the batch linear algebra
    let mut sparse = SparseRelations::new(factorbase_size);
    // which factor-base primes have actually appeared: the matrix only needs a
    // surplus over these, not over the full factor base (for small n most large
    // primes never divide any Q(x)).
    let mut appeared = vec![false; factorbase_size];
    let mut appeared_count = 0usize;

    // progress: report every 10% of the (estimated) max relations needed. The actual
    // target is appeared_count + RELATION_SURPLUS; appeared_count is bounded by the
    // factor base, so this is the upper bound.
    let max_relations = factorbase_size + RELATION_SURPLUS;
    let progress_step = (max_relations / 10).max(1);
    let collection_start = Instant::now();

    while sparse.len() < appeared_count + RELATION_SURPLUS {
        // The sieving threads never exit on their own, so a closed channel can only
        // mean that they panicked: nothing more will arrive.
        let Ok((relation, index_thread)) = receiver.recv() else {
            break;
        };
        // full relations go straight to the matrix; partials (one or two large
        // primes) are routed through the partial-relation graph, which yields a full
        // relation only when it closes a cycle.
        let relation = if relation.is_full() {
            trace!("thread {index_thread}: full relation");
            relation
        } else if let Some(mut full) = partial_relations.add(relation) {
            trace!("thread {index_thread}: partial relation, completing a full one");
            // the product of the partials' u matters only modulo kn
            full.u %= &params.kn;
            full
        } else {
            trace!("thread {index_thread}: partial relation");
            continue;
        };
        for &c in &relation.factors {
            if !appeared[c as usize] {
                appeared[c as usize] = true;
                appeared_count += 1;
            }
        }
        sparse.push_sparse(relation.factors, (relation.u, relation.v));
        if sparse.len().is_multiple_of(progress_step) {
            info!(
                "{} relations ({}% of at most {max_relations}) after {:.2?}",
                sparse.len(),
                10 * (sparse.len() / progress_step),
                collection_start.elapsed()
            );
        }
    }
    info!(
        "collected {} relations ({appeared_count} primes appearing) in {:.2?}",
        sparse.len(),
        collection_start.elapsed()
    );
    sparse
}

#[cfg(test)]
mod tests {
    use super::*;

    // the signature of find_candidates
    type Scan = fn(&[u8], u8, usize, &mut Vec<u32>);

    // Both scans find exactly the positions at or above the threshold, also for
    // thresholds of 128 and more, where a signed byte comparison would fail, and in
    // a tail shorter than a SIMD vector.
    #[test]
    fn scans_find_the_positions_reaching_the_threshold() {
        let mut seed = 0x9E37_79B9_7F4A_7C15u64;
        let logs: Vec<u8> = (0..1000)
            .map(|_| {
                seed = seed
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                (seed >> 56) as u8
            })
            .collect();
        let offset = 12345;
        let scans: [Scan; 2] = [find_candidates, find_candidates_scalar];
        for threshold in [0, 1, 50, 127, 128, 129, 200, 255] {
            let want: Vec<u32> = (0..logs.len())
                .filter(|&i| logs[i] >= threshold)
                .map(|i| (offset + i) as u32)
                .collect();
            for (s, scan) in scans.iter().enumerate() {
                let mut got = vec![0];
                scan(&logs, threshold, offset, &mut got);
                assert_eq!(got[0], 0, "scan {s} must append");
                assert_eq!(got[1..], want, "scan {s}, threshold {threshold}");
            }
        }
    }

    // With the small prime variation and an allowance that lets the first stage
    // pass every position, the scan finds exactly the candidates of sieving all
    // primes; with a realistic allowance, a subset.
    #[test]
    fn small_prime_variation_keeps_the_candidates() {
        use crate::block_sieve::{Blocking, SieveScratch, SievedPrimes};
        let n: Integer = "6427752177035961102167848371107669985402627402189138248671463"
            .parse()
            .unwrap();
        let factorbase = crate::factorbase::make_factorbase(&n, 2000);
        let n_roots = crate::factorbase::square_roots_mod_factorbase(&n, &factorbase);
        let logs = crate::factorbase::compute_logs(&factorbase);
        let inverses = crate::factorbase::compute_inverses(&factorbase);
        let m = 65536usize;
        let mut generators =
            new_polynomial_generators(&n, m as u64, 1, &factorbase, &n_roots, &factorbase);
        let first_sieved = factorbase.partition_point(|&p| p <= 256);
        assert!(first_sieved > NUM_SKIP_PRIMES + 20);
        let mut scratch = SieveScratch::default();
        let mut candidates = |roots: &Roots, first: usize, allowance: u8, threshold: u8| {
            let mut candidates = Vec::new();
            let thresholds = vec![threshold; (2 * m).div_ceil(SCAN_WINDOW)];
            let unsieved = Unsieved {
                indices: NUM_SKIP_PRIMES..first,
                allowance,
                factorbase: &factorbase,
                logs: &logs,
                inverses: &inverses,
            };
            let sieved = SievedPrimes {
                primes: &factorbase,
                logs: &logs,
                first,
            };
            sieve_over_factorbase_blocked(
                m,
                sieved,
                roots,
                &mut scratch,
                Blocking::with_size(1 << 15),
                |block_start, sums| {
                    scan_block(
                        block_start,
                        sums,
                        &thresholds,
                        &unsieved,
                        roots,
                        &mut candidates,
                    )
                },
            );
            candidates
        };
        let mut found = 0;
        for _ in 0..3 {
            let (_, roots) = generators[0].next_polynomial();
            for threshold in [40, 55, 70] {
                let all = candidates(roots, NUM_SKIP_PRIMES, 0, threshold);
                found += all.len();
                assert_eq!(candidates(roots, first_sieved, 255, threshold), all);
                let some = candidates(roots, first_sieved, 20, threshold);
                assert!(some.iter().all(|pos| all.contains(pos)));
            }
        }
        assert!(found > 100, "only {found} candidates");
    }

    #[test]
    fn lp_slack_defaults() {
        let close = |x: f64, y: f64| (x - y).abs() < 1e-12;
        // without the double large prime variation: constant
        for n_bits in [64, 202, 250, 301] {
            assert!(close(default_lp_slack_multiplier(false, n_bits), 0.75));
        }
        // with it: linear between (251, 0.72) and (300, 1.15), clamped outside
        assert!(close(default_lp_slack_multiplier(true, 251), 0.72));
        assert!(close(default_lp_slack_multiplier(true, 300), 1.15));
        assert!(close(
            default_lp_slack_multiplier(true, 270),
            0.72 + 0.43 * 19.0 / 49.0
        ));
        assert!(close(default_lp_slack_multiplier(true, 200), 0.72));
        assert!(close(default_lp_slack_multiplier(true, 400), 1.15));
    }
}
