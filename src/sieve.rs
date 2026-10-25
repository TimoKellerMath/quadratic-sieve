use std::io::{self, Write};
use std::sync::atomic::Ordering;
use std::sync::{OnceLock, mpsc};
use std::thread;
use std::time::{Duration, Instant};

use rug::Integer;

use crate::block_sieve::{
    SIEVE_CALLS, SIEVE_LOOP_NANOS, SIEVE_SETUP_NANOS, SieveScratch, sieve_over_factorbase_blocked,
};
use crate::debug_print;
use crate::factorbase::*;
use crate::format_color::format_color;
use crate::large_primes::PartialStore;
use crate::linalg::*;
use crate::multiplier::*;
use crate::number_theory::*;
use crate::relation::Relation;
use crate::siqs_generator::*;
use crate::trial_division::TrialDivision;

/// A full or partial relation sent from a sieving thread to the collecting
/// thread, with the index of the sieving thread.
type RelationMsg = (Relation, usize);

/// Slack multiplier for the sieve threshold, in units of the large-prime bound's
/// log — `log2(large_prime_multiplier · p_max)`, the size of the biggest admissible
/// large prime. So 1.0 admits every single-large-prime partial and 2.0 every
/// double-large-prime cofactor, independent of the factor-base size or the
/// large-prime multiplier in use.
///
/// Defaults are measured optima: 0.75 without the double large prime variation
/// (measured at 202 bits). With it, the optimum grows with the size of N (larger
/// non-smooth cofactors make partials more valuable): ~0.72 measured at 251 bits,
/// ~1.15 at ~300 bits (the old-default equivalent; finer sweep pending), linearly
/// interpolated in between and clamped outside. Overridable via the
/// `SIQS_LP_SLACK` env var (e.g. `SIQS_LP_SLACK=1.5`) for parameter sweeps.
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

/// A/B switch: set `SIQS_GLOBAL_THRESHOLD` to disable the per-block thresholds and
/// use the single global `log2(kn/a)` bound for the whole interval (the pre-per-block
/// behavior), for benchmarking the two strategies against each other.
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
    // Barrett reciprocals and the square roots of kn modulo its primes
    factorbase: Vec<u32>,
    logs: Vec<u8>,
    reciprocals: Vec<u64>,
    square_roots: Vec<u32>,
    // the factor base without the primes dividing k, from which a is built
    factorbase_without_k: Vec<u32>,
    sieve_interval_length: usize,
    large_prime_multiplier: u32,
    use_dlp: bool,
    // large-prime slack in bits: how much non-smooth cofactor a candidate may keep
    lp_slack: u32,
}

impl SieveParams {
    fn new(n: &Integer) -> Result<SieveParams, NumberTheoryError> {
        let k = compute_multiplier(n)?;
        println!("k = {k}");
        let kn: Integer = n.clone() * k;
        // heuristic value for the factor base
        let log2_kn = (kn.significant_bits() + 1) as usize;
        let (factorbase_size, sieve_interval_length, large_prime_multiplier) =
            compute_sieve_parameters(log2_kn);
        println!("factor base size: {factorbase_size}");
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
        // Barrett reciprocals for the resieve step's per-prime `x mod p`.
        let reciprocals = compute_reciprocals(&factorbase);
        // double large prime variation: only worthwhile for larger N, where non-smooth
        // cofactors are big enough that admitting two large primes pays for the extra
        // primality test / Pollard-rho split and the larger partial-relation graph.
        let n_bits = n.significant_bits();
        let use_dlp = n_bits > 250;
        println!("double large prime: {use_dlp}");
        let lp_slack = lp_slack_bits(
            use_dlp,
            n_bits,
            *logs.last().unwrap() as u32,
            large_prime_multiplier,
        );
        println!(
            "lp slack multiplier: {:.2} ({lp_slack} bits)",
            lp_slack_multiplier(use_dlp, n_bits),
        );
        Ok(SieveParams {
            k,
            kn,
            factorbase,
            logs,
            reciprocals,
            square_roots,
            factorbase_without_k,
            sieve_interval_length,
            large_prime_multiplier,
            use_dlp,
            lp_slack,
        })
    }

    // one polynomial generator per sieving thread
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
    let kn_bits = params.kn.significant_bits();
    let mut logs_for_polynomial = vec![0u8; 2 * sieve_interval_length];
    // scratch reused across polynomials by the blocked sieve
    let mut sieve_scratch = SieveScratch::default();
    // positions of a polynomial's candidates, reused across polynomials
    let mut candidates = Vec::new();
    let mut trial_division = TrialDivision::new(
        &params.factorbase,
        &params.reciprocals,
        params.k,
        params.large_prime_multiplier,
        params.use_dlp,
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

    // A sieving thread never decides on its own to stop: it runs until the
    // collecting thread drops the relation receiver, and the next `send` below then
    // fails and breaks `'outer_loop`.
    'outer_loop: loop {
        let prof_t0 = Instant::now();
        let (polynomial, roots) = polynomial_generator.next_polynomial();
        debug_print!("{}", format_color("?", index_thread));
        const BLOCK_SIZE: usize = 2 * 65536;
        let prof_t1 = Instant::now();
        let sum_small_logs = sieve_over_factorbase_blocked(
            sieve_interval_length,
            &params.factorbase,
            roots,
            &params.logs,
            &mut logs_for_polynomial,
            &mut sieve_scratch,
            BLOCK_SIZE,
        );
        // Per-block thresholds: log2|Q(x)| is not flat over the interval — it is
        // ≈ log2(kn/a) over most of it but dips near the two roots of Q at
        // x ≈ ±M/√2, where smooth values are both likelier and cheaper. A single
        // threshold derived from the maximum misses those, so evaluate |Q| at each
        // scan block's midpoint and give every block its own
        // threshold = log2|Q(mid)| − large-prime slack − sum of skipped small logs.
        // f64 is exact enough here: its absolute error ~2^(bits−52) is far below
        // |Q(x)| at any integer x.
        let log2_kn_over_a = kn_bits.saturating_sub(polynomial.a.significant_bits());
        let a_f = polynomial.a.to_f64();
        let b_f = polynomial.b.to_f64();
        let c_f = polynomial.c.to_f64();
        let prof_t2 = Instant::now();
        let total = logs_for_polynomial.len();
        const SCAN_BLOCK: usize = 16384;
        candidates.clear();
        for block_start in (0..total).step_by(SCAN_BLOCK) {
            let block_end = (block_start + SCAN_BLOCK).min(total);
            let x_mid = (block_start + block_end) as f64 / 2.0 - sieve_interval_length as f64;
            let q_mid = (a_f * x_mid + 2.0 * b_f) * x_mid + c_f;
            // fall back to the global bound if the A/B switch disables per-block
            // thresholds, if f64 overflowed (kn beyond ~2^1020), or the midpoint
            // sits implausibly close to a root of Q
            let q_bits = if !use_global_threshold() && q_mid.is_finite() && q_mid.abs() >= 2.0 {
                q_mid.abs().log2() as u32
            } else {
                log2_kn_over_a
            };
            let threshold: u8 = q_bits
                .saturating_sub(params.lp_slack)
                .saturating_sub(sum_small_logs)
                .clamp(1, u8::MAX as u32) as u8;
            find_candidates(
                &logs_for_polynomial[block_start..block_end],
                threshold,
                block_start,
                &mut candidates,
            );
        }
        prof_candidates += candidates.len() as u64;
        for &i in &candidates {
            let x = (i as i32) - (sieve_interval_length as i32);
            polynomial.evaluate(x, &mut v);
            if let Some((factors, large_primes)) = trial_division.factor(x, &v, roots) {
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
            prof_sieve += prof_t2 - prof_t1;
            prof_scan += prof_t2.elapsed();
            if prof_polys.is_multiple_of(2000) {
                // sieve-internal split, averaged across all threads' calls
                let calls = SIEVE_CALLS.load(Ordering::Relaxed).max(1);
                let setup = SIEVE_SETUP_NANOS.load(Ordering::Relaxed) / calls / 1000;
                let bloop = SIEVE_LOOP_NANOS.load(Ordering::Relaxed) / calls / 1000;
                let polys = prof_polys as f64;
                eprintln!(
                    "[profile] {prof_polys} polys | per poly: poly {:.0}us \
                     sieve {:.0}us (setup {setup}us loop {bloop}us) scan+factor {:.0}us | \
                     candidates {:.2} relations: full {:.4} 1LP {:.4} 2LP {:.4}",
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

/// Appends `offset + i` to `candidates` for every position `i` whose sieve value
/// `logs[i]` reaches `threshold`, in increasing order.
#[cfg(target_feature = "avx2")]
fn find_candidates(logs: &[u8], threshold: u8, offset: usize, candidates: &mut Vec<usize>) {
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
                candidates.push(offset + 32 * c + mask.trailing_zeros() as usize);
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
fn find_candidates(logs: &[u8], threshold: u8, offset: usize, candidates: &mut Vec<usize>) {
    find_candidates_scalar(logs, threshold, offset, candidates);
}

/// [`find_candidates`] without SIMD: for builds without AVX2, and for the tail.
fn find_candidates_scalar(logs: &[u8], threshold: u8, offset: usize, candidates: &mut Vec<usize>) {
    for (i, &log) in logs.iter().enumerate() {
        if log >= threshold {
            candidates.push(offset + i);
        }
    }
}

/// Relations that may wait in the channel before the sieving threads block: enough
/// to absorb bursts, few enough to bound the memory if the collecting thread falls
/// behind.
const CHANNEL_CAPACITY: usize = 1024;

/// Factors n with the self-initializing quadratic sieve. Returns a factor, or `None`
/// if no dependency gives one.
///
/// `num_threads` threads sieve and send their relations to the calling thread,
/// which combines the partial ones and collects the full ones until there are 192
/// more than primes appearing in them. Then Block Lanczos
/// ([`SparseRelations::dependencies_lanczos`]) finds dependencies, on
/// `num_threads + 1` threads, and each is tried until one gives a factor.
pub fn quadratic_sieve_lanczos(
    n: &Integer,
    num_threads: usize,
) -> Result<Option<Integer>, NumberTheoryError> {
    // fixed seed for the randomized starting block, for reproducible runs
    const LANCZOS_SEED: u64 = 0x5161_7A9F_2C3D_4E5F;

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
    println!(
        "Block Lanczos on {} threads returned {} dependencies in {:.2?}",
        num_threads + 1,
        dependencies.len(),
        lanczos_start.elapsed()
    );
    let factor = dependencies
        .iter()
        .find_map(|dependency| relations.find_factor(dependency, n));
    match &factor {
        Some(factor) => println!("found factor: {factor}"),
        None => println!("no factor found among the dependencies"),
    }
    io::stdout().flush().unwrap();
    Ok(factor)
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
    // surplus over *these*, not over the full factor base (for small N most large
    // primes never divide any Q(x)).
    let mut appeared = vec![false; factorbase_size];
    let mut appeared_count = 0usize;

    // progress: report every 10% of the (estimated) max relations needed. The actual
    // target is appeared_count + RELATION_SURPLUS; appeared_count is bounded by the
    // factor base, so this is the upper bound.
    let max_relations = factorbase_size + RELATION_SURPLUS;
    let progress_step = (max_relations / 10).max(1);
    let collection_start = Instant::now();
    // time each 10% step so slow ones can be flagged
    let mut last_step_time = collection_start;

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
            debug_print!("{}", format_color("+", index_thread));
            relation
        } else if let Some(full) = partial_relations.add(relation) {
            debug_print!("{}", format_color(":", index_thread));
            full
        } else {
            debug_print!("{}", format_color(".", index_thread));
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
            let step = sparse.len() / progress_step;
            let elapsed = last_step_time.elapsed();
            print!("({step}: {} ms)", elapsed.as_millis());
            io::stdout().flush().unwrap();
            last_step_time = Instant::now();
        }
    }
    println!(
        "\ncollected {} relations ({appeared_count} primes appearing) in {:.2?}",
        sparse.len(),
        collection_start.elapsed()
    );
    sparse
}

#[cfg(test)]
mod tests {
    use super::*;

    // the signature of find_candidates
    type Scan = fn(&[u8], u8, usize, &mut Vec<usize>);

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
            let want: Vec<usize> = (0..logs.len())
                .filter(|&i| logs[i] >= threshold)
                .map(|i| offset + i)
                .collect();
            for (s, scan) in scans.iter().enumerate() {
                let mut got = vec![0];
                scan(&logs, threshold, offset, &mut got);
                assert_eq!(got[0], 0, "scan {s} must append");
                assert_eq!(got[1..], want, "scan {s}, threshold {threshold}");
            }
        }
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
