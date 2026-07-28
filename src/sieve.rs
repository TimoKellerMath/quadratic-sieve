use std::io::{self, Write};
use std::sync::atomic::Ordering;
use std::sync::{Arc, Mutex, OnceLock, mpsc};
use std::time::{Duration, Instant};

use rug::Integer;

use fixedbitset::FixedBitSet;
use rustc_hash::FxHashSet;

// debug_print! expands to nothing in release, leaving format_color unused there.
#[allow(unused_imports)]
use crate::debug_print;
use crate::factorbase::*;
#[allow(unused_imports)]
use crate::format_color::format_color;
use crate::linalg::*;
use crate::multiplier::*;
use crate::number_theory::*;
use crate::relations::*;
use crate::siqs_generator::*;

/// A (partial) relation sent from a producer (sieving) thread to the consumer:
/// `(u, v, relation, p, q, index_thread)`, where `p`/`q` are the large primes
/// (1 = none) and `relation` is the GF(2) exponent vector over the factor base.
type RelationMsg = (Integer, Integer, FixedBitSet, u32, u32, usize);

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
    if let Some(m) = OVERRIDE.get_or_init(|| {
        std::env::var("SIQS_LP_SLACK")
            .ok()
            .and_then(|s| s.parse().ok())
    }) {
        return *m;
    }
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

/// One producer thread: repeatedly sieve a polynomial, scan for survivors, factor
/// each over the factor base, and send the resulting (partial) relations to the
/// consumer. Shared by [`quadratic_sieve_multithreaded`] and
/// [`quadratic_sieve_lanczos`] so the sieving hot path has a single definition.
#[allow(clippy::too_many_arguments)]
fn run_sieve_producer(
    index_thread: usize,
    polynomial_generator: &mut SIQSPolynomialData,
    logs: &[u8],
    factorbase: &[u32],
    reciprocals: &[u64],
    kn: &Integer,
    sieve_interval_length: usize,
    kn_bits: u32,
    k: u32,
    large_prime_multiplier: u32,
    use_dlp: bool,
    // large-prime slack in bits: how much non-smooth cofactor a candidate may keep.
    // Computed once by the entry function via lp_slack_bits (it depends on n's size).
    lp_slack: u32,
    sender: &mpsc::Sender<RelationMsg>,
) {
    let mut logs_for_polynomial = vec![0u8; 2 * sieve_interval_length];
    // scratch reused across polynomials by the blocked sieve
    let mut next_pos: Vec<usize> = Vec::with_capacity(2 * factorbase.len());
    // per-block buckets of large-prime hits (packed position|log), reused across
    // polynomials
    let mut buckets: Vec<Vec<u32>> = Vec::new();
    // scratch integer reused by factor_over_factorbase per candidate
    let mut factor_scratch = Integer::new();
    // scratch bitset reused across candidates (cloned out only on a hit)
    let mut relation_scratch = FixedBitSet::with_capacity(factorbase.len());
    // scratch (u, v) reused across candidates; cloned out only on a hit
    let mut u_scratch = Integer::new();
    let mut v_scratch = Integer::new();

    // SIQS_PROFILE: thread 0 periodically prints a per-phase time breakdown
    let profile = std::env::var("SIQS_PROFILE").is_ok() && index_thread == 0;
    let mut prof_polys = 0u64;
    let mut prof_poly = Duration::ZERO;
    let mut prof_sieve = Duration::ZERO;
    let mut prof_scan = Duration::ZERO;

    // Producers run forever: a producer never decides on its own to stop. The
    // consumer is the sole authority that terminates them — it drops the relation
    // receiver, and the next `send` below then fails and breaks `'outer_loop`.
    'outer_loop: loop {
        let prof_t0 = Instant::now();
        let (polynomial, roots) = polynomial_generator.next_polynomial();
        debug_print!("{}", format_color("?", index_thread));
        const BLOCK_SIZE: usize = 2 * 65536;
        let prof_t1 = Instant::now();
        let sum_small_logs = sieve_over_factorbase_blocked(
            sieve_interval_length,
            factorbase,
            roots,
            reciprocals,
            logs,
            &mut logs_for_polynomial,
            &mut next_pos,
            &mut buckets,
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
        let mut block_start = 0usize;
        while block_start < total {
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
                .saturating_sub(lp_slack)
                .saturating_sub(sum_small_logs)
                .clamp(1, u8::MAX as u32) as u8;
            let mut i = block_start;
            #[cfg(target_feature = "avx2")]
            unsafe {
                use std::arch::x86_64::*;
                let thr_vec = _mm256_set1_epi8(threshold as i8);
                let ptr = logs_for_polynomial.as_ptr();
                while i + 32 <= block_end {
                    let chunk = _mm256_loadu_si256(ptr.add(i) as *const __m256i);
                    // unsigned: chunk >= threshold  iff  max(chunk, thr) == chunk
                    let maxv = _mm256_max_epu8(chunk, thr_vec);
                    let eq = _mm256_cmpeq_epi8(maxv, chunk);
                    let mask = _mm256_movemask_epi8(eq) as u32;
                    if mask != 0 {
                        let mut m = mask;
                        while m != 0 {
                            let j = m.trailing_zeros() as usize;
                            m &= m - 1;
                            let idx = i + j;
                            let x = (idx as i32) - (sieve_interval_length as i32);
                            evaluate_polynomial_at(
                                x, &polynomial, kn, &mut u_scratch, &mut v_scratch,
                            );
                            if let Some((relation, p, q)) = factor_over_factorbase(
                                x,
                                &v_scratch,
                                factorbase,
                                roots,
                                reciprocals,
                                k,
                                large_prime_multiplier,
                                use_dlp,
                                &mut factor_scratch,
                                &mut relation_scratch,
                            ) {
                                if sender
                                    .send((
                                        u_scratch.clone(),
                                        v_scratch.clone(),
                                        relation,
                                        p,
                                        q,
                                        index_thread,
                                    ))
                                    .is_err()
                                {
                                    break 'outer_loop;
                                }
                            }
                        }
                    }
                    i += 32;
                }
            }
            while i < block_end {
                let log = logs_for_polynomial[i];
                if log >= threshold {
                    let x = (i as i32) - (sieve_interval_length as i32);
                    evaluate_polynomial_at(x, &polynomial, kn, &mut u_scratch, &mut v_scratch);
                    if let Some((relation, p, q)) = factor_over_factorbase(
                        x,
                        &v_scratch,
                        factorbase,
                        roots,
                        reciprocals,
                        k,
                        large_prime_multiplier,
                        use_dlp,
                        &mut factor_scratch,
                        &mut relation_scratch,
                    ) {
                        if sender
                            .send((
                                u_scratch.clone(),
                                v_scratch.clone(),
                                relation,
                                p,
                                q,
                                index_thread,
                            ))
                            .is_err()
                        {
                            break 'outer_loop;
                        }
                    }
                }
                i += 1;
            }
            block_start = block_end;
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
                eprintln!(
                    "[profile] {prof_polys} polys | per poly: poly {:.0}us \
                     sieve {:.0}us (setup {setup}us loop {bloop}us) scan+factor {:.0}us",
                    prof_poly.as_micros() as f64 / prof_polys as f64,
                    prof_sieve.as_micros() as f64 / prof_polys as f64,
                    prof_scan.as_micros() as f64 / prof_polys as f64,
                );
            }
        }
    }
}

pub fn quadratic_sieve_multithreaded(
    n: &Integer,
    num_threads: usize,
) -> Result<Option<Integer>, NumberTheoryError> {
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
        .filter(|p| k % *p == 0)
        .map(|p| *p as u32);
    let mut factorbase = factorbase_without_k.clone();
    factorbase.extend(prime_divisors_of_multiplier);
    factorbase.sort_unstable();
    factorbase.dedup();
    let square_roots = square_roots_mod_factorbase(&kn, &factorbase);
    let mut polynomial_generators = new_polynomial_generators(
        &kn,
        sieve_interval_length as u64,
        num_threads,
        &factorbase,
        &square_roots,
        &factorbase_without_k,
    );
    let logs = Arc::new(compute_logs(&factorbase));
    // Barrett reciprocals for the resieve step's per-prime `x mod p`.
    let reciprocals = Arc::new(compute_reciprocals(&factorbase));
    let factorbase = Arc::new(factorbase.clone());
    let kn_bits = kn.significant_bits();
    // double large prime variation: only worthwhile for larger N, where non-smooth
    // cofactors are big enough that admitting two large primes pays for the extra
    // primality test / Pollard-rho split and the larger partial-relation graph.
    let n_bits = n.significant_bits();
    let use_dlp = n_bits > 250;
    println!("double large prime: {use_dlp}");
    let lp_slack = lp_slack_bits(use_dlp, n_bits, *logs.last().unwrap() as u32, large_prime_multiplier);
    println!(
        "lp slack multiplier: {:.2} ({lp_slack} bits)",
        lp_slack_multiplier(use_dlp, n_bits),
    );
    let n = Arc::new(n);
    let kn = Arc::new(kn.clone());
    let shared_factor = Arc::new(Mutex::new(None));
    rayon::scope(|s| {
        let (sender, receiver) = mpsc::channel();
        // consumer thread: processes (partial) relations
        {
            let shared_factor = Arc::clone(&shared_factor);
            let factorbase = Arc::clone(&factorbase);
            let n = Arc::clone(&n);
            s.spawn(move |_| {
                // set up matrix for relations over the factorbase
                let mut relations = Relations::new(factorbase.len());
                // combines (partial) relations into full ones: a single-prime hash map
                // without the double large prime variation, the cycle graph with it
                let mut partial_relations = PartialStore::new(use_dlp);
                // time each 10% progress step (same step as add_relation's `(k)` report)
                // and flag the slow ones. `step` mirrors Relations::add_relation.
                let progress_step = (factorbase.len() / 10).max(1);
                let mut last_step_time = Instant::now();

                loop {
                    let received: Result<(Integer, Integer, FixedBitSet, u32, u32, usize), _> =
                        receiver.recv();
                    // all producers have exited and dropped their senders: stop.
                    let Ok((u, v, relation, p, q, index_thread)) = received else {
                        return;
                    };
                    // full relations go straight to the matrix; partials (one or two
                    // large primes) are routed through the partial-relation graph,
                    // which yields a full relation only when it closes a cycle.
                    let full = if p == 1 && q == 1 {
                        debug_print!("{}", format_color("+", index_thread));
                        Some((relation, u, v))
                    } else {
                        match partial_relations.add(relation, u, v, p, q) {
                            Some(full) => {
                                debug_print!("{}", format_color(":", index_thread));
                                Some(full)
                            }
                            None => {
                                debug_print!("{}", format_color(".", index_thread));
                                None
                            }
                        }
                    };
                    let Some((relation, u, v)) = full else {
                        continue;
                    };
                    relations.add_relation(relation, (u, v));
                    // when a 10% step boundary is crossed, report its time if it was slow
                    let count = relations.len();
                    if count.is_multiple_of(progress_step) {
                        let elapsed = last_step_time.elapsed();
                        if elapsed > Duration::from_secs(5) {
                            print!("({} {} ms)", count / progress_step, elapsed.as_millis());
                            io::stdout().flush().unwrap();
                        }
                        last_step_time = Instant::now();
                    }
                    // Gaussian elimination
                    if let Some(relation) = relations.gaussian_elimination() {
                        debug_print!("{}", format_color("!", index_thread));
                        if let Some(factor) = relations.find_factor(&relation, &n) {
                            // dropping the receiver makes every producer's next
                            // `send` fail, terminating them.
                            drop(receiver);
                            println!("\nfound factor: {factor} (thread #{index_thread})");
                            io::stdout().flush().unwrap();
                            *shared_factor.lock().unwrap() = Some(factor);
                            return;
                        }
                        // relation was not useful, drop the last relation
                        relations.drop_last_relation();
                    }
                }
            });
        }

        spawn_sieve_producers(
            s,
            &mut polynomial_generators,
            &logs,
            &factorbase,
            &reciprocals,
            &kn,
            sieve_interval_length,
            kn_bits,
            k,
            large_prime_multiplier,
            use_dlp,
            lp_slack,
            &sender,
        );
        // drop the original sender so the consumer's recv() terminates once every
        // producer (each holding a clone) has exited.
        drop(sender);
    });
    Ok(shared_factor.lock().unwrap().clone())
}

/// Spawn one producer thread per polynomial generator into the rayon scope, each
/// cloning the shared inputs and the relation sender. Shared by both solvers.
#[allow(clippy::too_many_arguments)]
fn spawn_sieve_producers<'scope, 'env>(
    s: &rayon::Scope<'scope>,
    polynomial_generators: &'scope mut [SIQSPolynomialData<'env>],
    logs: &'scope Arc<Vec<u8>>,
    factorbase: &'scope Arc<Vec<u32>>,
    reciprocals: &'scope Arc<Vec<u64>>,
    kn: &'scope Arc<Integer>,
    sieve_interval_length: usize,
    kn_bits: u32,
    k: u32,
    large_prime_multiplier: u32,
    use_dlp: bool,
    lp_slack: u32,
    sender: &mpsc::Sender<RelationMsg>,
) {
    for (index_thread, polynomial_generator) in polynomial_generators.iter_mut().enumerate() {
        let logs = Arc::clone(logs);
        let factorbase = Arc::clone(factorbase);
        let reciprocals = Arc::clone(reciprocals);
        let kn = Arc::clone(kn);
        let sender = sender.clone();
        s.spawn(move |_| {
            run_sieve_producer(
                index_thread,
                polynomial_generator,
                &logs,
                &factorbase,
                &reciprocals,
                &kn,
                sieve_interval_length,
                kn_bits,
                k,
                large_prime_multiplier,
                use_dlp,
                lp_slack,
                &sender,
            );
        });
    }
}

/// Block Lanczos variant: collect a full batch of relations, then solve the linear
/// algebra once with [`SparseRelations::dependencies_lanczos`] instead of the
/// incremental dense Gaussian elimination used by [`quadratic_sieve_multithreaded`].
///
/// The producer (sieving) side is identical; only the consumer differs: it routes
/// partials through the same combiner but accumulates the full relations sparsely
/// until it has `factorbase_size + RELATION_SURPLUS` of them, then runs Block Lanczos
/// and tries each returned dependency through `find_factor`. This trades the
/// incremental "stop as soon as a dependency appears" early exit for an O(n²) (rather
/// than O(n³)) linear-algebra phase — the right tradeoff once the factor base is large.
pub fn quadratic_sieve_lanczos(
    n: &Integer,
    num_threads: usize,
) -> Result<Option<Integer>, NumberTheoryError> {
    // surplus relations beyond the number of appearing primes, so the kernel (hence
    // the number of dependencies) is at least this large. Kept comfortably above the
    // 64-wide Block Lanczos block so the kernel dimension never sits exactly on the
    // block boundary (the degenerate case where a single block can fail to capture it).
    const RELATION_SURPLUS: usize = 192;
    // fixed seed for the randomized starting block, for reproducible runs
    const LANCZOS_SEED: u64 = 0x5161_7A9F_2C3D_4E5F;

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
        .filter(|p| k % *p == 0)
        .map(|p| *p as u32);
    let mut factorbase = factorbase_without_k.clone();
    factorbase.extend(prime_divisors_of_multiplier);
    factorbase.sort_unstable();
    factorbase.dedup();
    let square_roots = square_roots_mod_factorbase(&kn, &factorbase);
    let mut polynomial_generators = new_polynomial_generators(
        &kn,
        sieve_interval_length as u64,
        num_threads,
        &factorbase,
        &square_roots,
        &factorbase_without_k,
    );
    let logs = Arc::new(compute_logs(&factorbase));
    let reciprocals = Arc::new(compute_reciprocals(&factorbase));
    let factorbase = Arc::new(factorbase.clone());
    let kn_bits = kn.significant_bits();
    let n_bits = n.significant_bits();
    let use_dlp = n_bits > 250;
    println!("double large prime: {use_dlp}");
    let lp_slack = lp_slack_bits(use_dlp, n_bits, *logs.last().unwrap() as u32, large_prime_multiplier);
    println!(
        "lp slack multiplier: {:.2} ({lp_slack} bits)",
        lp_slack_multiplier(use_dlp, n_bits),
    );
    let n = Arc::new(n);
    let kn = Arc::new(kn.clone());
    let shared_factor = Arc::new(Mutex::new(None));
    rayon::scope(|s| {
        let (sender, receiver) = mpsc::channel();
        // consumer thread: combine partials, accumulate full relations, then solve
        {
            let shared_factor = Arc::clone(&shared_factor);
            let factorbase = Arc::clone(&factorbase);
            let n = Arc::clone(&n);
            s.spawn(move |_| {
                // combines (partial) relations into full ones (shared, global state)
                let mut partial_relations = PartialStore::new(use_dlp);
                // full relations collected sparsely for the batch linear algebra
                let mut sparse = SparseRelations::new(factorbase.len());
                // dedup: the sieve re-finds the same smooth values (identical parity
                // rows are useless duplicates that inflate the relation count without
                // adding rank), so collect each distinct parity vector at most once.
                let mut seen: FxHashSet<Vec<u32>> = FxHashSet::default();
                // which factor-base primes have actually appeared: the matrix only
                // needs a surplus over *these*, not over the full factor base (for
                // small N most large primes never divide any Q(x)).
                let mut appeared = vec![false; factorbase.len()];
                let mut appeared_count = 0usize;

                // progress: report every 10% of the (estimated) max relations needed.
                // The actual target is appeared_count + RELATION_SURPLUS; appeared_count
                // is bounded by the factor base, so this is the upper bound.
                let max_relations = factorbase.len() + RELATION_SURPLUS;
                let progress_step = (max_relations / 10).max(1);
                let collection_start = Instant::now();
                // time each 10% step so slow ones can be flagged
                let mut last_step_time = collection_start;

                // Producers run forever; this consumer is the sole authority that
                // stops them. Collect until we hold RELATION_SURPLUS more distinct
                // relations than distinct primes appearing — then the kernel (hence
                // the number of dependencies) is at least that big.
                while sparse.len() < appeared_count + RELATION_SURPLUS {
                    let Ok((u, v, relation, p, q, index_thread)) = receiver.recv() else {
                        // Producers never exit on their own, so a closed channel can
                        // only mean a producer panicked: nothing more will arrive.
                        break;
                    };
                    let full = if p == 1 && q == 1 {
                        debug_print!("{}", format_color("+", index_thread));
                        Some((relation, u, v))
                    } else {
                        match partial_relations.add(relation, u, v, p, q) {
                            Some(full) => {
                                debug_print!("{}", format_color(":", index_thread));
                                Some(full)
                            }
                            None => {
                                debug_print!("{}", format_color(".", index_thread));
                                None
                            }
                        }
                    };
                    if let Some((relation, u, v)) = full {
                        let cols: Vec<u32> = relation.ones().map(|c| c as u32).collect();
                        if seen.insert(cols.clone()) {
                            for &c in &cols {
                                if !appeared[c as usize] {
                                    appeared[c as usize] = true;
                                    appeared_count += 1;
                                }
                            }
                            sparse.push_sparse(cols, (u, v));
                            if sparse.len().is_multiple_of(progress_step) {
                                let step = sparse.len() / progress_step;
                                let elapsed = last_step_time.elapsed();
                                print!("({step}: {} ms)", elapsed.as_millis());
                                io::stdout().flush().unwrap();
                                last_step_time = Instant::now();
                            }
                        }
                    }
                }
                // Enough relations collected: terminate every producer — dropping the
                // receiver makes their next `send` fail — then run the linear algebra.
                drop(receiver);
                let collection_time = collection_start.elapsed();
                println!(
                    "\ncollected {} distinct relations ({appeared_count} primes appearing) \
                     in {collection_time:.2?}; running Block Lanczos with {} threads…",
                    sparse.len(),
                    num_threads + 1
                );
                io::stdout().flush().unwrap();
                let lanczos_start = Instant::now();
                let dependencies = sparse.dependencies_lanczos(LANCZOS_SEED, num_threads + 1);
                let lanczos_time = lanczos_start.elapsed();
                println!(
                    "Block Lanczos returned {} dependencies in {lanczos_time:.2?}",
                    dependencies.len()
                );
                for dependency in &dependencies {
                    if let Some(factor) = sparse.find_factor(dependency, &n) {
                        println!("found factor: {factor}");
                        io::stdout().flush().unwrap();
                        *shared_factor.lock().unwrap() = Some(factor);
                        return;
                    }
                }
                println!("no factor found among the dependencies");
            });
        }

        spawn_sieve_producers(
            s,
            &mut polynomial_generators,
            &logs,
            &factorbase,
            &reciprocals,
            &kn,
            sieve_interval_length,
            kn_bits,
            k,
            large_prime_multiplier,
            use_dlp,
            lp_slack,
            &sender,
        );
        drop(sender);
    });
    Ok(shared_factor.lock().unwrap().clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_make_factorbase() {
        let factorbase = make_factorbase(&Integer::from(400003), 10);
        // index 0 holds the sentinel 0 standing for -1
        assert_eq!(factorbase, vec![0u32, 2, 3, 7, 29, 31, 37, 43, 71, 73]);
    }

    #[test]
    fn test_square_roots_mod_factorbase() {
        let n = Integer::from(400003);
        let factorbase = make_factorbase(&n, 10);
        let square_roots = square_roots_mod_factorbase(&n, &factorbase);
        // index 0 (the -1 sentinel) has square root 0
        assert_eq!(square_roots, vec![0u32, 1, 1, 4, 8, 14, 12, 24, 29, 6]);
    }

    #[test]
    fn test_compute_sieve_parameters() {
        for bits in 63..=213 {
            println!("{bits}: {:?}", compute_sieve_parameters(bits));
        }
    }
}
