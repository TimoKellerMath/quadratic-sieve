use std::io::{self, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, mpsc};

use rug::Integer;

use fixedbitset::FixedBitSet;

// debug_print! expands to nothing in release, leaving format_color unused there.
#[allow(unused_imports)]
use crate::debug_print;
use crate::factorbase::*;
#[allow(unused_imports)]
use crate::format_color::format_color;
use crate::multiplier::*;
use crate::number_theory::*;
use crate::relations::*;
use crate::siqs_generator::*;

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
    let factorbase = Arc::new(factorbase.clone());
    let kn_bits = kn.significant_bits();
    // double large prime variation: only worthwhile for larger N, where non-smooth
    // cofactors are big enough that admitting two large primes pays for the extra
    // primality test / Pollard-rho split and the larger partial-relation graph.
    let use_dlp = n.significant_bits() > 250;
    println!("double large prime: {use_dlp}");
    let n = Arc::new(n);
    let kn = Arc::new(kn.clone());
    let found = Arc::new(AtomicBool::new(false));
    let shared_factor = Arc::new(Mutex::new(None));
    rayon::scope(|s| {
        let (sender, receiver) = mpsc::channel();
        // consumer thread: processes (partial) relations
        {
            let found = Arc::clone(&found);
            let shared_factor = Arc::clone(&shared_factor);
            let factorbase = Arc::clone(&factorbase);
            let n = Arc::clone(&n);
            s.spawn(move |_| {
                // set up matrix for relations over the factorbase
                let mut relations = Relations::new(factorbase.len());
                // combines (partial) relations into full ones: a single-prime hash map
                // without the double large prime variation, the cycle graph with it
                let mut partial_relations = PartialStore::new(use_dlp);

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
                    // Gaussian elimination
                    if let Some(relation) = relations.gaussian_elimination() {
                        debug_print!("{}", format_color("!", index_thread));
                        if let Some(factor) = relations.find_factor(&relation, &n) {
                            drop(receiver);
                            println!("\nfound factor: {factor} (thread #{index_thread})");
                            io::stdout().flush().unwrap();
                            *shared_factor.lock().unwrap() = Some(factor);
                            found.store(true, Ordering::Relaxed);
                            return;
                        }
                        // relation was not useful, drop the last relation
                        relations.drop_last_relation();
                    }
                }
            });
        }

        for (index_thread, polynomial_generator) in polynomial_generators.iter_mut().enumerate() {
            let found = Arc::clone(&found);
            let logs = Arc::clone(&logs);
            let factorbase = Arc::clone(&factorbase);
            let kn = Arc::clone(&kn);
            // create thread #i that computes (num_threads) new q's if there is none available in qs (atomic)
            // storing the relations and the linear algebra step is atomic
            // producer threads: produce (partial) relations
            let sender1 = sender.clone();
            s.spawn(move |_| {
                let mut logs_for_polynomial = vec![0u8; 2 * sieve_interval_length];
                // scratch reused across polynomials by the blocked sieve
                let mut next_pos: Vec<usize> = Vec::with_capacity(2 * factorbase.len());
                // scratch integer reused by factor_over_factorbase per candidate
                let mut factor_scratch = Integer::new();

                'outer_loop: loop {
                    if found.load(Ordering::Relaxed) {
                        break 'outer_loop;
                    }
                    let (polynomial, roots) = polynomial_generator.next_polynomial();
                    debug_print!("{}", format_color("?", index_thread));
                    const BLOCK_SIZE: usize = 2 * 65536;
                    let sum_small_logs = sieve_over_factorbase_blocked(
                        sieve_interval_length,
                        &factorbase,
                        roots,
                        &logs,
                        &mut logs_for_polynomial,
                        &mut next_pos,
                        BLOCK_SIZE,
                    );
                    // threshold = log_2(kn/a) - large-prime slack - sum of small logs.
                    // With the double large prime variation we allow two large primes,
                    // so reserve extra slack — 1.5x the largest prime's log, a middle
                    // ground between one prime's worth and a full two, admitting fewer
                    // candidates than 2x while still catching most semiprime cofactors.
                    let log2_kn_over_a = kn_bits.saturating_sub(polynomial.a.significant_bits());
                    let largest_log = *logs.last().unwrap() as u32;
                    let lp_slack = if use_dlp {
                        3 * largest_log / 2
                    } else {
                        largest_log
                    };
                    let threshold: u8 = log2_kn_over_a
                        .saturating_sub(lp_slack)
                        .saturating_sub(sum_small_logs)
                        .min(u8::MAX as u32) as u8;
                    let total = logs_for_polynomial.len();
                    let mut i = 0usize;
                    #[cfg(target_feature = "avx2")]
                    unsafe {
                        use std::arch::x86_64::*;
                        let thr_vec = _mm256_set1_epi8(threshold as i8);
                        let ptr = logs_for_polynomial.as_ptr();
                        while i + 32 <= total {
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
                                    let (u, v) = evaluate_polynomial_at(x, &polynomial, &kn);
                                    if let Some((relation, p, q)) = factor_over_factorbase(
                                        x, &v, &factorbase, roots, k, large_prime_multiplier,
                                        use_dlp, &mut factor_scratch,
                                    ) {
                                        if sender1
                                            .send((u, v, relation, p, q, index_thread))
                                            .is_err() {
                                            break 'outer_loop;
                                        }
                                    }
                                }
                            }
                            i += 32;
                        }
                    }
                    while i < total {
                        let log = logs_for_polynomial[i];
                        if log >= threshold {
                            let x = (i as i32) - (sieve_interval_length as i32);
                            let (u, v) = evaluate_polynomial_at(x, &polynomial, &kn);
                            if let Some((relation, p, q)) = factor_over_factorbase(
                                x, &v, &factorbase, roots, k, large_prime_multiplier,
                                use_dlp, &mut factor_scratch,
                            ) {
                                if sender1
                                    .send((u, v, relation, p, q, index_thread))
                                    .is_err() {
                                    break 'outer_loop;
                                }
                            }
                        }
                        i += 1;
                    }
                }
            });
        }
        // drop the original sender so the consumer's recv() terminates once every
        // producer (each holding a clone) has exited.
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
