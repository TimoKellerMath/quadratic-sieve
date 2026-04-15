use std::io::{self, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, mpsc};
use std::time::Instant;

use rug::Integer;

use fixedbitset::FixedBitSet;

use rustc_hash::FxHashMap;

pub mod number_theory;
use crate::number_theory::*;
pub mod constants;
pub mod factorbase;
use crate::factorbase::*;
pub mod polynomial_generator;
pub mod siqs_generator;
use crate::siqs_generator::*;
pub mod relations;
use crate::relations::*;
pub mod multiplier;
use crate::multiplier::*;
pub mod debug_print;
pub mod format_color;
#[allow(unused_imports)]
use crate::format_color::format_color;

fn quadratic_sieve_multithreaded(
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
                let mut big_prime_relations =
                    FxHashMap::<u32, (FixedBitSet, Integer, Integer)>::default();

                loop {
                    let (mut u, mut v, mut relation, big_prime, index_thread): (
                        Integer,
                        Integer,
                        FixedBitSet,
                        u32,
                        usize,
                    ) = receiver.recv().unwrap();
                    // add relation, index, (u,v)
                    if big_prime > 1 {
                        if let Some((relation2, u2, v2)) = big_prime_relations.get(&big_prime) {
                            relation ^= relation2;
                            u *= u2;
                            v *= v2;
                            debug_print!("{}", format_color(":", index_thread));
                        } else {
                            big_prime_relations.insert(big_prime, (relation, u, v));
                            debug_print!("{}", format_color(".", index_thread));
                            continue;
                        }
                    } else {
                        debug_print!("{}", format_color("+", index_thread));
                    }
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

                'outer_loop: loop {
                    if found.load(Ordering::Relaxed) {
                        break 'outer_loop;
                    }
                    let (polynomial, roots) = polynomial_generator.next_polynomial();
                    debug_print!("{}", format_color("?", index_thread));
                    //const BLOCK_SIZE_FOR_RYZEN6850: usize = 2 * 65536;
                    let sum_small_logs = sieve_over_factorbase(
                        sieve_interval_length,
                        &factorbase,
                        roots,
                        &logs,
                        &mut logs_for_polynomial,
                        //BLOCK_SIZE_FOR_RYZEN6850,
                    );
                    // threshold = log_2(kn/a) - log of largest prime - sum of small logs
                    let log2_kn_over_a = kn_bits.saturating_sub(polynomial.a.significant_bits());
                    let threshold: u8 = log2_kn_over_a
                        .saturating_sub(*logs.last().unwrap() as u32)
                        .saturating_sub(sum_small_logs)
                        .min(u8::MAX as u32) as u8;
                    for (i, &log) in logs_for_polynomial.iter().enumerate() {
                        let x = (i as i32) - (sieve_interval_length as i32);
                        if log >= threshold {
                            // trial divisions — evaluate polynomial using Horner's scheme
                            let (u, v) = evaluate_polynomial_at(x, &polynomial, &kn);
                            // if Q(x) = v factored over factor base:
                            if let Some((relation, big_prime)) =
                                factor_over_factorbase(&v, &factorbase, k, large_prime_multiplier)
                            {
                                if sender1
                                    .send((u, v, relation, big_prime, index_thread))
                                    .is_err() {
                                    // terminate when the consumer loop has terminated (because it found a non-trivial factor)
                                    break 'outer_loop;
                                }
                            }
                        }
                    }
                }
            });
        }
    });
    Ok(shared_factor.lock().unwrap().clone())
}

#[cfg(test)]
mod tests {
    //use std::str::FromStr;

    //use rug::integer::IsPrime;

    use super::*;

    #[test]
    fn test_make_factorbase() {
        let factorbase = make_factorbase(&Integer::from(400003), 10);
        let factorbase2: Vec<Integer> = vec![-1, 2, 3, 7, 29, 31, 37, 43, 71, 73]
            .iter()
            .map(|&k| Integer::from(k))
            .collect();
        assert_eq!(factorbase, factorbase2);
    }

    #[test]
    fn test_square_roots_mod_factorbase() {
        let n = Integer::from(400003);
        let factorbase = make_factorbase(&n, 10);
        let square_roots = square_roots_mod_factorbase(&n, &factorbase);
        let square_roots2: Vec<Integer> = vec![1, 1, 1, 4, 8, 14, 12, 24, 29, 6]
            .iter()
            .map(|&k| Integer::from(k))
            .collect();
        assert_eq!(square_roots, square_roots2);
    }

    #[test]
    fn test_compute_sieve_parameters() {
        for bits in 63..=213 {
            println!("{bits}: {:?}", compute_sieve_parameters(bits));
        }
    }

    /*#[test]
    fn test_roots_mod_p() {
        let kn = Integer::from(13 * 17);
        let factorbase = make_factorbase(&kn, 10);
        println!("factorbase = {factorbase:?}");
        let square_roots = square_roots_mod_factorbase(&kn, &factorbase);
        println!("square roots = {square_roots:?}");
        let mut q = Integer::from(3);
        for _ in 0..10 {
            while kn.legendre(&q) != 1 {
                q = q.next_prime();
            }
            let polynomial = generate_polynomial(&kn, &q).unwrap();
            println!("polynomial = {polynomial:?}");
            let mut q_inverse = q.clone();
            q_inverse = q_inverse.invert(&kn).unwrap();
            for (i, p) in factorbase.iter().enumerate() {
                if i == 0 {
                    // ignore -1 in factor base
                    continue;
                }
                let (root1, root2) = roots_mod_p(&polynomial, square_roots[i], *p);
                println!("p = {p}: roots = {root1}, {root2}");
                let (_, y) =
                    evaluate_polynomial_at(&Integer::from(root1), &polynomial, &q_inverse, &kn);
                println!("y_1 = {y}");
                assert!(y.is_divisible(&Integer::from(*p)));
                let (_, y) =
                    evaluate_polynomial_at(&Integer::from(root2), &polynomial, &q_inverse, &kn);
                println!("y_2 = {y}");
                assert!(y.is_divisible(&Integer::from(*p)));
            }
        }
    }

    #[test]
    fn test_sieve_over_factorbase() {
        let kn = Integer::from(13 * 17);
        let factorbase = make_factorbase(&kn, 4);
        println!("factorbase = {factorbase:?}");
        let square_roots = square_roots_mod_factorbase(&kn, &factorbase);
        println!("square roots = {square_roots:?}");
        let logs = compute_logs(&factorbase);
        println!("logs = {logs:?}");
        let mut q = Integer::from(3);
        while kn.legendre(&q) != 1 {
            q = q.next_prime();
        }
        let polynomial = generate_polynomial(&kn, &q).unwrap();
        println!("polynomial = {polynomial:?}");
        let sieve_interval_length = 8;
        println!("sieve interval length = {sieve_interval_length}");
        let logs_for_polynomial =
            sieve_over_factorbase(&polynomial, 8, &factorbase, &square_roots, &logs);
        println!("logs: {logs_for_polynomial:?}");
    }*/
}

fn main() {
    /*let n = Integer::from(314159265358979323i64);
    let factor = quadratic_sieve_multithreaded(&n, 1).unwrap().unwrap();
    println!("factor1 = {factor}");*/
    // 2^149 - 1
    /* let n = (Integer::from(1) << 149) - 1;
    let now = Instant::now();
    let factor = quadratic_sieve_multithreaded(&n, 1).unwrap().unwrap();
    let elapsed_time = now.elapsed();
    println!("factor1 = {factor} ({} ms)", elapsed_time.as_millis());*/

    /*let now = Instant::now();
    let n = (Integer::from(1) << 128) + 1;
    let factor = quadratic_sieve_multithreaded(&n, 1).unwrap().unwrap();
    let elapsed_time = now.elapsed();
    println!("factor1 = {factor} ({} ms)", elapsed_time.as_millis());*/

    // 80 + 90 bit
    /*let n = "1496577676626844588240589522709118530816928848545473"
        .parse::<Integer>()
        .unwrap();
    let now = Instant::now();
    let factor = quadratic_sieve_multithreaded(&n, 8).unwrap().unwrap();
    let elapsed_time = now.elapsed();
    println!("factor1 = {factor} ({} ms)", elapsed_time.as_millis());*/

    // 100 + 102 bit
    let n = "6427752177035961102167848371107669985402627402189138248671463"
        .parse::<Integer>()
        .unwrap();
    let now = Instant::now();
    let factor = quadratic_sieve_multithreaded(&n, 7).unwrap().unwrap();
    let elapsed_time = now.elapsed();
    println!("factor1 = {factor} ({} ms)", elapsed_time.as_millis());

    /*// 2^128 + 1
    let n = (Integer::from(1) << 128) + 1;
    let factor = quadratic_sieve(&n).unwrap().unwrap();
    println!("factor1 = {factor}");

    // 2^149 - 1
    let n = (Integer::from(1) << 149) - 1;
    let factor = quadratic_sieve(&n).unwrap().unwrap();
    println!("factor1 = {factor}");*/
}
