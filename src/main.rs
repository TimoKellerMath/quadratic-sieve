use std::collections::HashMap;
use std::io::{self, Write};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Instant;

use rug::{Float, Integer};

use bit_vec::BitVec;

pub mod number_theory;
use crate::number_theory::*;
pub mod constants;
use crate::constants::*;
pub mod factorbase;
use crate::factorbase::*;
pub mod polynomial_generator;
pub mod siqs_generator;
use crate::siqs_generator::*;
pub mod relations;
use crate::relations::*;
pub mod multiplier;
use crate::multiplier::*;
pub mod format_color;
use crate::format_color::*;

// run the quadratic sieve algorithm on n
fn quadratic_sieve_multithreaded(
    n: &Integer,
    num_threads: usize,
) -> Result<Option<Integer>, NumberTheoryError> {
    let k = compute_multiplier(n)?;
    println!("k = {k}");
    let kn: Integer = n.clone() * k;
    // heuristic value for the factor base
    let log2_kn = Float::with_val(PREC, &kn)
        .log2()
        .round()
        .to_u32_saturating()
        .unwrap() as usize;
    let (factorbase_size, sieve_interval_length, large_prime_multiplier) =
        compute_sieve_parameters(log2_kn);
    println!("factor base size: {factorbase_size}");
    let factorbase_without_k = make_factorbase(&kn, factorbase_size);
    // add prime factors of multiplier k to factor base
    let prime_divisors_of_multiplier = SMALL_PRIMES
        .iter()
        .filter(|p| k % *p == 0)
        .map(|p| *p as i64);
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
    //println!("factor base: {factorbase:?}");
    let logs = Arc::new(compute_logs(&factorbase));
    let factorbase = Arc::new(factorbase.clone());
    // set up matrix for relations over the factorbase
    let relations_data = Relations::new(factorbase.len());
    let big_prime_relations = HashMap::<u32, (BitVec, Integer, Integer)>::new();
    let kn_float = kn.to_f64();
    let n = Arc::new(n);
    let kn = Arc::new(kn.clone());
    let shared_relations_data = Arc::new(Mutex::new(relations_data));
    let shared_big_prime_relations_data = Arc::new(Mutex::new(big_prime_relations));
    let shared_factor = Arc::new(Mutex::new(None));
    thread::scope(|s| {
        for (index_thread, polynomial_generator) in polynomial_generators.iter_mut().enumerate() {
            //let mut polynomial_generator = polynomial_generators.get_mut(index_thread).unwrap();
            let relations = Arc::clone(&shared_relations_data);
            let big_prime_relations = Arc::clone(&shared_big_prime_relations_data);
            let shared_factor = Arc::clone(&shared_factor);
            let logs = Arc::clone(&logs);
            let factorbase = Arc::clone(&factorbase);
            let n = Arc::clone(&n);
            let kn = Arc::clone(&kn);
            // create thread #i that computes (num_threads) new q's if there is none available in qs (atomic)
            // storing the relations and the linear algebra step is atomic
            s.spawn(move || {
            'outer_loop: loop {
                if shared_factor.lock().unwrap().is_some() {
                    break 'outer_loop;
                }
                let (polynomial, roots) = polynomial_generator.next_polynomial();
                //println!("polynomial: {polynomial:?}");
                print!("{}", format_color("?", index_thread));
                let (logs_for_polynomial, sum_small_logs) = sieve_over_factorbase(
                    sieve_interval_length,
                    &factorbase,
                    roots,
                    &logs,
                    &polynomial,
                    &kn
                );
                // add relations
                // target = log_2(kn/(a*sqrt(2)) * SCALE_LOGS - (scaled log of largest prime in factorbase) - (scaled log of sum of small logs)
                // note: kn/(a*sqrt(2)) \approx (sieve_interval_length)*sqrt(kn)
                let threshold: i64 = (((Float::with_val(PREC, kn_float)
                    / Float::with_val(PREC, &polynomial.a)).log2() // / Float::with_val(PREC, 2.0).sqrt()
                    * SCALE_LOGS)
                    .to_u32_saturating()
                    .unwrap()
                    - logs.last().unwrap()
                    - sum_small_logs) as i64;
                // TODO: change into log_2(2 x sqrt{kn})
                /*let threshold_base: i64 = ((2f64 * kn_float.sqrt()).log2() * SCALE_LOGS) as i64 // TODO cache sqrt(kn);
                    - (*logs.last().unwrap() as i64)
                    - (sum_small_logs as i64);*/
                for (i, log) in logs_for_polynomial.into_iter().enumerate() {
                    let x = (i as i64) - (sieve_interval_length as i64);
                    //let threshold_x = ((x.abs() as f64 + 1f64).log2() * SCALE_LOGS) as i64;
                    //if log as i64 >= threshold_base + threshold_x {
                    if log as i64 >= threshold {
                        //print!(",");
                        // trial divisions
                        // evaluate polynomial using Horner's scheme
                        let (mut u, mut v) = evaluate_polynomial_at(x, &polynomial, &kn);
                        //println!("u = {u}, v = {v}");
                        // if Q(x) = y factored over factor base:
                        if let Some((mut relation, big_prime)) =
                            factor_over_factorbase(&v, &factorbase, k, large_prime_multiplier)
                        {
                            //println!("big_prime = {big_prime}\nrelation = {relation}");
                            if shared_factor.lock().unwrap().is_some() {
                                break 'outer_loop;
                            }
                            // add relation, index, (u,v)
                            if big_prime > 1 {
                                let mut big_prime_relations = big_prime_relations.lock().unwrap();
                                if let Some((relation2, u2, v2)) =
                                    big_prime_relations.get(&big_prime)
                                {
                                    relation.xor(relation2);
                                    u *= u2;
                                    v *= v2;
                                    print!("{}", format_color(":", index_thread));
                                } else {
                                    big_prime_relations.insert(big_prime, (relation, u, v));
                                    print!("{}", format_color(".", index_thread));
                                    continue;
                                }
                            } else {
                                print!("{}", format_color("+", index_thread));
                            }
                            // atomic
                            let mut relations = relations.lock().unwrap();
                            relations.add_relation(&relation, &(u, v));
                            // Gaussian elimination
                            if let Some(relation) = relations.gaussian_elimination() {
                                //println!("{relation:?}");
                                print!("{}", format_color("!", index_thread));
                                io::stdout().flush().unwrap();
                                if let Some(factor) = relations.find_factor(&relation, &n) {
                                    println!(
                                        "\nused {} polynomials to find {} relations: {factor} (thread #{index_thread})",
                                        polynomial_generator.num_polynomials,
                                        relations.len()
                                    );
                                    *shared_factor.lock().unwrap() = Some(factor);
                                    // drop last relation, so the other threads don't use it
                                    relations.drop_last_relation();
                                    break 'outer_loop;
                                }
                                // relation was not useful, drop the last relation
                                relations.drop_last_relation();
                            }
                        }
                        else {
                            //print!(","); // y doesn't factor over factorbase
                        }
                    }
                    else {
                        //print!("-");
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
    let factor = quadratic_sieve_multithreaded(&n, 8).unwrap().unwrap();
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
