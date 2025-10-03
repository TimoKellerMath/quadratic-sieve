use crate::constants::PREC;
use crate::format_color::*;
use crate::number_theory::lift_square_root_mod_q2;
use crate::polynomial_generator::Polynomial;
use itertools::Itertools;
use rug::{Complete, Float, Integer};

#[inline]
fn product_i64_to_integer(vector: &[i64]) -> Integer {
    let mut result = Integer::from(1);
    for x in vector {
        result *= *x;
    }
    result
}

#[inline]
fn product_refi64_to_f64(vector: &[&i64]) -> f64 {
    let mut result = 1f64;
    for x in vector {
        result *= **x as f64;
    }
    result
}

// one for each thread
pub struct SIQSPolynomialData<'a> {
    thread_number: usize,
    s: usize,                          // #prime factors of q
    thread_specific_factors: Vec<i64>, // fixed for each thread
    prod_thread_specific_factors: Integer,
    num_factors: usize,
    list_of_qis: Vec<Vec<i64>>,     // successive choices of remaining qi's
    num_a: usize,                   // the num_a-th chosen a
    bis: Vec<Integer>, // for i = 1..s: B[i] = a/q[i] * gamma, gamma = sqrt(n mod p) * (a/q[i])^-1 (mod q[i])
    q_inv_mod_ps: Vec<Option<i64>>, //  for all p \nmid a in factorbase: (a^-1 mod p)
    bainv2ips: Vec<Vec<Option<i64>>>, // Bainv2ips[i,p] = (2 * B[i] * (a^-1 mod p)) (mod p), for all \nmid a in factorbase
    roots: Vec<Option<(i64, i64)>>, // for all p \nmid a in factorbase: (root1,root2) = (ainv * (sqrt(n mod p) - b), ainv * (-sqrt(n mod p) - b)) (mod p)

    j: usize, // index of polynomial for fixed a, 1 <= j <= 2^(s-1) - 1,
    a: Integer,
    q: Integer,
    q_inverse_mod_n: Integer,
    b: Integer, // the b for j

    n: &'a Integer,
    factorbase: &'a Vec<i64>,
    n_roots: &'a Vec<i64>, // the roots of n modulo the primes in the factor base
    //sieve_interval_length: u64,
    //prime_factors_for_q: &'a Vec<i64>, // we choose the q from this subset of the factorbase
    pub num_polynomials: usize, // record the number of polynomials used
}

impl<'a> SIQSPolynomialData<'a> {
    const Q_RANGE: usize = 10;
    //const RANGE_MULTIPLIER: usize = 3;

    fn initialize_new_set_of_polynomials(
        thread_specific_factors: &[i64],
        thread_number: usize,
        num_a: usize,
        n: &'a Integer,
        sieve_interval_length: u64,
        factorbase: &'a Vec<i64>,
        prime_factors_for_q: &'a [i64],
        roots: &'a Vec<i64>,
    ) -> SIQSPolynomialData<'a> {
        let mut polynomial_data = SIQSPolynomialData {
            thread_number,
            j: 0, // index of polynomial for fixed a, 1 <= j <= 2^(s-1) - 1,
            s: 0,
            num_factors: 0,
            thread_specific_factors: thread_specific_factors.to_vec(),
            prod_thread_specific_factors: product_i64_to_integer(thread_specific_factors),
            q: Integer::from(1),
            q_inverse_mod_n: Integer::from(1),
            list_of_qis: Vec::<Vec<i64>>::new(),
            num_a,                                   // index of current element of list_of_qis
            bis: Vec::<Integer>::new(), // for i = 1..s: B[i] = a/q[i] * gamma, gamma = sqrt(n mod p) * (a/q[i])^-1 (mod q[i])
            q_inv_mod_ps: Vec::<Option<i64>>::new(), //  for all p \nmid a in factorbase: (a^-1 mod p)
            bainv2ips: Vec::<Vec<Option<i64>>>::new(), // Bainv2ips[i,p] = (2 * B[i] * (a^-1 mod p)) (mod p), for all p \nmid a in factorbase
            a: Integer::from(0),
            b: Integer::from(0), // the b for j,
            roots: Vec::<Option<(i64, i64)>>::new(),
            n,
            factorbase,
            n_roots: roots,
            num_polynomials: 0,
        };
        // compute size of "average" qi
        // q \approx sqrt((sqrt(2 * kn)/sieve_interval_length)
        let total_q_size = ((2f64 * Float::with_val(PREC, n.clone())).sqrt()
            / Float::with_val(PREC, sieve_interval_length))
        .sqrt();
        polynomial_data.compute_list_of_factors_of_q(&total_q_size, prime_factors_for_q);
        polynomial_data.precompute_polynomial_data_for_q(n, factorbase, roots);
        println!(
            "thread #{thread_number}: {} + {} = {} factors",
            thread_specific_factors.len(),
            polynomial_data.s,
            polynomial_data.num_factors
        );
        //print!("{}", format_color(format!("thread #{thread_number}: {} + {} = {} factors", thread_specific_factors.len(), polynomial_data.s, polynomial_data.num_factors), self.thread_number));
        polynomial_data
    }

    fn compute_average_size_of_q(&self, total_q_size: &Float, s: usize) -> f64 {
        (total_q_size.clone() / Float::with_val(PREC, self.prod_thread_specific_factors.clone()))
            .root(s as u32)
            .to_f64()
    }

    fn compute_number_of_factors_of_q(
        &self,
        total_q_size: &Float,
        prime_factors_for_q: &[i64],
    ) -> (usize, usize) {
        // fixed number of factors: 5
        /*let s = 7 - self.thread_specific_factors.len();
        let average_q_size: i64 = self.compute_average_size_of_q(total_q_size, s) as i64;
        let i = prime_factors_for_q.iter().position(|&p| p > average_q_size).expect("average q size too large for factorbase");
        (s, i)*/

        // compute maximum possible number of factors
        let mut s = 2_usize;
        let mut s_min;
        let mut i_min;
        // look for the smallest possible s
        loop {
            let average_q_size: i64 = self.compute_average_size_of_q(total_q_size, s) as i64;
            if let Some(i) = prime_factors_for_q.iter().position(|&p| p > average_q_size)
                && prime_factors_for_q.get(i + Self::Q_RANGE).is_some()
            {
                (s_min, i_min) = (s, i);
                s += 1;
                break;
            }
            s += 1;
        }
        // look for the maximum possible s
        loop {
            let average_q_size: i64 = self.compute_average_size_of_q(total_q_size, s) as i64;
            if let Some(i) = prime_factors_for_q.iter().position(|&p| p > average_q_size)
                && average_q_size > prime_factors_for_q[Self::Q_RANGE]
                && prime_factors_for_q[i - Self::Q_RANGE]
                    > *self.thread_specific_factors.last().unwrap()
                && prime_factors_for_q.get(i + Self::Q_RANGE).is_some()
            {
                //println!("s = {s}");
                (s_min, i_min) = (s, i);
            } else {
                return (s_min, i_min);
            }
            s += 1;
        }
    }

    fn compute_list_of_factors_of_q(&mut self, total_q_size: &Float, prime_factors_for_q: &[i64]) {
        let (s, i) = self.compute_number_of_factors_of_q(total_q_size, prime_factors_for_q);
        self.s = s;
        self.num_factors = s + self.thread_specific_factors.len();
        let range_size = Self::Q_RANGE;
        //let range_size = Self::RANGE_MULTIPLIER * s;
        let i_min = i - range_size; // extend this for the next values of a
        assert!(prime_factors_for_q[i_min] > *self.thread_specific_factors.last().unwrap());
        let combinations = prime_factors_for_q
            .iter()
            .skip(i_min)
            .take(range_size * 2)
            .combinations(s);
        const SCALE: f64 = 65536.0;
        let prod_thread_specific_factors = self.prod_thread_specific_factors.to_f64();
        let total_q_size = total_q_size.to_f64();
        let quotient = prod_thread_specific_factors / total_q_size;
        let qis_with_quality = combinations.into_iter().map(|combination| {
            (
                combination.clone(),
                ((quotient * product_refi64_to_f64(combination.as_slice()))
                    .log2()
                    .abs()
                    * SCALE) as i64,
            )
        });
        let qis_by_quality = qis_with_quality
            .sorted_unstable_by_key(|(_, quality)| *quality)
            .map(|(combination, _)| combination);
        self.list_of_qis = Vec::<Vec<i64>>::new();
        for qis in qis_by_quality {
            let mut new_qis: Vec<i64> = self.thread_specific_factors.to_vec();
            for q in qis {
                new_qis.push(*q);
            }
            //let q = product_i64_to_integer(&new_qis);
            //let quality = (Float::with_val(PREC,q) / Float::with_val(PREC,total_q_size)).log2().abs();
            //println!("quality: {quality}");
            self.list_of_qis.push(new_qis);
        }
        println!("{} q's", self.list_of_qis.len());
    }

    fn root_of_linear_polynomial_mod_p(b: &Integer, c: &Integer, p: i64) -> Option<i64> {
        if p <= 2 {
            return None;
        }
        let twice_b: Integer = (b << 1u32).complete();
        if let Ok(twice_b_inverse) = twice_b.invert(&Integer::from(p)) {
            // TODO: can this fail?
            let root1 = twice_b_inverse * c;
            let root = -(root1.mod_u(p as u32) as i64);
            //println!("root = {root}, b = {b}, c = {c}, p = {p}");
            debug_assert!((Integer::from(2) * b * root + c).is_divisible_u(p as u32));
            Some(root)
        } else {
            // if poly = c (p), then either there is no zero or the polynomial is 0
            None
        }
    }

    fn precompute_polynomial_data_for_q(&mut self, n: &Integer, factorbase: &[i64], roots: &[i64]) {
        print!("{}", format_color("|", self.thread_number));
        let qis = &self.list_of_qis[self.num_a];
        self.q = product_i64_to_integer(qis);
        self.a = self.q.square_ref().complete();
        self.q_inverse_mod_n = self.q.invert_ref(n).unwrap().complete();

        // compute the corresponding B[i]'s with B[i]^2 = delta_{ij} * n (mod q[j])
        self.bis.clear();
        for q in qis {
            let a_div_q = self.q.div_exact_u_ref(*q as u32).complete();
            let root_q: i64 = roots[factorbase.iter().position(|&p| p == *q).unwrap()];
            let a_div_q_squared = a_div_q.square();
            let q_squared = Integer::from(*q).square();
            let root_mod_q_squared =
                lift_square_root_mod_q2(n, &Integer::from(root_q), &q_squared).unwrap(); // TODO: cache this!
            let mut gamma = ((root_mod_q_squared
                * a_div_q_squared.invert_ref(&q_squared).unwrap().complete())
                % q_squared.clone())
            .to_i64()
            .unwrap();
            let q_squared = q_squared.to_i64().unwrap();
            if gamma > (q_squared / 2) {
                gamma = q_squared - gamma;
            }
            self.bis.push(a_div_q_squared * gamma);
        }

        // compute a^-1 (mod p) if it exists
        self.q_inv_mod_ps.clear();
        for p in factorbase {
            if *p > 2
                && let Some(q_inv_mod_p) = self.a.invert_ref(&Integer::from(*p))
            {
                let ainvp = q_inv_mod_p.complete().to_i64().unwrap();
                self.q_inv_mod_ps.push(Some(ainvp));
            } else {
                self.q_inv_mod_ps.push(None);
            }
        }

        // compute Bainv2_{j,p} (mod p); they are used to update the roots when changing b_i to b_{i+1} in the polynomial
        self.bainv2ips.clear();
        for b in self.bis.iter() {
            self.bainv2ips.push(Vec::<Option<i64>>::new());
            for (i, &ainvp) in self.q_inv_mod_ps.iter().enumerate() {
                if let Some(ainvp) = ainvp {
                    let bainv2jp =
                        (b * (ainvp * 2_i64)).complete().mod_u(factorbase[i] as u32) as i64;
                    self.bainv2ips.last_mut().unwrap().push(Some(bainv2jp));
                } else {
                    self.bainv2ips.last_mut().unwrap().push(None);
                }
            }
        }

        // compute b
        self.b = self.bis.iter().sum();
        let c = (self.b.square_ref().complete() - n).div_exact(&self.a); // TODO: store in self.c

        // DEBUG: test B[i]
        for (i, q) in qis.iter().enumerate() {
            debug_assert!(
                (self.bis[i].clone().square() - n.clone())
                    .is_divisible(&Integer::from(*q as u32).square())
            );
            debug_assert!(
                (self.b.clone().square() - n.clone())
                    .is_divisible(&Integer::from(*q as u32).square())
            );
        }
        for (i, q) in qis.iter().enumerate() {
            for (j, b) in self.bis.iter().enumerate() {
                if i == j {
                    continue;
                }
                debug_assert!(b.clone().is_divisible(&Integer::from(*q as u32).square()));
            }
        }
        debug_assert!((self.b.clone().square() - n.clone()).is_divisible(&self.q.clone().square()));

        // compute roots of polynomial modulo p in factorbase
        self.roots.clear();
        for (i, &p) in factorbase.iter().enumerate() {
            // TODO: factor out into "roots of polynomial"; update root updates!
            if let Some(ainvp) = self.q_inv_mod_ps[i] {
                let roots = (
                    (ainvp * (roots[i] - &self.b).complete()).mod_u(p as u32) as i64,
                    (ainvp * (-roots[i] - &self.b).complete()).mod_u(p as u32) as i64,
                );
                self.roots.push(Some(roots));
                //debug_assert!(((self.q.clone() * roots.0 + self.b.clone()).square() - n.clone()).is_divisible_u(p as u32));
                //debug_assert!(((self.q.clone() * roots.1 + self.b.clone()).square() - n.clone()).is_divisible_u(p as u32));
            } else {
                // q = 0 (mod p) => we have a linear polynomial
                if let Some(root) = Self::root_of_linear_polynomial_mod_p(&self.b, &c, p) {
                    self.roots.push(Some((root, root)));
                }
                //else if c.is_divisible_u(p)
                else {
                    // if poly = c (p), then either there is no zero or the polynomial is 0
                    self.roots.push(None);
                }
            }
        }
    }

    // returns the next polynomial and its roots modulo the primes in the factorbase
    pub fn next_polynomial(&mut self) -> (Polynomial, &Vec<Option<(i64, i64)>>) {
        self.num_polynomials += 1;

        // the first polynomial has already been computed in initialize_new_set_of_polynomials()
        if self.j == 0 {
            self.j += 1;
            let b = self.b.clone();
            let c = (b.square_ref().complete() - self.n).div_exact(&self.a);
            debug_assert_eq!(b.clone().square() - self.a.clone() * c.clone(), *self.n);
            return (
                Polynomial {
                    a: self.a.clone(),
                    b,
                    c,
                    q_inverse: self.q_inverse_mod_n.clone(),
                },
                &self.roots,
            );
        }
        // after the last polynomial:
        // initialize_new_set_of_polynomials(index_thread)
        if self.j == 1 << (self.num_factors - 1) {
            // generate new aself.num_a += 1;
            if self.num_a >= self.list_of_qis.len() {
                panic!("need completely new set of q_i's.");
            }
            self.precompute_polynomial_data_for_q(self.n, self.factorbase, self.n_roots);
            let b = self.b.clone();
            let c = (b.square_ref().complete() - self.n).div_exact(&self.a);
            debug_assert_eq!(b.clone().square() - self.a.clone() * c.clone(), *self.n);
            self.j = 1;
            self.num_a += 1;
            return (
                Polynomial {
                    a: self.a.clone(),
                    b,
                    c,
                    q_inverse: self.q_inverse_mod_n.clone(),
                },
                &self.roots,
            );
        }

        let nu = (self.j * 2).trailing_zeros() as usize;
        let rounded_exponent = if self.j.is_multiple_of(1 << nu) {
            self.j / (1 << nu)
        } else {
            (self.j / (1 << nu)) + 1
        };
        self.j += 1;
        debug_assert!(1 <= nu && nu <= (1 << self.num_factors));
        let nu = nu - 1;
        if rounded_exponent % 2 == 0 {
            self.b += &self.bis[nu];
            self.b += &self.bis[nu];
        } else {
            self.b -= &self.bis[nu];
            self.b -= &self.bis[nu];
        }
        let b = self.b.clone();
        let c = (b.square_ref().complete() - self.n).div_exact(&self.a);
        debug_assert_eq!(b.clone().square() - self.a.clone() * c.clone(), *self.n); // discriminant of polynomial should be n

        // update roots with new b, old a
        for (index_p, roots) in self.roots.iter_mut().enumerate() {
            let p: i64 = self.factorbase[index_p];
            if self.q_inv_mod_ps[index_p].is_none() {
                // double root, i.e., we have a linear polynomial (really? it only means discriminant is 0)
                if let Some(root) = Self::root_of_linear_polynomial_mod_p(&b, &c, p) {
                    // TODO: prime divisors of b can change (become less)
                    *roots = Some((root, root));
                    //println!("p = {p}: root = {root}");
                } else {
                    *roots = None;
                }
            } else if let Some(roots_) = *roots
                && let Some(bainv2ip) = self.bainv2ips[nu][index_p]
            {
                let mut new_roots: (i64, i64) = if rounded_exponent % 2 != 0 {
                    (roots_.0 + bainv2ip, roots_.1 + bainv2ip)
                } else {
                    (roots_.0 - bainv2ip, roots_.1 - bainv2ip)
                };
                // micro optimization
                //let new_roots_ = (new_roots.0 % p, new_roots.1 % p);
                if new_roots.0 >= p {
                    new_roots.0 -= p;
                } else if new_roots.0 <= -p {
                    new_roots.0 += p;
                }
                if new_roots.1 >= p {
                    new_roots.1 -= p;
                } else if new_roots.1 <= -p {
                    new_roots.1 += p;
                }
                //debug_assert_eq!(new_roots_, (new_roots.0, new_roots.1));
                *roots = Some((new_roots.0, new_roots.1));
                //*roots = Some((new_roots.0 % p, new_roots.1 % p));
                // check that we really have roots of (ax + b)^2 - n
                debug_assert!(
                    (self.a.clone() * new_roots.0 * new_roots.0
                        + 2u32 * b.clone() * new_roots.0
                        + c.clone())
                    .is_divisible_u(p as u32)
                );
                debug_assert!(
                    (self.a.clone() * new_roots.1 * new_roots.1
                        + 2u32 * b.clone() * new_roots.1
                        + c.clone())
                    .is_divisible_u(p as u32)
                );
            }
        }
        (
            Polynomial {
                a: self.a.clone(),
                b,
                c,
                q_inverse: self.q_inverse_mod_n.clone(),
            },
            &self.roots,
        ) // TODO: return reference
    }
}

pub fn new_polynomial_generators<'a>(
    n: &'a Integer,
    sieve_interval_length: u64,
    num_threads: usize,
    factorbase: &'a Vec<i64>,
    roots: &'a Vec<i64>,
    prime_factors_for_q: &'a [i64],
) -> Vec<SIQSPolynomialData<'a>> {
    let num_thread_factors = (1u32..)
        .find(|k| Integer::from(2 * *k).binomial(*k) >= num_threads)
        .unwrap() as usize;
    //let num_thread_factors = 2_usize;
    let start_index_thread_factors = 4_usize; // TODO: should fit into factorbase, but otherwise, our number is too small
    // for each thread: compute machine specific divisors
    assert!(
        Integer::from(2 * num_thread_factors)
            .binomial(num_thread_factors as u32)
            .to_u32()
            .unwrap()
            >= num_threads as u32
    );
    let combinations = prime_factors_for_q
        .iter()
        .skip(start_index_thread_factors)
        //.chunks(num_thread_factors);
        .combinations(num_thread_factors);
    /*let factors = prime_factors_for_q
    .iter()
    .skip(start_index_thread_factors);*/
    let mut thread_polynomial_data = Vec::<SIQSPolynomialData>::with_capacity(num_threads);
    for (thread_number, combination) in combinations.into_iter().enumerate().take(num_threads) {
        //let mut index_larger_factor = start_index_thread_factors + 2 * num_threads;
        //for (thread_number, smaller_factor) in factors.enumerate().take(num_threads) {
        // ensures that two different threads differ in at least one thread specific factor
        let thread_specific_factors: Vec<i64> = combination.into_iter().copied().collect();
        //let thread_specific_factors: Vec<i64> = vec![*smaller_factor, prime_factors_for_q[index_larger_factor]];
        //println!("{thread_specific_factors:?}");
        //index_larger_factor -= 1;
        // for each thread: run initialize_new_set_of_polynomials
        thread_polynomial_data.push(SIQSPolynomialData::initialize_new_set_of_polynomials(
            &thread_specific_factors,
            thread_number,
            0,
            n,
            sieve_interval_length,
            factorbase,
            prime_factors_for_q,
            roots,
        ));
    }
    thread_polynomial_data
}
