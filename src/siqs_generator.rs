use crate::constants::PREC;
use crate::format_color::*;
use crate::{debug_print,debug_println};
use crate::number_theory::{lift_square_root_mod_q2, modular_inverse_u32};
use crate::polynomial_generator::Polynomial;
use core::num::NonZero;
use std::num::NonZeroU32;
use itertools::{Itertools, izip};
use rug::{Complete, Float, Integer};

#[inline]
fn product_u32_to_integer(vector: &[u32]) -> Integer {
    vector.iter().fold(Integer::from(1), |acc, &x| acc * x)
}

#[inline]
fn product_refu32_to_f32(vector: &[&u32]) -> f32 {
    vector.iter().map(|&&x| x as f32).product()
}

// one for each thread
pub struct SIQSPolynomialData<'a> {
    thread_number: usize,
    s: usize,                          // #prime factors of q
    thread_specific_factors: Vec<u32>, // fixed for each thread
    prod_thread_specific_factors: Integer,
    num_factors: usize,
    list_of_qis: Vec<Vec<u32>>, // successive choices of remaining qi's
    num_a: usize,               // the num_a-th chosen a
    bis: Vec<Integer>, // for i = 1..s: B[i] = a/q[i] * gamma, gamma = sqrt(n mod p) * (a/q[i])^-1 (mod q[i])
    q_inv_mod_ps: Vec<Option<NonZeroU32>>, //  for all p \nmid a in factorbase: (a^-1 mod p)
    // Bainv2ips[i,p] = (2 * B[i] * (a^-1 mod p)) (mod p), for all p \nmid a in
    // factorbase. Plain u32 (0 dummy where p | a): validity is decided by
    // q_inv_mod_ps[p].is_none(), so an Option here would only double the memory
    // traffic of the per-polynomial root-update loop.
    bainv2ips: Vec<Vec<u32>>,
    roots: Vec<Option<(u32, u32)>>, // for all p \nmid a in factorbase: (root1,root2) = (ainv * (sqrt(n mod p) - b), ainv * (-sqrt(n mod p) - b)) (mod p)

    j: usize, // index of polynomial for fixed a, 1 <= j <= 2^(s-1) - 1,
    a: Integer,
    q: Integer,
    q_inverse_mod_n: Integer,
    b: Integer, // the b for j

    n: &'a Integer,
    factorbase: &'a [u32],
    n_roots: &'a [u32], // the roots of n modulo the primes in the factor base
    //sieve_interval_length: u64,
    prime_factors_for_q: &'a [u32], // we choose the q from this subset of the factorbase
    total_q_size: Float,            // target size of a = q^2, used to regenerate list_of_qis
    window_offset: usize,           // shift of the prime window when regenerating fresh a's
    pub num_polynomials: usize,     // record the number of polynomials used
}

impl<'a> SIQSPolynomialData<'a> {
    const Q_RANGE: usize = 10;
    //const RANGE_MULTIPLIER: usize = 3;

    fn initialize_new_set_of_polynomials(
        thread_specific_factors: &[u32],
        thread_number: usize,
        num_a: usize,
        n: &'a Integer,
        sieve_interval_length: u64,
        factorbase: &'a [u32],
        prime_factors_for_q: &'a [u32],
        roots: &'a [u32],
    ) -> SIQSPolynomialData<'a> {
        // compute size of "average" qi
        // q \approx sqrt((sqrt(2 * kn)/sieve_interval_length)
        let total_q_size = ((2f32 * Float::with_val(PREC, n.clone())).sqrt()
            / Float::with_val(PREC, sieve_interval_length))
        .sqrt();
        let mut polynomial_data = SIQSPolynomialData {
            thread_number,
            j: 0, // index of polynomial for fixed a, 1 <= j <= 2^(s-1) - 1,
            s: 0,
            num_factors: 0,
            thread_specific_factors: thread_specific_factors.to_vec(),
            prod_thread_specific_factors: product_u32_to_integer(thread_specific_factors),
            q: Integer::from(1),
            q_inverse_mod_n: Integer::from(1),
            list_of_qis: Vec::new(),
            num_a,                      // index of current element of list_of_qis
            bis: Vec::new(), // for i = 1..s: B[i] = a/q[i] * gamma, gamma = sqrt(n mod p) * (a/q[i])^-1 (mod q[i])
            q_inv_mod_ps: Vec::with_capacity(factorbase.len()), //  for all p \nmid a in factorbase: (a^-1 mod p)
            bainv2ips: Vec::new(), // Bainv2ips[i,p] = (2 * B[i] * (a^-1 mod p)) (mod p), for all p \nmid a in factorbase
            a: Integer::from(0),
            b: Integer::from(0), // the b for j,
            roots: Vec::with_capacity(factorbase.len()),
            n,
            factorbase,
            n_roots: roots,
            prime_factors_for_q,
            total_q_size: total_q_size.clone(),
            window_offset: 0,
            num_polynomials: 0,
        };
        polynomial_data.compute_list_of_factors_of_q(&total_q_size, prime_factors_for_q);
        polynomial_data.precompute_polynomial_data_for_q(n, factorbase, roots);
        debug_println!(
            "thread #{thread_number}: {} + {} = {} factors",
            thread_specific_factors.len(),
            polynomial_data.s,
            polynomial_data.num_factors
        );
        //print!("{}", format_color(format!("thread #{thread_number}: {} + {} = {} factors", thread_specific_factors.len(), polynomial_data.s, polynomial_data.num_factors), self.thread_number));
        polynomial_data
    }

    fn compute_average_size_of_q(&self, total_q_size: &Float, s: usize) -> f32 {
        (total_q_size.clone() / Float::with_val(PREC, self.prod_thread_specific_factors.clone()))
            .root(s as u32)
            .to_f32()
    }

    fn compute_number_of_factors_of_q(
        &self,
        total_q_size: &Float,
        prime_factors_for_q: &[u32],
    ) -> (usize, usize) {
        // fixed number of factors: 5
        /*let s = 7 - self.thread_specific_factors.len();
        let average_q_size: u32 = self.compute_average_size_of_q(total_q_size, s) as u32;
        let i = prime_factors_for_q.iter().position(|&p| p > average_q_size).expect("average q size too large for factorbase");
        (s, i)*/

        // compute maximum possible number of factors
        let mut s = 2_usize;
        let mut s_min;
        let mut i_min;
        // look for the smallest possible s
        loop {
            let average_q_size: u32 = self.compute_average_size_of_q(total_q_size, s) as u32;
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
            let average_q_size: u32 = self.compute_average_size_of_q(total_q_size, s) as u32;
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

    fn compute_list_of_factors_of_q(&mut self, total_q_size: &Float, prime_factors_for_q: &[u32]) {
        let (s, i) = self.compute_number_of_factors_of_q(total_q_size, prime_factors_for_q);
        self.s = s;
        self.num_factors = s + self.thread_specific_factors.len();
        let range_size = Self::Q_RANGE;
        //let range_size = Self::RANGE_MULTIPLIER * s;
        let n_primes = prime_factors_for_q.len();
        // q's prime factors must be larger than every thread-specific factor (so
        // they stay distinct from them) and must skip the -1 sentinel at index 0;
        // `lo` is the first factor-base index that satisfies this.
        let tsf_last = *self.thread_specific_factors.last().unwrap();
        let lo = prime_factors_for_q
            .iter()
            .position(|&p| p > tsf_last)
            .unwrap_or(0);
        // Window of `window` primes from which we pick combinations of `s`,
        // positioned near the ideal index `i`. Clamp every index into
        // [lo, n_primes) so the math can't underflow for small N (where the ideal
        // q is tiny, pushing `i` below range_size) or run past a short factor base.
        // window_offset shifts the window towards larger primes when a previous
        // batch of a's was exhausted, yielding fresh combinations.
        let window = (range_size * 2).min(n_primes.saturating_sub(lo)).max(s);
        let i_min = i.saturating_sub(range_size).max(lo);
        let max_start = n_primes.saturating_sub(window).max(lo);
        let start = (i_min + self.window_offset).clamp(lo, max_start);
        let take = window.min(n_primes - start);
        let combinations = prime_factors_for_q
            .iter()
            .skip(start)
            .take(take)
            .combinations(s);
        const SCALE: f32 = 65536.0;
        let prod_thread_specific_factors = self.prod_thread_specific_factors.to_f32();
        let total_q_size = total_q_size.to_f32();
        let quotient = prod_thread_specific_factors / total_q_size;
        let qis_with_quality = combinations.into_iter().map(|combination| {
            (
                combination.clone(),
                ((quotient * product_refu32_to_f32(combination.as_slice()))
                    .log2()
                    .abs()
                    * SCALE) as u32,
            )
        });
        let qis_by_quality = qis_with_quality
            .sorted_unstable_by_key(|(_, quality)| *quality)
            .map(|(combination, _)| combination);
        self.list_of_qis = Vec::new();
        for qis in qis_by_quality {
            let mut new_qis: Vec<u32> = self.thread_specific_factors.to_vec();
            for q in qis {
                new_qis.push(*q);
            }
            //let q = product_u32_to_integer(&new_qis);
            //let quality = (Float::with_val(PREC,q) / Float::with_val(PREC,total_q_size)).log2().abs();
            //println!("quality: {quality}");
            self.list_of_qis.push(new_qis);
        }
        debug_println!("{} q's", self.list_of_qis.len());
    }

    fn root_of_linear_polynomial_mod_p(b: &Integer, c: &Integer, p: u32) -> Option<u32> {
        if p <= 2 {
            return None;
        }
        let twice_b: Integer = (b << 1u32).complete();
        if let Ok(twice_b_inverse) = twice_b.invert(&Integer::from(p)) {
            // TODO: can this fail?
            let root1 = twice_b_inverse * c;
            let root = p - root1.mod_u(p as u32);
            //println!("root = {root}, b = {b}, c = {c}, p = {p}");
            debug_assert!((Integer::from(2) * b * root + c).is_divisible_u(p as u32));
            Some(root)
        } else {
            // if poly = c (p), then either there is no zero or the polynomial is 0
            None
        }
    }

    fn precompute_polynomial_data_for_q(&mut self, n: &Integer, factorbase: &[u32], roots: &[u32]) {
        debug_print!("{}", format_color("|", self.thread_number));
        let qis = &self.list_of_qis[self.num_a];
        self.q = product_u32_to_integer(qis);
        self.a = self.q.square_ref().complete();
        self.q_inverse_mod_n = self.q.invert_ref(n).unwrap().complete();

        // compute the corresponding B[i]'s with B[i]^2 = delta_{ij} * n (mod q[j])
        self.bis.clear();
        for q in qis {
            let a_div_q = self.q.div_exact_u_ref(*q as u32).complete();
            let root_q: u32 = roots[factorbase.iter().position(|&p| p == *q).unwrap()];
            let a_div_q_squared = a_div_q.square();
            let q_squared = Integer::from(*q).square();
            let root_mod_q_squared =
                lift_square_root_mod_q2(n, &Integer::from(root_q), &q_squared).unwrap(); // TODO: cache this!
            let mut gamma = ((root_mod_q_squared
                * a_div_q_squared.invert_ref(&q_squared).unwrap().complete())
                % q_squared.clone())
            .to_u32()
            .unwrap();
            let q_squared = q_squared.to_u32().unwrap();
            if gamma > (q_squared / 2) {
                gamma = q_squared - gamma;
            }
            self.bis.push(a_div_q_squared * gamma);
        }

        // compute a^-1 (mod p) if it exists
        self.q_inv_mod_ps.clear();
        for &p in factorbase {
            if p > 2
                && let Some(ainvp) = modular_inverse_u32(self.a.mod_u(p), p)
            {
                self.q_inv_mod_ps.push(Some(
                    NonZero::<u32>::new(ainvp).expect("modular inverse mod a prime is nonzero"),
                ));
            } else {
                self.q_inv_mod_ps.push(None);
            }
        }

        // compute Bainv2_{j,p} (mod p); they are used to update the roots when changing b_i to b_{i+1} in the polynomial
        self.bainv2ips.clear();
        for b in self.bis.iter() {
            self.bainv2ips
                .push(Vec::with_capacity(factorbase.len()));
            let bainv2ips = self.bainv2ips.last_mut().unwrap();
            for (&ainvp, &p) in izip!(&self.q_inv_mod_ps, factorbase) {
                if let Some(ainvp) = ainvp {
                    let bainv2jp =
                        (b.mod_u(p) as u64 * (ainvp.get() as u64 * 2) % p as u64) as u32;
                    bainv2ips.push(bainv2jp);
                } else {
                    bainv2ips.push(0); // dummy: q_inv_mod_ps is None here, never read
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
        assert!(factorbase.len() == self.q_inv_mod_ps.len() && factorbase.len() == roots.len());
        for (&p, q_inv, root) in izip!(factorbase, &self.q_inv_mod_ps, roots) {
            // TODO: factor out into "roots of polynomial"; update root updates!
            if let Some(ainvp) = q_inv {
                let roots = (
                    (ainvp.get() * (root - &self.b).complete()).mod_u(p as u32) as u32,
                    (ainvp.get() * (-(*root as i32) - &self.b).complete()).mod_u(p as u32) as u32,
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
    pub fn next_polynomial(&mut self) -> (Polynomial<'_>, &[Option<(u32, u32)>]) {
        self.num_polynomials += 1;

        // the first polynomial has already been computed in initialize_new_set_of_polynomials()
        if self.j == 0 {
            self.j += 1;
            let b = self.b.clone();
            let c = (b.square_ref().complete() - self.n).div_exact(&self.a);
            debug_assert_eq!(b.clone().square() - self.a.clone() * c.clone(), *self.n);
            return (
                Polynomial {
                    a: &self.a,
                    b,
                    c,
                    q_inverse: &self.q_inverse_mod_n,
                },
                &self.roots,
            );
        }
        // after the last polynomial:
        // initialize_new_set_of_polynomials(index_thread)
        if self.j == 1 << (self.num_factors - 1) {
            // generate new a
            if self.num_a >= self.list_of_qis.len() {
                // exhausted all a's for the current prime window: shift the window
                // towards larger primes and regenerate a fresh batch of a's instead
                // of aborting the whole factorization.
                self.window_offset += Self::Q_RANGE;
                let total_q_size = self.total_q_size.clone();
                let prime_factors_for_q = self.prime_factors_for_q;
                self.compute_list_of_factors_of_q(&total_q_size, prime_factors_for_q);
                self.num_a = 0;
            }
            self.precompute_polynomial_data_for_q(self.n, self.factorbase, self.n_roots);
            let b = self.b.clone();
            let c = (b.square_ref().complete() - self.n).div_exact(&self.a);
            debug_assert_eq!(b.clone().square() - self.a.clone() * c.clone(), *self.n);
            self.j = 1;
            self.num_a += 1;
            return (
                Polynomial {
                    a: &self.a,
                    b,
                    c,
                    q_inverse: &self.q_inverse_mod_n,
                },
                &self.roots,
            );
        }

        let (rounded_exponent, nu) = self.compute_nu_and_rounded_exponent();
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
        assert!(
            self.roots.len() == self.q_inv_mod_ps.len()
                && self.factorbase.len() == self.roots.len()
                && self.roots.len() == self.bainv2ips[nu].len()
        );
        for (roots, &p, q_inv, &bainv) in izip!(
            &mut self.roots,
            self.factorbase,
            &self.q_inv_mod_ps,
            &self.bainv2ips[nu]
        ) {
            if q_inv.is_none() {
                // double root, i.e., we have a linear polynomial (really? it only means discriminant is 0)
                if let Some(root) = Self::root_of_linear_polynomial_mod_p(&b, &c, p) {
                    // TODO: prime divisors of b can change (become less)
                    *roots = Some((root, root));
                    //println!("p = {p}: root = {root}");
                } else {
                    *roots = None;
                }
            } else if let Some(roots_) = *roots {
                let new_roots =
                    Self::new_roots_with_sign(roots_, bainv, p, rounded_exponent % 2 != 0);
                *roots = Some(new_roots);
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
                a: &self.a,
                b,
                c,
                q_inverse: &self.q_inverse_mod_n,
            },
            &self.roots,
        )
    }

    #[inline]
    fn new_roots_with_sign(roots: (u32, u32), b: u32, p: u32, sign: bool) -> (u32, u32) {
        if sign {
            let new_roots = (roots.0 + b, roots.1 + b);
            (
                if new_roots.0 >= p {
                    new_roots.0 - p
                } else {
                    new_roots.0
                },
                if new_roots.1 >= p {
                    new_roots.1 - p
                } else {
                    new_roots.1
                },
            )
        } else {
            let new_roots = (p + roots.0 - b, p + roots.1 - b);
            (
                if new_roots.0 >= p {
                    new_roots.0 - p
                } else {
                    new_roots.0
                },
                if new_roots.1 >= p {
                    new_roots.1 - p
                } else {
                    new_roots.1
                },
            )
        }
    }

    #[inline]
    fn compute_nu_and_rounded_exponent(&mut self) -> (usize, usize) {
        let nu = (self.j * 2).trailing_zeros() as usize;
        let rounded_exponent = if self.j.is_multiple_of(1 << nu) {
            self.j / (1 << nu)
        } else {
            (self.j / (1 << nu)) + 1
        };
        self.j += 1;
        debug_assert!(1 <= nu && nu <= (1 << self.num_factors));
        let nu = nu - 1;
        (rounded_exponent, nu)
    }

    #[cfg(test)]
    fn window_offset(&self) -> usize {
        self.window_offset
    }
}

pub fn new_polynomial_generators<'a>(
    n: &'a Integer,
    sieve_interval_length: u64,
    num_threads: usize,
    factorbase: &'a [u32],
    roots: &'a [u32],
    prime_factors_for_q: &'a [u32],
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
        let thread_specific_factors: Vec<u32> = combination.into_iter().copied().collect();
        //let thread_specific_factors: Vec<u32> = vec![*smaller_factor, prime_factors_for_q[index_larger_factor]];
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::factorbase::{make_factorbase, square_roots_mod_factorbase};

    // C makes next_polynomial regenerate a fresh batch of a coefficients (by
    // advancing window_offset) instead of panicking once the precomputed list is
    // used up. Driving full exhaustion needs millions of polynomials for a
    // realistic N, so test the mechanism directly: advancing window_offset and
    // recomputing must shift the prime-selection window and thus the a's.
    #[test]
    fn test_window_offset_shifts_generated_as() {
        // The 202-bit benchmark N: large enough that the q-factor index lands well
        // past Q_RANGE (a smaller N would underflow the i - range_size index math).
        let n = "6427752177035961102167848371107669985402627402189138248671463"
            .parse::<Integer>()
            .unwrap();
        let factorbase = make_factorbase(&n, 1500);
        let roots = square_roots_mod_factorbase(&n, &factorbase);
        let mut generators =
            new_polynomial_generators(&n, 65536, 1, &factorbase, &roots, &factorbase);
        let generator = &mut generators[0];

        assert_eq!(generator.window_offset(), 0);
        let before = generator.list_of_qis.clone();
        assert!(!before.is_empty());

        // Simulate exhaustion: advance the window and regenerate (as the new
        // branch in next_polynomial does) and confirm we get different a's.
        let total_q_size = generator.total_q_size.clone();
        generator.window_offset += SIQSPolynomialData::Q_RANGE;
        generator.compute_list_of_factors_of_q(&total_q_size, &factorbase);
        let after = generator.list_of_qis.clone();

        assert_ne!(
            before, after,
            "advancing window_offset did not change the generated a coefficients"
        );
    }

    // Small N: the factor base is short and the ideal q is tiny, so the
    // prime-selection window sits near the start of the factor base. Building a
    // generator must not panic (it used to underflow `i - range_size` and trip
    // the window assert) and must produce a usable set of distinct a-factors.
    #[test]
    fn test_small_n_generator_builds() {
        let p = ((Integer::from(1) << 16u32) + 12345u32).next_prime();
        let q = ((Integer::from(1) << 16u32) + 67890u32).next_prime();
        let n = p * q;
        let factorbase = make_factorbase(&n, 100);
        let roots = square_roots_mod_factorbase(&n, &factorbase);
        let generators =
            new_polynomial_generators(&n, 65536, 1, &factorbase, &roots, &factorbase);
        let g = &generators[0];
        assert!(g.s >= 2, "need at least two q-factors, got s={}", g.s);
        assert!(
            !g.list_of_qis.is_empty(),
            "no a coefficients generated for small N"
        );
        // every chosen q-factor must be a real factor-base prime (> 2) and the
        // factors within one a must be distinct
        for qis in &g.list_of_qis {
            assert_eq!(qis.len(), g.num_factors);
            for &qi in qis {
                assert!(qi > 2 && factorbase.contains(&qi));
            }
            let mut sorted = qis.clone();
            sorted.sort_unstable();
            sorted.dedup();
            assert_eq!(sorted.len(), qis.len(), "duplicate q-factor in a");
        }
    }
}
