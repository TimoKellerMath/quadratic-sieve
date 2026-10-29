use crate::number_theory::{lift_square_root_mod_q2, modular_inverse_u32};
use crate::polynomial_generator::{Polynomial, Roots};
use core::num::NonZero;
use itertools::Itertools;
use log::{debug, trace};
use rug::{Complete, Integer};
use std::num::NonZeroU32;

#[inline]
fn product_u32_to_integer(vector: &[u32]) -> Integer {
    vector.iter().fold(Integer::from(1), |acc, &x| acc * x)
}

#[inline]
fn product_refu32_to_f32(vector: &[&u32]) -> f32 {
    vector.iter().map(|&&x| x as f32).product()
}

/// The polynomial generator of one sieving thread. It generates families of
/// polynomials Q(x) = a x² + 2 b x + c with b² − a c = n, where all 2^(s−1)
/// polynomials of a family share a = q² and q is a product of s factor-base primes:
/// a combination of primes specific to the thread, which keeps the a of different
/// threads apart, and further primes chosen so that a comes close to its ideal size
/// √(2n) / M for the sieve interval [−M, M). Within a family, the roots modulo the
/// factor base are updated by additions. The roots are kept as offsets into the
/// interval, see [`Roots`].
pub struct SIQSPolynomialData<'a> {
    thread_number: usize,
    // the primes of q: those specific to the thread and their product, the number s
    // of further ones, and the number of all of them, which is the s of the docs
    thread_specific_factors: Vec<u32>,
    prod_thread_specific_factors: Integer,
    s: usize,
    num_factors: usize,
    // the choices of the primes of q, best first, and the index of the next one
    list_of_qis: Vec<Vec<u32>>,
    num_a: usize,
    // for each prime q_i of q: B_i with B_i² ≡ n (mod q_i²) and B_i ≡ 0 (mod q_j²) for
    // j ≠ i, so that the b = Σ ±B_i are the square roots of n modulo a
    bis: Vec<Integer>,
    // a⁻¹ mod p for each factor-base prime p, or None if p | a or p ≤ 2
    q_inv_mod_ps: Vec<Option<NonZeroU32>>,
    // bainv2ips[i][p] = 2 B_i a⁻¹ mod p for each factor-base prime p, by which the
    // roots change when B_i changes its sign in b. A plain u32 with a dummy 0 where
    // q_inv_mod_ps is None, since an Option would double the memory traffic of the
    // root update.
    bainv2ips: Vec<Vec<u32>>,
    // the roots of the current polynomial modulo the factor-base primes, as offsets
    // into the sieve interval
    roots: Roots,
    // the indices of the primes dividing a, where Q has a linear root
    linear_roots: Vec<usize>,
    // the half-length M of the sieve interval [−M, M)
    m: u64,

    // the number of polynomials of the current family generated so far
    j: usize,
    a: Integer,
    q: Integer,
    q_inverse_mod_n: Integer,
    // b of the current polynomial, and c of the first one of the family
    b: Integer,
    c: Integer,

    // n, the factor base and the square roots of n modulo its primes
    n: &'a Integer,
    factorbase: &'a [u32],
    n_roots: &'a [u32],
    // the primes from which q is built
    prime_factors_for_q: &'a [u32],
    // the ideal size of q, from which list_of_qis is computed
    total_q_size: f64,
    // how far the window of primes for q has moved towards larger primes, after the
    // lists of a before were used up
    window_offset: usize,
}

impl<'a> SIQSPolynomialData<'a> {
    // the further primes of q are chosen from a window of 2 Q_RANGE primes around
    // their ideal size
    const Q_RANGE: usize = 10;

    fn initialize_new_set_of_polynomials(
        thread_specific_factors: &[u32],
        thread_number: usize,
        n: &'a Integer,
        sieve_interval_length: u64,
        factorbase: &'a [u32],
        prime_factors_for_q: &'a [u32],
        roots: &'a [u32],
    ) -> SIQSPolynomialData<'a> {
        // the ideal q = √a for a = √(2n) / M
        let total_q_size = ((2.0 * n.to_f64()).sqrt() / sieve_interval_length as f64).sqrt();
        let mut polynomial_data = SIQSPolynomialData {
            thread_number,
            j: 0,
            s: 0,
            num_factors: 0,
            thread_specific_factors: thread_specific_factors.to_vec(),
            prod_thread_specific_factors: product_u32_to_integer(thread_specific_factors),
            q: Integer::from(1),
            q_inverse_mod_n: Integer::from(1),
            list_of_qis: Vec::new(),
            num_a: 0,
            bis: Vec::new(),
            q_inv_mod_ps: Vec::with_capacity(factorbase.len()),
            bainv2ips: Vec::new(),
            a: Integer::from(0),
            b: Integer::from(0),
            c: Integer::from(0),
            roots: Roots::default(),
            linear_roots: Vec::new(),
            m: sieve_interval_length,
            n,
            factorbase,
            n_roots: roots,
            prime_factors_for_q,
            total_q_size,
            window_offset: 0,
        };
        polynomial_data.compute_list_of_factors_of_q(total_q_size, prime_factors_for_q);
        polynomial_data.precompute_polynomial_data_for_q(n, factorbase, roots);
        debug!(
            "thread #{thread_number}: {} + {} = {} factors",
            thread_specific_factors.len(),
            polynomial_data.s,
            polynomial_data.num_factors
        );
        polynomial_data
    }

    fn compute_average_size_of_q(&self, total_q_size: f64, s: usize) -> f32 {
        (total_q_size / self.prod_thread_specific_factors.to_f64()).powf(1.0 / s as f64) as f32
    }

    // The number s of further primes of q, and the index i of the first prime above
    // their average size: the largest s for which there are Q_RANGE primes on either
    // side of i above the thread-specific ones, or else the smallest s for which
    // there are Q_RANGE primes above i.
    fn compute_number_of_factors_of_q(
        &self,
        total_q_size: f64,
        prime_factors_for_q: &[u32],
    ) -> (usize, usize) {
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
                (s_min, i_min) = (s, i);
            } else {
                return (s_min, i_min);
            }
            s += 1;
        }
    }

    // Fills list_of_qis with the choices of s primes from the window around their
    // ideal size, each with the thread-specific primes, sorted by how close their
    // product comes to the ideal q.
    fn compute_list_of_factors_of_q(&mut self, total_q_size: f64, prime_factors_for_q: &[u32]) {
        let (s, i) = self.compute_number_of_factors_of_q(total_q_size, prime_factors_for_q);
        self.s = s;
        self.num_factors = s + self.thread_specific_factors.len();
        let range_size = Self::Q_RANGE;
        let n_primes = prime_factors_for_q.len();
        // q's prime factors must be larger than every thread-specific factor (so
        // they stay distinct from them) and must skip the -1 sentinel at index 0;
        // `lo` is the first factor-base index that satisfies this.
        let tsf_last = *self.thread_specific_factors.last().unwrap();
        let lo = prime_factors_for_q
            .iter()
            .position(|&p| p > tsf_last)
            .unwrap_or(0);
        // The window of `window` primes from which the combinations of `s` are picked,
        // near the ideal index `i`. Every index is clamped into [lo, n_primes), so
        // that nothing underflows for small n (where the ideal q is tiny, which pushes
        // `i` below range_size) or runs past a short factor base. window_offset
        // shifts the window towards larger primes once the lists of a before are
        // used up, which gives new combinations.
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
        let total_q_size = total_q_size as f32;
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
            self.list_of_qis.push(new_qis);
        }
        debug!(
            "thread #{}: {} q's",
            self.thread_number,
            self.list_of_qis.len()
        );
    }

    // The root of the sieving polynomial modulo a prime p | a, where it is linear:
    // a x^2 + 2 b x + c ≡ 2 b x + c (mod p). 2b is invertible, since p | b would
    // imply p | kn, which the q-primes exclude. None for p <= 2.
    fn linear_root_mod_p(b: &Integer, c: &Integer, p: u32) -> Option<u32> {
        if p <= 2 {
            return None;
        }
        let twice_b = (2 * b.mod_u(p) as u64 % p as u64) as u32;
        let inverse = modular_inverse_u32(twice_b, p).expect("2b is invertible mod p for p | a");
        // x = -c / (2b) mod p
        let minus_c = (p - c.mod_u(p)) % p;
        let root = (minus_c as u64 * inverse as u64 % p as u64) as u32;
        debug_assert!((Integer::from(2) * b * root + c).is_divisible_u(p));
        Some(root)
    }

    // The offset (r + M) mod p into the sieve interval [−M, M) of a root r modulo p:
    // position r + M of the interval stands for x = r.
    #[inline]
    fn offset(m: u64, root: u32, p: u32) -> u32 {
        ((root as u64 + m) % p as u64) as u32
    }

    // The root r modulo p of an offset (r + M) mod p, the inverse of `offset`.
    fn root_of_offset(m: u64, offset: u32, p: u32) -> u32 {
        ((offset as u64 + p as u64 - m % p as u64) % p as u64) as u32
    }

    // The roots of the first polynomial of the current a modulo every factor-base
    // prime, from the square roots `n_roots` of n: r = a^-1 (±sqrt(n) - b) (mod p),
    // as offsets into the sieve interval.
    fn compute_roots(&mut self, factorbase: &[u32], n_roots: &[u32]) {
        self.roots.clear();
        assert!(factorbase.len() == self.q_inv_mod_ps.len() && factorbase.len() == n_roots.len());
        let m = self.m;
        for ((&p, q_inv), &root) in factorbase.iter().zip(&self.q_inv_mod_ps).zip(n_roots) {
            let roots = match q_inv {
                Some(ainvp) => {
                    let (p64, ainvp) = (p as u64, ainvp.get() as u64);
                    let b = self.b.mod_u(p) as u64;
                    let root = root as u64;
                    Some((
                        Self::offset(m, ((root + p64 - b) % p64 * ainvp % p64) as u32, p),
                        Self::offset(m, ((2 * p64 - root - b) % p64 * ainvp % p64) as u32, p),
                    ))
                }
                None => Self::linear_root_mod_p(&self.b, &self.c, p).map(|root| {
                    let offset = Self::offset(m, root, p);
                    (offset, offset)
                }),
            };
            self.roots.push(roots);
        }
    }

    // Switches to the next a of the list: computes q⁻¹ mod n, the B_i, a⁻¹ and
    // 2 B_i a⁻¹ modulo the factor base, and the first polynomial of the family and its
    // roots.
    fn precompute_polynomial_data_for_q(&mut self, n: &Integer, factorbase: &[u32], roots: &[u32]) {
        trace!("thread #{}: next a", self.thread_number);
        let qis = &self.list_of_qis[self.num_a];
        self.num_a += 1;
        self.q = product_u32_to_integer(qis);
        self.a = self.q.square_ref().complete();
        self.q_inverse_mod_n = self.q.invert_ref(n).unwrap().complete();

        // B_i = (a / q_i²) γ_i with γ_i ≡ √n (a / q_i²)⁻¹ (mod q_i²)
        self.bis.clear();
        for q in qis {
            let a_div_q = self.q.div_exact_u_ref(*q).complete();
            let root_q: u32 = roots[factorbase.iter().position(|&p| p == *q).unwrap()];
            let a_div_q_squared = a_div_q.square();
            let q_squared = Integer::from(*q).square();
            let root_mod_q_squared =
                lift_square_root_mod_q2(n, &Integer::from(root_q), &Integer::from(*q)).unwrap();
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

        // a⁻¹ mod p, where it exists
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
        self.linear_roots.clear();
        self.linear_roots.extend(
            (0..factorbase.len()).filter(|&i| factorbase[i] > 2 && self.q_inv_mod_ps[i].is_none()),
        );

        // 2 B_i a⁻¹ mod p
        self.bainv2ips.clear();
        for b in self.bis.iter() {
            self.bainv2ips.push(Vec::with_capacity(factorbase.len()));
            let bainv2ips = self.bainv2ips.last_mut().unwrap();
            for (&ainvp, &p) in self.q_inv_mod_ps.iter().zip(factorbase) {
                if let Some(ainvp) = ainvp {
                    let bainv2jp = (b.mod_u(p) as u64 * (ainvp.get() as u64 * 2) % p as u64) as u32;
                    bainv2ips.push(bainv2jp);
                } else {
                    // dummy: q_inv_mod_ps is None here; it must stay 0, since the
                    // root update adds it before replacing these roots by the
                    // linear ones
                    bainv2ips.push(0);
                }
            }
        }

        // the first polynomial of the family: b = Σ B_i
        self.b = self.bis.iter().sum();
        self.c = (self.b.square_ref().complete() - n).div_exact(&self.a);

        for (i, q) in qis.iter().enumerate() {
            debug_assert!(
                (self.bis[i].clone().square() - n.clone())
                    .is_divisible(&Integer::from(*q).square())
            );
            debug_assert!(
                (self.b.clone().square() - n.clone()).is_divisible(&Integer::from(*q).square())
            );
        }
        for (i, q) in qis.iter().enumerate() {
            for (j, b) in self.bis.iter().enumerate() {
                if i == j {
                    continue;
                }
                debug_assert!(b.clone().is_divisible(&Integer::from(*q).square()));
            }
        }
        debug_assert!((self.b.clone().square() - n.clone()).is_divisible(&self.q.clone().square()));

        self.compute_roots(factorbase, roots);
    }

    /// The next polynomial and its roots modulo the factor-base primes. After the last
    /// polynomial of a family comes the first of the next a, and after the last a of
    /// the list, the first of a new list, from larger primes.
    pub fn next_polynomial(&mut self) -> (Polynomial<'_>, &Roots) {
        // the first polynomial of the family, computed with its a
        if self.j == 0 {
            self.j += 1;
            let b = self.b.clone();
            let c = self.c.clone();
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
        // after the last polynomial of the family, switch to the next a
        if self.j == 1 << (self.num_factors - 1) {
            if self.num_a >= self.list_of_qis.len() {
                // all a of the list are used up: shift the window of primes towards
                // larger ones for a new list
                self.window_offset += Self::Q_RANGE;
                let prime_factors_for_q = self.prime_factors_for_q;
                self.compute_list_of_factors_of_q(self.total_q_size, prime_factors_for_q);
                self.num_a = 0;
            }
            self.precompute_polynomial_data_for_q(self.n, self.factorbase, self.n_roots);
            let b = self.b.clone();
            let c = self.c.clone();
            debug_assert_eq!(b.clone().square() - self.a.clone() * c.clone(), *self.n);
            self.j = 1;
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
        debug_assert_eq!(b.clone().square() - self.a.clone() * c.clone(), *self.n);

        // Update the roots for the new b, all but those of −1 and 2, which have none:
        // add or subtract 2 B_ν a⁻¹; the offsets change like the roots. The primes
        // dividing a have a dummy 0 there, so they keep their roots, which are
        // replaced by the linear ones below.
        let len = self.factorbase.len();
        assert!(self.roots.len() == len && self.bainv2ips[nu].len() == len);
        let (r1, r2) = (&mut self.roots.r1[2..], &mut self.roots.r2[2..]);
        let (primes, deltas) = (&self.factorbase[2..], &self.bainv2ips[nu][2..]);
        update_roots(r1, r2, deltas, primes, rounded_exponent % 2 != 0);
        let m = self.m;
        for &i in &self.linear_roots {
            let p = self.factorbase[i];
            let root = Self::linear_root_mod_p(&b, &c, p).expect("p > 2");
            let offset = Self::offset(m, root, p);
            (self.roots.r1[i], self.roots.r2[i]) = (offset, offset);
        }
        // check that they are roots of Q
        debug_assert!((2..len).all(|i| {
            let p = self.factorbase[i];
            [self.roots.r1[i], self.roots.r2[i]].iter().all(|&offset| {
                let root = Self::root_of_offset(m, offset, p);
                (self.a.clone() * root * root + 2u32 * b.clone() * root + c.clone())
                    .is_divisible_u(p)
            })
        }));
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

    // The Gray code step to the next polynomial of the family: for 2^ν ∥ 2j, b changes
    // by 2 B_ν, with the sign (−1)^⌈j / 2^ν⌉. Returns ⌈j / 2^ν⌉ and the index ν − 1
    // of B_ν, and advances j.
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

/// Adds `deltas[i]` to the roots `r1[i]` and `r2[i]` modulo `primes[i]` if `add`,
/// else subtracts it, for roots and deltas below their primes, without SIMD: for
/// builds without AVX2, and for the rest after the vectors.
fn update_roots_scalar(r1: &mut [u32], r2: &mut [u32], deltas: &[u32], primes: &[u32], add: bool) {
    for (((r1, r2), &delta), &p) in r1.iter_mut().zip(r2.iter_mut()).zip(deltas).zip(primes) {
        if add {
            // r + delta < 2p, and of it and r + delta − p, the one below p is the
            // smaller unsigned
            let (s1, s2) = (*r1 + delta, *r2 + delta);
            *r1 = s1.min(s1.wrapping_sub(p));
            *r2 = s2.min(s2.wrapping_sub(p));
        } else {
            // r − delta wraps below 0, and then r − delta + p is the smaller unsigned
            let (d1, d2) = (r1.wrapping_sub(delta), r2.wrapping_sub(delta));
            *r1 = d1.min(d1.wrapping_add(p));
            *r2 = d2.min(d2.wrapping_add(p));
        }
    }
}

/// [`update_roots_scalar`] without SIMD.
#[cfg(not(target_feature = "avx2"))]
fn update_roots(r1: &mut [u32], r2: &mut [u32], deltas: &[u32], primes: &[u32], add: bool) {
    update_roots_scalar(r1, r2, deltas, primes, add);
}

/// [`update_roots_scalar`] for 8 primes at a time.
#[cfg(target_feature = "avx2")]
fn update_roots(r1: &mut [u32], r2: &mut [u32], deltas: &[u32], primes: &[u32], add: bool) {
    use std::arch::x86_64::*;
    let n = r1.len();
    assert!(r2.len() == n && deltas.len() == n && primes.len() == n);
    let mut i = 0;
    while i + 8 <= n {
        // SAFETY: AVX2 is enabled at compile time, and i + 8 <= n, the length of all
        // four slices
        unsafe {
            let delta = _mm256_loadu_si256(deltas.as_ptr().add(i).cast());
            let p = _mm256_loadu_si256(primes.as_ptr().add(i).cast());
            for roots in [r1.as_mut_ptr().add(i), r2.as_mut_ptr().add(i)] {
                let r = _mm256_loadu_si256(roots.cast());
                let r = if add {
                    let s = _mm256_add_epi32(r, delta);
                    _mm256_min_epu32(s, _mm256_sub_epi32(s, p))
                } else {
                    let d = _mm256_sub_epi32(r, delta);
                    _mm256_min_epu32(d, _mm256_add_epi32(d, p))
                };
                _mm256_storeu_si256(roots.cast(), r);
            }
        }
        i += 8;
    }
    update_roots_scalar(&mut r1[i..], &mut r2[i..], &deltas[i..], &primes[i..], add);
}

/// One polynomial generator per sieving thread, for n with the given `factorbase`,
/// the square roots `roots` of n modulo it and the interval [−M, M), M =
/// `sieve_interval_length`. The q of each generator are products of primes from
/// `prime_factors_for_q`, a subset of the factor base, which include a combination of
/// primes specific to the generator.
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
    // the thread-specific factors start at the fifth prime, which every factor base
    // from the parameter table (at least 100 primes) leaves room for
    let start_index_thread_factors = 4;
    assert!(
        prime_factors_for_q.len() >= start_index_thread_factors + num_thread_factors,
        "factor base too small for {num_threads} threads"
    );
    // enough combinations of thread-specific primes for all threads
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
        .combinations(num_thread_factors);
    let mut thread_polynomial_data = Vec::<SIQSPolynomialData>::with_capacity(num_threads);
    for (thread_number, combination) in combinations.into_iter().enumerate().take(num_threads) {
        // two threads differ in at least one thread-specific prime
        let thread_specific_factors: Vec<u32> = combination.into_iter().copied().collect();
        thread_polynomial_data.push(SIQSPolynomialData::initialize_new_set_of_polynomials(
            &thread_specific_factors,
            thread_number,
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

    // next_polynomial makes a new list of a, by advancing window_offset, once the
    // list is used up. That takes millions of polynomials for a realistic n, so test
    // the mechanism directly: advancing window_offset and recomputing must shift the
    // window of primes and thus the a.
    #[test]
    fn test_window_offset_shifts_generated_as() {
        // The 202-bit example: large enough that the index of the q-primes lands well
        // past Q_RANGE (a smaller n would underflow the i - range_size index math).
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

        // advance the window and recompute, as next_polynomial does once the list is
        // used up: the a must change
        generator.window_offset += SIQSPolynomialData::Q_RANGE;
        generator.compute_list_of_factors_of_q(generator.total_q_size, &factorbase);
        let after = generator.list_of_qis.clone();

        assert_ne!(
            before, after,
            "advancing window_offset did not change the generated a coefficients"
        );
    }

    // The first switch to a new a must not rebuild the a the constructor already
    // used, which would sieve its whole family of polynomials a second time.
    #[test]
    fn test_polynomials_do_not_repeat() {
        let n = "6427752177035961102167848371107669985402627402189138248671463"
            .parse::<Integer>()
            .unwrap();
        let factorbase = make_factorbase(&n, 1500);
        let roots = square_roots_mod_factorbase(&n, &factorbase);
        let mut generators =
            new_polynomial_generators(&n, 65536, 1, &factorbase, &roots, &factorbase);
        let generator = &mut generators[0];
        // three families of 2^(num_factors - 1) polynomials each
        let count = 3 << (generator.num_factors - 1);
        let mut seen = std::collections::HashSet::new();
        for i in 0..count {
            let (polynomial, _) = generator.next_polynomial();
            assert!(
                seen.insert((polynomial.a.clone(), polynomial.b.clone())),
                "polynomial {i} repeats an earlier one"
            );
        }
    }

    // Across whole families, every root solves Q(r) ≡ 0 (mod p), as an offset into
    // the interval, a prime has a single root exactly when it divides a, and
    // c = (b^2 - n)/a is exact.
    #[test]
    fn polynomials_and_roots_are_consistent() {
        let n = "6427752177035961102167848371107669985402627402189138248671463"
            .parse::<Integer>()
            .unwrap();
        let factorbase = make_factorbase(&n, 1500);
        let n_roots = square_roots_mod_factorbase(&n, &factorbase);
        let mut generators =
            new_polynomial_generators(&n, 65536, 1, &factorbase, &n_roots, &factorbase);
        let generator = &mut generators[0];
        let count = 3 << (generator.num_factors - 1);
        for _ in 0..count {
            let (polynomial, roots) = generator.next_polynomial();
            let (a, b, c) = (polynomial.a, &polynomial.b, &polynomial.c);
            assert_eq!(b.clone().square() - a.clone() * c, n);
            for (i, &p) in factorbase.iter().enumerate() {
                let Some((r1, r2)) = roots.get(i) else {
                    assert!(p <= 2, "no roots mod {p}");
                    continue;
                };
                for r in [r1, r2] {
                    assert!(r < p, "root {r} mod {p} is not reduced");
                    // offset r stands for x = r - M, with M = 65536
                    let x = r as i32 - 65536;
                    let q_x = a.clone() * x * x + b.clone() * 2u32 * x + c;
                    assert_eq!(q_x.mod_u(p), 0, "Q({x}) != 0 mod {p}");
                }
                assert_eq!(r1 == r2, a.is_divisible_u(p), "number of roots mod {p}");
            }
        }
    }

    // a = q^2 with q the product of the q-primes, and B_i^2 ≡ n (mod q_i^2) while
    // B_i ≡ 0 (mod q_j^2) for j != i, so b = sum of B_i is a square root of n mod a.
    #[test]
    fn b_i_are_square_roots_of_n_mod_their_q_squared() {
        let n = "6427752177035961102167848371107669985402627402189138248671463"
            .parse::<Integer>()
            .unwrap();
        let factorbase = make_factorbase(&n, 1500);
        let n_roots = square_roots_mod_factorbase(&n, &factorbase);
        let mut generators =
            new_polynomial_generators(&n, 65536, 1, &factorbase, &n_roots, &factorbase);
        let generator = &mut generators[0];
        let family = 1usize << (generator.num_factors - 1);
        for k in 0..3 * family {
            let a = generator.next_polynomial().0.a.clone();
            if k % family != 0 {
                continue;
            }
            // the first polynomial of a family: check its a and B_i
            let qis = &generator.list_of_qis[generator.num_a - 1];
            let q = qis.iter().fold(Integer::from(1), |q, &q_i| q * q_i);
            assert_eq!(a, q.square());
            assert_eq!(generator.bis.len(), qis.len());
            for (i, b_i) in generator.bis.iter().enumerate() {
                for (j, &q_j) in qis.iter().enumerate() {
                    let residue = if i == j {
                        b_i.clone().square() - &n
                    } else {
                        b_i.clone()
                    };
                    assert!(
                        residue.is_divisible(&Integer::from(q_j).square()),
                        "B_{i} is wrong mod q_{j}^2"
                    );
                }
            }
        }
    }

    // The root of the linear polynomial 2 b x + c modulo p | a is reduced and
    // correct for every c, including c ≡ 0, where it used to be p (ceb1033).
    #[test]
    fn linear_root_is_reduced_and_correct() {
        let p = 101u32;
        for b in [Integer::from(12345), Integer::from(-12345)] {
            for residue in 0..p {
                for c in [
                    Integer::from(residue + 7 * p),
                    Integer::from(residue) - 1000 * p,
                ] {
                    let root = SIQSPolynomialData::linear_root_mod_p(&b, &c, p).unwrap();
                    assert!(root < p, "root {root} mod {p} is not reduced");
                    assert_eq!((b.clone() * 2u32 * root + &c).mod_u(p), 0);
                }
            }
            assert_eq!(
                SIQSPolynomialData::linear_root_mod_p(&b, &Integer::from(3 * p), p),
                Some(0)
            );
        }
        // no roots for the -1 entry and modulo 2
        for p in [0, 2] {
            assert_eq!(
                SIQSPolynomialData::linear_root_mod_p(&Integer::from(5), &Integer::from(3), p),
                None
            );
        }
    }

    // The root update, scalar and the one compiled in, adds and subtracts modulo
    // each prime, for roots and deltas anywhere below their primes.
    #[test]
    fn root_update_is_modular() {
        let mut seed = 0x2545_F491_4F6C_DD1Du64;
        let mut random = |bound: u32| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed % bound as u64) as u32
        };
        // primes up to the largest factor-base primes, and a length that leaves a
        // rest after the vectors
        let primes: Vec<u32> = (0..1003)
            .map(|i| [3, 5, 13, 65537, 1_179_641, 16_777_213][i % 6])
            .collect();
        let deltas: Vec<u32> = primes.iter().map(|&p| random(p)).collect();
        let r1: Vec<u32> = primes.iter().map(|&p| random(p)).collect();
        let mut r2: Vec<u32> = primes.iter().map(|&p| random(p)).collect();
        // the extremes 0 and p - 1
        r2[..6].copy_from_slice(&[0, 4, 0, 65536, 0, 16_777_212]);
        for add in [false, true] {
            let (mut v1, mut v2) = (r1.clone(), r2.clone());
            let (mut s1, mut s2) = (r1.clone(), r2.clone());
            update_roots(&mut v1, &mut v2, &deltas, &primes, add);
            update_roots_scalar(&mut s1, &mut s2, &deltas, &primes, add);
            for i in 0..primes.len() {
                let (p, d) = (primes[i] as u64, deltas[i] as u64);
                let want = |r: u32| (if add { r as u64 + d } else { r as u64 + p - d } % p) as u32;
                assert_eq!(
                    (v1[i], v2[i]),
                    (want(r1[i]), want(r2[i])),
                    "add {add}, prime {p}"
                );
                assert_eq!(
                    (s1[i], s2[i]),
                    (v1[i], v2[i]),
                    "add {add}, prime {p}, scalar"
                );
            }
        }
    }

    // Small n: the factor base is short and the ideal q is tiny, so the window of
    // primes for q sits near the start of the factor base. Building a generator must
    // not panic (it used to underflow `i - range_size` and trip the window assert)
    // and must produce a usable set of distinct primes for a.
    #[test]
    fn test_small_n_generator_builds() {
        let p = ((Integer::from(1) << 16u32) + 12345u32).next_prime();
        let q = ((Integer::from(1) << 16u32) + 67890u32).next_prime();
        let n = p * q;
        let factorbase = make_factorbase(&n, 100);
        let roots = square_roots_mod_factorbase(&n, &factorbase);
        let generators = new_polynomial_generators(&n, 65536, 1, &factorbase, &roots, &factorbase);
        let g = &generators[0];
        assert!(g.s >= 2, "need at least two q-factors, got s={}", g.s);
        assert!(
            !g.list_of_qis.is_empty(),
            "no a coefficients generated for small n"
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
