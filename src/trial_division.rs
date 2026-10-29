use crate::constants::NUM_SKIP_PRIMES;
use crate::number_theory::{is_prime_u32, is_probable_prime_base2, pollard_rho_u64};
use crate::polynomial_generator::Roots;
use crate::relation::LargePrimes;
use rug::{Assign, Integer};
use std::ops::Range;

/// `pos % p` for a position pos < 2^24 and a prime 3 ≤ p < 2^24, without a
/// division, from `inverse` = 1/p as an f32: pos / p as an f32 errs by less than 1,
/// so its truncation q is floor(pos / p) or off by one, pos − q p lies in [−p, 2p),
/// and one correction in either direction reduces it. The AVX2 root check computes
/// the same in its lanes.
#[inline]
fn pos_mod_p(pos: u32, p: u32, inverse: f32) -> u32 {
    let q = (pos as f32 * inverse) as u32;
    // q p <= pos + p < 2^25
    let r = pos as i32 - (q * p) as i32;
    if r < 0 {
        (r + p as i32) as u32
    } else if r >= p as i32 {
        (r - p as i32) as u32
    } else {
        r as u32
    }
}

/// How the root check reduces a position pos < 2M modulo the primes of a range.
#[derive(Clone, Copy)]
enum Reduction {
    /// p ≤ M: pos mod p by [`pos_mod_p`].
    Full,
    /// M < p < 2M: pos mod p is pos or pos − p.
    Subtract,
    /// p > 2M: pos mod p is pos.
    None,
}

/// Appends to `divisors[k]` the indices i in `indices` for which pos ≡ `roots.r1[i]`
/// or `roots.r2[i]` (mod p) for pos = `positions[k]` and the prime p =
/// `factorbase[i]`, in increasing order. All primes of `indices` must be reducible
/// by `reduction`.
#[inline]
fn find_divisors_scalar(
    positions: &[u32],
    factorbase: &[u32],
    roots: &Roots,
    inverses: &[f32],
    indices: Range<usize>,
    reduction: Reduction,
    divisors: &mut [Vec<u32>],
) {
    for i in indices {
        let (p, r1, r2) = (factorbase[i], roots.r1[i], roots.r2[i]);
        for (&pos, divisors) in positions.iter().zip(divisors.iter_mut()) {
            let r = match reduction {
                Reduction::Full => pos_mod_p(pos, p, inverses[i]),
                Reduction::Subtract => {
                    if pos >= p {
                        pos - p
                    } else {
                        pos
                    }
                }
                Reduction::None => pos,
            };
            if r == r1 || r == r2 {
                divisors.push(i as u32);
            }
        }
    }
}

/// The root check of [`TrialDivision::find_divisors`] for the three ranges of
/// primes `ranges`, without SIMD.
#[cfg(not(target_feature = "avx2"))]
fn find_divisors(
    positions: &[u32],
    factorbase: &[u32],
    roots: &Roots,
    inverses: &[f32],
    ranges: [Range<usize>; 3],
    divisors: &mut [Vec<u32>],
) {
    let [full, subtract, none] = ranges;
    let check = |indices, reduction, divisors: &mut [Vec<u32>]| {
        find_divisors_scalar(
            positions, factorbase, roots, inverses, indices, reduction, divisors,
        )
    };
    check(full, Reduction::Full, divisors);
    check(subtract, Reduction::Subtract, divisors);
    check(none, Reduction::None, divisors);
}

/// The root check of [`TrialDivision::find_divisors`] for the three ranges of
/// primes `ranges`, 8 primes at a time, and the rest of each range scalar.
#[cfg(target_feature = "avx2")]
fn find_divisors(
    positions: &[u32],
    factorbase: &[u32],
    roots: &Roots,
    inverses: &[f32],
    ranges: [Range<usize>; 3],
    divisors: &mut [Vec<u32>],
) {
    use std::arch::x86_64::*;
    // the positions in all lanes, as integers and as floats (exact below 2^24)
    let lanes: Vec<(__m256i, __m256)> = positions
        .iter()
        // SAFETY: AVX2 is enabled at compile time
        .map(|&pos| unsafe { (_mm256_set1_epi32(pos as i32), _mm256_set1_ps(pos as f32)) })
        .collect();
    let [full, subtract, none] = ranges;
    for (indices, reduction) in [
        (full, Reduction::Full),
        (subtract, Reduction::Subtract),
        (none, Reduction::None),
    ] {
        let mut i = indices.start;
        while i + 8 <= indices.end {
            // SAFETY: AVX2 is enabled at compile time, and i + 8 <= indices.end <=
            // the length of every array, since the ranges lie within the factor base
            unsafe {
                let p = _mm256_loadu_si256(factorbase.as_ptr().add(i).cast());
                let r1 = _mm256_loadu_si256(roots.r1.as_ptr().add(i).cast());
                let r2 = _mm256_loadu_si256(roots.r2.as_ptr().add(i).cast());
                let inverse = _mm256_loadu_ps(inverses.as_ptr().add(i));
                for (&(pos, pos_f), divisors) in lanes.iter().zip(divisors.iter_mut()) {
                    let r = match reduction {
                        // as in pos_mod_p; the unsigned minimum picks the
                        // candidate r, r + p or r − p that lies in [0, p)
                        Reduction::Full => {
                            let q = _mm256_cvttps_epi32(_mm256_mul_ps(pos_f, inverse));
                            let r = _mm256_sub_epi32(pos, _mm256_mullo_epi32(q, p));
                            let r = _mm256_min_epu32(r, _mm256_add_epi32(r, p));
                            _mm256_min_epu32(r, _mm256_sub_epi32(r, p))
                        }
                        Reduction::Subtract => _mm256_min_epu32(pos, _mm256_sub_epi32(pos, p)),
                        Reduction::None => pos,
                    };
                    let hit = _mm256_or_si256(_mm256_cmpeq_epi32(r, r1), _mm256_cmpeq_epi32(r, r2));
                    let mut mask = _mm256_movemask_ps(_mm256_castsi256_ps(hit)) as u32;
                    while mask != 0 {
                        divisors.push((i + mask.trailing_zeros() as usize) as u32);
                        mask &= mask - 1;
                    }
                }
            }
            i += 8;
        }
        find_divisors_scalar(
            positions,
            factorbase,
            roots,
            inverses,
            i..indices.end,
            reduction,
            divisors,
        );
    }
}

/// Trial division of the sieve's candidates over the factor base, with the bounds
/// for large primes. It reuses its scratch across candidates, so every sieving
/// thread has its own.
pub struct TrialDivision<'a> {
    factorbase: &'a [u32],
    // 1/p for each factor-base prime, for pos_mod_p
    inverses: &'a [f32],
    // the sieved primes by how a position pos < 2M is reduced modulo them: p <= M,
    // M < p < 2M and p > 2M
    ranges: [Range<usize>; 3],
    k: u32,
    large_prime_multiplier: u32,
    use_dlp: bool,
    // for each candidate of the current polynomial, the indices of the sieved primes
    // that divide Q there, in increasing order
    divisors: Vec<Vec<u32>>,
    // the cofactor of the candidate
    cofactor: Integer,
    // the factors found so far
    factors: Vec<u32>,
}

impl<'a> TrialDivision<'a> {
    /// Trial division over `factorbase`, with the `inverses` 1/p of its primes as
    /// f32, for the sieve interval [−M, M), M = `sieve_interval_length` < 2^23, and
    /// the multiplier `k`. Large primes are those below `large_prime_multiplier`
    /// times the largest factor-base prime, and `use_dlp` admits two of them.
    pub fn new(
        factorbase: &'a [u32],
        inverses: &'a [f32],
        sieve_interval_length: usize,
        k: u32,
        large_prime_multiplier: u32,
        use_dlp: bool,
    ) -> TrialDivision<'a> {
        let m = sieve_interval_length as u64;
        let first = NUM_SKIP_PRIMES.min(factorbase.len());
        // the primes are sorted ascending (the 0 for −1 comes first)
        let medium = factorbase.partition_point(|&p| p as u64 <= m).max(first);
        let large = factorbase
            .partition_point(|&p| (p as u64) < 2 * m)
            .max(medium);
        TrialDivision {
            factorbase,
            inverses,
            ranges: [first..medium, medium..large, large..factorbase.len()],
            k,
            large_prime_multiplier,
            use_dlp,
            divisors: Vec::new(),
            cofactor: Integer::new(),
            factors: Vec::new(),
        }
    }

    /// Finds the sieved primes p (from index [`NUM_SKIP_PRIMES`] on) that divide Q
    /// at each candidate position pos = x + M of the sieve interval [−M, M), for a
    /// polynomial with the offsets `roots`: those with pos ≡ r1 or r2 (mod p), which
    /// [`TrialDivision::factor`] then divides out. It checks all candidates in one
    /// pass over the factor base, so the roots are read once per polynomial instead
    /// of once per candidate.
    pub fn find_divisors(&mut self, positions: &[u32], roots: &Roots) {
        if self.divisors.len() < positions.len() {
            self.divisors.resize_with(positions.len(), Vec::new);
        }
        let divisors = &mut self.divisors[..positions.len()];
        for divisors in divisors.iter_mut() {
            divisors.clear();
        }
        if positions.is_empty() {
            return;
        }
        debug_assert!(positions.iter().all(|&pos| pos < 1 << 24));
        // only −1 and 2 have no roots, so a NONE never needs to be matched
        debug_assert!(self.ranges[0].clone().all(|i| roots.get(i).is_some()));
        find_divisors(
            positions,
            self.factorbase,
            roots,
            self.inverses,
            self.ranges.clone(),
            divisors,
        );
    }

    /// Factors y = Q(x) at the candidate with index `candidate` of the last
    /// [`TrialDivision::find_divisors`] over the factor base. Returns the indices of
    /// the factor-base primes with an odd exponent, in increasing order, and the
    /// large primes left: none for a full relation, one or, with the double large
    /// prime variation, two for a partial one. `None` if y is 0 or not smooth
    /// enough.
    pub fn factor(&mut self, candidate: usize, y: &Integer) -> Option<(Vec<u32>, LargePrimes)> {
        let factorbase = self.factorbase;
        if y.is_zero() {
            return None;
        }
        // assign reuses the scratch's allocation instead of cloning y
        let y_ = &mut self.cofactor;
        y_.assign(y);
        // only the rare successful relation is cloned out at the return
        let factors = &mut self.factors;
        factors.clear();
        // the sign, index 0
        if y_.is_negative() {
            factors.push(0);
            y_.abs_mut();
        }
        // 2 in factorbase: divide out 2^exponent in place (y_ != 0 checked above)
        let exponent = y_.find_one(0).unwrap();
        *y_ >>= exponent;
        if exponent % 2 == 1 {
            factors.push(1);
        }

        // indices 2..NUM_SKIP_PRIMES: sieve skips these, so trial-divide directly
        for (i, &p) in factorbase.iter().enumerate().take(NUM_SKIP_PRIMES).skip(2) {
            let mut exp = 0u32;
            while y_.is_divisible_u(p) {
                y_.div_exact_u_mut(p);
                exp += 1;
            }
            if exp & 1 == 1 {
                factors.push(i as u32);
            }
            if *y_ == 1 {
                return Some((factors.clone(), LargePrimes::NONE));
            }
        }

        // the sieved primes that divide y, found by find_divisors; in u64 arithmetic
        // once the cofactor fits in 63 bits
        let divisors = &self.divisors[candidate];
        let mut d = 0;
        while d < divisors.len() && y_.significant_bits() > 63 {
            let i = divisors[d];
            let p = factorbase[i as usize];
            let mut exp = 0u32;
            while y_.is_divisible_u(p) {
                y_.div_exact_u_mut(p);
                exp += 1;
            }
            debug_assert!(exp > 0, "{p} does not divide Q at its root");
            if exp & 1 == 1 {
                factors.push(i);
            }
            d += 1;
        }
        // A cofactor above 64 bits has only prime factors above the largest
        // factor-base prime, too large for one or two large primes below
        // largest_prime * lpm (far below 2^32): no usable relation. This is the
        // common case for larger n.
        let mut y_u64 = y_.to_u64()?;
        for &i in &divisors[d..] {
            let p = factorbase[i as usize] as u64;
            let mut exp = 0u32;
            while y_u64.is_multiple_of(p) {
                y_u64 /= p;
                exp += 1;
            }
            debug_assert!(exp > 0, "{p} does not divide Q at its root");
            if exp & 1 == 1 {
                factors.push(i);
            }
        }
        if y_u64 == 1 {
            return Some((factors.clone(), LargePrimes::NONE));
        }
        // every prime factor of y_u64 is larger than the largest factor-base prime
        let largest_prime = *factorbase.last().unwrap() as u64;
        debug_assert!(Integer::from(y_u64).gcd_u(self.k) == 1);
        // large prime bound: largest_prime * lpm stays below 2^32, so a single large
        // prime always fits in u32.
        let lp_bound = largest_prime * self.large_prime_multiplier as u64;
        // single large prime variation: y_u64 has no factor <= largest_prime, and
        // lp_bound < largest_prime^2, so a value below lp_bound is necessarily prime.
        if y_u64 < lp_bound {
            return Some((factors.clone(), LargePrimes::one(y_u64 as u32)));
        }
        // double large prime variation: y_u64 is a product of large primes (it survived
        // trial division by the whole factor base). Accept it only if it splits into two
        // primes, each below lp_bound, i.e. y_u64 is a semiprime <= lp_bound^2.
        //
        // The common case here is a single prime cofactor > lp_bound (useless): the
        // base-2 test rejects it with one modular exponentiation, where the full
        // primality test would run all its witnesses on a prime (the worst case). A
        // `false` result certifies compositeness, so the Pollard-rho split below is
        // guaranteed to terminate. p and q are <= lp_bound < 2^32, so the cheaper
        // 3-witness is_prime_u32 suffices to confirm them prime.
        if self.use_dlp && y_u64 <= lp_bound * lp_bound && !is_probable_prime_base2(y_u64) {
            let p = pollard_rho_u64(y_u64);
            let q = y_u64 / p;
            if p <= lp_bound && q <= lp_bound && is_prime_u32(p) && is_prime_u32(q) {
                if p == q {
                    // cofactor is a prime square: already a perfect square, so the large
                    // prime contributes nothing to the parity vector. This is a full
                    // relation (find_factor recovers p via the v product).
                    return Some((factors.clone(), LargePrimes::NONE));
                }
                return Some((factors.clone(), LargePrimes::two(p as u32, q as u32)));
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // pos_mod_p is exact for every position below 2^24, for small primes, primes
    // around the bounds M and 2M of realistic intervals, and the largest prime
    // below 2^24.
    #[test]
    fn pos_mod_p_matches_remainder() {
        for p in [3u32, 13, 101, 65537, 589_811, 1_179_641, 16_777_213] {
            let inverse = 1.0 / p as f32;
            for pos in 0..1u32 << 24 {
                if pos_mod_p(pos, p, inverse) != pos % p {
                    panic!("pos_mod_p({pos}, {p}) = {}", pos_mod_p(pos, p, inverse));
                }
            }
        }
    }

    // an n of about 100 bits, whose polynomials yield every kind of relation
    fn example_n() -> Integer {
        let p = ((Integer::from(1) << 49u32) + 12345u32).next_prime();
        let q = ((Integer::from(1) << 50u32) + 67890u32).next_prime();
        p * q
    }

    // The root checks, scalar and the one compiled in, find exactly the primes that
    // divide Q at each position, for all three ranges of primes, also with more
    // candidates than a vector has lanes.
    #[test]
    fn divisors_are_the_primes_dividing_q() {
        let n: Integer = "6427752177035961102167848371107669985402627402189138248671463"
            .parse()
            .unwrap();
        let factorbase = crate::factorbase::make_factorbase(&n, 3000);
        let n_roots = crate::factorbase::square_roots_mod_factorbase(&n, &factorbase);
        let inverses = crate::factorbase::compute_inverses(&factorbase);
        // the largest prime is about 60000, so all three ranges have primes
        let m = 12000usize;
        let mut generators = crate::siqs_generator::new_polynomial_generators(
            &n,
            m as u64,
            1,
            &factorbase,
            &n_roots,
            &factorbase,
        );
        let mut trial_division = TrialDivision::new(&factorbase, &inverses, m, 1, 40, true);
        let ranges = trial_division.ranges.clone();
        assert!(ranges.iter().all(|range| range.len() > 8), "{ranges:?}");
        let mut y = Integer::new();
        for _ in 0..3 {
            let (polynomial, roots) = generators[0].next_polynomial();
            // all positions, in batches of 13
            let positions: Vec<u32> = (0..2 * m as u32).collect();
            for batch in positions.chunks(13) {
                trial_division.find_divisors(batch, roots);
                let mut scalar = vec![Vec::new(); batch.len()];
                for (range, reduction) in
                    ranges
                        .iter()
                        .zip([Reduction::Full, Reduction::Subtract, Reduction::None])
                {
                    find_divisors_scalar(
                        batch,
                        &factorbase,
                        roots,
                        &inverses,
                        range.clone(),
                        reduction,
                        &mut scalar,
                    );
                }
                for (k, &pos) in batch.iter().enumerate() {
                    polynomial.evaluate(pos as i32 - m as i32, &mut y);
                    let want: Vec<u32> = (NUM_SKIP_PRIMES..factorbase.len())
                        .filter(|&i| y.is_divisible_u(factorbase[i]))
                        .map(|i| i as u32)
                        .collect();
                    assert_eq!(trial_division.divisors[k], want, "position {pos}");
                    assert_eq!(scalar[k], want, "position {pos}, scalar");
                }
            }
        }
    }

    // The relation of y over the factor base by trial division with every prime,
    // classified independently of TrialDivision::factor: full, one large prime
    // below the bound, or two large primes below it (split by trial division).
    fn brute_force_relation(
        y: &Integer,
        factorbase: &[u32],
        large_prime_multiplier: u32,
    ) -> Option<(Vec<u32>, LargePrimes)> {
        if *y == 0 {
            return None;
        }
        let mut factors = Vec::new();
        if *y < 0 {
            factors.push(0);
        }
        let mut m = y.clone().abs();
        for (i, &p) in factorbase.iter().enumerate().skip(1) {
            let mut exponent = 0;
            while m.is_divisible_u(p) {
                m.div_exact_u_mut(p);
                exponent += 1;
            }
            if exponent % 2 == 1 {
                factors.push(i as u32);
            }
        }
        if m == 1 {
            return Some((factors, LargePrimes::NONE));
        }
        // the remaining prime factors all exceed the largest factor-base prime
        let m = m.to_u64()?;
        let largest = *factorbase.last().unwrap() as u64;
        let bound = largest * large_prime_multiplier as u64;
        if m < bound {
            return Some((factors, LargePrimes::one(m as u32)));
        }
        let is_prime = |x: u64| Integer::from(x).is_probably_prime(30) != rug::integer::IsPrime::No;
        if m > bound * bound || is_prime(m) {
            return None;
        }
        let mut p = (largest + 1) | 1;
        while m % p != 0 {
            p += 2;
        }
        let q = m / p;
        if q > bound || !is_prime(q) {
            return None;
        }
        Some(if p == q {
            (factors, LargePrimes::NONE)
        } else {
            (factors, LargePrimes::two(p as u32, q as u32))
        })
    }

    // At every position of the interval, trial division finds the same relation as
    // brute force: for an interval longer than the largest prime, where every
    // position is reduced, and for a short one, where most primes exceed M or 2M.
    // Every kind of outcome occurs.
    #[test]
    fn trial_division_matches_brute_force() {
        let n = example_n();
        let factorbase = crate::factorbase::make_factorbase(&n, 300);
        let n_roots = crate::factorbase::square_roots_mod_factorbase(&n, &factorbase);
        let inverses = crate::factorbase::compute_inverses(&factorbase);
        // none, full, one large prime, two large primes
        let mut outcomes = [0usize; 4];
        for m in [65536usize, 1500] {
            let mut generators = crate::siqs_generator::new_polynomial_generators(
                &n,
                m as u64,
                1,
                &factorbase,
                &n_roots,
                &factorbase,
            );
            let (polynomial, roots) = generators[0].next_polynomial();
            let large_prime_multiplier = 40;
            let mut trial_division =
                TrialDivision::new(&factorbase, &inverses, m, 1, large_prime_multiplier, true);
            let mut y = Integer::new();
            let positions: Vec<u32> = (0..2 * m as u32).collect();
            for batch in positions.chunks(64) {
                trial_division.find_divisors(batch, roots);
                for (candidate, &pos) in batch.iter().enumerate() {
                    let x = pos as i32 - m as i32;
                    polynomial.evaluate(x, &mut y);
                    let got = trial_division.factor(candidate, &y);
                    let want = brute_force_relation(&y, &factorbase, large_prime_multiplier);
                    assert_eq!(got, want, "M = {m}, x = {x}");
                    outcomes[want.map_or(0, |(_, large_primes)| 1 + large_primes.count())] += 1;
                }
            }
        }
        assert!(
            outcomes.iter().all(|&count| count > 0),
            "outcomes (none, full, 1LP, 2LP): {outcomes:?}"
        );
    }
}
