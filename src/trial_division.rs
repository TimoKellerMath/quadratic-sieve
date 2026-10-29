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

/// The sum of `logs[i]` over the indices i of `indices` whose prime divides Q at the
/// position `pos` of the sieve interval: pos ≡ r1 or r2 (mod p) for the offsets
/// `roots`, a double root counted once, as the sieve would have added them. For the
/// primes that the small prime variation does not sieve; without SIMD.
fn divisor_logs_scalar(
    pos: u32,
    indices: Range<usize>,
    factorbase: &[u32],
    roots: &Roots,
    inverses: &[f32],
    logs: &[u8],
) -> u32 {
    indices
        .filter(|&i| {
            let r = pos_mod_p(pos, factorbase[i], inverses[i]);
            r == roots.r1[i] || r == roots.r2[i]
        })
        .map(|i| logs[i] as u32)
        .sum()
}

/// [`divisor_logs_scalar`] without SIMD.
#[cfg(not(target_feature = "avx2"))]
pub(crate) fn divisor_logs(
    pos: u32,
    indices: Range<usize>,
    factorbase: &[u32],
    roots: &Roots,
    inverses: &[f32],
    logs: &[u8],
) -> u32 {
    divisor_logs_scalar(pos, indices, factorbase, roots, inverses, logs)
}

/// [`divisor_logs_scalar`] for 8 primes at a time, and the rest scalar.
#[cfg(target_feature = "avx2")]
pub(crate) fn divisor_logs(
    pos: u32,
    indices: Range<usize>,
    factorbase: &[u32],
    roots: &Roots,
    inverses: &[f32],
    logs: &[u8],
) -> u32 {
    use std::arch::x86_64::*;
    // the arrays the vectors are loaded from, all as long as the factor base
    let n = factorbase.len();
    let (r1s, r2s, inverses, logs) = (&roots.r1[..n], &roots.r2[..n], &inverses[..n], &logs[..n]);
    assert!(indices.end <= n);
    let mut i = indices.start;
    // SAFETY: AVX2 is enabled at compile time, and i + 8 <= indices.end <= n, the
    // length of all five arrays
    let sum = unsafe {
        let (pos_i, pos_f) = (_mm256_set1_epi32(pos as i32), _mm256_set1_ps(pos as f32));
        let mut sums = _mm256_setzero_si256();
        while i + 8 <= indices.end {
            let p = _mm256_loadu_si256(factorbase.as_ptr().add(i).cast());
            let r = pos_mod_p_avx2(pos_i, pos_f, p, _mm256_loadu_ps(inverses.as_ptr().add(i)));
            let r1 = _mm256_loadu_si256(r1s.as_ptr().add(i).cast());
            let r2 = _mm256_loadu_si256(r2s.as_ptr().add(i).cast());
            let hit = _mm256_or_si256(_mm256_cmpeq_epi32(r, r1), _mm256_cmpeq_epi32(r, r2));
            // the 8 logs, widened to the lanes
            let log = _mm256_cvtepu8_epi32(_mm_loadl_epi64(logs.as_ptr().add(i).cast()));
            sums = _mm256_add_epi32(sums, _mm256_and_si256(hit, log));
            i += 8;
        }
        // the sum of the lanes
        let s = _mm_add_epi32(
            _mm256_castsi256_si128(sums),
            _mm256_extracti128_si256(sums, 1),
        );
        let s = _mm_add_epi32(s, _mm_shuffle_epi32(s, 0b01_00_11_10));
        let s = _mm_add_epi32(s, _mm_shuffle_epi32(s, 0b10_11_00_01));
        _mm_cvtsi128_si32(s) as u32
    };
    sum + divisor_logs_scalar(pos, i..indices.end, factorbase, roots, inverses, logs)
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

/// [`pos_mod_p`] in 8 lanes: the position, in all lanes as an integer `pos` and as
/// a float `pos_f`, modulo the primes `p` with the `inverses`.
#[cfg(target_feature = "avx2")]
#[inline(always)]
fn pos_mod_p_avx2(
    pos: std::arch::x86_64::__m256i,
    pos_f: std::arch::x86_64::__m256,
    p: std::arch::x86_64::__m256i,
    inverses: std::arch::x86_64::__m256,
) -> std::arch::x86_64::__m256i {
    use std::arch::x86_64::*;
    // SAFETY: AVX2 is enabled at compile time
    unsafe {
        let q = _mm256_cvttps_epi32(_mm256_mul_ps(pos_f, inverses));
        let r = _mm256_sub_epi32(pos, _mm256_mullo_epi32(q, p));
        // the unsigned minimum picks the candidate r, r + p or r − p in [0, p)
        let r = _mm256_min_epu32(r, _mm256_add_epi32(r, p));
        _mm256_min_epu32(r, _mm256_sub_epi32(r, p))
    }
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
    // the arrays the vectors are loaded from, all as long as the factor base, which
    // contains the ranges
    let n = factorbase.len();
    let (r1s, r2s, inverse_slice) = (&roots.r1[..n], &roots.r2[..n], &inverses[..n]);
    assert!(ranges.iter().all(|range| range.end <= n));
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
            // SAFETY: AVX2 is enabled at compile time, and i + 8 <= indices.end <= n,
            // the length of all four arrays
            unsafe {
                let p = _mm256_loadu_si256(factorbase.as_ptr().add(i).cast());
                let r1 = _mm256_loadu_si256(r1s.as_ptr().add(i).cast());
                let r2 = _mm256_loadu_si256(r2s.as_ptr().add(i).cast());
                let inverses = _mm256_loadu_ps(inverse_slice.as_ptr().add(i));
                for (&(pos, pos_f), divisors) in lanes.iter().zip(divisors.iter_mut()) {
                    let r = match reduction {
                        Reduction::Full => pos_mod_p_avx2(pos, pos_f, p, inverses),
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

/// The bound lp_bound^exponent, at most lp_bound^2, of a cofactor with two large
/// primes below `lp_bound`: msieve uses 1.8, YAFU 1.75 to 1.95 by the size of kn.
/// The larger the cofactor, the costlier the split and the less likely its primes
/// are to close a cycle.
pub fn dlp_bound(lp_bound: u64, exponent: f64) -> u64 {
    if exponent >= 2.0 {
        lp_bound * lp_bound
    } else {
        (lp_bound as f64).powf(exponent) as u64
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
    // the length 2M of the sieve interval
    interval: usize,
    k: u32,
    // the bound of a large prime, below the square of the largest factor-base prime
    lp_bound: u64,
    // with the double large prime variation, the bound of a cofactor with two large
    // primes
    dlp_bound: Option<u64>,
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
    /// times the largest factor-base prime, which must be below that prime squared
    /// and 2^32. With `dlp_bound`, the double large prime variation admits two of
    /// them in a cofactor up to that bound.
    pub fn new(
        factorbase: &'a [u32],
        inverses: &'a [f32],
        sieve_interval_length: usize,
        k: u32,
        large_prime_multiplier: u32,
        dlp_bound: Option<u64>,
    ) -> TrialDivision<'a> {
        // the AVX2 root check loads them unchecked
        assert_eq!(
            inverses.len(),
            factorbase.len(),
            "one inverse per factor-base prime"
        );
        let m = sieve_interval_length as u64;
        let first = NUM_SKIP_PRIMES.min(factorbase.len());
        // the primes are sorted ascending (the 0 for −1 comes first)
        let medium = factorbase.partition_point(|&p| p as u64 <= m).max(first);
        let large = factorbase
            .partition_point(|&p| (p as u64) < 2 * m)
            .max(medium);
        let largest_prime = *factorbase.last().unwrap() as u64;
        let lp_bound = largest_prime * large_prime_multiplier as u64;
        debug_assert!(lp_bound < largest_prime * largest_prime && lp_bound < 1 << 32);
        TrialDivision {
            factorbase,
            inverses,
            ranges: [first..medium, medium..large, large..factorbase.len()],
            interval: 2 * sieve_interval_length,
            k,
            lp_bound,
            dlp_bound,
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
        assert!(
            roots.r1.len() == self.factorbase.len() && roots.r2.len() == self.factorbase.len(),
            "roots for each factor-base prime"
        );
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
        debug_assert!(positions.iter().all(|&pos| (pos as usize) < self.interval));
        // only −1 and 2 have no roots, so a NONE never needs to be matched
        debug_assert!(
            (self.ranges[0].start..self.factorbase.len()).all(|i| roots.get(i).is_some())
        );
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
        // single large prime variation: y_u64 has no factor <= largest_prime, and
        // lp_bound < largest_prime^2, so a value below lp_bound is necessarily prime.
        // It fits in a u32.
        let lp_bound = self.lp_bound;
        if y_u64 < lp_bound {
            return Some((factors.clone(), LargePrimes::one(y_u64 as u32)));
        }
        // double large prime variation: y_u64 is a product of large primes (it survived
        // trial division by the whole factor base). Accept it only if it splits into two
        // primes, each below lp_bound, and is at most dlp_bound <= lp_bound^2. Below
        // largest_prime^2 it is a prime.
        //
        // The common case here is a single prime cofactor > lp_bound (useless): the
        // base-2 test rejects it with one modular exponentiation, where the full
        // primality test would run all its witnesses on a prime (the worst case). A
        // `false` result certifies compositeness, so the Pollard-rho split below is
        // guaranteed to terminate. p and q are <= lp_bound < 2^32, so the cheaper
        // 3-witness is_prime_u32 suffices to confirm them prime.
        let dlp_bound = self.dlp_bound?;
        if y_u64 >= largest_prime * largest_prime
            && y_u64 <= dlp_bound
            && !is_probable_prime_base2(y_u64)
        {
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

    // primes for the reductions: small ones, ones around the bounds M and 2M of
    // realistic intervals, and the largest one below 2^24
    const PRIMES: [u32; 8] = [5, 7, 13, 101, 65537, 589_811, 1_179_641, 16_777_213];

    // The inverse 1/p rounded to f32, and its neighbors, which are still close
    // enough for p >= 5 but push the quotient off in both directions.
    fn inverses(p: u32) -> [f32; 3] {
        let inverse = 1.0 / p as f32;
        [
            inverse,
            f32::from_bits(inverse.to_bits() - 1),
            f32::from_bits(inverse.to_bits() + 1),
        ]
    }

    // pos_mod_p is exact for every position below 2^24, correcting the quotient in
    // both directions.
    #[test]
    fn pos_mod_p_matches_remainder() {
        let (mut too_large, mut too_small) = (0, 0);
        for p in PRIMES {
            for inverse in inverses(p) {
                for pos in 0..1u32 << 24 {
                    if pos_mod_p(pos, p, inverse) != pos % p {
                        panic!("pos_mod_p({pos}, {p}, {inverse})");
                    }
                    let q = (pos as f32 * inverse) as u32;
                    too_large += (q > pos / p) as usize;
                    too_small += (q < pos / p) as usize;
                }
            }
        }
        assert!(too_large > 0 && too_small > 0, "{too_large} {too_small}");
        // the smallest prime it is used for, with the rounded inverse
        let inverse = 1.0 / 3.0;
        assert!((0..1u32 << 24).all(|pos| pos_mod_p(pos, 3, inverse) == pos % 3));
    }

    // The AVX2 reduction is exact for every position below 2^24, in every lane.
    #[cfg(target_feature = "avx2")]
    #[test]
    fn avx2_pos_mod_p_matches_remainder() {
        use std::arch::x86_64::*;
        for k in 0..3 {
            let inverses = PRIMES.map(|p| inverses(p)[k]);
            // SAFETY: AVX2 is enabled at compile time, and the arrays have 8 elements
            unsafe {
                let p = _mm256_loadu_si256(PRIMES.as_ptr().cast());
                let inverse = _mm256_loadu_ps(inverses.as_ptr());
                for pos in 0..1u32 << 24 {
                    let r = pos_mod_p_avx2(
                        _mm256_set1_epi32(pos as i32),
                        _mm256_set1_ps(pos as f32),
                        p,
                        inverse,
                    );
                    let mut lanes = [0u32; 8];
                    _mm256_storeu_si256(lanes.as_mut_ptr().cast(), r);
                    if lanes != PRIMES.map(|p| pos % p) {
                        panic!("position {pos}, inverses {k}: {lanes:?}");
                    }
                }
            }
        }
    }

    // The logs of the dividing primes, scalar and the ones compiled in, agree with
    // brute force at every position, for ranges with and without a rest after the
    // vectors.
    #[test]
    fn divisor_logs_are_the_logs_of_the_dividing_primes() {
        let n: Integer = "6427752177035961102167848371107669985402627402189138248671463"
            .parse()
            .unwrap();
        let factorbase = crate::factorbase::make_factorbase(&n, 500);
        let n_roots = crate::factorbase::square_roots_mod_factorbase(&n, &factorbase);
        let inverses = crate::factorbase::compute_inverses(&factorbase);
        let logs = crate::factorbase::compute_logs(&factorbase);
        let m = 20000u32;
        let mut generators = crate::siqs_generator::new_polynomial_generators(
            &n,
            m as u64,
            1,
            &factorbase,
            &n_roots,
            &factorbase,
        );
        let (_, roots) = generators[0].next_polynomial();
        for indices in [NUM_SKIP_PRIMES..37, NUM_SKIP_PRIMES..38, 50..450] {
            for pos in 0..2 * m {
                let want: u32 = indices
                    .clone()
                    .filter(|&i| {
                        let r = pos % factorbase[i];
                        r == roots.r1[i] || r == roots.r2[i]
                    })
                    .map(|i| logs[i] as u32)
                    .sum();
                let args = (indices.clone(), &factorbase, roots, &inverses, &logs);
                assert_eq!(
                    divisor_logs(pos, args.0.clone(), args.1, args.2, args.3, args.4),
                    want
                );
                assert_eq!(
                    divisor_logs_scalar(pos, args.0, args.1, args.2, args.3, args.4),
                    want
                );
            }
        }
    }

    // The root check needs the roots of every factor-base prime.
    #[test]
    #[should_panic(expected = "roots for each factor-base prime")]
    fn root_check_rejects_missing_roots() {
        let factorbase = crate::factorbase::make_factorbase(&example_n(), 30);
        let inverses = crate::factorbase::compute_inverses(&factorbase);
        let mut trial_division = TrialDivision::new(&factorbase, &inverses, 1000, 1, 40, None);
        trial_division.find_divisors(&[1], &Roots::default());
    }

    // an n of about 100 bits, whose polynomials yield every kind of relation
    fn example_n() -> Integer {
        let p = ((Integer::from(1) << 49u32) + 12345u32).next_prime();
        let q = ((Integer::from(1) << 50u32) + 67890u32).next_prime();
        p * q
    }

    // The root checks, scalar and the one compiled in, find exactly the primes that
    // divide Q at each position, for all three ranges of primes, each with a rest
    // after its vectors, and for batches of positions.
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
        let mut trial_division =
            TrialDivision::new(&factorbase, &inverses, m, 1, 40, Some(1 << 40));
        let ranges = trial_division.ranges.clone();
        assert!(
            ranges
                .iter()
                .all(|range| range.len() > 8 && range.len() % 8 != 0),
            "{ranges:?}"
        );
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
        dlp_bound: u64,
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
        if m > dlp_bound || is_prime(m) {
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
    // position is reduced, and for a short one, where most primes exceed M or 2M;
    // and with the largest bound of a cofactor with two large primes, and a smaller
    // one, which rejects some. Every kind of outcome occurs.
    #[test]
    fn trial_division_matches_brute_force() {
        let n = example_n();
        let factorbase = crate::factorbase::make_factorbase(&n, 300);
        let n_roots = crate::factorbase::square_roots_mod_factorbase(&n, &factorbase);
        let inverses = crate::factorbase::compute_inverses(&factorbase);
        let large_prime_multiplier = 40;
        let lp_bound = *factorbase.last().unwrap() as u64 * large_prime_multiplier as u64;
        // none, full, one large prime, two large primes; by the bound
        let mut outcomes = [[0usize; 4]; 2];
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
            for (exponent, outcomes) in [2.0, 1.8].into_iter().zip(&mut outcomes) {
                let bound = dlp_bound(lp_bound, exponent);
                let mut trial_division = TrialDivision::new(
                    &factorbase,
                    &inverses,
                    m,
                    1,
                    large_prime_multiplier,
                    Some(bound),
                );
                let mut y = Integer::new();
                let positions: Vec<u32> = (0..2 * m as u32).collect();
                for batch in positions.chunks(64) {
                    trial_division.find_divisors(batch, roots);
                    for (candidate, &pos) in batch.iter().enumerate() {
                        let x = pos as i32 - m as i32;
                        polynomial.evaluate(x, &mut y);
                        let got = trial_division.factor(candidate, &y);
                        let want =
                            brute_force_relation(&y, &factorbase, large_prime_multiplier, bound);
                        assert_eq!(got, want, "M = {m}, x = {x}, exponent {exponent}");
                        outcomes[want.map_or(0, |(_, large_primes)| 1 + large_primes.count())] += 1;
                    }
                }
            }
        }
        assert!(
            outcomes[1][3] < outcomes[0][3],
            "the smaller bound rejects no cofactor: {outcomes:?}"
        );
        let outcomes = outcomes[1];
        assert!(
            outcomes.iter().all(|&count| count > 0),
            "outcomes (none, full, 1LP, 2LP): {outcomes:?}"
        );
    }
}
