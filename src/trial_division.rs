use crate::constants::NUM_SKIP_PRIMES;
use crate::number_theory::{is_prime_u32, is_probable_prime_base2, pollard_rho_u64};
use crate::polynomial_generator::Roots;
use crate::relation::LargePrimes;
use rug::{Assign, Integer};

// Compute `pos % p` using a precomputed Barrett reciprocal `recip = floor(2^64 / p)`,
// replacing the per-prime hardware division in the root check with a multiply and
// a shift.
//
// Correctness: for pos < 2^32 and p in [2, 2^32), q = floor(pos*recip / 2^64) is
// floor(pos/p) or one less, so r = pos - q*p lands in [0, 2p) and a single
// conditional subtraction reduces it to pos mod p.
#[inline]
fn pos_mod_p(pos: u32, p: u32, recip: u64) -> u32 {
    let q = ((pos as u128 * recip as u128) >> 64) as u64;
    let mut r = pos as u64 - q * p as u64;
    if r >= p as u64 {
        r -= p as u64;
    }
    r as u32
}

/// Trial division of the sieve's candidates over the factor base, with the bounds
/// for large primes. It reuses its scratch across candidates, so every sieving
/// thread has its own.
pub struct TrialDivision<'a> {
    factorbase: &'a [u32],
    reciprocals: &'a [u64],
    k: u32,
    large_prime_multiplier: u32,
    use_dlp: bool,
    // the cofactor of the candidate
    cofactor: Integer,
    // the factors found so far
    factors: Vec<u32>,
}

impl<'a> TrialDivision<'a> {
    /// Trial division over `factorbase` with its Barrett `reciprocals`, for the
    /// multiplier `k`. Large primes are those below `large_prime_multiplier` times the
    /// largest factor-base prime, and `use_dlp` admits two of them.
    pub fn new(
        factorbase: &'a [u32],
        reciprocals: &'a [u64],
        k: u32,
        large_prime_multiplier: u32,
        use_dlp: bool,
    ) -> TrialDivision<'a> {
        TrialDivision {
            factorbase,
            reciprocals,
            k,
            large_prime_multiplier,
            use_dlp,
            cofactor: Integer::new(),
            factors: Vec::new(),
        }
    }

    /// Factors y = Q(x) over the factor base, where `pos` = x + M is the position of
    /// x in the sieve interval [−M, M), dividing only by the sieved primes p for
    /// which `pos` is one of the offsets `roots` of Q modulo p. Returns the indices
    /// of the factor-base primes with an odd exponent, in increasing order, and the
    /// large primes left: none for a full relation, one or, with the double large
    /// prime variation, two for a partial one. `None` if y is 0 or not smooth
    /// enough.
    pub fn factor(
        &mut self,
        pos: u32,
        y: &Integer,
        roots: &Roots,
    ) -> Option<(Vec<u32>, LargePrimes)> {
        let (factorbase, reciprocals) = (self.factorbase, self.reciprocals);
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

        // indices NUM_SKIP_PRIMES..: sieved primes. p | Q(x) iff pos ≡ root1 or root2
        // (mod p), so skip the big-int divisibility test for primes that don't hit
        // pos, which is reduced mod each p with the Barrett reciprocals.
        // Switch to u64 arithmetic once the cofactor fits in 63 bits. Its size only
        // changes when a prime divides it, so check it only then: significant_bits is
        // a GMP call, too slow to make for every prime.
        let mut i = NUM_SKIP_PRIMES;
        let mut fits_u64 = y_.significant_bits() <= 63;
        while !fits_u64 && i < factorbase.len() {
            let p = factorbase[i];
            let divides = match roots.get(i) {
                Some((r1, r2)) => {
                    let pmp = pos_mod_p(pos, p, reciprocals[i]);
                    pmp == r1 || pmp == r2
                }
                None => y_.is_divisible_u(p), // no roots known: divide
            };
            if divides {
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
                fits_u64 = y_.significant_bits() <= 63;
            }
            i += 1;
        }

        // u64 fast path with sqrt early termination.
        // If the cofactor still exceeds 64 bits after trial-dividing the whole factor
        // base, its remaining prime factors are all larger than the largest factor-base
        // prime; it cannot be a (single) large prime below largest_prime * lpm (which
        // is far below 2^64), so this candidate yields no usable relation. This is the
        // common case for larger n, where Q(x) is big enough that non-smooth cofactors
        // stay above 64 bits.
        let mut y_u64 = y_.to_u64()?;
        while i < factorbase.len() {
            let p = factorbase[i] as u64;
            if p * p > y_u64 {
                break;
            }
            let divides = match roots.get(i) {
                Some((r1, r2)) => {
                    let pmp = pos_mod_p(pos, factorbase[i], reciprocals[i]);
                    pmp == r1 || pmp == r2
                }
                None => y_u64 % p == 0,
            };
            if divides {
                let mut exp = 0u32;
                while y_u64 % p == 0 {
                    y_u64 /= p;
                    exp += 1;
                }
                if exp & 1 == 1 {
                    factors.push(i as u32);
                }
                if y_u64 == 1 {
                    return Some((factors.clone(), LargePrimes::NONE));
                }
            }
            i += 1;
        }

        // remainder y_u64 is 1 or prime
        if y_u64 == 1 {
            return Some((factors.clone(), LargePrimes::NONE));
        }
        // locate prime in factorbase[i..] via binary search
        let largest_prime = *factorbase.last().unwrap() as u64;
        if y_u64 <= largest_prime
            && let Ok(offset) = factorbase[i..].binary_search(&(y_u64 as u32))
        {
            factors.push((i + offset) as u32);
            return Some((factors.clone(), LargePrimes::NONE));
        }
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

    #[test]
    fn pos_mod_p_matches_remainder() {
        // a spread of factor-base-sized primes, including the largest that fits in u32
        let primes: [u32; 7] = [5, 97, 65537, 1_000_003, 16_777_213, 100_003, 4_294_967_291];
        // positions: extremes plus a scattering
        let positions: [u32; 8] = [
            0,
            1,
            65_536,
            1_234_567,
            (1 << 24) - 1,
            2_000_000_000,
            i32::MAX as u32,
            u32::MAX,
        ];
        for &p in &primes {
            let recip = ((1u128 << 64) / p as u128) as u64;
            for &pos in &positions {
                assert_eq!(pos_mod_p(pos, p, recip), pos % p, "pos_mod_p({pos}, {p})");
            }
        }
    }

    // an n of about 100 bits, whose polynomials yield every kind of relation
    fn example_n() -> Integer {
        let p = ((Integer::from(1) << 49u32) + 12345u32).next_prime();
        let q = ((Integer::from(1) << 50u32) + 67890u32).next_prime();
        p * q
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
    // brute force, and every kind of outcome occurs.
    #[test]
    fn trial_division_matches_brute_force() {
        let n = example_n();
        let factorbase = crate::factorbase::make_factorbase(&n, 300);
        let n_roots = crate::factorbase::square_roots_mod_factorbase(&n, &factorbase);
        let reciprocals = crate::factorbase::compute_reciprocals(&factorbase);
        let mut generators = crate::siqs_generator::new_polynomial_generators(
            &n,
            65536,
            1,
            &factorbase,
            &n_roots,
            &factorbase,
        );
        let (polynomial, roots) = generators[0].next_polynomial();
        let large_prime_multiplier = 40;
        let mut trial_division =
            TrialDivision::new(&factorbase, &reciprocals, 1, large_prime_multiplier, true);
        let mut y = Integer::new();
        // none, full, one large prime, two large primes
        let mut outcomes = [0usize; 4];
        for x in -65536..65536 {
            polynomial.evaluate(x, &mut y);
            let got = trial_division.factor((x + 65536) as u32, &y, roots);
            let want = brute_force_relation(&y, &factorbase, large_prime_multiplier);
            assert_eq!(got, want, "x = {x}");
            outcomes[want.map_or(0, |(_, large_primes)| 1 + large_primes.count())] += 1;
        }
        assert!(
            outcomes.iter().all(|&count| count > 0),
            "outcomes (none, full, 1LP, 2LP): {outcomes:?}"
        );
    }
}
