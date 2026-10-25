use crate::constants::NUM_SKIP_PRIMES;
use crate::number_theory::{is_prime_u32, is_probable_prime_base2, pollard_rho_u64};
use crate::polynomial_generator::Roots;
use fixedbitset::FixedBitSet;
use rug::{Assign, Integer};

// Compute `x.rem_euclid(p)` (result in [0, p)) using a precomputed Barrett
// reciprocal `recip = floor(2^64 / p)`, replacing the per-prime hardware division
// in the resieve loop with a multiply+shift. `x` is given split into magnitude and
// sign so the same reduction serves the byte- and u64-cofactor passes.
//
// Correctness: for a = |x| < 2^32 and p in [2, 2^32), q = floor(a*recip / 2^64) is
// floor(a/p) or one less, so r = a - q*p lands in [0, 2p) and a single conditional
// subtraction reduces it to a mod p. The Euclidean fixup maps a negative x to p - r.
#[inline]
fn x_mod_p(x_abs: u32, x_neg: bool, p: u32, recip: u64) -> u32 {
    let q = ((x_abs as u128 * recip as u128) >> 64) as u64;
    let mut r = x_abs as u64 - q * p as u64;
    if r >= p as u64 {
        r -= p as u64;
    }
    let r = r as u32;
    if x_neg && r != 0 { p - r } else { r }
}

// try to factor y = Q(x) over factorbase, using resieve: only divide by p if x ≡ root (mod p).
// On success returns the relation together with up to two large primes (1 = none):
//   (relation, 1, 1)  full relation
//   (relation, p, 1)  single-large-prime partial
//   (relation, p, q)  double-large-prime partial (only produced when use_dlp is set)
pub fn factor_over_factorbase(
    x: i32,
    y: &Integer,
    factorbase: &[u32],
    roots: &Roots,
    reciprocals: &[u64],
    k: u32,
    large_prime_multiplier: u32,
    use_dlp: bool,
    scratch: &mut Integer,
    relation_scratch: &mut FixedBitSet,
) -> Option<(FixedBitSet, u32, u32)> {
    if y.is_zero() {
        return None;
    }
    // Reuse the caller-owned scratch integer instead of cloning y on every
    // candidate; assign reuses scratch's existing allocation.
    let y_ = scratch;
    y_.assign(y);
    // Reuse the caller-owned bitset (capacity == factorbase.len()) rather than
    // allocating one per candidate: most candidates fail, so this avoids a hot
    // alloc/zero/free; the rare successful relation is cloned out at the return.
    let relation = relation_scratch;
    relation.clear();
    // -1 in factorbase
    if y_.is_negative() {
        relation.set(0, true);
        y_.abs_mut();
    }
    // 2 in factorbase: divide out 2^exponent in place (y_ != 0 checked above)
    let exponent = y_.find_one(0).unwrap();
    *y_ >>= exponent;
    if exponent % 2 == 1 {
        relation.set(1, true);
    }

    // indices 2..NUM_SKIP_PRIMES: sieve skips these, so trial-divide directly
    for (i, &p) in factorbase.iter().enumerate().take(NUM_SKIP_PRIMES).skip(2) {
        let mut exp = 0u32;
        while y_.is_divisible_u(p) {
            y_.div_exact_u_mut(p);
            exp += 1;
        }
        if exp & 1 == 1 {
            relation.set(i, true);
        }
        if *y_ == 1 {
            return Some((relation.clone(), 1, 1));
        }
    }

    // x is constant across the resieve; reduce it mod each p via the Barrett
    // reciprocals instead of a hardware divide per prime.
    let x_abs = x.unsigned_abs();
    let x_neg = x < 0;
    // indices NUM_SKIP_PRIMES..: sieved primes. p | Q(x) iff x ≡ root1 or root2 (mod p),
    // so skip the big-int divisibility test for primes that don't hit x.
    // Switch to u64 arithmetic once the cofactor fits in 63 bits. Its size only
    // changes when a prime divides it, so check it only then: significant_bits is
    // a GMP call, too slow to make for every prime.
    let mut i = NUM_SKIP_PRIMES;
    let mut fits_u64 = y_.significant_bits() <= 63;
    while !fits_u64 && i < factorbase.len() {
        let p = factorbase[i];
        let divides = match roots.get(i) {
            Some((r1, r2)) => {
                let xmp = x_mod_p(x_abs, x_neg, p, reciprocals[i]);
                xmp == r1 || xmp == r2
            }
            None => y_.is_divisible_u(p), // p | a: resieve info unavailable
        };
        if divides {
            let mut exp = 0u32;
            while y_.is_divisible_u(p) {
                y_.div_exact_u_mut(p);
                exp += 1;
            }
            if exp & 1 == 1 {
                relation.set(i, true);
            }
            if *y_ == 1 {
                return Some((relation.clone(), 1, 1));
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
    // common case for larger N, where Q(x) is big enough that non-smooth cofactors
    // stay above 64 bits.
    let mut y_u64 = y_.to_u64()?;
    while i < factorbase.len() {
        let p = factorbase[i] as u64;
        if p * p > y_u64 {
            break;
        }
        let divides = match roots.get(i) {
            Some((r1, r2)) => {
                let xmp = x_mod_p(x_abs, x_neg, factorbase[i], reciprocals[i]) as u64;
                xmp == r1 as u64 || xmp == r2 as u64
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
                relation.set(i, true);
            }
            if y_u64 == 1 {
                return Some((relation.clone(), 1, 1));
            }
        }
        i += 1;
    }

    // remainder y_u64 is 1 or prime
    if y_u64 == 1 {
        return Some((relation.clone(), 1, 1));
    }
    // locate prime in factorbase[i..] via binary search
    let largest_prime = *factorbase.last().unwrap() as u64;
    if y_u64 <= largest_prime
        && let Ok(offset) = factorbase[i..].binary_search(&(y_u64 as u32))
    {
        relation.toggle(i + offset);
        return Some((relation.clone(), 1, 1));
    }
    debug_assert!(Integer::from(y_u64).gcd_u(k) == 1);
    // large prime bound: largest_prime * lpm stays below 2^32, so a single large
    // prime always fits in u32.
    let lp_bound = largest_prime * large_prime_multiplier as u64;
    // single large prime variation: y_u64 has no factor <= largest_prime, and
    // lp_bound < largest_prime^2, so a value below lp_bound is necessarily prime.
    if y_u64 < lp_bound {
        return Some((relation.clone(), y_u64 as u32, 1));
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
    if use_dlp && y_u64 <= lp_bound * lp_bound && !is_probable_prime_base2(y_u64) {
        let p = pollard_rho_u64(y_u64);
        let q = y_u64 / p;
        if p <= lp_bound && q <= lp_bound && is_prime_u32(p) && is_prime_u32(q) {
            if p == q {
                // cofactor is a prime square: already a perfect square, so the large
                // prime contributes nothing to the parity vector. This is a full
                // relation (find_factor recovers p via the v product).
                return Some((relation.clone(), 1, 1));
            }
            return Some((relation.clone(), p as u32, q as u32));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn x_mod_p_matches_rem_euclid() {
        // a spread of factor-base-sized primes, including the largest that fits in u32
        let primes: [u32; 7] = [5, 97, 65537, 1_000_003, 16_777_213, 100_003, 4_294_967_291];
        // x values: extremes plus a scattering of both signs
        let xs: [i32; 9] = [
            0,
            1,
            -1,
            i32::MAX,
            i32::MIN,
            1_234_567,
            -1_234_567,
            -65_536,
            2_000_000_000,
        ];
        for &p in &primes {
            let recip = ((1u128 << 64) / p as u128) as u64;
            for &x in &xs {
                let got = x_mod_p(x.unsigned_abs(), x < 0, p, recip);
                let want = (x as i64).rem_euclid(p as i64) as u32;
                assert_eq!(got, want, "x_mod_p({x}, {p})");
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
    // classified independently of factor_over_factorbase: full, one large prime
    // below the bound, or two large primes below it (split by trial division).
    fn brute_force_relation(
        y: &Integer,
        factorbase: &[u32],
        large_prime_multiplier: u32,
    ) -> Option<(FixedBitSet, u32, u32)> {
        if *y == 0 {
            return None;
        }
        let mut relation = FixedBitSet::with_capacity(factorbase.len());
        relation.set(0, *y < 0);
        let mut m = y.clone().abs();
        for (i, &p) in factorbase.iter().enumerate().skip(1) {
            let mut exponent = 0;
            while m.is_divisible_u(p) {
                m.div_exact_u_mut(p);
                exponent += 1;
            }
            relation.set(i, exponent % 2 == 1);
        }
        if m == 1 {
            return Some((relation, 1, 1));
        }
        // the remaining prime factors all exceed the largest factor-base prime
        let m = m.to_u64()?;
        let largest = *factorbase.last().unwrap() as u64;
        let bound = largest * large_prime_multiplier as u64;
        if m < bound {
            return Some((relation, m as u32, 1));
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
            (relation, 1, 1)
        } else {
            (relation, p as u32, q as u32)
        })
    }

    // At every position of the interval, factor_over_factorbase finds the same
    // relation as brute force, and every kind of outcome occurs.
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
        let (mut u, mut y) = (Integer::new(), Integer::new());
        let mut scratch = Integer::new();
        let mut relation_scratch = FixedBitSet::with_capacity(factorbase.len());
        let sorted = |(relation, p, q): (FixedBitSet, u32, u32)| (relation, p.min(q), p.max(q));
        // none, full, one large prime, two large primes
        let mut outcomes = [0usize; 4];
        for x in -65536..65536 {
            polynomial.evaluate(x, &n, &mut u, &mut y);
            let got = factor_over_factorbase(
                x,
                &y,
                &factorbase,
                roots,
                &reciprocals,
                1,
                large_prime_multiplier,
                true,
                &mut scratch,
                &mut relation_scratch,
            )
            .map(sorted);
            let want = brute_force_relation(&y, &factorbase, large_prime_multiplier).map(sorted);
            assert_eq!(got, want, "x = {x}");
            outcomes[match want {
                None => 0,
                Some((_, 1, 1)) => 1,
                Some((_, 1, _)) => 2,
                Some(_) => 3,
            }] += 1;
        }
        assert!(
            outcomes.iter().all(|&count| count > 0),
            "outcomes (none, full, 1LP, 2LP): {outcomes:?}"
        );
    }
}
