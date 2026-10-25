use std::fmt::{self, Debug};

//use rug::ops::SubFrom;
//use num_traits::{Zero};
use rug::integer::IsPrime;
use rug::{Complete, Integer};
//use rug::ops::DivRounding;

#[derive(Debug, Clone)]
pub enum NumberTheoryError {
    IsEven(Integer),
    NotCoprime(Integer, Integer),
    IsNonsquare(Integer, Integer),
    AlgorithmFailed,
    /// A prime, or a number below 2, given to be factored.
    NotComposite(Integer),
}

impl fmt::Display for NumberTheoryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NumberTheoryError::IsEven(a) => write!(f, "{a} is even"),
            NumberTheoryError::NotCoprime(a, b) => write!(f, "gcd({a}, {b}) != 1"),
            NumberTheoryError::IsNonsquare(a, p) => write!(f, "{a} not a square mod {p}"),
            NumberTheoryError::AlgorithmFailed => write!(f, "algorithm failed"),
            NumberTheoryError::NotComposite(a) => write!(f, "{a} is not composite"),
        }
    }
}

impl std::error::Error for NumberTheoryError {}

// all primes <= 1000
pub const SMALL_PRIMES: [u32; 168] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
    197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
    311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
    431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547,
    557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
    661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797,
    809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929,
    937, 941, 947, 953, 967, 971, 977, 983, 991, 997,
];

// Montgomery arithmetic modulo an odd `n`, replacing the per-multiply 128-bit
// division of a plain `(a * b) % n` with the cheaper REDC reduction. Values are held
// in Montgomery form `a * R mod n` with `R = 2^64`; `mul` keeps that form, and
// `gcd(x, n)` is unaffected by the form because `gcd(R, n) = 1` for odd `n` (so
// Pollard-rho can run entirely in Montgomery form).
struct Montgomery {
    n: u64,
    neg_ninv: u64, // -n^{-1} mod 2^64
    r2: u64,       // R^2 mod n, converts a plain residue into Montgomery form
    one: u64,      // R mod n = Montgomery form of 1
}

impl Montgomery {
    // `n` must be odd and > 1.
    fn new(n: u64) -> Montgomery {
        debug_assert!(n & 1 == 1 && n > 1);
        // n^{-1} mod 2^64 by Newton iteration; each step doubles the correct bits,
        // so 6 steps from a 1-bit seed reach the full 64 bits.
        let mut ninv = 1u64;
        for _ in 0..6 {
            ninv = ninv.wrapping_mul(2u64.wrapping_sub(n.wrapping_mul(ninv)));
        }
        // R mod n = 2^64 mod n = (-n) mod n
        let r = n.wrapping_neg() % n;
        let r2 = ((r as u128 * r as u128) % n as u128) as u64;
        Montgomery {
            n,
            neg_ninv: ninv.wrapping_neg(),
            r2,
            one: r,
        }
    }

    // REDC: given x = a*b < n * 2^64, return a*b*R^{-1} mod n in [0, n).
    #[inline]
    fn reduce(&self, x: u128) -> u64 {
        let q = (x as u64).wrapping_mul(self.neg_ninv); // chosen so x + q*n ≡ 0 (mod 2^64)
        let m = q as u128 * self.n as u128;
        let (sum, carry) = x.overflowing_add(m);
        let t = (sum >> 64) as u64; // (x + q*n) / 2^64, exact since the low word cancels
        // the quotient is < 2n; one conditional subtraction lands it in [0, n).
        // A carry out of 128 bits means the true quotient is t + 2^64, and
        // t.wrapping_sub(n) yields that value reduced mod n in one step.
        if carry {
            t.wrapping_sub(self.n)
        } else if t >= self.n {
            t - self.n
        } else {
            t
        }
    }

    #[inline]
    fn mul(&self, a: u64, b: u64) -> u64 {
        self.reduce(a as u128 * b as u128)
    }

    // convert a plain residue into Montgomery form
    #[inline]
    fn to_mont(&self, a: u64) -> u64 {
        self.mul(a % self.n, self.r2)
    }

    // a + b for a, b in [0, n), result in [0, n)
    #[inline]
    fn add(&self, a: u64, b: u64) -> u64 {
        let (s, carry) = a.overflowing_add(b);
        if carry || s >= self.n {
            s.wrapping_sub(self.n)
        } else {
            s
        }
    }

    // base^exp mod n, with `base` a plain residue; the result is returned in
    // Montgomery form (the caller compares it against `one` / `n - one`).
    fn pow(&self, base: u64, mut exp: u64) -> u64 {
        let mut result = self.one;
        let mut b = self.to_mont(base);
        while exp > 0 {
            if exp & 1 == 1 {
                result = self.mul(result, b);
            }
            b = self.mul(b, b);
            exp >>= 1;
        }
        result
    }
}

#[inline]
fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

// Deterministic Miller–Rabin over the given witness set: returns true iff no
// witness proves `n` composite. With a witness set known to be complete for the
// range of `n`, this is an exact primality test. `n` divisible by a witness is
// resolved directly (prime iff equal to that witness).
fn miller_rabin(n: u64, witnesses: &[u64]) -> bool {
    if n < 2 {
        return false;
    }
    for &p in witnesses {
        if n.is_multiple_of(p) {
            return n == p;
        }
    }
    // n is now odd and coprime to every witness, so Montgomery arithmetic applies.
    let mont = Montgomery::new(n);
    let neg_one = n - mont.one; // Montgomery form of n - 1
    // write n - 1 = d * 2^s with d odd
    let mut d = n - 1;
    let mut s = 0u32;
    while d & 1 == 0 {
        d >>= 1;
        s += 1;
    }
    'witness: for &a in witnesses {
        let mut x = mont.pow(a, d);
        if x == mont.one || x == neg_one {
            continue;
        }
        for _ in 0..s - 1 {
            x = mont.mul(x, x);
            if x == neg_one {
                continue 'witness;
            }
        }
        return false;
    }
    true
}

// Deterministic primality test for n < 2^64. The witness set
// {2,3,5,7,11,13,17,19,23,29,31,37} is known to be correct for all n < 3.3 * 10^24.
pub fn is_prime_u64(n: u64) -> bool {
    const WITNESSES: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    miller_rabin(n, &WITNESSES)
}

// Deterministic primality test for n < 2^32. The witness set {2, 7, 61} is known
// to be correct for all n < 4,759,123,141 > 2^32, so only three rounds are needed
// — cheaper than the full 2^64 set when the input is known to fit in 32 bits.
pub fn is_prime_u32(n: u64) -> bool {
    debug_assert!(n < 1u64 << 32);
    const WITNESSES: [u64; 3] = [2, 7, 61];
    miller_rabin(n, &WITNESSES)
}

// Single strong-probable-prime round to base 2 for odd n > 2. A `false` result
// means base 2 is a Miller–Rabin witness, which is a *certificate* that n is
// composite; `true` means n is only a probable prime. Used to cheaply reject the
// common single-prime cofactor before attempting a Pollard-rho split (which would
// not terminate on a prime): one modular exponentiation instead of a full test.
pub fn is_probable_prime_base2(n: u64) -> bool {
    debug_assert!(n & 1 == 1 && n > 2);
    let mont = Montgomery::new(n);
    let neg_one = n - mont.one; // Montgomery form of n - 1
    let mut d = n - 1;
    let mut s = 0u32;
    while d & 1 == 0 {
        d >>= 1;
        s += 1;
    }
    let mut x = mont.pow(2, d);
    if x == mont.one || x == neg_one {
        return true;
    }
    for _ in 0..s - 1 {
        x = mont.mul(x, x);
        if x == neg_one {
            return true;
        }
    }
    false
}

// Pollard's rho: return a non-trivial divisor of the composite, odd `n`.
// Used to split a double-large-prime cofactor (a product of two ~30-bit primes)
// into its two prime factors; for such semiprimes this returns one of them.
//
// Brent's variant of the cycle search (one f-evaluation per step instead of
// Floyd's three) with the gcd batched: the per-step differences are accumulated
// into a single Montgomery product and only `gcd(product, n)` is taken once per
// `BATCH` steps. gcd(product, n) is unchanged by the Montgomery form because
// gcd(R, n) = 1, so the returned divisor is a genuine factor of n.
pub fn pollard_rho_u64(n: u64) -> u64 {
    if n & 1 == 0 {
        return 2;
    }
    const BATCH: usize = 128;
    let mont = Montgomery::new(n);
    let two = mont.to_mont(2);
    let mut c = mont.one; // Montgomery form of c, starting at 1
    loop {
        let f = |x: u64| mont.add(mont.mul(x, x), c);
        let mut y = two;
        let mut x = two; // checkpoint: y's value at the start of the current round
        let mut ys = two; // y's value at the start of the current batch (for backtracking)
        let mut q = mont.one; // running product of |x - y|, Montgomery form of 1
        let mut d = 1u64;
        let mut r = 1usize; // round length, doubling each round (Brent)
        while d == 1 {
            x = y;
            for _ in 0..r {
                y = f(y);
            }
            let mut k = 0;
            while k < r && d == 1 {
                ys = y;
                let count = BATCH.min(r - k);
                for _ in 0..count {
                    y = f(y);
                    let diff = x.abs_diff(y);
                    q = mont.mul(q, diff); // 0 once the cycle closes (x == y)
                }
                d = gcd_u64(q, n);
                k += count;
            }
            r *= 2;
        }
        if d == n {
            // a batch product hit all of n (the cycle closed within it): re-walk the
            // last batch one step at a time to isolate which difference carried the
            // factor. If even that yields n, this c failed — bump it and retry.
            loop {
                ys = f(ys);
                let diff = x.abs_diff(ys);
                d = gcd_u64(diff, n);
                if d != 1 {
                    break;
                }
            }
        }
        if d != n {
            return d;
        }
        c = mont.add(c, mont.one); // c += 1
    }
}

// compute a^2 (mod p)
#[inline]
pub fn square_mod_p(a: &Integer, p: &Integer) -> Integer {
    a.square_ref().complete() % p
}

// modular inverse of a mod p for prime p (or None if p | a); a must be < 2^31
#[inline]
pub fn modular_inverse_u32(a: u32, p: u32) -> Option<u32> {
    if a == 0 {
        return None;
    }
    let mut t: i64 = 0;
    let mut newt: i64 = 1;
    let mut r: i64 = p as i64;
    let mut newr: i64 = a as i64;
    while newr != 0 {
        let q = r / newr;
        let tmp = t - q * newt;
        t = newt;
        newt = tmp;
        let tmp = r - q * newr;
        r = newr;
        newr = tmp;
    }
    if r != 1 {
        return None;
    }
    if t < 0 {
        t += p as i64;
    }
    Some(t as u32)
}

// compute (a_,k) with a = a_ 2^k, a_ odd (or (0,0) if a == 0)
pub fn factor_out_power_of_2(a: &Integer) -> (Integer, u32) {
    let k = match a.find_one(0) {
        Some(k) => k,
        None => return (Integer::from(0), 0), // a == 0
    };
    let a_: Integer = a.clone() >> k;
    debug_assert_eq!(a_.clone() << k, *a);
    (a_, k)
}

// compute a quadratic non-residue mod p
pub fn quadratic_non_residue_mod_p(p: &Integer) -> Result<Integer, NumberTheoryError> {
    if p.is_even() {
        return Err(NumberTheoryError::IsEven(p.clone()));
    }
    if p.get_bit(1) {
        // p = 3 (4) =>
        return Ok(Integer::from(-1)); // -1 is a quadratic non-residue
    }
    let mut a;
    for q in SMALL_PRIMES {
        a = Integer::from(q);
        if a.legendre(p) == -1 {
            return Ok(a);
        }
    }
    a = Integer::from(*SMALL_PRIMES.last().unwrap());
    loop {
        a += 1;
        if a.legendre(p) == -1 {
            return Ok(a);
        }
    }
}

// compute square root of a (mod p)
// using the Shanks--Tonelli algorithm
pub fn square_root_mod_p(a: &Integer, p: &Integer) -> Result<Integer, NumberTheoryError> {
    debug_assert_eq!(p.is_probably_prime(10), IsPrime::Yes);
    if *p == 2 {
        return Ok(a.clone());
    }
    match a.legendre(p) {
        -1 => return Err(NumberTheoryError::IsNonsquare(a.clone(), p.clone())),
        0 => return Ok(Integer::from(0)),
        _ => (),
    }
    if p.get_bit(1) {
        // p == 3 (mod 4) => square_root = a^((p+1)/4)
        let square_root = a
            .pow_mod_ref(&((p + 1u32).complete() >> 2), p)
            .unwrap()
            .complete();
        return Ok(square_root);
    }
    let (m, mut k) = factor_out_power_of_2(&(p - Integer::from(1)));
    debug_assert_ne!(k, 0);
    let mut square_root = a
        .pow_mod_ref(&(&m >> 1u32).complete(), p)
        .unwrap()
        .complete(); // a^((m-1)/2), uses that m is odd
    let mut remainder = a * square_root.square_ref().complete();
    remainder %= p;
    square_root *= a;
    square_root %= p;
    if remainder == 1 {
        return Ok(square_root);
    }
    let quadratic_non_residue = quadratic_non_residue_mod_p(p)?;
    let mut y = quadratic_non_residue.pow_mod_ref(&m, p).unwrap().complete();
    while remainder != 1 {
        let mut k_ = 0; // the order of z_ (mod p) divides 2^(k-1)
        let mut z_ = remainder.clone();
        while z_ != 1 {
            // determine its order 2^k_ with k_ < k
            z_.square_mut();
            z_ %= p;
            k_ += 1;
        }
        if k_ == k {
            return Err(NumberTheoryError::IsNonsquare(a.clone(), p.clone()));
        }
        let t = y
            .pow_mod_ref(&(Integer::from(1) << (k - k_ - 1)), p)
            .unwrap()
            .complete();
        y = t.clone().square();
        y %= p;
        square_root *= t;
        square_root %= p;
        remainder *= &y;
        remainder %= p;
        k = k_;
    }
    debug_assert_eq!(square_mod_p(&square_root, p), a.clone() % p);
    Ok(square_root)
}

// Input: sqrt_mod_q^2 = x (mod q)
// Assume: gcd(2 * sqrt_mod_q, q) = 1
// Output: a^2 = x (mod q^2)
pub fn lift_square_root_mod_q2(
    x: &Integer,
    sqrt_mod_q: &Integer,
    q: &Integer,
) -> Result<Integer, NumberTheoryError> {
    debug_assert!(q > &Integer::from(2));
    //debug_assert!((sqrt_mod_p.clone().square() - x).is_divisible(&p));
    let q_square = q.square_ref().complete();
    let mut a: Integer = (sqrt_mod_q << 1u32).complete();
    match a.invert_mut(&q_square) {
        // a = (2s)^-1 (mod p^2)
        Ok(()) => (),
        Err(_) => return Err(NumberTheoryError::NotCoprime(a, q_square)),
    }
    let sqrt_mod_q2 = ((sqrt_mod_q.square_ref() + x).complete() * a) % q_square; // S = (s^2 + x)/(2s) (mod p^2)
    Ok(sqrt_mod_q2)
}

#[cfg(test)]
mod tests {
    use rug::integer::IsPrime;

    use super::*;

    #[test]
    fn test_montgomery_primality() {
        // cross-check the u64/u32 deterministic tests against rug, including primes
        // and semiprimes whose product exceeds 2^63 (exercises reduce's carry path).
        let cases: [u64; 14] = [
            3,
            61,
            65537,
            4_294_967_291, // largest prime < 2^32
            4_294_967_295, // 3 * 5 * 17 * 257 * 65537
            1_000_000_007,
            1_000_000_007 * 998_244_353, // semiprime ~ 2^60
            (1u64 << 61) - 1,            // Mersenne prime M61
            18_446_744_073_709_551_557,  // largest prime < 2^64
            2047,                        // base-2 strong pseudoprime, actually 23 * 89
            3_215_031_751,               // strong pseudoprime to bases 2,3,5,7
            (1u64 << 62) + 1,
            (4_000_000_007u64) * (4_000_000_009u64), // ~2^63.5 semiprime
            9_999_999_999_999_999_999,
        ];
        for &n in &cases {
            let want = matches!(
                Integer::from(n).is_probably_prime(40),
                IsPrime::Yes | IsPrime::Probably
            );
            assert_eq!(is_prime_u64(n), want, "is_prime_u64({n})");
            if n < 1u64 << 32 {
                assert_eq!(is_prime_u32(n), want, "is_prime_u32({n})");
            }
            if n & 1 == 1 && n > 2 {
                // a `false` base-2 result must be a genuine compositeness certificate
                if !is_probable_prime_base2(n) {
                    assert!(!want, "base-2 wrongly certified prime {n} composite");
                }
            }
        }
    }

    #[test]
    fn test_pollard_rho_splits_semiprimes() {
        // odd composites including a > 2^63 product; rho must return a proper factor.
        let cases: [u64; 5] = [
            23 * 89,
            1_000_000_007 * 998_244_353,
            4_294_967_291 * 4_294_967_279, // ~2^63.99, two large primes
            (4_000_000_007u64) * (4_000_000_009u64),
            3_215_031_751,
        ];
        for &n in &cases {
            let d = pollard_rho_u64(n);
            assert!(
                d > 1 && d < n && n.is_multiple_of(d),
                "pollard_rho_u64({n}) = {d}"
            );
        }

        // stress: every product of two distinct small primes. Small factors make the
        // cycle close quickly, exercising the batch-overshoot backtrack path.
        for (i, &p) in SMALL_PRIMES.iter().enumerate() {
            if p == 2 {
                continue; // odd composites only
            }
            for &qf in SMALL_PRIMES.iter().skip(i + 1) {
                if qf == 2 {
                    continue;
                }
                let n = p as u64 * qf as u64;
                let d = pollard_rho_u64(n);
                assert!(
                    d > 1 && d < n && n.is_multiple_of(d),
                    "pollard_rho_u64({n}) = {d}"
                );
            }
        }
    }

    #[test]
    fn test_shanks_tonelli() {
        let mut p = Integer::from(2);
        for _ in 0..100 {
            p = p.next_prime();
            //println!("p = {p}:");
            let mut num_squares_mod_p = 0;
            let mut num_nonsquares_mod_p = 0;
            for a in 1..p.to_i32().unwrap() {
                let root = square_root_mod_p(&Integer::from(a), &p);
                //println!("{root:?}");
                match root {
                    Ok(_) => num_squares_mod_p += 1,
                    Err(NumberTheoryError::IsNonsquare(_, _)) => num_nonsquares_mod_p += 1,
                    _ => (),
                }
            }
            assert_eq!(num_squares_mod_p, p.clone() >> 1);
            assert_eq!(num_nonsquares_mod_p, p.clone() >> 1);
        }
        //let a = Integer::from_str("680564733841876926926749214863536422913").unwrap();
        //let p = Integer::from_str("16777217").unwrap(); // Carmichael number!
        //assert_eq!(p.is_probably_prime(10), IsPrime::No);
        //let x = square_mod_p(&a, &p);
        //assert_eq!(x.square() % p, a);
    }

    #[test]
    fn test_lift_square_root_mod_q2() {
        let q = Integer::from(97);
        for n in 1..97 {
            let a = Integer::from(n);
            if a.legendre(&q) == 1 {
                let root = square_root_mod_p(&a, &q).unwrap();
                let lifted = lift_square_root_mod_q2(&a, &root, &q).unwrap();
                assert_eq!(lifted.square() % q.clone().square(), a);
            }
        }
    }
}
