use std::fmt::{self, Debug};

use num_bigint::{BigInt, RandBigInt};
use num_traits::{Zero, One, Signed};
use num_integer::{Integer};

#[derive(Debug)]
enum NumberTheoryError {
    //IsZero,
    IsNotPositive(BigInt),
    IsEven(BigInt),
    //NotPrime(BigInt),
    NotCoprime(BigInt, BigInt),
    IsNonsquare(BigInt, BigInt),
    AlgorithmFailed,
}

impl fmt::Display for NumberTheoryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            //NumberTheoryError::IsZero => write!(f, "is zero"),
            NumberTheoryError::IsNotPositive(a) => write!(f, "{a} < 0"),
            NumberTheoryError::IsEven(a) => write!(f, "{a} is even"),
            //NumberTheoryError::NotPrime(a) => write!(f, "{a} not prime"),
            NumberTheoryError::NotCoprime(a,b) => write!(f, "gcd({a}, {b}) != 1"), 
            NumberTheoryError::IsNonsquare(a,p) => write!(f, "{a} not a square mod {p}"),
            NumberTheoryError::AlgorithmFailed => write!(f, "algorithm failed"),
        }
    }
}

/*
impl std::error::Error for NumberTheoryError {
    fn description(&self) -> &str {
        self.fmt(f)
    }
}*/

const SMALL_PRIMES: [i32; 70] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349];

fn trial_division(n: &BigInt) -> Option<i32> {
    return SMALL_PRIMES.iter().find_map(|&p| if n.is_multiple_of(&BigInt::from(p)) {Some(p)} else {None});
}

fn is_small_composite(n: &BigInt) -> bool {
    if SMALL_PRIMES.iter().any(|&p| *n == BigInt::from(p)) {
        return false;
    }
    return SMALL_PRIMES.iter().any(|&p| n.is_multiple_of(&BigInt::from(p)));
}

fn is_pseudo_prime(n: &BigInt, num_tries: usize) -> bool {
    if *n <= BigInt::one() {
        return false;
    }
    if *n <= BigInt::from(3) {
        return true;
    }
    if n.is_even() || is_small_composite(n) { // even and != 2?
        return false;
    }
    let n_minus_one = n - BigInt::one();
    let power_of_2 = n_minus_one.trailing_zeros().unwrap();
    let odd_part = &n_minus_one >> power_of_2;

    let mut rng = rand::thread_rng();
    'outer: for _ in 0..num_tries {
        // Miller-Rabin test
        let base = rng.gen_bigint_range(&BigInt::from(2), &n_minus_one);
        if !base.gcd(n).is_one() {
            return false;
        }

        let mut a = base.modpow(&odd_part, &n);
        if a.is_one() {
            continue;
        }
        for _ in 0..power_of_2 {
            if a == n_minus_one { // a = -1 (n)
                continue 'outer;
            }
            a = square_mod_p(&a, n);
        }
        if !a.is_one() {
            return false;
        }
    }
    return true;
}

fn next_pseudo_prime(n: &BigInt, num_tries: usize) -> BigInt {
    if *n <= BigInt::one() {
        return BigInt::from(2);
    }
    if *n == BigInt::from(2) {
        return BigInt::from(3);
    }
    let mut p = n.clone(); // n >= 3
    if p.is_even() { // ensure p odd
        p.inc();
    }
    loop {
        p += BigInt::from(2);
        if is_pseudo_prime(&p, num_tries) {
            return p;
        }
    }
}

fn is_square_mod_p(a_: &BigInt, p_: &BigInt) -> Result<bool,NumberTheoryError> {
    if *p_ <= BigInt::ZERO {
        return Err(NumberTheoryError::IsNotPositive(p_.clone()));
    }
    if p_.is_even() {
        return Err(NumberTheoryError::IsEven(p_.clone()));
    }
    if !a_.gcd(p_).is_one() {
        return Err(NumberTheoryError::NotCoprime(a_.clone(), p_.clone()));
    }
    let mut a = a_.clone();
    let mut p = p_.clone();
    let mut result = true;
    while !a.is_one() && !a.is_zero() {
        // reduce a to half-system (-p/2, p/2)
        if a > (p.clone() >> 1) { // p >> 1 = (p-1)/2 since p is odd
            a -= p.clone();
        }
        // first supplementary law
        if a.is_negative() {
            if p.bit(1) { // p = 3 (4)?
                result = !result;
            }
            a = -a;
        }
        // second supplementary law
        let order = match a.trailing_zeros() {
            Some(i) => i,
            None => panic!("is_square_mod_p: a == 0"), // a == 0 should never happen (while condition)
        };
        if (order % 2 == 1) && (p.bit(1) ^ p.bit(2)) { // p = +-3 (8)?
            result = !result;
        }
        a >>= order;
        // quadratic reciprocity
        if a.bit(1) && p.bit(1) { // a = p = 3 (4)?
            result = !result;
        }
        (p, a) = (a.clone(), p % a);
    }
    let jacobi_symbol = a_.modpow(&(p_.clone() >> 1), &p_.clone()); // p/2 = (p-1)/2 since p is odd
    assert!((jacobi_symbol == BigInt::one()) == result); // sanity check: is Euler's criterion satisfied?
    return Ok(result);
}

fn quadratic_non_residue_mod_p(p: &BigInt) -> Result<BigInt, NumberTheoryError> {
    if p.is_even() {
        return Err(NumberTheoryError::IsEven(p.clone()));
    }
    let mut rng = rand::thread_rng();
    let p_minus_one = p - BigInt::one();
    if p.bit(1) { // p = 3 (4) => 
        return Ok(p_minus_one); // -1 is a quadratic non-residue
    }
    loop {
        let a = rng.gen_bigint_range(&BigInt::from(2), &p_minus_one);
        if !is_square_mod_p(&a, &p)? {
            return Ok(a);
        }
    }
}

fn square_mod_p(a: &BigInt, p: &BigInt) -> BigInt {
    return (a * a) % p;
}

// Shanks-Tonelli algorithm
fn square_root_mod_p(a: &BigInt, p: &BigInt) -> Result<BigInt, NumberTheoryError> {
    if a.is_zero() || *p == BigInt::from(2) {
        return Ok(a.clone());
    }
    if !is_square_mod_p(a, p)? {
        return Err(NumberTheoryError::IsNonsquare(a.clone(), p.clone()));
    }
    let mut k = match (p.clone() - BigInt::one()).trailing_zeros() {
        Some(i) => i,
        None => return Ok(a.clone()), // a == 0
    };
    assert!(k > 0);
    let m = p.clone() >> k;
    assert!(m.is_odd());
    let mut m_plus_1_div_2 = m.clone();
    m_plus_1_div_2.inc();
    m_plus_1_div_2 >>= 1;
    let mut r = a.modpow(&m_plus_1_div_2, p);
    let mut n = a.modpow(&m, p);
    let mut an = a.clone() * n.clone();
    an %= p;
    assert!(r.modpow(&BigInt::from(2), p) == an);
    if n.is_one() {
        //assert!(r.modpow(&BigInt::from(2), p) == *a);
        assert_eq!(square_mod_p(&r, p), *a);
        return Ok(r);
    }
    let z = quadratic_non_residue_mod_p(p)?;
    while !n.is_one() {
        let mut k_ = 0;
        let mut n_ = n.clone();
        assert!(n_.modpow(&(BigInt::from(1) << (k-1)), p).is_one()); // the order of n_ (mod p) divides 2^(k-1)
        while !n_.is_one() { // determine its order 2^k_ with k_ < k
            //n_ = n_.modpow(&BigInt::from(2), p);
            n_ = square_mod_p(&n_, p);
            k_ += 1;
        }
        assert!(k_ < k);
        let c = z.modpow(&m, p);
        let mut c_ = c.modpow(&(BigInt::one() << (k - k_ - 1)), p);
        r *= c_.clone();
        r %= p;
        //c_ = c_.modpow(&BigInt::from(2), p);
        c_ = square_mod_p(&c_, p);
        n *= c_;
        n %= p;
        k = k_;
    }
    //assert!(r.modpow(&BigInt::from(2), p) == *a);
    assert_eq!(square_mod_p(&r, p), *a);
    return Ok(r);
}

/*
impl Iterator for std::ops::RangeInclusive<BigInt> {
    type Item = BigInt;

    #[inline]
    fn next(&mut self) -> Option<BigInt> {
        if self.0 < self.1 {
            self.0.inc();
            Some(v)
        } else {
            None
        }
    }
}*/

fn chinese_remainder_theorem(residues_and_moduli: &[(&BigInt, &BigInt)]) -> Result<(BigInt,BigInt), NumberTheoryError> {
    let mut n_result = BigInt::one();
    let mut a_result = BigInt::zero();
    for (a,n) in residues_and_moduli.iter() {
        // a' = a (n)
        // a' = a_result (n_result)
        // a' = a n_result (n_result^-1 mod n) + a_result n (n^-1 mod a_result)
        let n_result_inverse = n_result.modinv(n).ok_or(NumberTheoryError::NotCoprime(n_result.clone(), (*n).clone()))?;
        let n_inverse = n.modinv(&n_result).ok_or(NumberTheoryError::NotCoprime(n_result.clone(), (*n).clone()))?;
        a_result = *a * n_result.clone() * n_result_inverse + a_result * *n * n_inverse;
        n_result *= *n;
    }
    return Ok((a_result,n_result));
}

fn factorize_p_minus_1_with_base(n: &BigInt, base: &BigInt, bound: u32) -> Result<Option<BigInt>,NumberTheoryError> {
    let mut exponent = BigInt::one();
    let mut base = base.clone();
    for e in 2..=bound {
        exponent *= e;
        if e % 32 == 0 {
            base = base.clone().modpow(&exponent, n);
            if base.is_one() {
                return Err(NumberTheoryError::AlgorithmFailed); // base has small order mod n
            }
            assert!(base < *n);
            let gcd = n.gcd(&(base.clone() - BigInt::one()));
            assert!(gcd != *n);
            if !gcd.is_one() && gcd != *n {
                return Ok(Some(gcd));
            }
            exponent = BigInt::one();
        }
    }
    return Ok(None); // no factor found
}

fn factorize_p_minus_1(n: &BigInt, bound: u32, n_bases: usize) -> Option<BigInt> {
    match trial_division(n) {
        Some(p) => {return Some(BigInt::from(p))},
        None => (),
    }
    let mut rng = rand::thread_rng();
    for _ in 0..n_bases {
        let base = rng.gen_bigint_range(&BigInt::from(2), &(n.clone() - BigInt::from(2)));
        let gcd = n.gcd(&base);
        if !gcd.is_one() {
            return Some(gcd);
        }
        match factorize_p_minus_1_with_base(n, &base, bound) {
            Ok(result) => return result,
            Err(_) => (),
        }
    }
    return None; // no factor found
}
/*
// x in F_{p^2}^*: x = a + b sqrt(r), a^2 - b^2 r = 1 [why not do p-1 and p+1 at the same time?]
fn pow(x: quadratic_element, e: usize), r: &BigInt, p: &BigInt) {
}

fn factorize_p_plus_1(n: &BigInt, bound: u32) -> Option<BigInt> {
    //let mut N = BigInt::one();
    let mut a = quadratic_element(BigInt::from(1), BigInt::one());
    let gcd = n.gcd(&a);
    if !gcd.is_one() {
        return Some(gcd);
    }
    let r = quadratic_non_residue(n)?;
    for e in 2..bound {
        //let e_ = BigInt::from(e);
        //N = N.lcm(&e_);
        for _ in 0..e {
            a = mul(a, a, &r, n);
        }
        let gcd = n.gcd(&(a.clone() - BigInt::one()));
        if !gcd.is_one() {
            return Some(gcd);
        }
        let gcd = n.gcd(&(a.clone() + BigInt::one()));
        if !gcd.is_one() {
            return Some(gcd);
        }
    }
    return None; // no factor found
}*/

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_pseudo_prime() {
        for p in SMALL_PRIMES {
            debug_assert!(is_pseudo_prime(&BigInt::from(p), 5), "{p} not pseudo prime");
        }
    }

    #[test]
    fn test_next_pseudo_prime() {  
        let mut primes = Vec::<BigInt>::new();
        let mut n = BigInt::from(0);
        while primes.len() < SMALL_PRIMES.len() {
            n = next_pseudo_prime(&n, 5);
            primes.push(n.clone());
        }
        println!("{primes:?}");
        //assert_eq!(SMALL_PRIMES.map(|n| BigInt::from(n)).iter().collect::<Vec<BigInt>>(), primes.as_slice());
        for (i,p) in primes.iter().enumerate() {
            assert_eq!(*p, BigInt::from(SMALL_PRIMES[i]));
        }
    }
}

fn main() {
    for n in 2..100 {
        println!("{n} is prime: {}", is_pseudo_prime(&BigInt::from(n), 5));
    }

    for k in 0..=100 {
        let mut n = BigInt::one();
        n <<= k;
        println!("p >= 2^{k}: {}", next_pseudo_prime(&n, 5));
    }

    let p = BigInt::from(37);
    for n in 0..=37 {
        print!("{n} is square mod {p}: ");
        let result = is_square_mod_p(&BigInt::from(n), &p);
        match result {
            Ok(sq) => {print!("{sq} with root "); let root = square_root_mod_p(&BigInt::from(n), &p);
            match root {
                Ok(sq) => println!("{sq}"),
                Err(e) => println!("{e}"),
            };},
            Err(e) => println!("{e}"),
        };
    }

    for n in (1i64 << 10)..=(1i64 << 10) + 100 {
        println!("{:?}", factorize_p_minus_1(&BigInt::from(n), 1 << 14, 3));
    }

    let mut n = BigInt::one();
    for p in SMALL_PRIMES {
        if p > 103 {
            break;
        }
        n *= p;
    }
    n.inc();
    println!("{:?}", factorize_p_minus_1(&n, 10000, 3));

    println!("{:?}", chinese_remainder_theorem(&[(&BigInt::one(), &BigInt::from(10)), (&BigInt::from(2), &BigInt::from(137))]));
}
