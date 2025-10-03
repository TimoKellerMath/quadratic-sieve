use std::fmt::{self, Debug};

//use rug::ops::SubFrom;
//use num_traits::{Zero};
use rug::integer::IsPrime;
use rug::{Complete, Integer};
//use rug::ops::DivRounding;

use rand::Rng;

// TODO: use rug's Error
#[derive(Debug, Clone)]
pub enum NumberTheoryError {
    //IsZero,
    //IsNotPositive(Integer),
    IsEven(Integer),
    //NotPrime(Integer),
    NotCoprime(Integer, Integer),
    IsNonsquare(Integer, Integer),
    AlgorithmFailed,
}

impl fmt::Display for NumberTheoryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            //NumberTheoryError::IsZero => write!(f, "is zero"),
            //NumberTheoryError::IsNotPositive(a) => write!(f, "{a} < 0"),
            NumberTheoryError::IsEven(a) => write!(f, "{a} is even"),
            //NumberTheoryError::NotPrime(a) => write!(f, "{a} not prime"),
            NumberTheoryError::NotCoprime(a, b) => write!(f, "gcd({a}, {b}) != 1"),
            NumberTheoryError::IsNonsquare(a, p) => write!(f, "{a} not a square mod {p}"),
            NumberTheoryError::AlgorithmFailed => write!(f, "algorithm failed"),
        }
    }
}

/* https://doc.rust-lang.org/rust-by-example/error/multiple_error_types/wrap_error.html
cast error
impl std::error::Error for NumberTheoryError {
    fn description(&self) -> &str {
        self.fmt(f)
    }
}*/

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

// return a small prime factor of n
#[inline]
pub fn trial_division(n: &Integer) -> Option<u32> {
    SMALL_PRIMES
        .iter()
        .find_map(|&p| if n.is_divisible_u(p) { Some(p) } else { None })
}

// return true if n is divisible by a small prime and not equal to a small prime
#[inline]
pub fn is_small_composite(n: &Integer) -> bool {
    SMALL_PRIMES.iter().any(|&p| *n != p && n.is_divisible_u(p))
}

// compute a^2 (mod p)
#[inline]
pub fn square_mod_p(a: &Integer, p: &Integer) -> Integer {
    a.square_ref().complete() % p
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

pub fn is_pseudo_prime(n: &Integer, num_tries: usize) -> bool {
    if n <= &Integer::from(1) {
        return false;
    }
    if n <= &Integer::from(3) {
        return true;
    }
    if n.is_even() || is_small_composite(n) {
        // even and != 2?
        return false;
    }
    let n_minus_one = n - Integer::from(1);
    let (odd_part, power_of_2) = factor_out_power_of_2(&n_minus_one);

    let mut rng = rand::thread_rng();
    'outer: for _ in 0..num_tries {
        // Miller-Rabin test
        let base = Integer::from(rng.gen_range(2..1024));
        if base.gcd_ref(n).complete() != 1 {
            return false;
        }

        let mut a = base.pow_mod_ref(&odd_part, n).unwrap().complete();
        if a == 1 {
            continue;
        }
        for _ in 0..power_of_2 {
            if a == n_minus_one {
                // a = -1 (n)
                continue 'outer;
            }
            a = square_mod_p(&a, n);
        }
        if a != 1 {
            return false;
        }
    }
    true
}

pub fn next_pseudo_prime(n: &Integer, num_tries: usize) -> Integer {
    if n <= &Integer::from(1) {
        return Integer::from(2);
    }
    if n == &Integer::from(2) {
        return Integer::from(3);
    }
    let mut p = n.clone(); // n >= 3
    if p.is_even() {
        // ensure p odd
        p += 1;
    }
    loop {
        p += 2;
        if is_pseudo_prime(&p, num_tries) {
            return p;
        }
    }
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
    let mut a = Integer::from(2);
    loop {
        if a.legendre(p) == -1 {
            return Ok(a);
        }
        a += 1;
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

// one square root of x (mod p^2)
// s^2 = x (p)  ==>
// S^2 = x (p^2) with S = (s + x s^-1)/2 = (s^2 + x)(2s)^-1 (mod p^2)
pub fn square_root_mod_p2(x: &Integer, p: &Integer) -> Result<Integer, NumberTheoryError> {
    debug_assert!(p > &Integer::from(2));
    let sqrt_mod_p: Integer = square_root_mod_p(x, p)?;
    //debug_assert!((sqrt_mod_p.clone().square() - x).is_divisible(&p));
    let p_square = p.square_ref().complete();
    let mut a: Integer = (&sqrt_mod_p << 1u32).complete();
    match a.invert_mut(&p_square) {
        // a = (2s)^-1 (mod p^2)
        Ok(()) => (),
        Err(_) => return Err(NumberTheoryError::NotCoprime(a, p_square)),
    }
    let sqrt_mod_p2 = ((sqrt_mod_p.square_ref() + x).complete() * a) % p_square; // S = (s^2 + x)/(2s) (mod p^2)
    Ok(sqrt_mod_p2)
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

// compute (a,n) with a = a_i (mod n_i)
pub fn chinese_remainder_theorem(
    residues_and_moduli: &[(&Integer, &Integer)],
) -> Result<(Integer, Integer), NumberTheoryError> {
    let mut n_result = Integer::from(1);
    let mut a_result = Integer::from(0);
    // TODO: consider doing it directly
    for (a, n) in residues_and_moduli.iter() {
        // a' = a (n)
        // a' = a_result (n_result)
        // a' = a n_result (n_result^-1 mod n) + a_result n (n^-1 mod a_result)
        let n_result_inverse = match n_result.invert_ref(n) {
            Some(a) => a,
            None => {
                return Err(NumberTheoryError::NotCoprime(
                    n_result.clone(),
                    (*n).clone(),
                ));
            }
        };
        let n_inverse = match n.invert_ref(&n_result) {
            Some(a) => a,
            None => {
                return Err(NumberTheoryError::NotCoprime(
                    n_result.clone(),
                    (*n).clone(),
                ));
            }
        };
        //a_result = *a * n_result.clone() * n_result_inverse.complete() + a_result * *n * n_inverse.complete();
        a_result *= *n * n_inverse.complete();
        a_result += *a * n_result.clone() * n_result_inverse.complete();
        n_result *= *n;
    }
    Ok((a_result, n_result.clone()))
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use rug::integer::IsPrime;

    use super::*;

    #[test]
    fn test_is_pseudoprime() {
        let p = Integer::from_str("16777217").unwrap(); // Carmichael number!
        assert_eq!(p.is_probably_prime(10), IsPrime::No);
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
    fn test_square_root_mod_p2() {
        let p = Integer::from(97);
        for n in 1..97 {
            let a = Integer::from(n);
            if a.legendre(&p) == 1 {
                let x = square_root_mod_p2(&a, &p);
                match x {
                    Ok(x) => assert_eq!(x.square() % p.clone().square(), a),
                    Err(_) => panic!("tried to take root of non-square"),
                }
            }
        }
    }

    #[test]
    fn test_crt() {
        if let Ok((a, _)) = chinese_remainder_theorem(&[
            (&Integer::from(1), &Integer::from(10)),
            (&Integer::from(2), &Integer::from(137)),
        ]) {
            assert_eq!(a.clone() % 10, 1);
            assert_eq!(a.clone() % 137, 2);
        };
    }
}
