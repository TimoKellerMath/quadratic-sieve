use num_traits::{Zero};
use rug::{Complete, Integer};

pub mod number_theory;
use crate::number_theory::{*};

// (p-1) factorization w.r.t. a base
// with big prime variation
fn factorize_p_minus_1_with_base(
    n: &Integer,
    base: &Integer,
    bound: u32,
) -> Result<Option<Integer>, NumberTheoryError> {
    let mut exponent = Integer::from(1);
    let mut base = base.clone();
    for e in 2..=bound {
        exponent *= e;
        if e % 32 == 0 {
            let _ = base.pow_mod_mut(&exponent, n);
            if base == 1 {
                return Err(NumberTheoryError::AlgorithmFailed); // base has small order mod n
            }
            let gcd = n.gcd_ref(&(base.clone() - Integer::ONE)).complete();
            if gcd != 1 && gcd != *n {
                return Ok(Some(gcd));
            }
            exponent = Integer::from(1);
        }
    }
    // large prime variation
    // precomputed base^(p_{i+1} - p_i)
    let mut powers = HashMap::<u32, Integer>::new();
    // compute base^{p_i}, bound <= p_i <= bound^2
    let mut p = Integer::from(bound - 1).next_prime();
    let mut next_p = p.clone().next_prime();
    let a = base.clone();
    base = base.pow_mod_ref(&p, n).unwrap().complete();
    while p <= Integer::from(bound).square_ref().complete() {
        let e = (next_p.clone() - p.clone()).to_u32().unwrap();
        let multiplier = powers.entry(e).or_insert(a.pow_mod_ref(&Integer::from(e), n).unwrap().complete());
        base *= multiplier.clone();
        base %= n;
        //debug_assert_eq!(a.pow_mod_ref(&next_p, n).unwrap().complete(), base);
        if base == 1 {
            return Err(NumberTheoryError::AlgorithmFailed); // base has small order mod n
        }
        let gcd = n.gcd_ref(&(base.clone() - Integer::ONE)).complete();
        if gcd != 1 && gcd != *n {
            return Ok(Some(gcd));
        }
        (p, next_p) = (next_p.clone(), next_p.clone().next_prime());
    }
    Ok(None) // no factor found
}

// (p-1) factorization
fn factorize_p_minus_1(n: &Integer, bound: u32, n_bases: usize) -> Option<Integer> {
    if let Some(p) = trial_division(n) { return Some(Integer::from(p)) };
    println!("no small factors");
    let mut base = Integer::from(2);
    for _ in 0..n_bases {
        println!("trying base {base}");
        let gcd = n.gcd_ref(&base).complete();
        if gcd != 1 {
            return Some(gcd);
        }
        if let Ok(result) = factorize_p_minus_1_with_base(n, &base, bound) { return result };
        base += 1;
    }
    None // no factor found
}

// x in F_{p^2}^*: x = a + b sqrt(r), a^2 - b^2 r = 1 [why not do p-1 and p+1 at the same time?]
fn pow_p_plus_1(x: &Integer, e: &Integer, p: &Integer) -> Integer {
    let mut x0 = x.clone();
    let mut x1: Integer = (x.clone().square() - 2) % p;
    for b in (0..e.significant_bits()).rev() {
        if e.get_bit(b) {
            x0 = (x0 * x1.clone() - x) % p;
            x1 = (x1.clone().square() - 2) % p;
        } else {
            x1 = (x0.clone() * x1 - x) % p;
            x0 = (x0.clone().square() - 2) % p;
        }
    }
    x0.clone()
}

// (p+1) factorization
fn factorize_p_plus_1(n: &Integer, bound: u32) -> Option<Integer> {
    let mut base = quadratic_non_residue_mod_p(n).unwrap();
    let mut exponent = Integer::from(1);
    for e in 2..bound {
        exponent *= e;
        if exponent.is_divisible_u(32) {
            base = pow_p_plus_1(&base.clone(), &exponent, n);
            let gcd = n.gcd_ref(&(base.clone() - Integer::from(1))).complete();
            if gcd != 1 {
                return Some(gcd);
            }
            let gcd = n.gcd_ref(&(base.clone() + Integer::from(1))).complete();
            if gcd != 1 {
                return Some(gcd);
            }
            exponent = Integer::from(1);
        }
    }
    None // no factor found
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use rug::integer::IsPrime;

    use super::*;

    #[test]
    pub fn test_p_minus_1_factorize() {
            let mut n = Integer::from(1);
        let mut p = Integer::from(1);
        while p < 103 {
            p = p.next_prime();
            n *= p.clone();
        }
        n += 1;
        let factor = factorize_p_minus_1(&n, 10000, 3).unwrap();
        assert!(factor != 1 && factor != n);
        let n2 = std::cmp::max(factor.clone(), n.div_exact(&factor));
        let factor2 = factorize_p_minus_1(&n2, 10000, 3).unwrap();
        assert!(factor2 != 1 && factor2 != n2);
        let n3 = std::cmp::max(factor2.clone(), n2.div_exact(&factor2));
        let factor3 = factorize_p_minus_1(&n3, 10000, 3).unwrap();
        assert!(factor3 != 1 && factor3 != n3);
    }

    #[test]
    fn test_p_plus_1_factorize() {
        let mut n = Integer::factorial(32).complete();
        n += 1;
        n = n.div_exact(&Integer::from(2281));
        let factor = factorize_p_plus_1(&n, 10000).unwrap();
        println!("factor1 = {factor}");
        assert!(factor != 1 && factor != n);
    }
}