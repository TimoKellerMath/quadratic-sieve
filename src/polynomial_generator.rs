use rug::{Assign, Integer};
use std::fmt::Debug;

/// A sieving polynomial Q(x) = a x^2 + 2 b x + c.
///
/// `a` and `q_inverse` are constant across the whole self-initialized set of
/// 2^(s-1) polynomials sharing one `a`, so they are borrowed from the generator
/// rather than cloned on every polynomial; only `b` and `c` change.
#[derive(Debug)]
pub struct Polynomial<'a> {
    pub a: &'a Integer,
    pub b: Integer,
    pub c: Integer,
    pub q_inverse: &'a Integer,
}

impl Polynomial<'_> {
    /// Writes Q(x) = ((a x + b) + b) x + c into `y`, reusing its allocation across
    /// candidates.
    pub fn evaluate(&self, x: i32, y: &mut Integer) {
        y.assign(self.a * x + &self.b);
        *y += &self.b;
        *y *= x;
        *y += &self.c;
    }

    /// The square root u = (a x + b) q^-1 of Q(x) modulo n, where b^2 - a c = n:
    /// a = q^2 and a Q(x) = (a x + b)^2 - n. Only needed for the candidates that
    /// give a relation.
    pub fn sqrt_mod(&self, x: i32, n: &Integer) -> Integer {
        let mut u = Integer::from(self.a * x + &self.b);
        u *= self.q_inverse;
        u %= n;
        debug_assert!({
            let mut y = Integer::new();
            self.evaluate(x, &mut y);
            (u.clone().square() - y).is_divisible(n)
        });
        u
    }
}

/// The roots of a sieving polynomial modulo each factor-base prime, in two arrays
/// so that loops over them need neither tags nor padding: prime `i` has the roots
/// `r1[i]` and `r2[i]`, which are equal if Q is linear modulo the prime (p | a),
/// and `r1[i] == Roots::NONE` if it has no roots.
#[derive(Debug, Clone, Default)]
pub struct Roots {
    pub r1: Vec<u32>,
    pub r2: Vec<u32>,
}

impl Roots {
    /// Marks a prime without roots (a root is always below its prime).
    pub const NONE: u32 = u32::MAX;

    /// The roots modulo prime `i`, if it has any.
    #[inline]
    pub fn get(&self, i: usize) -> Option<(u32, u32)> {
        let r1 = self.r1[i];
        (r1 != Self::NONE).then(|| (r1, self.r2[i]))
    }

    /// Appends the roots modulo the next prime.
    pub fn push(&mut self, roots: Option<(u32, u32)>) {
        let (r1, r2) = roots.unwrap_or((Self::NONE, Self::NONE));
        self.r1.push(r1);
        self.r2.push(r2);
    }

    /// The number of primes.
    pub fn len(&self) -> usize {
        self.r1.len()
    }

    /// Whether there are no primes.
    pub fn is_empty(&self) -> bool {
        self.r1.is_empty()
    }

    /// Removes all primes, keeping the allocations.
    pub fn clear(&mut self) {
        self.r1.clear();
        self.r2.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // an n of about 100 bits, whose polynomials yield every kind of relation
    fn example_n() -> Integer {
        let p = ((Integer::from(1) << 49u32) + 12345u32).next_prime();
        let q = ((Integer::from(1) << 50u32) + 67890u32).next_prime();
        p * q
    }

    // a·Q(x) = (a x + b)^2 - n and u^2 ≡ Q(x) (mod n)
    #[test]
    fn evaluation_gives_a_congruence_of_squares() {
        let n = example_n();
        let factorbase = crate::factorbase::make_factorbase(&n, 300);
        let n_roots = crate::factorbase::square_roots_mod_factorbase(&n, &factorbase);
        let mut generators = crate::siqs_generator::new_polynomial_generators(
            &n,
            65536,
            1,
            &factorbase,
            &n_roots,
            &factorbase,
        );
        let (polynomial, _) = generators[0].next_polynomial();
        let mut y = Integer::new();
        for x in [-65536, -1000, -1, 0, 1, 777, 65535] {
            polynomial.evaluate(x, &mut y);
            let ax_b = polynomial.a.clone() * x + &polynomial.b;
            assert_eq!(polynomial.a.clone() * &y, ax_b.square() - &n, "x = {x}");
            let u = polynomial.sqrt_mod(x, &n);
            assert!((u.square() - &y).is_divisible(&n), "x = {x}");
        }
    }
}
