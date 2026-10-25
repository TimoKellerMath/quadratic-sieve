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
    // compute (u,y) with u^2 = v (n), writing into the caller-owned `u` and `y` so their
    // allocations are reused across candidates instead of allocating a fresh pair per
    // survivor (the common case is a non-relation, where the result is just discarded).
    // y = ((a x + b) + b) * x + c = ax^2 + 2bx + c = Q(x) = ((qx + b)^2 - n)/q
    // u = (qx + b) * q^-1 (n)
    pub fn evaluate(&self, x: i32, n: &Integer, u: &mut Integer, y: &mut Integer) {
        y.assign(self.a * x + &self.b);
        // u = qx + b
        u.assign(&*y);
        *y += &self.b;
        *y *= x;
        *y += &self.c; // y = ux + c = qx^2 + 2bx + c = qx^2 + 2bx + (b^2-n)/q^2
        // qy = (qx)^2 + 2b(qx) + (b^2-n)/q = (qx+b)^2 - b^2 + qc = u^2 - (b^2 + qc)
        debug_assert_eq!(y.clone() * self.a, u.clone().square() - n);
        // u = (qx+b)/q = x + b/q (mod n)
        *u *= self.q_inverse;
        *u %= n;
        // (u/q)^2 = x^2 + 2bx/q + (b^2/q^2) =!= y = qx^2 + 2bx + c (mod n)
        debug_assert!((u.clone().square() - y.clone()).is_divisible(n));
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
        let (mut u, mut y) = (Integer::new(), Integer::new());
        for x in [-65536, -1000, -1, 0, 1, 777, 65535] {
            polynomial.evaluate(x, &n, &mut u, &mut y);
            let ax_b = polynomial.a.clone() * x + &polynomial.b;
            assert_eq!(polynomial.a.clone() * &y, ax_b.square() - &n, "x = {x}");
            assert!((u.clone().square() - &y).is_divisible(&n), "x = {x}");
        }
    }
}
