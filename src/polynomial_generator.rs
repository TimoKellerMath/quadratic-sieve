use rug::Integer;
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
