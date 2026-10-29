use rug::Integer;
use std::cmp::Ordering;

/// A relation u^2 ≡ v (mod kn), found by trial division or combined from partial
/// relations: the factor-base primes with an odd exponent in v, as sorted indices
/// into the factor base (index 0 stands for −1), and the large primes left in v.
#[derive(Debug, Clone, PartialEq)]
pub struct Relation {
    /// The square root of v modulo kn.
    pub u: Integer,
    /// Up to its sign, a product of factor-base primes and large primes.
    pub v: Integer,
    /// The indices of the factor-base primes with an odd exponent in v, in increasing
    /// order.
    pub factors: Vec<u32>,
    /// The large primes in v with an odd exponent.
    pub large_primes: LargePrimes,
}

impl Relation {
    /// Whether no large primes are left, so that the relation can go into the matrix.
    pub fn is_full(&self) -> bool {
        self.large_primes == LargePrimes::NONE
    }

    /// Multiplies `other` into this relation. Primes in both enter v squared, so the
    /// factor sets and the large primes combine by symmetric difference.
    pub fn combine(&mut self, other: &Relation) {
        self.factors = symmetric_difference(&self.factors, &other.factors);
        self.u *= &other.u;
        self.v *= &other.v;
        self.large_primes = self.large_primes.symmetric_difference(other.large_primes);
    }
}

// the elements in exactly one of the two sorted lists, sorted
fn symmetric_difference(a: &[u32], b: &[u32]) -> Vec<u32> {
    debug_assert!(a.is_sorted_by(|x, y| x < y) && b.is_sorted_by(|x, y| x < y));
    let mut result = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            Ordering::Less => {
                result.push(a[i]);
                i += 1;
            }
            Ordering::Greater => {
                result.push(b[j]);
                j += 1;
            }
            Ordering::Equal => {
                i += 1;
                j += 1;
            }
        }
    }
    result.extend_from_slice(&a[i..]);
    result.extend_from_slice(&b[j..]);
    result
}

/// The large primes left in a relation: none, one or two.
///
/// Stored in two slots with `a <= b`, where an empty slot holds 1 (no prime equals
/// 1): then [`crate::large_primes::PartialRelations`] can read the pair as an edge
/// between two vertices of its graph, 1 standing for no prime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LargePrimes {
    a: u32,
    b: u32,
}

impl LargePrimes {
    /// No large primes.
    pub const NONE: LargePrimes = LargePrimes { a: 1, b: 1 };

    /// One large prime.
    pub fn one(p: u32) -> LargePrimes {
        LargePrimes { a: 1, b: p }
    }

    /// Two large primes.
    pub fn two(p: u32, q: u32) -> LargePrimes {
        LargePrimes {
            a: p.min(q),
            b: p.max(q),
        }
    }

    /// The number of large primes.
    pub fn count(self) -> usize {
        (self.a != 1) as usize + (self.b != 1) as usize
    }

    // the largest prime in the set, or 1 if the set is empty
    #[inline]
    pub(crate) fn pivot(self) -> u32 {
        self.b
    }

    // the two slots, the smaller first: 1 stands for an empty one
    #[inline]
    pub(crate) fn pair(self) -> (u32, u32) {
        (self.a, self.b)
    }

    // symmetric difference: primes appearing an odd number of times across the two
    // sets. Combining along a cycle, the two sets always share a vertex (a prime, or
    // the empty slot), so the result has at most two elements. Computed by odd-count
    // over all four slots (order-independent: a running 2-slot toggle could
    // transiently overflow before the shared element cancels).
    pub(crate) fn symmetric_difference(self, other: LargePrimes) -> LargePrimes {
        let vals = [self.a, self.b, other.a, other.b];
        let mut out = [1u32; 2];
        let mut len = 0usize;
        for i in 0..vals.len() {
            let x = vals[i];
            // skip empty slots and values already emitted on an earlier index
            if x == 1 || vals[..i].contains(&x) {
                continue;
            }
            if vals.iter().filter(|&&y| y == x).count() % 2 == 1 {
                if len < 2 {
                    out[len] = x;
                }
                len += 1;
            }
        }
        debug_assert!(len <= 2, "large-prime set exceeded two elements");
        LargePrimes::two(out[0], out[1])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn factor_lists_combine_by_symmetric_difference() {
        assert_eq!(symmetric_difference(&[], &[]), Vec::<u32>::new());
        assert_eq!(symmetric_difference(&[1, 3, 5], &[]), vec![1, 3, 5]);
        assert_eq!(
            symmetric_difference(&[1, 3, 5], &[2, 3, 6]),
            vec![1, 2, 5, 6]
        );
        assert_eq!(symmetric_difference(&[0, 4], &[0, 4]), Vec::<u32>::new());
    }

    #[test]
    fn large_prime_sets_cancel_shared_primes() {
        let elements = |primes: LargePrimes| (primes.a, primes.b);
        let (one, two) = (LargePrimes::one, LargePrimes::two);
        assert_eq!(elements(one(7).symmetric_difference(one(7))), (1, 1));
        assert_eq!(elements(two(3, 7).symmetric_difference(one(7))), (1, 3));
        assert_eq!(elements(two(7, 3).symmetric_difference(two(5, 7))), (3, 5));
        assert_eq!(
            elements(LargePrimes::NONE.symmetric_difference(one(5))),
            (1, 5)
        );
        assert_eq!(
            [LargePrimes::NONE, one(5), two(3, 5)].map(LargePrimes::count),
            [0, 1, 2]
        );
    }
}
