use fixedbitset::FixedBitSet;
use rug::Integer;
use rustc_hash::FxHashMap;

/// An unordered set of at most two large primes attached to a (partial) relation.
/// Empty slots are stored as 1 (no prime equals 1), with `a <= b` so the larger
/// prime — the pivot used by [`PartialRelations`] — is always `b`.
#[derive(Clone, Copy)]
struct LargePrimes {
    a: u32,
    b: u32,
}

impl LargePrimes {
    fn new(p: u32, q: u32) -> LargePrimes {
        if p <= q {
            LargePrimes { a: p, b: q }
        } else {
            LargePrimes { a: q, b: p }
        }
    }

    // the largest prime in the set, or 1 if the set is empty
    #[inline]
    fn pivot(self) -> u32 {
        self.b
    }

    // symmetric difference: primes appearing an odd number of times across the two
    // sets. The two sets always share their pivot, so the result has at most two
    // elements. Computed by odd-count over all four slots (order-independent: a
    // running 2-slot toggle could transiently overflow before the shared pivot
    // cancels).
    fn symmetric_difference(self, other: LargePrimes) -> LargePrimes {
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
        LargePrimes::new(out[0], out[1])
    }
}

/// Combines partial relations (those left with one or two large primes after trial
/// division) into full relations.
///
/// Each partial is an edge in a graph whose vertices are large primes; a full
/// relation is a cycle, in which every large prime occurs an even number of times
/// and therefore cancels. Cycles are detected incrementally by Gaussian elimination
/// over GF(2): `reps[p]` holds a stored relation whose pivot (largest) large prime
/// is `p`. A new partial is reduced against the stored relations, eliminating its
/// pivot at each step (the pivot strictly decreases, so this terminates); if its
/// prime set becomes empty it is a completed full relation, otherwise it becomes the
/// representative for its remaining pivot.
///
/// The single-large-prime variation is the special case where every set has one
/// element: two partials sharing a prime immediately reduce to a full relation.
#[derive(Default)]
pub struct PartialRelations {
    reps: FxHashMap<u32, (FixedBitSet, Integer, Integer, LargePrimes)>,
}

impl PartialRelations {
    pub fn new() -> PartialRelations {
        PartialRelations::default()
    }

    /// Feed a partial relation with large primes `p` and `q` (1 = none). Returns the
    /// combined `(relation, u, v)` if it completes a full relation, else stores it.
    pub fn add(
        &mut self,
        mut relation: FixedBitSet,
        mut u: Integer,
        mut v: Integer,
        p: u32,
        q: u32,
    ) -> Option<(FixedBitSet, Integer, Integer)> {
        let mut primes = LargePrimes::new(p, q);
        loop {
            let pivot = primes.pivot();
            if pivot == 1 {
                // no large primes left: this is a full relation
                return Some((relation, u, v));
            }
            if let Some((relation2, u2, v2, primes2)) = self.reps.get(&pivot) {
                // eliminate the pivot by multiplying with its representative; the
                // shared pivot enters v squared, which find_factor handles as a square
                relation ^= relation2;
                u *= u2;
                v *= v2;
                primes = primes.symmetric_difference(*primes2);
            } else {
                // new pivot: store this relation as its representative
                self.reps.insert(pivot, (relation, u, v, primes));
                return None;
            }
        }
    }
}

/// Storage for partial relations, selecting the cheapest scheme for the variation in
/// use. With the double large prime variation disabled, partials carry a single large
/// prime and are matched directly through a hash map (the original, lowest-overhead
/// path). With it enabled, partials carry up to two large primes and are combined
/// through the cycle-finding graph in [`PartialRelations`].
pub enum PartialStore {
    Single(FxHashMap<u32, (FixedBitSet, Integer, Integer)>),
    Double(PartialRelations),
}

impl PartialStore {
    pub fn new(use_dlp: bool) -> PartialStore {
        if use_dlp {
            PartialStore::Double(PartialRelations::new())
        } else {
            PartialStore::Single(FxHashMap::default())
        }
    }

    /// Feed a partial relation with large primes `p` and `q` (1 = none; in the
    /// single-prime path `q` is always 1). Returns the combined `(relation, u, v)`
    /// once it completes a full relation, otherwise stores it and returns None.
    pub fn add(
        &mut self,
        mut relation: FixedBitSet,
        mut u: Integer,
        mut v: Integer,
        p: u32,
        q: u32,
    ) -> Option<(FixedBitSet, Integer, Integer)> {
        match self {
            // original single-large-prime hash map: two partials sharing the prime
            // combine into a full relation; the first one is kept as the match.
            PartialStore::Single(map) => {
                debug_assert_eq!(q, 1);
                if let Some((relation2, u2, v2)) = map.get(&p) {
                    relation ^= relation2;
                    u *= u2;
                    v *= v2;
                    Some((relation, u, v))
                } else {
                    map.insert(p, (relation, u, v));
                    None
                }
            }
            PartialStore::Double(graph) => graph.add(relation, u, v, p, q),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // a relation over `len` columns with the given bits set
    fn bits(ones: &[usize], len: usize) -> FixedBitSet {
        let mut relation = FixedBitSet::with_capacity(len);
        for &i in ones {
            relation.insert(i);
        }
        relation
    }

    #[test]
    fn large_prime_sets_cancel_shared_primes() {
        let set = LargePrimes::new;
        let elements = |primes: LargePrimes| (primes.a, primes.b);
        assert_eq!(elements(set(7, 1).symmetric_difference(set(7, 1))), (1, 1));
        assert_eq!(elements(set(3, 7).symmetric_difference(set(7, 1))), (1, 3));
        assert_eq!(elements(set(7, 3).symmetric_difference(set(5, 7))), (3, 5));
        assert_eq!(elements(set(1, 1).symmetric_difference(set(5, 1))), (1, 5));
    }

    // Partials with the large primes {11}, {11, 13} and {13} form a cycle; the
    // third completes a full relation combining all three.
    #[test]
    fn partials_on_a_cycle_combine_into_a_full_relation() {
        let mut partials = PartialRelations::new();
        let a = (bits(&[0, 2], 8), Integer::from(3), Integer::from(5));
        let b = (bits(&[2, 4], 8), Integer::from(7), Integer::from(9));
        let c = (bits(&[4, 5], 8), Integer::from(11), Integer::from(13));
        assert!(partials.add(a.0.clone(), a.1, a.2, 11, 1).is_none());
        assert!(partials.add(b.0.clone(), b.1, b.2, 11, 13).is_none());
        let (relation, u, v) = partials.add(c.0.clone(), c.1, c.2, 13, 1).unwrap();
        let mut expected = a.0;
        expected ^= &b.0;
        expected ^= &c.0;
        assert_eq!(relation, expected);
        assert_eq!(u, 3 * 7 * 11);
        assert_eq!(v, 5 * 9 * 13);
    }

    // With single large primes only, the cycle graph combines exactly like the
    // plain hash map.
    #[test]
    fn single_and_double_large_prime_storage_agree_on_single_primes() {
        let mut single = PartialStore::new(false);
        let mut double = PartialStore::new(true);
        let mut combined = 0;
        for (i, &p) in [11u32, 13, 11, 17, 13, 11, 19].iter().enumerate() {
            let relation = bits(&[i % 8], 8);
            let (u, v) = (Integer::from(2 * i + 3), Integer::from(2 * i + 5));
            let from_single = single.add(relation.clone(), u.clone(), v.clone(), p, 1);
            let from_double = double.add(relation, u, v, p, 1);
            assert_eq!(from_single, from_double, "partial {i} with large prime {p}");
            combined += from_single.is_some() as usize;
        }
        assert_eq!(combined, 3);
    }
}
