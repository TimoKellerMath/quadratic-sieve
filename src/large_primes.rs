use crate::relation::{LargePrimes, Relation};
use rustc_hash::FxHashMap;

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
/// The single large prime variation is the special case where every set has one
/// element: two partials sharing a prime immediately reduce to a full relation.
#[derive(Default)]
pub struct PartialRelations {
    reps: FxHashMap<u32, Relation>,
}

impl PartialRelations {
    /// An empty graph.
    pub fn new() -> PartialRelations {
        PartialRelations::default()
    }

    /// Adds a partial relation. Returns the full relation it completes, if any;
    /// otherwise the partial is stored.
    pub fn add(&mut self, mut relation: Relation) -> Option<Relation> {
        loop {
            let pivot = relation.large_primes.pivot();
            if pivot == 1 {
                // no large primes left: this is a full relation
                return Some(relation);
            }
            if let Some(representative) = self.reps.get(&pivot) {
                // eliminate the pivot by multiplying with its representative; the
                // shared pivot enters v squared, which find_factor handles as a square
                relation.combine(representative);
            } else {
                // new pivot: store this relation as its representative
                self.reps.insert(pivot, relation);
                return None;
            }
        }
    }
}

/// Storage for partial relations, with the cheaper scheme for the large prime
/// variation in use.
pub enum PartialStore {
    /// Single large primes: the first partial with each prime, by its prime, which
    /// every later partial with the prime is combined with.
    Single(FxHashMap<u32, Relation>),
    /// One or two large primes: the cycle-finding graph.
    Double(PartialRelations),
}

impl PartialStore {
    /// Empty storage, for the double large prime variation if `use_dlp` is set.
    pub fn new(use_dlp: bool) -> PartialStore {
        if use_dlp {
            PartialStore::Double(PartialRelations::new())
        } else {
            PartialStore::Single(FxHashMap::default())
        }
    }

    /// Adds a partial relation, with exactly one large prime for
    /// [`PartialStore::Single`]. Returns the full relation it completes, if any;
    /// otherwise the partial is stored.
    pub fn add(&mut self, mut relation: Relation) -> Option<Relation> {
        match self {
            PartialStore::Single(map) => {
                let prime = relation.large_primes.pivot();
                debug_assert_eq!(relation.large_primes, LargePrimes::one(prime));
                if let Some(first) = map.get(&prime) {
                    relation.combine(first);
                    Some(relation)
                } else {
                    map.insert(prime, relation);
                    None
                }
            }
            PartialStore::Double(graph) => graph.add(relation),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rug::Integer;

    fn relation(factors: &[u32], u: u32, v: u32, large_primes: LargePrimes) -> Relation {
        Relation {
            u: Integer::from(u),
            v: Integer::from(v),
            factors: factors.to_vec(),
            large_primes,
        }
    }

    // Partials with the large primes {11}, {11, 13} and {13} form a cycle; the
    // third completes a full relation combining all three.
    #[test]
    fn partials_on_a_cycle_combine_into_a_full_relation() {
        let mut partials = PartialRelations::new();
        let a = relation(&[0, 2], 3, 5, LargePrimes::one(11));
        let b = relation(&[2, 4], 7, 9, LargePrimes::two(11, 13));
        let c = relation(&[4, 5], 11, 13, LargePrimes::one(13));
        assert!(partials.add(a).is_none());
        assert!(partials.add(b).is_none());
        let full = partials.add(c).unwrap();
        assert_eq!(
            full,
            relation(&[0, 5], 3 * 7 * 11, 5 * 9 * 13, LargePrimes::NONE)
        );
    }

    // With single large primes only, the cycle graph combines exactly like the
    // plain hash map.
    #[test]
    fn single_and_double_large_prime_storage_agree_on_single_primes() {
        let mut single = PartialStore::new(false);
        let mut double = PartialStore::new(true);
        let mut combined = 0;
        for (i, &p) in [11u32, 13, 11, 17, 13, 11, 19].iter().enumerate() {
            let i = i as u32;
            let partial = relation(&[i % 8], 2 * i + 3, 2 * i + 5, LargePrimes::one(p));
            let from_single = single.add(partial.clone());
            let from_double = double.add(partial);
            assert_eq!(from_single, from_double, "partial {i} with large prime {p}");
            combined += from_single.is_some() as usize;
        }
        assert_eq!(combined, 3);
    }
}
