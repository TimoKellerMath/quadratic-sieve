use crate::relation::{LargePrimes, Relation};
use rustc_hash::FxHashMap;

/// Combines partial relations (those left with one or two large primes after trial
/// division) into full relations.
///
/// Each partial is an edge in a graph whose vertices are the large primes and 1,
/// which stands for no prime: a partial with the large primes p and q joins p and
/// q, one with the single large prime p joins 1 and p. The partials kept form a
/// spanning forest of the graph. A new partial whose two vertices are already
/// connected closes a cycle with the path between them, and the product of the
/// partials around the cycle is a full relation, in which every large prime occurs
/// twice. A new partial that joins two trees is kept as an edge of the forest: the
/// smaller tree is re-rooted at its vertex and hung from the other vertex, which
/// keeps the trees shallow and the cycles short.
///
/// The number of full relations is the number of independent cycles, edges minus
/// vertices plus trees, as for any cycle basis. Short cycles keep the full relations
/// small: their v are products of the partials' v, which the square root at the end
/// has to multiply.
#[derive(Default)]
pub struct PartialRelations {
    // the partials kept, the edges of the forest
    edges: Vec<Relation>,
    // the parent of each vertex that is not a root, and the edge to it
    parents: FxHashMap<u32, (u32, u32)>,
    // the number of vertices of each tree with more than one, by its root
    sizes: FxHashMap<u32, u32>,
}

impl PartialRelations {
    /// An empty graph.
    pub fn new() -> PartialRelations {
        PartialRelations::default()
    }

    /// Adds a partial relation. Returns the full relation it completes, if any;
    /// otherwise the partial is stored.
    pub fn add(&mut self, mut relation: Relation) -> Option<Relation> {
        let (p, q) = relation.large_primes.pair();
        debug_assert!(q != 1, "not a partial relation");
        let (root_p, root_q) = (self.root(p), self.root(q));
        if root_p == root_q {
            // a cycle: multiply in the edges on the paths from p and q up to their
            // lowest common ancestor
            for edge in self.path(p, q) {
                relation.combine(&self.edges[edge as usize]);
            }
            debug_assert!(relation.is_full(), "the cycle leaves large primes");
            return Some(relation);
        }
        // join the trees: re-root the smaller one at its vertex and hang it from the
        // other vertex
        let size = |root| self.sizes.get(&root).copied().unwrap_or(1);
        let (size_p, size_q) = (size(root_p), size(root_q));
        let (child, parent, child_root, parent_root) = if size_p <= size_q {
            (p, q, root_p, root_q)
        } else {
            (q, p, root_q, root_p)
        };
        self.reroot(child);
        let edge = self.edges.len() as u32;
        self.edges.push(relation);
        self.parents.insert(child, (parent, edge));
        self.sizes.remove(&child_root);
        self.sizes.insert(parent_root, size_p + size_q);
        None
    }

    // the root of the tree of vertex `v`
    fn root(&self, mut v: u32) -> u32 {
        while let Some(&(parent, _)) = self.parents.get(&v) {
            v = parent;
        }
        v
    }

    // the edges on the path between the vertices `p` and `q` of one tree
    fn path(&self, p: u32, q: u32) -> Vec<u32> {
        // the ancestors of p, with the edges up to them
        let mut ancestors = FxHashMap::default();
        let (mut v, mut edges_p) = (p, Vec::new());
        ancestors.insert(p, 0);
        while let Some(&(parent, edge)) = self.parents.get(&v) {
            edges_p.push(edge);
            v = parent;
            ancestors.insert(v, edges_p.len());
        }
        // up from q to the first ancestor of p, the lowest common one
        let (mut v, mut edges) = (q, Vec::new());
        while !ancestors.contains_key(&v) {
            let &(parent, edge) = self.parents.get(&v).expect("p and q share a tree");
            edges.push(edge);
            v = parent;
        }
        edges.extend_from_slice(&edges_p[..ancestors[&v]]);
        edges
    }

    // makes vertex `v` the root of its tree, by reversing the path to the old root
    fn reroot(&mut self, v: u32) {
        let (mut vertex, mut new_parent) = (v, None);
        loop {
            let old_parent = self.parents.remove(&vertex);
            if let Some(new_parent) = new_parent {
                self.parents.insert(vertex, new_parent);
            }
            let Some((parent, edge)) = old_parent else {
                break;
            };
            new_parent = Some((vertex, edge));
            vertex = parent;
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

    // On a random graph, every full relation is a product of partials whose large
    // primes cancel, there are as many as independent cycles (edges minus vertices
    // plus trees), and the cycles stay short.
    #[test]
    fn random_partials_give_one_full_relation_per_independent_cycle() {
        let mut seed = 0x9E37_79B9_7F4A_7C15u64;
        let mut random = |bound: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % bound
        };
        // the large primes stand in as 3, 5, ..., and v records the partials of a
        // relation as a product of distinct primes, which must be squarefree in a
        // simple cycle
        let primes: Vec<u32> = (0..400).map(|i| 3 + 2 * i).collect();
        let mut partials = PartialRelations::new();
        let mut vertices = std::collections::HashSet::from([1u32]);
        let mut fulls = 0;
        let mut longest = 0;
        let edges = 1500;
        for i in 0..edges {
            let p = primes[random(primes.len() as u64) as usize];
            let q = primes[random(primes.len() as u64) as usize];
            let large_primes = match random(3) {
                0 => LargePrimes::one(p),
                _ if p != q => LargePrimes::two(p, q),
                _ => LargePrimes::one(q),
            };
            vertices.insert(p);
            vertices.insert(q);
            // u is the index of the partial, plus one
            let partial = relation(&[i % 7], i + 1, 1, large_primes);
            if let Some(full) = partials.add(partial) {
                assert!(full.is_full());
                fulls += 1;
                longest = longest.max(full.u.significant_bits());
            }
        }
        // count the trees with an independent union-find
        let mut parent: std::collections::HashMap<u32, u32> =
            vertices.iter().map(|&v| (v, v)).collect();
        fn find(parent: &mut std::collections::HashMap<u32, u32>, v: u32) -> u32 {
            let p = parent[&v];
            if p == v {
                return v;
            }
            let root = find(parent, p);
            parent.insert(v, root);
            root
        }
        let mut trees = vertices.len();
        for edge in &partials.edges {
            let (p, q) = edge.large_primes.pair();
            let (rp, rq) = (find(&mut parent, p), find(&mut parent, q));
            assert_ne!(rp, rq, "the kept partials contain a cycle");
            parent.insert(rp, rq);
            trees -= 1;
        }
        // only the vertices that some edge touches count; all of them do here
        assert_eq!(fulls, edges as usize - (vertices.len() - trees));
        // a product of a few partial indices below 1500: a cycle of at most about
        // 20 edges
        assert!(
            longest < 20 * 11,
            "longest cycle has a product of {longest} bits"
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
