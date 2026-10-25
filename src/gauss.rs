use crate::square_root::find_factor;
use fixedbitset::FixedBitSet;
use rug::Integer;
use std::io::{self, Write};

pub struct Relations {
    relations: Vec<FixedBitSet>,
    indices: Vec<FixedBitSet>,
    pivot: Vec<usize>,
    xsys: Vec<(Integer, Integer)>,
}

impl Relations {
    pub fn new(factorbase_size: usize) -> Relations {
        Relations {
            relations: Vec::with_capacity(factorbase_size),
            indices: Vec::with_capacity(factorbase_size),
            pivot: (0..factorbase_size).collect(),
            xsys: Vec::with_capacity(factorbase_size),
        }
    }

    #[inline]
    pub fn add_relation(&mut self, relation: FixedBitSet, xy: (Integer, Integer)) {
        self.relations.push(relation);
        // relations.len() transiently reaches factorbase_size + 1: the rank can
        // grow up to factorbase_size, and the next relation is pushed (setting bit
        // index factorbase_size here) before gaussian_elimination pops the
        // guaranteed-dependent row. All index bitsets must share this capacity so
        // the ^= in gaussian_elimination stays in bounds.
        let mut new_index = FixedBitSet::with_capacity(self.factorbase_size() + 1);
        new_index.set(self.relations.len() - 1, true);
        self.indices.push(new_index);
        // progress report every 10% of the factorbase size
        let step = (self.factorbase_size() / 10).max(1);
        if self.relations.len().is_multiple_of(step) {
            print!("({})", self.relations.len() / step);
            io::stdout().flush().unwrap();
        }
        self.xsys.push(xy);
    }

    // do Gaussian eliminations in bit vectors relations
    // modify the indices of the (x_i,y_i) accordingly
    pub fn gaussian_elimination(&mut self) -> Option<FixedBitSet> {
        assert!(!self.relations.is_empty()); // helps the compiler elide bounds checks
        let last_idx = self.relations.len() - 1;
        // eliminate in place: borrow last row mutably and earlier rows immutably
        {
            let (earlier_rels, last_rel_slice) = self.relations.split_at_mut(last_idx);
            let last_rel = &mut last_rel_slice[0];
            let (earlier_idxs, last_idx_slice) = self.indices.split_at_mut(last_idx);
            let last_index = &mut last_idx_slice[0];
            for i in 0..last_idx {
                if last_rel[self.pivot[i]] {
                    *last_rel ^= &earlier_rels[i];
                    *last_index ^= &earlier_idxs[i];
                }
            }
        }
        // find pivot[k] with last relation == 1 at k
        let last_rel = &self.relations[last_idx];
        for i in last_idx..self.pivot.len() {
            if last_rel[self.pivot[i]] {
                self.pivot.swap(last_idx, i);
                return None;
            }
        }
        // non-trivial dependency: drop the 0-row and return its index set
        self.relations.pop();
        Some(self.indices.pop().unwrap())
    }

    // Given the indices of relations whose v's multiply to a square, compute
    // gcd(x + y, n) for x = prod u and y = sqrt(prod v), if it is a proper factor.
    pub fn find_factor(&self, relation: &FixedBitSet, n: &Integer) -> Option<Integer> {
        find_factor(relation.ones().map(|j| &self.xsys[j]), n)
    }

    #[inline]
    pub fn factorbase_size(&self) -> usize {
        self.pivot.len()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.relations.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.relations.is_empty()
    }

    #[inline]
    pub fn drop_last_relation(&mut self) {
        self.xsys.pop();
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

    // 90^2 - 8051 = 7^2: one relation with a square v and an empty parity vector
    // is a dependency on its own, and gives 8051 = 83 · 97.
    #[test]
    fn gaussian_elimination_and_find_factor_on_a_tiny_example() {
        let n = Integer::from(8051);
        let mut relations = Relations::new(4);
        relations.add_relation(bits(&[], 4), (Integer::from(90), Integer::from(49)));
        let dependency = relations.gaussian_elimination().expect("a zero row");
        assert_eq!(dependency.ones().collect::<Vec<_>>(), vec![0]);
        let factor = relations.find_factor(&dependency, &n).expect("a factor");
        assert!(factor == 83 || factor == 97, "factor {factor}");
    }

    // Over 3 columns, the 4th relation is always dependent; its index 3 used to
    // overflow the index bitsets (3d42e99).
    #[test]
    fn gaussian_elimination_at_full_rank() {
        let rows = [
            bits(&[0], 3),
            bits(&[1], 3),
            bits(&[2], 3),
            bits(&[0, 1], 3),
        ];
        let mut relations = Relations::new(3);
        for (i, row) in rows.iter().enumerate() {
            relations.add_relation(row.clone(), (Integer::from(1), Integer::from(1)));
            let dependency = relations.gaussian_elimination();
            if i < 3 {
                assert!(dependency.is_none(), "row {i} is independent");
            } else {
                let dependency = dependency.expect("4 rows over 3 columns are dependent");
                assert_eq!(dependency.ones().collect::<Vec<_>>(), vec![0, 1, 3]);
            }
        }
    }
}
