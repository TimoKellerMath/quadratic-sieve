use crate::{number_theory::factor_out_power_of_2, polynomial_generator::Polynomial};
use bit_vec::BitVec;
use rug::{Complete, Integer};

pub struct Relations {
    relations: Vec<BitVec>,
    indices: Vec<BitVec>,
    pivot: Vec<usize>,
    xsys: Vec<(Integer, Integer)>,
}

pub trait RelationOperationData {
    fn new(factorbase_size: usize) -> Self;
    fn add_relation(&mut self, relation: &BitVec, xy: &(Integer, Integer));
    fn gaussian_elimination(&mut self) -> Option<BitVec>;
    fn find_factor(&self, relation: &BitVec, n: &Integer) -> Option<Integer>;
    fn factorbase_size(&self) -> usize;
    fn len(&self) -> usize;
    fn drop_last_relation(&mut self);
}

impl RelationOperationData for Relations {
    fn new(factorbase_size: usize) -> Relations {
        let mut relation_data = Relations {
            relations: Vec::<BitVec>::with_capacity(factorbase_size),
            indices: Vec::<BitVec>::with_capacity(factorbase_size),
            pivot: vec![0_usize; factorbase_size],
            xsys: Vec::<(Integer, Integer)>::with_capacity(factorbase_size),
        };
        for (i, entry) in relation_data.pivot.iter_mut().enumerate() {
            *entry = i;
        }
        relation_data
    }

    #[inline]
    fn add_relation(&mut self, relation: &BitVec, xy: &(Integer, Integer)) {
        self.relations.push(relation.clone());
        let mut new_index = BitVec::from_elem(self.factorbase_size(), false);
        new_index.set(self.relations.len() - 1, true);
        self.indices.push(new_index);
        // progress report every 10% of the factorbase size
        if self
            .relations
            .len()
            .is_multiple_of(self.factorbase_size() / 10)
        {
            print!("({})", self.relations.len() / (self.factorbase_size() / 10));
        }
        self.xsys.push(xy.clone());
    }

    // do Gaussian eliminations in bit vectors relations
    // modify the indices of the (x_i,y_i) accordingly
    fn gaussian_elimination(&mut self) -> Option<BitVec> {
        let last_relation: &mut BitVec = &mut self.relations.last().unwrap().clone();
        // eliminate all 1's in the last relation by adding previous relations
        for (i, row) in self.relations.iter().enumerate() {
            // only eliminate with previous relations
            if i == self.relations.len() - 1 {
                break;
            }
            if last_relation[self.pivot[i]] {
                last_relation.xor(row);
                // change indices accordingly
                let index = self.indices[i].clone();
                if let Some(last_index) = self.indices.last_mut() {
                    last_index.xor(&index);
                }
            }
        }
        // find pivot[k] with last relation has an 1 at k
        for i in self.relations.len() - 1..self.pivot.len() {
            let j = self.pivot[i];
            if last_relation[j] {
                let j_tmp = self.pivot[self.relations.len() - 1];
                self.pivot[self.relations.len() - 1] = j;
                self.pivot[i] = j_tmp;
                if let Some(relation) = self.relations.last_mut() {
                    *relation = last_relation.clone();
                }
                return None;
            }
        }
        // if it does not exist, then we have found a non-trivial linear dependency
        // remove the 0-row in relations
        self.relations.pop();
        // and return the found relation
        Some(self.indices.pop().unwrap())
    }

    // given a bitvector of indices i such that y := prod_i y_i is a square,
    // construct x := prod_i x_i and compute gcd(x +- y, n)
    // and return it if it is != 1, n
    fn find_factor(&self, relation: &BitVec, n: &Integer) -> Option<Integer> {
        // corresponding rows in indices give combination of ys
        let mut x = Integer::from(1);
        let mut y = Integer::from(1);
        let mut v = Integer::from(1);
        for (j, bit) in relation.iter().enumerate() {
            if bit {
                let u = &self.xsys[j].0;
                let v1 = &self.xsys[j].1;
                x *= u;
                x %= n;
                let d = v1.gcd_ref(&v).complete();
                v = v.div_exact(&d) * v1.div_exact_ref(&d).complete();
                y *= d;
                y %= n;
            }
        }
        //    println!("x = {x}, v = {v}");
        debug_assert!(v.is_perfect_square());
        y *= v.sqrt();
        y %= n;
        //assert!((x.clone().square() - y.clone().square()).is_divisible(n));
        let gcd = n.gcd_ref(&(&x + &y).complete()).complete();
        //println!("gcd = {gcd}");
        if gcd != 1 && gcd != *n {
            return Some(gcd);
        }
        //println!("x = {x}, y = {y}");
        debug_assert!((x.clone().square() - y.clone().square()).is_divisible(n));
        None
    }

    #[inline]
    fn factorbase_size(&self) -> usize {
        self.pivot.len()
    }

    #[inline]
    fn len(&self) -> usize {
        self.relations.len()
    }

    #[inline]
    fn drop_last_relation(&mut self) {
        self.xsys.pop();
    }
}

// try to factor y over factorbase
pub fn factor_over_factorbase(
    y: &Integer,
    factorbase: &[i64],
    k: u32,
    large_prime_multiplier: i64,
) -> Option<(BitVec, u32)> {
    if y.is_zero() {
        return None;
    }
    let mut y_ = y.clone();
    // initialized with false
    let mut relation = BitVec::from_elem(factorbase.len(), false);
    for (i, p) in factorbase.iter().enumerate() {
        if i == 0 {
            // -1 in factorbase
            if y_.is_negative() {
                relation.set(i, true);
                y_ = -y_;
            }
            continue;
        }
        if i == 1 {
            // 2 in factorbase
            let exponent;
            (y_, exponent) = factor_out_power_of_2(&y_);
            if exponent % 2 == 1 {
                relation.set(i, true);
            }
            continue;
        }
        let exponent = y_.remove_factor_mut(&Integer::from(*p));
        if exponent % 2 == 1 {
            relation.set(i, true);
        }
        if y_ == 1 {
            return Some((relation, 1));
        }
    }
    // often y is divisible by prime divisors of k. As we are only interested in modulo n, not kn, we can factor out all prime divisors of k
    debug_assert!(y_.clone().gcd_u(k) == 1);
    // is the remaining factor prime? (big prime variation)
    let largest_prime = *factorbase.last().unwrap();
    if y_ < largest_prime * large_prime_multiplier {
        //if y_ < largest_prime * largest_prime { here we have to use y_.to_i64().unwrap()
        //println!("remaining y_ = {y_} (small enough)");
        return Some((relation, y_.to_u32().unwrap()));
    }
    None
}

pub fn sieve_over_factorbase(
    sieve_interval_length: usize,
    factorbase: &[i64],
    roots: &[Option<(i64, i64)>],
    logs: &[u32],
    polynomial: &Polynomial,
    n: &Integer,
) -> (Vec<u32>, u32) {
    let mut logs_for_polynomial = vec![0; 2 * sieve_interval_length];
    // skip small primes and subtract the sum of their logs from target
    const NUM_SKIP_PRIMES: usize = 6;
    debug_assert!(NUM_SKIP_PRIMES >= 1); // we must skip -1
    debug_assert_eq!(factorbase.len(), roots.len());
    debug_assert_eq!(factorbase.len(), logs.len());
    //println!("roots = {:?}", &roots[..5]);
    // sieve for all primes p_i with i >= NUM_SKIP_PRIMES in factor base
    for (i, &p) in factorbase.iter().enumerate() {
        if i < NUM_SKIP_PRIMES {
            // ignore -1 and small primes in factor base
            continue;
        }
        if let Some((root1, root2)) = roots[i] {
            debug_assert!(root1.abs() < p && root2.abs() < p);
            /*if p <= 100 {
                println!("p = {p}, roots = ({root1},{root2}), polynomial = {polynomial:?}");
            }*/
            debug_assert!(
                evaluate_polynomial_at(root1, polynomial, n)
                    .1
                    .is_divisible_u(p as u32)
            );
            debug_assert!(
                evaluate_polynomial_at(root2, polynomial, n)
                    .1
                    .is_divisible_u(p as u32)
            );
            let lower_bound: i64 = -(sieve_interval_length as i64) % p;
            let index1 = if root1 >= lower_bound {
                (root1 - lower_bound) as usize
            } else {
                (p + root1 - lower_bound) as usize
            };
            // sieve with first root
            for value in logs_for_polynomial
                .iter_mut()
                .skip(index1)
                .step_by(p as usize)
            {
                *value += logs[i];
            }
            /*for i in (index1..logs_for_polynomial.len()).step_by(p as usize) {
                let x = -(sieve_interval_length as i64) + (i as i64);
                debug_assert!(evaluate_polynomial_at(x, polynomial, n).1.is_divisible_u(p as u32));
            }*/
            // double roots indicate linear polynomial (mod p) => only divisible once
            if root2 == root1 {
                /*
                // NB: This should fail!
                for i in (index1..logs_for_polynomial.len()).step_by(p as usize) {
                    let x = -(sieve_interval_length as i64) + (i as i64);
                    debug_assert!(evaluate_polynomial_at(x, polynomial, n).1.is_divisible(&Integer::from(p).square_ref().complete()));
                }*/
                continue;
            }
            let index2 = if root2 >= lower_bound {
                (root2 - lower_bound) as usize
            } else {
                (p + root2 - lower_bound) as usize
            };
            // double root => sieve twice!
            // sieve with second root
            for value in logs_for_polynomial
                .iter_mut()
                .skip(index2)
                .step_by(p as usize)
            {
                *value += logs[i];
            }
        }
    }
    (
        logs_for_polynomial,
        logs[..NUM_SKIP_PRIMES].iter().sum::<u32>(),
    )
}

// compute (u,y) with u^2 = v (n)
// y = ((a x + b) + b) * x + c = ax^2 + 2bx + c = Q(x) = ((qx + b)^2 - n)/q
// u = (qx + b) * q^-1 (n)
pub fn evaluate_polynomial_at(x: i64, polynomial: &Polynomial, n: &Integer) -> (Integer, Integer) {
    let mut y = (&polynomial.a * x + &polynomial.b).complete();
    // u = qx + b
    let mut u = y.clone();
    y += &polynomial.b;
    y *= x;
    y += &polynomial.c; // y = ux + c = qx^2 + 2bx + c = qx^2 + 2bx + (b^2-n)/q^2
    // qy = (qx)^2 + 2b(qx) + (b^2-n)/q = (qx+b)^2 - b^2 + qc = u^2 - (b^2 + qc)
    debug_assert_eq!(y.clone() * &polynomial.a, u.clone().square() - n);
    // u = (qx+b)/q = x + b/q (mod n)
    u *= &polynomial.q_inverse;
    u %= n;
    // (u/q)^2 = x^2 + 2bx/q + (b^2/q^2) =!= y = qx^2 + 2bx + c (mod n)
    debug_assert!((u.clone().square() - y.clone()).is_divisible(n));
    (u, y)
}
