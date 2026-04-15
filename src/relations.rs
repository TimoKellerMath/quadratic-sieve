use crate::{constants::NUM_SKIP_PRIMES, number_theory::factor_out_power_of_2, polynomial_generator::Polynomial};
use fixedbitset::FixedBitSet;
use itertools::izip;
use rug::{Complete, Integer};
use std::io::{self, Write};

pub struct Relations {
    relations: Vec<FixedBitSet>,
    indices: Vec<FixedBitSet>,
    pivot: Vec<usize>,
    xsys: Vec<(Integer, Integer)>,
}

pub trait RelationOperationData {
    fn new(factorbase_size: usize) -> Self;
    fn add_relation(&mut self, relation: FixedBitSet, xy: (Integer, Integer));
    fn gaussian_elimination(&mut self) -> Option<FixedBitSet>;
    fn find_factor(&self, relation: &FixedBitSet, n: &Integer) -> Option<Integer>;
    fn factorbase_size(&self) -> usize;
    fn len(&self) -> usize;
    fn drop_last_relation(&mut self);
}

impl RelationOperationData for Relations {
    fn new(factorbase_size: usize) -> Relations {
        Relations {
            relations: Vec::with_capacity(factorbase_size),
            indices: Vec::with_capacity(factorbase_size),
            pivot: (0..factorbase_size).collect(),
            xsys: Vec::with_capacity(factorbase_size),
        }
    }

    #[inline]
    fn add_relation(&mut self, relation: FixedBitSet, xy: (Integer, Integer)) {
        self.relations.push(relation);
        let mut new_index = FixedBitSet::with_capacity(self.factorbase_size());
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
    fn gaussian_elimination(&mut self) -> Option<FixedBitSet> {
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

    // given a FixedBitSettor of indices i such that y := prod_i y_i is a square,
    // construct x := prod_i x_i and compute gcd(x +- y, n)
    // and return it if it is != 1, n
    fn find_factor(&self, relation: &FixedBitSet, n: &Integer) -> Option<Integer> {
        // corresponding rows in indices give combination of ys
        let mut x = Integer::from(1);
        let mut y = Integer::from(1);
        let mut v = Integer::from(1);
        for j in relation.ones() {
            let u = &self.xsys[j].0;
            let v1 = &self.xsys[j].1;
            x *= u;
            x %= n;
            let d = v1.gcd_ref(&v).complete();
            v = v.div_exact(&d) * v1.div_exact_ref(&d).complete();
            y *= d;
            y %= n;
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

// try to factor y = Q(x) over factorbase, using resieve: only divide by p if x ≡ root (mod p)
pub fn factor_over_factorbase(
    x: i32,
    y: &Integer,
    factorbase: &[u32],
    roots: &[Option<(u32, u32)>],
    k: u32,
    large_prime_multiplier: u32,
) -> Option<(FixedBitSet, u32)> {
    if y.is_zero() {
        return None;
    }
    let mut y_ = y.clone();
    let mut relation = FixedBitSet::with_capacity(factorbase.len());
    // -1 in factorbase
    if y_.is_negative() {
        relation.set(0, true);
        y_ = -y_;
    }
    // 2 in factorbase
    let exponent;
    (y_, exponent) = factor_out_power_of_2(&y_);
    if exponent % 2 == 1 {
        relation.set(1, true);
    }

    // indices 2..NUM_SKIP_PRIMES: sieve skips these, so trial-divide directly
    for i in 2..NUM_SKIP_PRIMES.min(factorbase.len()) {
        let p = factorbase[i];
        let mut exp = 0u32;
        while y_.is_divisible_u(p) {
            y_.div_exact_u_mut(p);
            exp += 1;
        }
        if exp & 1 == 1 {
            relation.set(i, true);
        }
        if y_ == 1 {
            return Some((relation, 1));
        }
    }

    let x64 = x as i64;
    // indices NUM_SKIP_PRIMES..: sieved primes. p | Q(x) iff x ≡ root1 or root2 (mod p),
    // so skip the big-int divisibility test for primes that don't hit x.
    let mut i = NUM_SKIP_PRIMES;
    while i < factorbase.len() {
        if y_.significant_bits() <= 63 {
            break;
        }
        let p = factorbase[i];
        let divides = match roots[i] {
            Some((r1, r2)) => {
                let xmp = x64.rem_euclid(p as i64) as u32;
                xmp == r1 || xmp == r2
            }
            None => y_.is_divisible_u(p), // p | a: resieve info unavailable
        };
        if divides {
            let mut exp = 0u32;
            while y_.is_divisible_u(p) {
                y_.div_exact_u_mut(p);
                exp += 1;
            }
            if exp & 1 == 1 {
                relation.set(i, true);
            }
            if y_ == 1 {
                return Some((relation, 1));
            }
        }
        i += 1;
    }

    // u64 fast path with sqrt early termination
    let mut y_u64 = y_.to_u64().unwrap();
    while i < factorbase.len() {
        let p = factorbase[i] as u64;
        if p * p > y_u64 {
            break;
        }
        let divides = match roots[i] {
            Some((r1, r2)) => {
                let xmp = x64.rem_euclid(p as i64) as u64;
                xmp == r1 as u64 || xmp == r2 as u64
            }
            None => y_u64 % p == 0,
        };
        if divides {
            let mut exp = 0u32;
            while y_u64 % p == 0 {
                y_u64 /= p;
                exp += 1;
            }
            if exp & 1 == 1 {
                relation.set(i, true);
            }
            if y_u64 == 1 {
                return Some((relation, 1));
            }
        }
        i += 1;
    }

    // remainder y_u64 is 1 or prime
    if y_u64 == 1 {
        return Some((relation, 1));
    }
    // locate prime in factorbase[i..] via binary search
    let largest_prime = *factorbase.last().unwrap() as u64;
    if y_u64 <= largest_prime {
        if let Ok(offset) = factorbase[i..].binary_search(&(y_u64 as u32)) {
            relation.toggle(i + offset);
            return Some((relation, 1));
        }
    }
    debug_assert!(Integer::from(y_u64).gcd_u(k) == 1);
    // big prime variation: small enough partial
    if y_u64 < largest_prime * large_prime_multiplier as u64 {
        return Some((relation, y_u64 as u32));
    }
    None
}

pub fn sieve_over_factorbase(
    sieve_interval_length: usize,
    factorbase: &[u32],
    roots: &[Option<(u32, u32)>],
    logs: &[u8],
    logs_for_polynomial: &mut [u8],
    //polynomial: &Polynomial,
    //n: &Integer,
) -> u32 {
    // reset buffer
    logs_for_polynomial.fill(0);

    // skip small primes and subtract the sum of their logs from target
    debug_assert!(NUM_SKIP_PRIMES >= 1); // we must skip -1
    debug_assert_eq!(factorbase.len(), roots.len());
    debug_assert_eq!(factorbase.len(), logs.len());
    //println!("roots = {:?}", &roots[..5]);
    // sieve for all primes p_i with i >= NUM_SKIP_PRIMES in factor base
    let total_len = logs_for_polynomial.len();
    for (&p, &roots, &log) in izip!(factorbase, roots, logs).skip(NUM_SKIP_PRIMES) {
        if let Some((root1, root2)) = roots {
            let p_us = p as usize;
            // smallest i >= 0 with (i - M) ≡ root (mod p), i.e. i ≡ root + M (mod p)
            let index1 = (root1 as usize + sieve_interval_length) % p_us;
            let mut j = index1;
            while j < total_len {
                logs_for_polynomial[j] += log;
                j += p_us;
            }
            // double root => p | a, Q is linear mod p, divisible only once
            if root2 == root1 {
                continue;
            }
            let index2 = (root2 as usize + sieve_interval_length) % p_us;
            let mut j = index2;
            while j < total_len {
                logs_for_polynomial[j] += log;
                j += p_us;
            }
        }
    }
    
    logs[..NUM_SKIP_PRIMES].iter().map(|&l| l as u32).sum::<u32>()
}

/// Blocked (segmented) version of the sieve which reuses `logs_for_polynomial`
/// and processes the sieve window in cache‑friendly blocks of `block_size`.
///
/// - `sieve_interval_length`: half the window length (total_len = 2 * sieve_interval_length)
/// - `factorbase`, `roots`, `logs`: same layout as existing code
/// - `logs_for_polynomial`: caller‑owned buffer with length == 2 * sieve_interval_length
/// - `block_size`: block size in elements (choose e.g. 8k .. 64k)
///
/// Returns sum of small logs (same as other variants).
pub fn sieve_over_factorbase_blocked(
    sieve_interval_length: usize,
    factorbase: &[u32],
    roots: &[Option<(u32, u32)>],
    logs: &[u8],
    logs_for_polynomial: &mut [u8],
    block_size: usize,
) -> u32 {
    debug_assert_eq!(factorbase.len(), roots.len());
    debug_assert_eq!(factorbase.len(), logs.len());
    let total_len = 2usize * sieve_interval_length;
    debug_assert_eq!(logs_for_polynomial.len(), total_len);
    // reset buffer (wiederverwenden statt neu alloziieren)
    logs_for_polynomial.fill(0);

    debug_assert!(NUM_SKIP_PRIMES >= 1);

    // trivial case: if block_size >= total_len, fall back to non‑blocked style (but still reusing buffer)
    let use_blocking = block_size > 0 && block_size < total_len;

    if !use_blocking {
        // simple fallback: do global stepping (similar to original, but reusing buffer)
        for (&p, &roots_opt, &log) in izip!(factorbase, roots, logs).skip(NUM_SKIP_PRIMES) {
            if let Some((root1, root2)) = roots_opt {
                let lower_bound: i32 = -(((sieve_interval_length as i64) % (p as i64)) as i32);
                let index1 = if root1 as i32 >= lower_bound {
                    (root1 as i32 - lower_bound) as usize
                } else {
                    (p as i32 + root1 as i32 - lower_bound) as usize
                };
                let step = p as usize;
                let mut i = index1;
                while i < total_len {
                    logs_for_polynomial[i] += log;
                    i += step;
                }
                if root2 != root1 {
                    let index2 = if root2 as i32 >= lower_bound {
                        (root2 as i32 - lower_bound) as usize
                    } else {
                        (p as i32 + root2 as i32 - lower_bound) as usize
                    };
                    let mut i = index2;
                    while i < total_len {
                        logs_for_polynomial[i] += log;
                        i += step;
                    }
                }
            }
        }
    } else {
        // blocked processing
        let mut block_start = 0usize;
        while block_start < total_len {
            let block_end = (block_start + block_size).min(total_len);
            for (&p, &roots_opt, &log) in izip!(factorbase, roots, logs).skip(NUM_SKIP_PRIMES) {
                if let Some((root1, root2)) = roots_opt {
                    let lower_bound: i32 = -(((sieve_interval_length as i64) % (p as i64)) as i32);
                    let index1 = if root1 as i32 >= lower_bound {
                        (root1 as i32 - lower_bound) as usize
                    } else {
                        (p as i32 + root1 as i32 - lower_bound) as usize
                    };
                    let p_usize = p as usize;

                    // compute smallest i >= block_start with i ≡ index1 (mod p)
                    let diff = index1 as isize - block_start as isize;
                    let offset = (((diff % p as isize) + p as isize) % p as isize) as usize;
                    let mut i = block_start + offset;
                    while i < block_end {
                        logs_for_polynomial[i] += log;
                        i += p_usize;
                    }

                    if root2 != root1 {
                        let index2 = if root2 as i32 >= lower_bound {
                            (root2 as i32 - lower_bound) as usize
                        } else {
                            (p as i32 + root2 as i32 - lower_bound) as usize
                        };
                        let diff2 = index2 as isize - block_start as isize;
                        let offset2 = (((diff2 % p as isize) + p as isize) % p as isize) as usize;
                        let mut i2 = block_start + offset2;
                        while i2 < block_end {
                            logs_for_polynomial[i2] += log;
                            i2 += p_usize;
                        }
                    }
                }
            }
            block_start = block_end;
        }
    }

    logs[..NUM_SKIP_PRIMES].iter().map(|&l| l as u32).sum::<u32>()
}

// compute (u,y) with u^2 = v (n)
// y = ((a x + b) + b) * x + c = ax^2 + 2bx + c = Q(x) = ((qx + b)^2 - n)/q
// u = (qx + b) * q^-1 (n)
pub fn evaluate_polynomial_at(x: i32, polynomial: &Polynomial, n: &Integer) -> (Integer, Integer) {
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
