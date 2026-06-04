use crate::number_theory::{is_prime_u64, pollard_rho_u64};
use crate::{constants::NUM_SKIP_PRIMES, polynomial_generator::Polynomial};
use fixedbitset::FixedBitSet;
use itertools::izip;
use rug::{Assign, Complete, Integer};
use rustc_hash::FxHashMap;
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

    // given a FixedBitSettor of indices i such that y := prod_i y_i is a square,
    // construct x := prod_i x_i and compute gcd(x +- y, n)
    // and return it if it is != 1, n
    pub fn find_factor(&self, relation: &FixedBitSet, n: &Integer) -> Option<Integer> {
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
    pub fn factorbase_size(&self) -> usize {
        self.pivot.len()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.relations.len()
    }

    #[inline]
    pub fn drop_last_relation(&mut self) {
        self.xsys.pop();
    }
}

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
pub struct PartialRelations {
    reps: FxHashMap<u32, (FixedBitSet, Integer, Integer, LargePrimes)>,
}

impl PartialRelations {
    pub fn new() -> PartialRelations {
        PartialRelations {
            reps: FxHashMap::default(),
        }
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

// try to factor y = Q(x) over factorbase, using resieve: only divide by p if x ≡ root (mod p).
// On success returns the relation together with up to two large primes (1 = none):
//   (relation, 1, 1)  full relation
//   (relation, p, 1)  single-large-prime partial
//   (relation, p, q)  double-large-prime partial (only produced when use_dlp is set)
pub fn factor_over_factorbase(
    x: i32,
    y: &Integer,
    factorbase: &[u32],
    roots: &[Option<(u32, u32)>],
    k: u32,
    large_prime_multiplier: u32,
    use_dlp: bool,
    scratch: &mut Integer,
) -> Option<(FixedBitSet, u32, u32)> {
    if y.is_zero() {
        return None;
    }
    // Reuse the caller-owned scratch integer instead of cloning y on every
    // candidate; assign reuses scratch's existing allocation.
    let y_ = scratch;
    y_.assign(y);
    let mut relation = FixedBitSet::with_capacity(factorbase.len());
    // -1 in factorbase
    if y_.is_negative() {
        relation.set(0, true);
        y_.abs_mut();
    }
    // 2 in factorbase: divide out 2^exponent in place (y_ != 0 checked above)
    let exponent = y_.find_one(0).unwrap();
    *y_ >>= exponent;
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
        if *y_ == 1 {
            return Some((relation, 1, 1));
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
            if *y_ == 1 {
                return Some((relation, 1, 1));
            }
        }
        i += 1;
    }

    // u64 fast path with sqrt early termination.
    // If the cofactor still exceeds 64 bits after trial-dividing the whole factor
    // base, its remaining prime factors are all larger than the largest factor-base
    // prime; it cannot be a (single) large prime below largest_prime * lpm (which
    // is far below 2^64), so this candidate yields no usable relation. This is the
    // common case for larger N, where Q(x) is big enough that non-smooth cofactors
    // stay above 64 bits.
    let Some(mut y_u64) = y_.to_u64() else {
        return None;
    };
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
                return Some((relation, 1, 1));
            }
        }
        i += 1;
    }

    // remainder y_u64 is 1 or prime
    if y_u64 == 1 {
        return Some((relation, 1, 1));
    }
    // locate prime in factorbase[i..] via binary search
    let largest_prime = *factorbase.last().unwrap() as u64;
    if y_u64 <= largest_prime {
        if let Ok(offset) = factorbase[i..].binary_search(&(y_u64 as u32)) {
            relation.toggle(i + offset);
            return Some((relation, 1, 1));
        }
    }
    debug_assert!(Integer::from(y_u64).gcd_u(k) == 1);
    // large prime bound: largest_prime * lpm stays below 2^32, so a single large
    // prime always fits in u32.
    let lp_bound = largest_prime * large_prime_multiplier as u64;
    // single large prime variation: y_u64 has no factor <= largest_prime, and
    // lp_bound < largest_prime^2, so a value below lp_bound is necessarily prime.
    if y_u64 < lp_bound {
        return Some((relation, y_u64 as u32, 1));
    }
    // double large prime variation: y_u64 is a product of large primes (it survived
    // trial division by the whole factor base). Accept it only if it splits into two
    // primes, each below lp_bound, i.e. y_u64 is a semiprime <= lp_bound^2.
    if use_dlp && y_u64 <= lp_bound * lp_bound && !is_prime_u64(y_u64) {
        let p = pollard_rho_u64(y_u64);
        let q = y_u64 / p;
        if p <= lp_bound && q <= lp_bound && is_prime_u64(p) && is_prime_u64(q) {
            if p == q {
                // cofactor is a prime square: already a perfect square, so the large
                // prime contributes nothing to the parity vector. This is a full
                // relation (find_factor recovers p via the v product).
                return Some((relation, 1, 1));
            }
            return Some((relation, p as u32, q as u32));
        }
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
/// - `next_pos`: caller‑owned scratch reused across calls (its contents are
///   overwritten each call); avoids reallocating ~2*factorbase.len() usizes per
///   polynomial. Only used on the blocked path.
/// - `block_size`: block size in elements (choose e.g. 8k .. 64k)
///
/// Returns sum of small logs (same as other variants).
pub fn sieve_over_factorbase_blocked(
    sieve_interval_length: usize,
    factorbase: &[u32],
    roots: &[Option<(u32, u32)>],
    logs: &[u8],
    logs_for_polynomial: &mut [u8],
    next_pos: &mut Vec<usize>,
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
        // fallback: single pass over the whole buffer, reusing buffer
        let buf_ptr = logs_for_polynomial.as_mut_ptr();
        for (&p, &roots_opt, &log) in izip!(factorbase, roots, logs).skip(NUM_SKIP_PRIMES) {
            if let Some((root1, root2)) = roots_opt {
                let p_us = p as usize;
                let index1 = (root1 as usize + sieve_interval_length) % p_us;
                let mut j = index1;
                while j < total_len {
                    unsafe { *buf_ptr.add(j) = (*buf_ptr.add(j)).wrapping_add(log); }
                    j += p_us;
                }
                if root2 == root1 {
                    continue;
                }
                let index2 = (root2 as usize + sieve_interval_length) % p_us;
                let mut j = index2;
                while j < total_len {
                    unsafe { *buf_ptr.add(j) = (*buf_ptr.add(j)).wrapping_add(log); }
                    j += p_us;
                }
            }
        }
    } else {
        // blocked processing: carry the next hit position across blocks per prime.
        // next_pos is caller-owned scratch; clear and refill it (reusing its
        // allocation) rather than allocating a fresh Vec every polynomial.
        next_pos.clear();
        for (&p, &roots_opt) in izip!(factorbase, roots).skip(NUM_SKIP_PRIMES) {
            if let Some((root1, root2)) = roots_opt {
                let p_us = p as usize;
                next_pos.push((root1 as usize + sieve_interval_length) % p_us);
                if root2 == root1 {
                    next_pos.push(usize::MAX); // marker: skip
                } else {
                    next_pos.push((root2 as usize + sieve_interval_length) % p_us);
                }
            } else {
                next_pos.push(usize::MAX);
                next_pos.push(usize::MAX);
            }
        }

        let buf_ptr = logs_for_polynomial.as_mut_ptr();
        let next_pos_ptr = next_pos.as_mut_ptr();
        let mut block_start = 0usize;
        while block_start < total_len {
            let block_end = (block_start + block_size).min(total_len);
            let mut idx = 0usize;
            for (&p, &log) in izip!(factorbase, logs).skip(NUM_SKIP_PRIMES) {
                let p_us = p as usize;
                unsafe {
                    let pos1 = *next_pos_ptr.add(idx);
                    if pos1 != usize::MAX {
                        let mut j = pos1;
                        while j < block_end {
                            *buf_ptr.add(j) = (*buf_ptr.add(j)).wrapping_add(log);
                            j += p_us;
                        }
                        *next_pos_ptr.add(idx) = j;
                    }
                    let pos2 = *next_pos_ptr.add(idx + 1);
                    if pos2 != usize::MAX {
                        let mut j = pos2;
                        while j < block_end {
                            *buf_ptr.add(j) = (*buf_ptr.add(j)).wrapping_add(log);
                            j += p_us;
                        }
                        *next_pos_ptr.add(idx + 1) = j;
                    }
                }
                idx += 2;
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
    let mut y = (polynomial.a * x + &polynomial.b).complete();
    // u = qx + b
    let mut u = y.clone();
    y += &polynomial.b;
    y *= x;
    y += &polynomial.c; // y = ux + c = qx^2 + 2bx + c = qx^2 + 2bx + (b^2-n)/q^2
    // qy = (qx)^2 + 2b(qx) + (b^2-n)/q = (qx+b)^2 - b^2 + qc = u^2 - (b^2 + qc)
    debug_assert_eq!(y.clone() * polynomial.a, u.clone().square() - n);
    // u = (qx+b)/q = x + b/q (mod n)
    u *= polynomial.q_inverse;
    u %= n;
    // (u/q)^2 = x^2 + 2bx/q + (b^2/q^2) =!= y = qx^2 + 2bx + c (mod n)
    debug_assert!((u.clone().square() - y.clone()).is_divisible(n));
    (u, y)
}
