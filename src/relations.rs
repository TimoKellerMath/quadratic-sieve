use crate::constants::NUM_SKIP_PRIMES;
use crate::number_theory::{is_prime_u32, is_probable_prime_base2, pollard_rho_u64};
use crate::polynomial_generator::{Polynomial, Roots};
use fixedbitset::FixedBitSet;
use rug::{Assign, Complete, Integer};
use rustc_hash::FxHashMap;
use std::io::{self, Write};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

/// Cumulative sieve-internal phase times across all threads (nanoseconds), only
/// accumulated when SIQS_PROFILE is set: bucket fill + carry-position setup vs the
/// add/drain block loop, and the number of sieve calls. Read by the producer's
/// profile report to break down where the sieve pass spends its time.
pub static SIEVE_SETUP_NANOS: AtomicU64 = AtomicU64::new(0);
pub static SIEVE_LOOP_NANOS: AtomicU64 = AtomicU64::new(0);
pub static SIEVE_CALLS: AtomicU64 = AtomicU64::new(0);

fn sieve_profile_enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("SIQS_PROFILE").is_ok())
}

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
    pub fn is_empty(&self) -> bool {
        self.relations.is_empty()
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

// Compute `x.rem_euclid(p)` (result in [0, p)) using a precomputed Barrett
// reciprocal `recip = floor(2^64 / p)`, replacing the per-prime hardware division
// in the resieve loop with a multiply+shift. `x` is given split into magnitude and
// sign so the same reduction serves the byte- and u64-cofactor passes.
//
// Correctness: for a = |x| < 2^32 and p in [2, 2^32), q = floor(a*recip / 2^64) is
// floor(a/p) or one less, so r = a - q*p lands in [0, 2p) and a single conditional
// subtraction reduces it to a mod p. The Euclidean fixup maps a negative x to p - r.
#[inline]
fn x_mod_p(x_abs: u32, x_neg: bool, p: u32, recip: u64) -> u32 {
    let q = ((x_abs as u128 * recip as u128) >> 64) as u64;
    let mut r = x_abs as u64 - q * p as u64;
    if r >= p as u64 {
        r -= p as u64;
    }
    let r = r as u32;
    if x_neg && r != 0 { p - r } else { r }
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
    roots: &Roots,
    reciprocals: &[u64],
    k: u32,
    large_prime_multiplier: u32,
    use_dlp: bool,
    scratch: &mut Integer,
    relation_scratch: &mut FixedBitSet,
) -> Option<(FixedBitSet, u32, u32)> {
    if y.is_zero() {
        return None;
    }
    // Reuse the caller-owned scratch integer instead of cloning y on every
    // candidate; assign reuses scratch's existing allocation.
    let y_ = scratch;
    y_.assign(y);
    // Reuse the caller-owned bitset (capacity == factorbase.len()) rather than
    // allocating one per candidate: most candidates fail, so this avoids a hot
    // alloc/zero/free; the rare successful relation is cloned out at the return.
    let relation = relation_scratch;
    relation.clear();
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
    for (i, &p) in factorbase.iter().enumerate().take(NUM_SKIP_PRIMES).skip(2) {
        let mut exp = 0u32;
        while y_.is_divisible_u(p) {
            y_.div_exact_u_mut(p);
            exp += 1;
        }
        if exp & 1 == 1 {
            relation.set(i, true);
        }
        if *y_ == 1 {
            return Some((relation.clone(), 1, 1));
        }
    }

    // x is constant across the resieve; reduce it mod each p via the Barrett
    // reciprocals instead of a hardware divide per prime.
    let x_abs = x.unsigned_abs();
    let x_neg = x < 0;
    // indices NUM_SKIP_PRIMES..: sieved primes. p | Q(x) iff x ≡ root1 or root2 (mod p),
    // so skip the big-int divisibility test for primes that don't hit x.
    // Switch to u64 arithmetic once the cofactor fits in 63 bits. Its size only
    // changes when a prime divides it, so check it only then: significant_bits is
    // a GMP call, too slow to make for every prime.
    let mut i = NUM_SKIP_PRIMES;
    let mut fits_u64 = y_.significant_bits() <= 63;
    while !fits_u64 && i < factorbase.len() {
        let p = factorbase[i];
        let divides = match roots.get(i) {
            Some((r1, r2)) => {
                let xmp = x_mod_p(x_abs, x_neg, p, reciprocals[i]);
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
                return Some((relation.clone(), 1, 1));
            }
            fits_u64 = y_.significant_bits() <= 63;
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
    let mut y_u64 = y_.to_u64()?;
    while i < factorbase.len() {
        let p = factorbase[i] as u64;
        if p * p > y_u64 {
            break;
        }
        let divides = match roots.get(i) {
            Some((r1, r2)) => {
                let xmp = x_mod_p(x_abs, x_neg, factorbase[i], reciprocals[i]) as u64;
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
                return Some((relation.clone(), 1, 1));
            }
        }
        i += 1;
    }

    // remainder y_u64 is 1 or prime
    if y_u64 == 1 {
        return Some((relation.clone(), 1, 1));
    }
    // locate prime in factorbase[i..] via binary search
    let largest_prime = *factorbase.last().unwrap() as u64;
    if y_u64 <= largest_prime
        && let Ok(offset) = factorbase[i..].binary_search(&(y_u64 as u32))
    {
        relation.toggle(i + offset);
        return Some((relation.clone(), 1, 1));
    }
    debug_assert!(Integer::from(y_u64).gcd_u(k) == 1);
    // large prime bound: largest_prime * lpm stays below 2^32, so a single large
    // prime always fits in u32.
    let lp_bound = largest_prime * large_prime_multiplier as u64;
    // single large prime variation: y_u64 has no factor <= largest_prime, and
    // lp_bound < largest_prime^2, so a value below lp_bound is necessarily prime.
    if y_u64 < lp_bound {
        return Some((relation.clone(), y_u64 as u32, 1));
    }
    // double large prime variation: y_u64 is a product of large primes (it survived
    // trial division by the whole factor base). Accept it only if it splits into two
    // primes, each below lp_bound, i.e. y_u64 is a semiprime <= lp_bound^2.
    //
    // The common case here is a single prime cofactor > lp_bound (useless): the
    // base-2 test rejects it with one modular exponentiation, where the full
    // primality test would run all its witnesses on a prime (the worst case). A
    // `false` result certifies compositeness, so the Pollard-rho split below is
    // guaranteed to terminate. p and q are <= lp_bound < 2^32, so the cheaper
    // 3-witness is_prime_u32 suffices to confirm them prime.
    if use_dlp && y_u64 <= lp_bound * lp_bound && !is_probable_prime_base2(y_u64) {
        let p = pollard_rho_u64(y_u64);
        let q = y_u64 / p;
        if p <= lp_bound && q <= lp_bound && is_prime_u32(p) && is_prime_u32(q) {
            if p == q {
                // cofactor is a prime square: already a perfect square, so the large
                // prime contributes nothing to the parity vector. This is a full
                // relation (find_factor recovers p via the v product).
                return Some((relation.clone(), 1, 1));
            }
            return Some((relation.clone(), p as u32, q as u32));
        }
    }
    None
}

/// Per-block buckets of large-prime hits for [`sieve_over_factorbase_blocked`], in one
/// flat array: bucket `b` occupies `data[b * stride..ends[b]]`. The stride covers every
/// hit a block can get, so the fill needs no capacity or bounds checks. Owned by the
/// caller so that the allocation is reused across polynomials.
#[derive(Default)]
pub struct Buckets {
    data: Vec<u32>,
    ends: Vec<usize>,
    stride: usize,
}

impl Buckets {
    // empty `num_blocks` buckets with room for `stride` entries each
    fn reset(&mut self, num_blocks: usize, stride: usize) {
        if self.data.len() < num_blocks * stride {
            // a zeroed allocation: pages that are never written are never touched
            self.data = vec![0; num_blocks * stride];
        }
        self.stride = stride;
        self.ends.clear();
        self.ends.extend((0..num_blocks).map(|b| b * stride));
    }

    // the hits that fall into block `b`
    fn block(&self, b: usize) -> &[u32] {
        debug_assert!(
            self.ends[b] <= (b + 1) * self.stride,
            "bucket {b} overflowed"
        );
        &self.data[b * self.stride..self.ends[b]]
    }
}

/// Appends `entry` to bucket `block` of the flat arrays of a [`Buckets`].
///
/// # Safety
///
/// `block` must be below the number of buckets, and the bucket must have room.
#[inline(always)]
unsafe fn push_hit(data: *mut u32, ends: *mut usize, block: usize, entry: u32) {
    // SAFETY: guaranteed by the caller
    unsafe {
        let end = ends.add(block);
        *data.add(*end) = entry;
        *end += 1;
    }
}

/// Blocked (segmented) version of the sieve which reuses `logs_for_polynomial`
/// and processes the sieve window in cache‑friendly blocks of `block_size`.
///
/// Primes are split at `block_size`:
/// - **Small primes** (`p <= block_size`) hit every block one or more times, so they
///   are carry‑sieved per block — the hit position is walked forward and remembered
///   in `next_pos` across blocks.
/// - **Large primes** (`p > block_size`) hit a given block at most once, so iterating
///   them per block (as a plain blocked sieve does) wastes a read/compare/write‑back
///   on every non‑hitting block. Instead each of their (few) hits is *bucketed* into
///   the block it lands in; a block then just drains its bucket. This turns the
///   large‑prime cost from O(num_blocks · num_large_primes) into O(num_large_hits).
///
/// - `sieve_interval_length`: half the window length (total_len = 2 * sieve_interval_length)
/// - `factorbase`, `roots`, `logs`: same layout as existing code; `factorbase` sorted ascending
/// - `logs_for_polynomial`: caller‑owned buffer with length == 2 * sieve_interval_length
/// - `next_pos`: caller‑owned scratch reused across calls (carry positions for small primes)
/// - `buckets`: caller‑owned scratch reused across calls; one bucket per block for the
///   large primes, each entry a packed `position | log << 24` word (total_len < 2^24,
///   which the largest tabulated sieve size satisfies). Halving the entry size keeps
///   the fill's write traffic — the bulk of the sieve setup — cache-resident longer.
///   Allocations are reused; contents are reset each call.
/// - `block_size`: block size in elements, a power of two (positions map to blocks by
///   a shift); one larger than the window gives a single block
///
/// Returns sum of small logs (same as other variants).
#[allow(clippy::too_many_arguments)]
pub fn sieve_over_factorbase_blocked(
    sieve_interval_length: usize,
    factorbase: &[u32],
    roots: &Roots,
    logs: &[u8],
    logs_for_polynomial: &mut [u8],
    next_pos: &mut Vec<usize>,
    buckets: &mut Buckets,
    block_size: usize,
) -> u32 {
    debug_assert_eq!(factorbase.len(), roots.len());
    debug_assert_eq!(factorbase.len(), logs.len());
    let total_len = 2usize * sieve_interval_length;
    debug_assert_eq!(logs_for_polynomial.len(), total_len);
    // reset buffer (reuse instead of reallocating)
    logs_for_polynomial.fill(0);

    assert!(
        block_size.is_power_of_two(),
        "block size {block_size} is not a power of two"
    );
    let block_shift = block_size.trailing_zeros();
    let num_blocks = total_len.div_ceil(block_size);

    // factorbase is sorted ascending, so primes <= block_size form a prefix. Skip the
    // first NUM_SKIP_PRIMES entries (-1 sentinel, 2, and the directly trial‑divided
    // small primes), the same as the per-prime loops below.
    let ns = NUM_SKIP_PRIMES.min(factorbase.len());
    let split = factorbase
        .partition_point(|&p| (p as usize) <= block_size)
        .max(ns);

    let profile = sieve_profile_enabled();
    let prof_t0 = profile.then(std::time::Instant::now);

    // --- bucket the large primes (p > block_size): one entry per hit ---
    // each root of a prime larger than a block hits that block at most once
    buckets.reset(num_blocks, 2 * (factorbase.len() - split));
    let data = buckets.data.as_mut_ptr();
    let ends = buckets.ends.as_mut_ptr();
    // the packed entry holds the position in 24 bits and the log in the top 8
    debug_assert!(total_len < (1 << 24));
    for (((&p, &root1), &root2), &log) in factorbase[split..]
        .iter()
        .zip(&roots.r1[split..])
        .zip(&roots.r2[split..])
        .zip(&logs[split..])
    {
        if root1 == Roots::NONE {
            continue;
        }
        let log_packed = (log as u32) << 24;
        let p_us = p as usize;
        let mut pos = (root1 as usize + sieve_interval_length) % p_us;
        while pos < total_len {
            // SAFETY: pos < total_len, so the block index is below num_blocks, and
            // the stride leaves room for every hit
            unsafe { push_hit(data, ends, pos >> block_shift, pos as u32 | log_packed) };
            pos += p_us;
        }
        if root2 != root1 {
            let mut pos = (root2 as usize + sieve_interval_length) % p_us;
            while pos < total_len {
                // SAFETY: as above
                unsafe { push_hit(data, ends, pos >> block_shift, pos as u32 | log_packed) };
                pos += p_us;
            }
        }
    }

    // --- carry positions for the small primes (p <= block_size) ---
    next_pos.clear();
    for ((&p, &root1), &root2) in factorbase[ns..split]
        .iter()
        .zip(&roots.r1[ns..split])
        .zip(&roots.r2[ns..split])
    {
        if root1 != Roots::NONE {
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

    let prof_t1 = profile.then(std::time::Instant::now);

    // --- process each block: small primes by carry walk, then drain its bucket ---
    let small_primes = &factorbase[ns..split];
    let small_logs = &logs[ns..split];
    let buf_ptr = logs_for_polynomial.as_mut_ptr();
    let next_pos_ptr = next_pos.as_mut_ptr();
    let mut block_start = 0usize;
    let mut block_idx = 0usize;
    while block_start < total_len {
        let block_end = (block_start + block_size).min(total_len);
        let mut idx = 0usize;
        for (&p, &log) in small_primes.iter().zip(small_logs) {
            let p_us = p as usize;
            // SAFETY: next_pos holds two entries per small prime, so idx + 1 is in
            // bounds, and every write stays below block_end <= total_len, the
            // length of the buffer
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
        // drain the large-prime hits that fall in this block
        for &packed in buckets.block(block_idx) {
            // SAFETY: every bucket entry holds a position below total_len
            unsafe {
                let slot = buf_ptr.add((packed & 0x00FF_FFFF) as usize);
                *slot = (*slot).wrapping_add((packed >> 24) as u8);
            }
        }
        block_start = block_end;
        block_idx += 1;
    }

    if let (Some(t0), Some(t1)) = (prof_t0, prof_t1) {
        SIEVE_SETUP_NANOS.fetch_add((t1 - t0).as_nanos() as u64, Ordering::Relaxed);
        SIEVE_LOOP_NANOS.fetch_add(t1.elapsed().as_nanos() as u64, Ordering::Relaxed);
        SIEVE_CALLS.fetch_add(1, Ordering::Relaxed);
    }

    logs[..ns].iter().map(|&l| l as u32).sum::<u32>()
}

// compute (u,y) with u^2 = v (n), writing into the caller-owned `u` and `y` so their
// allocations are reused across candidates instead of allocating a fresh pair per
// survivor (the common case is a non-relation, where the result is just discarded).
// y = ((a x + b) + b) * x + c = ax^2 + 2bx + c = Q(x) = ((qx + b)^2 - n)/q
// u = (qx + b) * q^-1 (n)
pub fn evaluate_polynomial_at(
    x: i32,
    polynomial: &Polynomial,
    n: &Integer,
    u: &mut Integer,
    y: &mut Integer,
) {
    y.assign(polynomial.a * x + &polynomial.b);
    // u = qx + b
    u.assign(&*y);
    *y += &polynomial.b;
    *y *= x;
    *y += &polynomial.c; // y = ux + c = qx^2 + 2bx + c = qx^2 + 2bx + (b^2-n)/q^2
    // qy = (qx)^2 + 2b(qx) + (b^2-n)/q = (qx+b)^2 - b^2 + qc = u^2 - (b^2 + qc)
    debug_assert_eq!(y.clone() * polynomial.a, u.clone().square() - n);
    // u = (qx+b)/q = x + b/q (mod n)
    *u *= polynomial.q_inverse;
    *u %= n;
    // (u/q)^2 = x^2 + 2bx/q + (b^2/q^2) =!= y = qx^2 + 2bx + c (mod n)
    debug_assert!((u.clone().square() - y.clone()).is_divisible(n));
}

#[cfg(test)]
mod tests {
    use super::*;

    // Naive reference sieve: for each non-skipped prime, walk every hit over the
    // whole window. The blocked/bucketed sieve must produce a byte-identical buffer.
    fn reference_sieve(
        sieve_interval_length: usize,
        factorbase: &[u32],
        roots: &Roots,
        logs: &[u8],
    ) -> Vec<u8> {
        let total_len = 2 * sieve_interval_length;
        let mut buf = vec![0u8; total_len];
        for i in NUM_SKIP_PRIMES..factorbase.len() {
            let Some((r1, r2)) = roots.get(i) else {
                continue;
            };
            let p = factorbase[i] as usize;
            let log = logs[i];
            let mut walk = |r: u32| {
                let mut pos = (r as usize + sieve_interval_length) % p;
                while pos < total_len {
                    buf[pos] = buf[pos].wrapping_add(log);
                    pos += p;
                }
            };
            walk(r1);
            if r2 != r1 {
                walk(r2);
            }
        }
        buf
    }

    #[test]
    fn bucketed_sieve_matches_reference() {
        // factorbase: [0 sentinel, 2, then odd primes], sorted ascending, with primes
        // both well below and well above the block sizes tested (forcing both the
        // carry path and the large-prime buckets, across many blocks).
        let mut primes = vec![0u32, 2];
        let mut p = 3u32;
        while primes.len() < 200 {
            if (2..p).all(|d| !p.is_multiple_of(d)) {
                primes.push(p);
            }
            p += 2;
        }
        let factorbase = primes;
        let sieve_interval_length = 500usize; // total_len = 1000
        // deterministic roots; None for the skipped prefix and a couple of others to
        // exercise the skip branches, plus one forced double root.
        let mut roots = Roots::default();
        let mut seed = 0x1234_5678u64;
        for (i, &pr) in factorbase.iter().enumerate() {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            if i < NUM_SKIP_PRIMES || pr < 2 || i % 37 == 0 {
                roots.push(None);
            } else if i % 53 == 0 {
                let r = (seed % pr as u64) as u32;
                roots.push(Some((r, r))); // double root
            } else {
                let r1 = (seed % pr as u64) as u32;
                let r2 = ((seed >> 17) % pr as u64) as u32;
                roots.push(Some((r1, r2)));
            }
        }
        let logs: Vec<u8> = factorbase
            .iter()
            .map(|&pr| ((pr.max(2) as f32).log2().round() as u8).max(1))
            .collect();

        let want = reference_sieve(sieve_interval_length, &factorbase, &roots, &logs);
        let total_len = 2 * sieve_interval_length;
        let mut next_pos = Vec::new();
        let mut buckets = Buckets::default();
        // block sizes that are tiny (many blocks), that don't divide total_len, and
        // that exceed total_len (single block) — every prime above the size goes to
        // the buckets.
        for &block_size in &[8usize, 16, 64, 256, 512, 1024, 4096] {
            let mut buf = vec![0u8; total_len];
            sieve_over_factorbase_blocked(
                sieve_interval_length,
                &factorbase,
                &roots,
                &logs,
                &mut buf,
                &mut next_pos,
                &mut buckets,
                block_size,
            );
            assert_eq!(buf, want, "mismatch at block_size = {block_size}");
        }
    }

    #[test]
    fn x_mod_p_matches_rem_euclid() {
        // a spread of factor-base-sized primes, including the largest that fits in u32
        let primes: [u32; 7] = [5, 97, 65537, 1_000_003, 16_777_213, 100_003, 4_294_967_291];
        // x values: extremes plus a scattering of both signs
        let xs: [i32; 9] = [
            0,
            1,
            -1,
            i32::MAX,
            i32::MIN,
            1_234_567,
            -1_234_567,
            -65_536,
            2_000_000_000,
        ];
        for &p in &primes {
            let recip = ((1u128 << 64) / p as u128) as u64;
            for &x in &xs {
                let got = x_mod_p(x.unsigned_abs(), x < 0, p, recip);
                let want = (x as i64).rem_euclid(p as i64) as u32;
                assert_eq!(got, want, "x_mod_p({x}, {p})");
            }
        }
    }

    // a relation over `len` columns with the given bits set
    fn bits(ones: &[usize], len: usize) -> FixedBitSet {
        let mut relation = FixedBitSet::with_capacity(len);
        for &i in ones {
            relation.insert(i);
        }
        relation
    }

    // an n of about 100 bits, whose polynomials yield every kind of relation
    fn example_n() -> Integer {
        let p = ((Integer::from(1) << 49u32) + 12345u32).next_prime();
        let q = ((Integer::from(1) << 50u32) + 67890u32).next_prime();
        p * q
    }

    // The relation of y over the factor base by trial division with every prime,
    // classified independently of factor_over_factorbase: full, one large prime
    // below the bound, or two large primes below it (split by trial division).
    fn brute_force_relation(
        y: &Integer,
        factorbase: &[u32],
        large_prime_multiplier: u32,
    ) -> Option<(FixedBitSet, u32, u32)> {
        if *y == 0 {
            return None;
        }
        let mut relation = FixedBitSet::with_capacity(factorbase.len());
        relation.set(0, *y < 0);
        let mut m = y.clone().abs();
        for (i, &p) in factorbase.iter().enumerate().skip(1) {
            let mut exponent = 0;
            while m.is_divisible_u(p) {
                m.div_exact_u_mut(p);
                exponent += 1;
            }
            relation.set(i, exponent % 2 == 1);
        }
        if m == 1 {
            return Some((relation, 1, 1));
        }
        // the remaining prime factors all exceed the largest factor-base prime
        let m = m.to_u64()?;
        let largest = *factorbase.last().unwrap() as u64;
        let bound = largest * large_prime_multiplier as u64;
        if m < bound {
            return Some((relation, m as u32, 1));
        }
        let is_prime = |x: u64| Integer::from(x).is_probably_prime(30) != rug::integer::IsPrime::No;
        if m > bound * bound || is_prime(m) {
            return None;
        }
        let mut p = (largest + 1) | 1;
        while m % p != 0 {
            p += 2;
        }
        let q = m / p;
        if q > bound || !is_prime(q) {
            return None;
        }
        Some(if p == q {
            (relation, 1, 1)
        } else {
            (relation, p as u32, q as u32)
        })
    }

    // At every position of the interval, factor_over_factorbase finds the same
    // relation as brute force, and every kind of outcome occurs.
    #[test]
    fn trial_division_matches_brute_force() {
        let n = example_n();
        let factorbase = crate::factorbase::make_factorbase(&n, 300);
        let n_roots = crate::factorbase::square_roots_mod_factorbase(&n, &factorbase);
        let reciprocals = crate::factorbase::compute_reciprocals(&factorbase);
        let mut generators = crate::siqs_generator::new_polynomial_generators(
            &n,
            65536,
            1,
            &factorbase,
            &n_roots,
            &factorbase,
        );
        let (polynomial, roots) = generators[0].next_polynomial();
        let large_prime_multiplier = 40;
        let (mut u, mut y) = (Integer::new(), Integer::new());
        let mut scratch = Integer::new();
        let mut relation_scratch = FixedBitSet::with_capacity(factorbase.len());
        let sorted = |(relation, p, q): (FixedBitSet, u32, u32)| (relation, p.min(q), p.max(q));
        // none, full, one large prime, two large primes
        let mut outcomes = [0usize; 4];
        for x in -65536..65536 {
            evaluate_polynomial_at(x, &polynomial, &n, &mut u, &mut y);
            let got = factor_over_factorbase(
                x,
                &y,
                &factorbase,
                roots,
                &reciprocals,
                1,
                large_prime_multiplier,
                true,
                &mut scratch,
                &mut relation_scratch,
            )
            .map(sorted);
            let want = brute_force_relation(&y, &factorbase, large_prime_multiplier).map(sorted);
            assert_eq!(got, want, "x = {x}");
            outcomes[match want {
                None => 0,
                Some((_, 1, 1)) => 1,
                Some((_, 1, _)) => 2,
                Some(_) => 3,
            }] += 1;
        }
        assert!(
            outcomes.iter().all(|&count| count > 0),
            "outcomes (none, full, 1LP, 2LP): {outcomes:?}"
        );
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
            evaluate_polynomial_at(x, &polynomial, &n, &mut u, &mut y);
            let ax_b = polynomial.a.clone() * x + &polynomial.b;
            assert_eq!(polynomial.a.clone() * &y, ax_b.square() - &n, "x = {x}");
            assert!((u.clone().square() - &y).is_divisible(&n), "x = {x}");
        }
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
