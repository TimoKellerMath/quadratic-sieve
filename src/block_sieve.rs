use crate::constants::NUM_SKIP_PRIMES;
use crate::machine::L1D;
use crate::polynomial_generator::Roots;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

/// Nanoseconds that [`sieve_over_factorbase_blocked`] spent filling the buckets and
/// setting up the carry positions, summed over all threads. Like the next two
/// counters, it is only accumulated if `SIQS_PROFILE` is set, for the profile report
/// of the sieving threads.
pub(crate) static SIEVE_SETUP_NANOS: AtomicU64 = AtomicU64::new(0);
/// Nanoseconds that [`sieve_over_factorbase_blocked`] spent in its block loop,
/// without the calls of its `on_block`.
pub(crate) static SIEVE_LOOP_NANOS: AtomicU64 = AtomicU64::new(0);
/// The number of calls of [`sieve_over_factorbase_blocked`].
pub(crate) static SIEVE_CALLS: AtomicU64 = AtomicU64::new(0);

/// Whether `SIQS_PROFILE` is set.
fn sieve_profile_enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("SIQS_PROFILE").is_ok())
}

/// The scratch of [`sieve_over_factorbase_blocked`]: the carry positions of the small
/// primes, the buckets of the large primes and the sums of the current block. Owned
/// by the caller so that the allocations are reused across polynomials.
#[derive(Default)]
pub struct SieveScratch {
    next_pos: Vec<usize>,
    buckets: Buckets,
    block: Vec<u8>,
}

/// The sum of the logs of the factor-base entries that
/// [`sieve_over_factorbase_blocked`] skips (see [`NUM_SKIP_PRIMES`]), which the
/// sieve threshold has to account for.
pub fn skipped_logs(logs: &[u8]) -> u32 {
    logs[..NUM_SKIP_PRIMES.min(logs.len())]
        .iter()
        .map(|&log| log as u32)
        .sum()
}

/// Per-block buckets of large-prime hits for [`sieve_over_factorbase_blocked`], in one
/// flat array: bucket `b` occupies `data[b * stride..ends[b]]`. The stride covers every
/// hit a block can get, so the fill needs no capacity or bounds checks.
#[derive(Default)]
struct Buckets {
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

/// How [`sieve_over_factorbase_blocked`] divides the interval: into blocks of `size`
/// positions, and these into sub-blocks of `sub_size` positions, through which the
/// primes up to `sub_bound` are walked one sub-block at a time, so that their many
/// hits stay in the L1.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Blocking {
    /// The size of a block, a power of two.
    pub size: usize,
    /// The size of a sub-block, at least 1.
    pub sub_size: usize,
    /// The largest prime walked through the sub-blocks.
    pub sub_bound: u32,
}

impl Blocking {
    /// Blocks of `size` positions, with sub-blocks of the size of the L1d,
    /// [`L1D`], for the primes up to an eighth of it, which hit a sub-block at
    /// least 8 times per root. Both were the fastest at 301 bits: the sieve took
    /// 5-7% less time than without sub-blocks, while 16 or 64 KiB, or the primes up
    /// to 16384, gained less.
    pub fn with_size(size: usize) -> Blocking {
        Blocking {
            size,
            sub_size: L1D,
            sub_bound: (L1D / 8) as u32,
        }
    }
}

/// Adds `logs[k]` at every position below `end` of the buffer `buf` that the k-th
/// of `primes` hits, from its two carry positions `next_pos[2 k]` and
/// `next_pos[2 k + 1]` on (`usize::MAX` for none), and leaves them at the next
/// hits, minus `rebase`. Both roots of a prime are walked in one loop, which halves
/// the loop steps.
///
/// # Safety
///
/// `next_pos` holds two entries per prime, the first of which is `usize::MAX` only
/// if both are, and `buf` has room for `end` bytes.
#[inline(always)]
unsafe fn carry_walk(
    primes: &[u32],
    logs: &[u8],
    next_pos: *mut usize,
    buf: *mut u8,
    end: usize,
    rebase: usize,
) {
    for (k, (&p, &log)) in primes.iter().zip(logs).enumerate() {
        let p = p as usize;
        // SAFETY: guaranteed by the caller
        unsafe {
            let (j1, j2) = (*next_pos.add(2 * k), *next_pos.add(2 * k + 1));
            if j1 == usize::MAX {
                continue;
            }
            if j2 == usize::MAX {
                // a single root
                let mut j = j1;
                while j < end {
                    *buf.add(j) = (*buf.add(j)).wrapping_add(log);
                    j += p;
                }
                *next_pos.add(2 * k) = j - rebase;
                continue;
            }
            // both roots while the larger one is inside, then the smaller one; their
            // order in next_pos does not matter
            let (mut lo, mut hi) = (j1.min(j2), j1.max(j2));
            while hi < end {
                *buf.add(lo) = (*buf.add(lo)).wrapping_add(log);
                *buf.add(hi) = (*buf.add(hi)).wrapping_add(log);
                lo += p;
                hi += p;
            }
            while lo < end {
                *buf.add(lo) = (*buf.add(lo)).wrapping_add(log);
                lo += p;
            }
            *next_pos.add(2 * k) = lo - rebase;
            *next_pos.add(2 * k + 1) = hi - rebase;
        }
    }
}

/// Sieves one polynomial over the interval [−M, M), M = `sieve_interval_length`:
/// position i of the interval stands for x = i − M and receives the sum of `logs[j]`
/// over the roots of the polynomial modulo `factorbase[j]`, given as offsets r into
/// the interval (see [`Roots`]), with i ≡ r, for every j from [`NUM_SKIP_PRIMES`] on.
///
/// The interval is sieved in blocks of `blocking.size` positions, a power of two, so
/// that a block stays in the cache; a size of at least 2M gives one block. Each
/// block is cleared just before it is sieved, and passed to `on_block` with its
/// first position as soon as it is complete, so that the sums of only one block are
/// held. A prime up to the block size hits every block, so it is walked through each
/// block from where the previous block left off, the smallest ones (see
/// [`Blocking`]) through each sub-block. A larger prime hits a block at most once
/// per root, so its hits are sorted into one bucket per block first, which the block
/// then drains: this costs a step per hit instead of one per prime and block.
///
/// `factorbase` is sorted ascending, and `roots` and `logs` belong to its primes.
/// 2M < 2^24, and `scratch` is reused across calls.
pub fn sieve_over_factorbase_blocked(
    sieve_interval_length: usize,
    factorbase: &[u32],
    roots: &Roots,
    logs: &[u8],
    scratch: &mut SieveScratch,
    blocking: Blocking,
    mut on_block: impl FnMut(usize, &[u8]),
) {
    let block_size = blocking.size;
    let SieveScratch {
        next_pos,
        buckets,
        block,
    } = scratch;
    debug_assert_eq!(factorbase.len(), roots.len());
    debug_assert_eq!(factorbase.len(), logs.len());
    let total_len = 2usize * sieve_interval_length;

    assert!(
        block_size.is_power_of_two(),
        "block size {block_size} is not a power of two"
    );
    assert!(blocking.sub_size > 0, "empty sub-blocks");
    let block_shift = block_size.trailing_zeros();
    let num_blocks = total_len.div_ceil(block_size);

    // factorbase is sorted ascending, so the primes up to block_size form a prefix,
    // [ns, split) after the skipped primes
    let ns = NUM_SKIP_PRIMES.min(factorbase.len());
    let split = factorbase
        .partition_point(|&p| (p as usize) <= block_size)
        .max(ns);

    let profile = sieve_profile_enabled();
    let prof_t0 = profile.then(std::time::Instant::now);

    // --- bucket the hits of the large primes (p > block_size) ---
    // each root of a prime larger than a block hits that block at most once
    buckets.reset(num_blocks, 2 * (factorbase.len() - split));
    let data = buckets.data.as_mut_ptr();
    let ends = buckets.ends.as_mut_ptr();
    // An entry packs the position into its low 24 bits and the log into the high 8:
    // 4 bytes instead of 8 for a separate position and log keep the fill's writes,
    // the bulk of the setup, in the cache longer.
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
        let mut pos = root1 as usize;
        while pos < total_len {
            // SAFETY: pos < total_len, so the block index is below num_blocks, and
            // the stride leaves room for every hit
            unsafe { push_hit(data, ends, pos >> block_shift, pos as u32 | log_packed) };
            pos += p_us;
        }
        if root2 != root1 {
            let mut pos = root2 as usize;
            while pos < total_len {
                // SAFETY: as above
                unsafe { push_hit(data, ends, pos >> block_shift, pos as u32 | log_packed) };
                pos += p_us;
            }
        }
    }

    // --- carry positions for the small primes (p <= block_size) ---
    // two per prime, relative to the start of the block to be sieved next (a root is
    // below p, so in the first block); usize::MAX marks a missing root (no roots, or
    // the second copy of a double root)
    next_pos.clear();
    for (&root1, &root2) in roots.r1[ns..split].iter().zip(&roots.r2[ns..split]) {
        if root1 != Roots::NONE {
            next_pos.push(root1 as usize);
            if root2 == root1 {
                next_pos.push(usize::MAX); // marker: skip
            } else {
                next_pos.push(root2 as usize);
            }
        } else {
            next_pos.push(usize::MAX);
            next_pos.push(usize::MAX);
        }
    }

    let prof_t1 = profile.then(std::time::Instant::now);
    let mut prof_on_block = std::time::Duration::ZERO;

    // --- process each block: small primes by carry walk, then drain its bucket ---
    let small_primes = &factorbase[ns..split];
    let small_logs = &logs[ns..split];
    // the small primes walked through the sub-blocks
    let tiny = small_primes.partition_point(|&p| p <= blocking.sub_bound);
    let next_pos_ptr = next_pos.as_mut_ptr();
    if block.len() < block_size.min(total_len) {
        block.resize(block_size.min(total_len), 0);
    }
    // a bucket entry's position within its block (blocks start at multiples of
    // block_size)
    let offset_mask = (block_size - 1) & 0x00FF_FFFF;
    for block_idx in 0..num_blocks {
        let block_start = block_idx << block_shift;
        let block_len = block_size.min(total_len - block_start);
        let sums = &mut block[..block_len];
        sums.fill(0);
        let buf_ptr = sums.as_mut_ptr();
        // SAFETY: next_pos holds two entries per small prime, the first of which is
        // usize::MAX only if both are, and every write stays below block_len, the
        // length of `sums`
        unsafe {
            let mut sub_end = 0;
            while sub_end < block_len {
                sub_end = (sub_end + blocking.sub_size).min(block_len);
                // relative to the next block after the last sub-block
                let rebase = if sub_end == block_len { block_len } else { 0 };
                carry_walk(
                    &small_primes[..tiny],
                    &small_logs[..tiny],
                    next_pos_ptr,
                    buf_ptr,
                    sub_end,
                    rebase,
                );
            }
            carry_walk(
                &small_primes[tiny..],
                &small_logs[tiny..],
                next_pos_ptr.add(2 * tiny),
                buf_ptr,
                block_len,
                block_len,
            );
        }
        // drain the large-prime hits that fall in this block
        for &packed in buckets.block(block_idx) {
            // SAFETY: the entries of bucket block_idx hold positions of this block
            unsafe {
                let slot = buf_ptr.add(packed as usize & offset_mask);
                *slot = (*slot).wrapping_add((packed >> 24) as u8);
            }
        }
        let prof_t = profile.then(std::time::Instant::now);
        on_block(block_start, sums);
        if let Some(t) = prof_t {
            prof_on_block += t.elapsed();
        }
    }

    if let (Some(t0), Some(t1)) = (prof_t0, prof_t1) {
        SIEVE_SETUP_NANOS.fetch_add((t1 - t0).as_nanos() as u64, Ordering::Relaxed);
        let block_loop = t1.elapsed() - prof_on_block;
        SIEVE_LOOP_NANOS.fetch_add(block_loop.as_nanos() as u64, Ordering::Relaxed);
        SIEVE_CALLS.fetch_add(1, Ordering::Relaxed);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Naive reference sieve: for each non-skipped prime, walk every hit over the
    // whole window, from the offsets. The blocked/bucketed sieve must produce a
    // byte-identical buffer.
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
                let mut pos = r as usize;
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
        let mut scratch = SieveScratch::default();
        // block sizes that are tiny (many blocks), that don't divide total_len, and
        // that exceed total_len (single block): every prime above the size goes to
        // the buckets. The scratch is reused, so each size must clear its blocks.
        // Sub-blocks of every size, which need not divide the block, for no, some
        // or all small primes.
        let blockings = [8usize, 16, 64, 256, 512, 1024, 4096, 64, 8]
            .into_iter()
            .flat_map(|size| {
                [(size, 0), (3, 40), (16, 300), (100, 5000), (5000, 5000)].map(
                    |(sub_size, sub_bound)| Blocking {
                        size,
                        sub_size,
                        sub_bound,
                    },
                )
            });
        for blocking in blockings {
            let block_size = blocking.size;
            let mut buf = vec![0u8; total_len];
            let mut next_start = 0;
            sieve_over_factorbase_blocked(
                sieve_interval_length,
                &factorbase,
                &roots,
                &logs,
                &mut scratch,
                blocking,
                |block_start, sums| {
                    // the blocks come in order, each complete
                    assert_eq!(block_start, next_start);
                    assert_eq!(sums.len(), block_size.min(total_len - block_start));
                    buf[block_start..block_start + sums.len()].copy_from_slice(sums);
                    next_start = block_start + sums.len();
                },
            );
            assert_eq!(next_start, total_len);
            assert_eq!(buf, want, "mismatch for {blocking:?}");
        }
    }
}
