use crate::constants::NUM_SKIP_PRIMES;
use crate::polynomial_generator::Roots;
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
    // two per prime; usize::MAX marks a missing root (no roots, or the second copy
    // of a double root)
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
}
