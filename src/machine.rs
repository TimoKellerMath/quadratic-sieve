/// The number of cores. One sieving thread per core is the fastest: two hardware
/// threads of a core slow each other down, since they share its L2 (at 301 bits, 8
/// threads sieve 2.2% faster than 7, 14 threads 5.9% slower than 8).
pub const CORES: usize = number(option_env!("SIQS_CORES"), 8);

/// The size of a core's L1 data cache, in bytes.
pub const L1D: usize = kib(option_env!("SIQS_L1D_KIB"), 32);

/// The size of a core's L2 cache, in bytes.
pub const L2: usize = kib(option_env!("SIQS_L2_KIB"), 512);

/// The size of the L3 cache shared by all cores, in bytes. Kept for the record; no
/// parameter depends on it yet.
pub const L3: usize = kib(option_env!("SIQS_L3_KIB"), 16 << 10);

// the sieve needs at least one core and non-empty caches
const _: () = assert!(
    CORES > 0 && L1D > 0 && L2 > 0,
    "a core count or cache size of 0"
);

/// The size of a sieve block, from [`L2`] by [`sieve_block_size`]. `SIQS_BLOCK_KIB`
/// overrides it at run time, for parameter sweeps.
pub const SIEVE_BLOCK_SIZE: usize = sieve_block_size(L2);

/// The size of a sieve block for an L2 of `l2` bytes, a power of two: the largest
/// one up to a quarter of the L2, which was the fastest on the tuned machine (128
/// KiB).
pub const fn sieve_block_size(l2: usize) -> usize {
    let quarter = l2 / 4;
    if quarter == 0 {
        1
    } else {
        1 << quarter.ilog2()
    }
}

/// `value` KiB in bytes, where `value` is a decimal number from the environment at
/// compile time, or `default` KiB if it is not set.
const fn kib(value: Option<&str>, default: usize) -> usize {
    number(value, default) << 10
}

/// `value`, a decimal number from the environment at compile time, or `default` if
/// it is not set. A malformed value fails the build.
const fn number(value: Option<&str>, default: usize) -> usize {
    let Some(value) = value else {
        return default;
    };
    let digits = value.as_bytes();
    assert!(!digits.is_empty(), "not a number");
    let mut number = 0usize;
    let mut i = 0;
    while i < digits.len() {
        assert!(digits[i].is_ascii_digit(), "not a number");
        number = number * 10 + (digits[i] - b'0') as usize;
        i += 1;
    }
    number
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sieve_block_is_a_quarter_of_the_l2() {
        assert_eq!(sieve_block_size(512 << 10), 128 << 10);
        assert_eq!(sieve_block_size(1 << 20), 256 << 10);
        // rounded down to a power of two
        assert_eq!(sieve_block_size(1280 << 10), 256 << 10);
        assert_eq!(sieve_block_size(3 << 20), 512 << 10);
        assert_eq!(sieve_block_size(0), 1);
    }

    #[test]
    fn sizes_are_read_from_decimal_numbers() {
        assert_eq!(kib(None, 32), 32 << 10);
        assert_eq!(kib(Some("1024"), 32), 1 << 20);
        assert_eq!(kib(Some("0"), 32), 0);
        assert_eq!(number(Some("12"), 8), 12);
        assert_eq!(number(None, 8), 8);
    }
}
