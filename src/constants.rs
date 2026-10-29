/// The number of factor-base entries that are not sieved: −1, 2 and the smallest odd
/// primes. Trial division divides them out directly, and the threshold assumes that
/// each contributes its log.
pub const NUM_SKIP_PRIMES: usize = 6;
// index 0 of the factor base stands for -1 and must never be sieved
const _: () = assert!(NUM_SKIP_PRIMES >= 1);
