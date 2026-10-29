/// The number of factor-base entries that are never sieved: −1, 2 and the smallest
/// odd primes. Trial division divides them out directly, and the threshold assumes
/// that each contributes its log. (The small prime variation leaves further primes
/// unsieved, whose logs the scan adds back exactly.)
pub const NUM_SKIP_PRIMES: usize = 6;
// index 0 of the factor base stands for -1 and must never be sieved
const _: () = assert!(NUM_SKIP_PRIMES >= 1);
