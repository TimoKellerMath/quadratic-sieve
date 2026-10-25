pub const NUM_SKIP_PRIMES: usize = 6;
// index 0 of the factor base stands for -1 and must never be sieved
const _: () = assert!(NUM_SKIP_PRIMES >= 1);
