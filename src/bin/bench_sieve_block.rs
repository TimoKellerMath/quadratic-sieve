// Times the sieve of one polynomial for several block sizes, with the parameters
// the sieve uses for a semiprime of the given size and the roots of its first
// polynomials. It runs on one thread, so unlike the sieving threads, the sieve has
// the shared caches to itself.
//
// Usage: bench_sieve_block [bits [polynomials [block size in KiB ...]]]
// Defaults: 301 bits, 1000 polynomials, block sizes of 16 to 512 KiB.
use rug::Integer;
use siqs::block_sieve::{Blocking, SieveScratch, SievedPrimes, sieve_over_factorbase_blocked};
use siqs::constants::NUM_SKIP_PRIMES;
use siqs::factorbase::{compute_logs, make_factorbase, square_roots_mod_factorbase};
use siqs::multiplier::{compute_multiplier, compute_sieve_parameters};
use siqs::number_theory::SMALL_PRIMES;
use siqs::siqs_generator::new_polynomial_generators;
use std::time::{Duration, Instant};

fn main() {
    let mut args = std::env::args().skip(1).map(|arg| {
        arg.parse::<usize>()
            .unwrap_or_else(|_| panic!("not a number: {arg}"))
    });
    let bits = args.next().unwrap_or(301);
    let polynomials = args.next().unwrap_or(1000).max(1);
    let mut block_sizes: Vec<usize> = args.map(|kib| kib << 10).collect();
    if block_sizes.is_empty() {
        block_sizes = (14..=19).map(|shift| 1 << shift).collect();
    }
    assert!(bits >= 40, "at least 40 bits");
    assert!(
        block_sizes.iter().all(|size| size.is_power_of_two()),
        "block sizes must be powers of two"
    );

    // a product of two primes of about half the size, with exactly `bits` bits
    let half = bits as u32 / 2;
    let p = (Integer::from(1) << half).next_prime();
    let q = (Integer::from(3) << (bits as u32 - half - 2)).next_prime();
    let n = p * q;
    assert_eq!(n.significant_bits() as usize, bits);

    // the parameters, as the sieve computes them for n
    let k = compute_multiplier(&n).expect("no small factors");
    let kn = n * k;
    let (factorbase_size, sieve_interval_length, _) =
        compute_sieve_parameters(kn.significant_bits() as usize + 1);
    let factorbase_without_k = make_factorbase(&kn, factorbase_size);
    let mut factorbase = factorbase_without_k.clone();
    factorbase.extend(SMALL_PRIMES.iter().filter(|&&p| k.is_multiple_of(p)));
    factorbase.sort_unstable();
    factorbase.dedup();
    let square_roots = square_roots_mod_factorbase(&kn, &factorbase);
    let logs = compute_logs(&factorbase);
    // SIQS_SPV_BOUND: the sieve skips the primes up to it, as with the small prime
    // variation
    let spv_bound: u32 = std::env::var("SIQS_SPV_BOUND")
        .ok()
        .and_then(|bound| bound.parse().ok())
        .unwrap_or(0);
    let primes = SievedPrimes::new(
        &factorbase,
        &logs,
        factorbase
            .partition_point(|&p| p <= spv_bound)
            .max(NUM_SKIP_PRIMES),
    );
    let mut generators = new_polynomial_generators(
        &kn,
        sieve_interval_length as u64,
        1,
        &factorbase,
        &square_roots,
        &factorbase_without_k,
    );
    let generator = &mut generators[0];
    println!(
        "{bits} bits: k = {k}, {} primes up to {}, interval of 2 * {sieve_interval_length}",
        factorbase.len(),
        factorbase.last().unwrap(),
    );

    let total_len = 2 * sieve_interval_length;
    let mut buffer = vec![0u8; total_len];
    let mut reference = vec![0u8; total_len];
    let mut scratch = SieveScratch::default();
    let mut times = vec![Duration::ZERO; block_sizes.len()];
    // one more polynomial to warm up
    for i in 0..=polynomials {
        let (_, roots) = generator.next_polynomial();
        // The block sizes take turns, so that they all see a machine of the same
        // temperature, and the first, which may find the roots still in the cache,
        // rotates. Every block size must give the same sums.
        for turn in 0..block_sizes.len() {
            let b = (i + turn) % block_sizes.len();
            // the time of the sieve, without copying its blocks out
            let start = Instant::now();
            let mut copy = Duration::ZERO;
            sieve_over_factorbase_blocked(
                sieve_interval_length,
                primes,
                roots,
                &mut scratch,
                Blocking::with_size(block_sizes[b]),
                |block_start, sums| {
                    let start = Instant::now();
                    buffer[block_start..block_start + sums.len()].copy_from_slice(sums);
                    copy += start.elapsed();
                },
            );
            if i > 0 {
                times[b] += start.elapsed() - copy;
            }
            if turn == 0 {
                reference.copy_from_slice(&buffer);
            } else {
                assert!(buffer == reference, "block size {} differs", block_sizes[b]);
            }
        }
    }

    for (&block_size, time) in block_sizes.iter().zip(&times) {
        println!(
            "block size {:>4} KiB: {:>6.0} us per polynomial",
            block_size >> 10,
            time.as_secs_f64() * 1e6 / polynomials as f64
        );
    }
}
