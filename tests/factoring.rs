// Integration tests for the public sieve entry point used by main.rs:
// siqs::sieve::quadratic_sieve_lanczos.
//
// Each test builds a known semiprime, factors it, and checks the returned
// factor is non-trivial and actually divides n. Run heavy cases with
// `cargo test --release -- --ignored`.

use rug::Integer;
use siqs::number_theory::NumberTheoryError;
use siqs::sieve::quadratic_sieve_lanczos;

/// Deterministic semiprime n = p*q with p ~ 2^bits_p, q ~ 2^bits_q.
fn semiprime(bits_p: u32, bits_q: u32) -> (Integer, Integer, Integer) {
    let p = ((Integer::from(1) << bits_p) + 12345u32).next_prime();
    let q = ((Integer::from(1) << bits_q) + 67890u32).next_prime();
    let n = p.clone() * q.clone();
    (n, p, q)
}

/// Assert the result is a valid non-trivial divisor of n.
fn assert_valid_factor(n: &Integer, result: Option<Integer>) {
    let factor = result
        .unwrap_or_else(|| panic!("sieve found no factor for {}-bit n", n.significant_bits()));
    assert!(
        factor != 1 && factor != *n,
        "trivial factor {factor} for {}-bit n",
        n.significant_bits()
    );
    assert!(
        n.is_divisible(&factor),
        "{factor} does not divide the {}-bit n",
        n.significant_bits()
    );
}

/// Factor n and assert a valid divisor.
fn check_factor(n: &Integer, num_threads: usize) {
    let result = quadratic_sieve_lanczos(n, num_threads)
        .unwrap_or_else(|e| panic!("sieve errored on {}-bit n: {e}", n.significant_bits()));
    assert_valid_factor(n, result);
}

// Small prime factors and the roots of perfect powers come back without sieving.
#[test]
fn small_factors_and_perfect_powers_need_no_sieve() {
    let factor = |n: Integer| quadratic_sieve_lanczos(&n, 1).unwrap();
    let p = (Integer::from(1) << 40u32).next_prime();
    let q = (Integer::from(1) << 41u32).next_prime();
    assert_eq!(factor(Integer::from(6)), Some(Integer::from(2)));
    assert_eq!(factor(p.clone() * 997u32), Some(Integer::from(997)));
    assert_eq!(factor(p.clone().square()), Some(p.clone()));
    assert_eq!(factor(p.clone().square() * &p), Some(p.clone()));
    assert_eq!(factor((p.clone() * &q).square()), Some(p * q));
}

#[test]
fn primes_and_numbers_below_two_are_errors() {
    let large_prime = (Integer::from(1) << 100u32).next_prime();
    for n in [-15, 0, 1, 2, 997]
        .map(Integer::from)
        .into_iter()
        .chain([large_prime])
    {
        let result = quadratic_sieve_lanczos(&n, 1);
        assert!(
            matches!(result, Err(NumberTheoryError::NotComposite(ref m)) if *m == n),
            "n = {n}: {result:?}"
        );
    }
}

// zero sieving threads count as one
#[test]
fn factors_with_zero_threads() {
    let (n, _, _) = semiprime(32, 32);
    check_factor(&n, 0);
}

#[test]
fn factors_64_bit() {
    let (n, _, _) = semiprime(32, 32);
    check_factor(&n, 1);
}

#[test]
fn factors_80_bit() {
    let (n, _, _) = semiprime(40, 40);
    check_factor(&n, 2);
}

#[test]
fn factors_96_bit() {
    let (n, _, _) = semiprime(48, 48);
    check_factor(&n, 2);
}

#[test]
fn factors_120_bit() {
    let (n, _, _) = semiprime(60, 60);
    check_factor(&n, 4);
}

#[test]
fn factors_unbalanced_100_bit() {
    // a smaller and a larger prime factor
    let (n, _, _) = semiprime(30, 70);
    check_factor(&n, 2);
}

#[test]
fn factors_150_bit() {
    let (n, _, _) = semiprime(75, 75);
    check_factor(&n, 4);
}

// Regression test: the sieving tasks used to run on rayon's pool, where in a pool
// with one thread a sieving task, which never ends, starved the collecting task.
#[test]
fn factors_inside_a_single_threaded_rayon_pool() {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .unwrap();
    let (n, _, _) = semiprime(40, 40);
    pool.install(|| check_factor(&n, 2));
}

#[test]
#[ignore = "slow (~1s): run with --ignored"]
fn factors_202_bit() {
    // the exact number main.rs factors
    let n = "6427752177035961102167848371107669985402627402189138248671463"
        .parse::<Integer>()
        .unwrap();
    check_factor(&n, 7);
}

#[test]
#[ignore = "slow: run with --ignored"]
fn factors_250_bit() {
    let (n, _, _) = semiprime(125, 125);
    check_factor(&n, 7);
}

/// Pseudo-random semiprimes from 40 to 100 bits in steps of 4: for each size, one
/// with factors of about half the size and one with factors of about a third and
/// two thirds of it.
fn random_semiprimes() -> Vec<Integer> {
    let mut state = 0x9E37_79B9_7F4A_7C15u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut random_prime = |bits: u32| {
        let random = (Integer::from(next()) << 64u32) | Integer::from(next());
        // exactly `bits` bits, then the next prime
        ((random >> (128 - bits)) | (Integer::from(1) << (bits - 1))).next_prime()
    };
    let mut semiprimes = Vec::new();
    for bits in (40..=100).step_by(4) {
        for p_bits in [bits / 2, bits / 3] {
            let p = random_prime(p_bits);
            let q = random_prime(bits - p_bits);
            if p != q {
                semiprimes.push(p * q);
            }
        }
    }
    semiprimes
}

#[test]
fn factors_random_semiprimes() {
    for n in random_semiprimes() {
        check_factor(&n, 2);
    }
}
