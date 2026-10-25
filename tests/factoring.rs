// Integration tests for the public sieve entry point used by main.rs:
// siqs::sieve::quadratic_sieve_multithreaded.
//
// Each test builds a known semiprime, factors it, and checks the returned
// factor is non-trivial and actually divides n. Run heavy cases with
// `cargo test --release -- --ignored`.

use rug::Integer;
use siqs::sieve::{quadratic_sieve_lanczos, quadratic_sieve_multithreaded};

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

/// Factor n with the incremental-Gaussian solver and assert a valid divisor.
fn check_factor(n: &Integer, num_threads: usize) {
    let result = quadratic_sieve_multithreaded(n, num_threads)
        .unwrap_or_else(|e| panic!("sieve errored on {}-bit n: {e}", n.significant_bits()));
    assert_valid_factor(n, result);
}

/// Factor n with the Block Lanczos solver and assert a valid divisor.
fn check_factor_lanczos(n: &Integer, num_threads: usize) {
    let result = quadratic_sieve_lanczos(n, num_threads).unwrap_or_else(|e| {
        panic!(
            "lanczos sieve errored on {}-bit n: {e}",
            n.significant_bits()
        )
    });
    assert_valid_factor(n, result);
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

// --- Block Lanczos solver: same numbers, batch linear algebra ---

#[test]
fn lanczos_factors_64_bit() {
    let (n, _, _) = semiprime(32, 32);
    check_factor_lanczos(&n, 1);
}

#[test]
fn lanczos_factors_96_bit() {
    let (n, _, _) = semiprime(48, 48);
    check_factor_lanczos(&n, 2);
}

#[test]
fn lanczos_factors_120_bit() {
    let (n, _, _) = semiprime(60, 60);
    check_factor_lanczos(&n, 4);
}

#[test]
fn lanczos_factors_150_bit() {
    let (n, _, _) = semiprime(75, 75);
    check_factor_lanczos(&n, 4);
}

#[test]
fn lanczos_factors_unbalanced_100_bit() {
    let (n, _, _) = semiprime(30, 70);
    check_factor_lanczos(&n, 2);
}

#[test]
#[ignore = "slow: run with --ignored"]
fn lanczos_factors_202_bit() {
    let n = "6427752177035961102167848371107669985402627402189138248671463"
        .parse::<Integer>()
        .unwrap();
    check_factor_lanczos(&n, 7);
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
