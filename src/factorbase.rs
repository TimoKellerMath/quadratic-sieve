use crate::number_theory::square_root_mod_p;
use rug::Integer;

/// The factor base of `size` entries for n: 0, which stands for −1, then 2 and the
/// smallest odd primes p with (n/p) = 1. Apart from the primes dividing n, these are
/// the only odd primes that divide numbers y² − n.
pub fn make_factorbase(n: &Integer, size: usize) -> Vec<u32> {
    let mut factorbase = Vec::with_capacity(size);
    factorbase.push(0);
    factorbase.push(2);
    let mut p = Integer::from(2);
    for _ in 2..size {
        p = p.next_prime();
        while n.legendre(&p) != 1 {
            p = p.next_prime();
        }
        factorbase.push(p.to_u32().unwrap());
    }
    factorbase
}

/// The inverses 1/p of the factor-base primes as f32, with which trial division
/// reduces a position modulo p by a multiplication instead of a division. The entry
/// for −1 is 0; trial division reads only those from
/// [`NUM_SKIP_PRIMES`](crate::constants::NUM_SKIP_PRIMES) on.
pub fn compute_inverses(factorbase: &[u32]) -> Vec<f32> {
    factorbase
        .iter()
        .map(|&p| if p >= 2 { 1.0 / p as f32 } else { 0.0 })
        .collect()
}

/// The logs of the factor-base primes, log2 p rounded to the nearest integer, and 0
/// for −1.
pub fn compute_logs(factorbase: &[u32]) -> Vec<u8> {
    std::iter::once(0u8) // log_2|-1|
        .chain(
            factorbase
                .iter()
                .skip(1)
                .map(|&p| (p as f32).log2().round() as u8),
        )
        .collect()
}

/// A square root of n modulo each odd factor-base prime, in [0, p), and the unused
/// placeholders 0 for −1 and 1 for 2. Panics if n is not a square modulo one of the
/// odd primes.
pub fn square_roots_mod_factorbase(n: &Integer, factorbase: &[u32]) -> Vec<u32> {
    let mut square_roots = Vec::with_capacity(factorbase.len());
    square_roots.push(0);
    square_roots.push(1);
    for p in factorbase.iter().skip(2) {
        square_roots.push(
            square_root_mod_p(n, &Integer::from(*p))
                .unwrap()
                .to_u32()
                .unwrap(),
        );
    }
    square_roots
}

#[cfg(test)]
mod tests {
    use super::*;
    use rug::integer::IsPrime;

    // the 202-bit example from main.rs
    fn example_n() -> Integer {
        "6427752177035961102167848371107669985402627402189138248671463"
            .parse()
            .unwrap()
    }

    #[test]
    fn test_make_factorbase() {
        let factorbase = make_factorbase(&Integer::from(400003), 10);
        // index 0 holds the sentinel 0 standing for -1
        assert_eq!(factorbase, vec![0u32, 2, 3, 7, 29, 31, 37, 43, 71, 73]);
    }

    #[test]
    fn factorbase_holds_exactly_the_quadratic_residue_primes() {
        let n = example_n();
        let factorbase = make_factorbase(&n, 500);
        assert_eq!(factorbase.len(), 500);
        assert_eq!(&factorbase[..2], &[0, 2]);
        // every odd prime up to the largest one, if and only if n is a square mod it
        let largest = *factorbase.last().unwrap();
        let expected: Vec<u32> = (3..=largest)
            .filter(|&p| {
                let p = Integer::from(p);
                p.is_probably_prime(30) != IsPrime::No && n.legendre(&p) == 1
            })
            .collect();
        assert_eq!(&factorbase[2..], &expected[..]);
    }

    #[test]
    fn test_square_roots_mod_factorbase() {
        let n = Integer::from(400003);
        let factorbase = make_factorbase(&n, 10);
        let square_roots = square_roots_mod_factorbase(&n, &factorbase);
        // index 0 (the -1 sentinel) has square root 0
        assert_eq!(square_roots, vec![0u32, 1, 1, 4, 8, 14, 12, 24, 29, 6]);
    }

    #[test]
    fn square_roots_square_to_n() {
        let n = example_n();
        let factorbase = make_factorbase(&n, 500);
        let square_roots = square_roots_mod_factorbase(&n, &factorbase);
        assert_eq!(&square_roots[..2], &[0, 1]);
        for (&p, &r) in factorbase.iter().zip(&square_roots).skip(2) {
            assert!(r < p, "root {r} of n mod {p} is not reduced");
            assert_eq!(
                (Integer::from(r).square() - &n).mod_u(p),
                0,
                "r^2 != n mod {p}"
            );
        }
    }

    #[test]
    fn logs_are_rounded_log2() {
        let factorbase = make_factorbase(&example_n(), 500);
        let logs = compute_logs(&factorbase);
        assert_eq!(logs.len(), factorbase.len());
        assert_eq!(&logs[..2], &[0, 1]);
        for (&p, &log) in factorbase.iter().zip(&logs).skip(1) {
            let error = ((p as f64).log2() - log as f64).abs();
            assert!(error <= 0.5 + 1e-6, "log of {p} is {log}");
        }
    }

    #[test]
    fn inverses_are_rounded_one_over_p() {
        let factorbase = make_factorbase(&example_n(), 500);
        let inverses = compute_inverses(&factorbase);
        // the -1 sentinel has none
        assert_eq!(inverses[0], 0.0);
        for (&p, &inverse) in factorbase.iter().zip(&inverses).skip(1) {
            let error = (inverse as f64 - 1.0 / p as f64).abs();
            assert!(
                error <= 1.0 / p as f64 * f32::EPSILON as f64 / 2.0,
                "inverse of {p}"
            );
        }
    }
}
