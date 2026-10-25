// this file uses the computation of the multiplier and some sieve parameters from msieve

use crate::number_theory::*;
use rug::{Complete, Integer};

pub fn compute_multiplier(n: &Integer) -> Result<u32, NumberTheoryError> {
    let multipliers = [
        1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30, 31, 33, 34, 35, 37,
        38, 39, 41, 42, 43, 46, 47, 51, 53, 55, 57, 58, 59, 61, 62, 65, 66, 67, 69, 70, 71, 73,
    ];
    let mut scores = vec![0f64; multipliers.len()];
    for (i, k) in multipliers.iter().enumerate() {
        let kn_mod_8: Integer = (Integer::from(*k) * n) % 8;
        let log_k = (*k as f64).ln();
        scores[i] = 0.5f64 * log_k;
        match kn_mod_8.to_u8().unwrap() {
            1 => scores[i] -= 2f64 * 2f64.ln(),
            5 => scores[i] -= 2f64.ln(),
            3 | 7 => scores[i] -= 0.5f64 * 2f64.ln(),
            _ => (),
        }
    }
    for p in SMALL_PRIMES {
        let contribution_p = (p as f64).ln() / ((p - 1) as f64);
        let n_mod_p = (n % p).complete().to_u32().unwrap();
        if n_mod_p == 0 {
            return Err(NumberTheoryError::NotCoprime(n.clone(), Integer::from(p)));
        }
        for (i, k) in multipliers.iter().enumerate() {
            let kn_mod_p = (k * n_mod_p) % p;
            if kn_mod_p == 0 {
                scores[i] -= contribution_p;
            }
            if Integer::from(kn_mod_p).legendre(&Integer::from(p)) == 1 {
                scores[i] -= 2f64 * contribution_p;
            }
        }
    }
    //println!("scores = {scores:?}");
    let mut min_score = f64::INFINITY;
    let mut index = 0;
    for (i, score) in scores.iter().enumerate() {
        if *score < min_score {
            min_score = *score;
            index = i;
        }
    }
    Ok(multipliers[index])
}

#[allow(dead_code)]
#[derive(Debug)]
struct SieveParameter {
    bits: usize,
    factorbase_size: usize,
    large_prime_multiplier: u32,
    sieve_size: usize,
}

// from msieve -> mpqs.c
#[rustfmt::skip]
const SIEVE_PARAMETERS: &[SieveParameter] = &[
    SieveParameter { bits: 64,  factorbase_size: 100,    large_prime_multiplier: 40,  sieve_size: 65536       },
    SieveParameter { bits: 128, factorbase_size: 450,    large_prime_multiplier: 40,  sieve_size: 65536       },
    SieveParameter { bits: 183, factorbase_size: 2000,   large_prime_multiplier: 40,  sieve_size: 65536       },
    SieveParameter { bits: 200, factorbase_size: 3000,   large_prime_multiplier: 50,  sieve_size: 3 * 65536   },
    SieveParameter { bits: 212, factorbase_size: 5400,   large_prime_multiplier: 50,  sieve_size: 3 * 65536   },
    SieveParameter { bits: 233, factorbase_size: 10000,  large_prime_multiplier: 100, sieve_size: 3 * 65536   },
    SieveParameter { bits: 249, factorbase_size: 27000,  large_prime_multiplier: 100, sieve_size: 3 * 65536   },
    SieveParameter { bits: 266, factorbase_size: 50000,  large_prime_multiplier: 100, sieve_size: 3 * 65536   },
    SieveParameter { bits: 283, factorbase_size: 55000,  large_prime_multiplier: 80,  sieve_size: 3 * 65536   },
    SieveParameter { bits: 298, factorbase_size: 60000,  large_prime_multiplier: 80,  sieve_size: 9 * 65536   },
    SieveParameter { bits: 315, factorbase_size: 80000,  large_prime_multiplier: 150, sieve_size: 9 * 65536   },
    SieveParameter { bits: 332, factorbase_size: 100000, large_prime_multiplier: 150, sieve_size: 9 * 65536   },
    SieveParameter { bits: 348, factorbase_size: 140000, large_prime_multiplier: 150, sieve_size: 9 * 65536   },
    SieveParameter { bits: 363, factorbase_size: 210000, large_prime_multiplier: 150, sieve_size: 13 * 65536  },
    SieveParameter { bits: 379, factorbase_size: 300000, large_prime_multiplier: 150, sieve_size: 17 * 65536  },
    SieveParameter { bits: 395, factorbase_size: 400000, large_prime_multiplier: 150, sieve_size: 21 * 65536  },
];

// From the bit length bits of n, compute the factorbase size and the sieve size
pub fn compute_sieve_parameters(bits: usize) -> (usize, usize, u32) {
    let first_parameter = &SIEVE_PARAMETERS[0];
    if bits <= first_parameter.bits {
        return (
            first_parameter.factorbase_size,
            first_parameter.sieve_size,
            first_parameter.large_prime_multiplier,
        );
    }
    let last_parameter = SIEVE_PARAMETERS.last().unwrap();
    if bits >= last_parameter.bits {
        return (
            last_parameter.factorbase_size,
            last_parameter.sieve_size,
            last_parameter.large_prime_multiplier,
        );
    }

    let idx = SIEVE_PARAMETERS
        .iter()
        .position(|parameter| bits <= parameter.bits)
        .unwrap();
    let parameter = &SIEVE_PARAMETERS[idx - 1];
    let next_parameter = &SIEVE_PARAMETERS[idx];
    let dist = next_parameter.bits - parameter.bits;
    let dist_low = bits - parameter.bits;
    let dist_high = next_parameter.bits - bits;
    (
        (((parameter.factorbase_size * dist_high + next_parameter.factorbase_size * dist_low)
            as f64)
            / (dist as f64)
            + 0.5f64) as usize,
        (((parameter.sieve_size * dist_high + next_parameter.sieve_size * dist_low) as f64)
            / (dist as f64)
            + 0.5f64) as usize,
        (((parameter.large_prime_multiplier * dist_high as u32
            + next_parameter.large_prime_multiplier * dist_low as u32) as f64)
            / (dist as f64)
            + 0.5f64) as u32,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multipliers_of_the_examples() {
        // the 202-, 251- and 301-bit examples from main.rs
        let n202: Integer = "6427752177035961102167848371107669985402627402189138248671463"
            .parse()
            .unwrap();
        let n251: Integer =
            "3618502788666131106986593281521497123009340068573423410141280881914517913789"
                .parse()
                .unwrap();
        let n301 =
            (Integer::from(1) << 150u32).next_prime() * (Integer::from(1) << 151u32).next_prime();
        assert_eq!(compute_multiplier(&n202).unwrap(), 23);
        assert_eq!(compute_multiplier(&n251).unwrap(), 1);
        assert_eq!(compute_multiplier(&n301).unwrap(), 3);
    }

    #[test]
    fn multiplier_rejects_small_factors() {
        let mersenne = (Integer::from(1) << 61u32) - 1u32;
        for p in [2u32, 7, 997] {
            let n = mersenne.clone() * p;
            assert!(
                matches!(compute_multiplier(&n), Err(NumberTheoryError::NotCoprime(_, q)) if q == p),
                "factor {p} not reported"
            );
        }
    }

    #[test]
    fn sieve_parameters_at_table_entries() {
        assert_eq!(compute_sieve_parameters(200), (3000, 3 * 65536, 50));
        assert_eq!(compute_sieve_parameters(212), (5400, 3 * 65536, 50));
        assert_eq!(compute_sieve_parameters(298), (60000, 9 * 65536, 80));
    }

    #[test]
    fn sieve_parameters_are_interpolated() {
        // halfway between the entries for 200 and 212 bits
        assert_eq!(compute_sieve_parameters(206), (4200, 3 * 65536, 50));
        // between 283 (55000, 3 * 65536, 80) and 298 (60000, 9 * 65536, 80)
        assert_eq!(compute_sieve_parameters(290), (57333, 380109, 80));
        // the factor base never shrinks as n grows
        for bits in 64..400 {
            assert!(compute_sieve_parameters(bits).0 <= compute_sieve_parameters(bits + 1).0);
        }
    }

    #[test]
    fn sieve_parameters_are_clamped_to_the_table() {
        assert_eq!(compute_sieve_parameters(10), (100, 65536, 40));
        assert_eq!(compute_sieve_parameters(64), (100, 65536, 40));
        // above the table, all three come from its last entry; the large-prime
        // multiplier used to come from the first one (c089ffc)
        assert_eq!(compute_sieve_parameters(395), (400000, 21 * 65536, 150));
        assert_eq!(compute_sieve_parameters(500), (400000, 21 * 65536, 150));
    }
}
