//! Factors integers with the self-initializing quadratic sieve (SIQS).
//!
//! The entry point is [`sieve::quadratic_sieve_lanczos`], which finds a nontrivial
//! factor of a composite n of about 64 to 300 bits on several threads:
//!
//! ```
//! use rug::Integer;
//! use siqs::sieve::quadratic_sieve_lanczos;
//!
//! let p = (Integer::from(1) << 40u32).next_prime();
//! let q = (Integer::from(1) << 41u32).next_prime();
//! let n = p.clone() * &q;
//! let factor = quadratic_sieve_lanczos(&n, 2).unwrap().expect("a factor");
//! assert!(factor == p || factor == q);
//! ```
//!
//! # The algorithm
//!
//! The sieve collects relations u² ≡ v (mod kn) in which v factors over the factor
//! base, a set of small primes, up to one or two large primes. A set of relations
//! whose v multiply to a square gives x² ≡ y² (mod n), and gcd(x + y, n) is a proper
//! factor of n with probability about 1/2 or more. The steps, by module:
//!
//! 1. [`multiplier`] chooses the multiplier k and the sizes of the factor base and the
//!    sieve interval; [`factorbase`] computes the factor base and, for each of its
//!    primes, a square root of kn, the log and a reciprocal.
//! 2. [`siqs_generator`] generates the sieving polynomials Q(x) = a x² + 2 b x + c with
//!    b² − a c = kn, where a = q² is a square, and their roots modulo the factor base
//!    ([`polynomial_generator`]). The 2^(s−1) polynomials sharing one a, where s is
//!    the number of primes in q, follow each other with a cheap update of the roots.
//! 3. [`block_sieve`] adds the logs of the factor-base primes dividing Q(x), for every
//!    x of the interval [−M, M), in blocks, with buckets for the primes larger than a
//!    block.
//! 4. [`sieve`] runs one sieving thread per polynomial generator. Each scans the sums
//!    for candidates, where they come close to log2 |Q(x)|, and factors Q(x) there by
//!    [`trial_division`], which returns a [`relation::Relation`].
//! 5. [`large_primes`] combines partial relations, those with large primes left, into
//!    full ones, on the thread that collects the relations.
//! 6. Once there are enough full relations, [`linalg`] finds dependencies among them
//!    with Block Lanczos over GF(2), and [`square_root`] turns one into a factor.
//!
//! [`number_theory`] provides the modular arithmetic for these steps.

#![warn(missing_docs)]

/// The sieve: sums of logs over one polynomial's interval, in blocks, with buckets
/// for the primes larger than a block.
pub mod block_sieve;
/// Constants shared by the sieve and trial division.
pub mod constants;
/// The factor base, and the square roots of kn, logs and reciprocals modulo its
/// primes.
pub mod factorbase;
/// Combining partial relations, with one or two large primes, into full relations.
pub mod large_primes;
/// Dependencies among the relations: Block Lanczos over GF(2), with a dense
/// elimination as reference and fallback.
pub mod linalg;
/// The caches the sieve is tuned for, set at compile time.
///
/// The defaults describe the machine on which the parameters were measured, an AMD
/// Ryzen 7 PRO 6850U (Zen 3+, 8 cores with 2 hardware threads each): 32 KiB of L1d
/// and 512 KiB of L2 per core, and 16 MiB of L3 shared by all cores. For another
/// machine, set `SIQS_L1D_KIB`, `SIQS_L2_KIB` or `SIQS_L3_KIB` (in KiB) when
/// compiling, e.g. `SIQS_L2_KIB=1024 cargo build --release`. The SIMD code is chosen
/// at compile time too, by the target features (`target-cpu=native` in
/// `.cargo/config.toml`).
pub mod machine;
/// The multiplier and the sieve parameters, both after msieve.
pub mod multiplier;
/// Modular square roots and inverses, and primality tests and Pollard rho for 64-bit
/// integers.
pub mod number_theory;
/// Sieving polynomials and their roots modulo the factor base.
pub mod polynomial_generator;
/// Relations and their large primes.
pub mod relation;
/// The entry point: the sieving threads and the collection of their relations.
pub mod sieve;
/// Self-initializing generation of the sieving polynomials, one generator per sieving
/// thread.
pub mod siqs_generator;
/// From a dependency to a factor.
pub mod square_root;
/// Trial division of the sieve's candidates, with the large prime variations.
pub mod trial_division;
