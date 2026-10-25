Rust implementation of the self-initializing/multiple polynomial quadratic sieve (SIQS/MPQS)

It factors integers from about 64 to 300 bits, such as RSA-style semiprimes,
on multiple threads.

## Features

- **Polynomials:** self-initialization (2^(s-1) polynomials per `a`) and a
  Knuth–Schroeppel multiplier.
- **Sieving:** segmented sieve with bucket sieving for primes larger than the
  block size, per-block thresholds from the size of Q(x), and an AVX2 threshold
  scan when compiled with AVX2.
- **Trial division:** resieving, with Barrett reduction for `x mod p`.
- **Large primes:** single large prime variation, and the double large prime
  variation above 250 bits (cofactors split by Pollard rho in Montgomery
  arithmetic, partials combined by cycle finding).
- **Linear algebra:** Block Lanczos over GF(2), parallelized, after removing
  singleton relations.
- **Threads:** one sieving thread per polynomial generator and one thread
  collecting relations.

## Requirements

- Rust (stable, edition 2024)
- GMP as a system library, e.g. `apt install libgmp-dev` or `pacman -S gmp`

`.cargo/config.toml` builds for the native CPU (`target-cpu=native`), so
binaries may not run on other machines.

## Usage

`cargo run --release` factors the example numbers in `src/main.rs` (202, 251
and 301 bits). There is no command-line interface yet; to factor your own
number, edit `src/main.rs` or call the library:

```rust
use rug::Integer;
use siqs::sieve::quadratic_sieve_lanczos;

let n: Integer = "6427752177035961102167848371107669985402627402189138248671463"
    .parse()
    .unwrap();
let num_threads = 7; // sieving threads
let factor: Option<Integer> = quadratic_sieve_lanczos(&n, num_threads).unwrap();
```

The library prints its progress to stdout. There are two solvers with the same
signature:

- `quadratic_sieve_lanczos` collects relations until it has 192 more than the
  number of primes that appear, then runs Block Lanczos. Use it for larger
  numbers.
- `quadratic_sieve_multithreaded` runs Gaussian elimination after every
  relation and stops at the first dependency. It is only practical for small
  factor bases.

`n` must not have prime factors below 1000 (an error is returned otherwise),
and it is not checked for primality or perfect powers, so remove small factors
and test for primality first.

### Environment variables

| Variable | Effect |
|---|---|
| `SIQS_LP_SLACK` | Sieve threshold slack, in units of the large-prime bound's log. Defaults: 0.75, or 0.72 to 1.15 with the double large prime variation, depending on the size of `n`. |
| `SIQS_GLOBAL_THRESHOLD` | Use one threshold for the whole sieve interval instead of one per block. |
| `SIQS_PROFILE` | Print per-phase timings of the first sieving thread to stderr every 2000 polynomials. |
| `SIQS_DUMP_MATRIX=path` | Write the relation matrix to `path` if Block Lanczos fails. |
| `SIQS_BL_DEBUG` | Print the rank Block Lanczos finds. |

### Other binaries

- `bench_sieve_block` compares sieve block sizes.
- `lanczos_repro` replays a matrix written by `SIQS_DUMP_MATRIX` through Block
  Lanczos.

## Performance

`quadratic_sieve_lanczos` on the examples in `src/main.rs`, with 7 sieving
threads on an AMD Ryzen 7 PRO 6850U laptop (8 cores). The total also includes
setup and computing the factor from the dependencies.

| `n` | Factor base | Relations | Block Lanczos | Total |
|---|---|---|---|---|
| 202 bits | 4,600 | 0.89 s | 0.03 s | 0.97 s |
| 251 bits | 32,412 | 20.7 s | 0.60 s | 22.2 s |
| 301 bits | 67,059 | 703 s | 3.2 s | 712 s |

## Tests

```sh
cargo test --profile profiling
cargo test --profile profiling --test factoring -- --ignored   # 202- and 250-bit cases
```

The `profiling` profile is optimized like `release` but without fat LTO, so it
builds much faster.

## Source overview

| File | Contents |
|---|---|
| `src/sieve.rs` | Driver: sieving threads, relation collection, both solvers |
| `src/siqs_generator.rs` | Self-initializing polynomial generation |
| `src/block_sieve.rs` | The sieve, in blocks, with buckets for the large primes |
| `src/trial_division.rs` | Trial division of the sieve's candidates |
| `src/large_primes.rs` | Combining partial relations into full ones |
| `src/gauss.rs` | Incremental Gaussian elimination |
| `src/square_root.rs` | From a dependency to a factor |
| `src/linalg.rs` | Block Lanczos and a dense GF(2) solver |
| `src/number_theory.rs` | Modular square roots, Miller–Rabin, Pollard rho |
| `src/multiplier.rs` | Multiplier selection and parameter table |
| `src/factorbase.rs` | Factor base, square roots of `kn`, logs, reciprocals |

## License

BSD 3-Clause, see [LICENSE](LICENSE). The Block Lanczos solver in
`src/linalg.rs` is derived from
[SebWouters/blanczos](https://github.com/SebWouters/blanczos) (BSD 3-Clause).
The multiplier selection and sieve parameters follow msieve (public domain).
