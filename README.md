Rust implementation of the self-initializing/multiple polynomial quadratic sieve (SIQS/MPQS)

It factors integers from about 64 to 300 bits, such as RSA-style semiprimes,
on multiple threads.

## Features

- **Polynomials:** self-initialization (2^(s-1) polynomials per `a`) and a
  Knuth–Schroeppel multiplier.
- **Sieving:** segmented sieve with bucket sieving for primes larger than the
  block size, L1-sized sub-blocks for the smallest sieved primes, the small prime
  variation (the primes up to 256 are not sieved, but added back at the
  positions the scan finds), per-window thresholds from the size of Q(x), and an
  AVX2 threshold scan when compiled with AVX2.
- **Trial division:** the primes dividing a candidate are found from the roots,
  for all candidates of a polynomial in one pass over the factor base (with AVX2
  when compiled with it), and only those are divided out.
- **Large primes:** single large prime variation, and the double large prime
  variation above 250 bits (cofactors split by Pollard rho in Montgomery
  arithmetic, partials combined by cycle finding).
- **Linear algebra:** Block Lanczos over GF(2), parallelized, after removing
  singleton relations.
- **Threads:** one sieving thread per polynomial generator; the calling thread
  collects the relations.

## Requirements

- Rust (stable, edition 2024)
- GMP as a system library, e.g. `apt install libgmp-dev` or `pacman -S gmp`

`.cargo/config.toml` builds for the native CPU (`target-cpu=native`), so
binaries may not run on other machines, and aligns loops to 64 bytes, so that
the speed of the hot loops does not depend on where the code lands.

The sieve is tuned for the caches of the machine in [Performance](#performance):
8 cores, 32 KiB of L1d and 512 KiB of L2 per core, 16 MiB of L3. For another
machine, set the number of cores and the cache sizes in KiB when compiling, e.g.
`SIQS_CORES=16 SIQS_L1D_KIB=48 SIQS_L2_KIB=2048 cargo build --release`
(see `src/machine.rs`; the L3 size, `SIQS_L3_KIB`, is recorded but not used yet).

## Usage

```sh
cargo run --release -- 340282366920938463463374607431768211457   # 2^128 + 1
cargo run --release -- -t 4 N1 N2   # with 4 sieving threads
cargo run --release                 # the examples of 202, 251 and 301 bits
```

`siqs [-t THREADS] [N ...]` factors each `N` and prints it as a product of two
factors, with the time taken. Without `N`, it factors the examples in
`src/main.rs`. The default is one sieving thread per core (8, see
`src/machine.rs`): two hardware threads of a core slow each other down, since
they share its L2. The calling thread collects the relations, which takes little
time.

To call the library instead:

```rust
use rug::Integer;
use siqs::sieve::quadratic_sieve_lanczos;

let n: Integer = "6427752177035961102167848371107669985402627402189138248671463"
    .parse()
    .unwrap();
let num_threads = 7; // sieving threads
let factor: Option<Integer> = quadratic_sieve_lanczos(&n, num_threads).unwrap();
```

It collects relations until it has 192 more than the number of primes that
appear, then runs Block Lanczos. A prime factor of `n` below 1000, or the root
`m` of a perfect power `n = m^k`, is returned without sieving; for primes and
`n < 2` the result is an error.

The library logs its progress with the [`log`](https://docs.rs/log) crate, so
it prints nothing unless the program sets up a logger; `src/main.rs` has a
minimal one that prints to stdout. `cargo doc --open` shows the API
documentation, with an overview of the algorithm.

### Environment variables

| Variable | Effect |
|---|---|
| `SIQS_LP_SLACK` | Sieve threshold slack, in units of the large-prime bound's log. Defaults: 0.75, or 1.3 to 1.7 with the double large prime variation, depending on the size of `n`. |
| `SIQS_GLOBAL_THRESHOLD` | Use one threshold for the whole sieve interval instead of one per scan window of 16384 positions. |
| `SIQS_FB_SIZE`, `SIQS_M`, `SIQS_LP_MULT` | Override the factor base size, the half-length M of the sieve interval [−M, M) and the large-prime multiplier of the parameter table, for parameter sweeps. |
| `SIQS_DLP` | `1` or `0` turns the double large prime variation on or off; by default it is on above 250 bits. |
| `SIQS_DLP_EXP` | A cofactor with two large primes may be up to the large-prime bound to this power, at most 2; 1.85 by default. |
| `SIQS_SPV_BOUND`, `SIQS_SPV_ALLOWANCE` | The small prime variation: the sieve skips the primes up to the bound (256 for factor bases of 1000 primes or more, else 0), and the scan lowers its thresholds by the allowance in bits (30) and adds the logs of the skipped primes that divide Q at the positions found. |
| `SIQS_BLOCK_KIB` | Sieve block size in KiB, a power of two; by default the largest one up to a quarter of the L2. |
| `SIQS_PROFILE` | Print per-phase timings of the first sieving thread to stderr every 2000 polynomials. |
| `SIQS_DUMP_MATRIX=path` | Write the relation matrix to `path` if Block Lanczos fails. |
| `SIQS_BL_DEBUG` | Print the rank Block Lanczos finds. |
| `SIQS_LOG` | Log level of `siqs`: `error`, `warn`, `info` (default), `debug` or `trace`. |

### Other binaries

- `bench_sieve_block [bits [polynomials [block size in KiB ...]]]` times the sieve
  for several block sizes, on one thread, with the parameters and polynomials for a
  semiprime of the given size (default 301 bits).
- `lanczos_repro [path [seeds]]` replays a matrix written by `SIQS_DUMP_MATRIX`
  through Block Lanczos, with `SIQS_FILTER` after removing the singleton relations,
  and with `SIQS_MAX_ROWS=r` on its first `r` relations only;
  `lanczos_repro synthetic [relations [columns [appearing]]]` uses a random matrix
  shaped like a relation matrix instead.

## Performance

The examples in `src/main.rs` with the default of 8 sieving threads (`siqs`), on
an AMD Ryzen 7 PRO 6850U laptop (8 cores), one run each; the laptop throttles, so
times vary by about 10%. The total also includes setup and computing the factor
from the dependencies.

| `n` | Factor base | Relations | Block Lanczos | Total |
|---|---|---|---|---|
| 202 bits | 4,600 | 0.35 s | 0.03 s | 0.41 s |
| 251 bits | 32,412 | 9.7 s | 0.78 s | 10.8 s |
| 301 bits | 67,059 | 221 s | 5.5 s | 228 s |

## Tests

```sh
cargo test
cargo test --profile profiling --test factoring -- --ignored   # 202- and 250-bit cases
```

The `test` profile is optimized and keeps the debug assertions, which check
costly invariants. The `profiling` profile is optimized like `release` but
without fat LTO, so it builds much faster.

## Source overview

| File | Contents |
|---|---|
| `src/main.rs` | Command-line interface |
| `src/sieve.rs` | Driver: sieving threads and relation collection |
| `src/siqs_generator.rs` | Self-initializing polynomial generation |
| `src/block_sieve.rs` | The sieve, in blocks, with buckets for the large primes |
| `src/trial_division.rs` | Trial division of the sieve's candidates |
| `src/large_primes.rs` | Combining partial relations into full ones |
| `src/square_root.rs` | From a dependency to a factor |
| `src/linalg.rs` | Block Lanczos and a dense GF(2) solver |
| `src/number_theory.rs` | Modular square roots, Miller–Rabin, Pollard rho |
| `src/multiplier.rs` | Multiplier selection and parameter table |
| `src/machine.rs` | The cache sizes the sieve is tuned for |
| `src/factorbase.rs` | Factor base, square roots of `kn`, logs, inverses |

## License

BSD 3-Clause, see [LICENSE](LICENSE). The Block Lanczos solver in
`src/linalg.rs` is derived from
[SebWouters/blanczos](https://github.com/SebWouters/blanczos) (BSD 3-Clause).
The multiplier selection and sieve parameters follow msieve (public domain).
