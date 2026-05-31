use std::time::Instant;

use rug::Integer;

use siqs::sieve::quadratic_sieve_multithreaded;

fn main() {
    // Other example inputs:
    //   2^128 + 1:   (Integer::from(1) << 128) + 1
    //   2^149 - 1:   (Integer::from(1) << 149) - 1
    //   80 + 90 bit: "1496577676626844588240589522709118530816928848545473"
    // 100 + 102 bit:
    let n = "6427752177035961102167848371107669985402627402189138248671463"
        .parse::<Integer>()
        .unwrap();
    let num_threads = 7;

    let now = Instant::now();
    let factor = quadratic_sieve_multithreaded(&n, num_threads)
        .unwrap()
        .unwrap();
    let elapsed_time = now.elapsed();
    println!("factor1 = {factor} ({} ms)", elapsed_time.as_millis());
}
