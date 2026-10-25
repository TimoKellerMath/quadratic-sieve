use std::time::Instant;

use log::{Level, LevelFilter, Log, Metadata, Record};
use rug::Integer;

use siqs::sieve::quadratic_sieve_lanczos;

/// Prints the library's log messages: warnings and errors to stderr, the rest to
/// stdout.
struct Logger;

impl Log for Logger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= log::max_level()
    }

    fn log(&self, record: &Record) {
        if !self.enabled(record.metadata()) {
            return;
        }
        match record.level() {
            Level::Error | Level::Warn => eprintln!("{}: {}", record.level(), record.args()),
            _ => println!("{}", record.args()),
        }
    }

    fn flush(&self) {}
}

fn main() {
    // log level from SIQS_LOG (error, warn, info, debug or trace), info by default
    let level = std::env::var("SIQS_LOG")
        .ok()
        .and_then(|level| level.parse().ok())
        .unwrap_or(LevelFilter::Info);
    log::set_logger(&Logger).expect("no other logger is set");
    log::set_max_level(level);

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
    let factor = quadratic_sieve_lanczos(&n, num_threads)
        .unwrap()
        .expect("No factor found.");
    let elapsed_time = now.elapsed();
    println!("factor1 = {factor} ({} ms)", elapsed_time.as_millis());

    // 125 + 126 bit:
    let n = "3618502788666131106986593281521497123009340068573423410141280881914517913789"
        .parse::<Integer>()
        .unwrap();
    let num_threads = 7;

    let now = Instant::now();
    let factor = quadratic_sieve_lanczos(&n, num_threads)
        .unwrap()
        .expect("No factor found.");
    let elapsed_time = now.elapsed();
    println!("factor1 = {factor} ({} ms)", elapsed_time.as_millis());

    // 150 + 151 bit:
    let n =
        (Integer::from(1u32) << 150i32).next_prime() * (Integer::from(1u32) << 151i32).next_prime();
    let num_threads = 7;

    let now = Instant::now();
    let factor = quadratic_sieve_lanczos(&n, num_threads)
        .unwrap()
        .expect("No factor found.");
    let elapsed_time = now.elapsed();
    println!("factor1 = {factor} ({} ms)", elapsed_time.as_millis());
}
