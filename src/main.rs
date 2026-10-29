use std::process::ExitCode;
use std::thread;
use std::time::Instant;

use log::{Level, LevelFilter, Log, Metadata, Record};
use rug::Integer;

use siqs::sieve::quadratic_sieve_lanczos;

const USAGE: &str = "\
Usage: siqs [-t THREADS] [N ...]

Factors each N with the self-initializing quadratic sieve and prints a factor.
Without N, it factors the examples of 202, 251 and 301 bits.

Options:
  -t, --threads THREADS  the number of sieving threads; the default is one less
                         than the available parallelism
  -h, --help             print this help

SIQS_LOG sets the log level: error, warn, info (the default), debug or trace.";

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

/// The command line: the number of sieving threads and the numbers to factor.
struct Args {
    num_threads: usize,
    numbers: Vec<Integer>,
}

/// Parses the arguments after the program name; `None` asks for the help.
fn parse_args(mut args: impl Iterator<Item = String>) -> Result<Option<Args>, String> {
    let mut num_threads = None;
    let mut numbers = Vec::new();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-h" | "--help" => return Ok(None),
            "-t" | "--threads" => {
                let value = args.next().ok_or("missing number of threads")?;
                let threads = value.parse::<usize>().ok().filter(|&threads| threads > 0);
                num_threads =
                    Some(threads.ok_or_else(|| format!("invalid number of threads: {value}"))?);
            }
            _ => numbers.push(
                arg.parse::<Integer>()
                    .map_err(|_| format!("not an integer: {arg}"))?,
            ),
        }
    }
    // the calling thread collects the relations
    let default_threads = || thread::available_parallelism().map_or(1, |n| n.get() - 1);
    Ok(Some(Args {
        num_threads: num_threads.unwrap_or_else(default_threads).max(1),
        numbers,
    }))
}

/// The examples factored without arguments: semiprimes of about 202, 251 and 301
/// bits, with factors of about equal size.
fn examples() -> Vec<Integer> {
    let next_prime = |bits: u32| (Integer::from(1) << bits).next_prime();
    vec![
        "6427752177035961102167848371107669985402627402189138248671463"
            .parse()
            .unwrap(),
        "3618502788666131106986593281521497123009340068573423410141280881914517913789"
            .parse()
            .unwrap(),
        next_prime(150) * next_prime(151),
    ]
}

fn main() -> ExitCode {
    let args = match parse_args(std::env::args().skip(1)) {
        Ok(Some(args)) => args,
        Ok(None) => {
            println!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        Err(message) => {
            eprintln!("error: {message}\n\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    let numbers = if args.numbers.is_empty() {
        examples()
    } else {
        args.numbers
    };

    // log level from SIQS_LOG (error, warn, info, debug or trace), info by default
    let level = std::env::var("SIQS_LOG")
        .ok()
        .and_then(|level| level.parse().ok())
        .unwrap_or(LevelFilter::Info);
    log::set_logger(&Logger).expect("no other logger is set");
    log::set_max_level(level);

    let mut status = ExitCode::SUCCESS;
    for n in &numbers {
        let start = Instant::now();
        match quadratic_sieve_lanczos(n, args.num_threads) {
            Ok(Some(factor)) => println!(
                "{n} = {factor} * {} ({} ms)",
                n.clone() / &factor,
                start.elapsed().as_millis()
            ),
            Ok(None) => {
                eprintln!("no factor found for {n}");
                status = ExitCode::FAILURE;
            }
            Err(error) => {
                eprintln!("error: {error}");
                status = ExitCode::FAILURE;
            }
        }
    }
    status
}
