use siqs::relations;

use std::time::Instant;

fn is_prime(n: u32) -> bool {
    if n < 2 { return false; }
    if n % 2 == 0 { return n == 2; }
    let mut d = 3u32;
    while (d as u64) * (d as u64) <= n as u64 {
        if n % d == 0 { return false; }
        d += 2;
    }
    true
}

// generate first `count` primes starting from 3 (we will later insert -1 and 2 if needed)
fn generate_primes(count: usize) -> Vec<u32> {
    let mut primes = Vec::with_capacity(count);
    let mut p = 3u32;
    while primes.len() < count {
        if is_prime(p) {
            primes.push(p);
        }
        p += 2;
    }
    primes
}

// tiny deterministic pseudo RNG
fn next_rand(seed: &mut u64) -> u64 {
    *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    *seed
}

fn main() {
    // parameters (anpassbar)
    let sieve_interval_length = 65536usize; // half-window; total_len = 131072
    let num_primes = 2000usize; // Größe des factorbase (ohne -1 und 2)
    let iters = 5usize; // wie oft pro Blockgröße laufen (für stabileren Mittelwert)

    // Build synthetic factorbase, roots and logs
    // We'll create factorbase entries: [-1, 2, primes...]
    let mut factorbase: Vec<u32> = Vec::with_capacity(2 + num_primes);
    factorbase.push(u32::MAX); // placeholder for -1 (index 0 in original code)
    factorbase.push(2); // index 1
    let primes = generate_primes(num_primes);
    factorbase.extend_from_slice(&primes);

    // roots: for -1 and 2 we put None placeholders (the sieve code expects alignment)
    let mut roots: Vec<Option<(u32, u32)>> = Vec::with_capacity(factorbase.len());
    roots.push(None); // -1
    roots.push(None); // 2

    // deterministic roots for primes
    let mut seed = 123456789u64;
    for &p in &primes {
        let r1 = (next_rand(&mut seed) % (p as u64)) as u32;
        let r2 = (next_rand(&mut seed) % (p as u64)) as u32;
        roots.push(Some((r1, r2)));
    }

    // logs: simple scaled ln(p)
    let mut logs: Vec<u32> = Vec::with_capacity(factorbase.len());
    logs.push(0); // -1
    logs.push(0); // 2
    for &p in &primes {
        let v = ((p as f64).ln() * 1000.0) as u32;
        logs.push(v.max(1));
    }

    // Prepare the reusable buffer
    let total_len = 2 * sieve_interval_length;
    let mut buffer = vec![0u32; total_len];

    // block sizes to test
    let block_sizes = vec![1024usize, 4096, 16384, 32768, 65536, 2 * 65536, 3 * 65536, 4 * 65536];

    println!("Benchmark: sieve interval total_len = {}, primes = {}", total_len, num_primes);
    println!("Running {} iterations per block size\n", iters);

    for &block_size in &block_sizes {
        // warmup
        let _ = crate::relations::sieve_over_factorbase_blocked(
            sieve_interval_length,
            &factorbase,
            &roots,
            &logs,
            &mut buffer,
            block_size,
        );

        // measure
        let start = Instant::now();
        for _ in 0..iters {
            let _ = crate::relations::sieve_over_factorbase_blocked(
                sieve_interval_length,
                &factorbase,
                &roots,
                &logs,
                &mut buffer,
                block_size,
            );
        }
        let elapsed = start.elapsed();
        let avg = elapsed / (iters as u32);
        println!(
            "block_size = {:6} -> total = {:>9} ns, avg = {:>9} ns",
            block_size,
            elapsed.as_nanos(),
            avg.as_nanos()
        );
    }

    println!("\nDone.");
}