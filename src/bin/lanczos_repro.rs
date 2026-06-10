// Replay a dumped relation matrix (SIQS_DUMP_MATRIX format) through Block Lanczos to
// reproduce and debug a failure. Usage: lanczos_repro [path] [num_seeds]
use siqs::linalg::block_lanczos;
use std::fs;

// QS-like synthetic: heavy small-prime columns (col 0 = -1 in ~half, a handful of
// very common small primes), a sparse large-prime tail, n_f slightly above n_r.
// rows use only the first `appearing` columns; the matrix is declared over `n_f`
// columns, so n_f - appearing columns are never set (zero rows of B).
fn synthetic(n_r: usize, appearing: usize, mut seed: u64) -> Vec<Vec<u32>> {
    let mut rng = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    (0..n_r)
        .map(|_| {
            let mut acc = vec![false; appearing];
            for c in 0..20u32 {
                if rng() % 2 == 0 {
                    acc[c as usize] ^= true;
                }
            }
            for _ in 0..10 {
                acc[(rng() % appearing as u64) as usize] ^= true;
            }
            (0..appearing as u32).filter(|&c| acc[c as usize]).collect()
        })
        .collect()
}

fn main() {
    if std::env::args().nth(1).as_deref() == Some("synthetic") {
        let n_r: usize = std::env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(4000);
        let n_f: usize = std::env::args().nth(3).and_then(|s| s.parse().ok()).unwrap_or(4100);
        // 4th arg = appearing columns (default n_f); n_f - appearing are padding
        let appearing: usize = std::env::args().nth(4).and_then(|s| s.parse().ok()).unwrap_or(n_f);
        let rows = synthetic(n_r, appearing, 0x1234_5678_9ABC_DEF0);
        println!("synthetic {n_r} relations, {appearing} appearing, declared n_f={n_f}");
        for t in 0..4u64 {
            let seed = 0x5161_7A9F_2C3D_4E5Fu64 ^ t.wrapping_mul(0x9E3779B97F4A7C15);
            match block_lanczos(&rows, n_f, seed) {
                None => println!("seed[{t}]: BREAKDOWN"),
                Some(d) if d.is_empty() => println!("seed[{t}]: EMPTY"),
                Some(d) => println!("seed[{t}]: {} deps", d.len()),
            }
        }
        return;
    }
    let path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/tmp/lanczos_matrix.txt".to_string());
    let num_seeds: u64 = std::env::args()
        .nth(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or(8);

    let text = fs::read_to_string(&path).expect("read matrix file");
    let mut lines = text.lines();
    let header = lines.next().expect("header");
    let mut it = header.split_whitespace();
    let n_r: usize = it.next().unwrap().parse().unwrap();
    let n_f: usize = it.next().unwrap().parse().unwrap();
    let mut rows: Vec<Vec<u32>> = lines
        .map(|l| l.split_whitespace().map(|x| x.parse().unwrap()).collect())
        .collect();
    assert_eq!(rows.len(), n_r, "row count mismatch");
    // optionally truncate to the first N relations (simulate a smaller surplus)
    if let Ok(maxr) = std::env::var("SIQS_MAX_ROWS") {
        let maxr: usize = maxr.parse().unwrap();
        rows.truncate(maxr);
    }
    let n_r = rows.len();
    println!("loaded {n_r} relations x {n_f} columns");

    // SIQS_FILTER=1: iteratively remove singleton relations (those containing a prime
    // that appears in exactly one surviving relation — such a relation can never be
    // part of a dependency, since nothing can cancel that prime), then run Block
    // Lanczos on the filtered matrix.
    if std::env::var("SIQS_FILTER").is_ok() {
        let mut alive: Vec<bool> = vec![true; rows.len()];
        let mut round = 0usize;
        loop {
            round += 1;
            let mut count = vec![0u32; n_f];
            for (r, cols) in rows.iter().enumerate() {
                if alive[r] {
                    for &c in cols {
                        count[c as usize] += 1;
                    }
                }
            }
            let mut removed = 0usize;
            for (r, cols) in rows.iter().enumerate() {
                if alive[r] && cols.iter().any(|&c| count[c as usize] == 1) {
                    alive[r] = false;
                    removed += 1;
                }
            }
            let live = alive.iter().filter(|&&a| a).count();
            println!("filter round {round}: removed {removed}, {live} remain");
            if removed == 0 {
                break;
            }
        }
        let filtered: Vec<Vec<u32>> = rows
            .iter()
            .zip(&alive)
            .filter(|(_, a)| **a)
            .map(|(r, _)| r.clone())
            .collect();
        let appearing = {
            let mut seen = vec![false; n_f];
            for cols in &filtered {
                for &c in cols {
                    seen[c as usize] = true;
                }
            }
            seen.iter().filter(|&&s| s).count()
        };
        println!(
            "filtered: {} relations, {appearing} appearing primes (surplus {})",
            filtered.len(),
            filtered.len() as i64 - appearing as i64
        );
        for t in 0..num_seeds {
            let seed = 0x5161_7A9F_2C3D_4E5Fu64 ^ t.wrapping_mul(0x9E3779B97F4A7C15);
            let t0 = std::time::Instant::now();
            match block_lanczos(&filtered, n_f, seed) {
                None => println!("seed[{t}]: BREAKDOWN ({:.2?})", t0.elapsed()),
                Some(d) if d.is_empty() => println!("seed[{t}]: EMPTY ({:.2?})", t0.elapsed()),
                Some(d) => {
                    // verify genuineness against the filtered rows
                    let mut bad = 0;
                    for dep in &d {
                        let mut acc = vec![false; n_f];
                        for &r in dep {
                            for &c in &filtered[r] {
                                acc[c as usize] ^= true;
                            }
                        }
                        if acc.iter().any(|&b| b) {
                            bad += 1;
                        }
                    }
                    println!(
                        "seed[{t}]: {} deps ({bad} non-genuine) ({:.2?})",
                        d.len(),
                        t0.elapsed()
                    );
                }
            }
        }
        return;
    }

    for t in 0..num_seeds {
        let seed = 0x5161_7A9F_2C3D_4E5Fu64 ^ t.wrapping_mul(0x9E3779B97F4A7C15);
        match block_lanczos(&rows, n_f, seed) {
            None => println!("seed[{t}]: BREAKDOWN"),
            Some(d) if d.is_empty() => println!("seed[{t}]: EMPTY (0 kernel vectors)"),
            Some(d) => println!("seed[{t}]: {} dependencies", d.len()),
        }
    }
}
