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

    for t in 0..num_seeds {
        let seed = 0x5161_7A9F_2C3D_4E5Fu64 ^ t.wrapping_mul(0x9E3779B97F4A7C15);
        match block_lanczos(&rows, n_f, seed) {
            None => println!("seed[{t}]: BREAKDOWN"),
            Some(d) if d.is_empty() => println!("seed[{t}]: EMPTY (0 kernel vectors)"),
            Some(d) => println!("seed[{t}]: {} dependencies", d.len()),
        }
    }
}
