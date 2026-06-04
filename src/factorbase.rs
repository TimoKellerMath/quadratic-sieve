use rug::Integer;
use crate::number_theory::square_root_mod_p;

// compute factor base for n with size size
pub fn make_factorbase(n: &Integer, size: usize) -> Vec<u32> {
    let mut factorbase = Vec::with_capacity(size); // we know how many elements our result will have
    factorbase.push(0); // 0 stands for -1
    factorbase.push(2);
    let mut p = Integer::from(2);
    for _ in 2..size {
        p = p.next_prime();
        while n.legendre(&p) != 1 {
            // note that the discriminant of our polynomials will be n
            p = p.next_prime();
        }
        factorbase.push(p.to_u32().unwrap());
    }
    factorbase
}

// Precompute a Barrett reciprocal m = floor(2^64 / p) for each factor-base prime,
// so the resieve step can compute `x mod p` with a multiply+shift instead of a
// hardware division (see `x_mod_p` in relations.rs). Entries for the -1 / sentinel
// slot (p < 2) are 0 and never used: the resieve only touches indices >=
// NUM_SKIP_PRIMES, where every prime is well above 2.
pub fn compute_reciprocals(factorbase: &[u32]) -> Vec<u64> {
    factorbase
        .iter()
        .map(|&p| {
            if p >= 2 {
                ((1u128 << 64) / p as u128) as u64
            } else {
                0
            }
        })
        .collect()
}

// compute rounded log_2(p) as u8 for p in the factor base
pub fn compute_logs(factorbase: &[u32]) -> Vec<u8> {
    std::iter::once(0u8) // log_2|-1|
        .chain(
            factorbase
                .iter()
                .skip(1)
                .map(|&p| (p as f32).log2().round() as u8),
        )
        .collect()
}

// compute the sqrt(n) (mod p) for p in the factor base
pub fn square_roots_mod_factorbase(n: &Integer, factorbase: &[u32]) -> Vec<u32> {
    let mut square_roots = Vec::with_capacity(factorbase.len()); // we know how many elements our result will have
    square_roots.push(0); // p = -1
    square_roots.push(1); // p = 2
    for p in factorbase.iter().skip(2) {
        // skip 1, 2
        square_roots.push(
            square_root_mod_p(n, &Integer::from(*p))
                .unwrap()
                .to_u32()
                .unwrap(),
        );
    }
    square_roots
}
