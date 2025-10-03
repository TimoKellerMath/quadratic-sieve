use rug::Integer;

use crate::number_theory::square_root_mod_p;

// compute factor base for n with size size
pub fn make_factorbase(n: &Integer, size: usize) -> Vec<i64> {
    let mut factorbase = Vec::with_capacity(size); // we know how many elements our result will have
    factorbase.push(-1);
    factorbase.push(2);
    let mut p = Integer::from(2);
    for _ in 2..size {
        p = p.next_prime();
        while n.legendre(&p) != 1 {
            // note that the discriminant of our polynomials will be n
            p = p.next_prime();
        }
        factorbase.push(p.to_i64().unwrap());
    }
    factorbase
}

pub const SCALE_LOGS: f64 = 1024.0; // compute log_2(p) * SCALE_LOGS insteaf of log_2(p), so we can work with rounded logs, i.e., u32's

// compute log(scale * p) for p in the factor base
pub fn compute_logs(factorbase: &[i64]) -> Vec<u32> {
    let mut logs = Vec::with_capacity(factorbase.len()); // we know how many elements our result will have
    for (i, p) in factorbase.iter().enumerate() {
        if i == 0 {
            logs.push(0); // log_2|-1|
            continue;
        }
        logs.push(((*p as f64).log2() * SCALE_LOGS).round() as u32); // round to nearest
    }
    logs
}

// compute the sqrt(n) (mod p) for p in the factor base
pub fn square_roots_mod_factorbase(n: &Integer, factorbase: &[i64]) -> Vec<i64> {
    let mut square_roots = Vec::with_capacity(factorbase.len()); // we know how many elements our result will have
    square_roots.push(0); // p = -1
    square_roots.push(1); // p = 2
    for p in factorbase.iter().skip(2) {
        // skip 1, 2
        square_roots.push(
            square_root_mod_p(n, &Integer::from(*p))
                .unwrap()
                .to_i64()
                .unwrap(),
        );
    }
    square_roots
}
