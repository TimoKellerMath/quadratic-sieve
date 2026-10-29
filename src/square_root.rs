use log::debug;
use rug::{Complete, Integer};

/// Turns a dependency into a factor. Given relations u_i^2 ≡ v_i (mod n) whose v_i
/// multiply to a square, computes x = prod u_i and y = sqrt(prod v_i) and returns
/// gcd(x + y, n) if it is a proper factor of n.
pub fn find_factor<'a>(
    relations: impl IntoIterator<Item = &'a (Integer, Integer)>,
    n: &Integer,
) -> Option<Integer> {
    let mut x = Integer::from(1);
    let mut vs = Vec::new();
    for (u, v) in relations {
        x *= u;
        x %= n;
        vs.push(v);
    }
    // the product of the v by a product tree: it multiplies numbers of similar
    // size, for which GMP has fast algorithms, where a running product of
    // millions of bits would take quadratic time
    let v = product(&vs);
    debug!(
        "dependency of {} relations, product of their v: {} bits",
        vs.len(),
        v.significant_bits()
    );
    debug_assert!(v.is_perfect_square());
    let y = v.sqrt() % n;
    let gcd = n.gcd_ref(&(&x + &y).complete()).complete();
    if gcd != 1 && gcd != *n {
        return Some(gcd);
    }
    debug_assert!((x.clone().square() - y.clone().square()).is_divisible(n));
    None
}

/// The product of `factors`, by halves.
fn product(factors: &[&Integer]) -> Integer {
    match factors {
        [] => Integer::from(1),
        [factor] => (*factor).clone(),
        _ => {
            let (left, right) = factors.split_at(factors.len() / 2);
            product(left) * product(right)
        }
    }
}
