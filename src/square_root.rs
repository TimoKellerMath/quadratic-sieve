use rug::{Complete, Integer};

/// Turns a dependency into a factor. Given relations u_i^2 ≡ v_i (mod n) whose v_i
/// multiply to a square, computes x = prod u_i and y = sqrt(prod v_i) and returns
/// gcd(x + y, n) if it is a proper factor of n.
pub fn find_factor<'a>(
    relations: impl IntoIterator<Item = &'a (Integer, Integer)>,
    n: &Integer,
) -> Option<Integer> {
    let mut x = Integer::from(1);
    let mut y = Integer::from(1);
    let mut v = Integer::from(1);
    for (u, v1) in relations {
        x *= u;
        x %= n;
        // accumulate the square part of the v-product via running gcds, so the
        // final y = sqrt(prod v) stays reduced
        let d = v1.gcd_ref(&v).complete();
        v = v.div_exact(&d) * v1.div_exact_ref(&d).complete();
        y *= d;
        y %= n;
    }
    debug_assert!(v.is_perfect_square());
    y *= v.sqrt();
    y %= n;
    let gcd = n.gcd_ref(&(&x + &y).complete()).complete();
    if gcd != 1 && gcd != *n {
        return Some(gcd);
    }
    debug_assert!((x.clone().square() - y.clone().square()).is_divisible(n));
    None
}
