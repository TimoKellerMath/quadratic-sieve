use rug::Integer;
use std::fmt::Debug;

/// A sieving polynomial Q(x) = a x^2 + 2 b x + c.
///
/// `a` and `q_inverse` are constant across the whole self-initialized set of
/// 2^(s-1) polynomials sharing one `a`, so they are borrowed from the generator
/// rather than cloned on every polynomial; only `b` and `c` change.
#[derive(Debug)]
pub struct Polynomial<'a> {
    pub a: &'a Integer,
    pub b: Integer,
    pub c: Integer,
    pub q_inverse: &'a Integer,
}
