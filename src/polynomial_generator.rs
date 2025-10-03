use rug::Integer;
use std::fmt::Debug;

#[derive(Debug)]
pub struct Polynomial {
    pub a: Integer,
    pub b: Integer,
    pub c: Integer,
    pub q_inverse: Integer,
}
