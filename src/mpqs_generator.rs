use rug::{Complete, Integer};
use rug::ops::DivRounding;
use crate::polynomial_generator::*;
use crate::number_theory::square_root_mod_p2;

pub struct MPQSPolynomialGenerator<'a> {
    n: &'a Integer,
    factorbase: &'a Vec<i64>,
    root_discs: &'a Vec<i64>, // the roots of n modulo the primes in the factor base
    pairs_of_roots: Vec<Option<(i64,i64)>>,
    qs: Vec<Integer>,
    current_q_max: Integer,
    pub num_polynomials: Vec<usize>,
    num_threads: usize,
}

impl<'a> MPQSPolynomialGenerator<'a> {
    pub fn new(n: &'a Integer, sieve_interval_length: u64, num_threads: usize, factorbase: &'a Vec<i64>, root_discs: &'a Vec<i64>) -> MPQSPolynomialGenerator<'a> {
        MPQSPolynomialGenerator {
            n,
            factorbase,
            pairs_of_roots: Vec::<Option<(i64,i64)>>::with_capacity(root_discs.len()),
            root_discs,
            // qs is a vector of q's with qs[(num_threads) * i + (index_thread)]
            // always enlarge it such that it has (num_threads) * i elements
            qs: Vec::<Integer>::new(),
            // the starting value of q for a: sqrt{2n}/(sieve size)
            // hence its square root for q
            current_q_max: (n * Integer::from(2))
                .sqrt()
                .div_floor(sieve_interval_length)
                .sqrt()
                .next_prime(),
            num_threads,
            num_polynomials: vec![0_usize; num_threads],
        }
    }
}

impl PolynomialGenerator for MPQSPolynomialGenerator<'_> {
    fn next_polynomial(
        &mut self,
        index_thread: usize,
    ) -> (Polynomial, &Vec<Option<(i64,i64)>>) {
        // atomic
        let num_polynomial = self.num_polynomials[index_thread];
        if self.qs.len() < self.num_threads * (num_polynomial + 1) {
            for _ in 0..self.num_threads {
                let q = {
                    while self.n.legendre(&self.current_q_max) != 1 {
                        self.current_q_max = self.current_q_max.clone().next_prime();
                    }
                    let q = self.current_q_max.clone();
                    self.current_q_max = self.current_q_max.clone().next_prime();
                    q
                };
                self.qs.push(q);
            }
        }
        // generate coefficients (a,b,c) of polynomial with a = p^2 for quadratic sieve
        // a = p^2
        // b = 2 sqrt(n) (mod a)
        // c = (b^2 - n)/a
        // discriminant = (2b)^2 - 4(b^2 - n) = 4n
        let q = &self.qs[num_polynomial * self.num_threads + index_thread];
        let a = q.square_ref().complete();
        let b = square_root_mod_p2(self.n, q).unwrap();
        let c = (b.square_ref().complete() - self.n).div_exact(&a);
        debug_assert_eq!(b.clone().square() - a.clone() * c.clone(), *self.n);
        let q_inverse_mod_n = q.invert_ref(self.n).unwrap().complete();
        let pairs_of_roots: Vec<Option<(i64, i64)>> = self.root_discs.iter().zip(self.factorbase.iter())
            .map(|(root_disc, p)|
                if *p > 2 && let Ok(a_inverse_) = a.clone().invert(&Integer::from(*p)) {
                    let a_inverse = a_inverse_.to_i64().unwrap();
                    let b_mod_p = (b.clone() % p).to_i64().unwrap();
                    let root1 = ((root_disc - b_mod_p) * a_inverse) % p;
                    let root2 = ((-root_disc - b_mod_p) * a_inverse) % p;
                    Some((root1, root2))
                }
                else {
                    None
                }
            ).collect();
        self.pairs_of_roots = pairs_of_roots;

        self.num_polynomials[index_thread] += 1;
        (Polynomial{a, b, c, q_inverse: q_inverse_mod_n}, &self.pairs_of_roots)
    }
}