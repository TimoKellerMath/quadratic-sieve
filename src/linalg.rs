//! Linear-algebra phase: collect relations as a sparse GF(2) matrix and solve for
//! dependencies (subsets of relations whose product over the factor base is a
//! square). This module is the batch counterpart to the incremental Gaussian
//! elimination in [`crate::relations::Relations`], and the staging ground for a
//! future Block Lanczos solver.
//!
//! [`dense_left_null_space`] is a straightforward dense GF(2) elimination. It is
//! O(R · F · R / 64) and meant as a correctness *oracle* — a reference the eventual
//! Block Lanczos implementation must agree with — not as the production solver.

use fixedbitset::FixedBitSet;
use rayon::prelude::*;
use rug::{Complete, Integer};

/// Relations stored sparsely for the batch linear-algebra phase: each relation keeps
/// only the factor-base column indices with odd exponent (its GF(2) row), together
/// with the `(u, v)` pair needed to recover a factor from a dependency, where
/// `u^2 ≡ v (mod n)`.
///
/// This is the sparse replacement for the dense per-relation `FixedBitSet` rows used
/// during sieving: a row of average weight `w` costs `w` `u32`s instead of `F/8`
/// bytes, which is the difference between a few MB and ~1 GB at the largest sizes.
pub struct SparseRelations {
    num_columns: usize,
    rows: Vec<Vec<u32>>,
    uvs: Vec<(Integer, Integer)>,
}

impl SparseRelations {
    pub fn new(num_columns: usize) -> SparseRelations {
        SparseRelations {
            num_columns,
            rows: Vec::new(),
            uvs: Vec::new(),
        }
    }

    /// Append a full relation given as the set of factor-base columns with odd
    /// exponent (a `FixedBitSet` over the factor base, as produced during sieving)
    /// together with its `(u, v)`.
    pub fn push(&mut self, relation: &FixedBitSet, uv: (Integer, Integer)) {
        debug_assert!(relation.len() <= self.num_columns);
        self.rows.push(relation.ones().map(|c| c as u32).collect());
        self.uvs.push(uv);
    }

    /// Append a relation already in sparse column form.
    pub fn push_sparse(&mut self, columns: Vec<u32>, uv: (Integer, Integer)) {
        debug_assert!(columns.iter().all(|&c| (c as usize) < self.num_columns));
        self.rows.push(columns);
        self.uvs.push(uv);
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn num_columns(&self) -> usize {
        self.num_columns
    }

    pub fn rows(&self) -> &[Vec<u32>] {
        &self.rows
    }

    /// Debug check: do the rows in `dependency` XOR to the zero vector (i.e. is it a
    /// genuine factor-base parity dependency)?
    pub fn dependency_xor_is_zero(&self, dependency: &[usize]) -> bool {
        let mut acc = vec![false; self.num_columns];
        for &j in dependency {
            for &c in &self.rows[j] {
                acc[c as usize] ^= true;
            }
        }
        acc.iter().all(|&b| !b)
    }

    /// A basis of the left null space over GF(2): every returned entry is a set of
    /// relation indices whose rows XOR to the zero vector (i.e. the product of their
    /// `v`s is a perfect square). Uses the dense reference solver.
    pub fn dependencies(&self) -> Vec<Vec<usize>> {
        dense_left_null_space(&self.rows, self.num_columns)
    }

    /// Recover a factor of `n` from one dependency (a subset of relation indices),
    /// or `None` if it yields a trivial gcd. Mirrors
    /// [`crate::relations::Relations::find_factor`].
    pub fn find_factor(&self, dependency: &[usize], n: &Integer) -> Option<Integer> {
        let mut x = Integer::from(1);
        let mut y = Integer::from(1);
        let mut v = Integer::from(1);
        for &j in dependency {
            let u = &self.uvs[j].0;
            let v1 = &self.uvs[j].1;
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
}

/// XOR row `src` into row `dst` (`src < dst`) of a `&mut [FixedBitSet]`, taking the
/// two disjoint borrows the borrow checker needs.
#[inline]
fn xor_row_into(rows: &mut [FixedBitSet], dst: usize, src: usize) {
    debug_assert!(src < dst);
    let (head, tail) = rows.split_at_mut(dst);
    tail[0] ^= &head[src];
}

/// Dense GF(2) left null-space basis.
///
/// Given `rows` over `num_columns` factor-base columns, returns every independent
/// subset of row indices whose rows XOR to the zero vector. The number returned is
/// exactly `rows.len() - rank`.
///
/// Each working row carries a `num_columns`-bit column part and a `rows.len()`-bit
/// tracking part recording which original rows have been combined into it (the same
/// device as `Relations::indices`). Rows are reduced against registered pivots until
/// they either acquire a fresh pivot column or vanish; a vanished column part means
/// the tracking part is a dependency. Pivot rows, once registered, are never modified
/// and their lowest set column is their pivot column, so each reduction strictly
/// raises a row's lowest set column — guaranteeing termination.
pub fn dense_left_null_space(rows: &[Vec<u32>], num_columns: usize) -> Vec<Vec<usize>> {
    let num_rows = rows.len();
    // column parts
    let mut work: Vec<FixedBitSet> = rows
        .iter()
        .map(|cols| {
            let mut bs = FixedBitSet::with_capacity(num_columns);
            for &c in cols {
                bs.insert(c as usize);
            }
            bs
        })
        .collect();
    // tracking parts, initialised to the identity
    let mut track: Vec<FixedBitSet> = (0..num_rows)
        .map(|i| {
            let mut bs = FixedBitSet::with_capacity(num_rows);
            bs.insert(i);
            bs
        })
        .collect();
    // pivot_row[c] = the row that owns column c as its pivot, if any
    let mut pivot_row: Vec<Option<usize>> = vec![None; num_columns];
    let mut dependencies: Vec<Vec<usize>> = Vec::new();

    for r in 0..num_rows {
        loop {
            // lowest still-set column of the column part
            match work[r].ones().next() {
                None => {
                    // column part is zero: the tracking part is a dependency
                    dependencies.push(track[r].ones().collect());
                    break;
                }
                Some(c) => match pivot_row[c] {
                    Some(pr) => {
                        // eliminate column c using its pivot row (pr < r)
                        xor_row_into(&mut work, r, pr);
                        xor_row_into(&mut track, r, pr);
                    }
                    None => {
                        // r becomes the pivot for column c
                        pivot_row[c] = Some(r);
                        break;
                    }
                },
            }
        }
    }
    dependencies
}

// ===========================================================================
// Block Lanczos over GF(2) (Montgomery 1995).
//
// Finds vectors in the kernel of the relation matrix B (a 64-wide block at a time),
// i.e. subsets of relations whose rows XOR to zero — the same output as
// `dense_left_null_space`, but in O(weight · #relations / 64) per iteration instead
// of the dense O(R²·F/64). Ported from the reference implementation at
// github.com/SebWouters/blanczos (the recurrence and the selection/`invert` step in
// particular are transcribed directly to avoid sign mistakes).
// That code is Copyright (c) 2020, Sebastian Wouters, under the BSD 3-Clause
// License; see LICENSE.
//
// Orientation: the matrix is B with `num_columns` rows (primes) and `R = rows.len()`
// columns (relations). `mul_regular` applies B (relations -> primes), `mul_transpose`
// applies Bᵀ (primes -> relations), and the symmetric operator A = BᵀB acts on
// length-R blocks. The kernel of B is extracted from the final (X, V0) blocks.
// ===========================================================================

type Mat = [u64; 64];

// out_r = Bᵀ * in_f : out[r] = XOR over primes p in relation r of in[p]
fn mul_transpose(rows: &[Vec<u32>], in_f: &[u64], out_r: &mut [u64]) {
    for (r, cols) in rows.iter().enumerate() {
        let mut acc = 0u64;
        for &p in cols {
            acc ^= in_f[p as usize];
        }
        out_r[r] = acc;
    }
}

// result = leftᵀ · right (a 64×64 matrix), for two equal-length N×64 blocks.
// result[i] holds row i; bit j is sum_k left[k][i]·right[k][j].
fn dot(left: &[u64], right: &[u64], result: &mut Mat) {
    *result = [0u64; 64];
    for m in 0..64u32 {
        let mut value = 0u64;
        for k in 0..left.len() {
            value ^= (left[k] << m) & right[k];
        }
        for i in 0..(64 - m) {
            result[i as usize] |= value & (1u64 << (i + m));
        }
    }
    for m in 1..64u32 {
        let mut value = 0u64;
        for k in 0..left.len() {
            value ^= (left[k] >> m) & right[k];
        }
        for i in 0..(64 - m) {
            result[(i + m) as usize] |= value & (1u64 << i);
        }
    }
}

// result = left · right, where right is a 64×64 matrix and left is N×64 (or 64×64).
fn mul(left: &[u64], right: &Mat, result: &mut [u64]) {
    for idx in 0..left.len() {
        let mut bits = left[idx];
        let mut acc = 0u64;
        while bits != 0 {
            let b = bits.trailing_zeros() as usize;
            acc ^= right[b];
            bits &= bits - 1;
        }
        result[idx] = acc;
    }
}

// Below the parallel block ops fall back to serial: the rayon split + join overhead
// isn't worth it for short vectors (and the small 64×64 `mul`/`dot` calls).
const PAR_THRESHOLD: usize = 4096;

// Parallel `mul_regular` over a column-major transpose index `cols_to_rows`, where
// cols_to_rows[p] lists the relations containing prime p. Each output prime is an
// independent XOR-reduction, so there is no write contention (unlike scattering over
// the row-major `rows`, which would need per-thread accumulators).
fn mul_regular_par(cols_to_rows: &[Vec<u32>], in_r: &[u64], out_f: &mut [u64]) {
    if cols_to_rows.len() < PAR_THRESHOLD {
        for (rs, o) in cols_to_rows.iter().zip(out_f.iter_mut()) {
            let mut acc = 0u64;
            for &r in rs {
                acc ^= in_r[r as usize];
            }
            *o = acc;
        }
        return;
    }
    out_f
        .par_iter_mut()
        .zip(cols_to_rows.par_iter())
        .for_each(|(o, rs)| {
            let mut acc = 0u64;
            for &r in rs {
                acc ^= in_r[r as usize];
            }
            *o = acc;
        });
}

// Parallel `mul_transpose`: each output relation is an independent XOR-reduction.
fn mul_transpose_par(rows: &[Vec<u32>], in_f: &[u64], out_r: &mut [u64]) {
    if rows.len() < PAR_THRESHOLD {
        mul_transpose(rows, in_f, out_r);
        return;
    }
    out_r
        .par_iter_mut()
        .zip(rows.par_iter())
        .for_each(|(o, cols)| {
            let mut acc = 0u64;
            for &p in cols {
                acc ^= in_f[p as usize];
            }
            *o = acc;
        });
}

// Parallel `dot`: the result is XOR_k outer(left[k], right[k]); chunk over k, dot each
// chunk serially, and XOR-combine the partial 64×64 matrices. Associativity of XOR
// makes this bit-identical to the serial `dot` regardless of chunking or thread count.
fn dot_par(left: &[u64], right: &[u64], result: &mut Mat) {
    if left.len() < PAR_THRESHOLD {
        dot(left, right, result);
        return;
    }
    const CHUNK: usize = 2048;
    *result = left
        .par_chunks(CHUNK)
        .zip(right.par_chunks(CHUNK))
        .map(|(l, r)| {
            let mut m = [0u64; 64];
            dot(l, r, &mut m);
            m
        })
        .reduce(
            || [0u64; 64],
            |mut a, b| {
                for i in 0..64 {
                    a[i] ^= b[i];
                }
                a
            },
        );
}

// Parallel `mul` where `right` is 64×64: each output row is independent.
fn mul_par(left: &[u64], right: &Mat, result: &mut [u64]) {
    if left.len() < PAR_THRESHOLD {
        mul(left, right, result);
        return;
    }
    result
        .par_iter_mut()
        .zip(left.par_iter())
        .for_each(|(o, &l)| {
            let mut bits = l;
            let mut acc = 0u64;
            while bits != 0 {
                let b = bits.trailing_zeros() as usize;
                acc ^= right[b];
                bits &= bits - 1;
            }
            *o = acc;
        });
}

// result = left ^ right
fn rox(left: &[u64], right: &[u64], result: &mut [u64]) {
    for i in 0..left.len() {
        result[i] = left[i] ^ right[i];
    }
}

// dst ^= src
fn xor_assign(dst: &mut [u64], src: &[u64]) {
    for i in 0..dst.len() {
        dst[i] ^= src[i];
    }
}

// mx += identity
fn plus1(mx: &mut Mat) {
    for (i, e) in mx.iter_mut().enumerate() {
        *e ^= 1u64 << i;
    }
}

fn and_mask(x: &mut [u64], mask: u64) {
    for e in x.iter_mut() {
        *e &= mask;
    }
}

fn nonzero(x: &[u64]) -> bool {
    x.iter().any(|&e| e != 0)
}

fn nonzero_masked(x: &[u64], mask: u64) -> bool {
    x.iter().any(|&e| e & mask != 0)
}

// Invert the largest invertible principal submatrix of the symmetric `t` = Vᵢᵀ A Vᵢ,
// writing the (masked) inverse into `right` and using `left` as scratch. Columns NOT
// selected in the previous iteration (mask bit 0) get pivot priority, so every column
// is selected within two consecutive iterations. Returns the new selection mask.
fn invert(t: &Mat, mask: u64, left: &mut Mat, right: &mut Mat) -> u64 {
    // ordering: previously-selected columns (mask bit set) go to the tail
    let mut c = [0u32; 64];
    let mut head = 0usize;
    let mut tail = 63usize;
    for bit in 0..64usize {
        if (mask >> bit) & 1 == 1 {
            c[tail] = bit as u32;
            tail = tail.wrapping_sub(1);
        } else {
            c[head] = bit as u32;
            head += 1;
        }
    }
    let mut newmask = 0u64;
    *left = *t;
    for (i, e) in right.iter_mut().enumerate() {
        *e = 1u64 << i;
    }
    for j in 0..64usize {
        let cj = c[j] as usize;
        let mut k = j;
        while k < 64 && ((left[c[k] as usize] >> cj) & 1) == 0 {
            k += 1;
        }
        if k != 64 {
            if k != j {
                left.swap(cj, c[k] as usize);
                right.swap(cj, c[k] as usize);
            }
            newmask |= 1u64 << cj;
            for row in 0..64 {
                if row != cj && ((left[row] >> cj) & 1) == 1 {
                    left[row] ^= left[cj];
                    right[row] ^= right[cj];
                }
            }
        } else {
            let mut k = j;
            while k < 64 && ((right[c[k] as usize] >> cj) & 1) == 0 {
                k += 1;
            }
            if k < 64 && k != j {
                left.swap(cj, c[k] as usize);
                right.swap(cj, c[k] as usize);
            }
            for row in 0..64 {
                if row != cj && ((right[row] >> cj) & 1) == 1 {
                    left[row] ^= left[cj];
                    right[row] ^= right[cj];
                }
            }
            left[cj] = 0;
            right[cj] = 0;
        }
    }
    for i in 0..64 {
        if (newmask >> i) & 1 == 0 {
            right[i] = 0;
        }
    }
    for e in right.iter_mut() {
        *e &= newmask;
    }
    newmask
}

// Final null-space extraction: among the 128 candidate vectors [vec1 | vec2] (X and
// the last V block), find combinations whose image under B ([bvec1 | bvec2]) is zero,
// then pack up to 64 nonzero kernel vectors. Returns (count, packed result over R).
fn elimination(bvec1: &[u64], bvec2: &[u64], vec1: &[u64], vec2: &[u64]) -> (u32, Vec<u64>) {
    let zrows = bvec1.len();
    let zcols = vec1.len();
    let zsize = zrows.max(zcols);
    const ZVECS: usize = 128;
    let mut vectors = vec![0u8; zsize * ZVECS];
    let mut solution = vec![0u8; ZVECS * ZVECS];
    for vec in 0..ZVECS {
        for row in 0..zrows {
            let bit = if vec < 64 {
                (bvec1[row] >> vec) & 1
            } else {
                (bvec2[row] >> (vec - 64)) & 1
            };
            vectors[row + zrows * vec] = bit as u8;
        }
        solution[vec + ZVECS * vec] = 1;
    }
    let mut solindex = 0usize;
    for row in 0..zrows {
        let mut search = solindex;
        while search < ZVECS && vectors[row + zrows * search] == 0 {
            search += 1;
        }
        if search != ZVECS {
            if search != solindex {
                for idx in row..zrows {
                    vectors.swap(idx + zrows * solindex, idx + zrows * search);
                }
                for vec in 0..ZVECS {
                    solution.swap(vec + ZVECS * solindex, vec + ZVECS * search);
                }
            }
            for sol in (solindex + 1)..ZVECS {
                if vectors[row + zrows * sol] != 0 {
                    for idx in row..zrows {
                        vectors[idx + zrows * sol] ^= vectors[idx + zrows * solindex];
                    }
                    for vec in 0..ZVECS {
                        solution[vec + ZVECS * sol] ^= solution[vec + ZVECS * solindex];
                    }
                }
            }
            solindex += 1;
        }
    }
    for e in vectors.iter_mut() {
        *e = 0;
    }
    for sol in solindex..ZVECS {
        for vec in 0..ZVECS {
            if solution[vec + ZVECS * sol] != 0 {
                for col in 0..zcols {
                    let bit = if vec < 64 {
                        (vec1[col] >> vec) & 1
                    } else {
                        (vec2[col] >> (vec - 64)) & 1
                    };
                    vectors[col + zcols * sol] ^= bit as u8;
                }
            }
        }
    }
    let mut nsols = 0u32;
    let mut result = vec![0u64; zcols];
    for vec in 0..ZVECS {
        let mut use_it = false;
        for col in 0..zcols {
            if vectors[col + zcols * vec] != 0 {
                use_it = nsols < 64;
                break;
            }
        }
        if use_it {
            for col in 0..zcols {
                result[col] |= (vectors[col + zcols * vec] as u64) << nsols;
            }
            nsols += 1;
        }
    }
    (nsols, result)
}

// column-major transpose index for the parallel `mul_regular`: cols_to_rows[p] is the
// list of relations containing prime p.
fn build_transpose(rows: &[Vec<u32>], n_f: usize) -> Vec<Vec<u32>> {
    let mut cols_to_rows: Vec<Vec<u32>> = vec![Vec::new(); n_f];
    for (r, cols) in rows.iter().enumerate() {
        for &p in cols {
            cols_to_rows[p as usize].push(r as u32);
        }
    }
    cols_to_rows
}

// Run the Block Lanczos iteration and return the raw blocks (X, V0), each a length-n_r
// array of 64-bit columns. `A·X = 0` (X spans up to 64 vectors of ker(A)). Returns
// None on the inner breakdown.
fn lanczos_iterate(
    rows: &[Vec<u32>],
    cols_to_rows: &[Vec<u32>],
    n_r: usize,
    n_f: usize,
    seed: u64,
) -> Option<(Vec<u64>, Vec<u64>)> {
    // xorshift RNG for the random starting block Y (stored in `x`)
    let mut state = seed ^ 0x9E3779B97F4A7C15u64 ^ (n_r as u64).wrapping_mul(0x100000001B3);
    let mut rng = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };

    let mut x: Vec<u64> = (0..n_r).map(|_| rng()).collect();
    let mut q = vec![0u64; n_r];
    let mut v0 = vec![0u64; n_r];
    let mut v1 = vec![0u64; n_r];
    let mut v2 = vec![0u64; n_r];
    let mut av0 = vec![0u64; n_r];
    let mut ntmp = vec![0u64; n_r];
    let mut workv = vec![0u64; n_r];
    let mut work1 = vec![0u64; n_f];

    // init: Q = A·Y ; V0 = Q ; AV0 = A·V0 ; T0 = V0ᵀ A V0
    mul_regular_par(cols_to_rows, &x, &mut work1);
    mul_transpose_par(rows, &work1, &mut q);
    v0.copy_from_slice(&q);
    mul_regular_par(cols_to_rows, &v0, &mut work1);
    mul_transpose_par(rows, &work1, &mut av0);
    let mut t0 = [0u64; 64];
    dot_par(&v0, &av0, &mut t0);

    let mut t1 = [0u64; 64];
    let mut w0i = [0u64; 64];
    let mut w1i = [0u64; 64];
    let mut w2i = [0u64; 64];
    let mut g = [0u64; 64];
    let mut d = [0u64; 64];
    let mut e = [0u64; 64];
    let mut f = [0u64; 64];
    let mut left = [0u64; 64];
    let mut mask = u64::MAX;

    // env-gated diagnostic: sum of selected columns per iteration = rank(A), so
    // n_r - rank(A) = dim ker(A) — the quantity that decides whether a 64-wide
    // block can capture the kernel at all.
    let debug = std::env::var("SIQS_BL_DEBUG").is_ok();
    let mut rank_a = 0usize;

    while nonzero(&t0) {
        let mask_prev = mask;
        mask = invert(&t0, mask, &mut left, &mut w0i);
        rank_a += mask.count_ones() as usize;
        let unselected = !(mask | mask_prev);
        if unselected != 0 && nonzero_masked(&v1, unselected) {
            // inner breakdown: columns in neither Sᵢ nor Sᵢ₋₁ but V₍ᵢ₋₁₎ nonzero there
            return None;
        }

        // X += V0 · (W0i · (V0ᵀ Q))      (solution accumulation, eq. 20)
        dot_par(&v0, &q, &mut d);
        mul(&w0i, &d, &mut e);
        mul_par(&v0, &e, &mut ntmp);
        xor_assign(&mut x, &ntmp);

        // F coefficient (eq. 19): F = W2i·(T1·W1i + I)·G_prev, masked
        mul(&t1, &w1i, &mut d);
        plus1(&mut d);
        mul(&w2i, &d, &mut e);
        mul(&e, &g, &mut f);
        and_mask(&mut f, mask);

        // E coefficient (eq. 19): E = W1i·T0, masked
        mul(&w1i, &t0, &mut e);
        and_mask(&mut e, mask);

        // G for the next iteration: G = (V0ᵀ A² V0 masked) ^ T0
        dot_par(&av0, &av0, &mut d);
        and_mask(&mut d, mask);
        rox(&d, &t0, &mut g);

        // D coefficient (eq. 19): D = W0i·G + I
        mul(&w0i, &g, &mut d);
        plus1(&mut d);

        // V_{i+1} = (A V0)·Sᵢ + V0·D + V1·E + V2·F      (eq. 18) -> ntmp
        and_mask(&mut av0, mask);
        mul_par(&v0, &d, &mut workv);
        rox(&av0, &workv, &mut ntmp);
        mul_par(&v1, &e, &mut workv);
        xor_assign(&mut ntmp, &workv);
        mul_par(&v2, &f, &mut workv);
        xor_assign(&mut ntmp, &workv);

        // rotate the V history and recompute A·V0
        std::mem::swap(&mut v2, &mut v1);
        std::mem::swap(&mut v1, &mut v0);
        std::mem::swap(&mut v0, &mut ntmp);
        mul_regular_par(cols_to_rows, &v0, &mut work1);
        mul_transpose_par(rows, &work1, &mut av0);

        // rotate the Winv and T history, recompute T0
        std::mem::swap(&mut w2i, &mut w1i);
        std::mem::swap(&mut w1i, &mut w0i);
        std::mem::swap(&mut t1, &mut t0);
        dot_par(&v0, &av0, &mut t0);
    }
    if debug {
        eprintln!(
            "[bl-debug] n_r={n_r} rank(A)={rank_a} dim_ker(A)={}",
            n_r - rank_a
        );
    }
    Some((x, v0))
}

/// Block Lanczos over GF(2): returns a set of dependencies (each a subset of relation
/// indices whose rows XOR to the zero vector), the same contract as
/// [`dense_left_null_space`]. Up to 64 independent dependencies are returned per call.
///
/// `seed` randomizes the starting block (Montgomery's algorithm is randomized); a
/// fixed seed makes the result reproducible. Returns `None` if the inner breakdown
/// occurs; `Some(deps)` otherwise. Caveat: when `dim ker(BᵀB) > 64` (a large GF(2)
/// isotropic radical), the 64-wide block can land entirely in the isotropic part and
/// the result is empty even though `ker(B)` is nonzero — retries do not help; the
/// matrix needs filtering or a wider block.
pub fn block_lanczos(rows: &[Vec<u32>], num_columns: usize, seed: u64) -> Option<Vec<Vec<usize>>> {
    let n_r = rows.len();
    let n_f = num_columns;
    if n_r == 0 {
        return Some(Vec::new());
    }
    let cols_to_rows = build_transpose(rows, n_f);
    let (x, v0) = lanczos_iterate(rows, &cols_to_rows, n_r, n_f, seed)?;

    // extract kernel vectors of B from [X | V0]
    let mut work1 = vec![0u64; n_f];
    let mut work2 = vec![0u64; n_f];
    mul_regular_par(&cols_to_rows, &x, &mut work1);
    mul_regular_par(&cols_to_rows, &v0, &mut work2);
    let (nsols, result) = elimination(&work1, &work2, &x, &v0);

    let mut deps = Vec::new();
    for s in 0..nsols as usize {
        let dep: Vec<usize> = (0..n_r)
            .filter(|&col| (result[col] >> s) & 1 == 1)
            .collect();
        if !dep.is_empty() {
            deps.push(dep);
        }
    }
    Some(deps)
}

/// Iteratively drop relations containing a prime that appears in exactly one
/// surviving relation. Such a relation can never participate in a dependency — its
/// unique prime has nothing to cancel against — so the left null space is unchanged
/// (inductively, as removals expose new singletons). Returns the indices of the
/// surviving relations.
///
/// This is not just a size optimization: singleton chains are exactly the structure
/// that traps the 64-wide Block Lanczos block in the isotropic radical of BᵀB
/// (observed on a real 31647×32412 QS matrix: unfiltered, every start returned an
/// empty kernel; filtered, every start returned 64 genuine dependencies).
fn filter_singletons(rows: &[Vec<u32>], num_columns: usize) -> Vec<u32> {
    let mut alive = vec![true; rows.len()];
    loop {
        let mut count = vec![0u32; num_columns];
        for (r, cols) in rows.iter().enumerate() {
            if alive[r] {
                for &c in cols {
                    count[c as usize] += 1;
                }
            }
        }
        let mut removed = false;
        for (r, cols) in rows.iter().enumerate() {
            if alive[r] && cols.iter().any(|&c| count[c as usize] == 1) {
                alive[r] = false;
                removed = true;
            }
        }
        if !removed {
            break;
        }
    }
    (0..rows.len() as u32)
        .filter(|&r| alive[r as usize])
        .collect()
}

impl SparseRelations {
    /// Dependencies via Block Lanczos (the production solver). Same contract as
    /// [`SparseRelations::dependencies`] but O(weight·R/64) per iteration instead of
    /// dense O(R²·F/64).
    ///
    /// Block Lanczos is randomized and can break down (or, near the 64-wide block
    /// boundary, fail to capture the kernel) for an unlucky start vector — both are
    /// resolved by retrying with a fresh seed. A nonzero kernel is guaranteed whenever
    /// there are more relations than primes that actually appear (rank ≤ appearing
    /// primes), so an empty result there is always a failure to retry, never a real
    /// answer. After exhausting retries we fall back to the exact dense solver.
    ///
    /// The matrix–block products inside Block Lanczos run on a private rayon pool of
    /// `num_threads` threads (so the solver's parallelism is independent of the global
    /// pool the sieve uses). The GF(2) reductions are associative, so the result is
    /// bit-identical to a single-threaded run with the same seed.
    pub fn dependencies_lanczos(&self, seed: u64, num_threads: usize) -> Vec<Vec<usize>> {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads.max(1))
            .build()
            .expect("failed to build Block Lanczos thread pool");
        pool.install(|| self.dependencies_lanczos_pooled(seed))
    }

    // The filter + retry loop; runs inside whatever rayon pool is installed by the
    // caller.
    fn dependencies_lanczos_pooled(&self, seed: u64) -> Vec<Vec<usize>> {
        // Remove singleton relations first (see filter_singletons): they cannot be
        // part of any dependency, and their chains are what traps the 64-wide block
        // in the isotropic radical, making Lanczos return an empty kernel.
        let keep = filter_singletons(&self.rows, self.num_columns);
        let filtered: Vec<Vec<u32>> = keep
            .iter()
            .map(|&r| self.rows[r as usize].clone())
            .collect();

        // primes that actually occur in the filtered set; rank is bounded by this, so
        // the kernel is nonzero once there are more relations than appearing primes.
        let mut appears = vec![false; self.num_columns];
        for row in &filtered {
            for &c in row {
                appears[c as usize] = true;
            }
        }
        let appearing = appears.iter().filter(|&&a| a).count();
        let kernel_expected = filtered.len() > appearing;

        // map a dependency over the filtered rows back to original relation indices
        let remap = |deps: Vec<Vec<usize>>| -> Vec<Vec<usize>> {
            deps.into_iter()
                .map(|dep| dep.into_iter().map(|i| keep[i] as usize).collect())
                .collect()
        };

        const TRIES: usize = 16;
        let mut breakdowns = 0usize;
        let mut empties = 0usize;
        for t in 0..TRIES as u64 {
            let s = seed ^ t.wrapping_mul(0x9E3779B97F4A7C15);
            match block_lanczos(&filtered, self.num_columns, s) {
                // success: a nonempty kernel was found
                Some(deps) if !deps.is_empty() => {
                    if t > 0 {
                        eprintln!("[lanczos] succeeded on attempt {}/{TRIES}", t + 1);
                    }
                    return remap(deps);
                }
                // completed with an empty kernel and none is expected: genuine
                Some(_) if !kernel_expected => return Vec::new(),
                // completed but empty though a kernel is expected: retry a fresh start
                Some(_) => empties += 1,
                // inner breakdown: retry a fresh start
                None => breakdowns += 1,
            }
        }
        // every attempt failed though a kernel must exist. The dense solver is exact
        // but sequential O(R·F·(R+F)/64) — minutes at scale — so warn loudly and (when
        // SIQS_DUMP_MATRIX is set) dump the matrix so the failure can be reproduced.
        eprintln!(
            "[lanczos] all {TRIES} attempts failed on a {}×{} matrix \
             ({breakdowns} breakdowns, {empties} empty); falling back to the SERIAL \
             dense solver — this is single-threaded and may take many minutes",
            filtered.len(),
            appearing,
        );
        self.dump_matrix_if_requested();
        if kernel_expected {
            return remap(dense_left_null_space(&filtered, self.num_columns));
        }
        Vec::new()
    }

    // If the SIQS_DUMP_MATRIX env var is set, write the sparse rows to that path (one
    // line per relation: space-separated column indices) so a failing Block Lanczos
    // input can be captured and replayed in a test.
    fn dump_matrix_if_requested(&self) {
        let Ok(path) = std::env::var("SIQS_DUMP_MATRIX") else {
            return;
        };
        use std::io::Write as _;
        let mut out = String::new();
        out.push_str(&format!("{} {}\n", self.rows.len(), self.num_columns));
        for row in &self.rows {
            for (i, c) in row.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                out.push_str(&c.to_string());
            }
            out.push('\n');
        }
        match std::fs::File::create(&path).and_then(|mut f| f.write_all(out.as_bytes())) {
            Ok(()) => eprintln!("[lanczos] dumped relation matrix to {path}"),
            Err(e) => eprintln!("[lanczos] failed to dump matrix to {path}: {e}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // deterministic pseudo-random bits
    fn next_rand(seed: &mut u64) -> u64 {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *seed
    }

    // XOR the given rows together (over num_columns) and return whether the result is
    // the zero vector.
    fn rows_xor_to_zero(rows: &[Vec<u32>], subset: &[usize], num_columns: usize) -> bool {
        let mut acc = vec![false; num_columns];
        for &i in subset {
            for &c in &rows[i] {
                acc[c as usize] ^= true;
            }
        }
        acc.iter().all(|&b| !b)
    }

    // rank over GF(2) of a set of {0,1}-vectors given as sorted index lists, computed
    // by an independent reduction (so it can't share a bug with the solver).
    fn gf2_rank(vectors: &[Vec<u32>], num_columns: usize) -> usize {
        let mut basis: Vec<FixedBitSet> = Vec::new();
        for v in vectors {
            let mut bs = FixedBitSet::with_capacity(num_columns);
            for &c in v {
                bs.insert(c as usize);
            }
            // reduce against the current basis (each basis vector keyed by its lowest bit)
            while let Some(lead) = bs.ones().next() {
                if let Some(b) = basis.iter().find(|b| b.ones().next() == Some(lead)) {
                    bs ^= b;
                } else {
                    basis.push(bs);
                    break;
                }
            }
        }
        basis.len()
    }

    #[test]
    fn null_space_of_random_matrices() {
        let mut seed = 0xC0FFEE_u64;
        for &(num_rows, num_columns) in &[(20usize, 12usize), (64, 50), (100, 60), (40, 40)] {
            // random rows, each column set with probability ~1/3
            let rows: Vec<Vec<u32>> = (0..num_rows)
                .map(|_| {
                    (0..num_columns as u32)
                        .filter(|_| next_rand(&mut seed) % 3 == 0)
                        .collect()
                })
                .collect();

            let deps = dense_left_null_space(&rows, num_columns);

            // (a) every dependency is a genuine null vector
            for dep in &deps {
                assert!(
                    !dep.is_empty(),
                    "empty dependency for {num_rows}x{num_columns}"
                );
                assert!(
                    rows_xor_to_zero(&rows, dep, num_columns),
                    "dependency does not XOR to zero for {num_rows}x{num_columns}"
                );
            }

            // (b) the dependencies are linearly independent over GF(2)
            let dep_vectors: Vec<Vec<u32>> = deps
                .iter()
                .map(|d| d.iter().map(|&i| i as u32).collect())
                .collect();
            assert_eq!(
                gf2_rank(&dep_vectors, num_rows),
                deps.len(),
                "dependencies not independent for {num_rows}x{num_columns}"
            );

            // (c) there are exactly num_rows - rank of them => a full null-space basis
            let rank = gf2_rank(&rows, num_columns);
            assert_eq!(
                deps.len(),
                num_rows - rank,
                "wrong nullity for {num_rows}x{num_columns}"
            );
        }
    }

    #[test]
    fn handcrafted_dependency() {
        // rows 0 and 3 are identical, rows 1+2 sum to row 4 -> two clear dependencies.
        let rows = vec![
            vec![0u32, 1],
            vec![1u32, 2],
            vec![2u32, 3],
            vec![0u32, 1], // == row 0
            vec![1u32, 3], // == row1 xor row2
        ];
        let num_columns = 4;
        let deps = dense_left_null_space(&rows, num_columns);
        assert_eq!(deps.len(), rows.len() - gf2_rank(&rows, num_columns));
        for dep in &deps {
            assert!(rows_xor_to_zero(&rows, dep, num_columns));
        }
    }

    // naive leftᵀ·right over GF(2), to validate the bit-twiddled `dot`
    fn naive_dot(left: &[u64], right: &[u64]) -> Mat {
        let mut out = [0u64; 64];
        for i in 0..64 {
            for j in 0..64 {
                let mut bit = 0u64;
                for k in 0..left.len() {
                    bit ^= ((left[k] >> i) & 1) & ((right[k] >> j) & 1);
                }
                if bit != 0 {
                    out[i] |= 1u64 << j;
                }
            }
        }
        out
    }

    // naive left·right where right is 64×64, to validate `mul`
    fn naive_mul(left: &[u64], right: &Mat) -> Vec<u64> {
        let mut out = vec![0u64; left.len()];
        for (idx, &l) in left.iter().enumerate() {
            for j in 0..64 {
                let mut bit = 0u64;
                for b in 0..64 {
                    bit ^= ((l >> b) & 1) & ((right[b] >> j) & 1);
                }
                if bit != 0 {
                    out[idx] |= 1u64 << j;
                }
            }
        }
        out
    }

    #[test]
    fn dot_and_mul_match_naive() {
        let mut seed = 0x5DEECE66Du64;
        let mut rng = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for n in [1usize, 5, 17, 64] {
            let left: Vec<u64> = (0..n).map(|_| rng()).collect();
            let right: Vec<u64> = (0..n).map(|_| rng()).collect();
            let mut got = [0u64; 64];
            dot(&left, &right, &mut got);
            assert_eq!(got, naive_dot(&left, &right), "dot mismatch n={n}");

            let mat: Mat = std::array::from_fn(|_| rng());
            let mut got_mul = vec![0u64; n];
            mul(&left, &mat, &mut got_mul);
            assert_eq!(got_mul, naive_mul(&left, &mat), "mul mismatch n={n}");
        }
    }

    #[test]
    fn block_lanczos_matches_dense_null_space() {
        let mut seed = 0x1357_9BDFu64;
        let mut rng = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for &(n_r, n_f) in &[(70usize, 50usize), (100, 70), (140, 100), (200, 150)] {
            let rows: Vec<Vec<u32>> = (0..n_r)
                .map(|_| (0..n_f as u32).filter(|_| rng() % 3 == 0).collect())
                .collect();

            let nullity = n_r - gf2_rank(&rows, n_f);
            let deps = block_lanczos(&rows, n_f, 0xC0FFEE).expect("block lanczos broke down");

            // every Block Lanczos dependency is a genuine null vector
            for dep in &deps {
                assert!(!dep.is_empty());
                assert!(
                    rows_xor_to_zero(&rows, dep, n_f),
                    "BL dependency not a null vector for {n_r}x{n_f}"
                );
            }
            // and they form a full-rank basis of the kernel (dimension = nullity,
            // since nullity < 64 here so a single block captures all of it)
            let dep_vectors: Vec<Vec<u32>> = deps
                .iter()
                .map(|d| d.iter().map(|&i| i as u32).collect())
                .collect();
            assert_eq!(
                gf2_rank(&dep_vectors, n_r),
                nullity,
                "BL did not recover the full kernel for {n_r}x{n_f}"
            );
        }
    }

    #[test]
    fn block_lanczos_tight_kernel_at_scale() {
        // Reproduce the 251-bit failure: nullity ~= 64 (= block width) at a scale with
        // many iterations. Random full-column-rank matrices with n_r = n_f + 64 have
        // nullity exactly 64. Block Lanczos must still recover a nonzero kernel.
        let mut seed = 0x9E37_79B9u64;
        let mut rng = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        // sparse rows (avg weight ~16, like real relations) keep it fast; random
        // n_r = n_f + 64 over n_f columns is full-column-rank w.h.p. => nullity ~64.
        for &n_f in &[1000usize, 3000, 6000] {
            let n_r = n_f + 64;
            let rows: Vec<Vec<u32>> = (0..n_r)
                .map(|_| {
                    let mut cols: Vec<u32> = (0..16).map(|_| (rng() % n_f as u64) as u32).collect();
                    cols.sort_unstable();
                    cols.dedup();
                    cols
                })
                .collect();
            let deps = block_lanczos(&rows, n_f, 0xC0FFEE).unwrap_or_default();
            for dep in &deps {
                assert!(
                    rows_xor_to_zero(&rows, dep, n_f),
                    "non-genuine dep at n_f={n_f}"
                );
            }
            assert!(!deps.is_empty(), "BL returned no dependencies at n_f={n_f}");
        }
    }

    #[test]
    fn block_lanczos_structured_matrix_seed_dependence() {
        // Mimic a real QS relation matrix: a few very heavy small-prime columns, a
        // long sparse large-prime tail, and a fraction of dense (DLP-combined) rows.
        // Such structure can make a given random start break down; verify the kernel
        // is recoverable by *some* start (the basis for retrying with fresh seeds).
        let mut seed = 0xDEAD_BEEFu64;
        let mut rng = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let n_f = 3000usize;
        let n_r = n_f + 64; // the real 251-bit case had surplus exactly 64 = block width
        let rows: Vec<Vec<u32>> = (0..n_r)
            .map(|i| {
                let mut cols: Vec<u32> = Vec::new();
                // heavy small-prime columns (0..32): present ~half the time
                for c in 0..32u32 {
                    if rng() % 2 == 0 {
                        cols.push(c);
                    }
                }
                // sparse tail, or a dense row every 20th (DLP cycle)
                let weight = if i % 20 == 0 { 60 } else { 12 };
                for _ in 0..weight {
                    cols.push((rng() % n_f as u64) as u32);
                }
                cols.sort_unstable();
                cols.dedup();
                cols
            })
            .collect();

        // try a handful of starts; count how many recover a nonzero kernel
        let mut successes = 0;
        for t in 0..8u64 {
            let s = 0x1234_5678u64 ^ t.wrapping_mul(0x9E3779B97F4A7C15);
            let deps = block_lanczos(&rows, n_f, s).unwrap_or_default();
            for dep in &deps {
                assert!(rows_xor_to_zero(&rows, dep, n_f), "non-genuine dep");
            }
            if !deps.is_empty() {
                successes += 1;
            }
        }
        // the kernel is nonzero (n_r > n_f), so at least one start must find it
        assert!(successes > 0, "no random start recovered the kernel");
        eprintln!("structured matrix: {successes}/8 starts succeeded");
    }

    #[test]
    fn block_lanczos_more_columns_than_relations() {
        // The real QS case: n_f (primes) > n_r (relations), with the kernel coming
        // from linear dependence among the relations (not from a wide matrix shape).
        // All other BL tests have n_r > n_f, so this orientation was untested.
        let mut seed = 0x0BADF00Du64;
        let mut rng = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let n_f = 3000usize;
        let independent = 1950usize;
        let mut rows: Vec<Vec<u32>> = (0..independent)
            .map(|_| {
                let mut cols: Vec<u32> = (0..12).map(|_| (rng() % n_f as u64) as u32).collect();
                cols.sort_unstable();
                cols.dedup();
                cols
            })
            .collect();
        // add 50 rows that are XORs of two earlier rows => 50 forced dependencies
        for _ in 0..50 {
            let a = (rng() % independent as u64) as usize;
            let b = (rng() % independent as u64) as usize;
            let mut acc = vec![false; n_f];
            for &c in &rows[a] {
                acc[c as usize] ^= true;
            }
            for &c in &rows[b] {
                acc[c as usize] ^= true;
            }
            rows.push((0..n_f as u32).filter(|&c| acc[c as usize]).collect());
        }
        let n_r = rows.len();
        assert!(n_f > n_r, "want more columns than relations");
        let nullity = n_r - gf2_rank(&rows, n_f);
        assert!(nullity > 0, "constructed matrix should have a kernel");

        let deps = block_lanczos(&rows, n_f, 0xC0FFEE).unwrap_or_default();
        for dep in &deps {
            assert!(rows_xor_to_zero(&rows, dep, n_f), "non-genuine dep");
        }
        assert!(
            !deps.is_empty(),
            "BL found no kernel for n_f={n_f} > n_r={n_r} (nullity={nullity})"
        );
    }

    #[test]
    fn block_lanczos_high_nullity_returns_genuine_vectors() {
        // Mimic a real relation matrix: many factor-base columns never appear (empty
        // columns => low rank => nullity >> 64), and relations overlap heavily on a
        // small set of columns. BL caps at 64 vectors, but every one it returns must
        // be a genuine kernel vector (rows XOR to zero) and they must be independent.
        let mut seed = 0x2468_ACE0u64;
        let mut rng = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let n_r = 481usize;
        let n_f = 417usize;
        let active = 40usize; // only the first `active` columns are ever set
        let rows: Vec<Vec<u32>> = (0..n_r)
            .map(|_| {
                let mut cols: Vec<u32> = (0..active as u32).filter(|_| rng() % 4 == 0).collect();
                cols.sort_unstable();
                cols.dedup();
                cols
            })
            .collect();

        let nullity = n_r - gf2_rank(&rows, n_f);
        assert!(nullity > 64, "expected high nullity, got {nullity}");

        let deps = block_lanczos(&rows, n_f, 0xBADC0DE).expect("block lanczos broke down");
        assert!(!deps.is_empty(), "BL returned no dependencies");
        for dep in &deps {
            assert!(
                rows_xor_to_zero(&rows, dep, n_f),
                "BL returned a non-genuine dependency at high nullity"
            );
        }
        let dep_vectors: Vec<Vec<u32>> = deps
            .iter()
            .map(|d| d.iter().map(|&i| i as u32).collect())
            .collect();
        assert_eq!(
            gf2_rank(&dep_vectors, n_r),
            deps.len(),
            "deps not independent"
        );
    }

    #[test]
    #[ignore = "benchmark: run with --ignored --nocapture"]
    fn block_lanczos_thread_scaling() {
        use std::time::Instant;
        let mut seed = 0xABCD_1234u64;
        let mut rng = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let n_f = 20000usize;
        let n_r = n_f + 192;
        let mut sr = SparseRelations::new(n_f);
        for _ in 0..n_r {
            let mut cols: Vec<u32> = (0..24).map(|_| (rng() % n_f as u64) as u32).collect();
            cols.sort_unstable();
            cols.dedup();
            sr.push_sparse(cols, (Integer::from(1), Integer::from(1)));
        }
        eprintln!("--- from main thread ---");
        for threads in [1usize, 8] {
            let start = Instant::now();
            let deps = sr.dependencies_lanczos(0xC0FFEE, threads);
            let elapsed = start.elapsed();
            eprintln!("threads={threads}: {elapsed:.2?}, {} deps", deps.len());
            assert!(!deps.is_empty());
        }
        // mimic the real call site: dependencies_lanczos is invoked from *inside* a
        // rayon::scope spawned task (the collector), not the main thread. If the
        // nested pool doesn't engage there, this will be ~as slow as 1 thread.
        eprintln!("--- from within rayon::scope spawn ---");
        for threads in [1usize, 8] {
            let mut elapsed = std::time::Duration::ZERO;
            rayon::scope(|s| {
                s.spawn(|_| {
                    let start = Instant::now();
                    let deps = sr.dependencies_lanczos(0xC0FFEE, threads);
                    elapsed = start.elapsed();
                    assert!(!deps.is_empty());
                });
            });
            eprintln!("threads={threads} (in scope): {elapsed:.2?}");
        }
    }

    #[test]
    fn filter_singletons_preserves_null_space() {
        let mut seed = 0xFEED_FACEu64;
        let mut rng = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let n_f = 400usize;
        // base rows over the first 300 columns, plus rows carrying unique primes
        // (singletons) in 300.., some chained (row only removable after another)
        let mut rows: Vec<Vec<u32>> = (0..320)
            .map(|_| {
                let mut cols: Vec<u32> = (0..8).map(|_| (rng() % 300) as u32).collect();
                cols.sort_unstable();
                cols.dedup();
                cols
            })
            .collect();
        for i in 0..50u32 {
            // rows 320..370: each carries unique prime 300+i — removable round 1
            let mut cols: Vec<u32> = (0..6).map(|_| (rng() % 300) as u32).collect();
            cols.push(300 + i);
            cols.sort_unstable();
            cols.dedup();
            rows.push(cols);
        }
        // a 2-chain: row A has primes {350, 351}, row B has {351}; B's removal makes
        // 350 a singleton only after A... (i.e. A has {398, 399}, B has {399, x})
        rows.push(vec![5, 398, 399]);
        rows.push(vec![7, 399]);

        let keep = filter_singletons(&rows, n_f);
        let filtered: Vec<Vec<u32>> = keep.iter().map(|&r| rows[r as usize].clone()).collect();
        assert!(filtered.len() < rows.len(), "nothing was filtered");

        // null space must be identical: same number of dependencies, and every
        // dependency of the filtered matrix is a dependency of the original (after
        // remapping), and vice versa (compare via counts + genuineness).
        let deps_full = dense_left_null_space(&rows, n_f);
        let deps_filt = dense_left_null_space(&filtered, n_f);
        assert_eq!(
            deps_full.len(),
            deps_filt.len(),
            "nullity changed by filtering"
        );
        for dep in &deps_filt {
            let remapped: Vec<usize> = dep.iter().map(|&i| keep[i] as usize).collect();
            assert!(rows_xor_to_zero(&rows, &remapped, n_f));
        }
        // no dependency of the original may involve a filtered-out row
        let kept: std::collections::HashSet<usize> = keep.iter().map(|&r| r as usize).collect();
        for dep in &deps_full {
            assert!(
                dep.iter().all(|r| kept.contains(r)),
                "a dependency used a singleton relation"
            );
        }
    }

    #[test]
    #[ignore = "needs src/bin/lanczos_matrix.txt (2MB dump of the failing 251-bit matrix)"]
    fn lanczos_real_251_bit_matrix_regression() {
        // The matrix on which unfiltered Block Lanczos returned an empty kernel for
        // every start (isotropic-radical trap). With singleton filtering inside
        // dependencies_lanczos this must now produce genuine dependencies, fast.
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/src/bin/lanczos_matrix.txt");
        let text = std::fs::read_to_string(path).expect("matrix dump present");
        let mut lines = text.lines();
        let mut header = lines.next().unwrap().split_whitespace();
        let n_r: usize = header.next().unwrap().parse().unwrap();
        let n_f: usize = header.next().unwrap().parse().unwrap();
        let mut sr = SparseRelations::new(n_f);
        for l in lines {
            let cols: Vec<u32> = l.split_whitespace().map(|x| x.parse().unwrap()).collect();
            sr.push_sparse(cols, (Integer::from(1), Integer::from(1)));
        }
        assert_eq!(sr.len(), n_r);

        let deps = sr.dependencies_lanczos(0x5161_7A9F_2C3D_4E5F, 8);
        assert!(
            !deps.is_empty(),
            "lanczos found no dependencies on the real matrix"
        );
        for dep in &deps {
            assert!(
                rows_xor_to_zero(sr.rows(), dep, n_f),
                "non-genuine dependency on the real matrix"
            );
        }
    }

    #[test]
    fn sparse_relations_dependencies_are_null_vectors() {
        let mut sr = SparseRelations::new(6);
        // a tiny set with a built-in square: rows 0,1,2 XOR to zero
        let uv = || (Integer::from(1), Integer::from(1));
        sr.push_sparse(vec![0, 1], uv());
        sr.push_sparse(vec![1, 2], uv());
        sr.push_sparse(vec![0, 2], uv());
        sr.push_sparse(vec![3, 4, 5], uv());
        assert_eq!(sr.len(), 4);
        let deps = sr.dependencies();
        assert!(!deps.is_empty());
        for dep in &deps {
            assert!(rows_xor_to_zero(sr.rows(), dep, sr.num_columns()));
        }
    }
}
