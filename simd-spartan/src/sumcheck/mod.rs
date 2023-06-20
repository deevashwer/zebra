use std::marker::PhantomData;

use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;
use ark_std::cfg_iter;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub mod constraints;
pub mod prover;
pub mod verifier;

// Predicate stores the scalar and multilinear extensions in each term of the predicate
pub type Predicate<'a, F> = Vec<(F, Vec<&'a DenseMultilinearExtension<F>>)>;

pub trait SumcheckPredicate<F: PrimeField>: Clone {
    fn fix_variables(&self, partial_point: &[F]) -> Self;
    fn index(&self, index: usize) -> F;
    fn num_vars(&self) -> usize;
    fn individual_degree() -> usize;
    fn get_predicate(&self) -> Predicate<F>;

    fn evaluate(&self, point: &[F]) -> Option<F> {
        if point.len() == self.num_vars() {
            let fixed = self.fix_variables(point);
            Some(fixed.index(0))
        } else {
            None
        }
    }

    fn round_poly(&self) -> Vec<F> {
        let deg = Self::individual_degree();
        let pred = self.get_predicate();
        let iters = (0..1 << (self.num_vars() - 1)).collect::<Vec<_>>();
        // for b in 0..1 << (self.num_vars() - 1) {
        let coeffs_map = cfg_iter!(iters).map(|b| {
            let odd_idx = (b << 1) + 1;
            let even_idx = b << 1;
            let mut pred_coeffs: Vec<Vec<Vec<F>>> = Vec::new();
            for h in 0..pred.len() {
                let mut term_coeffs = Vec::new();
                for i in 0..pred[h].1.len() {
                    let term = pred[h].1[i];
                    term_coeffs.push(vec![term[even_idx], term[odd_idx] - term[even_idx]]);
                }
                pred_coeffs.push(term_coeffs);
            }
            let mut local_coeff_vec = vec![F::zero(); deg + 1];
            for h in 0..pred_coeffs.len() {
                for i in 1..pred_coeffs[h].len() {
                    let p = &pred_coeffs[h][0];
                    let q = &pred_coeffs[h][i];
                    // r = p * q (only storing coeffs)
                    let new_len = p.len() + q.len() - 1;
                    let mut r = vec![F::zero(); new_len];
                    for j in 0..p.len() {
                        for k in 0..q.len() {
                            r[j + k] += p[j] * q[k];
                        }
                    }
                    // always accumulating r in 0-th coefficient
                    pred_coeffs[h][0] = r;
                }
                let r = &pred_coeffs[h][0];
                for j in 0..r.len() {
                    local_coeff_vec[j] += pred[h].0 * r[j];
                }
            }
            local_coeff_vec
        });
        #[cfg(feature = "parallel")]
        let coeffs = coeffs_map.reduce(
            || vec![F::zero(); deg + 1],
            |mut acc, vec| {
                for i in 0..deg + 1 {
                    acc[i] += vec[i];
                }
                acc
            },
        );
        #[cfg(not(feature = "parallel"))]
        let coeffs = coeffs_map.fold(vec![F::zero(); deg + 1], |mut acc, vec| {
            for i in 0..deg + 1 {
                acc[i] += vec[i];
            }
            acc
        });
        return coeffs;
    }
}

pub struct IPForMVSumcheck<F: PrimeField, P: SumcheckPredicate<F>> {
    #[doc(hidden)]
    _field: PhantomData<F>,
    _predicate: PhantomData<P>,
}
