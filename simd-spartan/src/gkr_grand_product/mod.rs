use std::marker::PhantomData;

use crate::{
    dense_mle::fix_variables_opt,
    sumcheck::{Predicate, SumcheckPredicate},
};
use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;

pub mod constraints;
pub mod prover;
pub mod verifier;

#[derive(Clone)]
pub struct GKRLevelPredicate<F: PrimeField> {
    /// P_{i}(x, 0)
    p_left: DenseMultilinearExtension<F>,
    /// P_{i}(x, 1)
    p_right: DenseMultilinearExtension<F>,
    /// eq(x, r)
    eq_r: DenseMultilinearExtension<F>,
    nv: usize,
}

impl<F: PrimeField> SumcheckPredicate<F> for GKRLevelPredicate<F> {
    fn fix_variables(&self, partial_point: &[F]) -> Self {
        assert!(partial_point.len() <= self.nv);
        let nv = self.nv - partial_point.len();
        let partial_point = partial_point.to_vec();
        let p_left = fix_variables_opt(&self.p_left, &partial_point);
        let p_right = fix_variables_opt(&self.p_right, &partial_point);
        let eq_r = fix_variables_opt(&self.eq_r, &partial_point);
        Self {
            p_left,
            p_right,
            eq_r,
            nv,
        }
    }

    fn index(&self, idx: usize) -> F {
        return self.p_left[idx] * self.p_right[idx] * self.eq_r[idx];
    }

    fn num_vars(&self) -> usize {
        return self.nv;
    }

    fn individual_degree() -> usize {
        return 3;
    }

    fn get_predicate(&self) -> Predicate<F> {
        let pred = vec![(F::one(), vec![&self.p_left, &self.p_right, &self.eq_r])];
        return pred;
    }
}

pub struct GKR<F: PrimeField> {
    _field: PhantomData<F>,
}

pub type GKRPredicate<F> = DenseMultilinearExtension<F>;
