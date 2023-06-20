pub mod constraints;
pub mod indexer;
pub mod prover;
pub mod verifier;

use std::marker::PhantomData;

use crate::{
    dense_mle::fix_variables_opt,
    sumcheck::{Predicate, SumcheckPredicate},
};
use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;
use ark_sponge::CryptographicSponge;

#[derive(Clone)]
pub struct FirstSumcheckPredicate<F: PrimeField> {
    // MLE for AZ, BZ and CZ over variable x
    az_x: DenseMultilinearExtension<F>,
    bz_x: DenseMultilinearExtension<F>,
    cz_x: DenseMultilinearExtension<F>,
    // MLE for equality predicate over x
    eq_x: DenseMultilinearExtension<F>,
    nv: usize,
}

impl<F: PrimeField> SumcheckPredicate<F> for FirstSumcheckPredicate<F> {
    fn fix_variables(&self, partial_point: &[F]) -> Self {
        assert!(partial_point.len() <= self.nv);
        let nv = self.nv - partial_point.len();
        let partial_point = partial_point.to_vec();
        let az_x = fix_variables_opt(&self.az_x, &partial_point);
        let bz_x = fix_variables_opt(&self.bz_x, &partial_point);
        let cz_x = fix_variables_opt(&self.cz_x, &partial_point);
        let eq_x = fix_variables_opt(&self.eq_x, &partial_point);
        Self {
            az_x,
            bz_x,
            cz_x,
            eq_x,
            nv,
        }
    }

    fn index(&self, idx: usize) -> F {
        return (self.az_x[idx] * self.bz_x[idx] - self.cz_x[idx]) * self.eq_x[idx];
    }

    fn num_vars(&self) -> usize {
        return self.nv;
    }

    fn individual_degree() -> usize {
        return 3;
    }

    fn get_predicate(&self) -> Predicate<F> {
        let pred = vec![
            (F::one(), vec![&self.az_x, &self.bz_x, &self.eq_x]),
            (F::zero() - F::one(), vec![&self.cz_x, &self.eq_x]),
        ];
        return pred;
    }
}

#[derive(Clone)]
pub struct SecondSumcheckPredicate<F: PrimeField> {
    // MLE for A(r_x, y) over y
    a_rx_y: DenseMultilinearExtension<F>,
    // MLE for B(r_x, y) over y
    b_rx_y: DenseMultilinearExtension<F>,
    // MLE for C(r_x, y) over y
    c_rx_y: DenseMultilinearExtension<F>,
    // MLE for Z(y)
    z_y: DenseMultilinearExtension<F>,
    /// Linear combination coeffs
    r_a_y: F,
    r_b_y: F,
    r_c_y: F,
    nv: usize,
}

impl<F: PrimeField> SumcheckPredicate<F> for SecondSumcheckPredicate<F> {
    fn fix_variables(&self, partial_point: &[F]) -> Self {
        assert!(partial_point.len() <= self.nv);
        let nv = self.nv - partial_point.len();
        let partial_point = partial_point.to_vec();
        let a_rx_y = fix_variables_opt(&self.a_rx_y, &partial_point);
        let b_rx_y = fix_variables_opt(&self.b_rx_y, &partial_point);
        let c_rx_y = fix_variables_opt(&self.c_rx_y, &partial_point);
        let z_y = fix_variables_opt(&self.z_y, &partial_point);
        Self {
            a_rx_y,
            b_rx_y,
            c_rx_y,
            z_y,
            r_a_y: self.r_a_y,
            r_b_y: self.r_b_y,
            r_c_y: self.r_c_y,
            nv,
        }
    }

    fn index(&self, idx: usize) -> F {
        return (self.r_a_y * self.a_rx_y[idx]
            + self.r_b_y * self.b_rx_y[idx]
            + self.r_c_y * self.c_rx_y[idx])
            * self.z_y[idx];
    }

    fn num_vars(&self) -> usize {
        return self.nv;
    }

    fn individual_degree() -> usize {
        return 2;
    }

    fn get_predicate(&self) -> Predicate<F> {
        let pred = vec![
            (self.r_a_y, vec![&self.a_rx_y, &self.z_y]),
            (self.r_b_y, vec![&self.b_rx_y, &self.z_y]),
            (self.r_c_y, vec![&self.c_rx_y, &self.z_y]),
        ];
        return pred;
    }
}

#[derive(Clone)]
pub struct ThirdSumcheckPredicate<F: PrimeField> {
    a_rx_h: DenseMultilinearExtension<F>,
    b_rx_h: DenseMultilinearExtension<F>,
    c_rx_h: DenseMultilinearExtension<F>,
    a_ry_h: DenseMultilinearExtension<F>,
    b_ry_h: DenseMultilinearExtension<F>,
    c_ry_h: DenseMultilinearExtension<F>,
    a_val_h: DenseMultilinearExtension<F>,
    b_val_h: DenseMultilinearExtension<F>,
    c_val_h: DenseMultilinearExtension<F>,
    r_a_h: F,
    r_b_h: F,
    r_c_h: F,
    nv: usize,
}

impl<F: PrimeField> SumcheckPredicate<F> for ThirdSumcheckPredicate<F> {
    fn fix_variables(&self, partial_point: &[F]) -> Self {
        assert!(partial_point.len() <= self.nv);
        let nv = self.nv - partial_point.len();
        let partial_point = partial_point.to_vec();
        let a_rx_h = fix_variables_opt(&self.a_rx_h, &partial_point);
        let b_rx_h = fix_variables_opt(&self.b_rx_h, &partial_point);
        let c_rx_h = fix_variables_opt(&self.c_rx_h, &partial_point);
        let a_ry_h = fix_variables_opt(&self.a_ry_h, &partial_point);
        let b_ry_h = fix_variables_opt(&self.b_ry_h, &partial_point);
        let c_ry_h = fix_variables_opt(&self.c_ry_h, &partial_point);
        let a_val_h = fix_variables_opt(&self.a_val_h, &partial_point);
        let b_val_h = fix_variables_opt(&self.b_val_h, &partial_point);
        let c_val_h = fix_variables_opt(&self.c_val_h, &partial_point);
        Self {
            a_rx_h,
            b_rx_h,
            c_rx_h,
            a_ry_h,
            b_ry_h,
            c_ry_h,
            a_val_h,
            b_val_h,
            c_val_h,
            r_a_h: self.r_a_h,
            r_b_h: self.r_b_h,
            r_c_h: self.r_c_h,
            nv,
        }
    }

    fn index(&self, idx: usize) -> F {
        return self.r_a_h * self.a_val_h[idx] * self.a_rx_h[idx] * self.a_ry_h[idx]
            + self.r_b_h * self.b_val_h[idx] * self.b_rx_h[idx] * self.b_ry_h[idx]
            + self.r_c_h * self.c_val_h[idx] * self.c_rx_h[idx] * self.c_ry_h[idx];
    }

    fn num_vars(&self) -> usize {
        return self.nv;
    }

    fn individual_degree() -> usize {
        return 3;
    }

    fn get_predicate(&self) -> Predicate<F> {
        let pred = vec![
            (self.r_a_h, vec![&self.a_val_h, &self.a_rx_h, &self.a_ry_h]),
            (self.r_b_h, vec![&self.b_val_h, &self.b_rx_h, &self.b_ry_h]),
            (self.r_c_h, vec![&self.c_val_h, &self.c_rx_h, &self.c_ry_h]),
        ];
        return pred;
    }
}

pub struct IPForR1CS<F: PrimeField, S: CryptographicSponge> {
    _field: PhantomData<F>,
    _sponge: PhantomData<S>,
}
