use std::borrow::Borrow;

use crate::MIN_RAYON_ITERS;
use ark_ff::PrimeField;
use ark_nonnative_field::NonNativeFieldVar;
use ark_poly::DenseMultilinearExtension;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::alloc::AllocationMode;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::cfg_iter_mut;
use ark_std::vec::Vec;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub fn merge_dense_mle<F: PrimeField>(
    mle_vec: Vec<&DenseMultilinearExtension<F>>,
) -> DenseMultilinearExtension<F> {
    let n = mle_vec.len();
    let nv = mle_vec[0].num_vars;
    let log_n = n.next_power_of_two().trailing_zeros() as usize;
    for i in 1..n {
        assert!(
            mle_vec[i].num_vars == nv,
            "MLEs must have the same number of variables"
        );
    }
    let mut combined_evals = Vec::new();
    for i in 0..n {
        for j in 0..1 << nv {
            combined_evals.push(mle_vec[i].evaluations[j]);
        }
    }
    for _ in n * (1 << nv)..1 << (log_n + nv) {
        combined_evals.push(F::zero());
    }
    DenseMultilinearExtension {
        evaluations: combined_evals,
        num_vars: log_n + nv,
    }
}

pub fn compute_lagrange_coeffs<F: PrimeField>(point: Vec<F>) -> Vec<F> {
    let dim = point.len();
    let one = F::one();
    let mut coeffs = vec![one; 1 << dim];
    for i in 0..dim {
        let r = point[i];
        let (coeffs_first, coeffs_second) = coeffs.split_at_mut(1 << i);
        cfg_iter_mut!(coeffs_second[..(1 << i)], MIN_RAYON_ITERS)
            .enumerate()
            .for_each(|(b, elem)| {
                *elem = coeffs_first[b] * r;
            });
        cfg_iter_mut!(coeffs_first, MIN_RAYON_ITERS).for_each(|elem| {
            *elem *= one - r;
        });
    }
    coeffs
}

pub fn precompute_eq_extension<F: PrimeField>(
    point: &[F],
    nv: usize,
) -> DenseMultilinearExtension<F> {
    assert!(point.len() == nv, "point must be of length nv");
    let evals = compute_lagrange_coeffs(point.to_vec());
    DenseMultilinearExtension {
        evaluations: evals,
        num_vars: nv,
    }
}

pub fn fix_variables_opt<F: PrimeField>(
    mle: &DenseMultilinearExtension<F>,
    partial_point: &Vec<F>,
) -> DenseMultilinearExtension<F> {
    let nv = mle.num_vars;
    assert!(partial_point.len() <= nv, "invalid size of partial point");
    let mut poly = &mle.evaluations;
    let mut new_poly = Vec::new();
    let dim = partial_point.len();
    // evaluate single variable of partial point from left to right
    for i in 1..dim + 1 {
        let r = partial_point[i - 1];
        let one_minus_r = F::one() - r;
        new_poly = (0..(1 << (nv - i)))
            .into_par_iter()
            .map(|b| poly[b << 1] * one_minus_r + poly[(b << 1) + 1] * r)
            .collect::<Vec<_>>();
        poly = &new_poly;
    }
    DenseMultilinearExtension {
        num_vars: nv - dim,
        evaluations: new_poly,
    }
}

pub fn fix_variables_custom_idx<F: PrimeField>(
    mle: &DenseMultilinearExtension<F>,
    idx: usize,
    point: F,
) -> DenseMultilinearExtension<F> {
    let nv = mle.num_vars;
    assert!(idx < nv, "invalid index");
    let poly = &mle.evaluations;
    let mut new_poly = vec![F::zero(); 1 << (nv - 1)];
    let r = point;
    let one_minus_r = F::one() - r;
    for i in 0..1 << (nv - idx - 1) {
        for j in 0..1 << idx {
            new_poly[i * (1 << idx) + j] = poly[i * (1 << (idx + 1)) + j] * one_minus_r
                + poly[i * (1 << (idx + 1)) + j + (1 << idx)] * r;
        }
    }
    DenseMultilinearExtension {
        num_vars: nv - 1,
        evaluations: new_poly,
    }
}

#[derive(Clone)]
pub struct DenseMLEVar<F: PrimeField, CF: PrimeField> {
    pub evaluations: Vec<NonNativeFieldVar<F, CF>>,
    pub num_vars: usize,
}

impl<F: PrimeField, CF: PrimeField> AllocVar<DenseMultilinearExtension<F>, CF>
    for DenseMLEVar<F, CF>
{
    fn new_variable<T: Borrow<DenseMultilinearExtension<F>>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|mle| {
            let mle = mle.borrow();
            let evaluations: Vec<NonNativeFieldVar<F, CF>> = mle
                .evaluations
                .iter()
                .map(|e| NonNativeFieldVar::new_variable(ns.clone(), || Ok(e), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;
            Ok(Self {
                evaluations,
                num_vars: mle.num_vars,
            })
        })
    }
}

impl<F: PrimeField, CF: PrimeField> DenseMLEVar<F, CF> {
    /// Construct a new polynomial from a list of evaluations where the index
    /// represents a point in {0,1}^`num_vars` in little endian form. For
    /// example, `0b1011` represents `P(1,1,0,1)`
    pub fn from_evaluations_vec(
        num_vars: usize,
        evaluations: Vec<NonNativeFieldVar<F, CF>>,
    ) -> Self {
        // assert that the number of variables matches the size of evaluations
        assert_eq!(
            evaluations.len(),
            1 << num_vars,
            "The size of evaluations should be 2^num_vars."
        );

        Self {
            num_vars,
            evaluations,
        }
    }

    pub fn from_evaluations_slice(
        num_vars: usize,
        evaluations: &[NonNativeFieldVar<F, CF>],
    ) -> Self {
        Self::from_evaluations_vec(num_vars, evaluations.to_vec())
    }

    pub fn evaluate(
        &self,
        point: &[NonNativeFieldVar<F, CF>],
    ) -> Result<NonNativeFieldVar<F, CF>, SynthesisError> {
        Ok(self.fix_variables(point)?.evaluations[0].clone())
    }

    pub fn fix_variables(
        &self,
        partial_point: &[NonNativeFieldVar<F, CF>],
    ) -> Result<Self, SynthesisError> {
        assert!(
            partial_point.len() <= self.num_vars,
            "invalid size of partial point"
        );
        let mut poly = self.evaluations.to_vec();
        let nv = self.num_vars;
        let dim = partial_point.len();
        let cs = self.evaluations[0].cs();
        let one: NonNativeFieldVar<F, CF> = NonNativeFieldVar::new_constant(cs, F::one())?;
        // evaluate single variable of partial point from left to right
        for i in 1..dim + 1 {
            let r = &partial_point[i - 1];
            let one_minus_r = &one - r;
            for b in 0..(1 << (nv - i)) {
                poly[b] = (&(poly[b << 1].mul_without_reduce(&one_minus_r)?)
                    + &(poly[(b << 1) + 1].mul_without_reduce(r))?)
                    .reduce()?;
            }
        }
        Ok(Self::from_evaluations_slice(
            nv - dim,
            &poly[..(1 << (nv - dim))],
        ))
    }
}
