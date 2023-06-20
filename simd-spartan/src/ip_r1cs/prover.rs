use std::{mem::take, ops::Add};

use crate::{
    dense_mle::merge_dense_mle,
    gkr_grand_product::GKR,
    ip_r1cs::indexer::{make_matrices_square, pad_variables},
    sumcheck::{IPForMVSumcheck, SumcheckPredicate},
    Error,
};

use super::{
    indexer::{Index, Matrix},
    verifier::{VerifierFirstMsg, VerifierSecondMsg, VerifierThirdMsg},
    FirstSumcheckPredicate, IPForR1CS, SecondSumcheckPredicate, ThirdSumcheckPredicate,
};
use crate::dense_mle::{compute_lagrange_coeffs, precompute_eq_extension};
use crate::gkr_grand_product::{
    prover::BatchProverMsg as GKRBatchProverMsg, prover::BatchProverState as GKRBatchProverState,
    prover::ProverMsg as GKRProverMsg, verifier::BatchVerifierMsg as GKRBatchVerifierMsg,
};
use crate::sumcheck::prover::{ProverMsg as SumcheckProverMsg, ProverState as SumcheckProverState};
use crate::sumcheck::verifier::VerifierMsg as SumcheckVerifierMsg;
use ark_ff::{to_bytes, PrimeField};
use ark_poly::{DenseMultilinearExtension, MultilinearExtension, SparseMultilinearExtension};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, OptimizationGoal};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{
    collect_sponge_bytes, collect_sponge_field_elements, Absorb, CryptographicSponge,
};
use ark_std::{
    cfg_iter, end_timer,
    io::{Read, Write},
    start_timer,
};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use std::collections::VecDeque;

pub struct ProverState<'a, F: PrimeField> {
    /// log(number of data-parallel instances)
    pub d: usize,
    /// log(|padded_v|+|w|)
    pub n: usize,
    /// log(|v|)
    pub k: usize,
    /// log(num_non_zero)
    pub m: usize,
    /// Index
    pub index: &'a Index<F>,
    /// Input Assignment
    pub v: Vec<Vec<F>>,
    /// Witness Assignment
    pub w: Vec<Vec<F>>,
    /// MLEs AZ
    pub az_x: DenseMultilinearExtension<F>,
    /// MLEs BZ
    pub bz_x: DenseMultilinearExtension<F>,
    /// MLEs CZ
    pub cz_x: DenseMultilinearExtension<F>,
    /// MLE Z
    pub z_y: Option<DenseMultilinearExtension<F>>,
    /// MLE A_E_rx(h)
    pub a_rx_h: Option<DenseMultilinearExtension<F>>,
    /// MLE B_E_rx(h)
    pub b_rx_h: Option<DenseMultilinearExtension<F>>,
    /// MLE C_E_rx(h)
    pub c_rx_h: Option<DenseMultilinearExtension<F>>,
    /// MLE A_E_ry(h)
    pub a_ry_h: Option<DenseMultilinearExtension<F>>,
    /// MLE B_E_ry(h)
    pub b_ry_h: Option<DenseMultilinearExtension<F>>,
    /// MLE C_E_ry(h)
    pub c_ry_h: Option<DenseMultilinearExtension<F>>,
    /// d challenges
    pub r_d: Option<Vec<F>>,
    /// x challenges
    pub r_x: Option<Vec<F>>,
    /// y challenges
    pub r_y: Option<Vec<F>>,
    /// challenges on R1CS matrices
    pub r_m: Option<Vec<F>>,
    pub r_n: Option<Vec<F>>,
    /// First Sumcheck State
    pub first_sumcheck_state: Option<SumcheckProverState<F, FirstSumcheckPredicate<F>>>,
    /// Second Sumcheck State
    pub second_sumcheck_state: Option<SumcheckProverState<F, SecondSumcheckPredicate<F>>>,
    /// Third Sumcheck State
    pub third_sumcheck_state: Option<SumcheckProverState<F, ThirdSumcheckPredicate<F>>>,
    /// Current GKR Level
    pub curr_gkr_level: usize,
    /// GKR States for products of size 2^m
    pub gkr_state_m: Option<GKRBatchProverState<F>>,
    /// GKR States for products of size 2^n
    pub gkr_state_n: Option<GKRBatchProverState<F>>,
}

/// The first set of prover oracles.
pub struct ProverFirstOracles<F: PrimeField> {
    /// The MLE of `w`.
    pub w_y: DenseMultilinearExtension<F>,
}

impl<F: PrimeField> ProverFirstOracles<F> {
    pub fn merged_poly(&self) -> &DenseMultilinearExtension<F> {
        &self.w_y
    }
}

pub struct ProverSecondOracles<F: PrimeField> {
    pub a_rx_h: DenseMultilinearExtension<F>,
    pub b_rx_h: DenseMultilinearExtension<F>,
    pub c_rx_h: DenseMultilinearExtension<F>,
    pub a_ry_h: DenseMultilinearExtension<F>,
    pub b_ry_h: DenseMultilinearExtension<F>,
    pub c_ry_h: DenseMultilinearExtension<F>,
}

impl<F: PrimeField> ProverSecondOracles<F> {
    pub fn merged_poly(&self) -> DenseMultilinearExtension<F> {
        let nv = self.a_rx_h.num_vars;
        let zero_mle = DenseMultilinearExtension {
            evaluations: vec![F::zero(); 1 << nv],
            num_vars: nv,
        };
        let mle_vec = ark_std::vec![
            // padding second oracles with 8 zero MLEs to make it compatible for linear combination with r_m commitment
            &zero_mle,
            &zero_mle,
            &zero_mle,
            &zero_mle,
            &zero_mle,
            &zero_mle,
            &zero_mle,
            &zero_mle,
            &self.a_rx_h,
            &self.b_rx_h,
            &self.c_rx_h,
            &self.a_ry_h,
            &self.b_ry_h,
            &self.c_ry_h,
        ];
        merge_dense_mle(mle_vec)
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverFirstMsg<F: PrimeField> {
    pub v_a_x: F,
    pub v_b_x: F,
    pub v_c_x: F,
}

impl<F: PrimeField> Absorb for ProverFirstMsg<F> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(to_bytes!(self.v_a_x, self.v_b_x, self.v_c_x).unwrap());
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> =
            collect_sponge_field_elements!(to_bytes!(self.v_a_x, self.v_b_x, self.v_c_x).unwrap());
        dest.extend(tmp);
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverSecondMsg<F: PrimeField> {
    pub v_a_y: F,
    pub v_b_y: F,
    pub v_c_y: F,
    pub v_w_y: F,
}

impl<F: PrimeField> Absorb for ProverSecondMsg<F> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(
            to_bytes!(self.v_a_y, self.v_b_y, self.v_c_y, self.v_w_y).unwrap()
        );
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> = collect_sponge_field_elements!(to_bytes!(
            self.v_a_y, self.v_b_y, self.v_c_y, self.v_w_y
        )
        .unwrap());
        dest.extend(tmp);
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverThirdMsg<F: PrimeField> {
    pub v_a_rx: F,
    pub v_b_rx: F,
    pub v_c_rx: F,
    pub v_a_ry: F,
    pub v_b_ry: F,
    pub v_c_ry: F,
    pub v_a_val: F,
    pub v_b_val: F,
    pub v_c_val: F,
}

impl<F: PrimeField> ProverThirdMsg<F> {
    pub fn first_iter(&self) -> Vec<F> {
        vec![
            self.v_a_rx,
            self.v_b_rx,
            self.v_c_rx,
            self.v_a_ry,
            self.v_b_ry,
            self.v_c_ry,
        ]
    }

    pub fn second_iter(&self) -> Vec<F> {
        vec![self.v_a_val, self.v_b_val, self.v_c_val]
    }
}

impl<F: PrimeField> Absorb for ProverThirdMsg<F> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(to_bytes!(
            self.v_a_rx,
            self.v_b_rx,
            self.v_c_rx,
            self.v_a_ry,
            self.v_b_ry,
            self.v_c_ry,
            self.v_a_val,
            self.v_b_val,
            self.v_c_val
        )
        .unwrap());
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> = collect_sponge_field_elements!(to_bytes!(
            self.v_a_rx,
            self.v_b_rx,
            self.v_c_rx,
            self.v_a_ry,
            self.v_b_ry,
            self.v_c_ry,
            self.v_a_val,
            self.v_b_val,
            self.v_c_val
        )
        .unwrap());
        dest.extend(tmp);
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverFourthMsg<F: PrimeField> {
    pub v_a_row_m: F,
    pub v_b_row_m: F,
    pub v_c_row_m: F,
    pub v_a_col_m: F,
    pub v_b_col_m: F,
    pub v_c_col_m: F,
    pub v_a_row_read_m: F,
    pub v_b_row_read_m: F,
    pub v_c_row_read_m: F,
    pub v_a_col_read_m: F,
    pub v_b_col_read_m: F,
    pub v_c_col_read_m: F,
    pub v_a_row_final_n: F,
    pub v_b_row_final_n: F,
    pub v_c_row_final_n: F,
    pub v_a_col_final_n: F,
    pub v_b_col_final_n: F,
    pub v_c_col_final_n: F,
}

impl<F: PrimeField> ProverFourthMsg<F> {
    pub fn first_iter(&self) -> Vec<F> {
        vec![
            self.v_a_row_m,
            self.v_b_row_m,
            self.v_c_row_m,
            self.v_a_col_m,
            self.v_b_col_m,
            self.v_c_col_m,
            self.v_a_row_read_m,
            self.v_b_row_read_m,
            self.v_c_row_read_m,
            self.v_a_col_read_m,
            self.v_b_col_read_m,
            self.v_c_col_read_m,
        ]
    }

    pub fn second_iter(&self) -> Vec<F> {
        vec![
            self.v_a_row_final_n,
            self.v_b_row_final_n,
            self.v_c_row_final_n,
            self.v_a_col_final_n,
            self.v_b_col_final_n,
            self.v_c_col_final_n,
        ]
    }
}

impl<F: PrimeField> Absorb for ProverFourthMsg<F> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(to_bytes!(
            self.v_a_row_m,
            self.v_b_row_m,
            self.v_c_row_m,
            self.v_a_col_m,
            self.v_b_col_m,
            self.v_c_col_m,
            self.v_a_row_read_m,
            self.v_b_row_read_m,
            self.v_c_row_read_m,
            self.v_a_col_read_m,
            self.v_b_col_read_m,
            self.v_c_col_read_m,
            self.v_a_row_final_n,
            self.v_b_row_final_n,
            self.v_c_row_final_n,
            self.v_a_col_final_n,
            self.v_b_col_final_n,
            self.v_c_col_final_n
        )
        .unwrap());
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> = collect_sponge_field_elements!(to_bytes!(
            self.v_a_row_m,
            self.v_b_row_m,
            self.v_c_row_m,
            self.v_a_col_m,
            self.v_b_col_m,
            self.v_c_col_m,
            self.v_a_row_read_m,
            self.v_b_row_read_m,
            self.v_c_row_read_m,
            self.v_a_col_read_m,
            self.v_b_col_read_m,
            self.v_c_col_read_m,
            self.v_a_row_final_n,
            self.v_b_row_final_n,
            self.v_c_row_final_n,
            self.v_a_col_final_n,
            self.v_b_col_final_n,
            self.v_c_col_final_n
        )
        .unwrap());
        dest.extend(tmp);
    }
}

impl<F: PrimeField, S: CryptographicSponge> IPForR1CS<F, S> {
    pub fn get_input_and_witness<'a, C: ConstraintSynthesizer<F>>(
        index: &'a Index<F>,
        c: C,
        construct_matrices: bool,
    ) -> Result<(Vec<F>, Vec<F>), crate::Error> {
        let pcs = ConstraintSystem::new_ref();
        // pcs.set_optimization_goal(OptimizationGoal::Weight);
        pcs.set_optimization_goal(OptimizationGoal::Constraints);
        pcs.set_mode(ark_relations::r1cs::SynthesisMode::Prove {
            // OptimizationGoal::Weight + construct_matrices: false has a bug; leads to different number of constraints
            construct_matrices: construct_matrices,
        });
        c.generate_constraints(pcs.clone())?;
        let input_original_len = pcs.num_instance_variables();
        let k = input_original_len.next_power_of_two().trailing_zeros() as usize;
        if construct_matrices {
            assert!(pcs.is_satisfied().unwrap());
        }
        pcs.finalize();
        pad_variables(pcs.clone());
        make_matrices_square(pcs.clone());

        let pcs = pcs.into_inner().unwrap();

        let (input_assignment, witness_assignment, num_constraints) = (
            pcs.instance_assignment,
            pcs.witness_assignment,
            pcs.num_constraints,
        );

        let num_input_variables = input_assignment.len();
        let num_witness_variables = witness_assignment.len();
        if index.index_info.num_constraints != num_constraints
            || num_input_variables + num_witness_variables != index.index_info.num_variables
        {
            return Err(Error::InstanceDoesNotMatchIndex);
        }

        if !num_input_variables.is_power_of_two() || num_input_variables != num_witness_variables {
            return Err(Error::InvalidPublicInputLength);
        }

        Ok((input_assignment[..1 << k].to_vec(), witness_assignment))
    }

    pub fn prover_init<'a>(
        index: &'a Index<F>,
        input: &Vec<Vec<F>>,
        mut witness: VecDeque<Vec<F>>,
    ) -> Result<ProverState<'a, F>, crate::Error> {
        assert!(input.len().is_power_of_two());
        assert!(witness.len() == input.len());
        let d = input.len().next_power_of_two().trailing_zeros() as usize;
        let k = index.index_info.input_nv();
        let n = index.index_info.constraints_nv();
        let m = index.index_info.weight_nv();
        let mut az: Vec<F> = Vec::with_capacity(1 << (n + d));
        let mut bz: Vec<F> = Vec::with_capacity(1 << (n + d));
        let mut cz: Vec<F> = Vec::with_capacity(1 << (n + d));
        let mut v = Vec::with_capacity(1 << (k + d));
        let mut w = Vec::with_capacity(1 << (n + d - 1));
        let iters = (0..1 << d).collect::<Vec<_>>();
        let mut mz = cfg_iter!(iters)
            .map(|&i| {
                let num_input_variables = input[i].len();
                let padded_num_input_variables = 1 << (n - 1);
                // Perform matrix multiplications
                let inner_prod_fn = |row: &[(F, usize)]| {
                    let mut acc = F::zero();
                    for &(ref coeff, j) in row {
                        let tmp = if j < num_input_variables {
                            input[i][j]
                        } else if j < padded_num_input_variables {
                            F::zero()
                        } else {
                            witness[i][j - padded_num_input_variables]
                        };

                        acc += &(if coeff.is_one() { tmp } else { tmp * coeff });
                    }
                    acc
                };
                let az_i = index
                    .a
                    .iter()
                    .map(|row| inner_prod_fn(row))
                    .collect::<Vec<F>>();
                let bz_i = index
                    .b
                    .iter()
                    .map(|row| inner_prod_fn(row))
                    .collect::<Vec<F>>();
                let cz_i = index
                    .c
                    .iter()
                    .map(|row| inner_prod_fn(row))
                    .collect::<Vec<F>>();
                (az_i, bz_i, cz_i)
            })
            .collect::<VecDeque<_>>();

        for i in 0..1 << d {
            let mz_i = mz.pop_front().unwrap();
            let (mut az_i, mut bz_i, mut cz_i) = mz_i;
            az.append(&mut az_i);
            bz.append(&mut bz_i);
            cz.append(&mut cz_i);

            // only need to store the relevant inputs
            v.push(input[i].clone());
            w.push(witness.pop_front().unwrap());
        }
        let az_x = DenseMultilinearExtension {
            evaluations: az,
            num_vars: n + d,
        };
        let bz_x = DenseMultilinearExtension {
            evaluations: bz,
            num_vars: n + d,
        };
        let cz_x = DenseMultilinearExtension {
            evaluations: cz,
            num_vars: n + d,
        };

        Ok(ProverState {
            d,
            n,
            k,
            m,
            index,
            v,
            w,
            az_x,
            bz_x,
            cz_x,
            z_y: None,
            a_rx_h: None,
            b_rx_h: None,
            c_rx_h: None,
            a_ry_h: None,
            b_ry_h: None,
            c_ry_h: None,
            r_d: None,
            r_x: None,
            r_y: None,
            r_m: None,
            r_n: None,
            first_sumcheck_state: None,
            second_sumcheck_state: None,
            third_sumcheck_state: None,
            curr_gkr_level: 0,
            gkr_state_m: None,
            gkr_state_n: None,
        })
    }

    /// Output the first round message and the next state.
    pub fn prover_first_round<'a>(
        state: &mut ProverState<'a, F>,
    ) -> Result<ProverFirstOracles<F>, Error> {
        let mut flattened_padded_z: Vec<F> = Vec::new();
        for i in 0..1 << state.d {
            flattened_padded_z.extend(state.v[i].clone());
            // completing input vector by padding with zeros
            flattened_padded_z.append(&mut vec![F::zero(); (1 << (state.n - 1)) - (1 << state.k)]);
            flattened_padded_z.extend(state.w[i].clone());
        }
        let mut flattened_padded_w: Vec<F> = Vec::new();
        for i in 0..1 << state.d {
            flattened_padded_w.append(&mut state.w[i]);
        }
        let z_y =
            DenseMultilinearExtension::from_evaluations_vec(state.n + state.d, flattened_padded_z);
        let w_y = DenseMultilinearExtension::from_evaluations_vec(
            state.n + state.d - 1,
            flattened_padded_w,
        );
        state.z_y = Some(z_y);
        Ok(ProverFirstOracles { w_y })
    }

    pub fn prover_first_sumcheck_setup<'a>(
        ver_message: &VerifierFirstMsg<F>,
        state: &mut ProverState<'a, F>,
    ) {
        let eq_x = precompute_eq_extension(&ver_message.tau, state.n + state.d);
        let first_sumcheck_predicate = FirstSumcheckPredicate {
            /// state.az_x, bz_x, cz_x should not be used again
            az_x: take(&mut state.az_x),
            bz_x: take(&mut state.bz_x),
            cz_x: take(&mut state.cz_x),
            eq_x,
            nv: state.n + state.d,
        };
        state.first_sumcheck_state = Some(IPForMVSumcheck::prover_init(first_sumcheck_predicate));
    }

    pub fn prover_first_sumcheck_round<'a>(
        v_msg: &Option<SumcheckVerifierMsg<F>>,
        state: &mut ProverState<'a, F>,
    ) -> Result<SumcheckProverMsg<F>, Error> {
        Ok(IPForMVSumcheck::prove_round(
            state.first_sumcheck_state.as_mut().unwrap(),
            v_msg,
        ))
    }

    pub fn prover_first_sumcheck_finalize<'a>(
        v_msg: &SumcheckVerifierMsg<F>,
        state: &mut ProverState<'a, F>,
    ) -> Result<ProverFirstMsg<F>, Error> {
        let first_sumcheck_predicate = &state.first_sumcheck_state.as_ref().unwrap().predicate;
        let final_challenge = v_msg.challenge;
        let first_sumcheck_predicate = first_sumcheck_predicate.fix_variables(&[final_challenge]);
        assert!(first_sumcheck_predicate.num_vars() == 0);
        let v_1 = first_sumcheck_predicate.az_x.evaluations[0];
        let v_2 = first_sumcheck_predicate.bz_x.evaluations[0];
        let v_3 = first_sumcheck_predicate.cz_x.evaluations[0];
        let mut r_xd = state
            .first_sumcheck_state
            .as_ref()
            .unwrap()
            .challenges
            .clone();
        r_xd.push(final_challenge);
        state.r_d = Some(r_xd[state.n..].to_vec());
        state.r_x = Some(r_xd[..state.n].to_vec());
        Ok(ProverFirstMsg {
            v_a_x: v_1,
            v_b_x: v_2,
            v_c_x: v_3,
        })
    }

    pub fn prover_second_sumcheck_setup<'a>(
        v_msg: VerifierSecondMsg<F>,
        state: &mut ProverState<'a, F>,
    ) {
        let matrix_to_sparse_mle_time = start_timer!(|| "matrix_to_sparse_mle");
        let a_mle = matrix_to_sparse_mle(&state.index.a, state.n);
        let b_mle = matrix_to_sparse_mle(&state.index.b, state.n);
        let c_mle = matrix_to_sparse_mle(&state.index.c, state.n);
        end_timer!(matrix_to_sparse_mle_time);

        let sparse_mle_fix_variables = start_timer!(|| "sparse_mle_fix_variables");
        let r_x = state.r_x.as_ref().unwrap().clone();
        assert!(r_x.len() == state.n, "r_x len should be state.n");
        let a_rx_y = a_mle.fix_variables(&r_x).to_dense_multilinear_extension();
        let b_rx_y = b_mle.fix_variables(&r_x).to_dense_multilinear_extension();
        let c_rx_y = c_mle.fix_variables(&r_x).to_dense_multilinear_extension();
        end_timer!(sparse_mle_fix_variables);

        // combining all z_y_d's into a single z_y
        let r_d = state.r_d.as_ref().unwrap().clone();
        let lagrange_coeffs_d = compute_lagrange_coeffs::<F>(r_d);
        let z_y = state.z_y.as_ref().unwrap();
        // let mut z_y_evals = Vec::new();
        let pow2_n = 1 << state.n;
        let z_y_evals = (0..pow2_n)
            .into_par_iter()
            .map(|i| {
                let mut tmp = F::zero();
                for j in 0..1 << state.d {
                    tmp += lagrange_coeffs_d[j] * z_y.evaluations[j * pow2_n + i];
                }
                tmp
            })
            .collect::<Vec<_>>();
        let z_y = DenseMultilinearExtension::from_evaluations_vec(state.n, z_y_evals);

        let second_sumcheck_predicate = SecondSumcheckPredicate {
            a_rx_y,
            b_rx_y,
            c_rx_y,
            z_y,
            r_a_y: v_msg.r_a_y,
            r_b_y: v_msg.r_b_y,
            r_c_y: v_msg.r_c_y,
            nv: state.n,
        };
        state.second_sumcheck_state = Some(IPForMVSumcheck::prover_init(second_sumcheck_predicate));
    }

    pub fn prover_second_sumcheck_round<'a>(
        v_msg: &Option<SumcheckVerifierMsg<F>>,
        state: &mut ProverState<'a, F>,
    ) -> Result<SumcheckProverMsg<F>, Error> {
        Ok(IPForMVSumcheck::prove_round(
            state.second_sumcheck_state.as_mut().unwrap(),
            v_msg,
        ))
    }

    pub fn prover_second_sumcheck_finalize<'a>(
        v_msg: &SumcheckVerifierMsg<F>,
        state: &mut ProverState<'a, F>,
    ) -> Result<ProverSecondMsg<F>, Error> {
        let second_sumcheck_predicate = &state.second_sumcheck_state.as_ref().unwrap().predicate;
        let final_challenge = v_msg.challenge;
        let second_sumcheck_predicate = second_sumcheck_predicate.fix_variables(&[final_challenge]);
        assert!(second_sumcheck_predicate.num_vars() == 0);
        let v_a = second_sumcheck_predicate.a_rx_y.evaluations[0];
        let v_b = second_sumcheck_predicate.b_rx_y.evaluations[0];
        let v_c = second_sumcheck_predicate.c_rx_y.evaluations[0];
        let v_z = second_sumcheck_predicate.z_y.evaluations[0];
        let mut r_y = state
            .second_sumcheck_state
            .as_ref()
            .unwrap()
            .challenges
            .clone();
        r_y.push(final_challenge);
        state.r_y = Some(r_y.clone());

        let v_v_time = start_timer!(|| "v_v Computation Time");
        let mut flattened_input = Vec::new();
        for i in 0..1 << state.d {
            flattened_input.extend(&state.v[i]);
        }
        let mut eval_point = r_y[..state.k].to_vec();
        eval_point.extend(state.r_d.as_ref().unwrap());
        let mut v_v =
            DenseMultilinearExtension::from_evaluations_vec(state.k + state.d, flattened_input)
                .evaluate(&eval_point)
                .unwrap();
        for i in state.k..state.n - 1 {
            v_v *= F::one() - r_y[i];
        }
        end_timer!(v_v_time);
        // extracting v_w from v_z
        let v_w = (v_z - v_v * (F::one() - r_y[state.n - 1])) / r_y[state.n - 1];
        Ok(ProverSecondMsg {
            v_a_y: v_a,
            v_b_y: v_b,
            v_c_y: v_c,
            v_w_y: v_w,
        })
    }

    pub fn prover_third_sumcheck_setup<'a>(
        v_msg: VerifierThirdMsg<F>,
        state: &mut ProverState<'a, F>,
    ) -> Result<ProverSecondOracles<F>, Error> {
        let e_rx = precompute_eq_extension(&state.r_x.as_ref().unwrap(), state.n);
        let e_ry = precompute_eq_extension(&state.r_y.as_ref().unwrap(), state.n);
        let mut a_rx_h = Vec::new();
        let mut b_rx_h = Vec::new();
        let mut c_rx_h = Vec::new();
        let mut a_ry_h = Vec::new();
        let mut b_ry_h = Vec::new();
        let mut c_ry_h = Vec::new();
        for i in 0..1 << state.m {
            a_rx_h.push(e_rx[state.index.a_arith.row[i]]);
            b_rx_h.push(e_rx[state.index.b_arith.row[i]]);
            c_rx_h.push(e_rx[state.index.c_arith.row[i]]);
            a_ry_h.push(e_ry[state.index.a_arith.col[i]]);
            b_ry_h.push(e_ry[state.index.b_arith.col[i]]);
            c_ry_h.push(e_ry[state.index.c_arith.col[i]]);
        }
        let a_rx_h = DenseMultilinearExtension::from_evaluations_vec(state.m, a_rx_h);
        let b_rx_h = DenseMultilinearExtension::from_evaluations_vec(state.m, b_rx_h);
        let c_rx_h = DenseMultilinearExtension::from_evaluations_vec(state.m, c_rx_h);
        let a_ry_h = DenseMultilinearExtension::from_evaluations_vec(state.m, a_ry_h);
        let b_ry_h = DenseMultilinearExtension::from_evaluations_vec(state.m, b_ry_h);
        let c_ry_h = DenseMultilinearExtension::from_evaluations_vec(state.m, c_ry_h);

        state.third_sumcheck_state = Some(IPForMVSumcheck::prover_init(ThirdSumcheckPredicate {
            a_rx_h: a_rx_h.clone(),
            b_rx_h: b_rx_h.clone(),
            c_rx_h: c_rx_h.clone(),
            a_ry_h: a_ry_h.clone(),
            b_ry_h: b_ry_h.clone(),
            c_ry_h: c_ry_h.clone(),
            /// state.index.*_arith.val should not be used again
            a_val_h: state.index.a_arith.val_mle.clone(),
            b_val_h: state.index.b_arith.val_mle.clone(),
            c_val_h: state.index.c_arith.val_mle.clone(),
            r_a_h: v_msg.r_a_spark,
            r_b_h: v_msg.r_b_spark,
            r_c_h: v_msg.r_c_spark,
            nv: state.m,
        }));

        state.a_rx_h = Some(a_rx_h.clone());
        state.b_rx_h = Some(b_rx_h.clone());
        state.c_rx_h = Some(c_rx_h.clone());
        state.a_ry_h = Some(a_ry_h.clone());
        state.b_ry_h = Some(b_ry_h.clone());
        state.c_ry_h = Some(c_ry_h.clone());

        Ok(ProverSecondOracles {
            a_rx_h,
            b_rx_h,
            c_rx_h,
            a_ry_h,
            b_ry_h,
            c_ry_h,
        })
    }

    pub fn prover_third_sumcheck_round<'a>(
        v_msg: &Option<SumcheckVerifierMsg<F>>,
        state: &mut ProverState<'a, F>,
    ) -> Result<SumcheckProverMsg<F>, Error> {
        Ok(IPForMVSumcheck::prove_round(
            state.third_sumcheck_state.as_mut().unwrap(),
            v_msg,
        ))
    }

    pub fn prover_third_sumcheck_finalize<'a>(
        v_msg: &SumcheckVerifierMsg<F>,
        state: &mut ProverState<'a, F>,
    ) -> Result<ProverThirdMsg<F>, Error> {
        let third_sumcheck_predicate = &state.third_sumcheck_state.as_ref().unwrap().predicate;
        let final_challenge = v_msg.challenge;
        let third_sumcheck_predicate = third_sumcheck_predicate.fix_variables(&[final_challenge]);
        assert!(third_sumcheck_predicate.num_vars() == 0);
        let v_a_rx = third_sumcheck_predicate.a_rx_h.evaluations[0];
        let v_b_rx = third_sumcheck_predicate.b_rx_h.evaluations[0];
        let v_c_rx = third_sumcheck_predicate.c_rx_h.evaluations[0];
        let v_a_ry = third_sumcheck_predicate.a_ry_h.evaluations[0];
        let v_b_ry = third_sumcheck_predicate.b_ry_h.evaluations[0];
        let v_c_ry = third_sumcheck_predicate.c_ry_h.evaluations[0];
        let v_a_val = third_sumcheck_predicate.a_val_h.evaluations[0];
        let v_b_val = third_sumcheck_predicate.b_val_h.evaluations[0];
        let v_c_val = third_sumcheck_predicate.c_val_h.evaluations[0];
        let mut r_h = state
            .third_sumcheck_state
            .as_ref()
            .unwrap()
            .challenges
            .clone();
        r_h.push(final_challenge);
        state.r_m = Some(r_h.clone());
        Ok(ProverThirdMsg {
            v_a_rx,
            v_b_rx,
            v_c_rx,
            v_a_ry,
            v_b_ry,
            v_c_ry,
            v_a_val,
            v_b_val,
            v_c_val,
        })
    }

    pub fn prover_gkr_setup<'a>(
        v_msg: VerifierThirdMsg<F>,
        state: &mut ProverState<'a, F>,
    ) -> Result<Vec<GKRBatchProverMsg<F>>, Error> {
        // Batch GKR level starts at 2
        state.curr_gkr_level = 1;
        let mut ret = Vec::new();

        let gamma_1 = v_msg.gamma_1;
        let gamma_2 = v_msg.gamma_2;
        let eq_x = precompute_eq_extension(&state.r_x.as_ref().unwrap(), state.n);
        let eq_y = precompute_eq_extension(&state.r_y.as_ref().unwrap(), state.n);
        let idx_n = DenseMultilinearExtension::from_evaluations_vec(
            state.n,
            (0..1 << state.n).map(|i| F::from(i as u64)).collect(),
        );
        let zero_n =
            DenseMultilinearExtension::from_evaluations_vec(state.n, vec![F::zero(); 1 << state.n]);

        let init_row = compress_tuple(state.n, vec![&idx_n, &eq_x, &zero_n], gamma_1, gamma_2);
        let init_col = compress_tuple(state.n, vec![&idx_n, &eq_y, &zero_n], gamma_1, gamma_2);

        let a_final_row = compress_tuple(
            state.n,
            vec![&idx_n, &eq_x, &state.index.a_arith.row_final_mle],
            gamma_1,
            gamma_2,
        );
        let a_final_col = compress_tuple(
            state.n,
            vec![&idx_n, &eq_y, &state.index.a_arith.col_final_mle],
            gamma_1,
            gamma_2,
        );
        let b_final_row = compress_tuple(
            state.n,
            vec![&idx_n, &eq_x, &state.index.b_arith.row_final_mle],
            gamma_1,
            gamma_2,
        );
        let b_final_col = compress_tuple(
            state.n,
            vec![&idx_n, &eq_y, &state.index.b_arith.col_final_mle],
            gamma_1,
            gamma_2,
        );
        let c_final_row = compress_tuple(
            state.n,
            vec![&idx_n, &eq_x, &state.index.c_arith.row_final_mle],
            gamma_1,
            gamma_2,
        );
        let c_final_col = compress_tuple(
            state.n,
            vec![&idx_n, &eq_y, &state.index.c_arith.col_final_mle],
            gamma_1,
            gamma_2,
        );

        let preds_n = vec![
            init_row,
            init_col,
            a_final_row,
            a_final_col,
            b_final_row,
            b_final_col,
            c_final_row,
            c_final_col,
        ];

        let (state_n, msg_n) = GKR::batch_prover_init(preds_n, state.n);
        assert!(state_n.level == state.curr_gkr_level);
        state.gkr_state_n = Some(state_n);
        ret.push(msg_n);

        let a_rs_row = compress_tuple(
            state.m,
            vec![
                &state.index.a_arith.row_mle,
                &state.a_rx_h.as_ref().unwrap(),
                &state.index.a_arith.row_read_mle,
            ],
            gamma_1,
            gamma_2,
        );
        let a_rs_col = compress_tuple(
            state.m,
            vec![
                &state.index.a_arith.col_mle,
                &state.a_ry_h.as_ref().unwrap(),
                &state.index.a_arith.col_read_mle,
            ],
            gamma_1,
            gamma_2,
        );
        let b_rs_row = compress_tuple(
            state.m,
            vec![
                &state.index.b_arith.row_mle,
                &state.b_rx_h.as_ref().unwrap(),
                &state.index.b_arith.row_read_mle,
            ],
            gamma_1,
            gamma_2,
        );
        let b_rs_col = compress_tuple(
            state.m,
            vec![
                &state.index.b_arith.col_mle,
                &state.b_ry_h.as_ref().unwrap(),
                &state.index.b_arith.col_read_mle,
            ],
            gamma_1,
            gamma_2,
        );
        let c_rs_row = compress_tuple(
            state.m,
            vec![
                &state.index.c_arith.row_mle,
                &state.c_rx_h.as_ref().unwrap(),
                &state.index.c_arith.row_read_mle,
            ],
            gamma_1,
            gamma_2,
        );
        let c_rs_col = compress_tuple(
            state.m,
            vec![
                &state.index.c_arith.col_mle,
                &state.c_ry_h.as_ref().unwrap(),
                &state.index.c_arith.col_read_mle,
            ],
            gamma_1,
            gamma_2,
        );

        let a_ws_row = compress_tuple(
            state.m,
            vec![
                &state.index.a_arith.row_mle,
                &state.a_rx_h.as_ref().unwrap(),
                &increment_mle(&state.index.a_arith.row_read_mle, F::one()),
            ],
            gamma_1,
            gamma_2,
        );
        let a_ws_col = compress_tuple(
            state.m,
            vec![
                &state.index.a_arith.col_mle,
                &state.a_ry_h.as_ref().unwrap(),
                &increment_mle(&state.index.a_arith.col_read_mle, F::one()),
            ],
            gamma_1,
            gamma_2,
        );
        let b_ws_row = compress_tuple(
            state.m,
            vec![
                &state.index.b_arith.row_mle,
                &state.b_rx_h.as_ref().unwrap(),
                &increment_mle(&state.index.b_arith.row_read_mle, F::one()),
            ],
            gamma_1,
            gamma_2,
        );
        let b_ws_col = compress_tuple(
            state.m,
            vec![
                &state.index.b_arith.col_mle,
                &state.b_ry_h.as_ref().unwrap(),
                &increment_mle(&state.index.b_arith.col_read_mle, F::one()),
            ],
            gamma_1,
            gamma_2,
        );
        let c_ws_row = compress_tuple(
            state.m,
            vec![
                &state.index.c_arith.row_mle,
                &state.c_rx_h.as_ref().unwrap(),
                &increment_mle(&state.index.c_arith.row_read_mle, F::one()),
            ],
            gamma_1,
            gamma_2,
        );
        let c_ws_col = compress_tuple(
            state.m,
            vec![
                &state.index.c_arith.col_mle,
                &state.c_ry_h.as_ref().unwrap(),
                &increment_mle(&state.index.c_arith.col_read_mle, F::one()),
            ],
            gamma_1,
            gamma_2,
        );

        let preds_m = vec![
            a_rs_row, a_rs_col, b_rs_row, b_rs_col, c_rs_row, c_rs_col, a_ws_row, a_ws_col,
            b_ws_row, b_ws_col, c_ws_row, c_ws_col,
        ];

        let (state_m, msg_m) = GKR::batch_prover_init(preds_m, state.m);
        assert!(state_m.level == state.curr_gkr_level);
        state.gkr_state_m = Some(state_m);
        ret.push(msg_m);

        Ok(ret)
    }

    pub fn prover_gkr_level_sumcheck_setup<'a>(
        v_msg: &GKRBatchVerifierMsg<F>,
        state: &mut ProverState<'a, F>,
    ) {
        if state.curr_gkr_level <= state.n {
            // in case it's the first v_msg, it will be of length 4
            // for GKR_n, we need to remove the last instance as there are just 8 instances to combine
            let v_msg_n = if v_msg.challenges.len() == 4 {
                GKRBatchVerifierMsg {
                    challenges: v_msg.challenges[0..3].to_vec(),
                }
            } else {
                v_msg.clone()
            };
            GKR::batch_prover_level_sumcheck_setup(&v_msg_n, state.gkr_state_n.as_mut().unwrap());
        }
        if state.curr_gkr_level <= state.m {
            GKR::batch_prover_level_sumcheck_setup(v_msg, state.gkr_state_m.as_mut().unwrap());
        }
    }

    pub fn prover_gkr_level_sumcheck_round<'a>(
        v_msg: &Option<SumcheckVerifierMsg<F>>,
        state: &mut ProverState<'a, F>,
    ) -> Result<Vec<SumcheckProverMsg<F>>, Error> {
        let mut ret = Vec::new();
        if state.curr_gkr_level <= state.n
            && !state
                .gkr_state_n
                .as_ref()
                .unwrap()
                .current_sumcheck_finished()
        {
            ret.push(GKR::batch_prover_level_sumcheck_round(
                v_msg,
                state.gkr_state_n.as_mut().unwrap(),
            ));
        }
        if state.curr_gkr_level <= state.m
            && !state
                .gkr_state_m
                .as_ref()
                .unwrap()
                .current_sumcheck_finished()
        {
            ret.push(GKR::batch_prover_level_sumcheck_round(
                v_msg,
                state.gkr_state_m.as_mut().unwrap(),
            ));
        }
        Ok(ret)
    }

    pub fn prover_gkr_level_sumcheck_finalize<'a>(
        v_msg: &SumcheckVerifierMsg<F>,
        state: &mut ProverState<'a, F>,
    ) -> Result<Vec<GKRBatchProverMsg<F>>, Error> {
        let mut ret = Vec::new();
        if state.curr_gkr_level <= state.n {
            let state_n = state.gkr_state_n.as_ref().unwrap();
            let state_m = state.gkr_state_m.as_ref().unwrap();
            assert!(state_n.batch_vars < state_m.batch_vars);
            // the final message for gkr_n was sent previously in one of the gkr_m rounds
            let v_msg_n = state_m.sumcheck_states[state.curr_gkr_level - 1].challenges
                [state_n.batch_vars + state.curr_gkr_level - 2];
            let v_msg_n = SumcheckVerifierMsg { challenge: v_msg_n };
            ret.push(GKR::batch_prover_level_sumcheck_finalize(
                &v_msg_n,
                state.gkr_state_n.as_mut().unwrap(),
            ));
        }
        if state.curr_gkr_level <= state.m {
            ret.push(GKR::batch_prover_level_sumcheck_finalize(
                v_msg,
                state.gkr_state_m.as_mut().unwrap(),
            ));
        }
        state.curr_gkr_level += 1;
        Ok(ret)
    }

    pub fn prover_gkr_finalize<'a>(
        v_msg: &GKRBatchVerifierMsg<F>,
        state: &mut ProverState<'a, F>,
    ) -> Result<ProverFourthMsg<F>, Error> {
        let level = state.curr_gkr_level - 1; // the last iteration does an extra +1
        println!("level: {}, n: {}, m: {}", level, state.n, state.m);
        assert!(level == state.n || level == state.m);

        assert!(state.n <= state.m);
        let state_m = state.gkr_state_m.as_ref().unwrap();
        // if n < m, the final challenge for n was sent in one of the m rounds
        let v_msg_n = if state.n < state.m {
            let last_challenge_n = state_m.challenges[state_m.batch_vars + state.n - 1];
            GKRBatchVerifierMsg {
                challenges: vec![last_challenge_n],
            }
        } else {
            v_msg.clone()
        };
        let (_, r_n) =
            GKR::batch_prover_evaluation_points(&v_msg_n, state.gkr_state_n.as_mut().unwrap());
        assert!(r_n.len() == state.n);
        state.r_n = Some(r_n.clone());

        let (_, r_m) =
            GKR::batch_prover_evaluation_points(v_msg, state.gkr_state_m.as_mut().unwrap());
        for i in 0..state.m {
            assert!(r_m[i] == state.r_m.as_ref().unwrap()[i]);
        }

        let v_a_row_m = state.index.a_arith.row_mle.evaluate(&r_m).unwrap();
        let v_b_row_m = state.index.b_arith.row_mle.evaluate(&r_m).unwrap();
        let v_c_row_m = state.index.c_arith.row_mle.evaluate(&r_m).unwrap();
        let v_a_col_m = state.index.a_arith.col_mle.evaluate(&r_m).unwrap();
        let v_b_col_m = state.index.b_arith.col_mle.evaluate(&r_m).unwrap();
        let v_c_col_m = state.index.c_arith.col_mle.evaluate(&r_m).unwrap();
        let v_a_row_read_m = state.index.a_arith.row_read_mle.evaluate(&r_m).unwrap();
        let v_b_row_read_m = state.index.b_arith.row_read_mle.evaluate(&r_m).unwrap();
        let v_c_row_read_m = state.index.c_arith.row_read_mle.evaluate(&r_m).unwrap();
        let v_a_col_read_m = state.index.a_arith.col_read_mle.evaluate(&r_m).unwrap();
        let v_b_col_read_m = state.index.b_arith.col_read_mle.evaluate(&r_m).unwrap();
        let v_c_col_read_m = state.index.c_arith.col_read_mle.evaluate(&r_m).unwrap();

        let v_a_row_final_n = state.index.a_arith.row_final_mle.evaluate(&r_n).unwrap();
        let v_b_row_final_n = state.index.b_arith.row_final_mle.evaluate(&r_n).unwrap();
        let v_c_row_final_n = state.index.c_arith.row_final_mle.evaluate(&r_n).unwrap();
        let v_a_col_final_n = state.index.a_arith.col_final_mle.evaluate(&r_n).unwrap();
        let v_b_col_final_n = state.index.b_arith.col_final_mle.evaluate(&r_n).unwrap();
        let v_c_col_final_n = state.index.c_arith.col_final_mle.evaluate(&r_n).unwrap();

        Ok(ProverFourthMsg {
            v_a_row_m,
            v_b_row_m,
            v_c_row_m,
            v_a_col_m,
            v_b_col_m,
            v_c_col_m,
            v_a_row_read_m,
            v_b_row_read_m,
            v_c_row_read_m,
            v_a_col_read_m,
            v_b_col_read_m,
            v_c_col_read_m,
            v_a_row_final_n,
            v_b_row_final_n,
            v_c_row_final_n,
            v_a_col_final_n,
            v_b_col_final_n,
            v_c_col_final_n,
        })
    }
}

pub fn matrix_to_sparse_mle<F: PrimeField>(
    mat: &Matrix<F>,
    n: usize,
) -> SparseMultilinearExtension<F> {
    let mut map = Vec::new();
    let pow2_n = 1 << n;
    for (x, row) in mat.iter().enumerate() {
        for (value, y) in row.iter() {
            map.push((y * pow2_n + x, *value));
        }
    }
    SparseMultilinearExtension::from_evaluations(n * 2, &map)
}

pub fn scale_sparse_mle<F: PrimeField>(
    mle: SparseMultilinearExtension<F>,
    scale: F,
) -> SparseMultilinearExtension<F> {
    let ev: Vec<_> = mle
        .evaluations
        .iter()
        .map(|(i, v)| (*i, scale * v))
        .collect();
    SparseMultilinearExtension::from_evaluations(mle.num_vars, &ev)
}

pub fn compress_tuple<F: PrimeField>(
    nv: usize,
    tuple: Vec<&DenseMultilinearExtension<F>>,
    gamma_1: F,
    gamma_2: F,
) -> DenseMultilinearExtension<F> {
    let mut evals = vec![F::zero() - gamma_2; 1 << nv];
    let mut multiplier = F::one();
    for mle in tuple {
        for j in 0..1 << nv {
            evals[j] += multiplier * mle[j];
        }
        multiplier *= gamma_1;
    }
    DenseMultilinearExtension::from_evaluations_vec(nv, evals)
}

pub fn increment_mle<F: PrimeField>(
    mle: &DenseMultilinearExtension<F>,
    increment: F,
) -> DenseMultilinearExtension<F> {
    let increment_mle = DenseMultilinearExtension::from_evaluations_vec(
        mle.num_vars,
        vec![increment; 1 << mle.num_vars],
    );
    mle.add(&increment_mle)
}
