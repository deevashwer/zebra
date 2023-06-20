use crate::{
    dense_mle::{fix_variables_custom_idx, precompute_eq_extension},
    sumcheck::{
        prover::{ProverMsg as SumcheckProverMsg, ProverState as SumcheckProverState},
        verifier::VerifierMsg as SumcheckVerifierMsg,
        IPForMVSumcheck, SumcheckPredicate,
    },
};
use ark_ff::{to_bytes, PrimeField};
use ark_poly::DenseMultilinearExtension;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_sponge::{collect_sponge_bytes, collect_sponge_field_elements, Absorb};
use std::collections::VecDeque;

use super::{
    verifier::{BatchVerifierMsg, VerifierMsg},
    GKRLevelPredicate, GKRPredicate, GKR,
};

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverMsg<F: PrimeField> {
    pub v_left: F,
    pub v_right: F,
}

impl<F: PrimeField> Absorb for ProverMsg<F> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(to_bytes!(self.v_left, self.v_right).unwrap());
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> =
            collect_sponge_field_elements!(to_bytes!(self.v_left, self.v_right).unwrap());
        dest.extend(tmp);
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct BatchProverMsg<F: PrimeField> {
    pub msgs: Vec<F>,
}

impl<F: PrimeField> Absorb for BatchProverMsg<F> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(to_bytes!(self.msgs).unwrap());
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> = collect_sponge_field_elements!(to_bytes!(self.msgs).unwrap());
        dest.extend(tmp);
    }
}

pub struct ProverState<F: PrimeField> {
    /// challenges used to merge two checks on each level into one
    pub challenges: Vec<F>,
    pub sumcheck_states: Vec<SumcheckProverState<F, GKRLevelPredicate<F>>>,
    /// The polynomial for each level
    pub level_poly: VecDeque<DenseMultilinearExtension<F>>,
    pub initial_claim: F,
    pub num_vars: usize,
    // levels go from 0 (output layer) to num_vars (input layer)
    pub level: usize,
}

pub struct BatchProverState<F: PrimeField> {
    /// challenges used to merge two checks on each level into one
    pub challenges: Vec<F>,
    pub sumcheck_states: Vec<SumcheckProverState<F, GKRLevelPredicate<F>>>,
    /// The polynomial for each level
    pub level_poly: VecDeque<DenseMultilinearExtension<F>>,
    pub initial_claims: Vec<F>,
    pub num_vars: usize,
    // batch_size = 2^batch_vars
    pub batch_vars: usize,
    // levels go from 0 (output layer) to num_vars (output layer)
    // level 0 has a 2^(batch_vars)-sized polynomial
    // level `num_vars` has a 2^(batch_vars+num_vars)-sized polynomial
    pub level: usize,
}

impl<F: PrimeField> BatchProverState<F> {
    pub fn current_sumcheck_finished(&self) -> bool {
        // round for verifier start at 0
        self.sumcheck_states[self.level - 1].round == self.batch_vars + self.level - 1
    }
}

impl<F: PrimeField> GKR<F> {
    pub fn prover_init(
        gkr_pred: GKRPredicate<F>,
        num_vars: usize,
    ) -> (ProverState<F>, ProverMsg<F>) {
        let mut level_poly = VecDeque::with_capacity(num_vars + 1);
        level_poly.push_front(gkr_pred);
        for i in (0..num_vars).rev() {
            let mut level_i = vec![F::one(); 1 << i];
            for j in 0..(1 << i) {
                // normally GKR does level_poly[0][2*j] * level_poly[i+1][2*j+1]
                // but a consequence of using this encoding is that the final challenge sampled by the verifier
                // for each level sumcheck corresponds to the LSB, where we want it to correspond to the MSB
                // We want it to correspond to the MSB because the final challenge in the third sumcheck in Spartan
                // also correponds to the MSB, and we want the challenges to be consistent to save on
                // polynomial commitment evaluation proofs
                level_i[j] = level_poly[0][j] * level_poly[0][j + (1 << i)];
            }
            level_poly.push_front(DenseMultilinearExtension::from_evaluations_vec(i, level_i));
        }
        let initial_claim = level_poly[0][0];
        let v_left = level_poly[1][0];
        let v_right = level_poly[1][1];

        (
            ProverState {
                challenges: Vec::with_capacity(num_vars),
                sumcheck_states: Vec::with_capacity(num_vars),
                level_poly,
                initial_claim,
                num_vars,
                // first level is already done by sending entire level_poly[1] to the verifier
                level: 2,
            },
            ProverMsg { v_left, v_right },
        )
    }

    pub fn prover_level_sumcheck_setup(v_msg: &VerifierMsg<F>, state: &mut ProverState<F>) {
        let level = state.level;
        assert!(level >= 2 && level <= state.num_vars);
        // p_left(x) = level_poly[level](0 || x), where input is in big-endian format
        let p_left = DenseMultilinearExtension::from_evaluations_slice(
            level - 1,
            &state.level_poly[level].evaluations[..(1 << (level - 1))],
        );
        // p_right(x) = level_poly[level](1 || x), where input is in big-endian format
        let p_right = DenseMultilinearExtension::from_evaluations_slice(
            level - 1,
            &state.level_poly[level].evaluations[(1 << (level - 1)..)],
        );

        // point = [challenges from previous sumcheck, v_msg.challenge]
        // v_msg.challenge corresponds to the MSB position
        let point = if level == 2 {
            vec![v_msg.challenge]
        } else {
            // the first sumcheck that is done has level = 2, and we want to refer the previous sumcheck
            let mut tmp = state.sumcheck_states[level - 3].challenges.clone();
            tmp.push(v_msg.challenge);
            tmp
        };
        let eq_r = precompute_eq_extension(&point, level - 1);
        let gkr_level_pred = GKRLevelPredicate {
            p_left,
            p_right,
            eq_r,
            nv: level - 1,
        };
        state.challenges.push(v_msg.challenge);
        state
            .sumcheck_states
            .push(IPForMVSumcheck::prover_init(gkr_level_pred));
    }

    pub fn prover_level_sumcheck_round(
        v_msg: &Option<SumcheckVerifierMsg<F>>,
        state: &mut ProverState<F>,
    ) -> SumcheckProverMsg<F> {
        // the first sumcheck that is done has level = 2
        IPForMVSumcheck::prove_round(&mut state.sumcheck_states[state.level - 2], v_msg)
    }

    pub fn prover_level_sumcheck_finalize(
        v_msg: &SumcheckVerifierMsg<F>,
        state: &mut ProverState<F>,
    ) -> ProverMsg<F> {
        let final_challenge = v_msg.challenge;
        state.sumcheck_states[state.level - 2]
            .challenges
            .push(final_challenge);
        // the first sumcheck that is done has level = 2
        let gkr_predicate = state.sumcheck_states[state.level - 2]
            .predicate
            .fix_variables(&[final_challenge]);
        assert!(gkr_predicate.num_vars() == 0);
        let v_left = gkr_predicate.p_left[0];
        let v_right = gkr_predicate.p_right[0];
        state.level += 1;
        ProverMsg { v_left, v_right }
    }

    pub fn batch_prover_init(
        gkr_pred: Vec<GKRPredicate<F>>,
        num_vars: usize,
    ) -> (BatchProverState<F>, BatchProverMsg<F>) {
        let mut level_poly = VecDeque::with_capacity(num_vars + 1);
        let batch_size = gkr_pred.len();
        let batch_vars = batch_size.next_power_of_two().trailing_zeros() as usize;
        let mut level_0 = vec![F::zero(); 1 << (num_vars + batch_vars)];
        // concatenate all the GKR predicates into a single polynomial
        for k in 0..batch_size {
            for j in 0..(1 << num_vars) {
                level_0[k * (1 << num_vars) + j] = gkr_pred[k][j];
            }
        }
        level_poly.push_front(DenseMultilinearExtension::from_evaluations_vec(
            num_vars + batch_vars,
            level_0,
        ));
        for i in (0..num_vars).rev() {
            let mut level_i = vec![F::zero(); 1 << (i + batch_vars)];
            for k in 0..batch_size {
                for j in 0..(1 << i) {
                    // as in GKR, we want the final challenge of the protocol to correspond to the `num_vars`-1-th variable
                    // thus, of the input polynomial with `num_vars`+`batch_vars` variables, only the variable at position
                    // `num_vars`-1 will not be fixed until the final challenge (LSB is index 0)
                    level_i[k * (1 << i) + j] = level_poly[0][k * (1 << (i + 1)) + j]
                        * level_poly[0][k * (1 << (i + 1)) + j + (1 << i)];
                }
            }
            level_poly.push_front(DenseMultilinearExtension::from_evaluations_vec(
                i + batch_vars,
                level_i,
            ));
        }
        let initial_claims = (0..batch_size)
            .map(|i| level_poly[0][i])
            .collect::<Vec<F>>();
        let prover_msg = BatchProverMsg {
            msgs: initial_claims.clone(),
        };

        (
            BatchProverState {
                challenges: Vec::with_capacity(num_vars),
                sumcheck_states: Vec::with_capacity(num_vars),
                level_poly,
                initial_claims,
                num_vars,
                batch_vars,
                // first sumcheck is run on level 1, verifier evaluates the extension of level 0
                level: 1,
            },
            prover_msg,
        )
    }

    pub fn batch_prover_level_sumcheck_setup(
        v_msg: &BatchVerifierMsg<F>,
        state: &mut BatchProverState<F>,
    ) {
        let level = state.level;
        let batch_vars = state.batch_vars;
        assert!(level >= 1 && level <= state.num_vars);
        // p_left(x_1 || x_2) = level_poly[level](x_1 || 0 || x_2), where x_1 is `batch_vars` bits and x_2 is `level`-1 bits
        let p_left = fix_variables_custom_idx(&state.level_poly[level], level - 1, F::zero());
        // p_right(x_1 || x_2) = level_poly[level](x_1 || 1 || x_2), where x_1 is `batch_vars` bits and x_2 is `level`-1 bits
        let p_right = fix_variables_custom_idx(&state.level_poly[level], level - 1, F::one());

        // point = [`level`-1 challenges from prev sumcheck, v_msg.challenge, `batch_vars` challenges from prev sumcheck]
        // v_msg.challenge corresponds to the MSB position
        let point = if level == 1 {
            assert!(v_msg.challenges.len() == state.batch_vars);
            v_msg.challenges.clone()
        } else {
            assert!(v_msg.challenges.len() == 1);
            // the first sumcheck that is done has level = 1, and we want to refer the previous sumcheck
            let tmp = &state.sumcheck_states[level - 2].challenges;
            let mut challenges = Vec::new();
            challenges.extend(tmp[..level - 2].to_vec());
            challenges.push(v_msg.challenges[0]);
            challenges.extend(tmp[level - 2..batch_vars + level - 2].to_vec());
            challenges
        };
        let eq_r = precompute_eq_extension(&point, batch_vars + level - 1);
        let gkr_level_pred = GKRLevelPredicate {
            p_left,
            p_right,
            eq_r,
            nv: batch_vars + level - 1,
        };
        state.challenges.extend(v_msg.challenges.clone());
        state
            .sumcheck_states
            .push(IPForMVSumcheck::prover_init(gkr_level_pred));
    }

    pub fn batch_prover_level_sumcheck_round(
        v_msg: &Option<SumcheckVerifierMsg<F>>,
        state: &mut BatchProverState<F>,
    ) -> SumcheckProverMsg<F> {
        // the first sumcheck that is done has level = 1
        IPForMVSumcheck::prove_round(&mut state.sumcheck_states[state.level - 1], v_msg)
    }

    pub fn batch_prover_level_sumcheck_finalize(
        v_msg: &SumcheckVerifierMsg<F>,
        state: &mut BatchProverState<F>,
    ) -> BatchProverMsg<F> {
        assert!(state.sumcheck_states.len() == state.level);
        let final_challenge = v_msg.challenge;
        state.sumcheck_states[state.level - 1]
            .challenges
            .push(final_challenge);
        // the first sumcheck that is done has level = 1
        let gkr_predicate = state.sumcheck_states[state.level - 1]
            .predicate
            .fix_variables(&[final_challenge]);
        assert!(gkr_predicate.num_vars() == 0);
        let v_left = gkr_predicate.p_left[0];
        let v_right = gkr_predicate.p_right[0];
        state.level += 1;
        BatchProverMsg {
            msgs: vec![v_left, v_right],
        }
    }

    // returns (evaluation point to combine batch instances, common evaluation_point for each instance in the batch)
    pub fn batch_prover_evaluation_points(
        v_msg: &BatchVerifierMsg<F>,
        state: &mut BatchProverState<F>,
    ) -> (Vec<F>, Vec<F>) {
        let level = state.level;
        let batch_vars = state.batch_vars;
        assert!(level == state.num_vars + 1);
        assert!(state.sumcheck_states.len() == state.num_vars);
        assert!(v_msg.challenges.len() == 1);

        let final_challenge = v_msg.challenges[0];
        state.challenges.push(final_challenge);

        let tmp = &state.sumcheck_states[level - 2].challenges;
        let mut point_2 = Vec::new();
        point_2.extend(tmp[..level - 2].to_vec());
        point_2.push(final_challenge);
        let point_1 = tmp[level - 2..batch_vars + level - 2].to_vec();
        (point_1, point_2)
    }
}
