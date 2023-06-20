use crate::{
    ip_r1cs::verifier::evaluate_eq_extension,
    sumcheck::{
        prover::ProverMsg as SumcheckProverMsg,
        verifier::{VerifierMsg as SumcheckVerifierMsg, VerifierState as SumcheckVerifierState},
        IPForMVSumcheck,
    },
    CHALLENGE_SIZE,
};
use ark_ff::PrimeField;
use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_sponge::CryptographicSponge;

use super::{
    prover::{BatchProverMsg, ProverMsg},
    GKRLevelPredicate, GKR,
};

#[derive(Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
/// Verifier Message
pub struct VerifierMsg<F: PrimeField> {
    /// challenge sampled by verifier
    pub challenge: F,
}

#[derive(Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct BatchVerifierMsg<F: PrimeField> {
    /// challenge sampled by verifier
    pub challenges: Vec<F>,
}

pub struct VerifierState<F: PrimeField> {
    /// challenges used to merge two checks on each level into one
    pub challenges: Vec<F>,
    pub sumcheck_states: Vec<SumcheckVerifierState<F>>,
    pub initial_claim: F,
    pub current_claim: F,
    pub num_vars: usize,
    // levels go from 0 (output layer) to num_vars - 1 (input layer)
    pub level: usize,
}

pub struct BatchVerifierState<F: PrimeField> {
    /// challenges used to merge two checks on each level into one
    pub challenges: Vec<F>,
    pub sumcheck_states: Vec<SumcheckVerifierState<F>>,
    pub initial_claims: Vec<F>,
    pub current_claim: F,
    pub num_vars: usize,
    pub batch_vars: usize,
    pub batch_size: usize,
    // levels go from 0 (output layer) to num_vars (input layer)
    pub level: usize,
}

impl<F: PrimeField> BatchVerifierState<F> {
    pub fn current_sumcheck_finished(&self) -> bool {
        self.sumcheck_states[self.level - 1].finished
    }
}

impl<F: PrimeField> GKR<F> {
    pub fn verifier_init<S: CryptographicSponge>(
        p_msg: ProverMsg<F>,
        num_vars: usize,
        sponge: &mut S,
    ) -> (VerifierState<F>, VerifierMsg<F>) {
        let level = 2;

        let mut challenges = Vec::with_capacity(num_vars);
        let challenge =
            sponge.squeeze_field_elements_with_sizes::<F>(vec![CHALLENGE_SIZE].as_slice())[0];
        challenges.push(challenge);

        let current_claim = p_msg.v_left * (F::one() - challenge) + p_msg.v_right * challenge;

        let mut sumcheck_states = Vec::with_capacity(num_vars);
        let initial_claim = p_msg.v_left * p_msg.v_right;
        let first_sumcheck_state =
            IPForMVSumcheck::<F, GKRLevelPredicate<F>>::verifier_init(level - 1, current_claim);
        sumcheck_states.push(first_sumcheck_state);

        (
            VerifierState {
                challenges,
                sumcheck_states,
                initial_claim: initial_claim,
                current_claim,
                num_vars,
                // first level is already checked by setting current claim to p_msg.v_left * p_msg.v_right
                level,
            },
            VerifierMsg { challenge },
        )
    }

    pub fn verifier_level_sumcheck_round<S: CryptographicSponge>(
        p_msg: SumcheckProverMsg<F>,
        state: &mut VerifierState<F>,
        sponge: &mut S,
    ) -> SumcheckVerifierMsg<F> {
        // the first sumcheck that is done has level = 2
        IPForMVSumcheck::<F, GKRLevelPredicate<F>>::verify_round(
            p_msg,
            &mut state.sumcheck_states[state.level - 2],
            sponge,
        )
    }

    pub fn verifier_level_sumcheck_finalize<S: CryptographicSponge>(
        p_msg: ProverMsg<F>,
        state: &mut VerifierState<F>,
        sponge: &mut S,
    ) -> Result<VerifierMsg<F>, crate::Error> {
        let subclaim = IPForMVSumcheck::<F, GKRLevelPredicate<F>>::check_and_generate_subclaim(
            &state.sumcheck_states[state.level - 2],
        )?;
        let r = subclaim.point;
        let e = subclaim.expected_evaluation;
        let r_prev = if state.level == 2 {
            vec![state.challenges[state.level - 2]]
        } else {
            let mut tmp = state.sumcheck_states[state.level - 3].challenges.clone();
            tmp.push(state.challenges[state.level - 2]);
            tmp
        };
        let eq_r = evaluate_eq_extension(&r_prev, &r, state.level - 1);
        if e != p_msg.v_left * p_msg.v_right * eq_r {
            return Err(crate::Error::Reject(Some(
                "invalid subclaim to GKR level sumcheck".into(),
            )));
        }

        let challenge =
            sponge.squeeze_field_elements_with_sizes::<F>(vec![CHALLENGE_SIZE].as_slice())[0];
        state.challenges.push(challenge);
        state.current_claim = p_msg.v_left * (F::one() - challenge) + p_msg.v_right * challenge;
        state.level += 1;

        if state.level <= state.num_vars {
            let next_sumcheck_state = IPForMVSumcheck::<F, GKRLevelPredicate<F>>::verifier_init(
                state.level - 1,
                state.current_claim,
            );
            state.sumcheck_states.push(next_sumcheck_state);
        }

        Ok(VerifierMsg { challenge })
    }
}

impl<F: PrimeField> GKR<F> {
    pub fn batch_verifier_init<S: CryptographicSponge>(
        p_msg: BatchProverMsg<F>,
        num_vars: usize,
        batch_size: usize,
        sponge: &mut S,
    ) -> (BatchVerifierState<F>, BatchVerifierMsg<F>) {
        let level = 1;
        let batch_vars = batch_size.next_power_of_two().trailing_zeros() as usize;

        let challenges = sponge
            .squeeze_field_elements_with_sizes::<F>(vec![CHALLENGE_SIZE; batch_vars].as_slice());

        let initial_claims = p_msg.msgs;
        let mut initial_claims_padded = initial_claims.clone();
        initial_claims_padded.extend(vec![F::zero(); (1 << batch_vars) - batch_size]);
        let initial_claim_mle =
            DenseMultilinearExtension::from_evaluations_vec(batch_vars, initial_claims_padded);
        let current_claim = initial_claim_mle.evaluate(&challenges).unwrap();

        let mut sumcheck_states = Vec::with_capacity(num_vars);
        let first_sumcheck_state = IPForMVSumcheck::<F, GKRLevelPredicate<F>>::verifier_init(
            batch_vars + level - 1,
            current_claim,
        );
        sumcheck_states.push(first_sumcheck_state);

        (
            BatchVerifierState {
                challenges: challenges.clone(),
                sumcheck_states,
                initial_claims,
                current_claim,
                num_vars,
                batch_vars,
                batch_size,
                level,
            },
            BatchVerifierMsg { challenges },
        )
    }

    pub fn batch_verifier_level_sumcheck_round<S: CryptographicSponge>(
        p_msg: SumcheckProverMsg<F>,
        state: &mut BatchVerifierState<F>,
        sponge: &mut S,
    ) -> SumcheckVerifierMsg<F> {
        // the first sumcheck that is done has level = 1
        IPForMVSumcheck::<F, GKRLevelPredicate<F>>::verify_round(
            p_msg,
            &mut state.sumcheck_states[state.level - 1],
            sponge,
        )
    }

    pub fn batch_verifier_level_sumcheck_finalize<S: CryptographicSponge>(
        p_msg: BatchProverMsg<F>,
        state: &mut BatchVerifierState<F>,
        sponge: &mut S,
    ) -> Result<BatchVerifierMsg<F>, crate::Error> {
        assert!(state.sumcheck_states.len() == state.level);
        let batch_vars = state.batch_vars;
        let level = state.level;
        let subclaim = IPForMVSumcheck::<F, GKRLevelPredicate<F>>::check_and_generate_subclaim(
            &state.sumcheck_states[level - 1],
        )?;
        let r = subclaim.point;
        let e = subclaim.expected_evaluation;
        assert!(state.challenges.len() == batch_vars + level - 1);
        let r_prev = if level == 1 {
            state.challenges.clone()
        } else {
            assert!(state.sumcheck_states[level - 2].challenges.len() == batch_vars + level - 2);
            let tmp = &state.sumcheck_states[level - 2].challenges;
            let mut challenges = Vec::new();
            challenges.extend(tmp[..level - 2].to_vec());
            challenges.push(state.challenges[batch_vars + level - 2]);
            challenges.extend(tmp[level - 2..batch_vars + level - 2].to_vec());
            challenges
        };
        let eq_r = evaluate_eq_extension(&r_prev, &r, batch_vars + level - 1);

        assert!(p_msg.msgs.len() == 2);
        let v_left = p_msg.msgs[0];
        let v_right = p_msg.msgs[1];
        if e != v_left * v_right * eq_r {
            return Err(crate::Error::Reject(Some(
                "invalid subclaim to GKR level sumcheck".into(),
            )));
        }

        let challenges =
            sponge.squeeze_field_elements_with_sizes::<F>(vec![CHALLENGE_SIZE].as_slice());
        let challenge = challenges[0];
        state.challenges.push(challenge);
        state.current_claim = v_left * (F::one() - challenge) + v_right * challenge;
        state.level += 1;

        if state.level <= state.num_vars {
            let next_sumcheck_state = IPForMVSumcheck::<F, GKRLevelPredicate<F>>::verifier_init(
                batch_vars + level,
                state.current_claim,
            );
            state.sumcheck_states.push(next_sumcheck_state);
        }

        Ok(BatchVerifierMsg { challenges })
    }

    // returns (evaluation point to combine batch instances, common evaluation_point for each instance in the batch)
    pub fn batch_verifier_evaluation_points(state: &BatchVerifierState<F>) -> (Vec<F>, Vec<F>) {
        let level = state.level;
        let batch_vars = state.batch_vars;
        assert!(level == state.num_vars + 1);
        assert!(state.sumcheck_states.len() == state.num_vars);
        assert!(state.sumcheck_states[level - 2].challenges.len() == batch_vars + level - 2);
        let tmp = &state.sumcheck_states[level - 2].challenges;
        let mut point_2 = Vec::new();
        point_2.extend(tmp[..level - 2].to_vec());
        point_2.push(state.challenges[batch_vars + level - 2]);
        let point_1 = tmp[level - 2..batch_vars + level - 2].to_vec();
        (point_1, point_2)
    }
}
