use std::borrow::Borrow;
use std::marker::PhantomData;
use std::ops::Add;

use crate::dense_mle::DenseMLEVar;
use crate::ip_r1cs::constraints::evaluate_eq_extension;
use crate::sumcheck::constraints::IPForMVSumcheckVar;
use crate::NonNativeVar;
use crate::CF;
use crate::CHALLENGE_SIZE;
use crate::F;
use ark_ec::AffineCurve;
use ark_ff::{One, Zero};
use ark_nonnative_field::NonNativeFieldMulResultVar;
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::alloc::AllocationMode;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::EqGadget;
use ark_r1cs_std::prelude::UInt8;
use ark_r1cs_std::ToBytesGadget;
use ark_relations::r1cs::ConstraintSystemRef;
use ark_relations::r1cs::Namespace;
use ark_relations::r1cs::SynthesisError;
use ark_sponge::collect_sponge_field_elements_gadget;
use ark_sponge::constraints::AbsorbGadget;
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::CryptographicSponge;

use super::prover::BatchProverMsg;
use super::prover::ProverMsg;
use super::GKRLevelPredicate;
use crate::sumcheck::constraints::{
    ProverMsgVar as SumcheckProverMsgVar, VerifierMsgVar as SumcheckVerifierMsgVar,
    VerifierStateVar as SumcheckVerifierStateVar,
};

#[derive(Clone)]
pub struct ProverMsgVar<G: AffineCurve> {
    pub v_left: NonNativeVar<G>,
    pub v_right: NonNativeVar<G>,
}

impl<G: AffineCurve> AllocVar<ProverMsg<F<G>>, CF<G>> for ProverMsgVar<G> {
    fn new_variable<T: Borrow<ProverMsg<F<G>>>>(
        cs: impl Into<Namespace<CF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|p_msg| {
            let p_msg = p_msg.borrow();
            let v_left = NonNativeFieldVar::new_variable(ns.clone(), || Ok(p_msg.v_left), mode)?;
            let v_right = NonNativeFieldVar::new_variable(ns.clone(), || Ok(p_msg.v_right), mode)?;
            Ok(Self { v_left, v_right })
        })
    }
}

impl<G: AffineCurve> AbsorbGadget<CF<G>> for ProverMsgVar<G> {
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<CF<G>>>, SynthesisError> {
        let mut msg_bytes = Vec::new();
        msg_bytes.append(&mut self.v_left.to_bytes()?);
        msg_bytes.append(&mut self.v_right.to_bytes()?);
        collect_sponge_field_elements_gadget!(msg_bytes)
    }

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<CF<G>>>, SynthesisError> {
        todo!()
    }
}

#[derive(Clone)]
pub struct BatchProverMsgVar<G: AffineCurve> {
    pub msgs: Vec<NonNativeVar<G>>,
}

impl<G: AffineCurve> AllocVar<BatchProverMsg<F<G>>, CF<G>> for BatchProverMsgVar<G> {
    fn new_variable<T: Borrow<BatchProverMsg<F<G>>>>(
        cs: impl Into<Namespace<CF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|p_msg| {
            let p_msg = p_msg.borrow();
            let msgs: Vec<NonNativeVar<G>> = p_msg
                .msgs
                .iter()
                .map(|c| NonNativeFieldVar::new_variable(ns.clone(), || Ok(c), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;
            Ok(Self { msgs })
        })
    }
}

impl<G: AffineCurve> AbsorbGadget<CF<G>> for BatchProverMsgVar<G> {
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<CF<G>>>, SynthesisError> {
        let mut msgs_bytes = Vec::new();
        for msg in &self.msgs {
            msgs_bytes.append(&mut msg.to_bytes()?);
        }

        collect_sponge_field_elements_gadget!(msgs_bytes)
    }

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<CF<G>>>, SynthesisError> {
        todo!()
    }
}

pub struct VerifierMsgVar<G: AffineCurve> {
    pub challenge: NonNativeVar<G>,
}

#[derive(Clone)]
pub struct BatchVerifierMsgVar<G: AffineCurve> {
    pub challenges: Vec<NonNativeVar<G>>,
}

pub struct VerifierStateVar<G: AffineCurve> {
    pub challenges: Vec<NonNativeVar<G>>,
    pub sumcheck_states: Vec<SumcheckVerifierStateVar<G>>,
    pub initial_claim: NonNativeVar<G>,
    pub current_claim: NonNativeVar<G>,
    pub num_vars: usize,
    pub level: usize,
}

pub struct BatchVerifierStateVar<G: AffineCurve> {
    pub challenges: Vec<NonNativeVar<G>>,
    pub sumcheck_states: Vec<SumcheckVerifierStateVar<G>>,
    pub initial_claims: Vec<NonNativeVar<G>>,
    pub current_claim: NonNativeVar<G>,
    pub num_vars: usize,
    pub batch_vars: usize,
    pub batch_size: usize,
    pub level: usize,
}

impl<G: AffineCurve> BatchVerifierStateVar<G> {
    pub fn current_sumcheck_finished(&self) -> bool {
        self.sumcheck_states[self.level - 1].finished
    }
}

pub struct GKRVar<G: AffineCurve> {
    _projective: PhantomData<G>,
}

impl<G: AffineCurve> GKRVar<G> {
    pub fn verifier_init<S: CryptographicSponge, SV: CryptographicSpongeVar<CF<G>, S>>(
        cs: ConstraintSystemRef<CF<G>>,
        p_msg: ProverMsgVar<G>,
        num_vars: usize,
        sponge: &mut SV,
    ) -> Result<(VerifierStateVar<G>, VerifierMsgVar<G>), SynthesisError> {
        let level = 2;

        let mut challenges = Vec::with_capacity(num_vars);
        let challenge = sponge
            .squeeze_nonnative_field_elements_with_sizes::<F<G>>(vec![CHALLENGE_SIZE].as_slice())?
            .0
            .pop()
            .unwrap();
        challenges.push(challenge.clone());

        let one = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::one())?;
        let one_minus_r = &one - &challenge;
        let current_claim = (p_msg.v_left.mul_without_reduce(&one_minus_r)?
            + p_msg.v_right.mul_without_reduce(&challenge)?)
        .reduce()?;

        let mut sumcheck_states = Vec::with_capacity(num_vars);
        let initial_claim = &p_msg.v_left * &p_msg.v_right;
        let first_sumcheck_state = IPForMVSumcheckVar::<G, GKRLevelPredicate<F<G>>>::verifier_init(
            level - 1,
            current_claim.clone(),
        );
        sumcheck_states.push(first_sumcheck_state);

        Ok((
            VerifierStateVar {
                challenges,
                sumcheck_states,
                initial_claim: initial_claim,
                current_claim,
                num_vars,
                level,
            },
            VerifierMsgVar { challenge },
        ))
    }

    pub fn verifier_level_sumcheck_round<
        S: CryptographicSponge,
        SV: CryptographicSpongeVar<CF<G>, S>,
    >(
        p_msg: SumcheckProverMsgVar<G>,
        state: &mut VerifierStateVar<G>,
        sponge: &mut SV,
    ) -> Result<SumcheckVerifierMsgVar<G>, SynthesisError> {
        IPForMVSumcheckVar::<G, GKRLevelPredicate<F<G>>>::verify_round(
            p_msg,
            &mut state.sumcheck_states[state.level - 2],
            sponge,
        )
    }

    pub fn verifier_level_sumcheck_finalize<
        S: CryptographicSponge,
        SV: CryptographicSpongeVar<CF<G>, S>,
    >(
        cs: ConstraintSystemRef<CF<G>>,
        p_msg: ProverMsgVar<G>,
        state: &mut VerifierStateVar<G>,
        sponge: &mut SV,
    ) -> Result<VerifierMsgVar<G>, SynthesisError> {
        let subclaim =
            IPForMVSumcheckVar::<G, GKRLevelPredicate<F<G>>>::check_and_generate_subclaim(
                cs.clone(),
                &state.sumcheck_states[state.level - 2],
            )?;
        let r = subclaim.point;
        let e = subclaim.expected_evaluation;
        let r_prev = if state.level == 2 {
            vec![state.challenges[state.level - 2].clone()]
        } else {
            let mut tmp = state.sumcheck_states[state.level - 3].challenges.clone();
            tmp.push(state.challenges[state.level - 2].clone());
            tmp
        };
        let eq_r = evaluate_eq_extension::<G>(cs.clone(), &r_prev, &r, state.level - 1)?;
        let e_expected = (&p_msg.v_right * &eq_r) * &p_msg.v_left;
        e.enforce_equal(&e_expected)?;

        let challenge = sponge
            .squeeze_nonnative_field_elements_with_sizes::<F<G>>(vec![CHALLENGE_SIZE].as_slice())?
            .0
            .pop()
            .unwrap();
        state.challenges.push(challenge.clone());

        let one = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::one())?;
        let one_minus_r = &one - &challenge;
        state.current_claim = (p_msg.v_left.mul_without_reduce(&one_minus_r)?
            + p_msg.v_right.mul_without_reduce(&challenge)?)
        .reduce()?;
        state.level += 1;

        if state.level <= state.num_vars {
            let next_sumcheck_state =
                IPForMVSumcheckVar::<G, GKRLevelPredicate<F<G>>>::verifier_init(
                    state.level - 1,
                    state.current_claim.clone(),
                );
            state.sumcheck_states.push(next_sumcheck_state);
        }

        Ok(VerifierMsgVar { challenge })
    }
}

impl<G: AffineCurve> GKRVar<G> {
    pub fn batch_verifier_init<S: CryptographicSponge, SV: CryptographicSpongeVar<CF<G>, S>>(
        cs: ConstraintSystemRef<CF<G>>,
        p_msg: BatchProverMsgVar<G>,
        num_vars: usize,
        batch_size: usize,
        sponge: &mut SV,
    ) -> Result<(BatchVerifierStateVar<G>, BatchVerifierMsgVar<G>), SynthesisError> {
        let level = 1;
        let batch_vars = batch_size.next_power_of_two().trailing_zeros() as usize;

        let challenges = sponge
            .squeeze_nonnative_field_elements_with_sizes::<F<G>>(
                vec![CHALLENGE_SIZE; batch_vars].as_slice(),
            )?
            .0;

        let initial_claims = p_msg.msgs;
        let zero = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::zero())?;
        let mut initial_claims_padded = initial_claims.clone();
        initial_claims_padded.extend(vec![zero.clone(); (1 << batch_vars) - batch_size]);
        let initial_claim_mle =
            DenseMLEVar::from_evaluations_vec(batch_vars, initial_claims_padded);
        let current_claim = initial_claim_mle.evaluate(&challenges)?;

        let mut sumcheck_states = Vec::with_capacity(num_vars);
        let first_sumcheck_state = IPForMVSumcheckVar::<G, GKRLevelPredicate<F<G>>>::verifier_init(
            batch_vars + level - 1,
            current_claim.clone(),
        );
        sumcheck_states.push(first_sumcheck_state);

        Ok((
            BatchVerifierStateVar {
                challenges: challenges.clone(),
                sumcheck_states,
                initial_claims,
                current_claim,
                num_vars,
                batch_vars,
                batch_size,
                level,
            },
            BatchVerifierMsgVar { challenges },
        ))
    }

    pub fn batch_verifier_level_sumcheck_round<
        S: CryptographicSponge,
        SV: CryptographicSpongeVar<CF<G>, S>,
    >(
        p_msg: SumcheckProverMsgVar<G>,
        state: &mut BatchVerifierStateVar<G>,
        sponge: &mut SV,
    ) -> Result<SumcheckVerifierMsgVar<G>, SynthesisError> {
        IPForMVSumcheckVar::<G, GKRLevelPredicate<F<G>>>::verify_round(
            p_msg,
            &mut state.sumcheck_states[state.level - 1],
            sponge,
        )
    }

    pub fn batch_verifier_level_sumcheck_finalize<
        S: CryptographicSponge,
        SV: CryptographicSpongeVar<CF<G>, S>,
    >(
        cs: ConstraintSystemRef<CF<G>>,
        p_msg: BatchProverMsgVar<G>,
        state: &mut BatchVerifierStateVar<G>,
        sponge: &mut SV,
    ) -> Result<BatchVerifierMsgVar<G>, SynthesisError> {
        assert!(state.sumcheck_states.len() == state.level);
        let batch_vars = state.batch_vars;
        let level = state.level;
        let subclaim =
            IPForMVSumcheckVar::<G, GKRLevelPredicate<F<G>>>::check_and_generate_subclaim(
                cs.clone(),
                &state.sumcheck_states[level - 1],
            )?;
        let r = subclaim.point;
        let e = subclaim.expected_evaluation;
        let r_prev = if level == 1 {
            state.challenges.clone()
        } else {
            assert!(state.sumcheck_states[level - 2].challenges.len() == batch_vars + level - 2);
            let tmp = state.sumcheck_states[level - 2].challenges.clone();
            let mut challenges = Vec::new();
            challenges.extend(tmp[..level - 2].to_vec());
            challenges.push(state.challenges[batch_vars + level - 2].clone());
            challenges.extend(tmp[level - 2..batch_vars + level - 2].to_vec());
            challenges
        };
        let eq_r = evaluate_eq_extension::<G>(cs.clone(), &r_prev, &r, batch_vars + level - 1)?;

        assert!(p_msg.msgs.len() == 2);
        let v_left = p_msg.msgs[0].clone();
        let v_right = p_msg.msgs[1].clone();

        let e_expected = (&v_right * &eq_r) * &v_left;
        e.enforce_equal(&e_expected)?;

        let challenge = sponge
            .squeeze_nonnative_field_elements_with_sizes::<F<G>>(vec![CHALLENGE_SIZE].as_slice())?
            .0
            .pop()
            .unwrap();
        state.challenges.push(challenge.clone());

        let one = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::one())?;
        let one_minus_r = &one - &challenge;
        state.current_claim = (v_left.mul_without_reduce(&one_minus_r)?
            + v_right.mul_without_reduce(&challenge)?)
        .reduce()?;
        state.level += 1;

        if state.level <= state.num_vars {
            let next_sumcheck_state =
                IPForMVSumcheckVar::<G, GKRLevelPredicate<F<G>>>::verifier_init(
                    batch_vars + level,
                    state.current_claim.clone(),
                );
            state.sumcheck_states.push(next_sumcheck_state);
        }

        Ok(BatchVerifierMsgVar {
            challenges: vec![challenge],
        })
    }

    pub fn batch_verifier_evaluation_points(
        state: &BatchVerifierStateVar<G>,
    ) -> (Vec<NonNativeVar<G>>, Vec<NonNativeVar<G>>) {
        let level = state.level;
        let batch_vars = state.batch_vars;
        assert!(level == state.num_vars + 1);
        assert!(state.sumcheck_states.len() == state.num_vars);
        assert!(state.sumcheck_states[level - 2].challenges.len() == batch_vars + level - 2);
        let tmp = &state.sumcheck_states[level - 2].challenges;
        let mut point_2 = Vec::new();
        point_2.extend(tmp[..level - 2].to_vec());
        point_2.push(state.challenges[batch_vars + level - 2].clone());
        let point_1 = tmp[level - 2..batch_vars + level - 2].to_vec();
        (point_1, point_2)
    }
}
