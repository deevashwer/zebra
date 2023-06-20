use std::borrow::Borrow;
use std::marker::PhantomData;

use crate::sumcheck::prover::ProverMsg;
use crate::NonNativeVar;
use crate::CF;
use crate::CHALLENGE_SIZE;
use crate::F;
use ark_ec::AffineCurve;
use ark_ff::One;
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

use super::SumcheckPredicate;

#[derive(Clone)]
pub struct ProverMsgVar<G: AffineCurve> {
    pub coeffs: Vec<NonNativeVar<G>>,
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
            let coeffs: Vec<NonNativeVar<G>> = p_msg
                .coeffs
                .iter()
                .map(|c| NonNativeFieldVar::new_variable(ns.clone(), || Ok(c), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;
            Ok(Self { coeffs })
        })
    }
}

impl<G: AffineCurve> AbsorbGadget<CF<G>> for ProverMsgVar<G> {
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<CF<G>>>, SynthesisError> {
        let mut coeffs_bytes = Vec::new();
        for coeff in &self.coeffs {
            coeffs_bytes.append(&mut coeff.to_bytes()?);
        }

        collect_sponge_field_elements_gadget!(coeffs_bytes)
    }

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<CF<G>>>, SynthesisError> {
        todo!()
    }
}

pub struct VerifierMsgVar<G: AffineCurve> {
    // pub challenge: Vec<Boolean<CF<G>>>,
    pub challenge: NonNativeVar<G>,
}

pub struct VerifierStateVar<G: AffineCurve> {
    // pub challenges: Vec<Vec<Boolean<CF<G>>>>,
    pub challenges: Vec<NonNativeVar<G>>,
    pub polynomials_received: Vec<Vec<NonNativeVar<G>>>,
    pub asserted_sum: NonNativeVar<G>,
    pub num_vars: usize,
    pub round: usize,
    pub finished: bool,
}

// impl<G: AffineCurve> AllocVar<VerifierState<F<G>>, CF<G>> for VerifierStateVar<G> {
//     fn new_variable<T: Borrow<VerifierState<F<G>>>>(
//         cs: impl Into<Namespace<CF<G>>>,
//         f: impl FnOnce() -> Result<T, SynthesisError>,
//         mode: AllocationMode,
//     ) -> Result<Self, SynthesisError> {
//         let ns = cs.into();
//         f().and_then(|state| {
//             let state = state.borrow();
//             let num_vars = state.num_vars;
//             let round = state.round;
//             let finished = state.finished;
//             let challenges: Vec<NonNativeVar<G>> = state
//                 .challenges
//                 .iter()
//                 .map(|c| NonNativeFieldVar::new_variable(ns.clone(), || Ok(c), mode))
//                 .collect::<Result<Vec<_>, SynthesisError>>()?;
//             let mut polynomials_received = Vec::new();
//             for poly in &state.polynomials_received {
//                 let poly_var: Vec<NonNativeVar<G>> = poly
//                     .iter()
//                     .map(|p| NonNativeFieldVar::new_variable(ns.clone(), || Ok(p), mode))
//                     .collect::<Result<Vec<_>, SynthesisError>>()?;
//                 polynomials_received.push(poly_var);
//             }
//             let asserted_sum =
//                 NonNativeFieldVar::new_variable(ns.clone(), || Ok(state.asserted_sum), mode)?;
//             Ok(Self {
//                 challenges,
//                 polynomials_received,
//                 asserted_sum,
//                 num_vars,
//                 round,
//                 finished,
//             })
//         })
//     }
// }

pub struct SubClaimVar<G: AffineCurve> {
    pub point: Vec<NonNativeVar<G>>,
    pub expected_evaluation: NonNativeVar<G>,
}

// impl<G: AffineCurve> AllocVar<SubClaim<F<G>>, CF<G>> for SubClaimVar<G> {
//     fn new_variable<T: Borrow<SubClaim<F<G>>>>(
//         cs: impl Into<Namespace<CF<G>>>,
//         f: impl FnOnce() -> Result<T, SynthesisError>,
//         mode: AllocationMode,
//     ) -> Result<Self, SynthesisError> {
//         let ns = cs.into();
//         f().and_then(|claim| {
//             let claim = claim.borrow();
//             let point: Vec<NonNativeVar<G>> = claim
//                 .point
//                 .iter()
//                 .map(|c| NonNativeFieldVar::new_variable(ns.clone(), || Ok(c), mode))
//                 .collect::<Result<Vec<_>, SynthesisError>>()?;
//             let expected_evaluation = NonNativeFieldVar::new_variable(
//                 ns.clone(),
//                 || Ok(claim.expected_evaluation),
//                 mode,
//             )?;
//             Ok(Self {
//                 point,
//                 expected_evaluation,
//             })
//         })
//     }
// }

pub struct IPForMVSumcheckVar<G: AffineCurve, P: SumcheckPredicate<F<G>>> {
    _projective: PhantomData<G>,
    _predicate: PhantomData<P>,
}

impl<G: AffineCurve, P: SumcheckPredicate<F<G>>> IPForMVSumcheckVar<G, P> {
    pub fn verifier_init(num_vars: usize, asserted_sum: NonNativeVar<G>) -> VerifierStateVar<G> {
        VerifierStateVar {
            challenges: Vec::with_capacity(num_vars),
            polynomials_received: Vec::with_capacity(num_vars),
            num_vars,
            asserted_sum,
            round: 1,
            finished: false,
        }
    }

    pub fn verify_round<S: CryptographicSponge, SV: CryptographicSpongeVar<CF<G>, S>>(
        prover_msg: ProverMsgVar<G>,
        verifier_state: &mut VerifierStateVar<G>,
        sponge: &mut SV,
    ) -> Result<VerifierMsgVar<G>, SynthesisError> {
        if verifier_state.finished {
            panic!("Incorrect verifier state: Verifier is already finished.");
        }

        let msg = Self::sample_round::<S, SV>(sponge)?;
        verifier_state.challenges.push(msg.challenge.clone());
        verifier_state.polynomials_received.push(prover_msg.coeffs);

        // Now, verifier should set `expected` to P(r).
        // This operation is also moved to `check_and_generate_subclaim`,
        // and will be done after the last round.

        if verifier_state.round == verifier_state.num_vars {
            // accept and close
            verifier_state.finished = true;
        } else {
            verifier_state.round += 1;
        }
        Ok(msg)
    }

    pub fn check_and_generate_subclaim(
        cs: ConstraintSystemRef<CF<G>>,
        verifier_state: &VerifierStateVar<G>,
    ) -> Result<SubClaimVar<G>, SynthesisError> {
        if !verifier_state.finished {
            panic!("Verifier has not finished.");
        }

        let mut expected = verifier_state.asserted_sum.clone();
        if verifier_state.polynomials_received.len() != verifier_state.num_vars {
            panic!("insufficient rounds");
        }
        for i in 0..verifier_state.num_vars {
            let coeffs = &verifier_state.polynomials_received[i];
            let deg = P::individual_degree();
            if coeffs.len() != deg + 1 {
                panic!("incorrect number of coeffs");
            }
            let p0 = &coeffs[0];
            let mut p1 = p0.clone();
            for i in 1..coeffs.len() {
                p1 += &coeffs[i];
            }
            // println!("p0: {:?}", p0.value());
            // println!("p1: {:?}", p1.value());
            // println!("expected: {:?}", expected.value());
            expected.enforce_equal(&(p0 + p1))?;
            let r = &verifier_state.challenges[i];
            let mut powers_of_r = Vec::with_capacity(deg + 1);
            let one = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::one())?;
            powers_of_r.push(one.clone());
            for j in 1..deg + 1 {
                powers_of_r.push(&powers_of_r[j - 1] * r);
            }
            let mut tmp_expected = coeffs[0].mul_without_reduce(&one)?;
            for j in 1..deg + 1 {
                tmp_expected += &coeffs[j].mul_without_reduce(&powers_of_r[j])?;
            }
            expected = tmp_expected.reduce()?;
        }

        return Ok(SubClaimVar {
            point: verifier_state.challenges.clone(),
            expected_evaluation: expected,
        });
    }

    #[inline]
    pub fn sample_round<S: CryptographicSponge, SV: CryptographicSpongeVar<CF<G>, S>>(
        sponge: &mut SV,
    ) -> Result<VerifierMsgVar<G>, SynthesisError> {
        let challenge = sponge
            .squeeze_nonnative_field_elements_with_sizes::<F<G>>(vec![CHALLENGE_SIZE].as_slice())?
            .0
            .pop()
            .unwrap();
        Ok(VerifierMsgVar { challenge })
    }
}
