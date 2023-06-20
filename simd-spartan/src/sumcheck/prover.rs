use ark_ff::{to_bytes, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_sponge::{collect_sponge_bytes, collect_sponge_field_elements, Absorb};
use ark_std::vec::Vec;

use super::{verifier::VerifierMsg, IPForMVSumcheck, SumcheckPredicate};

/// Prover Message
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverMsg<F: PrimeField> {
    /// coeffs of round polynomial
    pub(crate) coeffs: Vec<F>,
}

impl<F: PrimeField> Absorb for ProverMsg<F> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(to_bytes!(self.coeffs).unwrap());
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> = collect_sponge_field_elements!(to_bytes!(self.coeffs).unwrap());
        dest.extend(tmp);
    }
}

/// Prover State
pub struct ProverState<F: PrimeField, P: SumcheckPredicate<F>> {
    pub challenges: Vec<F>,
    pub predicate: P,
    pub num_vars: usize,
    pub round: usize,
}

impl<F: PrimeField, P: SumcheckPredicate<F>> IPForMVSumcheck<F, P> {
    pub fn prover_init(predicate: P) -> ProverState<F, P> {
        let num_vars = predicate.num_vars();
        if num_vars == 0 {
            panic!("Attempt to prove a constant.")
        }

        ProverState {
            challenges: Vec::with_capacity(num_vars),
            predicate: predicate,
            num_vars: num_vars,
            round: 0,
        }
    }

    /// receive message from verifier, generate prover message, and proceed to next round
    ///
    /// Main algorithm used is from section 3.2 of [XZZPS19](https://eprint.iacr.org/2019/317.pdf#subsection.3.2).
    pub fn prove_round(
        prover_state: &mut ProverState<F, P>,
        v_msg: &Option<VerifierMsg<F>>,
    ) -> ProverMsg<F> {
        if let Some(msg) = v_msg {
            if prover_state.round == 0 {
                panic!("first round should be prover first.");
            }
            prover_state.challenges.push(msg.challenge);

            // fix argument
            let i = prover_state.round;
            let r = prover_state.challenges[i - 1];
            // let fix_variables_timer = start_timer!(|| format!("fix_variables {} {}", i,prover_state.predicate.num_vars()));
            prover_state.predicate = prover_state.predicate.fix_variables(&[r]);
            // end_timer!(fix_variables_timer);
        } else {
            if prover_state.round > 0 {
                panic!("verifier message is empty");
            }
        }

        prover_state.round += 1;

        if prover_state.round > prover_state.num_vars {
            panic!("Prover is not active");
        }

        // let round_poly_timer = start_timer!(|| format!("round_poly {}", prover_state.predicate.num_vars()));
        let round_poly = prover_state.predicate.round_poly();
        // end_timer!(round_poly_timer);
        ProverMsg { coeffs: round_poly }
    }
}
