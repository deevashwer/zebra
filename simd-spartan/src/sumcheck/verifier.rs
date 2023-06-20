use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_sponge::CryptographicSponge;

use crate::CHALLENGE_SIZE;

use super::{prover::ProverMsg, IPForMVSumcheck, SumcheckPredicate};

#[derive(Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
/// Verifier Message
pub struct VerifierMsg<F: PrimeField> {
    /// challenge sampled by verifier
    pub challenge: F,
}

/// Verifier State
pub struct VerifierState<F: PrimeField> {
    /// a list storing the challenges sampled by the verifier at each round
    pub challenges: Vec<F>,
    /// a list storing the univariate polynomial in evaluation form sent by the prover at each round
    pub polynomials_received: Vec<Vec<F>>,
    pub asserted_sum: F,
    pub num_vars: usize,
    pub round: usize,
    pub finished: bool,
}
/// Subclaim when verifier is convinced
pub struct SubClaim<F: PrimeField> {
    /// the multi-dimensional point that this multilinear extension is evaluated to
    pub point: Vec<F>,
    /// the expected evaluation
    pub expected_evaluation: F,
}

impl<F: PrimeField, P: SumcheckPredicate<F>> IPForMVSumcheck<F, P> {
    /// initialize the verifier
    pub fn verifier_init(num_vars: usize, asserted_sum: F) -> VerifierState<F> {
        let num_vars = num_vars;
        VerifierState {
            challenges: Vec::with_capacity(num_vars),
            polynomials_received: Vec::with_capacity(num_vars),
            num_vars: num_vars,
            asserted_sum,
            round: 1,
            finished: false,
        }
    }

    /// Run verifier at current round, given prover message
    ///
    /// Normally, this function should perform actual verification. Instead, `verify_round` only samples
    /// and stores randomness and perform verifications altogether in `check_and_generate_subclaim` at
    /// the last step.
    pub fn verify_round<S: CryptographicSponge>(
        prover_msg: ProverMsg<F>,
        verifier_state: &mut VerifierState<F>,
        sponge: &mut S,
    ) -> VerifierMsg<F> {
        if verifier_state.finished {
            panic!("Incorrect verifier state: Verifier is already finished.");
        }

        // Now, verifier should check if the received P(0) + P(1) = expected. The check is moved to
        // `check_and_generate_subclaim`, and will be done after the last round.

        let msg = Self::sample_round(sponge);
        verifier_state.challenges.push(msg.challenge);
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
        msg
    }

    /// verify the sumcheck phase, and generate the subclaim
    ///
    /// If the asserted sum is correct, then the multilinear polynomial evaluated at `subclaim.point`
    /// is `subclaim.expected_evaluation`. Otherwise, it is highly unlikely that those two will be equal.
    /// Larger field size guarantees smaller soundness error.
    pub fn check_and_generate_subclaim(
        verifier_state: &VerifierState<F>,
    ) -> Result<SubClaim<F>, crate::Error> {
        if !verifier_state.finished {
            panic!("Verifier has not finished.");
        }

        let mut expected = verifier_state.asserted_sum;
        if verifier_state.polynomials_received.len() != verifier_state.num_vars {
            panic!("insufficient rounds");
        }
        for i in 0..verifier_state.num_vars {
            let coeffs = &verifier_state.polynomials_received[i];
            let deg = P::individual_degree();
            if coeffs.len() != deg + 1 {
                panic!("incorrect number of coeffs");
            }
            let p0 = coeffs[0];
            let p1: F = coeffs.iter().sum();
            // println!("p0: {:?}", p0);
            // println!("p1: {:?}", p1);
            // println!("expected: {:?}", expected);
            if p0 + p1 != expected {
                return Err(crate::Error::Reject(Some(
                    "Prover message is not consistent with the claim.".into(),
                )));
            }
            let r = verifier_state.challenges[i];
            let mut powers_of_r = Vec::with_capacity(deg + 1);
            powers_of_r.push(F::one());
            for j in 1..deg + 1 {
                powers_of_r.push(powers_of_r[j - 1] * r);
            }
            expected = coeffs
                .iter()
                .zip(powers_of_r.iter())
                .map(|(c, d)| *c * *d)
                .sum();
        }

        return Ok(SubClaim {
            point: verifier_state.challenges.clone(),
            expected_evaluation: expected,
        });
    }

    /// simulate a verifier message without doing verification
    ///
    /// Given the same calling context, `random_oracle_round` output exactly the same message as
    /// `verify_round`
    #[inline]
    pub fn sample_round<S: CryptographicSponge>(sponge: &mut S) -> VerifierMsg<F> {
        VerifierMsg {
            challenge: sponge
                .squeeze_field_elements_with_sizes::<F>(vec![CHALLENGE_SIZE].as_slice())[0],
        }
    }
}
