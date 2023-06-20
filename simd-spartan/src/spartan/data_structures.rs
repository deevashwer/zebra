use ark_ec::AffineCurve;
use ark_ff::{to_bytes, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{collect_sponge_bytes, collect_sponge_field_elements, Absorb};
use ark_std::io::{Read, Write};

use crate::gkr_grand_product::prover::BatchProverMsg as GKRBatchProverMsg;
use crate::hyrax_pc::{
    Commitment as HyraxCommitment, CommitterKey as HyraxCommitterKey, Proof as HyraxProof,
    VerifierKey as HyraxVerifierKey,
};
use crate::ip_r1cs::indexer::{Index, IndexInfo};
use crate::ip_r1cs::prover::{ProverFirstMsg, ProverFourthMsg, ProverSecondMsg, ProverThirdMsg};
use crate::sumcheck::prover::ProverMsg as SumcheckProverMsg;

/// Verification key for a specific index (i.e., R1CS matrices).
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct IndexVerifierKey<G: AffineCurve + Absorb> {
    /// Stores information about the size of the index, as well as its field of
    /// definition.
    pub index_info: IndexInfo<G::ScalarField>,
    /// Commitments to the indexed polynomials.
    pub index_comms: Vec<HyraxCommitment<G>>,
    /// The verifier key for this index, trimmed from the universal SRS.
    pub verifier_key: HyraxVerifierKey<G>,
}

impl<G: AffineCurve + Absorb> Absorb for IndexVerifierKey<G> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(self.index_info, self.index_comms);
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> = collect_sponge_field_elements!(self.index_info, self.index_comms);
        dest.extend(tmp);
    }
}

/// Proving key for a specific index (i.e., R1CS matrices).
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct IndexProverKey<G: AffineCurve + Absorb> {
    /// The index verifier key.
    pub index_vk: IndexVerifierKey<G>,
    /// The index itself.
    pub index: Index<G::ScalarField>,
    /// The committer key for this index, trimmed from the universal SRS.
    pub committer_key: HyraxCommitterKey<G>,
}

/// A zkSNARK proof.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<G: AffineCurve + Absorb> {
    /// Commitments to the polynomials produced by the AHP prover.
    pub first_oracles: HyraxCommitment<G>,
    pub second_oracles: HyraxCommitment<G>,
    pub prover_sumcheck_messages: Vec<SumcheckProverMsg<G::ScalarField>>,
    pub prover_gkr_sumcheck_messages: Vec<Vec<SumcheckProverMsg<G::ScalarField>>>,
    pub prover_gkr_messages: Vec<Vec<GKRBatchProverMsg<G::ScalarField>>>,
    /// Evaluations of these polynomials.
    pub prover_first_message: ProverFirstMsg<G::ScalarField>,
    pub prover_second_message: ProverSecondMsg<G::ScalarField>,
    pub prover_third_message: ProverThirdMsg<G::ScalarField>,
    pub prover_fourth_message: ProverFourthMsg<G::ScalarField>,
    /// evaluation proofs from the polynomial commitments
    pub pc_proof_ryd: HyraxProof<G>,
    pub pc_proof_rm: HyraxProof<G>,
    pub pc_proof_rn: HyraxProof<G>,
}

#[derive(Clone)]
pub struct InputInstance<F: PrimeField> {
    // formatted_input = 1 || input
    pub formatted_input: Vec<Vec<F>>,
}

impl<F: PrimeField> InputInstance<F> {
    pub fn new(formatted_input: Vec<Vec<F>>) -> Self {
        assert!(formatted_input.len().is_power_of_two());
        // let d = input.len().next_power_of_two().trailing_zeros() as usize;
        // let mut formatted_input = vec![vec![F::one()]; 1 << d];
        // for i in 0..1 << d {
        //     formatted_input[i].extend(input[i].clone());
        // }
        Self { formatted_input }
    }
}

impl<F: PrimeField> Absorb for InputInstance<F> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(to_bytes!(self.formatted_input).unwrap());
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> = collect_sponge_field_elements!(to_bytes!(self.formatted_input).unwrap());
        dest.extend(tmp);
    }
}
