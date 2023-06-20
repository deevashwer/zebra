use std::borrow::Borrow;
use std::marker::PhantomData;

use crate::dense_mle::DenseMLEVar;
use crate::gkr_grand_product::constraints::BatchProverMsgVar as GKRBatchProverMsgVar;
use crate::hyrax_pc::constraints::{
    CommitmentVar as HyraxCommitmentVar, MVPolyCommitmentVar as HyraxVar,
    ProofVar as HyraxProofVar, VerifierKeyVar as HyraxVerifierKeyVar,
};
use crate::ip_r1cs::constraints::IPForR1CSVar;
use crate::ip_r1cs::constraints::{
    ProverFirstMsgVar, ProverFourthMsgVar, ProverSecondMsgVar, ProverThirdMsgVar,
};
use crate::ip_r1cs::indexer::IndexInfo;
use crate::spartan::data_structures::{IndexVerifierKey, InputInstance, Proof};
use crate::spartan::{Spartan, SPONGE_RATE};
use crate::sumcheck::constraints::ProverMsgVar as SumcheckProverMsgVar;
use crate::NonNativeVar;
use crate::CF;
use crate::F;
use ark_ec::AffineCurve;
use ark_ff::{One, Zero};
use ark_marlin::sponge::CryptographicSpongeWithRate;
use ark_marlin::CryptographicSpongeParameters;
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::alloc::AllocationMode;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::prelude::{EqGadget, UInt8};
use ark_r1cs_std::uint64::UInt64;
use ark_r1cs_std::ToBytesGadget;
use ark_relations::r1cs::Namespace;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::{AbsorbGadget, CryptographicSpongeVar};
use ark_sponge::{
    absorb_gadget, collect_sponge_field_elements_gadget, Absorb, CryptographicSponge,
};

pub struct IndexVerifierKeyVar<
    G: AffineCurve + Absorb,
    C: CurveVar<G::Projective, CF<G>> + AbsorbGadget<CF<G>>,
> {
    /// Stores information about the size of the index, as well as its field of
    /// definition.
    pub index_info: IndexInfo<F<G>>,
    /// Commitments to the indexed polynomials.
    pub index_comms: Vec<HyraxCommitmentVar<G, C>>,
    /// The verifier key for this index, trimmed from the universal SRS.
    pub verifier_key: HyraxVerifierKeyVar<G, C>,
}

impl<G, C> AllocVar<IndexVerifierKey<G>, CF<G>> for IndexVerifierKeyVar<G, C>
where
    G: AffineCurve + Absorb,
    C: CurveVar<G::Projective, CF<G>> + AbsorbGadget<CF<G>>,
{
    fn new_variable<T: Borrow<IndexVerifierKey<G>>>(
        cs: impl Into<Namespace<CF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|vk| {
            let vk = vk.borrow();
            let index_info = vk.index_info;
            let index_comms: Vec<HyraxCommitmentVar<G, C>> = vk
                .index_comms
                .iter()
                .map(|c| HyraxCommitmentVar::new_variable(ns.clone(), || Ok(c.clone()), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;
            let verifier_key = HyraxVerifierKeyVar::new_variable(
                ns.clone(),
                || Ok(vk.verifier_key.clone()),
                mode,
            )?;
            Ok(Self {
                index_info,
                index_comms,
                verifier_key,
            })
        })
    }
}

impl<G: AffineCurve + Absorb, C: CurveVar<G::Projective, CF<G>> + AbsorbGadget<CF<G>>>
    AbsorbGadget<CF<G>> for IndexVerifierKeyVar<G, C>
{
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<CF<G>>>, SynthesisError> {
        let cs = self.verifier_key.comm_key[0].cs().clone();
        let num_copies =
            UInt64::<CF<G>>::new_constant(cs.clone(), self.index_info.num_copies as u64)?;
        let num_variables =
            UInt64::<CF<G>>::new_constant(cs.clone(), self.index_info.num_variables as u64)?;
        let num_constraints =
            UInt64::<CF<G>>::new_constant(cs.clone(), self.index_info.num_constraints as u64)?;
        let max_weight =
            UInt64::<CF<G>>::new_constant(cs.clone(), self.index_info.max_weight as u64)?;
        let num_instance_variables = UInt64::<CF<G>>::new_constant(
            cs.clone(),
            self.index_info.num_instance_variables as u64,
        )?;

        collect_sponge_field_elements_gadget!(
            &num_copies.to_bytes()?,
            &num_variables.to_bytes()?,
            &num_constraints.to_bytes()?,
            &max_weight.to_bytes()?,
            &num_instance_variables.to_bytes()?,
            &self.index_comms
        )
    }

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<CF<G>>>, SynthesisError> {
        todo!()
    }
}

pub struct ProofVar<
    G: AffineCurve + Absorb,
    C: CurveVar<G::Projective, CF<G>> + AbsorbGadget<CF<G>>,
> {
    /// Commitments to the polynomials produced by the AHP prover.
    pub first_oracles: HyraxCommitmentVar<G, C>,
    pub second_oracles: HyraxCommitmentVar<G, C>,
    pub prover_sumcheck_messages: Vec<SumcheckProverMsgVar<G>>,
    pub prover_gkr_sumcheck_messages: Vec<Vec<SumcheckProverMsgVar<G>>>,
    pub prover_gkr_messages: Vec<Vec<GKRBatchProverMsgVar<G>>>,
    /// Evaluations of these polynomials.
    pub prover_first_message: ProverFirstMsgVar<G>,
    pub prover_second_message: ProverSecondMsgVar<G>,
    pub prover_third_message: ProverThirdMsgVar<G>,
    pub prover_fourth_message: ProverFourthMsgVar<G>,
    /// evaluation proofs from the polynomial commitments
    pub pc_proof_ryd: HyraxProofVar<G>,
    pub pc_proof_rm: HyraxProofVar<G>,
    pub pc_proof_rn: HyraxProofVar<G>,
}

impl<G, C> AllocVar<Proof<G>, CF<G>> for ProofVar<G, C>
where
    G: AffineCurve + Absorb,
    C: CurveVar<G::Projective, CF<G>> + AbsorbGadget<CF<G>>,
{
    fn new_variable<T: Borrow<Proof<G>>>(
        cs: impl Into<Namespace<CF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|proof| {
            let proof = proof.borrow();
            let first_oracles = HyraxCommitmentVar::new_variable(
                ns.clone(),
                || Ok(proof.first_oracles.clone()),
                mode,
            )?;
            let second_oracles = HyraxCommitmentVar::new_variable(
                ns.clone(),
                || Ok(proof.second_oracles.clone()),
                mode,
            )?;
            let prover_sumcheck_messages: Vec<SumcheckProverMsgVar<G>> = proof
                .prover_sumcheck_messages
                .iter()
                .map(|msg| SumcheckProverMsgVar::new_variable(ns.clone(), || Ok(msg.clone()), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;
            let prover_gkr_sumcheck_messages: Vec<Vec<SumcheckProverMsgVar<G>>> = proof
                .prover_gkr_sumcheck_messages
                .iter()
                .map(|msg_vec| {
                    msg_vec
                        .iter()
                        .map(|msg| {
                            SumcheckProverMsgVar::new_variable(ns.clone(), || Ok(msg.clone()), mode)
                        })
                        .collect()
                })
                .collect::<Result<Vec<Vec<_>>, SynthesisError>>()?;
            let prover_gkr_messages: Vec<Vec<GKRBatchProverMsgVar<G>>> = proof
                .prover_gkr_messages
                .iter()
                .map(|msg_vec| {
                    msg_vec
                        .iter()
                        .map(|msg| {
                            GKRBatchProverMsgVar::new_variable(ns.clone(), || Ok(msg.clone()), mode)
                        })
                        .collect()
                })
                .collect::<Result<Vec<Vec<_>>, SynthesisError>>()?;
            let prover_first_message = ProverFirstMsgVar::new_variable(
                ns.clone(),
                || Ok(proof.prover_first_message.clone()),
                mode,
            )?;
            let prover_second_message = ProverSecondMsgVar::new_variable(
                ns.clone(),
                || Ok(proof.prover_second_message.clone()),
                mode,
            )?;
            let prover_third_message = ProverThirdMsgVar::new_variable(
                ns.clone(),
                || Ok(proof.prover_third_message.clone()),
                mode,
            )?;
            let prover_fourth_message = ProverFourthMsgVar::new_variable(
                ns.clone(),
                || Ok(proof.prover_fourth_message.clone()),
                mode,
            )?;
            let pc_proof_ryd =
                HyraxProofVar::new_variable(ns.clone(), || Ok(proof.pc_proof_ryd.clone()), mode)?;
            let pc_proof_rm =
                HyraxProofVar::new_variable(ns.clone(), || Ok(proof.pc_proof_rm.clone()), mode)?;
            let pc_proof_rn =
                HyraxProofVar::new_variable(ns.clone(), || Ok(proof.pc_proof_rn.clone()), mode)?;
            Ok(Self {
                first_oracles,
                second_oracles,
                prover_sumcheck_messages,
                prover_gkr_sumcheck_messages,
                prover_gkr_messages,
                prover_first_message,
                prover_second_message,
                prover_third_message,
                prover_fourth_message,
                pc_proof_ryd,
                pc_proof_rm,
                pc_proof_rn,
            })
        })
    }
}

#[derive(Clone)]
pub struct InputInstanceVar<G: AffineCurve> {
    pub formatted_input: Vec<Vec<NonNativeVar<G>>>,
}

impl<G: AffineCurve> AllocVar<InputInstance<F<G>>, CF<G>> for InputInstanceVar<G> {
    fn new_variable<T: Borrow<InputInstance<F<G>>>>(
        cs: impl Into<Namespace<CF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|input| {
            let input = input.borrow();
            let pow2_d = input.formatted_input.len();
            let mut formatted_input = Vec::new();
            for i in 0..pow2_d {
                let tmp: Vec<NonNativeVar<G>> = input.formatted_input[i]
                    .iter()
                    .map(|inp| NonNativeFieldVar::new_variable(ns.clone(), || Ok(inp), mode))
                    .collect::<Result<Vec<_>, SynthesisError>>()?;
                formatted_input.push(tmp);
            }
            Ok(Self { formatted_input })
        })
    }
}

impl<G: AffineCurve> AbsorbGadget<CF<G>> for InputInstanceVar<G> {
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<CF<G>>>, SynthesisError> {
        let mut input_bytes = Vec::new();
        let pow2_d = self.formatted_input.len();
        for i in 0..pow2_d {
            for elem in &self.formatted_input[i] {
                input_bytes.append(&mut elem.to_bytes()?);
            }
        }

        collect_sponge_field_elements_gadget!(input_bytes)
    }

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<CF<G>>>, SynthesisError> {
        todo!()
    }
}

pub struct SpartanVar<
    G: AffineCurve + Absorb,
    C: CurveVar<G::Projective, CF<G>> + AbsorbGadget<CF<G>>,
    S: CryptographicSponge,
    SV: CryptographicSpongeVar<CF<G>, S>,
> {
    _projective: PhantomData<G>,
    _curve: PhantomData<C>,
    _sponge: PhantomData<S>,
    _sponge_var: PhantomData<SV>,
}

impl<G, C, S, SV> SpartanVar<G, C, S, SV>
where
    G: AffineCurve + Absorb,
    C: CurveVar<G::Projective, CF<G>> + AbsorbGadget<CF<G>>,
    S: CryptographicSpongeWithRate,
    SV: CryptographicSpongeVar<CF<G>, S, Parameters = <S as CryptographicSponge>::Parameters>,
    <S as CryptographicSponge>::Parameters: CryptographicSpongeParameters,
{
    pub fn verify(
        cs: ConstraintSystemRef<CF<G>>,
        index_vk: &IndexVerifierKeyVar<G, C>,
        public_input: &InputInstanceVar<G>,
        proof: &ProofVar<G, C>,
    ) -> Result<Boolean<CF<G>>, SynthesisError> {
        let start_cost = cs.num_constraints();
        let sponge_params = <S as CryptographicSponge>::Parameters::from_rate(SPONGE_RATE);
        let mut sponge = SV::new(cs.clone(), &sponge_params);

        let protocol_name: Vec<UInt8<CF<G>>> = Spartan::<G, S>::PROTOCOL_NAME
            .iter()
            .map(|&c| UInt8::constant(c))
            .collect::<Vec<_>>();
        absorb_gadget!(&mut sponge, protocol_name, index_vk, public_input);
        absorb_gadget!(&mut sponge, proof.first_oracles);
        let (_, mut verifier_state) = IPForR1CSVar::<G, S, SV>::verifier_init(
            cs.clone(),
            index_vk.index_info,
            public_input.formatted_input.clone(),
            &mut sponge,
        )?;
        println!(
            "Verifier Init Constraints {:?}",
            cs.num_constraints() - start_cost
        );
        // println!("Status: {:?}", cs.is_satisfied());

        // Common sumcheck variables
        let d = verifier_state.d;
        let n = verifier_state.index_info.constraints_nv();
        let mut idx_sumcheck = 0;
        let mut idx_gkr_sumcheck = 0;
        let mut idx_gkr = 0;

        // --------------------------------------------------------------------
        // First sumcheck

        let start_cost = cs.num_constraints();
        for _ in 0..n + d {
            let p_msg = proof.prover_sumcheck_messages[idx_sumcheck].clone();
            absorb_gadget!(&mut sponge, p_msg);
            IPForR1CSVar::verifier_first_sumcheck_round(p_msg, &mut verifier_state, &mut sponge)?;
            idx_sumcheck += 1;
        }

        let prover_first_msg = proof.prover_first_message.clone();
        absorb_gadget!(&mut sponge, prover_first_msg);
        IPForR1CSVar::verifier_first_sumcheck_finalize(
            cs.clone(),
            prover_first_msg.clone(),
            &mut verifier_state,
            &mut sponge,
        )?;
        println!(
            "First Sumcheck Constraints {:?}",
            cs.num_constraints() - start_cost
        );
        // println!("Status: {:?}", cs.is_satisfied());

        // --------------------------------------------------------------------
        // Second sumcheck

        let start_cost = cs.num_constraints();
        for _ in 0..n {
            let p_msg = proof.prover_sumcheck_messages[idx_sumcheck].clone();
            absorb_gadget!(&mut sponge, p_msg);
            IPForR1CSVar::verifier_second_sumcheck_round(p_msg, &mut verifier_state, &mut sponge)?;
            idx_sumcheck += 1;
        }

        let prover_second_msg = proof.prover_second_message.clone();
        absorb_gadget!(&mut sponge, prover_second_msg);
        IPForR1CSVar::verifier_second_sumcheck_finalize(
            cs.clone(),
            prover_second_msg.clone(),
            &mut verifier_state,
            &mut sponge,
        )?;
        println!(
            "Second Sumcheck Constraints {:?}",
            cs.num_constraints() - start_cost
        );
        // println!("Status: {:?}", cs.is_satisfied());

        // --------------------------------------------------------------------
        // Third sumcheck and GKR (in parallel)

        let start_cost = cs.num_constraints();
        absorb_gadget!(&mut sponge, proof.second_oracles);

        let prover_gkr_msg = proof.prover_gkr_messages[idx_gkr].clone();
        idx_gkr += 1;
        absorb_gadget!(&mut sponge, prover_gkr_msg);
        IPForR1CSVar::verifier_gkr_setup(
            cs.clone(),
            prover_gkr_msg,
            &mut verifier_state,
            &mut sponge,
        )?;

        let m = verifier_state.index_info.weight_nv();
        let batch_n_nv = verifier_state.index_info.batch_constraints_poly_nv();
        let batch_m_nv = verifier_state.index_info.batch_weight_poly_nv();
        // the GKR iterations need to be run for max(m, n) times
        // assuming m is always >= n
        assert!(m >= n);
        assert!(batch_m_nv >= batch_n_nv);
        // first do the first m - 1 sumcheck instances of GKR
        // and then do the last one in parallel with third sumcheck of IP for R1CS
        for i in 0..m - 1 {
            let start_cost_local = cs.num_constraints();
            for _ in 0..i + batch_m_nv {
                let p_msg = proof.prover_gkr_sumcheck_messages[idx_gkr_sumcheck].clone();
                idx_gkr_sumcheck += 1;
                absorb_gadget!(&mut sponge, p_msg);
                IPForR1CSVar::verifier_gkr_level_sumcheck_round(
                    p_msg,
                    &mut verifier_state,
                    &mut sponge,
                )?;
            }
            let prover_gkr_msg = proof.prover_gkr_messages[idx_gkr].clone();
            idx_gkr += 1;
            absorb_gadget!(&mut sponge, prover_gkr_msg);
            IPForR1CSVar::verifier_gkr_level_sumcheck_finalize(
                cs.clone(),
                prover_gkr_msg,
                &mut verifier_state,
                &mut sponge,
            )?;
            println!(
                "GKR Sumcheck {} Constraints {:?}",
                i,
                cs.num_constraints() - start_cost_local
            );
        }
        let start_cost_local = cs.num_constraints();
        // the first m-1 iterations of the third sumcheck are run in parallel with the first m-1 iterations of the final sumcheck of GKR
        for _ in 0..m - 1 {
            let p_msg_1 = proof.prover_sumcheck_messages[idx_sumcheck].clone();
            idx_sumcheck += 1;
            let p_msg_2 = proof.prover_gkr_sumcheck_messages[idx_gkr_sumcheck].clone();
            idx_gkr_sumcheck += 1;
            absorb_gadget!(&mut sponge, p_msg_1, p_msg_2);
            let mut sponge_clone = sponge.clone();
            IPForR1CSVar::verifier_third_sumcheck_round(
                p_msg_1,
                &mut verifier_state,
                &mut sponge_clone,
            )?;
            let mut sponge_clone = sponge.clone();
            IPForR1CSVar::verifier_gkr_level_sumcheck_round(
                p_msg_2,
                &mut verifier_state,
                &mut sponge_clone,
            )?;
        }
        // then perform the next batch_m_nv iterations of final sumcheck of GKR
        for _ in 0..batch_m_nv {
            let p_msg = proof.prover_gkr_sumcheck_messages[idx_gkr_sumcheck].clone();
            idx_gkr_sumcheck += 1;
            absorb_gadget!(&mut sponge, p_msg);
            IPForR1CSVar::verifier_gkr_level_sumcheck_round(
                p_msg,
                &mut verifier_state,
                &mut sponge,
            )?;
        }
        // now the last iteration which is different from others
        let p_msg = proof.prover_sumcheck_messages[idx_sumcheck].clone();
        let prover_gkr_msg = proof.prover_gkr_messages[idx_gkr].clone();
        absorb_gadget!(&mut sponge, p_msg, prover_gkr_msg);
        let mut sponge_clone = sponge.clone();
        IPForR1CSVar::verifier_third_sumcheck_round(p_msg, &mut verifier_state, &mut sponge_clone)?;
        let mut sponge_clone = sponge.clone();
        IPForR1CSVar::verifier_gkr_level_sumcheck_finalize(
            cs.clone(),
            prover_gkr_msg,
            &mut verifier_state,
            &mut sponge_clone,
        )?;
        println!(
            "GKR Final Sumcheck and IP_R1CS Third Sumcheck Constraints {:?}",
            cs.num_constraints() - start_cost_local
        );

        let start_cost_local = cs.num_constraints();
        absorb_gadget!(
            &mut sponge,
            proof.prover_third_message.clone(),
            proof.prover_fourth_message.clone()
        );
        // finalize the third sumcheck instance verifier
        IPForR1CSVar::verifier_third_sumcheck_finalize(
            cs.clone(),
            proof.prover_third_message.clone(),
            &mut verifier_state,
            &mut sponge,
        )?;
        // finalize the GKR instance verifier
        let verifier_fourth_msg = IPForR1CSVar::verifier_gkr_finalize(
            cs.clone(),
            proof.prover_third_message.clone(),
            proof.prover_fourth_message.clone(),
            &mut verifier_state,
            &mut sponge,
        )?;
        println!(
            "GKR and IP_R1CS Third Sumcheck Finalize Constraints {:?}",
            cs.num_constraints() - start_cost_local
        );
        println!(
            "GKR and IP_R1CS Third Sumcheck Total Constraints {:?}",
            cs.num_constraints() - start_cost
        );
        // println!("Status: {:?}", cs.is_satisfied());

        // --------------------------------------------------------------------
        // Poly Commitment Checks

        let mut r_m = verifier_state.r_m.as_ref().unwrap().clone();
        let mut r_n = verifier_state.r_n.as_ref().unwrap().clone();
        let r_m_ext = verifier_fourth_msg.r_m_ext;
        let r_n_ext = verifier_fourth_msg.r_n_ext;

        let start_cost = cs.num_constraints();
        let zero: NonNativeVar<G> = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::zero())?;
        // computing v_m_1
        let mut v_m_vec_1 = vec![zero.clone(); 8];
        v_m_vec_1.extend(proof.prover_third_message.first_iter());
        v_m_vec_1.extend(vec![zero.clone(); 2]);
        let v_m_mle_1 = DenseMLEVar {
            evaluations: v_m_vec_1,
            num_vars: 4,
        };
        let v_m_1 = v_m_mle_1.evaluate(&r_m_ext).unwrap();

        // computing v_m_2
        let mut v_m_vec_2 = proof.prover_third_message.second_iter();
        v_m_vec_2.extend(proof.prover_fourth_message.first_iter());
        v_m_vec_2.extend(vec![zero.clone(); 3]);
        let v_m_mle_2 = DenseMLEVar {
            evaluations: v_m_vec_2,
            num_vars: 4,
        };
        let v_m_2 = v_m_mle_2.evaluate(&r_m_ext).unwrap();

        // computing v_n
        let mut v_n_vec = proof.prover_fourth_message.second_iter();
        v_n_vec.extend(vec![zero.clone(); 2]);
        let v_n_mle = DenseMLEVar {
            evaluations: v_n_vec,
            num_vars: 3,
        };
        let v_n = v_n_mle.evaluate(&r_n_ext).unwrap();
        println!(
            "Claim Evaluation Constraints {:?}",
            cs.num_constraints() - start_cost
        );
        // println!("Status: {:?}", cs.is_satisfied());

        // final challenges r_m and r_n
        r_m.extend(r_m_ext);
        r_n.extend(r_n_ext);

        let start_cost = cs.num_constraints();
        // ignoring the final r_y challenge used to fold input and witness
        let mut r_yd: Vec<NonNativeVar<G>> = verifier_state.r_y.as_ref().unwrap()[..n - 1].to_vec();
        r_yd.extend(verifier_state.r_d.as_ref().unwrap().clone());
        let proof_ryd = HyraxVar::check(
            cs.clone(),
            &index_vk.verifier_key,
            &&proof.first_oracles,
            &r_yd,
            &verifier_state.v_w.unwrap(),
            &proof.pc_proof_ryd,
        )?;
        println!(
            "Verifying proof_ryd Constraints {:?}",
            cs.num_constraints() - start_cost
        );
        // println!("Status: {:?}", cs.is_satisfied());

        let start_cost = cs.num_constraints();
        let one: NonNativeVar<G> = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::one())?;
        let proof_rm = HyraxVar::batch_check(
            cs.clone(),
            &index_vk.verifier_key,
            vec![&proof.second_oracles, &index_vk.index_comms[0]],
            &vec![one.clone(), verifier_fourth_msg.r_m_lin_comb],
            &r_m,
            &vec![v_m_1, v_m_2],
            &proof.pc_proof_rm,
        )?;
        println!(
            "Verifying proof_rm Constraints {:?}",
            cs.num_constraints() - start_cost
        );
        // println!("Status: {:?}", cs.is_satisfied());

        let start_cost = cs.num_constraints();
        let proof_rn = HyraxVar::check(
            cs.clone(),
            &index_vk.verifier_key,
            &index_vk.index_comms[1],
            &r_n,
            &v_n,
            &proof.pc_proof_rn,
        )?;
        println!(
            "Verifying proof_rn Constraints {:?}",
            cs.num_constraints() - start_cost
        );
        // println!("Status: {:?}", cs.is_satisfied());

        proof_ryd
            .and(&proof_rm)?
            .and(&proof_rn)?
            .enforce_equal(&Boolean::TRUE)?;
        // println!("Status: {:?}", cs.is_satisfied());

        Ok(Boolean::TRUE)
    }
}
