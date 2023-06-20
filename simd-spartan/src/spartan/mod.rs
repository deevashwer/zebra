use std::collections::VecDeque;
use std::marker::PhantomData;

use ark_ec::AffineCurve;
use ark_ff::{to_bytes, One, Zero};
use ark_marlin::sponge::CryptographicSpongeWithRate;
use ark_marlin::CryptographicSpongeParameters;
use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_sponge::absorb;
use ark_sponge::Absorb;
use ark_sponge::CryptographicSponge;
use ark_std::{end_timer, start_timer};

use crate::hyrax_pc::MVPolyCommitment as Hyrax;
use crate::ip_r1cs::IPForR1CS;
use crate::F;

use self::data_structures::Proof;
use self::data_structures::{IndexProverKey, IndexVerifierKey, InputInstance};
pub mod constraints;
pub mod data_structures;

pub struct Spartan<G: AffineCurve, S: CryptographicSponge> {
    _projective: PhantomData<G>,
    _sponge: PhantomData<S>,
}

pub const SPONGE_RATE: usize = 4;

impl<G: AffineCurve + Absorb, S: CryptographicSpongeWithRate> Spartan<G, S>
where
    <S as CryptographicSponge>::Parameters: CryptographicSpongeParameters,
{
    /// The personalization string for this protocol.
    pub const PROTOCOL_NAME: &'static [u8] = b"SPARTAN-2022";

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier keys.
    pub fn circuit_specific_setup<C: ConstraintSynthesizer<G::ScalarField>>(
        num_copies: usize,
        c: C,
    ) -> Result<(IndexProverKey<G>, IndexVerifierKey<G>), crate::Error> {
        let index_time = start_timer!(|| "Spartan::Index");

        let index = IPForR1CS::<G::ScalarField, S>::index(num_copies, c)?;
        let ck = Hyrax::setup(index.index_info.max_nv());

        let commit_time = start_timer!(|| "Commit to index polynomials");
        let r_m_poly = index.merged_r_m_poly();
        let r_m_comm = Hyrax::commit(&ck, &r_m_poly);
        let r_n_poly = index.merged_r_n_poly();
        let r_n_comm = Hyrax::commit(&ck, &r_n_poly);
        let index_comms = vec![r_m_comm, r_n_comm];
        end_timer!(commit_time);

        let index_vk = IndexVerifierKey {
            index_info: index.index_info,
            index_comms,
            verifier_key: ck.clone(),
        };

        let index_pk = IndexProverKey {
            index,
            index_vk: index_vk.clone(),
            committer_key: ck,
        };

        end_timer!(index_time);

        Ok((index_pk, index_vk))
    }

    pub fn get_input_and_witness<C: ConstraintSynthesizer<G::ScalarField>>(
        index_pk: &IndexProverKey<G>,
        c: C,
        construct_matrices: bool,
    ) -> Result<(Vec<G::ScalarField>, Vec<G::ScalarField>), crate::Error> {
        IPForR1CS::<G::ScalarField, S>::get_input_and_witness(
            &index_pk.index,
            c,
            construct_matrices,
        )
    }

    /// Create a zkSNARK asserting that the constraint system is satisfied.
    pub fn prove(
        index_pk: &IndexProverKey<G>,
        input: &Vec<Vec<G::ScalarField>>,
        witness: VecDeque<Vec<G::ScalarField>>,
    ) -> Result<Proof<G>, crate::Error> {
        let prover_time = start_timer!(|| "Spartan::Prover");
        let prover_init = start_timer!(|| "Spartan::Prover Init");
        let mut prover_state =
            IPForR1CS::<G::ScalarField, S>::prover_init(&index_pk.index, input, witness)?;
        end_timer!(prover_init);
        let public_input = prover_state.v.clone();
        println!(
            "d: {}, n: {}, m: {}, k: {}",
            prover_state.d, prover_state.n, prover_state.m, prover_state.k
        );

        let mut sponge = S::from_rate(SPONGE_RATE);

        absorb!(
            &mut sponge,
            to_bytes!(&Self::PROTOCOL_NAME)?,
            index_pk.index_vk,
            to_bytes!(public_input)?
        );

        // --------------------------------------------------------------------
        // First round

        let prover_first_round = start_timer!(|| "Spartan::Prover First Round");
        let prover_first_oracles =
            IPForR1CS::<G::ScalarField, S>::prover_first_round(&mut prover_state)?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let first_comm_poly = prover_first_oracles.merged_poly();
        let first_comm = Hyrax::commit(&index_pk.committer_key, first_comm_poly);
        end_timer!(first_round_comm_time);

        absorb!(&mut sponge, first_comm);
        let (verifier_first_msg, mut verifier_state) =
            IPForR1CS::verifier_init(index_pk.index_vk.index_info, public_input, &mut sponge)?;
        end_timer!(prover_first_round);

        // Common sumcheck variables
        let mut prover_sumcheck_msgs = Vec::new();
        let n = prover_state.index.index_info.constraints_nv();
        let d = prover_state.d;

        // --------------------------------------------------------------------
        // First sumcheck

        let prover_first_sumcheck = start_timer!(|| "Spartan::Prover First Sumcheck");
        IPForR1CS::<G::ScalarField, S>::prover_first_sumcheck_setup(
            &verifier_first_msg,
            &mut prover_state,
        );

        let mut verifier_sumcheck_msg = None;
        for _ in 0..n + d {
            let p_msg = IPForR1CS::<G::ScalarField, S>::prover_first_sumcheck_round(
                &verifier_sumcheck_msg,
                &mut prover_state,
            )?;
            absorb!(&mut sponge, p_msg);
            prover_sumcheck_msgs.push(p_msg.clone());
            verifier_sumcheck_msg = Some(IPForR1CS::verifier_first_sumcheck_round(
                p_msg,
                &mut verifier_state,
                &mut sponge,
            )?);
        }

        let prover_first_msg = IPForR1CS::<G::ScalarField, S>::prover_first_sumcheck_finalize(
            &verifier_sumcheck_msg.unwrap(),
            &mut prover_state,
        )?;

        absorb!(&mut sponge, prover_first_msg);
        let verifier_second_msg = IPForR1CS::verifier_first_sumcheck_finalize(
            prover_first_msg.clone(),
            &mut verifier_state,
            &mut sponge,
        )?;
        end_timer!(prover_first_sumcheck);
        // println!("first sumcheck done");

        // --------------------------------------------------------------------
        // Second sumcheck

        let prover_second_sumcheck = start_timer!(|| "Spartan::Prover Second Sumcheck");
        IPForR1CS::<G::ScalarField, S>::prover_second_sumcheck_setup(
            verifier_second_msg,
            &mut prover_state,
        );

        let mut verifier_sumcheck_msg = None;
        for _ in 0..n {
            let p_msg = IPForR1CS::<G::ScalarField, S>::prover_second_sumcheck_round(
                &verifier_sumcheck_msg,
                &mut prover_state,
            )?;
            absorb!(&mut sponge, p_msg);
            prover_sumcheck_msgs.push(p_msg.clone());
            verifier_sumcheck_msg = Some(IPForR1CS::verifier_second_sumcheck_round(
                p_msg,
                &mut verifier_state,
                &mut sponge,
            )?);
        }

        let prover_second_msg = IPForR1CS::<G::ScalarField, S>::prover_second_sumcheck_finalize(
            &verifier_sumcheck_msg.unwrap(),
            &mut prover_state,
        )?;

        absorb!(&mut sponge, prover_second_msg);
        let verifier_third_msg = IPForR1CS::verifier_second_sumcheck_finalize(
            prover_second_msg.clone(),
            &mut verifier_state,
            &mut sponge,
        )?;
        end_timer!(prover_second_sumcheck);
        // println!("second sumcheck done");

        // --------------------------------------------------------------------
        // Third sumcheck and GKR (in parallel)

        let mut prover_gkr_msgs = Vec::new();
        let mut prover_gkr_sumcheck_msgs = Vec::new();

        let prover_third_sumcheck_and_gkr =
            start_timer!(|| "Spartan::Prover Third Sumcheck and GKR");

        // Third sumcheck setup
        // doing it first because it sets up some of the state for GKR
        let prover_second_oracles = IPForR1CS::<G::ScalarField, S>::prover_third_sumcheck_setup(
            verifier_third_msg.clone(),
            &mut prover_state,
        )?;
        let second_comm_poly = prover_second_oracles.merged_poly();
        let second_comm = Hyrax::commit(&index_pk.committer_key, &second_comm_poly);
        absorb!(&mut sponge, second_comm);

        // GKR setup
        let mut prover_gkr_msg = IPForR1CS::<G::ScalarField, S>::prover_gkr_setup(
            verifier_third_msg.clone(),
            &mut prover_state,
        )?;
        prover_gkr_msgs.push(prover_gkr_msg.clone());
        absorb!(&mut sponge, prover_gkr_msg);
        let mut verifier_gkr_msg =
            IPForR1CS::verifier_gkr_setup(prover_gkr_msg, &mut verifier_state, &mut sponge)?;

        let m = prover_state.index.index_info.weight_nv();
        let batch_n_nv = prover_state.index.index_info.batch_constraints_poly_nv();
        let batch_m_nv = prover_state.index.index_info.batch_weight_poly_nv();
        // the GKR iterations need to be run for max(m, n) times
        // assuming m is always >= n
        assert!(m >= n);
        assert!(batch_m_nv >= batch_n_nv);
        // first do the first m - 1 sumcheck instances of GKR
        // and then do the last one in parallel with third sumcheck of IP for R1CS
        for i in 0..m - 1 {
            IPForR1CS::<G::ScalarField, S>::prover_gkr_level_sumcheck_setup(
                &verifier_gkr_msg,
                &mut prover_state,
            );
            let mut verifier_sumcheck_msg = None;
            for _ in 0..i + batch_m_nv {
                let p_msg = IPForR1CS::<G::ScalarField, S>::prover_gkr_level_sumcheck_round(
                    &verifier_sumcheck_msg,
                    &mut prover_state,
                )?;
                absorb!(&mut sponge, p_msg);
                prover_gkr_sumcheck_msgs.push(p_msg.clone());
                verifier_sumcheck_msg = Some(IPForR1CS::verifier_gkr_level_sumcheck_round(
                    p_msg,
                    &mut verifier_state,
                    &mut sponge,
                )?);
            }
            prover_gkr_msg = IPForR1CS::<G::ScalarField, S>::prover_gkr_level_sumcheck_finalize(
                verifier_sumcheck_msg.as_ref().unwrap(),
                &mut prover_state,
            )?;
            prover_gkr_msgs.push(prover_gkr_msg.clone());
            absorb!(&mut sponge, prover_gkr_msg);
            verifier_gkr_msg = IPForR1CS::verifier_gkr_level_sumcheck_finalize(
                prover_gkr_msg,
                &mut verifier_state,
                &mut sponge,
            )?;
        }
        // setup the last sumcheck instance for GKR
        IPForR1CS::<G::ScalarField, S>::prover_gkr_level_sumcheck_setup(
            &verifier_gkr_msg,
            &mut prover_state,
        );
        // the first m-1 iterations of the third sumcheck are run in parallel with the first m-1 iterations of the final sumcheck of GKR
        let mut verifier_sumcheck_msg = None;
        let mut verifier_sumcheck_msg_gkr = None;
        for _ in 0..m - 1 {
            let p_msg_1 = IPForR1CS::<G::ScalarField, S>::prover_third_sumcheck_round(
                &verifier_sumcheck_msg,
                &mut prover_state,
            )?;
            let p_msg_2 = IPForR1CS::<G::ScalarField, S>::prover_gkr_level_sumcheck_round(
                &verifier_sumcheck_msg_gkr,
                &mut prover_state,
            )?;
            absorb!(&mut sponge, p_msg_1, p_msg_2);
            prover_sumcheck_msgs.push(p_msg_1.clone());
            prover_gkr_sumcheck_msgs.push(p_msg_2.clone());
            let mut sponge_clone = sponge.clone();
            verifier_sumcheck_msg = Some(IPForR1CS::verifier_third_sumcheck_round(
                p_msg_1,
                &mut verifier_state,
                &mut sponge_clone,
            )?);
            let mut sponge_clone = sponge.clone();
            verifier_sumcheck_msg_gkr = Some(IPForR1CS::verifier_gkr_level_sumcheck_round(
                p_msg_2,
                &mut verifier_state,
                &mut sponge_clone,
            )?);
            assert!(verifier_sumcheck_msg == verifier_sumcheck_msg_gkr);
        }
        // then perform the next batch_m_nv iterations of final sumcheck of GKR
        for _ in 0..batch_m_nv {
            let p_msg = IPForR1CS::<G::ScalarField, S>::prover_gkr_level_sumcheck_round(
                &verifier_sumcheck_msg_gkr,
                &mut prover_state,
            )?;
            absorb!(&mut sponge, p_msg);
            prover_gkr_sumcheck_msgs.push(p_msg.clone());
            verifier_sumcheck_msg_gkr = Some(IPForR1CS::verifier_gkr_level_sumcheck_round(
                p_msg,
                &mut verifier_state,
                &mut sponge,
            )?);
        }
        // now the last iteration of both third sumcheck and final sumcheck of GKR which is different from others
        let p_msg = IPForR1CS::<G::ScalarField, S>::prover_third_sumcheck_round(
            &verifier_sumcheck_msg,
            &mut prover_state,
        )?;
        prover_gkr_msg = IPForR1CS::<G::ScalarField, S>::prover_gkr_level_sumcheck_finalize(
            &verifier_sumcheck_msg_gkr.unwrap(),
            &mut prover_state,
        )?;
        absorb!(&mut sponge, p_msg, prover_gkr_msg);
        prover_sumcheck_msgs.push(p_msg.clone());
        prover_gkr_msgs.push(prover_gkr_msg.clone());
        let mut sponge_clone = sponge.clone();
        verifier_sumcheck_msg = Some(IPForR1CS::verifier_third_sumcheck_round(
            p_msg,
            &mut verifier_state,
            &mut sponge_clone,
        )?);
        let mut sponge_clone = sponge.clone();
        verifier_gkr_msg = IPForR1CS::verifier_gkr_level_sumcheck_finalize(
            prover_gkr_msg,
            &mut verifier_state,
            &mut sponge_clone,
        )?;
        assert!(
            verifier_sumcheck_msg.as_ref().unwrap().challenge == verifier_gkr_msg.challenges[0]
        );

        // finalize the third sumcheck instance prover
        let prover_third_msg = IPForR1CS::<G::ScalarField, S>::prover_third_sumcheck_finalize(
            verifier_sumcheck_msg.as_ref().unwrap(),
            &mut prover_state,
        )?;
        // finalize the GKR instance prover
        let prover_fourth_msg = IPForR1CS::<G::ScalarField, S>::prover_gkr_finalize(
            &verifier_gkr_msg,
            &mut prover_state,
        )?;

        absorb!(
            &mut sponge,
            prover_third_msg.clone(),
            prover_fourth_msg.clone()
        );
        // finalize the third sumcheck instance verifier
        IPForR1CS::verifier_third_sumcheck_finalize(
            prover_third_msg.clone(),
            &mut verifier_state,
            &mut sponge,
        )?;
        // finalize the GKR instance verifier
        let verifier_fourth_msg = IPForR1CS::verifier_gkr_finalize(
            prover_third_msg.clone(),
            prover_fourth_msg.clone(),
            &mut verifier_state,
            &mut sponge,
        )?;

        end_timer!(prover_third_sumcheck_and_gkr);

        // --------------------------------------------------------------------
        // Poly Commitment Checks
        let mut r_m = prover_state.r_m.as_ref().unwrap().clone();
        let mut r_n = prover_state.r_n.as_ref().unwrap().clone();
        let r_m_ext = verifier_fourth_msg.r_m_ext;
        let r_n_ext = verifier_fourth_msg.r_n_ext;
        r_m.extend(&r_m_ext);
        r_n.extend(&r_n_ext);

        // ignoring the final r_y challenge used to fold input and witness
        let mut r_yd = prover_state.r_y.as_ref().unwrap()[..n - 1].to_vec();
        r_yd.extend(prover_state.r_d.as_ref().unwrap());
        let prover_pc_proof_ryd = start_timer!(|| "Spartan::Prover PC Proof r_yd");
        let pc_proof_ryd = Hyrax::open(&index_pk.committer_key, &first_comm_poly, &r_yd);
        end_timer!(prover_pc_proof_ryd);

        let prover_pc_proof_rm = start_timer!(|| "Spartan::Prover PC Proof r_m");
        let pc_proof_rm = Hyrax::batch_open(
            &index_pk.committer_key,
            vec![&second_comm_poly, &index_pk.index.merged_r_m_poly()],
            vec![F::<G>::one(), verifier_fourth_msg.r_m_lin_comb],
            &r_m,
        );
        end_timer!(prover_pc_proof_rm);

        let prover_pc_proof_rn = start_timer!(|| "Spartan::Prover PC Proof r_n");
        let pc_proof_rn = Hyrax::open(
            &index_pk.committer_key,
            &index_pk.index.merged_r_n_poly(),
            &r_n,
        );
        end_timer!(prover_pc_proof_rn);
        end_timer!(prover_time);

        Ok(Proof {
            first_oracles: first_comm,
            second_oracles: second_comm,
            prover_sumcheck_messages: prover_sumcheck_msgs,
            prover_gkr_sumcheck_messages: prover_gkr_sumcheck_msgs,
            prover_gkr_messages: prover_gkr_msgs,
            prover_first_message: prover_first_msg,
            prover_second_message: prover_second_msg,
            prover_third_message: prover_third_msg,
            prover_fourth_message: prover_fourth_msg,
            pc_proof_ryd,
            pc_proof_rm,
            pc_proof_rn,
        })
    }

    pub fn verify(
        index_vk: &IndexVerifierKey<G>,
        public_input: InputInstance<F<G>>,
        proof: &Proof<G>,
    ) -> Result<bool, crate::Error> {
        let verifier_time = start_timer!(|| "Spartan::Verifier");
        let verifier_init = start_timer!(|| "Spartan::Verifier Init");

        let mut sponge = S::from_rate(SPONGE_RATE);

        absorb!(
            &mut sponge,
            to_bytes!(&Self::PROTOCOL_NAME)?,
            index_vk,
            public_input
        );
        absorb!(&mut sponge, proof.first_oracles);
        let (_, mut verifier_state) = IPForR1CS::verifier_init(
            index_vk.index_info,
            public_input.formatted_input,
            &mut sponge,
        )?;
        end_timer!(verifier_init);

        // Common sumcheck variables
        let d = verifier_state.d;
        let n = verifier_state.index_info.constraints_nv();
        let mut idx_sumcheck = 0;
        let mut idx_gkr_sumcheck = 0;
        let mut idx_gkr = 0;

        // --------------------------------------------------------------------
        // First sumcheck

        let verifier_first_sumcheck = start_timer!(|| "Spartan::Verifier First Sumcheck");
        for _ in 0..n + d {
            let p_msg = proof.prover_sumcheck_messages[idx_sumcheck].clone();
            absorb!(&mut sponge, p_msg);
            IPForR1CS::verifier_first_sumcheck_round(p_msg, &mut verifier_state, &mut sponge)?;
            idx_sumcheck += 1;
        }

        let prover_first_msg = proof.prover_first_message.clone();
        absorb!(&mut sponge, prover_first_msg);
        IPForR1CS::verifier_first_sumcheck_finalize(
            prover_first_msg.clone(),
            &mut verifier_state,
            &mut sponge,
        )?;
        end_timer!(verifier_first_sumcheck);

        // --------------------------------------------------------------------
        // Second sumcheck

        let verifier_second_sumcheck = start_timer!(|| "Spartan::Verifier Second Sumcheck");

        for _ in 0..n {
            let p_msg = proof.prover_sumcheck_messages[idx_sumcheck].clone();
            absorb!(&mut sponge, p_msg);
            IPForR1CS::verifier_second_sumcheck_round(p_msg, &mut verifier_state, &mut sponge)?;
            idx_sumcheck += 1;
        }

        let prover_second_msg = proof.prover_second_message.clone();
        absorb!(&mut sponge, prover_second_msg);
        IPForR1CS::verifier_second_sumcheck_finalize(
            prover_second_msg.clone(),
            &mut verifier_state,
            &mut sponge,
        )?;
        end_timer!(verifier_second_sumcheck);

        // --------------------------------------------------------------------
        // Third sumcheck and GKR (in parallel)

        let verifier_third_sumcheck_and_gkr =
            start_timer!(|| "Spartan::Verifier Third Sumcheck and GKR");

        absorb!(&mut sponge, proof.second_oracles);

        let prover_gkr_msg = proof.prover_gkr_messages[idx_gkr].clone();
        idx_gkr += 1;
        absorb!(&mut sponge, prover_gkr_msg);
        IPForR1CS::verifier_gkr_setup(prover_gkr_msg, &mut verifier_state, &mut sponge)?;

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
            for _ in 0..i + batch_m_nv {
                let p_msg = proof.prover_gkr_sumcheck_messages[idx_gkr_sumcheck].clone();
                idx_gkr_sumcheck += 1;
                absorb!(&mut sponge, p_msg);
                IPForR1CS::verifier_gkr_level_sumcheck_round(
                    p_msg,
                    &mut verifier_state,
                    &mut sponge,
                )?;
            }
            let prover_gkr_msg = proof.prover_gkr_messages[idx_gkr].clone();
            idx_gkr += 1;
            absorb!(&mut sponge, prover_gkr_msg);
            IPForR1CS::verifier_gkr_level_sumcheck_finalize(
                prover_gkr_msg,
                &mut verifier_state,
                &mut sponge,
            )?;
        }
        // the first m-1 iterations of the third sumcheck are run in parallel with the first m-1 iterations of the final sumcheck of GKR
        for _ in 0..m - 1 {
            let p_msg_1 = proof.prover_sumcheck_messages[idx_sumcheck].clone();
            idx_sumcheck += 1;
            let p_msg_2 = proof.prover_gkr_sumcheck_messages[idx_gkr_sumcheck].clone();
            idx_gkr_sumcheck += 1;
            absorb!(&mut sponge, p_msg_1, p_msg_2);
            let mut sponge_clone = sponge.clone();
            IPForR1CS::verifier_third_sumcheck_round(
                p_msg_1,
                &mut verifier_state,
                &mut sponge_clone,
            )?;
            let mut sponge_clone = sponge.clone();
            IPForR1CS::verifier_gkr_level_sumcheck_round(
                p_msg_2,
                &mut verifier_state,
                &mut sponge_clone,
            )?;
        }
        // then perform the next batch_m_nv iterations of final sumcheck of GKR
        for _ in 0..batch_m_nv {
            let p_msg = proof.prover_gkr_sumcheck_messages[idx_gkr_sumcheck].clone();
            idx_gkr_sumcheck += 1;
            absorb!(&mut sponge, p_msg);
            IPForR1CS::verifier_gkr_level_sumcheck_round(p_msg, &mut verifier_state, &mut sponge)?;
        }
        // now the last iteration which is different from others
        let p_msg = proof.prover_sumcheck_messages[idx_sumcheck].clone();
        let prover_gkr_msg = proof.prover_gkr_messages[idx_gkr].clone();
        absorb!(&mut sponge, p_msg, prover_gkr_msg);
        let mut sponge_clone = sponge.clone();
        IPForR1CS::verifier_third_sumcheck_round(p_msg, &mut verifier_state, &mut sponge_clone)?;
        let mut sponge_clone = sponge.clone();
        IPForR1CS::verifier_gkr_level_sumcheck_finalize(
            prover_gkr_msg,
            &mut verifier_state,
            &mut sponge_clone,
        )?;

        absorb!(
            &mut sponge,
            proof.prover_third_message.clone(),
            proof.prover_fourth_message.clone()
        );
        // finalize the third sumcheck instance verifier
        IPForR1CS::verifier_third_sumcheck_finalize(
            proof.prover_third_message.clone(),
            &mut verifier_state,
            &mut sponge,
        )?;
        // finalize the GKR instance verifier
        let verifier_fourth_msg = IPForR1CS::verifier_gkr_finalize(
            proof.prover_third_message.clone(),
            proof.prover_fourth_message.clone(),
            &mut verifier_state,
            &mut sponge,
        )?;

        end_timer!(verifier_third_sumcheck_and_gkr);

        // --------------------------------------------------------------------
        // Poly Commitment Checks
        let mut r_m = verifier_state.r_m.as_ref().unwrap().clone();
        let mut r_n = verifier_state.r_n.as_ref().unwrap().clone();
        let r_m_ext = verifier_fourth_msg.r_m_ext;
        let r_n_ext = verifier_fourth_msg.r_n_ext;

        // computing v_m_1
        let mut v_m_vec_1 = vec![F::<G>::zero(); 8];
        v_m_vec_1.extend(proof.prover_third_message.first_iter());
        v_m_vec_1.extend(vec![F::<G>::zero(); 2]);
        let v_m_mle_1 = DenseMultilinearExtension {
            evaluations: v_m_vec_1,
            num_vars: 4,
        };
        let v_m_1 = v_m_mle_1.evaluate(&r_m_ext).unwrap();

        // computing v_m_2
        let mut v_m_vec_2 = proof.prover_third_message.second_iter();
        v_m_vec_2.extend(proof.prover_fourth_message.first_iter());
        v_m_vec_2.extend(vec![F::<G>::zero(); 3]);
        let v_m_mle_2 = DenseMultilinearExtension {
            evaluations: v_m_vec_2,
            num_vars: 4,
        };
        let v_m_2 = v_m_mle_2.evaluate(&r_m_ext).unwrap();

        // computing v_n
        let mut v_n_vec = proof.prover_fourth_message.second_iter();
        v_n_vec.extend(vec![F::<G>::zero(); 2]);
        let v_n_mle = DenseMultilinearExtension {
            evaluations: v_n_vec,
            num_vars: 3,
        };
        let v_n = v_n_mle.evaluate(&r_n_ext).unwrap();

        // final challenges r_m and r_n
        r_m.extend(&r_m_ext);
        r_n.extend(&r_n_ext);

        // ignoring the final r_y challenge used to fold input and witness
        let mut r_yd = verifier_state.r_y.as_ref().unwrap()[..n - 1].to_vec();
        r_yd.extend(verifier_state.r_d.as_ref().unwrap());
        let verifier_pc_proof_ryd = start_timer!(|| "Spartan::Verifier PC Proof r_yd");
        let proof_ry = Hyrax::check(
            &index_vk.verifier_key,
            &&proof.first_oracles,
            &r_yd,
            verifier_state.v_w.unwrap(),
            &proof.pc_proof_ryd,
        );
        end_timer!(verifier_pc_proof_ryd);

        let verifier_pc_proof_rm = start_timer!(|| "Spartan::Verifier PC Proof r_m");
        let proof_rm = Hyrax::batch_check(
            &index_vk.verifier_key,
            vec![&proof.second_oracles, &index_vk.index_comms[0]],
            vec![F::<G>::one(), verifier_fourth_msg.r_m_lin_comb],
            &r_m,
            vec![v_m_1, v_m_2],
            &proof.pc_proof_rm,
        );
        end_timer!(verifier_pc_proof_rm);

        let verifier_pc_proof_rn = start_timer!(|| "Spartan::Verifier PC Proof r_n");
        let proof_rn = Hyrax::check(
            &index_vk.verifier_key,
            &index_vk.index_comms[1],
            &r_n,
            v_n,
            &proof.pc_proof_rn,
        );
        end_timer!(verifier_pc_proof_rn);
        end_timer!(verifier_time);

        assert!(proof_ry, "PC Proof r_y failed");
        assert!(proof_rm, "PC Proof r_m failed");
        assert!(proof_rn, "PC Proof r_n failed");

        Ok(true)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_ff::{Field, PrimeField};
    use ark_nonnative_field::NonNativeFieldVar;
    use ark_r1cs_std::alloc::AllocationMode;
    use ark_relations::{
        lc,
        r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
    };
    use ark_sponge::poseidon::PoseidonSponge;

    use crate::spartan::constraints::IndexVerifierKeyVar;
    use crate::spartan::constraints::InputInstanceVar;
    use crate::spartan::constraints::ProofVar;
    use crate::spartan::constraints::SpartanVar;
    use ark_ff::UniformRand;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::boolean::Boolean;
    use ark_r1cs_std::prelude::EqGadget;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_std::cfg_iter;
    use ark_std::ops::MulAssign;
    use ark_std::rand::RngCore;
    #[cfg(feature = "parallel")]
    use rayon::prelude::*;

    // use ark_bls12_377::{Fq, Fr, G1Affine as GAffine};
    // type C = ark_bls12_377::constraints::G1Var;

    use ark_grumpkin::{fq::Fq, fr::Fr, Affine as GAffine};
    type C = ark_grumpkin::constraints::GVar;

    type F = Fr;
    type CF = Fq;
    type S = PoseidonSponge<CF>;
    type SpartanInst = Spartan<GAffine, S>;
    type SpartanInstVar = SpartanVar<GAffine, C, S, PoseidonSpongeVar<CF>>;

    #[derive(Copy, Clone)]
    struct Circuit<F: Field> {
        a: Option<F>,
        b: Option<F>,
        num_constraints: usize,
        num_witness: usize,
        num_inputs: usize,
    }

    impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for Circuit<ConstraintF> {
        fn generate_constraints(
            self,
            cs: ConstraintSystemRef<ConstraintF>,
        ) -> Result<(), SynthesisError> {
            let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
            let a_native = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b_native = self.b.ok_or(SynthesisError::AssignmentMissing)?;
            let c_native = a_native * b_native;
            let c = cs.new_input_variable(|| Ok(c_native))?;

            for _ in 0..(self.num_inputs - 1) {
                cs.new_input_variable(|| Ok(c_native))?;
            }

            for _ in 0..(self.num_witness - 3) {
                cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
            }

            for _ in 0..self.num_constraints {
                cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)
                    .unwrap();
            }
            Ok(())
        }
    }

    fn test_circuit(
        num_copies: usize,
        num_constraints: usize,
        num_witness: usize,
        num_inputs: usize,
    ) {
        let rng = &mut ark_std::test_rng();

        let a = Fr::rand(rng);
        let b = Fr::rand(rng);
        let mut c = a;
        c.mul_assign(&b);

        let circ_time = start_timer!(|| "Spartan::Circuit Construction");
        let circ = Circuit {
            a: Some(a),
            b: Some(b),
            num_constraints,
            num_witness,
            num_inputs,
        };
        end_timer!(circ_time);

        let (index_pk, index_vk) = SpartanInst::circuit_specific_setup(num_copies, circ).unwrap();
        println!("Called index");

        let construct_z = start_timer!(|| "Spartan::Prover Witness Construction");
        let index = (0..num_copies).collect::<Vec<usize>>();
        let (input, witness) = cfg_iter!(index)
            .map(|i| {
                let rng = &mut ark_std::test_rng();
                for _ in 0..*i {
                    rng.next_u64();
                }
                let a = Fr::rand(rng);
                let b = Fr::rand(rng);
                let mut c = a;
                c.mul_assign(&b);

                let circ_i = Circuit {
                    a: Some(a),
                    b: Some(b),
                    num_constraints,
                    num_witness,
                    num_inputs,
                };
                if *i == 0 {
                    SpartanInst::get_input_and_witness(&index_pk, circ_i, true).unwrap()
                } else {
                    SpartanInst::get_input_and_witness(&index_pk, circ_i, false).unwrap()
                }
            })
            .unzip();
        end_timer!(construct_z);

        let proof = SpartanInst::prove(&index_pk, &input, witness).unwrap();
        println!("Called prover");

        let public_input: InputInstance<F> = InputInstance::new(input);
        let res = SpartanInst::verify(&index_vk, public_input.clone(), &proof).is_ok();
        println!("Called verifier; Result: {}", res);
        assert!(res, "Verification Failed");

        let cs = ConstraintSystem::<CF>::new_ref();

        let index_vk_var =
            IndexVerifierKeyVar::<GAffine, C>::new_constant(cs.clone(), index_vk.clone()).unwrap();
        let public_input_var =
            InputInstanceVar::<GAffine>::new_input(cs.clone(), || Ok(public_input)).unwrap();
        let proof_var = ProofVar::<GAffine, C>::new_witness(cs.clone(), || Ok(proof)).unwrap();

        let start_cost = cs.num_constraints();
        SpartanInstVar::verify(cs.clone(), &index_vk_var, &public_input_var, &proof_var)
            .unwrap()
            .enforce_equal(&Boolean::TRUE)
            .unwrap();
        println!(
            "Cost of verifying Spartan proof {:?}",
            cs.num_constraints() - start_cost
        );

        println!("Num constaints: {:}", cs.num_constraints());
        println!("Num instance: {:}", cs.num_instance_variables());
        println!("Num witness: {:}", cs.num_witness_variables());

        // assert!(cs.is_satisfied().unwrap());

        // println!("\nShould not verify (i.e. verifier messages should print below):");
        // assert!(SpartanInst::verify(&index_vk, vec![a, a], &proof).is_err());
    }

    #[derive(Copy, Clone)]
    struct NonNativeAddCircuit<TargetField: PrimeField, BaseField: PrimeField> {
        a: TargetField,
        b: TargetField,
        c: TargetField,
        _base_field: PhantomData<BaseField>,
    }

    impl<TargetField: PrimeField, BaseField: PrimeField> ConstraintSynthesizer<BaseField>
        for NonNativeAddCircuit<TargetField, BaseField>
    {
        fn generate_constraints(
            self,
            cs: ConstraintSystemRef<BaseField>,
        ) -> Result<(), SynthesisError> {
            let a = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
                ark_relations::ns!(cs, "alloc a"),
                || Ok(self.a),
            )?;
            let b = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
                ark_relations::ns!(cs, "alloc b"),
                || Ok(self.b),
            )?;
            let c = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
                ark_relations::ns!(cs, "alloc c"),
                || Ok(self.c),
            )?;

            let a_plus_b = a + &b;

            c.enforce_equal(&a_plus_b)?;
            Ok(())
        }
    }

    fn spartan_nonnative_add_circuit() {
        let rng = &mut ark_std::test_rng();
        let num_copies = 1;

        let a = Fq::rand(rng);
        let b = Fq::rand(rng);
        let c = a + b;

        let circ_time = start_timer!(|| "Spartan::Circuit Construction");
        let circ = NonNativeAddCircuit::<Fq, Fr> {
            a,
            b,
            c,
            _base_field: PhantomData::<Fr>,
        };
        end_timer!(circ_time);

        let (index_pk, index_vk) = SpartanInst::circuit_specific_setup(num_copies, circ).unwrap();
        println!("Called index");

        let construct_z = start_timer!(|| "Spartan::Prover Witness Construction");
        let index = (0..num_copies).collect::<Vec<usize>>();
        let (input, witness) = cfg_iter!(index)
            .map(|i| {
                let rng = &mut ark_std::test_rng();
                for _ in 0..*i {
                    rng.next_u64();
                }
                let a = Fq::rand(rng);
                let b = Fq::rand(rng);
                let c = a + b;

                let circ_i = NonNativeAddCircuit::<Fq, Fr> {
                    a,
                    b,
                    c,
                    _base_field: PhantomData::<Fr>,
                };
                if *i == 0 {
                    SpartanInst::get_input_and_witness(&index_pk, circ_i, true).unwrap()
                } else {
                    SpartanInst::get_input_and_witness(&index_pk, circ_i, false).unwrap()
                }
            })
            .unzip();
        end_timer!(construct_z);

        let proof = SpartanInst::prove(&index_pk, &input, witness).unwrap();
        println!("Called prover");

        let public_input: InputInstance<F> = InputInstance::new(input);
        let res = SpartanInst::verify(&index_vk, public_input.clone(), &proof).is_ok();
        println!("Called verifier; Result: {}", res);
        assert!(res, "Verification Failed");

        let cs = ConstraintSystem::<CF>::new_ref();

        let index_vk_var =
            IndexVerifierKeyVar::<GAffine, C>::new_constant(cs.clone(), index_vk.clone()).unwrap();
        let public_input_var =
            InputInstanceVar::<GAffine>::new_input(cs.clone(), || Ok(public_input)).unwrap();
        let proof_var = ProofVar::<GAffine, C>::new_witness(cs.clone(), || Ok(proof)).unwrap();

        let start_cost = cs.num_constraints();
        SpartanInstVar::verify(cs.clone(), &index_vk_var, &public_input_var, &proof_var)
            .unwrap()
            .enforce_equal(&Boolean::TRUE)
            .unwrap();
        println!(
            "Cost of verifying Spartan proof {:?}",
            cs.num_constraints() - start_cost
        );

        println!("Num constaints: {:}", cs.num_constraints());
        println!("Num instance: {:}", cs.num_instance_variables());
        println!("Num witness: {:}", cs.num_witness_variables());
    }

    #[test]
    fn test_big_circuit() {
        let num_constraints = 1 << 19;
        let num_witness = 1 << 18;
        let num_inputs = 16;
        let num_copies = 512;

        test_circuit(num_copies, num_constraints, num_witness, num_inputs);
    }

    #[test]
    fn test_med_circuit() {
        let num_constraints = 1 << 12;
        let num_witness = 1 << 11;
        let num_inputs = 16;
        let num_copies = 64;

        test_circuit(num_copies, num_constraints, num_witness, num_inputs);
    }

    #[test]
    fn test_small_circuit() {
        let num_constraints = 1 << 6;
        let num_witness = 1 << 5;
        let num_inputs = 6;
        let num_copies = 4;

        test_circuit(num_copies, num_constraints, num_witness, num_inputs);
    }

    #[test]
    fn test_nonnative_add_circuit() {
        spartan_nonnative_add_circuit();
    }
}
