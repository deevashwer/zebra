use std::borrow::Borrow;
use std::marker::PhantomData;

use super::verifier::{P1, P2, P3};
use crate::dense_mle::DenseMLEVar;
use crate::gkr_grand_product::constraints::{
    BatchProverMsgVar as GKRBatchProverMsgVar, BatchVerifierMsgVar as GKRBatchVerifierMsgVar,
    BatchVerifierStateVar as GKRBatchVerifierStateVar, GKRVar,
};
use crate::ip_r1cs::prover::{ProverFirstMsg, ProverFourthMsg, ProverSecondMsg, ProverThirdMsg};
use crate::sumcheck::constraints::{
    IPForMVSumcheckVar, ProverMsgVar as SumcheckProverMsgVar,
    VerifierMsgVar as SumcheckVerifierMsgVar, VerifierStateVar as SumcheckVerifierStateVar,
};
use crate::NonNativeVar;
use crate::CF;
use crate::CHALLENGE_SIZE;
use crate::F;
use ark_ec::AffineCurve;
use ark_ff::{One, Zero};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::alloc::AllocationMode;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::{EqGadget, UInt8};
use ark_r1cs_std::ToBytesGadget;
use ark_relations::r1cs::Namespace;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::{AbsorbGadget, CryptographicSpongeVar};
use ark_sponge::{collect_sponge_field_elements_gadget, CryptographicSponge};

use super::indexer::IndexInfo;

pub struct VerifierStateVar<G: AffineCurve> {
    /// log(number of data-parallel instances)
    pub d: usize,
    /// log(|padded_v|+|w|)
    pub n: usize,
    /// log(|v|)
    pub k: usize,
    /// log(num_non_zero)
    pub m: usize,
    pub index_info: IndexInfo<F<G>>,
    /// Input Assignment
    pub v: Vec<Vec<NonNativeVar<G>>>,
    pub tau: Vec<NonNativeVar<G>>,
    // For combining z_i's
    pub r_d: Option<Vec<NonNativeVar<G>>>,
    // challenges from initial sumcheck over x
    pub r_x: Option<Vec<NonNativeVar<G>>>,
    // For combining sumcheck over y
    pub r_a_y: Option<NonNativeVar<G>>,
    pub r_b_y: Option<NonNativeVar<G>>,
    pub r_c_y: Option<NonNativeVar<G>>,
    // sumcheck challenges kept in boolean format for efficiency while opening
    pub r_y: Option<Vec<NonNativeVar<G>>>,
    pub r_m: Option<Vec<NonNativeVar<G>>>,
    pub r_n: Option<Vec<NonNativeVar<G>>>,
    // W(r_y) = v_w,
    pub v_w: Option<NonNativeVar<G>>,
    // For combining sumcheck over h
    pub r_a_spark: Option<NonNativeVar<G>>,
    pub r_b_spark: Option<NonNativeVar<G>>,
    pub r_c_spark: Option<NonNativeVar<G>>,
    // For combining GKR claims
    pub gamma_1: Option<NonNativeVar<G>>,
    pub gamma_2: Option<NonNativeVar<G>>,
    // sumcheck states
    pub first_sumcheck_state: SumcheckVerifierStateVar<G>,
    pub second_sumcheck_state: Option<SumcheckVerifierStateVar<G>>,
    pub third_sumcheck_state: Option<SumcheckVerifierStateVar<G>>,
    /// Current GKR Level
    pub curr_gkr_level: usize,
    /// GKR States for products of size 2^n
    pub gkr_state_n: Option<GKRBatchVerifierStateVar<G>>,
    /// GKR States for products of size 2^m
    pub gkr_state_m: Option<GKRBatchVerifierStateVar<G>>,
}

#[derive(Clone)]
pub struct VerifierFirstMsgVar<G: AffineCurve> {
    /// for checking Q(t) = \sum_x F(x)*eq(x, t) on a random point tau
    pub tau: Vec<NonNativeVar<G>>,
}

#[derive(Clone)]
pub struct VerifierSecondMsgVar<G: AffineCurve> {
    /// for linearly combining a_r_x(y), b_r_x(y), c_r_x(y)
    pub r_a_y: NonNativeVar<G>,
    pub r_b_y: NonNativeVar<G>,
    pub r_c_y: NonNativeVar<G>,
}

#[derive(Clone)]
pub struct VerifierThirdMsgVar<G: AffineCurve> {
    /// for linearly combining val_m(h) * m_e_rx(h) * m_e_ry(h) for m \in {a, b, c}
    pub r_a_spark: NonNativeVar<G>,
    pub r_b_spark: NonNativeVar<G>,
    pub r_c_spark: NonNativeVar<G>,
    /// for linearly combining elements of tuples in
    /// Init Set (Init), Read Set (RS), Write Set (WS), and Final Set (Final)
    pub gamma_1: NonNativeVar<G>,
    pub gamma_2: NonNativeVar<G>,
}

#[derive(Clone)]
pub struct VerifierFourthMsgVar<G: AffineCurve> {
    /// for linearly combining r_m commitments
    pub r_m_lin_comb: NonNativeVar<G>,
    pub r_m_ext: Vec<NonNativeVar<G>>,
    pub r_n_ext: Vec<NonNativeVar<G>>,
}

#[derive(Clone)]
pub struct ProverFirstMsgVar<G: AffineCurve> {
    pub v_a_x: NonNativeVar<G>,
    pub v_b_x: NonNativeVar<G>,
    pub v_c_x: NonNativeVar<G>,
}

impl<G: AffineCurve> AllocVar<ProverFirstMsg<F<G>>, CF<G>> for ProverFirstMsgVar<G> {
    fn new_variable<T: Borrow<ProverFirstMsg<F<G>>>>(
        cs: impl Into<Namespace<CF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|msg| {
            let msg = msg.borrow();
            let v_a_x: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_a_x), mode)?;
            let v_b_x: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_b_x), mode)?;
            let v_c_x: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_c_x), mode)?;
            Ok(Self {
                v_a_x,
                v_b_x,
                v_c_x,
            })
        })
    }
}

impl<G: AffineCurve> AbsorbGadget<CF<G>> for ProverFirstMsgVar<G> {
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<CF<G>>>, SynthesisError> {
        let mut msg_bytes = Vec::new();
        msg_bytes.append(&mut self.v_a_x.to_bytes()?);
        msg_bytes.append(&mut self.v_b_x.to_bytes()?);
        msg_bytes.append(&mut self.v_c_x.to_bytes()?);
        collect_sponge_field_elements_gadget!(msg_bytes)
    }

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<CF<G>>>, SynthesisError> {
        todo!()
    }
}

#[derive(Clone)]
pub struct ProverSecondMsgVar<G: AffineCurve> {
    pub v_a_y: NonNativeVar<G>,
    pub v_b_y: NonNativeVar<G>,
    pub v_c_y: NonNativeVar<G>,
    pub v_w_y: NonNativeVar<G>,
}

impl<G: AffineCurve> AllocVar<ProverSecondMsg<F<G>>, CF<G>> for ProverSecondMsgVar<G> {
    fn new_variable<T: Borrow<ProverSecondMsg<F<G>>>>(
        cs: impl Into<Namespace<CF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|msg| {
            let msg = msg.borrow();
            let v_a_y: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_a_y), mode)?;
            let v_b_y: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_b_y), mode)?;
            let v_c_y: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_c_y), mode)?;
            let v_w_y: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_w_y), mode)?;
            Ok(Self {
                v_a_y,
                v_b_y,
                v_c_y,
                v_w_y,
            })
        })
    }
}

impl<G: AffineCurve> AbsorbGadget<CF<G>> for ProverSecondMsgVar<G> {
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<CF<G>>>, SynthesisError> {
        let mut msg_bytes = Vec::new();
        msg_bytes.append(&mut self.v_a_y.to_bytes()?);
        msg_bytes.append(&mut self.v_b_y.to_bytes()?);
        msg_bytes.append(&mut self.v_c_y.to_bytes()?);
        msg_bytes.append(&mut self.v_w_y.to_bytes()?);
        collect_sponge_field_elements_gadget!(msg_bytes)
    }

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<CF<G>>>, SynthesisError> {
        todo!()
    }
}

#[derive(Clone)]
pub struct ProverThirdMsgVar<G: AffineCurve> {
    pub v_a_rx: NonNativeVar<G>,
    pub v_b_rx: NonNativeVar<G>,
    pub v_c_rx: NonNativeVar<G>,
    pub v_a_ry: NonNativeVar<G>,
    pub v_b_ry: NonNativeVar<G>,
    pub v_c_ry: NonNativeVar<G>,
    pub v_a_val: NonNativeVar<G>,
    pub v_b_val: NonNativeVar<G>,
    pub v_c_val: NonNativeVar<G>,
}

impl<G: AffineCurve> ProverThirdMsgVar<G> {
    pub fn first_iter(&self) -> Vec<NonNativeVar<G>> {
        vec![
            self.v_a_rx.clone(),
            self.v_b_rx.clone(),
            self.v_c_rx.clone(),
            self.v_a_ry.clone(),
            self.v_b_ry.clone(),
            self.v_c_ry.clone(),
        ]
    }

    pub fn second_iter(&self) -> Vec<NonNativeVar<G>> {
        vec![
            self.v_a_val.clone(),
            self.v_b_val.clone(),
            self.v_c_val.clone(),
        ]
    }
}

impl<G: AffineCurve> AllocVar<ProverThirdMsg<F<G>>, CF<G>> for ProverThirdMsgVar<G> {
    fn new_variable<T: Borrow<ProverThirdMsg<F<G>>>>(
        cs: impl Into<Namespace<CF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|msg| {
            let msg = msg.borrow();
            let v_a_rx: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_a_rx), mode)?;
            let v_b_rx: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_b_rx), mode)?;
            let v_c_rx: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_c_rx), mode)?;
            let v_a_ry: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_a_ry), mode)?;
            let v_b_ry: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_b_ry), mode)?;
            let v_c_ry: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_c_ry), mode)?;
            let v_a_val: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_a_val), mode)?;
            let v_b_val: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_b_val), mode)?;
            let v_c_val: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_c_val), mode)?;
            Ok(Self {
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
        })
    }
}

impl<G: AffineCurve> AbsorbGadget<CF<G>> for ProverThirdMsgVar<G> {
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<CF<G>>>, SynthesisError> {
        let mut msg_bytes = Vec::new();
        msg_bytes.append(&mut self.v_a_rx.to_bytes()?);
        msg_bytes.append(&mut self.v_b_rx.to_bytes()?);
        msg_bytes.append(&mut self.v_c_rx.to_bytes()?);
        msg_bytes.append(&mut self.v_a_ry.to_bytes()?);
        msg_bytes.append(&mut self.v_b_ry.to_bytes()?);
        msg_bytes.append(&mut self.v_c_ry.to_bytes()?);
        msg_bytes.append(&mut self.v_a_val.to_bytes()?);
        msg_bytes.append(&mut self.v_b_val.to_bytes()?);
        msg_bytes.append(&mut self.v_c_val.to_bytes()?);
        collect_sponge_field_elements_gadget!(msg_bytes)
    }

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<CF<G>>>, SynthesisError> {
        todo!()
    }
}

#[derive(Clone)]
pub struct ProverFourthMsgVar<G: AffineCurve> {
    pub v_a_row_m: NonNativeVar<G>,
    pub v_b_row_m: NonNativeVar<G>,
    pub v_c_row_m: NonNativeVar<G>,
    pub v_a_col_m: NonNativeVar<G>,
    pub v_b_col_m: NonNativeVar<G>,
    pub v_c_col_m: NonNativeVar<G>,
    pub v_a_row_read_m: NonNativeVar<G>,
    pub v_b_row_read_m: NonNativeVar<G>,
    pub v_c_row_read_m: NonNativeVar<G>,
    pub v_a_col_read_m: NonNativeVar<G>,
    pub v_b_col_read_m: NonNativeVar<G>,
    pub v_c_col_read_m: NonNativeVar<G>,
    pub v_a_row_final_n: NonNativeVar<G>,
    pub v_b_row_final_n: NonNativeVar<G>,
    pub v_c_row_final_n: NonNativeVar<G>,
    pub v_a_col_final_n: NonNativeVar<G>,
    pub v_b_col_final_n: NonNativeVar<G>,
    pub v_c_col_final_n: NonNativeVar<G>,
}

impl<G: AffineCurve> ProverFourthMsgVar<G> {
    pub fn first_iter(&self) -> Vec<NonNativeVar<G>> {
        vec![
            self.v_a_row_m.clone(),
            self.v_b_row_m.clone(),
            self.v_c_row_m.clone(),
            self.v_a_col_m.clone(),
            self.v_b_col_m.clone(),
            self.v_c_col_m.clone(),
            self.v_a_row_read_m.clone(),
            self.v_b_row_read_m.clone(),
            self.v_c_row_read_m.clone(),
            self.v_a_col_read_m.clone(),
            self.v_b_col_read_m.clone(),
            self.v_c_col_read_m.clone(),
        ]
    }

    pub fn second_iter(&self) -> Vec<NonNativeVar<G>> {
        vec![
            self.v_a_row_final_n.clone(),
            self.v_b_row_final_n.clone(),
            self.v_c_row_final_n.clone(),
            self.v_a_col_final_n.clone(),
            self.v_b_col_final_n.clone(),
            self.v_c_col_final_n.clone(),
        ]
    }
}

impl<G: AffineCurve> AllocVar<ProverFourthMsg<F<G>>, CF<G>> for ProverFourthMsgVar<G> {
    fn new_variable<T: Borrow<ProverFourthMsg<F<G>>>>(
        cs: impl Into<Namespace<CF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|msg| {
            let msg = msg.borrow();
            let v_a_row_m: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_a_row_m), mode)?;
            let v_b_row_m: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_b_row_m), mode)?;
            let v_c_row_m: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_c_row_m), mode)?;
            let v_a_col_m: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_a_col_m), mode)?;
            let v_b_col_m: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_b_col_m), mode)?;
            let v_c_col_m: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_c_col_m), mode)?;
            let v_a_row_read_m: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_a_row_read_m), mode)?;
            let v_b_row_read_m: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_b_row_read_m), mode)?;
            let v_c_row_read_m: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_c_row_read_m), mode)?;
            let v_a_col_read_m: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_a_col_read_m), mode)?;
            let v_b_col_read_m: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_b_col_read_m), mode)?;
            let v_c_col_read_m: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_c_col_read_m), mode)?;
            let v_a_row_final_n: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_a_row_final_n), mode)?;
            let v_b_row_final_n: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_b_row_final_n), mode)?;
            let v_c_row_final_n: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_c_row_final_n), mode)?;
            let v_a_col_final_n: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_a_col_final_n), mode)?;
            let v_b_col_final_n: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_b_col_final_n), mode)?;
            let v_c_col_final_n: NonNativeVar<G> =
                NonNativeFieldVar::new_variable(ns.clone(), || Ok(msg.v_c_col_final_n), mode)?;
            Ok(Self {
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
        })
    }
}

impl<G: AffineCurve> AbsorbGadget<CF<G>> for ProverFourthMsgVar<G> {
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<CF<G>>>, SynthesisError> {
        let mut msg_bytes = Vec::new();
        msg_bytes.append(&mut self.v_a_row_m.to_bytes()?);
        msg_bytes.append(&mut self.v_b_row_m.to_bytes()?);
        msg_bytes.append(&mut self.v_c_row_m.to_bytes()?);
        msg_bytes.append(&mut self.v_a_col_m.to_bytes()?);
        msg_bytes.append(&mut self.v_b_col_m.to_bytes()?);
        msg_bytes.append(&mut self.v_c_col_m.to_bytes()?);
        msg_bytes.append(&mut self.v_a_row_read_m.to_bytes()?);
        msg_bytes.append(&mut self.v_b_row_read_m.to_bytes()?);
        msg_bytes.append(&mut self.v_c_row_read_m.to_bytes()?);
        msg_bytes.append(&mut self.v_a_col_read_m.to_bytes()?);
        msg_bytes.append(&mut self.v_b_col_read_m.to_bytes()?);
        msg_bytes.append(&mut self.v_c_col_read_m.to_bytes()?);
        msg_bytes.append(&mut self.v_a_row_final_n.to_bytes()?);
        msg_bytes.append(&mut self.v_b_row_final_n.to_bytes()?);
        msg_bytes.append(&mut self.v_c_row_final_n.to_bytes()?);
        msg_bytes.append(&mut self.v_a_col_final_n.to_bytes()?);
        msg_bytes.append(&mut self.v_b_col_final_n.to_bytes()?);
        msg_bytes.append(&mut self.v_c_col_final_n.to_bytes()?);
        collect_sponge_field_elements_gadget!(msg_bytes)
    }

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<CF<G>>>, SynthesisError> {
        todo!()
    }
}

pub struct IPForR1CSVar<
    G: AffineCurve,
    S: CryptographicSponge,
    SV: CryptographicSpongeVar<CF<G>, S>,
> {
    _projective: PhantomData<G>,
    _sponge: PhantomData<S>,
    _sponge_var: PhantomData<SV>,
}

impl<G: AffineCurve, S: CryptographicSponge, SV: CryptographicSpongeVar<CF<G>, S>>
    IPForR1CSVar<G, S, SV>
{
    pub fn verifier_init(
        cs: ConstraintSystemRef<CF<G>>,
        index_info: IndexInfo<F<G>>,
        input: Vec<Vec<NonNativeVar<G>>>,
        sponge: &mut SV,
    ) -> Result<(VerifierFirstMsgVar<G>, VerifierStateVar<G>), SynthesisError> {
        assert!(input.len().is_power_of_two());
        let d = input.len().next_power_of_two().trailing_zeros() as usize;
        let n = index_info.constraints_nv();
        let k = index_info.input_nv();
        let m = index_info.weight_nv();
        assert!(index_info.num_constraints == index_info.num_variables);
        let zero: NonNativeVar<G> = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::zero())?;
        // this padded_input has len 1 << k and not 1 << (n - 1).
        let mut padded_input = input.clone();
        for i in 0..1 << d {
            assert!(input[i].len() <= 1 << k);
            for _ in input[i].len()..1 << k {
                padded_input[i].push(zero.clone());
            }
        }
        let (tau, _) = sponge.squeeze_nonnative_field_elements_with_sizes::<F<G>>(
            vec![CHALLENGE_SIZE; n + d].as_slice(),
        )?;
        let msg = VerifierFirstMsgVar { tau: tau.clone() };
        let sumcheck_state = IPForMVSumcheckVar::<G, P1<F<G>>>::verifier_init(n + d, zero);
        Ok((
            msg,
            VerifierStateVar {
                d,
                n,
                k,
                m,
                index_info,
                v: padded_input,
                tau,
                r_x: None,
                r_d: None,
                r_a_y: None,
                r_b_y: None,
                r_c_y: None,
                r_y: None,
                r_m: None,
                r_n: None,
                v_w: None,
                r_a_spark: None,
                r_b_spark: None,
                r_c_spark: None,
                gamma_1: None,
                gamma_2: None,
                first_sumcheck_state: sumcheck_state,
                second_sumcheck_state: None,
                third_sumcheck_state: None,
                curr_gkr_level: 0,
                gkr_state_n: None,
                gkr_state_m: None,
            },
        ))
    }

    pub fn verifier_first_sumcheck_round(
        p_msg: SumcheckProverMsgVar<G>,
        state: &mut VerifierStateVar<G>,
        sponge: &mut SV,
    ) -> Result<SumcheckVerifierMsgVar<G>, SynthesisError> {
        Ok(IPForMVSumcheckVar::<G, P1<F<G>>>::verify_round(
            p_msg,
            &mut state.first_sumcheck_state,
            sponge,
        )?)
    }

    pub fn verifier_first_sumcheck_finalize(
        cs: ConstraintSystemRef<CF<G>>,
        p_msg: ProverFirstMsgVar<G>,
        state: &mut VerifierStateVar<G>,
        sponge: &mut SV,
    ) -> Result<VerifierSecondMsgVar<G>, SynthesisError> {
        let subclaim = IPForMVSumcheckVar::<G, P1<F<G>>>::check_and_generate_subclaim(
            cs.clone(),
            &mut state.first_sumcheck_state,
        )?;
        let r_xd = subclaim.point;
        state.r_d = Some(r_xd[state.n..].to_vec());
        state.r_x = Some(r_xd[..state.n].to_vec());
        let e_x = subclaim.expected_evaluation;
        let v_eq = evaluate_eq_extension::<G>(cs.clone(), &r_xd, &state.tau, state.n + state.d)?;
        e_x.enforce_equal(&((&p_msg.v_a_x * &p_msg.v_b_x - &p_msg.v_c_x) * &v_eq))?;

        let (r_vec, _) = sponge.squeeze_nonnative_field_elements_with_sizes::<F<G>>(
            vec![CHALLENGE_SIZE; 3].as_slice(),
        )?;
        let r_a = &r_vec[0];
        let r_b = &r_vec[1];
        let r_c = &r_vec[2];
        state.r_a_y = Some(r_a.clone());
        state.r_b_y = Some(r_b.clone());
        state.r_c_y = Some(r_c.clone());

        // set next sumcheck state
        let sumcheck_state = IPForMVSumcheckVar::<G, P2<F<G>>>::verifier_init(
            state.n,
            // TODO: fix
            (r_a.mul_without_reduce(&p_msg.v_a_x)?
                + r_b.mul_without_reduce(&p_msg.v_b_x)?
                + r_c.mul_without_reduce(&p_msg.v_c_x)?)
            .reduce()?,
        );
        state.second_sumcheck_state = Some(sumcheck_state);

        Ok(VerifierSecondMsgVar {
            r_a_y: r_a.clone(),
            r_b_y: r_b.clone(),
            r_c_y: r_c.clone(),
        })
    }

    pub fn verifier_second_sumcheck_round(
        p_msg: SumcheckProverMsgVar<G>,
        state: &mut VerifierStateVar<G>,
        sponge: &mut SV,
    ) -> Result<SumcheckVerifierMsgVar<G>, SynthesisError> {
        Ok(IPForMVSumcheckVar::<G, P2<F<G>>>::verify_round(
            p_msg,
            state.second_sumcheck_state.as_mut().unwrap(),
            sponge,
        )?)
    }

    pub fn verifier_second_sumcheck_finalize(
        cs: ConstraintSystemRef<CF<G>>,
        p_msg: ProverSecondMsgVar<G>,
        state: &mut VerifierStateVar<G>,
        sponge: &mut SV,
    ) -> Result<VerifierThirdMsgVar<G>, SynthesisError> {
        let subclaim = IPForMVSumcheckVar::<G, P2<F<G>>>::check_and_generate_subclaim(
            cs.clone(),
            state.second_sumcheck_state.as_mut().unwrap(),
        )?;
        let e_y = &subclaim.expected_evaluation;
        let r_y = subclaim.point;

        // computing v_z from v_w and v_v
        let v_w = &p_msg.v_w_y;
        let mut flattened_input = Vec::new();
        for i in 0..1 << state.d {
            flattened_input.extend(state.v[i].clone());
        }
        let mut eval_point = r_y[..state.k].to_vec();
        eval_point.extend(state.r_d.as_ref().unwrap().clone());
        let mut v_v = DenseMLEVar::from_evaluations_vec(state.k + state.d, flattened_input)
            .evaluate(&eval_point)
            .unwrap();
        let one = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::one())?;
        for i in state.k..state.n - 1 {
            v_v *= &one - &r_y[i];
        }
        let v_z = v_v * (&one - &r_y[state.n - 1]) + v_w * &r_y[state.n - 1];

        e_y.enforce_equal(
            &((state.r_a_y.as_ref().unwrap() * &p_msg.v_a_y
                + state.r_b_y.as_ref().unwrap() * &p_msg.v_b_y
                + state.r_c_y.as_ref().unwrap() * &p_msg.v_c_y)
                * &v_z),
        )?;
        state.r_y = Some(r_y.clone());
        state.v_w = Some(p_msg.v_w_y);

        let (r_vec, _) = sponge.squeeze_nonnative_field_elements_with_sizes::<F<G>>(
            vec![CHALLENGE_SIZE; 5].as_slice(),
        )?;
        let r_a_spark = &r_vec[0];
        let r_b_spark = &r_vec[1];
        let r_c_spark = &r_vec[2];
        let gamma_1 = &r_vec[3];
        let gamma_2 = &r_vec[4];
        state.r_a_spark = Some(r_a_spark.clone());
        state.r_b_spark = Some(r_b_spark.clone());
        state.r_c_spark = Some(r_c_spark.clone());
        state.gamma_1 = Some(gamma_1.clone());
        state.gamma_2 = Some(gamma_2.clone());

        // set next sumcheck state
        let sumcheck_state = IPForMVSumcheckVar::<G, P3<F<G>>>::verifier_init(
            state.m,
            r_a_spark * &p_msg.v_a_y + r_b_spark * &p_msg.v_b_y + r_c_spark * &p_msg.v_c_y,
        );
        state.third_sumcheck_state = Some(sumcheck_state);

        Ok(VerifierThirdMsgVar {
            r_a_spark: r_a_spark.clone(),
            r_b_spark: r_b_spark.clone(),
            r_c_spark: r_c_spark.clone(),
            gamma_1: gamma_1.clone(),
            gamma_2: gamma_2.clone(),
        })
    }

    pub fn verifier_third_sumcheck_round(
        p_msg: SumcheckProverMsgVar<G>,
        state: &mut VerifierStateVar<G>,
        sponge: &mut SV,
    ) -> Result<SumcheckVerifierMsgVar<G>, SynthesisError> {
        Ok(IPForMVSumcheckVar::<G, P3<F<G>>>::verify_round(
            p_msg,
            state.third_sumcheck_state.as_mut().unwrap(),
            sponge,
        )?)
    }

    pub fn verifier_third_sumcheck_finalize(
        cs: ConstraintSystemRef<CF<G>>,
        p_msg: ProverThirdMsgVar<G>,
        state: &mut VerifierStateVar<G>,
        _sponge: &mut SV,
    ) -> Result<(), SynthesisError> {
        let subclaim = IPForMVSumcheckVar::<G, P3<F<G>>>::check_and_generate_subclaim(
            cs.clone(),
            state.third_sumcheck_state.as_mut().unwrap(),
        )?;
        let e_h = &subclaim.expected_evaluation;
        let r_h = subclaim.point;

        e_h.enforce_equal(
            &(state.r_a_spark.as_ref().unwrap() * &p_msg.v_a_val * &p_msg.v_a_rx * &p_msg.v_a_ry
                + state.r_b_spark.as_ref().unwrap()
                    * &p_msg.v_b_val
                    * &p_msg.v_b_rx
                    * &p_msg.v_b_ry
                + state.r_c_spark.as_ref().unwrap()
                    * &p_msg.v_c_val
                    * &p_msg.v_c_rx
                    * &p_msg.v_c_ry),
        )?;

        state.r_m = Some(r_h.clone());

        Ok(())
    }

    pub fn verifier_gkr_setup(
        cs: ConstraintSystemRef<CF<G>>,
        p_msg: Vec<GKRBatchProverMsgVar<G>>,
        state: &mut VerifierStateVar<G>,
        sponge: &mut SV,
    ) -> Result<GKRBatchVerifierMsgVar<G>, SynthesisError> {
        // GKR level starts at 1
        state.curr_gkr_level = 1;

        let mut v_msgs = Vec::new();

        // use the same sponge across GKR instances to ensure that the same challenges are used
        let mut sponge_clone = sponge.clone();
        let (state_n, msg_n) = GKRVar::batch_verifier_init(
            cs.clone(),
            p_msg[0].clone(),
            state.n,
            8,
            &mut sponge_clone,
        )?;
        state.gkr_state_n = Some(state_n);
        v_msgs.push(msg_n);
        let mut sponge_clone = sponge.clone();
        let (state_m, msg_m) = GKRVar::batch_verifier_init(
            cs.clone(),
            p_msg[1].clone(),
            state.m,
            12,
            &mut sponge_clone,
        )?;
        state.gkr_state_m = Some(state_m);
        v_msgs.push(msg_m);

        assert!(v_msgs[0].challenges.len() == 3);
        assert!(v_msgs[1].challenges.len() == 4);
        Ok(v_msgs[1].clone())
    }

    pub fn verifier_gkr_level_sumcheck_round(
        p_msg: Vec<SumcheckProverMsgVar<G>>,
        state: &mut VerifierStateVar<G>,
        sponge: &mut SV,
    ) -> Result<SumcheckVerifierMsgVar<G>, SynthesisError> {
        let mut v_msgs = Vec::new();
        let mut idx = 0;
        if state.curr_gkr_level <= state.n
            && !state
                .gkr_state_n
                .as_ref()
                .unwrap()
                .current_sumcheck_finished()
        {
            let mut sponge_clone = sponge.clone();
            v_msgs.push(GKRVar::batch_verifier_level_sumcheck_round(
                p_msg[idx].clone(),
                state.gkr_state_n.as_mut().unwrap(),
                &mut sponge_clone,
            )?);
            idx += 1;
        }
        if state.curr_gkr_level <= state.m
            && !state
                .gkr_state_m
                .as_ref()
                .unwrap()
                .current_sumcheck_finished()
        {
            let mut sponge_clone = sponge.clone();
            v_msgs.push(GKRVar::batch_verifier_level_sumcheck_round(
                p_msg[idx].clone(),
                state.gkr_state_m.as_mut().unwrap(),
                &mut sponge_clone,
            )?);
        }
        Ok(v_msgs.pop().unwrap())
    }

    pub fn verifier_gkr_level_sumcheck_finalize(
        cs: ConstraintSystemRef<CF<G>>,
        p_msg: Vec<GKRBatchProverMsgVar<G>>,
        state: &mut VerifierStateVar<G>,
        sponge: &mut SV,
    ) -> Result<GKRBatchVerifierMsgVar<G>, SynthesisError> {
        let mut v_msgs = Vec::new();
        let mut idx = 0;
        if state.curr_gkr_level <= state.n {
            let mut sponge_clone = sponge.clone();
            v_msgs.push(GKRVar::batch_verifier_level_sumcheck_finalize(
                cs.clone(),
                p_msg[idx].clone(),
                &mut state.gkr_state_n.as_mut().unwrap(),
                &mut sponge_clone,
            )?);
            idx += 1;
        }
        if state.curr_gkr_level <= state.m {
            let mut sponge_clone = sponge.clone();
            v_msgs.push(GKRVar::batch_verifier_level_sumcheck_finalize(
                cs.clone(),
                p_msg[idx].clone(),
                &mut state.gkr_state_m.as_mut().unwrap(),
                &mut sponge_clone,
            )?);
            idx += 1;
        }
        state.curr_gkr_level += 1;
        Ok(v_msgs.pop().unwrap())
    }

    pub fn verifier_gkr_finalize(
        cs: ConstraintSystemRef<CF<G>>,
        p_msg_1: ProverThirdMsgVar<G>,
        p_msg_2: ProverFourthMsgVar<G>,
        state: &mut VerifierStateVar<G>,
        sponge: &mut SV,
    ) -> Result<VerifierFourthMsgVar<G>, SynthesisError> {
        // retrieve state
        let r_x = state.r_x.as_ref().unwrap();
        let r_y = state.r_y.as_ref().unwrap();
        let gamma_1 = state.gamma_1.as_ref().unwrap();
        let gamma_2 = state.gamma_2.as_ref().unwrap();

        let check_initial_claim = |init: &NonNativeVar<G>,
                                   r#final: &NonNativeVar<G>,
                                   rs: &NonNativeVar<G>,
                                   ws: &NonNativeVar<G>|
         -> Result<_, SynthesisError> {
            let lhs = init * ws;
            lhs.enforce_equal(&(r#final * rs))?;
            Ok(())
        };
        let state_n = state.gkr_state_n.as_ref().unwrap();
        let state_m = state.gkr_state_m.as_ref().unwrap();

        // check that the initial claims are correct
        let [init_row_iclaim, init_col_iclaim, a_final_row_iclaim, a_final_col_iclaim, b_final_row_iclaim, b_final_col_iclaim, c_final_row_iclaim, c_final_col_iclaim]: [NonNativeVar<G>; 8] = state_n.initial_claims.clone().try_into().unwrap();
        let [a_rs_row_iclaim, a_rs_col_iclaim, b_rs_row_iclaim, b_rs_col_iclaim, c_rs_row_iclaim, c_rs_col_iclaim, a_ws_row_iclaim, a_ws_col_iclaim, b_ws_row_iclaim, b_ws_col_iclaim, c_ws_row_iclaim, c_ws_col_iclaim]: [NonNativeVar<G>; 12] = state_m.initial_claims.clone().try_into().unwrap();
        check_initial_claim(
            &init_row_iclaim,
            &a_final_row_iclaim,
            &a_rs_row_iclaim,
            &a_ws_row_iclaim,
        )?;
        check_initial_claim(
            &init_col_iclaim,
            &a_final_col_iclaim,
            &a_rs_col_iclaim,
            &a_ws_col_iclaim,
        )?;
        check_initial_claim(
            &init_row_iclaim,
            &b_final_row_iclaim,
            &b_rs_row_iclaim,
            &b_ws_row_iclaim,
        )?;
        check_initial_claim(
            &init_col_iclaim,
            &b_final_col_iclaim,
            &b_rs_col_iclaim,
            &b_ws_col_iclaim,
        )?;
        check_initial_claim(
            &init_row_iclaim,
            &c_final_row_iclaim,
            &c_rs_row_iclaim,
            &c_ws_row_iclaim,
        )?;
        check_initial_claim(
            &init_col_iclaim,
            &c_final_col_iclaim,
            &c_rs_col_iclaim,
            &c_ws_col_iclaim,
        )?;

        // some sanity checks
        let level = state.curr_gkr_level - 1;
        assert!(level == state.n || level == state.m);
        assert!(state_n.level == state.n + 1);
        assert!(state_m.level == state.m + 1);

        // get r_n and r_m from GKR challenges
        let (r_batch_n, r_n) = GKRVar::batch_verifier_evaluation_points(state_n);
        assert!(r_n.len() == state.n);
        state.r_n = Some(r_n.clone());
        let (r_batch_m, r_m) = GKRVar::batch_verifier_evaluation_points(state_m);

        let compute_final_claim = |t_1: &NonNativeVar<G>,
                                   t_2: &NonNativeVar<G>,
                                   t_3: &NonNativeVar<G>,
                                   gamma_1: &NonNativeVar<G>,
                                   gamma_1_sq: &NonNativeVar<G>,
                                   gamma_2: &NonNativeVar<G>|
         -> Result<_, SynthesisError> {
            let claim = t_1 - gamma_2
                + (t_2.mul_without_reduce(gamma_1)? + t_3.mul_without_reduce(gamma_1_sq)?)
                    .reduce()?;
            Ok(claim)
        };

        // get final evaluations of the locally computed polynomials
        let v_eq_x = evaluate_eq_extension::<G>(cs.clone(), &r_x, &r_n, state.n)?;
        let v_eq_y = evaluate_eq_extension::<G>(cs.clone(), &r_y, &r_n, state.n)?;
        let v_idx_n = evaluate_idx_mle::<G>(cs.clone(), state.n, &r_n)?;
        let zero = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::zero())?;
        let one = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::one())?;
        let gamma_1_sq = gamma_1 * gamma_1;

        let init_row_fclaim =
            compute_final_claim(&v_idx_n, &v_eq_x, &zero, &gamma_1, &gamma_1_sq, &gamma_2)?;
        let init_col_fclaim =
            compute_final_claim(&v_idx_n, &v_eq_y, &zero, &gamma_1, &gamma_1_sq, &gamma_2)?;
        let a_final_row_fclaim = compute_final_claim(
            &v_idx_n,
            &v_eq_x,
            &p_msg_2.v_a_row_final_n,
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let a_final_col_fclaim = compute_final_claim(
            &v_idx_n,
            &v_eq_y,
            &p_msg_2.v_a_col_final_n,
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let b_final_row_fclaim = compute_final_claim(
            &v_idx_n,
            &v_eq_x,
            &p_msg_2.v_b_row_final_n,
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let b_final_col_fclaim = compute_final_claim(
            &v_idx_n,
            &v_eq_y,
            &p_msg_2.v_b_col_final_n,
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let c_final_row_fclaim = compute_final_claim(
            &v_idx_n,
            &v_eq_x,
            &p_msg_2.v_c_row_final_n,
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let c_final_col_fclaim = compute_final_claim(
            &v_idx_n,
            &v_eq_y,
            &p_msg_2.v_c_col_final_n,
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;

        let a_rs_row_fclaim = compute_final_claim(
            &p_msg_2.v_a_row_m,
            &p_msg_1.v_a_rx,
            &p_msg_2.v_a_row_read_m,
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let a_rs_col_fclaim = compute_final_claim(
            &p_msg_2.v_a_col_m,
            &p_msg_1.v_a_ry,
            &p_msg_2.v_a_col_read_m,
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let b_rs_row_fclaim = compute_final_claim(
            &p_msg_2.v_b_row_m,
            &p_msg_1.v_b_rx,
            &p_msg_2.v_b_row_read_m,
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let b_rs_col_fclaim = compute_final_claim(
            &p_msg_2.v_b_col_m,
            &p_msg_1.v_b_ry,
            &p_msg_2.v_b_col_read_m,
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let c_rs_row_fclaim = compute_final_claim(
            &p_msg_2.v_c_row_m,
            &p_msg_1.v_c_rx,
            &p_msg_2.v_c_row_read_m,
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let c_rs_col_fclaim = compute_final_claim(
            &p_msg_2.v_c_col_m,
            &p_msg_1.v_c_ry,
            &p_msg_2.v_c_col_read_m,
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let a_ws_row_fclaim = compute_final_claim(
            &p_msg_2.v_a_row_m,
            &p_msg_1.v_a_rx,
            &(&p_msg_2.v_a_row_read_m + &one),
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let a_ws_col_fclaim = compute_final_claim(
            &p_msg_2.v_a_col_m,
            &p_msg_1.v_a_ry,
            &(&p_msg_2.v_a_col_read_m + &one),
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let b_ws_row_fclaim = compute_final_claim(
            &p_msg_2.v_b_row_m,
            &p_msg_1.v_b_rx,
            &(&p_msg_2.v_b_row_read_m + &one),
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let b_ws_col_fclaim = compute_final_claim(
            &p_msg_2.v_b_col_m,
            &p_msg_1.v_b_ry,
            &(&p_msg_2.v_b_col_read_m + &one),
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let c_ws_row_fclaim = compute_final_claim(
            &p_msg_2.v_c_row_m,
            &p_msg_1.v_c_rx,
            &(&p_msg_2.v_c_row_read_m + &one),
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;
        let c_ws_col_fclaim = compute_final_claim(
            &p_msg_2.v_c_col_m,
            &p_msg_1.v_c_ry,
            &(&p_msg_2.v_c_col_read_m + &one),
            &gamma_1,
            &gamma_1_sq,
            &gamma_2,
        )?;

        let final_claims_n = vec![
            init_row_fclaim,
            init_col_fclaim,
            a_final_row_fclaim,
            a_final_col_fclaim,
            b_final_row_fclaim,
            b_final_col_fclaim,
            c_final_row_fclaim,
            c_final_col_fclaim,
        ];
        let mut final_claims_m = vec![
            a_rs_row_fclaim,
            a_rs_col_fclaim,
            b_rs_row_fclaim,
            b_rs_col_fclaim,
            c_rs_row_fclaim,
            c_rs_col_fclaim,
            a_ws_row_fclaim,
            a_ws_col_fclaim,
            b_ws_row_fclaim,
            b_ws_col_fclaim,
            c_ws_row_fclaim,
            c_ws_col_fclaim,
        ];
        final_claims_m.extend(vec![zero.clone(); 4]);

        // check that the final sumchecks claims are correct
        let claim_n = state_n.current_claim.clone();
        let claim_m = state_m.current_claim.clone();

        let final_claims_n = DenseMLEVar::from_evaluations_vec(3, final_claims_n);
        let final_claims_m = DenseMLEVar::from_evaluations_vec(4, final_claims_m);
        let expected_claim_n = final_claims_n.evaluate(&r_batch_n)?;
        let expected_claim_m = final_claims_m.evaluate(&r_batch_m)?;

        expected_claim_m.enforce_equal(&claim_m)?;
        expected_claim_n.enforce_equal(&claim_n)?;

        let (mut r_m_lin_comb, _) = sponge.squeeze_nonnative_field_elements_with_sizes::<F<G>>(
            vec![CHALLENGE_SIZE; 1].as_slice(),
        )?;
        let r_m_lin_comb = r_m_lin_comb.pop().unwrap();
        Ok(VerifierFourthMsgVar {
            r_m_lin_comb,
            r_m_ext: r_batch_m,
            r_n_ext: r_batch_n,
        })
    }
}

pub fn evaluate_eq_extension<G: AffineCurve>(
    cs: ConstraintSystemRef<CF<G>>,
    point_1: &Vec<NonNativeVar<G>>,
    point_2: &Vec<NonNativeVar<G>>,
    nv: usize,
) -> Result<NonNativeVar<G>, SynthesisError> {
    assert!(point_1.len() == nv, "point_1 must be of length nv");
    assert!(
        point_2.len() == point_1.len(),
        "point_1 length must equal point_2 length"
    );
    let mut ret = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::one())?;
    let one = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::one())?;
    for i in 0..nv {
        let r = &point_1[i];
        let s = &point_2[i];
        let one_minus_r = &one - r;
        let one_minus_s = &one - s;
        let tmp = r.mul_without_reduce(&s)? + one_minus_r.mul_without_reduce(&one_minus_s)?;
        ret *= tmp.reduce()?;
    }
    Ok(ret)
}

// note that idx_MLE is the same as the polynomial that converts bits to integer
// so its i-th coefficient is 2^i (going from least significant to most significant)
pub fn evaluate_idx_mle<G: AffineCurve>(
    cs: ConstraintSystemRef<CF<G>>,
    nv: usize,
    r: &Vec<NonNativeVar<G>>,
) -> Result<NonNativeVar<G>, SynthesisError> {
    let mut ret = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::zero())?;
    let mut multiplier = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::one())?;
    let two = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::one() + F::<G>::one())?;
    for i in 0..nv {
        ret = &ret + (&r[i] * &multiplier);
        multiplier = &multiplier * &two;
    }
    Ok(ret)
}
