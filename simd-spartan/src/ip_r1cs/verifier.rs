use crate::sumcheck::prover::ProverMsg as SumcheckProverMsg;
use crate::sumcheck::verifier::{
    VerifierMsg as SumcheckVerifierMsg, VerifierState as SumcheckVerifierState,
};
use crate::sumcheck::IPForMVSumcheck;
use crate::{Error, CHALLENGE_SIZE};
use ark_ff::PrimeField;
use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
use ark_sponge::CryptographicSponge;

use super::prover::{ProverFirstMsg, ProverFourthMsg, ProverSecondMsg, ProverThirdMsg};
use super::{indexer::IndexInfo, IPForR1CS};
use super::{FirstSumcheckPredicate, SecondSumcheckPredicate, ThirdSumcheckPredicate};
use crate::gkr_grand_product::{
    prover::BatchProverMsg as GKRBatchProverMsg, verifier::BatchVerifierMsg as GKRBatchVerifierMsg,
    verifier::BatchVerifierState as GKRBatchVerifierState, GKR,
};

pub struct VerifierState<F: PrimeField> {
    /// log(number of data-parallel instances)
    pub d: usize,
    /// log(|padded_v|+|w|)
    pub n: usize,
    /// log(|v|)
    pub k: usize,
    /// log(num_non_zero)
    pub m: usize,
    pub index_info: IndexInfo<F>,
    /// Input Assignment
    pub v: Vec<Vec<F>>,
    pub tau: Vec<F>,
    // For combining z_i's
    pub r_d: Option<Vec<F>>,
    // challenges from initial sumcheck over x
    pub r_x: Option<Vec<F>>,
    // For combining sumcheck over y
    pub r_a_y: Option<F>,
    pub r_b_y: Option<F>,
    pub r_c_y: Option<F>,
    // sumcheck challenges that will be checked with poly commitment
    pub r_y: Option<Vec<F>>,
    pub r_m: Option<Vec<F>>,
    pub r_n: Option<Vec<F>>,
    // W(r_y) = v_w,
    pub v_w: Option<F>,
    // For combining Spark claims over matrices
    pub r_a_spark: Option<F>,
    pub r_b_spark: Option<F>,
    pub r_c_spark: Option<F>,
    // For combining GKR claims
    pub gamma_1: Option<F>,
    pub gamma_2: Option<F>,
    // sumcheck states
    pub first_sumcheck_state: SumcheckVerifierState<F>,
    pub second_sumcheck_state: Option<SumcheckVerifierState<F>>,
    pub third_sumcheck_state: Option<SumcheckVerifierState<F>>,
    /// Current GKR Level
    pub curr_gkr_level: usize,
    /// GKR States for products of size 2^n
    pub gkr_state_n: Option<GKRBatchVerifierState<F>>,
    /// GKR States for products of size 2^m
    pub gkr_state_m: Option<GKRBatchVerifierState<F>>,
}

/// First message of the verifier.
#[derive(Clone)]
pub struct VerifierFirstMsg<F: PrimeField> {
    /// for checking Q(t_1, t_2) = \sum_x F(g, x)*eq((g, x), (t_1, t_2)) on random points tau_1, tau_2
    pub tau: Vec<F>,
}

#[derive(Clone)]
pub struct VerifierSecondMsg<F: PrimeField> {
    /// for linearly combining a_r_x(y), b_r_x(y), c_r_x(y)
    pub r_a_y: F,
    pub r_b_y: F,
    pub r_c_y: F,
}

#[derive(Clone)]
pub struct VerifierThirdMsg<F: PrimeField> {
    /// for linearly combining Spark claims over a, b, c matrices
    pub r_a_spark: F,
    pub r_b_spark: F,
    pub r_c_spark: F,
    /// for linearly combining elements of tuples in
    /// Init Set (Init), Read Set (RS), Write Set (WS), and Final Set (Final)
    pub gamma_1: F,
    pub gamma_2: F,
}

#[derive(Clone)]
pub struct VerifierFourthMsg<F: PrimeField> {
    /// for linearly combining r_m commitments
    pub r_m_lin_comb: F,
    pub r_m_ext: Vec<F>,
    pub r_n_ext: Vec<F>,
}

pub(crate) type P1<F> = FirstSumcheckPredicate<F>;
pub(crate) type P2<F> = SecondSumcheckPredicate<F>;
pub(crate) type P3<F> = ThirdSumcheckPredicate<F>;

impl<F: PrimeField, S: CryptographicSponge> IPForR1CS<F, S> {
    /// Output the first message and next round state.
    pub fn verifier_init(
        index_info: IndexInfo<F>,
        input: Vec<Vec<F>>,
        sponge: &mut S,
    ) -> Result<(VerifierFirstMsg<F>, VerifierState<F>), Error> {
        assert!(input.len().is_power_of_two());
        let d = input.len().next_power_of_two().trailing_zeros() as usize;
        let n = index_info.constraints_nv();
        let k = index_info.input_nv();
        let m = index_info.weight_nv();
        if index_info.num_constraints != index_info.num_variables {
            return Err(Error::NonSquareMatrix);
        }
        // this padded_input has len 1 << k and not 1 << (n - 1).
        let mut padded_input = input.clone();
        for i in 0..1 << d {
            if input[i].len() > 1 << k {
                return Err(Error::InvalidPublicInputLength);
            }
            for _ in input[i].len()..1 << k {
                padded_input[i].push(F::zero());
            }
        }
        let tau =
            sponge.squeeze_field_elements_with_sizes::<F>(vec![CHALLENGE_SIZE; n + d].as_slice());
        let msg = VerifierFirstMsg { tau: tau.clone() };
        let sumcheck_state = IPForMVSumcheck::<F, P1<F>>::verifier_init(n + d, F::zero());
        Ok((
            msg.clone(),
            VerifierState {
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
        p_msg: SumcheckProverMsg<F>,
        state: &mut VerifierState<F>,
        sponge: &mut S,
    ) -> Result<SumcheckVerifierMsg<F>, Error> {
        Ok(IPForMVSumcheck::<F, P1<F>>::verify_round(
            p_msg,
            &mut state.first_sumcheck_state,
            sponge,
        ))
    }

    pub fn verifier_first_sumcheck_finalize(
        p_msg: ProverFirstMsg<F>,
        state: &mut VerifierState<F>,
        sponge: &mut S,
    ) -> Result<VerifierSecondMsg<F>, Error> {
        let subclaim = IPForMVSumcheck::<F, P1<F>>::check_and_generate_subclaim(
            &mut state.first_sumcheck_state,
        )?;
        let r_xd = subclaim.point;
        state.r_d = Some(r_xd[state.n..].to_vec());
        state.r_x = Some(r_xd[..state.n].to_vec());
        let e_x = subclaim.expected_evaluation;
        let v_eq = evaluate_eq_extension(&r_xd, &state.tau, state.n + state.d);
        if e_x != (p_msg.v_a_x * p_msg.v_b_x - p_msg.v_c_x) * v_eq {
            return Err(Error::Reject(Some(
                "invalid subclaim to first sumcheck".into(),
            )));
        }
        let [r_a, r_b, r_c]: [F; 3] = sponge
            .squeeze_field_elements_with_sizes::<F>(vec![CHALLENGE_SIZE; 3].as_slice())
            .try_into()
            .unwrap();
        state.r_a_y = Some(r_a);
        state.r_b_y = Some(r_b);
        state.r_c_y = Some(r_c);

        // set next sumcheck state
        let sumcheck_state = IPForMVSumcheck::<F, P2<F>>::verifier_init(
            state.n,
            r_a * p_msg.v_a_x + r_b * p_msg.v_b_x + r_c * p_msg.v_c_x,
        );
        state.second_sumcheck_state = Some(sumcheck_state);

        Ok(VerifierSecondMsg {
            r_a_y: r_a,
            r_b_y: r_b,
            r_c_y: r_c,
        })
    }

    pub fn verifier_second_sumcheck_round(
        p_msg: SumcheckProverMsg<F>,
        state: &mut VerifierState<F>,
        sponge: &mut S,
    ) -> Result<SumcheckVerifierMsg<F>, Error> {
        Ok(IPForMVSumcheck::<F, P2<F>>::verify_round(
            p_msg,
            state.second_sumcheck_state.as_mut().unwrap(),
            sponge,
        ))
    }

    pub fn verifier_second_sumcheck_finalize(
        p_msg: ProverSecondMsg<F>,
        state: &mut VerifierState<F>,
        sponge: &mut S,
    ) -> Result<VerifierThirdMsg<F>, Error> {
        let subclaim = IPForMVSumcheck::<F, P2<F>>::check_and_generate_subclaim(
            state.second_sumcheck_state.as_mut().unwrap(),
        )?;
        let r_y = subclaim.point;
        let e_y = subclaim.expected_evaluation;

        // computing v_z from v_w and v_v
        let v_w = p_msg.v_w_y;
        let mut flattened_input = Vec::new();
        for i in 0..1 << state.d {
            flattened_input.extend(&state.v[i]);
        }
        let mut eval_point = r_y[..state.k].to_vec();
        eval_point.extend(state.r_d.as_ref().unwrap());
        let mut v_v =
            DenseMultilinearExtension::from_evaluations_vec(state.k + state.d, flattened_input)
                .evaluate(&eval_point)
                .unwrap();
        for i in state.k..state.n - 1 {
            v_v *= F::one() - r_y[i];
        }
        let v_z = v_v * (F::one() - r_y[state.n - 1]) + v_w * r_y[state.n - 1];

        if e_y
            != (state.r_a_y.unwrap() * p_msg.v_a_y
                + state.r_b_y.unwrap() * p_msg.v_b_y
                + state.r_c_y.unwrap() * p_msg.v_c_y)
                * v_z
        {
            return Err(Error::Reject(Some(
                "invalid subclaim to second sumcheck".into(),
            )));
        }
        state.r_y = Some(r_y);
        state.v_w = Some(p_msg.v_w_y);

        let [r_a, r_b, r_c, gamma_1, gamma_2]: [F; 5] = sponge
            .squeeze_field_elements_with_sizes::<F>(vec![CHALLENGE_SIZE; 5].as_slice())
            .try_into()
            .unwrap();
        state.r_a_spark = Some(r_a);
        state.r_b_spark = Some(r_b);
        state.r_c_spark = Some(r_c);
        state.gamma_1 = Some(gamma_1);
        state.gamma_2 = Some(gamma_2);

        // set next sumcheck state
        let sumcheck_state = IPForMVSumcheck::<F, P3<F>>::verifier_init(
            state.m,
            r_a * p_msg.v_a_y + r_b * p_msg.v_b_y + r_c * p_msg.v_c_y,
        );
        state.third_sumcheck_state = Some(sumcheck_state);

        Ok(VerifierThirdMsg {
            r_a_spark: r_a,
            r_b_spark: r_b,
            r_c_spark: r_c,
            gamma_1,
            gamma_2,
        })
    }

    pub fn verifier_third_sumcheck_round(
        p_msg: SumcheckProverMsg<F>,
        state: &mut VerifierState<F>,
        sponge: &mut S,
    ) -> Result<SumcheckVerifierMsg<F>, Error> {
        Ok(IPForMVSumcheck::<F, P3<F>>::verify_round(
            p_msg,
            state.third_sumcheck_state.as_mut().unwrap(),
            sponge,
        ))
    }

    pub fn verifier_third_sumcheck_finalize(
        p_msg: ProverThirdMsg<F>,
        state: &mut VerifierState<F>,
        _sponge: &mut S,
    ) -> Result<(), Error> {
        let subclaim = IPForMVSumcheck::<F, P3<F>>::check_and_generate_subclaim(
            state.third_sumcheck_state.as_mut().unwrap(),
        )?;
        let r_h = subclaim.point;
        let e_h = subclaim.expected_evaluation;

        if e_h
            != (state.r_a_spark.unwrap() * p_msg.v_a_val * p_msg.v_a_rx * p_msg.v_a_ry
                + state.r_b_spark.unwrap() * p_msg.v_b_val * p_msg.v_b_rx * p_msg.v_b_ry
                + state.r_c_spark.unwrap() * p_msg.v_c_val * p_msg.v_c_rx * p_msg.v_c_ry)
        {
            return Err(Error::Reject(Some(
                "invalid subclaim to third sumcheck".into(),
            )));
        }
        state.r_m = Some(r_h);

        Ok(())
    }

    pub fn verifier_gkr_setup(
        p_msg: Vec<GKRBatchProverMsg<F>>,
        state: &mut VerifierState<F>,
        sponge: &mut S,
    ) -> Result<GKRBatchVerifierMsg<F>, Error> {
        // GKR level starts at 1
        state.curr_gkr_level = 1;

        let mut v_msgs = Vec::new();

        // use the same sponge across GKR instances to ensure that the same challenges are used
        let mut sponge_clone = sponge.clone();
        let (state_n, msg_n) =
            GKR::batch_verifier_init(p_msg[0].clone(), state.n, 8, &mut sponge_clone);
        state.gkr_state_n = Some(state_n);
        v_msgs.push(msg_n);
        let mut sponge_clone = sponge.clone();
        let (state_m, msg_m) =
            GKR::batch_verifier_init(p_msg[1].clone(), state.m, 12, &mut sponge_clone);
        state.gkr_state_m = Some(state_m);
        v_msgs.push(msg_m);

        assert!(v_msgs[0].challenges.len() == 3);
        assert!(v_msgs[1].challenges.len() == 4);
        for i in 0..3 {
            assert!(v_msgs[0].challenges[i] == v_msgs[1].challenges[i]);
        }
        Ok(v_msgs[1].clone())
    }

    pub fn verifier_gkr_level_sumcheck_round(
        p_msg: Vec<SumcheckProverMsg<F>>,
        state: &mut VerifierState<F>,
        sponge: &mut S,
    ) -> Result<SumcheckVerifierMsg<F>, Error> {
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
            v_msgs.push(GKR::batch_verifier_level_sumcheck_round(
                p_msg[idx].clone(),
                state.gkr_state_n.as_mut().unwrap(),
                &mut sponge_clone,
            ));
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
            v_msgs.push(GKR::batch_verifier_level_sumcheck_round(
                p_msg[idx].clone(),
                state.gkr_state_m.as_mut().unwrap(),
                &mut sponge_clone,
            ));
        }
        for i in 0..v_msgs.len() {
            assert!(v_msgs[0] == v_msgs[i]);
        }
        Ok(v_msgs.pop().unwrap())
    }

    pub fn verifier_gkr_level_sumcheck_finalize(
        p_msg: Vec<GKRBatchProverMsg<F>>,
        state: &mut VerifierState<F>,
        sponge: &mut S,
    ) -> Result<GKRBatchVerifierMsg<F>, Error> {
        let mut v_msgs = Vec::new();
        let mut idx = 0;
        if state.curr_gkr_level <= state.n {
            let mut sponge_clone = sponge.clone();
            v_msgs.push(GKR::batch_verifier_level_sumcheck_finalize(
                p_msg[idx].clone(),
                &mut state.gkr_state_n.as_mut().unwrap(),
                &mut sponge_clone,
            )?);
            idx += 1;
        }
        if state.curr_gkr_level <= state.m {
            let mut sponge_clone = sponge.clone();
            v_msgs.push(GKR::batch_verifier_level_sumcheck_finalize(
                p_msg[idx].clone(),
                &mut state.gkr_state_m.as_mut().unwrap(),
                &mut sponge_clone,
            )?);
            idx += 1;
        }
        for i in 0..v_msgs.len() {
            assert!(v_msgs[0] == v_msgs[i]);
        }
        state.curr_gkr_level += 1;
        Ok(v_msgs.pop().unwrap())
    }

    pub fn verifier_gkr_finalize(
        p_msg_1: ProverThirdMsg<F>,
        p_msg_2: ProverFourthMsg<F>,
        state: &mut VerifierState<F>,
        sponge: &mut S,
    ) -> Result<VerifierFourthMsg<F>, Error> {
        // retrieve state
        let r_x = state.r_x.as_ref().unwrap();
        let r_y = state.r_y.as_ref().unwrap();
        let gamma_1 = state.gamma_1.unwrap();
        let gamma_2 = state.gamma_2.unwrap();

        let check_initial_claim = |init: F, r#final: F, rs: F, ws: F| -> Result<_, Error> {
            if init * ws != r#final * rs {
                return Err(Error::Reject(Some(
                    "Some GKR initial claim is incorrect: Init * WS != Final * RS".into(),
                )));
            }
            Ok(())
        };
        let state_n = state.gkr_state_n.as_ref().unwrap();
        let state_m = state.gkr_state_m.as_ref().unwrap();

        // check that the initial claims are correct
        let [init_row_iclaim, init_col_iclaim, a_final_row_iclaim, a_final_col_iclaim, b_final_row_iclaim, b_final_col_iclaim, c_final_row_iclaim, c_final_col_iclaim]: [F; 8] = state_n.initial_claims.clone().try_into().unwrap();
        let [a_rs_row_iclaim, a_rs_col_iclaim, b_rs_row_iclaim, b_rs_col_iclaim, c_rs_row_iclaim, c_rs_col_iclaim, a_ws_row_iclaim, a_ws_col_iclaim, b_ws_row_iclaim, b_ws_col_iclaim, c_ws_row_iclaim, c_ws_col_iclaim]: [F; 12] = state_m.initial_claims.clone().try_into().unwrap();
        check_initial_claim(
            init_row_iclaim,
            a_final_row_iclaim,
            a_rs_row_iclaim,
            a_ws_row_iclaim,
        )?;
        check_initial_claim(
            init_col_iclaim,
            a_final_col_iclaim,
            a_rs_col_iclaim,
            a_ws_col_iclaim,
        )?;
        check_initial_claim(
            init_row_iclaim,
            b_final_row_iclaim,
            b_rs_row_iclaim,
            b_ws_row_iclaim,
        )?;
        check_initial_claim(
            init_col_iclaim,
            b_final_col_iclaim,
            b_rs_col_iclaim,
            b_ws_col_iclaim,
        )?;
        check_initial_claim(
            init_row_iclaim,
            c_final_row_iclaim,
            c_rs_row_iclaim,
            c_ws_row_iclaim,
        )?;
        check_initial_claim(
            init_col_iclaim,
            c_final_col_iclaim,
            c_rs_col_iclaim,
            c_ws_col_iclaim,
        )?;

        // some sanity checks
        let level = state.curr_gkr_level - 1;
        assert!(level == state.n || level == state.m);
        assert!(state_n.level == state.n + 1);
        assert!(state_m.level == state.m + 1);

        // get r_n and r_m from GKR challenges
        let (r_batch_n, r_n) = GKR::batch_verifier_evaluation_points(state_n);
        assert!(r_n.len() == state.n);
        state.r_n = Some(r_n.clone());
        let (r_batch_m, r_m) = GKR::batch_verifier_evaluation_points(state_m);
        for i in 0..state.m {
            assert!(r_m[i] == state.r_m.as_ref().unwrap()[i]);
        }

        let compute_final_claim =
            |t_1: F, t_2: F, t_3: F, gamma_1: F, gamma_2: F| -> Result<F, Error> {
                Ok(compress_tuple(vec![t_1, t_2, t_3], gamma_1, gamma_2))
            };

        // get final evaluations of the locally computed polynomials
        let v_eq_x = evaluate_eq_extension(&r_x, &r_n, state.n);
        let v_eq_y = evaluate_eq_extension(&r_y, &r_n, state.n);
        let v_idx_n = evaluate_idx_mle(state.n, &r_n);

        let init_row_fclaim = compute_final_claim(v_idx_n, v_eq_x, F::zero(), gamma_1, gamma_2)?;
        let init_col_fclaim = compute_final_claim(v_idx_n, v_eq_y, F::zero(), gamma_1, gamma_2)?;
        let a_final_row_fclaim =
            compute_final_claim(v_idx_n, v_eq_x, p_msg_2.v_a_row_final_n, gamma_1, gamma_2)?;
        let a_final_col_fclaim =
            compute_final_claim(v_idx_n, v_eq_y, p_msg_2.v_a_col_final_n, gamma_1, gamma_2)?;
        let b_final_row_fclaim =
            compute_final_claim(v_idx_n, v_eq_x, p_msg_2.v_b_row_final_n, gamma_1, gamma_2)?;
        let b_final_col_fclaim =
            compute_final_claim(v_idx_n, v_eq_y, p_msg_2.v_b_col_final_n, gamma_1, gamma_2)?;
        let c_final_row_fclaim =
            compute_final_claim(v_idx_n, v_eq_x, p_msg_2.v_c_row_final_n, gamma_1, gamma_2)?;
        let c_final_col_fclaim =
            compute_final_claim(v_idx_n, v_eq_y, p_msg_2.v_c_col_final_n, gamma_1, gamma_2)?;

        let a_rs_row_fclaim = compute_final_claim(
            p_msg_2.v_a_row_m,
            p_msg_1.v_a_rx,
            p_msg_2.v_a_row_read_m,
            gamma_1,
            gamma_2,
        )?;
        let a_rs_col_fclaim = compute_final_claim(
            p_msg_2.v_a_col_m,
            p_msg_1.v_a_ry,
            p_msg_2.v_a_col_read_m,
            gamma_1,
            gamma_2,
        )?;
        let b_rs_row_fclaim = compute_final_claim(
            p_msg_2.v_b_row_m,
            p_msg_1.v_b_rx,
            p_msg_2.v_b_row_read_m,
            gamma_1,
            gamma_2,
        )?;
        let b_rs_col_fclaim = compute_final_claim(
            p_msg_2.v_b_col_m,
            p_msg_1.v_b_ry,
            p_msg_2.v_b_col_read_m,
            gamma_1,
            gamma_2,
        )?;
        let c_rs_row_fclaim = compute_final_claim(
            p_msg_2.v_c_row_m,
            p_msg_1.v_c_rx,
            p_msg_2.v_c_row_read_m,
            gamma_1,
            gamma_2,
        )?;
        let c_rs_col_fclaim = compute_final_claim(
            p_msg_2.v_c_col_m,
            p_msg_1.v_c_ry,
            p_msg_2.v_c_col_read_m,
            gamma_1,
            gamma_2,
        )?;
        let a_ws_row_fclaim = compute_final_claim(
            p_msg_2.v_a_row_m,
            p_msg_1.v_a_rx,
            p_msg_2.v_a_row_read_m + F::one(),
            gamma_1,
            gamma_2,
        )?;
        let a_ws_col_fclaim = compute_final_claim(
            p_msg_2.v_a_col_m,
            p_msg_1.v_a_ry,
            p_msg_2.v_a_col_read_m + F::one(),
            gamma_1,
            gamma_2,
        )?;
        let b_ws_row_fclaim = compute_final_claim(
            p_msg_2.v_b_row_m,
            p_msg_1.v_b_rx,
            p_msg_2.v_b_row_read_m + F::one(),
            gamma_1,
            gamma_2,
        )?;
        let b_ws_col_fclaim = compute_final_claim(
            p_msg_2.v_b_col_m,
            p_msg_1.v_b_ry,
            p_msg_2.v_b_col_read_m + F::one(),
            gamma_1,
            gamma_2,
        )?;
        let c_ws_row_fclaim = compute_final_claim(
            p_msg_2.v_c_row_m,
            p_msg_1.v_c_rx,
            p_msg_2.v_c_row_read_m + F::one(),
            gamma_1,
            gamma_2,
        )?;
        let c_ws_col_fclaim = compute_final_claim(
            p_msg_2.v_c_col_m,
            p_msg_1.v_c_ry,
            p_msg_2.v_c_col_read_m + F::one(),
            gamma_1,
            gamma_2,
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
        final_claims_m.extend(vec![F::zero(); 4]);

        // check that the final sumchecks claims are correct
        let claim_n = state_n.current_claim;
        let claim_m = state_m.current_claim;

        let final_claims_n = DenseMultilinearExtension::from_evaluations_vec(3, final_claims_n);
        let final_claims_m = DenseMultilinearExtension::from_evaluations_vec(4, final_claims_m);
        let expected_claim_n = final_claims_n.evaluate(&r_batch_n).unwrap();
        let expected_claim_m = final_claims_m.evaluate(&r_batch_m).unwrap();

        if claim_n != expected_claim_n {
            return Err(Error::Reject(Some(
                "Claim output by GKR final sumcheck for n instances is incorrect".into(),
            )));
        }
        if claim_m != expected_claim_m {
            return Err(Error::Reject(Some(
                "Claim output by GKR final sumcheck for m instances is incorrect".into(),
            )));
        }

        let r_m_lin_comb =
            sponge.squeeze_field_elements_with_sizes::<F>(vec![CHALLENGE_SIZE; 1].as_slice())[0];
        Ok(VerifierFourthMsg {
            r_m_lin_comb,
            r_m_ext: r_batch_m,
            r_n_ext: r_batch_n,
        })
    }
}

pub fn evaluate_eq_extension<F: PrimeField>(point_1: &Vec<F>, point_2: &Vec<F>, nv: usize) -> F {
    assert!(point_1.len() == nv, "point_1 must be of length nv");
    assert!(
        point_2.len() == point_1.len(),
        "point_1 length must equal point_2 length"
    );
    let mut ret = F::one();
    for i in 0..nv {
        ret *= point_1[i] * point_2[i] + (F::one() - point_1[i]) * (F::one() - point_2[i]);
    }
    ret
}

pub fn compress_tuple<F: PrimeField>(tuple: Vec<F>, gamma_1: F, gamma_2: F) -> F {
    let mut eval = F::zero() - gamma_2;
    let mut multiplier = F::one();
    for mle_eval in tuple {
        eval += multiplier * mle_eval;
        multiplier *= gamma_1;
    }
    eval
}

// note that idx_MLE is the same as the polynomial that converts bits to integer
// so its i-th coefficient is 2^i (going from least significant to most significant)
pub fn evaluate_idx_mle<F: PrimeField>(nv: usize, r: &Vec<F>) -> F {
    let mut ret = F::zero();
    let mut multiplier = F::one();
    let two = F::one() + F::one();
    for i in 0..nv {
        ret += r[i] * multiplier;
        multiplier *= two;
    }
    ret
}
