use crate::spartan::{constraints::SpartanVar as SpartanGadget, Spartan};
use crate::{
    spartan::constraints::IndexVerifierKeyVar as SpartanVKVar,
    spartan::constraints::InputInstanceVar as SpartanInputVar,
    spartan::constraints::ProofVar as SpartanProofVar,
    spartan::data_structures::IndexVerifierKey as SpartanVK,
    spartan::data_structures::InputInstance as SpartanInput,
    spartan::data_structures::Proof as SpartanProof,
};
use ark_bn254::{
    constraints::PairingVar as BN254PairingVar, Bn254 as BN254PairingEngine, Fq as BN254Fq,
    Fr as BN254Fr,
};
use ark_crypto_primitives::crh::{constraints::CRHSchemeGadget, CRHScheme};
use ark_crypto_primitives::snark::constraints::SNARKGadget;
use ark_crypto_primitives::snark::{FromFieldElementsGadget, NonNativeFieldInputVar};
use ark_crypto_primitives::{
    crh::sha256::{
        constraints::{Sha256Gadget, UnitVar},
        Sha256,
    },
    snark::BooleanInputVar,
};
use ark_ff::{to_bytes, BigInteger, FpParameters, One, PrimeField};
use ark_groth16::{constraints::Groth16VerifierGadget, Groth16};
use ark_groth16::{Proof as Groth16Proof, VerifyingKey as GrothVerifyingKey};
use ark_grumpkin::{constraints::GVar as GrumpkinGVar, Affine as GrumpkinAffine};
use ark_marlin::sponge::CryptographicSpongeVarNonNative;
use ark_marlin::CryptographicSpongeWithRate;
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::prelude::UInt8;
use ark_r1cs_std::ToConstraintFieldGadget;
use ark_r1cs_std::{
    alloc::AllocVar, eq::EqGadget, fields::fp::AllocatedFp, fields::fp::FpVar, R1CSVar,
    ToBitsGadget, ToBytesGadget,
};
use ark_relations::{
    lc, ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};
use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_sponge::{absorb, absorb_gadget, FieldBasedCryptographicSponge};
use ark_sponge::{
    constraints::CryptographicSpongeVar, poseidon::PoseidonSponge, CryptographicSponge,
};

use crate::spartan::SPONGE_RATE;

type MainField = BN254Fr;
type HelpField = BN254Fq;
type Groth = Groth16<BN254PairingEngine>;
type GrothGadget = Groth16VerifierGadget<BN254PairingEngine, BN254PairingVar>;
type GrothProof = Groth16Proof<BN254PairingEngine>;
type GrothVK = GrothVerifyingKey<BN254PairingEngine>;
type MainCRH = PoseidonSponge<MainField>;
type MainCRHGadget = PoseidonSpongeVar<MainField>;
type MainSponge = PoseidonSponge<MainField>;
type MainSpongeVar = PoseidonSpongeVar<MainField>;
type CRHSC = Sha256;
type MainCRHSCGadget = Sha256Gadget<MainField>;
type HelpCRHSCGadget = Sha256Gadget<HelpField>;
const MainFieldMaxSize: usize = 8 * (<MainField as PrimeField>::Params::CAPACITY / 8) as usize;

type SIMDSpartan = Spartan<GrumpkinAffine, MainSponge>;
type SIMDSpartanGadget = SpartanGadget<GrumpkinAffine, GrumpkinGVar, MainSponge, MainSpongeVar>;
type SIMDSpartanInput = SpartanInput<HelpField>;
type SIMDSpartanProof = SpartanProof<GrumpkinAffine>;
type SIMDSpartanVK = SpartanVK<GrumpkinAffine>;
type SIMDSpartanInputVar = SpartanInputVar<GrumpkinAffine>;
type SIMDSpartanProofVar = SpartanProofVar<GrumpkinAffine, GrumpkinGVar>;
type SIMDSpartanVKVar = SpartanVKVar<GrumpkinAffine, GrumpkinGVar>;
// const HelpFieldMaxSize: usize = 8 * (<HelpField as PrimeField>::Params::CAPACITY / 8) as usize;

#[derive(Copy, Clone)]
struct ZebraConfig {
    pub num_constraints_per_client: usize,
    pub num_witnesses_per_client: usize,
    pub num_inputs_per_client: usize,
    pub num_client_specific_inputs: usize,
    pub num_clients: usize,
}

#[derive(Clone)]
struct GrothClientCircuitV1 {
    a: MainField,
    b: MainField,
    config: ZebraConfig,
}

impl GrothClientCircuitV1 {
    pub fn circuit_inputs(&self) -> (Vec<MainField>, Vec<MainField>, MainField, Vec<u8>) {
        let c = self.a * self.b;

        let num_client_independent_inputs =
            self.config.num_inputs_per_client - self.config.num_client_specific_inputs;
        let input_ind = vec![c; num_client_independent_inputs];
        // compute hash of client independent inputs with MainCRH and set it as input to the circuit
        let c_bytes_ind = to_bytes!(input_ind).unwrap();
        let mut crh = MainCRH::from_rate(SPONGE_RATE);
        absorb!(&mut crh, c_bytes_ind);
        let input_hash_ind = crh.squeeze_native_field_elements(1).pop().unwrap();

        let num_client_specific_inputs = self.config.num_client_specific_inputs;
        let input_sc = vec![c; num_client_specific_inputs];
        // compute hash of client specific inputs with CRHSC and set it as input to the circuit
        let c_bytes_sc = to_bytes!(input_sc).unwrap();
        let input_hash_sc = <CRHSC as CRHScheme>::evaluate(&(), c_bytes_sc).unwrap();

        (input_ind, input_sc, input_hash_ind, input_hash_sc)
    }
}

/* Inputs:
   input_hash_ind (MainField as NativeVar)
   input_hash_sc (32*8 bits tightly packed into 32*8/MainFieldMaxSize MainField elements) (endianness: little-endian)
*/
impl ConstraintSynthesizer<MainField> for GrothClientCircuitV1 {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<MainField>,
    ) -> Result<(), SynthesisError> {
        let a_native = self.a;
        let b_native = self.b;
        let c_native = a_native * b_native;
        let a = cs.new_witness_variable(|| Ok(a_native))?;
        let b = cs.new_witness_variable(|| Ok(b_native))?;
        let c = cs.new_witness_variable(|| Ok(c_native))?;
        let c_fp = FpVar::Var(AllocatedFp::new(Some(c_native), c, cs.clone()));
        for _ in 0..(self.config.num_witnesses_per_client - 4) {
            cs.new_witness_variable(|| Ok(a_native))?;
        }

        for _ in 0..self.config.num_constraints_per_client {
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)
                .unwrap();
        }
        let (_, _, input_hash_ind_native, input_hash_sc_native) = self.circuit_inputs();

        // check consistency of witness and input_ind
        let num_client_independent_inputs =
            self.config.num_inputs_per_client - self.config.num_client_specific_inputs;
        let input_ind = FpVar::new_input(cs.clone(), || Ok(input_hash_ind_native))?;
        let mut c_bytes = Vec::new();
        for _ in 0..num_client_independent_inputs {
            c_bytes.append(&mut c_fp.to_bytes()?);
        }
        let mut crh_var =
            <MainCRHGadget as CryptographicSpongeVarNonNative<HelpField, _, _>>::from_rate(
                cs.clone(),
                SPONGE_RATE,
            );
        absorb_gadget!(&mut crh_var, c_bytes);
        let expected_input = crh_var.squeeze_field_elements(1)?.pop().unwrap();
        input_ind.enforce_equal(&expected_input)?;

        // check consistency of witness and input_sc
        let num_client_specific_inputs = self.config.num_client_specific_inputs;
        let input_sc = UInt8::new_input_vec(cs.clone(), &input_hash_sc_native)?;
        let mut c_bytes = Vec::new();
        for _ in 0..num_client_specific_inputs {
            c_bytes.append(&mut c_fp.to_bytes()?);
        }
        let expected_input = <MainCRHSCGadget as CRHSchemeGadget<CRHSC, MainField>>::evaluate(
            &UnitVar::default(),
            &c_bytes,
        )?
        .to_bytes()?;
        input_sc.enforce_equal(&expected_input)?;

        if cs.is_in_setup_mode() {
            println!("Groth Client Constraints: {}", cs.num_constraints());
            println!("Groth Client Inputs: {}", cs.num_instance_variables());
            println!("Groth Client Witnesses: {}", cs.num_witness_variables());
        } else {
            assert!(cs.is_satisfied().is_ok());
        }
        Ok(())
    }
}

#[derive(Clone)]
struct GrothClientCircuitV2 {
    a: MainField,
    b: MainField,
    config: ZebraConfig,
}

impl GrothClientCircuitV2 {
    pub fn circuit_inputs(&self) -> (Vec<MainField>, Vec<MainField>, MainField, Vec<u8>) {
        let c = self.a * self.b;

        let num_client_independent_inputs =
            self.config.num_inputs_per_client - self.config.num_client_specific_inputs;
        let input_ind = vec![c; num_client_independent_inputs];
        // compute hash of client independent inputs with MainCRH and set it as input to the circuit
        let c_bytes_ind = to_bytes!(input_ind).unwrap();
        let mut crh = MainCRH::from_rate(SPONGE_RATE);
        absorb!(&mut crh, c_bytes_ind);
        let input_hash_ind = crh.squeeze_native_field_elements(1).pop().unwrap();

        let num_client_specific_inputs = self.config.num_client_specific_inputs;
        let input_sc = vec![c; num_client_specific_inputs];
        // compute hash of client specific inputs with CRHSC and set it as input to the circuit
        let c_bytes_sc = to_bytes!(input_sc).unwrap();
        let input_hash_sc = <CRHSC as CRHScheme>::evaluate(&(), c_bytes_sc).unwrap();

        (input_ind, input_sc, input_hash_ind, input_hash_sc)
    }
}

/* Inputs:
   input_hash_ind (MainField as NativeVar)
   inputs_hash_sc (num_client_specific MainField elements as NativeVar)
*/
impl ConstraintSynthesizer<MainField> for GrothClientCircuitV2 {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<MainField>,
    ) -> Result<(), SynthesisError> {
        let a_native = self.a;
        let b_native = self.b;
        let c_native = a_native * b_native;
        let a = cs.new_witness_variable(|| Ok(a_native))?;
        let b = cs.new_witness_variable(|| Ok(b_native))?;
        let c = cs.new_witness_variable(|| Ok(c_native))?;
        let c_fp = FpVar::Var(AllocatedFp::new(Some(c_native), c, cs.clone()));
        for _ in 0..(self.config.num_witnesses_per_client - 4) {
            cs.new_witness_variable(|| Ok(a_native))?;
        }

        for _ in 0..self.config.num_constraints_per_client {
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)
                .unwrap();
        }
        let (_, input_sc, input_hash_ind_native, _) = self.circuit_inputs();

        // check consistency of witness and input_ind
        let num_client_independent_inputs =
            self.config.num_inputs_per_client - self.config.num_client_specific_inputs;
        let input_ind = FpVar::new_input(cs.clone(), || Ok(input_hash_ind_native))?;
        let mut c_bytes = Vec::new();
        for _ in 0..num_client_independent_inputs {
            c_bytes.append(&mut c_fp.to_bytes()?);
        }
        let mut crh_var =
            <MainCRHGadget as CryptographicSpongeVarNonNative<HelpField, _, _>>::from_rate(
                cs.clone(),
                SPONGE_RATE,
            );
        absorb_gadget!(&mut crh_var, c_bytes);
        let expected_input = crh_var.squeeze_field_elements(1)?.pop().unwrap();
        input_ind.enforce_equal(&expected_input)?;

        // input all inputs_sc
        for input in input_sc {
            cs.new_input_variable(|| Ok(input))?;
        }

        if cs.is_in_setup_mode() {
            println!("Groth Client Constraints: {}", cs.num_constraints());
            println!("Groth Client Inputs: {}", cs.num_instance_variables());
            println!("Groth Client Witnesses: {}", cs.num_witness_variables());
        } else {
            assert!(cs.is_satisfied().is_ok());
        }
        Ok(())
    }
}

// More work for user, less work for aggregator
#[derive(Clone)]
struct SpartanCircuitV1 {
    groth_proof: GrothProof,
    inputs_hash_ind: MainField,
    inputs_hash_sc: Vec<u8>,
    vk: GrothVK,
    pre_hash: Vec<u8>,
    post_hash: Vec<u8>,
}

/* Inputs:
   input_hash_ind (MainField as bits)
   input_hash_sc (32*8 bits tightly packed into 32*8/HelpFieldMaxSize HelpField elements) (endianness: little-endian)
   pre_hash (32*8 bits tightly packed into 32*8/HelpFieldMaxSize HelpField elements) (endianness: little-endian)
   post_hash (32*8 bits tightly packed into 32*8/HelpFieldMaxSize HelpField elements) (endianness: little-endian)
*/
impl ConstraintSynthesizer<HelpField> for SpartanCircuitV1 {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<HelpField>,
    ) -> Result<(), SynthesisError> {
        // input input_hash_ind and input_hash_sc
        // will be mapped to a single HelpField element. Only works because HelpField > MainField
        let help_input_hash_ind: Vec<HelpField> =
            BooleanInputVar::repack_input(&vec![self.inputs_hash_ind]);
        assert!(help_input_hash_ind.len() == 1);
        let mut input_hash_ind = Vec::new();
        for input in help_input_hash_ind {
            input_hash_ind.push(FpVar::new_input(ns!(cs, "input_hash_ind"), || Ok(input))?);
        }
        let input_hash_sc = UInt8::new_input_vec(ns!(cs, "input_hash_sc"), &self.inputs_hash_sc)?;

        // input pre-hash and post-hash
        let pre_hash_var = UInt8::new_input_vec(ns!(cs, "pre_hash"), &self.pre_hash)?;
        let mut hash_input = pre_hash_var;
        hash_input.extend(input_hash_sc.clone());
        let post_hash_var = UInt8::new_input_vec(ns!(cs, "post_hash"), &self.post_hash)?;

        let post_hash_var_expected =
            <HelpCRHSCGadget as CRHSchemeGadget<CRHSC, HelpField>>::evaluate(
                &UnitVar::default(),
                &hash_input,
            )?
            .to_bytes()?;
        post_hash_var.enforce_equal(&post_hash_var_expected)?;

        // verify Groth proof
        let mut input = Vec::new();
        // convert input_hash_ind and input_hash_sc to BooleanInputVar
        // first input_hash_ind
        for input_ind in input_hash_ind {
            input.push(input_ind.to_bits_le()?);
        }
        // then input_hash_sc
        let input_hash_sc_bits = input_hash_sc.to_bits_le()?;
        let input_hash_sc_bits_as_chunks = input_hash_sc_bits
            .chunks(MainFieldMaxSize)
            .collect::<Vec<_>>();
        for input_chunk in input_hash_sc_bits_as_chunks {
            let input_chunk = input_chunk.to_vec();
            input.push(input_chunk);
        }
        let input = <GrothGadget as SNARKGadget<MainField, HelpField, Groth>>::InputVar::new(input);
        // input proof and vk
        let proof_var =
            <GrothGadget as SNARKGadget<MainField, HelpField, Groth>>::ProofVar::new_witness(
                ns!(cs, "alloc_proof"),
                || Ok(self.groth_proof),
            )?;
        let vk_var = <GrothGadget as SNARKGadget<
            MainField,
            HelpField,
            Groth,
        >>::VerifyingKeyVar::new_constant(ns!(cs, "alloc_vk"), self.vk.clone())?;
        <GrothGadget as SNARKGadget<MainField, HelpField, Groth>>::verify(
            &vk_var, &input, &proof_var,
        )?
        .enforce_equal(&Boolean::TRUE)?;

        if cs.is_in_setup_mode() {
            println!("Spartan Constraints: {}", cs.num_constraints());
            println!("Spartan Inputs: {}", cs.num_instance_variables());
            println!("Spartan Witnesses: {}", cs.num_witness_variables());
        }
        Ok(())
    }
}

// More work for aggregator, less work for user
#[derive(Clone)]
struct SpartanCircuitV2 {
    groth_proof: GrothProof,
    inputs_hash_ind: MainField,
    inputs_sc: Vec<MainField>,
    inputs_hash_sc: Vec<u8>,
    vk: GrothVK,
    pre_hash: Vec<u8>,
    post_hash: Vec<u8>,
}

/* Inputs:
   input_hash_ind (MainField as bits)
   input_hash_sc (32*8 bits tightly packed into 32*8/HelpFieldMaxSize HelpField elements) (endianness: little-endian)
   pre_hash (32*8 bits tightly packed into 32*8/HelpFieldMaxSize HelpField elements) (endianness: little-endian)
   post_hash (32*8 bits tightly packed into 32*8/HelpFieldMaxSize HelpField elements) (endianness: little-endian)
*/
impl ConstraintSynthesizer<HelpField> for SpartanCircuitV2 {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<HelpField>,
    ) -> Result<(), SynthesisError> {
        // input input_hash_ind and input_hash_sc
        // will be mapped to a single HelpField element. Only works because HelpField > MainField
        let help_input_hash_ind: HelpField =
            BooleanInputVar::repack_input(&vec![self.inputs_hash_ind])
                .pop()
                .unwrap();
        let input_hash_ind =
            FpVar::new_input(ns!(cs, "input_hash_ind"), || Ok(help_input_hash_ind))?;
        let input_hash_sc = UInt8::new_input_vec(ns!(cs, "input_hash_sc"), &self.inputs_hash_sc)?;

        // input pre-hash and post-hash
        let pre_hash_var = UInt8::new_input_vec(ns!(cs, "pre_hash"), &self.pre_hash)?;
        let mut hash_input = pre_hash_var;
        hash_input.extend(input_hash_sc.clone());
        let post_hash_var = UInt8::new_input_vec(ns!(cs, "post_hash"), &self.post_hash)?;

        let post_hash_var_expected =
            <HelpCRHSCGadget as CRHSchemeGadget<CRHSC, HelpField>>::evaluate(
                &UnitVar::default(),
                &hash_input,
            )?
            .to_bytes()?;
        post_hash_var.enforce_equal(&post_hash_var_expected)?;

        // input all inputs_sc as witnesses
        let help_inputs_sc: Vec<HelpField> = BooleanInputVar::repack_input(&self.inputs_sc);
        assert!(help_inputs_sc.len() == self.inputs_sc.len());
        let mut inputs_sc = Vec::new();
        for input in help_inputs_sc {
            inputs_sc.push(FpVar::new_witness(ns!(cs, "inputs_sc"), || Ok(input))?);
        }

        // verify Groth proof
        let mut input = Vec::new();
        // convert input_hash_ind and input_hash_sc to BooleanInputVar
        // first input_hash_ind
        input.push(input_hash_ind.to_bits_le()?);
        // then inputs_sc
        for input_sc in inputs_sc {
            input.push(input_sc.to_bits_le()?);
        }
        let input_groth =
            <GrothGadget as SNARKGadget<MainField, HelpField, Groth>>::InputVar::new(input.clone());
        // input proof and vk
        let proof_var =
            <GrothGadget as SNARKGadget<MainField, HelpField, Groth>>::ProofVar::new_witness(
                ns!(cs, "alloc_proof"),
                || Ok(self.groth_proof),
            )?;
        let vk_var = <GrothGadget as SNARKGadget<
            MainField,
            HelpField,
            Groth,
        >>::VerifyingKeyVar::new_constant(ns!(cs, "alloc_vk"), self.vk.clone())?;
        <GrothGadget as SNARKGadget<MainField, HelpField, Groth>>::verify(
            &vk_var,
            &input_groth,
            &proof_var,
        )?
        .enforce_equal(&Boolean::TRUE)?;

        // check consistency with inputs_hash_sc
        let inputs_sc_bits = input[1..].to_vec();
        let mut inputs_sc_bytes = Vec::new();
        for mut input_bits in inputs_sc_bits {
            let num_bits = <HelpField as PrimeField>::BigInt::NUM_LIMBS * 64;
            let remainder =
                core::iter::repeat(Boolean::constant(false)).take(num_bits - input_bits.len());
            input_bits.extend(remainder);
            let mut bytes = input_bits
                .chunks(8)
                .map(UInt8::from_bits_le)
                .collect::<Vec<_>>();
            inputs_sc_bytes.append(&mut bytes);
        }
        let expected_inputs_hash_sc =
            <HelpCRHSCGadget as CRHSchemeGadget<CRHSC, HelpField>>::evaluate(
                &UnitVar::default(),
                &inputs_sc_bytes,
            )?
            .to_bytes()?;
        input_hash_sc.enforce_equal(&expected_inputs_hash_sc)?;

        if cs.is_in_setup_mode() {
            println!("Spartan Constraints: {}", cs.num_constraints());
            println!("Spartan Inputs: {}", cs.num_instance_variables());
            println!("Spartan Witnesses: {}", cs.num_witness_variables());
        }
        Ok(())
    }
}

#[derive(Clone)]
struct GrothServerCircuit {
    spartan_proof: SIMDSpartanProof,
    inputs_hash_sc: Vec<Vec<u8>>,
    inputs_ind: Vec<MainField>,
    vk: SIMDSpartanVK,
    config: ZebraConfig,
}

impl GrothServerCircuit {
    pub fn compute_pre_post_hashes(input_hash_sc: &Vec<Vec<u8>>) -> (Vec<Vec<u8>>, Vec<Vec<u8>>) {
        let num_clients = input_hash_sc.len();
        let mut pre_hash_vec = Vec::new();
        let mut post_hash_vec = Vec::new();
        let curr_pre_hash = &vec![0u8; 32];
        for i in 0..num_clients {
            pre_hash_vec.push(curr_pre_hash.clone());
            let curr_hash = &input_hash_sc[i];
            let mut hash_input = curr_pre_hash.clone();
            hash_input.extend(curr_hash);
            let curr_post_hash = <CRHSC as CRHScheme>::evaluate(&(), hash_input).unwrap();
            post_hash_vec.push(curr_post_hash);
        }
        (pre_hash_vec, post_hash_vec)
    }
}

/* Inputs:
   inputs_ind (num_client_independent_inputs many MainField elements as NativeVars)
   initial_hash (32*8 bits tightly packed into 32*8/MainFieldMaxSize MainField elements) (endianness: little-endian)
   final_hash (32*8 bits tightly packed into 32*8/MainFieldMaxSize MainField elements) (endianness: little-endian)
*/
impl ConstraintSynthesizer<MainField> for GrothServerCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<MainField>,
    ) -> Result<(), SynthesisError> {
        assert!(
            self.config.num_inputs_per_client - self.config.num_client_specific_inputs
                == self.inputs_ind.len()
        );
        assert!(self.config.num_clients == self.inputs_hash_sc.len());

        // computing vectors of pre_hash, input_hash_sc, and post_hash for each client
        let (pre_hash_vec_native, post_hash_vec_native) =
            GrothServerCircuit::compute_pre_post_hashes(&self.inputs_hash_sc);
        let mut pre_hash_vec = Vec::new();
        let mut inputs_hash_sc = Vec::new();
        let mut post_hash_vec = Vec::new();
        for i in 0..self.config.num_clients {
            pre_hash_vec.push(UInt8::new_witness_vec(cs.clone(), &pre_hash_vec_native[i])?);
            inputs_hash_sc.push(UInt8::new_witness_vec(cs.clone(), &self.inputs_hash_sc[i])?);
            post_hash_vec.push(UInt8::new_witness_vec(
                cs.clone(),
                &post_hash_vec_native[i],
            )?);
        }

        let mut inputs_ind = Vec::new();
        for input in self.inputs_ind {
            inputs_ind.push(FpVar::new_input(cs.clone(), || Ok(input))?);
        }
        let initial_hash = UInt8::new_input_vec(cs.clone(), &pre_hash_vec_native[0])?;
        let final_hash = UInt8::new_input_vec(
            cs.clone(),
            &post_hash_vec_native[self.config.num_clients - 1],
        )?;
        // check consistency of pre and post hashes with inputs
        pre_hash_vec[0].enforce_equal(&initial_hash)?;
        post_hash_vec[self.config.num_clients - 1].enforce_equal(&final_hash)?;

        // compute hash of inputs_ind
        let mut input_ind_bytes = Vec::new();
        for input_ind in inputs_ind {
            input_ind_bytes.append(&mut input_ind.to_bytes()?);
        }
        let mut crh_var =
            <MainCRHGadget as CryptographicSpongeVarNonNative<HelpField, _, _>>::from_rate(
                cs.clone(),
                SPONGE_RATE,
            );
        absorb_gadget!(&mut crh_var, input_ind_bytes);
        // inputs_hash_ind as a MainField element
        let inputs_hash_ind = crh_var.squeeze_field_elements(1)?.pop().unwrap();

        // Vector of HelpField (nonnative) elements passed to the Spartan server circuit
        let mut spartan_circuit_inputs = Vec::new();
        for i in 0..self.config.num_clients {
            // first construct the MainField input elements per client
            let mut main_client_input = Vec::new();
            main_client_input.push(inputs_hash_ind.clone());
            main_client_input.extend(inputs_hash_sc[i].to_constraint_field()?);
            main_client_input.extend(pre_hash_vec[i].to_constraint_field()?);
            main_client_input.extend(post_hash_vec[i].to_constraint_field()?);
            let mut help_client_input_wrapped: NonNativeFieldInputVar<HelpField, MainField> =
                NonNativeFieldInputVar::from_field_elements(&main_client_input)?;
            // Spartan takes formatted input with first element always one
            let mut help_client_input = vec![NonNativeFieldVar::new_constant(
                cs.clone(),
                HelpField::one(),
            )?];
            help_client_input.append(&mut help_client_input_wrapped.val);
            spartan_circuit_inputs.push(help_client_input);
        }
        let spartan_circuit_inputs = SIMDSpartanInputVar {
            formatted_input: spartan_circuit_inputs,
        };
        // input vk and proof
        let vk = SIMDSpartanVKVar::new_constant(cs.clone(), self.vk.clone())?;
        let proof = SIMDSpartanProofVar::new_witness(cs.clone(), || Ok(self.spartan_proof))?;

        // Spartan SIMD Verification
        SIMDSpartanGadget::verify(cs.clone(), &vk, &spartan_circuit_inputs, &proof)?
            .enforce_equal(&Boolean::TRUE)?;

        if cs.is_in_setup_mode() {
            println!("Groth Server Constraints: {}", cs.num_constraints());
            println!("Groth Server Inputs: {}", cs.num_instance_variables());
            println!("Groth Server Witnesses: {}", cs.num_witness_variables());
        } else {
            assert!(cs.is_satisfied().is_ok());
        }

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use ark_crypto_primitives::SNARK;
    use ark_ff::{ToConstraintField, UniformRand};
    use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal, SynthesisMode};
    use ark_std::{cfg_iter, end_timer, start_timer};
    #[cfg(feature = "parallel")]
    use rayon::prelude::*;

    use super::*;

    fn test_zebra_v1(config: ZebraConfig) {
        let rng = &mut ark_std::test_rng();

        let a = MainField::rand(rng);
        let b = MainField::rand(rng);
        let groth_client_circuit = GrothClientCircuitV1 { a, b, config };
        let (input_ind, _, input_hash_ind, input_hash_sc) = groth_client_circuit.circuit_inputs();

        let groth_client_setup = start_timer!(|| "Groth Client Setup");
        let (groth_client_pk, groth_client_vk) =
            <Groth as SNARK<MainField>>::circuit_specific_setup(groth_client_circuit.clone(), rng)
                .unwrap();
        end_timer!(groth_client_setup);

        let groth_client_prove = start_timer!(|| "Groth Client Prove");
        let groth_client_proof =
            <Groth as SNARK<MainField>>::prove(&groth_client_pk, groth_client_circuit, rng)
                .unwrap();
        end_timer!(groth_client_prove);

        let groth_client_verify = start_timer!(|| "Groth Client Verify");
        let mut groth_client_input = Vec::new();
        groth_client_input.push(input_hash_ind);
        groth_client_input.append(
            &mut ToConstraintField::<MainField>::to_field_elements(&input_hash_sc).unwrap(),
        );
        assert!(
            <Groth as SNARK::<MainField>>::verify(
                &groth_client_vk,
                &groth_client_input,
                &groth_client_proof
            )
            .is_ok(),
            "Groth Client Verification Failed"
        );
        end_timer!(groth_client_verify);

        let spartan_dummy_circuit = SpartanCircuitV1 {
            groth_proof: groth_client_proof.clone(),
            inputs_hash_ind: input_hash_ind,
            inputs_hash_sc: input_hash_sc.clone(),
            vk: groth_client_vk.clone(),
            pre_hash: vec![0u8; 32],
            post_hash: vec![0u8; 32],
        };

        let spartan_setup = start_timer!(|| "Spartan Setup");
        let (spartan_pk, spartan_vk) =
            SIMDSpartan::circuit_specific_setup(config.num_clients, spartan_dummy_circuit).unwrap();
        end_timer!(spartan_setup);

        // input_sc_vec = num_clients copies of input_sc
        let input_sc_vec = vec![input_hash_sc.clone(); config.num_clients];
        let (pre_hash_vec, post_hash_vec) =
            GrothServerCircuit::compute_pre_post_hashes(&input_sc_vec);

        let spartan_input_witness = start_timer!(|| "Spartan Input and Witness Construction");
        let index = (0..config.num_clients).collect::<Vec<usize>>();
        let (spartan_input, spartan_witness) = cfg_iter!(index)
            .map(|&i| {
                let circ = SpartanCircuitV1 {
                    groth_proof: groth_client_proof.clone(),
                    inputs_hash_ind: input_hash_ind.clone(),
                    inputs_hash_sc: input_hash_sc.clone(),
                    vk: groth_client_vk.clone(),
                    pre_hash: pre_hash_vec[i].clone(),
                    post_hash: post_hash_vec[i].clone(),
                };
                SIMDSpartan::get_input_and_witness(&spartan_pk, circ, false).unwrap()
            })
            .unzip();
        end_timer!(spartan_input_witness);

        let spartan_prove = start_timer!(|| "Spartan Prove");
        let spartan_proof =
            SIMDSpartan::prove(&spartan_pk, &spartan_input, spartan_witness).unwrap();
        end_timer!(spartan_prove);

        let spartan_verify = start_timer!(|| "Spartan Verify");
        let help_input_hash_ind: Vec<HelpField> =
            BooleanInputVar::repack_input(&vec![input_hash_ind]);
        let mut spartan_input = Vec::new();
        for i in 0..config.num_clients {
            let mut per_client_input = Vec::new();
            per_client_input.push(HelpField::one());
            per_client_input.extend(help_input_hash_ind.clone());
            per_client_input.append(
                &mut ToConstraintField::<HelpField>::to_field_elements(&input_sc_vec[i]).unwrap(),
            );
            per_client_input.append(
                &mut ToConstraintField::<HelpField>::to_field_elements(&pre_hash_vec[i]).unwrap(),
            );
            per_client_input.append(
                &mut ToConstraintField::<HelpField>::to_field_elements(&post_hash_vec[i]).unwrap(),
            );
            spartan_input.push(per_client_input);
        }
        let spartan_input = SIMDSpartanInput::new(spartan_input);
        assert!(
            SIMDSpartan::verify(&spartan_vk, spartan_input, &spartan_proof).is_ok(),
            "Spartan Verification Failed"
        );
        end_timer!(spartan_verify);

        let groth_server_circuit = GrothServerCircuit {
            spartan_proof,
            inputs_hash_sc: input_sc_vec,
            inputs_ind: input_ind.clone(),
            vk: spartan_vk.clone(),
            config: config,
        };

        let constraint_time = start_timer!(|| "Generating Groth Server constraints");
        let cs = ConstraintSystem::<MainField>::new_ref();
        let start_cost = cs.num_constraints();
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        cs.set_mode(SynthesisMode::Setup);
        groth_server_circuit.generate_constraints(cs.clone());
        println!(
            "Cost of verifying Spartan proof {:?}",
            cs.num_constraints() - start_cost
        );
        end_timer!(constraint_time);

        // Groth server verification is slow in arkworks
        // Getting constraints for Groth server verification
        // and benchmarking them in gnark
        /*
        let groth_server_setup = start_timer!(|| "Groth Server Setup");
        let (groth_server_pk, groth_server_vk) =
            <Groth as SNARK<MainField>>::circuit_specific_setup(groth_server_circuit.clone(), rng)
                .unwrap();
        end_timer!(groth_server_setup);

        let groth_server_prove = start_timer!(|| "Groth Server Prove");
        let groth_server_proof =
            <Groth as SNARK<MainField>>::prove(&groth_server_pk, groth_server_circuit, rng)
                .unwrap();
        end_timer!(groth_server_prove);

        let groth_server_verify = start_timer!(|| "Groth Server Verify");
        let mut groth_server_input = Vec::new();
        for input in input_ind {
            groth_server_input.push(input);
        }
        groth_server_input.append(
            &mut ToConstraintField::<MainField>::to_field_elements(&pre_hash_vec[0]).unwrap(),
        );
        groth_server_input.append(
            &mut ToConstraintField::<MainField>::to_field_elements(
                &post_hash_vec[config.num_clients - 1],
            )
            .unwrap(),
        );
        assert!(
            <Groth as SNARK::<MainField>>::verify(
                &groth_server_vk,
                &groth_server_input,
                &groth_server_proof
            )
            .is_ok(),
            "Groth Server Verification Failed"
        );
        end_timer!(groth_server_verify);
        */
    }

    fn test_zebra_v2(config: ZebraConfig) {
        let rng = &mut ark_std::test_rng();

        let a = MainField::rand(rng);
        let b = MainField::rand(rng);
        let groth_client_circuit = GrothClientCircuitV2 { a, b, config };
        let (input_ind, input_sc, input_hash_ind, input_hash_sc) =
            groth_client_circuit.circuit_inputs();

        let groth_client_setup = start_timer!(|| "Groth Client Setup");
        let (groth_client_pk, groth_client_vk) =
            <Groth as SNARK<MainField>>::circuit_specific_setup(groth_client_circuit.clone(), rng)
                .unwrap();
        end_timer!(groth_client_setup);

        let groth_client_prove = start_timer!(|| "Groth Client Prove");
        let groth_client_proof =
            <Groth as SNARK<MainField>>::prove(&groth_client_pk, groth_client_circuit, rng)
                .unwrap();
        end_timer!(groth_client_prove);

        let groth_client_verify = start_timer!(|| "Groth Client Verify");
        let mut groth_client_input = Vec::new();
        groth_client_input.push(input_hash_ind);
        for input in &input_sc {
            groth_client_input.push(*input);
        }
        assert!(
            <Groth as SNARK::<MainField>>::verify(
                &groth_client_vk,
                &groth_client_input,
                &groth_client_proof
            )
            .is_ok(),
            "Groth Client Verification Failed"
        );
        end_timer!(groth_client_verify);

        let spartan_dummy_circuit = SpartanCircuitV2 {
            groth_proof: groth_client_proof.clone(),
            inputs_hash_ind: input_hash_ind,
            inputs_sc: input_sc.clone(),
            inputs_hash_sc: input_hash_sc.clone(),
            vk: groth_client_vk.clone(),
            pre_hash: vec![0u8; 32],
            post_hash: vec![0u8; 32],
        };

        let spartan_setup = start_timer!(|| "Spartan Setup");
        let (spartan_pk, spartan_vk) =
            SIMDSpartan::circuit_specific_setup(config.num_clients, spartan_dummy_circuit).unwrap();
        end_timer!(spartan_setup);

        // input_sc_vec = num_clients copies of input_sc
        let input_sc_vec = vec![input_hash_sc.clone(); config.num_clients];
        let (pre_hash_vec, post_hash_vec) =
            GrothServerCircuit::compute_pre_post_hashes(&input_sc_vec);

        let spartan_input_witness = start_timer!(|| "Spartan Input and Witness Construction");
        let index = (0..config.num_clients).collect::<Vec<usize>>();
        let (spartan_input, spartan_witness) = cfg_iter!(index)
            .map(|&i| {
                let circ = SpartanCircuitV2 {
                    groth_proof: groth_client_proof.clone(),
                    inputs_hash_ind: input_hash_ind.clone(),
                    inputs_sc: input_sc.clone(),
                    inputs_hash_sc: input_hash_sc.clone(),
                    vk: groth_client_vk.clone(),
                    pre_hash: pre_hash_vec[i].clone(),
                    post_hash: post_hash_vec[i].clone(),
                };
                // if i == 0 {
                //     SIMDSpartan::get_input_and_witness(&spartan_pk, circ, true).unwrap()
                // } else {
                //     SIMDSpartan::get_input_and_witness(&spartan_pk, circ, false).unwrap()
                // }
                SIMDSpartan::get_input_and_witness(&spartan_pk, circ, false).unwrap()
            })
            .unzip();
        end_timer!(spartan_input_witness);

        let spartan_prove = start_timer!(|| "Spartan Prove");
        let spartan_proof =
            SIMDSpartan::prove(&spartan_pk, &spartan_input, spartan_witness).unwrap();
        end_timer!(spartan_prove);

        let spartan_verify = start_timer!(|| "Spartan Verify");
        let help_input_hash_ind: Vec<HelpField> =
            BooleanInputVar::repack_input(&vec![input_hash_ind]);
        let mut spartan_input = Vec::new();
        for i in 0..config.num_clients {
            let mut per_client_input = Vec::new();
            per_client_input.push(HelpField::one());
            per_client_input.extend(help_input_hash_ind.clone());
            per_client_input.append(
                &mut ToConstraintField::<HelpField>::to_field_elements(&input_sc_vec[i]).unwrap(),
            );
            per_client_input.append(
                &mut ToConstraintField::<HelpField>::to_field_elements(&pre_hash_vec[i]).unwrap(),
            );
            per_client_input.append(
                &mut ToConstraintField::<HelpField>::to_field_elements(&post_hash_vec[i]).unwrap(),
            );
            spartan_input.push(per_client_input);
        }
        let spartan_input = SIMDSpartanInput::new(spartan_input);
        assert!(
            SIMDSpartan::verify(&spartan_vk, spartan_input, &spartan_proof).is_ok(),
            "Spartan Verification Failed"
        );
        end_timer!(spartan_verify);

        let groth_server_circuit = GrothServerCircuit {
            spartan_proof,
            inputs_hash_sc: input_sc_vec,
            inputs_ind: input_ind.clone(),
            vk: spartan_vk.clone(),
            config: config,
        };
        let groth_server_setup = start_timer!(|| "Groth Server Setup");
        let (groth_server_pk, groth_server_vk) =
            <Groth as SNARK<MainField>>::circuit_specific_setup(groth_server_circuit.clone(), rng)
                .unwrap();
        end_timer!(groth_server_setup);

        let groth_server_prove = start_timer!(|| "Groth Server Prove");
        let groth_server_proof =
            <Groth as SNARK<MainField>>::prove(&groth_server_pk, groth_server_circuit, rng)
                .unwrap();
        end_timer!(groth_server_prove);

        let groth_server_verify = start_timer!(|| "Groth Server Verify");
        let mut groth_server_input = Vec::new();
        for input in input_ind {
            groth_server_input.push(input);
        }
        groth_server_input.append(
            &mut ToConstraintField::<MainField>::to_field_elements(&pre_hash_vec[0]).unwrap(),
        );
        groth_server_input.append(
            &mut ToConstraintField::<MainField>::to_field_elements(
                &post_hash_vec[config.num_clients - 1],
            )
            .unwrap(),
        );
        assert!(
            <Groth as SNARK::<MainField>>::verify(
                &groth_server_vk,
                &groth_server_input,
                &groth_server_proof
            )
            .is_ok(),
            "Groth Server Verification Failed"
        );
        end_timer!(groth_server_verify);
    }

    #[test]
    fn test_big() {
        let config = ZebraConfig {
            num_constraints_per_client: 1 << 16,
            num_witnesses_per_client: 1 << 15,
            num_inputs_per_client: 24,
            num_client_specific_inputs: 11,
            num_clients: 512,
        };

        // test_zebra_v2(config);
        test_zebra_v1(config);
    }

    #[test]
    fn test_med() {
        let config = ZebraConfig {
            num_constraints_per_client: 1 << 16,
            num_witnesses_per_client: 1 << 15,
            num_inputs_per_client: 24,
            num_client_specific_inputs: 11,
            num_clients: 64,
        };

        // test_zebra_v2(config);
        test_zebra_v1(config);
    }

    #[test]
    fn test_small() {
        let config = ZebraConfig {
            num_constraints_per_client: 1 << 8,
            num_witnesses_per_client: 1 << 7,
            num_inputs_per_client: 5,
            num_client_specific_inputs: 2,
            num_clients: 4,
        };

        // test_zebra_v2(config);
        test_zebra_v1(config);
    }
}
