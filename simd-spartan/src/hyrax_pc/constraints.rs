use std::borrow::Borrow;
use std::marker::PhantomData;

use crate::dense_mle::DenseMLEVar;
use crate::NonNativeVar;
use crate::CF;
use crate::F;
use ark_ec::AffineCurve;
use ark_ff::{BigInteger, PrimeField};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::alloc::AllocationMode;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::prelude::EqGadget;
use ark_r1cs_std::prelude::UInt8;
use ark_r1cs_std::uint64::UInt64;
use ark_r1cs_std::ToBitsGadget;
use ark_r1cs_std::ToBytesGadget;
use ark_relations::r1cs::ConstraintSystemRef;
use ark_relations::r1cs::Namespace;
use ark_relations::r1cs::SynthesisError;
use ark_sponge::collect_sponge_field_elements_gadget;
use ark_sponge::constraints::bits_le_to_nonnative;
use ark_sponge::constraints::AbsorbGadget;
use ark_sponge::Absorb;
use ark_std::One;

use super::Commitment;
use super::Proof;
use super::VerifierKey;

pub struct VerifierKeyVar<G: AffineCurve, C: CurveVar<G::Projective, CF<G>>> {
    /// The key used to commit to polynomials.
    pub comm_key: Vec<C>,
    #[doc(hidden)]
    pub _curve: PhantomData<G>,
}

impl<G: AffineCurve, C: CurveVar<G::Projective, CF<G>>> VerifierKeyVar<G, C> {
    pub fn max_dim(&self) -> usize {
        2 * self.comm_key.len().trailing_zeros() as usize
    }
}

impl<G, C> AllocVar<VerifierKey<G>, CF<G>> for VerifierKeyVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, CF<G>>,
{
    fn new_variable<T: Borrow<VerifierKey<G>>>(
        cs: impl Into<Namespace<CF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|vk| {
            let vk = vk.borrow();
            let comm_key: Vec<C> = vk
                .comm_key
                .iter()
                .map(|g| C::new_variable(ns.clone(), || Ok(g.clone()), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;
            Ok(Self {
                comm_key,
                _curve: PhantomData,
            })
        })
    }
}

pub struct CommitmentVar<
    G: AffineCurve + Absorb,
    C: CurveVar<G::Projective, CF<G>> + AbsorbGadget<CF<G>>,
> {
    pub comm: Vec<C>,
    pub dim1: usize,
    pub dim2: usize,
    #[doc(hidden)]
    pub _curve: PhantomData<G>,
}

impl<G, C> AllocVar<Commitment<G>, CF<G>> for CommitmentVar<G, C>
where
    G: AffineCurve + Absorb,
    C: CurveVar<G::Projective, CF<G>> + AbsorbGadget<CF<G>>,
{
    fn new_variable<T: Borrow<Commitment<G>>>(
        cs: impl Into<Namespace<CF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|comm| {
            let comm = comm.borrow();
            let dim1 = comm.dim1;
            let dim2 = comm.dim2;
            let comm: Vec<C> = comm
                .comm
                .iter()
                .map(|c| {
                    // C::new_variable(ns.clone(), || Ok(c.clone()), mode)
                    C::new_variable_omit_prime_order_check(
                        ns.clone(),
                        || Ok(c.into_projective().clone()),
                        mode,
                    )
                })
                .collect::<Result<Vec<_>, SynthesisError>>()?;
            Ok(Self {
                comm,
                dim1,
                dim2,
                _curve: PhantomData,
            })
        })
    }
}

impl<G, C> AbsorbGadget<CF<G>> for CommitmentVar<G, C>
where
    G: AffineCurve + Absorb,
    C: CurveVar<G::Projective, CF<G>> + AbsorbGadget<CF<G>>,
{
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<CF<G>>>, SynthesisError> {
        let cs = self.comm[0].cs().clone();
        let dim1 = UInt64::<CF<G>>::new_constant(cs.clone(), self.dim1 as u64)?;
        let dim2 = UInt64::<CF<G>>::new_constant(cs.clone(), self.dim2 as u64)?;

        collect_sponge_field_elements_gadget!(&self.comm, &dim1.to_bytes()?, &dim2.to_bytes()?)
    }

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<CF<G>>>, SynthesisError> {
        todo!()
    }
}

pub struct ProofVar<G: AffineCurve> {
    pub elems: Vec<Vec<Boolean<CF<G>>>>,
    // providing bits of lagrange coeffs for first dimension
    // to save on cost of computing them circuit can just check
    // if the supplied bits are consistent with computed coeffs
    pub coeffs_dim_1: Vec<Vec<Boolean<CF<G>>>>,
}

impl<G: AffineCurve> AllocVar<Proof<G>, CF<G>> for ProofVar<G> {
    fn new_variable<T: Borrow<Proof<G>>>(
        cs: impl Into<Namespace<CF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|proof| {
            let proof = proof.borrow();
            let elems: Vec<Vec<Boolean<CF<G>>>> = proof
                .elems
                .iter()
                .map(|e| {
                    e.into_repr()
                        .to_bits_le()
                        .iter()
                        .map(|b| Boolean::new_variable(ns.clone(), || Ok(b.clone()), mode))
                        .collect::<Result<Vec<_>, SynthesisError>>()
                })
                .collect::<Result<Vec<_>, SynthesisError>>()?;
            // computing lagrange coefficients for the first dimension
            let dim1 = ((proof.point.len() as f32) / 2.0).floor() as usize;
            let one = G::ScalarField::one();
            let partial_point = &proof.point[..dim1];
            let mut coeffs_dim_1 = vec![one; 1 << dim1];
            for i in 0..dim1 {
                let r = partial_point[i];
                for b in 0..(1 << i) {
                    coeffs_dim_1[(1 << i) + b] = coeffs_dim_1[b] * r;
                    coeffs_dim_1[b] *= one - r;
                }
            }
            let coeffs_dim_1: Vec<Vec<Boolean<CF<G>>>> = coeffs_dim_1
                .iter()
                .map(|c| {
                    c.into_repr()
                        .to_bits_le()
                        .iter()
                        .map(|b| Boolean::new_variable(ns.clone(), || Ok(b.clone()), mode))
                        .collect::<Result<Vec<_>, SynthesisError>>()
                })
                .collect::<Result<Vec<_>, SynthesisError>>()?;
            Ok(Self {
                elems,
                coeffs_dim_1,
            })
        })
    }
}

pub struct MVPolyCommitmentVar<G: AffineCurve, C: CurveVar<G::Projective, CF<G>>> {
    _projective: PhantomData<G>,
    _curve: PhantomData<C>,
}

impl<G, C> MVPolyCommitmentVar<G, C>
where
    G: AffineCurve + Absorb,
    C: CurveVar<G::Projective, CF<G>> + AbsorbGadget<CF<G>>,
{
    pub fn check<'a>(
        cs: ConstraintSystemRef<CF<G>>,
        vk: &VerifierKeyVar<G, C>,
        comm: &CommitmentVar<G, C>,
        point: &Vec<NonNativeVar<G>>,
        value: &NonNativeVar<G>,
        proof: &ProofVar<G>,
    ) -> Result<Boolean<CF<G>>, SynthesisError> {
        let dim1 = comm.dim1;
        let dim2 = comm.dim2;
        assert!(point.len() == dim1 + dim2, "incorrect number of points");
        assert!(
            dim1 + dim2 <= vk.max_dim(),
            "current setup doesn't work for a poly with this many vars"
        );

        let start_cost = cs.num_constraints();
        let one: NonNativeVar<G> = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::one())?;
        let mut scalars = vec![one.clone(); 1 << dim1];
        let partial_point = &point[..dim1];
        for i in 0..dim1 {
            let r = &partial_point[i];
            let one_minus_r = &one - r;
            for b in 0..(1 << i) {
                scalars[(1 << i) + b] = &scalars[b] * r;
                scalars[b] *= &one_minus_r;
            }
        }
        let coeffs_dim_1_nonnative: Vec<NonNativeVar<G>> =
            bits_le_to_nonnative(cs.clone(), proof.coeffs_dim_1.iter())?;
        for i in 0..1 << dim1 {
            scalars[i].enforce_equal(&coeffs_dim_1_nonnative[i])?;
        }
        println!(
            "Cost of non_native arith per dim (dim1: {}): {:?}",
            dim1,
            (cs.num_constraints() - start_cost) / (1 << dim1)
        );
        let start_cost = cs.num_constraints();
        let actual_comm = C::multi_scalar_mul_le(&comm.comm, &proof.coeffs_dim_1)?;
        println!(
            "Cost of scalar_mul per dim (dim1: {}): {:?}",
            dim1,
            (cs.num_constraints() - start_cost) / (1 << dim1)
        );
        let start_cost = cs.num_constraints();
        let expected_comm =
            C::multi_scalar_mul_le(&vk.comm_key[..1 << dim2].to_vec(), &proof.elems)?;
        println!(
            "Cost of scalar_mul per dim (dim2: {}): {:?}",
            dim2,
            (cs.num_constraints() - start_cost) / (1 << dim2)
        );
        let comm_cond = actual_comm.is_eq(&expected_comm)?;

        let start_cost = cs.num_constraints();
        let partial_point = &point[dim1..];
        let proof_nonnative: Vec<NonNativeVar<G>> =
            bits_le_to_nonnative(cs.clone(), proof.elems.iter())?;
        let proof_mle = DenseMLEVar::from_evaluations_slice(dim2, &proof_nonnative);
        let expected_value = proof_mle.evaluate(partial_point)?;
        println!(
            "Cost of non_native arith per dim (dim2: {}): {:?}",
            dim2,
            (cs.num_constraints() - start_cost) / (1 << dim2)
        );
        let value_cond = value.is_eq(&expected_value)?;

        comm_cond.and(&value_cond)
    }

    pub fn batch_check<'a>(
        cs: ConstraintSystemRef<CF<G>>,
        vk: &VerifierKeyVar<G, C>,
        comms: Vec<&CommitmentVar<G, C>>,
        coeffs: &Vec<NonNativeVar<G>>,
        point: &Vec<NonNativeVar<G>>,
        values: &Vec<NonNativeVar<G>>,
        proof: &ProofVar<G>,
    ) -> Result<Boolean<CF<G>>, SynthesisError> {
        let dim1 = comms[0].dim1;
        let dim2 = comms[0].dim2;
        assert!(point.len() == dim1 + dim2, "incorrect number of points");
        assert!(
            dim1 + dim2 <= vk.max_dim(),
            "current setup doesn't work for a poly with this many vars"
        );
        assert!(comms.len() == coeffs.len(), "incorrect number of scalars");
        assert!(comms.len() == values.len(), "incorrect number of values");

        let start_cost = cs.num_constraints();
        let one: NonNativeVar<G> = NonNativeFieldVar::new_constant(cs.clone(), F::<G>::one())?;
        let mut scalars = vec![one.clone(); 1 << dim1];
        let partial_point = &point[..dim1];
        for i in 0..dim1 {
            let r = &partial_point[i];
            let one_minus_r = &one - r;
            for b in 0..(1 << i) {
                scalars[(1 << i) + b] = &scalars[b] * r;
                scalars[b] *= &one_minus_r;
            }
        }
        let coeffs_dim_1_nonnative: Vec<NonNativeVar<G>> =
            bits_le_to_nonnative(cs.clone(), proof.coeffs_dim_1.iter())?;
        for i in 0..1 << dim1 {
            scalars[i].enforce_equal(&coeffs_dim_1_nonnative[i])?;
        }
        println!(
            "Cost of non_native arith per dim (dim1: {}): {:?}",
            dim1,
            (cs.num_constraints() - start_cost) / (1 << dim1)
        );
        let start_cost = cs.num_constraints();
        let actual_comms = comms
            .iter()
            .map(|&commitment| C::multi_scalar_mul_le(&commitment.comm, &proof.coeffs_dim_1))
            .collect::<Result<Vec<_>, SynthesisError>>()?;
        println!(
            "Cost of scalar_mul per dim (dim1: {}): {:?}",
            dim1,
            (cs.num_constraints() - start_cost) / (1 << dim1)
        );
        let start_cost = cs.num_constraints();
        let coeffs_bits_le = coeffs
            .iter()
            .map(|c| c.to_bits_le())
            .collect::<Result<Vec<_>, SynthesisError>>()?;
        let actual_combined_comm = C::multi_scalar_mul_le(&actual_comms, &coeffs_bits_le)?;
        println!(
            "Cost of combining comms (dim1: {}): {:?}",
            dim1,
            (cs.num_constraints() - start_cost) / (1 << dim1)
        );
        let start_cost = cs.num_constraints();
        let expected_comm =
            C::multi_scalar_mul_le(&vk.comm_key[..1 << dim2].to_vec(), &proof.elems)?;
        println!(
            "Cost of scalar_mul per dim (dim2: {}): {:?}",
            dim2,
            (cs.num_constraints() - start_cost) / (1 << dim2)
        );
        let comm_cond = actual_combined_comm.is_eq(&expected_comm)?;

        let start_cost = cs.num_constraints();
        let partial_point = &point[dim1..];
        let proof_nonnative: Vec<NonNativeVar<G>> =
            bits_le_to_nonnative(cs.clone(), proof.elems.iter())?;
        let proof_mle = DenseMLEVar::from_evaluations_slice(dim2, &proof_nonnative);
        let expected_value = proof_mle.evaluate(partial_point)?;
        println!(
            "Cost of non_native arith per dim (dim2: {}): {:?}",
            dim2,
            (cs.num_constraints() - start_cost) / (1 << dim2)
        );

        let mut combined_value = coeffs[0].mul_without_reduce(&values[0])?;
        for i in 1..coeffs.len() {
            combined_value += &coeffs[i].mul_without_reduce(&values[i])?;
        }
        let value_cond = combined_value.reduce()?.is_eq(&expected_value)?;

        comm_cond.and(&value_cond)
    }
}

#[cfg(test)]
mod tests {
    use crate::hyrax_pc::constraints::CommitmentVar;
    use crate::hyrax_pc::constraints::MVPolyCommitmentVar;
    use crate::hyrax_pc::constraints::ProofVar;
    use crate::hyrax_pc::constraints::VerifierKeyVar;
    use crate::hyrax_pc::MVPolyCommitment;
    use ark_nonnative_field::NonNativeFieldVar;
    use ark_poly::DenseMultilinearExtension;
    use ark_poly::MultilinearExtension;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::boolean::Boolean;
    use ark_r1cs_std::prelude::EqGadget;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use ark_grumpkin::{fq::Fq, fr::Fr, Affine as GAffine};
    type C = ark_grumpkin::constraints::GVar;

    type F = Fr;
    type CF = Fq;

    #[test]
    fn print_costs() {
        let nv: usize = 12;
        let mut rng = ark_std::test_rng();
        type PC = MVPolyCommitment<GAffine>;
        type PCVar = MVPolyCommitmentVar<GAffine, C>;
        let ck = PC::setup(nv + 4);
        let poly1 = DenseMultilinearExtension::<F>::rand(nv, &mut rng);
        let poly2 = DenseMultilinearExtension::<F>::rand(nv, &mut rng);

        let comm1 = PC::commit(&ck, &poly1);
        let comm2 = PC::commit(&ck, &poly2);

        let point: Vec<F> = (0..nv).into_iter().map(|_| F::rand(&mut rng)).collect();

        let coeff1 = F::rand(&mut rng);
        let coeff2 = F::rand(&mut rng);

        let proof1 = PC::open(&ck, &poly1, &point[..]);
        let proof = PC::batch_open(&ck, vec![&poly1, &poly2], vec![coeff1, coeff2], &point[..]);

        let value1 = poly1.fix_variables(&point[..])[0];
        let value2 = poly2.fix_variables(&point[..])[0];

        let cs = ConstraintSystem::<CF>::new_ref();

        let start_cost = cs.num_constraints();
        let vk_var = VerifierKeyVar::<GAffine, C>::new_constant(cs.clone(), ck.clone()).unwrap();
        println!(
            "Cost of allocating vk {:?}",
            cs.num_constraints() - start_cost
        );

        let start_cost = cs.num_constraints();
        let comm1_var = CommitmentVar::<GAffine, C>::new_witness(cs.clone(), || Ok(comm1)).unwrap();
        println!(
            "Cost of allocating comm {:?}",
            cs.num_constraints() - start_cost
        );
        let comm2_var = CommitmentVar::<GAffine, C>::new_witness(cs.clone(), || Ok(comm2)).unwrap();

        let start_cost = cs.num_constraints();
        let point_var: Vec<NonNativeFieldVar<F, CF>> = point
            .iter()
            .map(|p| NonNativeFieldVar::new_witness(cs.clone(), || Ok(p)).unwrap())
            .collect::<Vec<_>>();
        println!(
            "Cost of allocating point {:?}",
            cs.num_constraints() - start_cost
        );

        let start_cost = cs.num_constraints();
        let val1_var = NonNativeFieldVar::<F, CF>::new_witness(cs.clone(), || Ok(value1)).unwrap();
        println!(
            "Cost of allocating val {:?}",
            cs.num_constraints() - start_cost
        );
        let val2_var = NonNativeFieldVar::<F, CF>::new_witness(cs.clone(), || Ok(value2)).unwrap();

        let coeff1_var =
            NonNativeFieldVar::<F, CF>::new_witness(cs.clone(), || Ok(coeff1)).unwrap();
        let coeff2_var =
            NonNativeFieldVar::<F, CF>::new_witness(cs.clone(), || Ok(coeff2)).unwrap();

        let start_cost = cs.num_constraints();
        let proof1_var = ProofVar::<GAffine>::new_witness(cs.clone(), || Ok(proof1)).unwrap();
        println!(
            "Cost of allocating proof {:?}",
            cs.num_constraints() - start_cost
        );
        let proof_var = ProofVar::<GAffine>::new_witness(cs.clone(), || Ok(proof)).unwrap();

        let start_cost = cs.num_constraints();
        PCVar::check(
            cs.clone(),
            &vk_var,
            &comm1_var,
            &point_var,
            &val1_var,
            &proof1_var,
        )
        .unwrap()
        .enforce_equal(&Boolean::TRUE)
        .unwrap();
        println!("Cost of verify: {:?}", cs.num_constraints() - start_cost);

        let start_cost = cs.num_constraints();
        PCVar::batch_check(
            cs.clone(),
            &vk_var,
            vec![&comm1_var, &comm2_var],
            &vec![coeff1_var, coeff2_var],
            &point_var,
            &vec![val1_var, val2_var],
            &proof_var,
        )
        .unwrap()
        .enforce_equal(&Boolean::TRUE)
        .unwrap();
        println!(
            "Cost of batch verify: {:?}",
            cs.num_constraints() - start_cost
        );

        println!("Num constaints: {:}", cs.num_constraints());
        println!("Num instance: {:}", cs.num_instance_variables());
        println!("Num witness: {:}", cs.num_witness_variables());

        assert!(cs.is_satisfied().unwrap());
    }
}
