use crate::dense_mle::{compute_lagrange_coeffs, fix_variables_opt};
use ark_ec::{msm, AffineCurve, ProjectiveCurve};
use ark_ff::{to_bytes, One, PrimeField, ToBytes, Zero};
use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{collect_sponge_bytes, collect_sponge_field_elements, Absorb};
use ark_std::cfg_iter;
use ark_std::{
    end_timer,
    io::{Read, Write},
    marker::PhantomData,
    start_timer,
};
use blake2::{Blake2s, Digest};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
// use rayon::par_iter::{IntoParallelIterator, ParallelIterator};

pub mod constraints;

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct UniversalParams<G: AffineCurve> {
    /// The key used to commit to polynomials.
    pub comm_key: Vec<G>,
}

/// don't need hiding
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommitterKey<G: AffineCurve> {
    /// The key used to commit to polynomials.
    pub comm_key: Vec<G>,
}

impl<G: AffineCurve> CommitterKey<G> {
    pub fn max_dim(&self) -> usize {
        2 * self.comm_key.len().trailing_zeros() as usize
    }
}

pub type VerifierKey<G> = CommitterKey<G>;

/// Commitment to a polynomial that optionally enforces a degree bound.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Commitment<G: AffineCurve + Absorb> {
    /// A Pedersen commitment to the polynomial.
    pub comm: Vec<G>,
    pub dim1: usize,
    pub dim2: usize,
}

impl<G: AffineCurve + Absorb> Commitment<G> {
    #[inline]
    pub fn empty() -> Self {
        Commitment {
            comm: vec![G::zero()],
            dim1: 0,
            dim2: 0,
        }
    }

    pub fn size_in_bytes(&self) -> usize {
        ark_ff::to_bytes![G::zero()].unwrap().len()
    }
}

impl<G: AffineCurve + Absorb> ToBytes for Commitment<G> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> ark_std::io::Result<()> {
        Ok(self.comm.write(&mut writer)?)
    }
}

impl<G: AffineCurve + Absorb> Absorb for Commitment<G> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(self.comm, self.dim1, self.dim2);
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> = collect_sponge_field_elements!(
            self.comm,
            self.dim1.to_le_bytes().to_vec(),
            self.dim2.to_le_bytes().to_vec()
        );
        dest.extend(tmp);
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<G: AffineCurve> {
    pub elems: Vec<G::ScalarField>,
    pub point: Vec<G::ScalarField>,
}

impl<G: AffineCurve> Proof<G> {
    pub fn size_in_bytes(&self) -> usize {
        ark_ff::to_bytes![self].unwrap().len()
    }
}

impl<G: AffineCurve> ToBytes for Proof<G> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> ark_std::io::Result<()> {
        Ok(self.elems.write(&mut writer)?)
    }
}

pub struct MVPolyCommitment<G: AffineCurve> {
    _projective: PhantomData<G>,
}

impl<G> MVPolyCommitment<G>
where
    G: AffineCurve + Absorb,
{
    /// `PROTOCOL_NAME` is used as a seed for the setup function.
    const PROTOCOL_NAME: &'static [u8] = b"HyraxVC-DL";

    pub fn sample_generators(num_generators: usize) -> Vec<G> {
        let generators: Vec<_> = ark_std::cfg_into_iter!(0..num_generators)
            .map(|i| {
                let i = i as u64;
                let mut hash = Blake2s::digest(&to_bytes![&Self::PROTOCOL_NAME, i].unwrap());
                let mut g = G::from_random_bytes(&hash);
                let mut j = 0u64;
                while g.is_none() {
                    hash = Blake2s::digest(&to_bytes![&Self::PROTOCOL_NAME, i, j].unwrap());
                    g = G::from_random_bytes(&hash);
                    j += 1;
                }
                let generator = g.unwrap();
                generator.mul_by_cofactor_to_projective()
            })
            .collect();

        G::Projective::batch_normalization_into_affine(&generators)
    }

    pub fn setup(nv: usize) -> CommitterKey<G> {
        let dim2 = ((nv as f32) / 2.0).ceil() as usize;
        let setup_time = start_timer!(|| format!("Sampling {} generators", 1 << dim2));
        let generators = Self::sample_generators(1 << dim2);
        end_timer!(setup_time);

        let ck = CommitterKey {
            comm_key: generators,
        };

        ck
    }

    pub fn commit<'a>(
        ck: &CommitterKey<G>,
        poly: &DenseMultilinearExtension<G::ScalarField>,
    ) -> Commitment<G> {
        let commit_time = start_timer!(|| "Committing to a vector");
        let nv = poly.num_vars();
        let dim2 = ((nv as f32) / 2.0).ceil() as usize;
        let dim1 = nv - dim2;
        assert!(
            nv <= ck.max_dim(),
            "current setup doesn't work for a poly with this many vars"
        );

        let scalars_time = start_timer!(|| "Transposing Scalars");
        let evals = poly.to_evaluations();
        let index = (0..1 << dim1).collect::<Vec<_>>();
        let scalars = cfg_iter!(index)
            .map(|i| {
                let mut scalars_i = Vec::with_capacity(1 << dim2);
                for j in 0..1 << dim2 {
                    scalars_i.push(evals[j * (1 << dim1) + i].into_repr());
                }
                scalars_i
            })
            .collect::<Vec<_>>();
        end_timer!(scalars_time);

        let msm_time = start_timer!(|| "MSM Time");
        let comm = cfg_iter!(scalars)
            .map(|s| {
                msm::VariableBaseMSM::multi_scalar_mul(&ck.comm_key[..1 << dim2], &s).into_affine()
            })
            .collect::<Vec<_>>();
        end_timer!(msm_time);

        let ret = Commitment { comm, dim1, dim2 };
        end_timer!(commit_time);
        ret
    }

    pub fn open<'a>(
        ck: &CommitterKey<G>,
        poly: &DenseMultilinearExtension<G::ScalarField>,
        point: &[G::ScalarField],
    ) -> Proof<G> {
        let nv = poly.num_vars();
        let dim2 = ((nv as f32) / 2.0).ceil() as usize;
        let dim1 = nv - dim2;
        assert!(point.len() == dim1 + dim2, "incorrect number of points");
        assert!(
            poly.num_vars() <= ck.max_dim(),
            "current setup doesn't work for a poly with this many vars"
        );

        let opening_time = start_timer!(|| "Opening a vector");

        let fixed_poly = fix_variables_opt(&poly, &point[..dim1].to_vec());

        end_timer!(opening_time);

        Proof {
            elems: fixed_poly.to_evaluations(),
            point: point.to_vec(),
        }
    }

    pub fn batch_open<'a>(
        ck: &CommitterKey<G>,
        polys: Vec<&DenseMultilinearExtension<G::ScalarField>>,
        coeffs: Vec<G::ScalarField>,
        point: &[G::ScalarField],
    ) -> Proof<G> {
        let nv = polys[0].num_vars();
        let dim2 = ((nv as f32) / 2.0).ceil() as usize;
        let dim1 = nv - dim2;
        assert!(point.len() == dim1 + dim2, "incorrect number of points");
        assert!(
            polys[0].num_vars() <= ck.max_dim(),
            "current setup doesn't work for a poly with this many vars"
        );
        assert!(polys.len() == coeffs.len(), "incorrect number of scalars");

        let opening_time = start_timer!(|| "Opening a vector");

        let combined_poly_vec = (0..1 << nv)
            .into_par_iter()
            .map(|i| {
                let mut sum_i = G::ScalarField::zero();
                for j in 0..polys.len() {
                    sum_i += polys[j].evaluations[i] * coeffs[j];
                }
                sum_i
            })
            .collect::<Vec<_>>();
        let combined_poly = DenseMultilinearExtension {
            num_vars: nv,
            evaluations: combined_poly_vec,
        };
        let fixed_poly = fix_variables_opt(&combined_poly, &point[..dim1].to_vec());

        end_timer!(opening_time);

        Proof {
            elems: fixed_poly.to_evaluations(),
            point: point.to_vec(),
        }
    }

    pub fn check<'a>(
        vk: &VerifierKey<G>,
        commitment: &Commitment<G>,
        point: &[G::ScalarField],
        value: G::ScalarField,
        proof: &Proof<G>,
    ) -> bool {
        let dim1 = commitment.dim1;
        let dim2 = commitment.dim2;
        assert!(point.len() == dim1 + dim2, "incorrect number of points");
        assert!(
            dim1 + dim2 <= vk.max_dim(),
            "current setup doesn't work for a poly with this many vars"
        );

        let scalars = compute_lagrange_coeffs::<G::ScalarField>(point[..dim1].to_vec());
        // let mut scalars = vec![one; 1 << dim1];
        // let partial_point = &point[..dim1];
        // for i in 0..dim1 {
        //     let r = partial_point[i];
        //     for b in 0..(1 << i) {
        //         scalars[(1 << i) + b] = scalars[b] * r;
        //         scalars[b] *= one - r;
        //     }
        // }
        let scalars_bigint = scalars.iter().map(|s| s.into_repr()).collect::<Vec<_>>();
        let actual_comm = msm::VariableBaseMSM::multi_scalar_mul(&commitment.comm, &scalars_bigint);

        let proof_bigint = proof
            .elems
            .iter()
            .map(|s| s.into_repr())
            .collect::<Vec<_>>();
        let expected_comm =
            msm::VariableBaseMSM::multi_scalar_mul(&vk.comm_key[..1 << dim2], &proof_bigint);
        let comm_cond = actual_comm == expected_comm;

        let partial_point = &point[dim1..];
        let proof_mle = DenseMultilinearExtension::from_evaluations_slice(dim2, &proof.elems[..]);
        let expected_value = proof_mle.evaluate(partial_point).unwrap();
        let value_cond = value == expected_value;

        // println!("comm_cond: {}, value_cond: {}", comm_cond, value_cond);

        comm_cond & value_cond
    }

    pub fn batch_check<'a>(
        vk: &VerifierKey<G>,
        comms: Vec<&Commitment<G>>,
        coeffs: Vec<G::ScalarField>,
        point: &[G::ScalarField],
        values: Vec<G::ScalarField>,
        proof: &Proof<G>,
    ) -> bool {
        let dim1 = comms[0].dim1;
        let dim2 = comms[0].dim2;
        assert!(point.len() == dim1 + dim2, "incorrect number of points");
        assert!(
            dim1 + dim2 <= vk.max_dim(),
            "current setup doesn't work for a poly with this many vars"
        );
        assert!(comms.len() == coeffs.len(), "incorrect number of scalars");
        assert!(comms.len() == values.len(), "incorrect number of values");

        let one = G::ScalarField::one();
        let mut scalars = vec![one; 1 << dim1];
        let partial_point = &point[..dim1];
        for i in 0..dim1 {
            let r = partial_point[i];
            for b in 0..(1 << i) {
                scalars[(1 << i) + b] = scalars[b] * r;
                scalars[b] *= one - r;
            }
        }
        let scalars_bigint = scalars.iter().map(|s| s.into_repr()).collect::<Vec<_>>();
        let actual_comms = comms
            .iter()
            .map(|&commitment| {
                msm::VariableBaseMSM::multi_scalar_mul(&commitment.comm, &scalars_bigint)
                    .into_affine()
            })
            .collect::<Vec<G>>();

        let coeffs_bigint = coeffs.iter().map(|s| s.into_repr()).collect::<Vec<_>>();
        let actual_combined_comm =
            msm::VariableBaseMSM::multi_scalar_mul(&actual_comms, &coeffs_bigint);

        let proof_bigint = proof
            .elems
            .iter()
            .map(|s| s.into_repr())
            .collect::<Vec<_>>();
        let expected_comm =
            msm::VariableBaseMSM::multi_scalar_mul(&vk.comm_key[..1 << dim2], &proof_bigint);
        let comm_cond = actual_combined_comm == expected_comm;

        let partial_point = &point[dim1..];
        let proof_mle = DenseMultilinearExtension::from_evaluations_slice(dim2, &proof.elems[..]);
        let expected_value = proof_mle.evaluate(partial_point).unwrap();

        let combined_value: G::ScalarField =
            values.iter().zip(coeffs.iter()).map(|(&v, &c)| v * c).sum();
        let value_cond = combined_value == expected_value;

        // println!("comm_cond: {}, value_cond: {}", comm_cond, value_cond);

        comm_cond & value_cond
    }
}

#[cfg(test)]
mod tests {
    use super::MVPolyCommitment;
    use ark_ec::AffineCurve;
    use ark_grumpkin::Affine as GAffine;
    use ark_poly::DenseMultilinearExtension;
    use ark_poly::MultilinearExtension;
    use ark_std::UniformRand;
    type F = <GAffine as AffineCurve>::ScalarField;

    #[test]
    fn test_comm() {
        let nv: usize = 20;
        let mut rng = ark_std::test_rng();
        type PC = MVPolyCommitment<GAffine>;
        let ck = PC::setup(nv + 4);
        let poly1 = DenseMultilinearExtension::<F>::rand(nv, &mut rng);
        let poly2 = DenseMultilinearExtension::<F>::rand(nv, &mut rng);

        let coeff1 = F::rand(&mut rng);
        let coeff2 = F::rand(&mut rng);

        let comm1 = PC::commit(&ck, &poly1);
        let comm2 = PC::commit(&ck, &poly2);

        let point: Vec<F> = (0..nv).into_iter().map(|_| F::rand(&mut rng)).collect();

        let proof1 = PC::open(&ck, &poly1, &point[..]);
        let proof2 = PC::open(&ck, &poly2, &point[..]);
        let proof = PC::batch_open(&ck, vec![&poly1, &poly2], vec![coeff1, coeff2], &point[..]);

        let value1 = poly1.evaluate(&point[..]).unwrap();
        let value2 = poly2.evaluate(&point[..]).unwrap();

        let output1 = PC::check(&ck, &comm1, &point[..], value1, &proof1);
        let output2 = PC::check(&ck, &comm2, &point[..], value2, &proof2);
        let output = PC::batch_check(
            &ck,
            vec![&comm1, &comm2],
            vec![coeff1, coeff2],
            &point[..],
            vec![value1, value2],
            &proof,
        );

        assert!(output1, "check1 unsuccessful");
        assert!(output2, "check2 unsuccessful");
        assert!(output, "batch_check unsuccessful");
    }
}
