pub mod dense_mle;
mod error;
pub mod gkr_grand_product;
pub mod hyrax_pc;
pub mod ip_r1cs;
pub mod zebra;
pub mod spartan;
pub mod sumcheck;
use ark_ec::AffineCurve;
use ark_ff::Field;
use ark_nonnative_field::NonNativeFieldVar;
use ark_sponge::FieldElementSize;
pub use error::Error;

pub(crate) type CF<G> = <<G as AffineCurve>::BaseField as Field>::BasePrimeField;
pub(crate) type F<G> = <G as AffineCurve>::ScalarField;
pub(crate) type NonNativeVar<G> = NonNativeFieldVar<F<G>, CF<G>>;
pub(crate) const CHALLENGE_SIZE: FieldElementSize = FieldElementSize::Truncated(128);
pub(crate) const MIN_RAYON_ITERS: usize = 16;
