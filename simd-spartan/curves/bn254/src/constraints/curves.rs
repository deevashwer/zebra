use crate::Parameters;
use ark_r1cs_std::groups::bn;

/// An element of G1 in the BN-254 bilinear group.
pub type G1Var = bn::G1Var<Parameters>;
/// An element of G2 in the BN-254 bilinear group.
pub type G2Var = bn::G2Var<Parameters>;

/// Represents the cached precomputation that can be performed on a G1 element
/// which enables speeding up pairing computation.
pub type G1PreparedVar = bn::G1PreparedVar<Parameters>;
/// Represents the cached precomputation that can be performed on a G2 element
/// which enables speeding up pairing computation.
pub type G2PreparedVar = bn::G2PreparedVar<Parameters>;

#[test]
fn test() {
    use ark_ec::models::bn::BnParameters;
    ark_curve_constraint_tests::curves::sw_test::<
        <Parameters as BnParameters>::G1Parameters,
        G1Var,
    >()
    .unwrap();
    ark_curve_constraint_tests::curves::sw_test::<
        <Parameters as BnParameters>::G2Parameters,
        G2Var,
    >()
    .unwrap();
}
