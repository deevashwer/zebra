use ark_relations::r1cs::SynthesisError;
use ark_std::fmt;

use ark_std::string::String;
use core::fmt::Formatter;
/// Error type for this crate
#[derive(fmt::Debug)]
pub enum Error {
    /// protocol rejects this proof
    Reject(Option<String>),
    /// IO Error
    IOError,
    /// Serialization Error
    SerializationError,
    /// Random Generator Error
    RNGError,
    /// Other caused by other operations
    OtherError(String),
    /// There was a synthesis error.
    R1CSError(SynthesisError),
    /// NonSquare Matix Error
    NonSquareMatrix,
    InvalidPublicInputLength,
    InvalidNumConstraints,
    InstanceDoesNotMatchIndex,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Self::OtherError(s) = self {
            f.write_str(s)
        } else {
            f.write_fmt(format_args!("{:?}", self))
        }
    }
}

impl ark_std::error::Error for Error {}

impl From<ark_std::io::Error> for Error {
    fn from(_: ark_std::io::Error) -> Self {
        Self::IOError
    }
}

impl From<ark_serialize::SerializationError> for Error {
    fn from(_: ark_serialize::SerializationError) -> Self {
        Self::SerializationError
    }
}
impl From<ark_std::rand::Error> for Error {
    fn from(_: ark_std::rand::Error) -> Self {
        Self::RNGError
    }
}

impl From<SynthesisError> for Error {
    fn from(err: SynthesisError) -> Self {
        Error::R1CSError(err)
    }
}
