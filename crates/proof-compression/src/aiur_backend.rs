//! Native BN254 scalar arithmetic for the Aiur interpreter.
//!
//! Execution uses the same scalar representation as the KZG backend. Artifact
//! constants cross a canonical four-limb boundary; host indices must additionally
//! fit in a machine word. Trace population and proving are separate adapters.

use crate::kzg::Scalar;
use aiur::{FieldWord, field::FieldBackend};
use ark_bn254::Fr;
use ark_ff::{Field, PrimeField};

pub mod fq;
pub mod g1;
pub mod kzg;

#[derive(Clone, Copy, Debug, Default)]
pub struct Bn254;

impl FieldBackend for Bn254 {
  type Element = Scalar;
  type Word = FieldWord;
  const ALL_ELEMENTS_VALID: bool = true;

  fn modulus(self) -> FieldWord {
    FieldWord::from_limbs_le(Fr::MODULUS.0)
  }

  fn from_u64(self, value: u64) -> Scalar {
    Scalar(Fr::from(value))
  }

  fn from_word(self, value: FieldWord) -> Scalar {
    let mut bytes = [0u8; 32];
    for (chunk, limb) in
      bytes.as_chunks_mut::<8>().0.iter_mut().zip(value.limbs_le())
    {
      *chunk = limb.to_le_bytes();
    }
    Scalar(Fr::from_le_bytes_mod_order(&bytes))
  }

  fn to_word(self, value: Scalar) -> FieldWord {
    FieldWord::from_limbs_le(value.canonical_limbs_le())
  }

  fn add(self, a: Scalar, b: Scalar) -> Scalar {
    a + b
  }

  fn sub(self, a: Scalar, b: Scalar) -> Scalar {
    a - b
  }

  fn neg(self, a: Scalar) -> Scalar {
    -a
  }

  fn mul(self, a: Scalar, b: Scalar) -> Scalar {
    a * b
  }

  fn inverse(self, a: Scalar) -> Option<Scalar> {
    a.0.inverse().map(Scalar)
  }
}
