use crate::r1cs::{
  CanonicalR1csV1, ConstraintPhase, LinearCombination, R1csBuilder, R1csError,
  Variable, Witness,
};
use ark_bls12_381::Fr;
use ark_ff::{AdditiveGroup, BigInteger, Field, PrimeField};

pub const STAGE4_PUBLIC_INPUT_LIMBS: usize = 2;
const LIMB_BITS: usize = 128;

/// The 256-bit Stage 3 statement digest exposed as two injective `Fr` limbs.
///
/// Digest bytes `0..16` form limb zero and bytes `16..32` form limb one, both
/// interpreted as little-endian integers. Each limb is below `2^128`, so the
/// conversion into BLS12-381 `Fr` is injective and performs no reduction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stage4PublicInputsV1 {
  limbs: [u128; STAGE4_PUBLIC_INPUT_LIMBS],
}

/// The two public `Fr` variables carrying the Stage 3 statement digest.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stage4PublicInputVariablesV1 {
  variables: [Variable; STAGE4_PUBLIC_INPUT_LIMBS],
}

impl Stage4PublicInputVariablesV1 {
  pub const fn variables(self) -> [Variable; STAGE4_PUBLIC_INPUT_LIMBS] {
    self.variables
  }
}

impl Stage4PublicInputsV1 {
  pub fn from_statement_digest(digest: [u8; 32]) -> Self {
    Self {
      limbs: [
        u128::from_le_bytes(digest[..16].try_into().expect("16-byte limb")),
        u128::from_le_bytes(digest[16..].try_into().expect("16-byte limb")),
      ],
    }
  }

  pub const fn limbs(self) -> [u128; STAGE4_PUBLIC_INPUT_LIMBS] {
    self.limbs
  }

  pub fn statement_digest(self) -> [u8; 32] {
    let mut digest = [0u8; 32];
    digest[..16].copy_from_slice(&self.limbs[0].to_le_bytes());
    digest[16..].copy_from_slice(&self.limbs[1].to_le_bytes());
    digest
  }

  pub fn field_elements(self) -> [Fr; STAGE4_PUBLIC_INPUT_LIMBS] {
    self.limbs.map(fr_from_u128)
  }

  /// Fixed-width canonical little-endian scalar encodings.
  pub fn scalar_bytes_le(self) -> [[u8; 32]; STAGE4_PUBLIC_INPUT_LIMBS] {
    self.field_elements().map(|element| {
      let mut encoded = [0u8; 32];
      let bytes = element.into_bigint().to_bytes_le();
      encoded[..bytes.len()].copy_from_slice(&bytes);
      encoded
    })
  }
}

/// Build the first canonical Stage 4 circuit slice: constrain 256 digest bits
/// to the two public field limbs. The bits become the connection point for the
/// in-circuit BLAKE3 output added by the Flock-verifier transcript phase.
pub fn build_stage4_public_input_binding(
  public_inputs: Stage4PublicInputsV1,
) -> Result<(CanonicalR1csV1, Witness), R1csError> {
  let mut builder = R1csBuilder::new();
  let public_variables =
    alloc_stage4_public_inputs(&mut builder, public_inputs)?.variables;

  for (limb_index, &limb) in public_inputs.limbs.iter().enumerate() {
    let mut packed = LinearCombination::zero();
    let mut coefficient = Fr::ONE;
    for bit_index in 0..LIMB_BITS {
      let bit = (limb >> bit_index) & 1;
      let variable = builder.alloc_private(Fr::from(bit as u64))?;
      builder.enforce_boolean(ConstraintPhase::Statement, variable);
      packed = packed.term(variable, coefficient);
      coefficient.double_in_place();
    }
    packed = packed
      .minus(&LinearCombination::from_variable(public_variables[limb_index]));
    builder.enforce_zero(ConstraintPhase::Statement, packed);
  }
  builder.finish()
}

/// Allocate the terminal statement digest before any private variables.
pub fn alloc_stage4_public_inputs(
  builder: &mut R1csBuilder,
  public_inputs: Stage4PublicInputsV1,
) -> Result<Stage4PublicInputVariablesV1, R1csError> {
  let variables = public_inputs
    .field_elements()
    .map(|value| builder.alloc_public(value))
    .into_iter()
    .collect::<Result<Vec<Variable>, R1csError>>()?
    .try_into()
    .map_err(|_| R1csError::InternalShape)?;
  Ok(Stage4PublicInputVariablesV1 { variables })
}

pub(crate) fn constrain_stage4_public_input_expressions(
  builder: &mut R1csBuilder,
  public_inputs: Stage4PublicInputVariablesV1,
  bits: &[LinearCombination; 256],
) {
  for (limb, public) in public_inputs.variables.into_iter().enumerate() {
    let mut coefficient = Fr::ONE;
    let packed = LinearCombination::from_terms(
      bits[limb * LIMB_BITS..(limb + 1) * LIMB_BITS].iter().flat_map(
        |expression| {
          let scaled = expression.clone().scale(coefficient);
          coefficient.double_in_place();
          scaled.terms().to_vec()
        },
      ),
    );
    builder.enforce_zero(
      ConstraintPhase::Statement,
      packed.minus(&LinearCombination::from_variable(public)),
    );
  }
}

fn fr_from_u128(value: u128) -> Fr {
  Fr::from_le_bytes_mod_order(&value.to_le_bytes())
}

#[cfg(test)]
mod tests {
  use super::*;

  fn fixture_digest() -> [u8; 32] {
    core::array::from_fn(|index| u8::try_from(index).unwrap())
  }

  #[test]
  fn digest_limb_encoding_is_injective_and_round_trips() {
    let digest = fixture_digest();
    let public = Stage4PublicInputsV1::from_statement_digest(digest);
    assert_eq!(
      public.limbs(),
      [0x0f0e0d0c0b0a09080706050403020100, 0x1f1e1d1c1b1a19181716151413121110,]
    );
    assert_eq!(public.statement_digest(), digest);
    for encoded in public.scalar_bytes_le() {
      assert!(encoded[16..].iter().all(|byte| *byte == 0));
    }
  }

  #[test]
  fn public_input_binding_has_stable_shape_and_rejects_mutation() {
    let public = Stage4PublicInputsV1::from_statement_digest(fixture_digest());
    let (r1cs, mut witness) =
      build_stage4_public_input_binding(public).unwrap();
    let census = r1cs.census();
    assert_eq!(r1cs.variables(), 259);
    assert_eq!(census.public_variables, 2);
    assert_eq!(census.private_variables, 256);
    assert_eq!(census.constraints, 258);
    assert_eq!(
      census.constraints_by_phase.get(&ConstraintPhase::Statement),
      Some(&258)
    );
    r1cs.check(&witness).unwrap();

    witness.set(Variable::from_index(1), Fr::from(9u64)).unwrap();
    assert!(matches!(r1cs.check(&witness), Err(R1csError::Unsatisfied { .. })));
  }

  #[test]
  fn circuit_digest_is_value_independent() {
    let first = Stage4PublicInputsV1::from_statement_digest([0x11; 32]);
    let second = Stage4PublicInputsV1::from_statement_digest([0xee; 32]);
    let (first, _) = build_stage4_public_input_binding(first).unwrap();
    let (second, _) = build_stage4_public_input_binding(second).unwrap();
    assert_eq!(first.digest(), second.digest());
  }
}
