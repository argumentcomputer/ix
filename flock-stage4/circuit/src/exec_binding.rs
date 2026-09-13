//! Generic public/private Exec statement binding, without legacy root slots.

use crate::{
  ConstraintPhase, F128TranscriptWordV1, F128VariablesV1, LinearCombination,
  R1csBuilder, R1csError, Stage4PublicInputVariablesV1,
  blake3::{Word32, alloc_word_in_phase},
  f128::{alloc_f128_constant, alloc_f128_private},
  public_inputs::constrain_stage4_public_input_expressions,
  statement::{
    F128StatementCircuitError, bind_computed_digest, bind_constant_digest,
    constrain_chunk, constrain_public_values_digest, digest_bytes,
    native_public_values_digest,
  },
};
use ark_bls12_381::Fr;
use ix_stage4_trace::{ExecBindingV0, ExecCommitmentsV0, ExecPublicWordV0};
use std::fmt;

#[derive(Clone, Copy)]
pub struct ExecBindingCircuitInputsV0<'a> {
  pub commitments: ExecCommitmentsV0,
  /// Variables already allocated and used by the constrained main transcript.
  pub byte_payloads: &'a [Vec<F128TranscriptWordV1>],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecBindingCircuitOutputV0 {
  pub topology_digest: [u8; 32],
  /// Reconstructed from the fixed template and computed S, not a prover dump.
  pub public_values: Vec<F128VariablesV1>,
  pub statement_digest: [u8; 32],
  pub public_digest: [u8; 32],
}

#[derive(Debug)]
pub enum ExecBindingCircuitError {
  Template(String),
  Hash(F128StatementCircuitError),
  R1cs(R1csError),
  Internal(&'static str),
}

impl fmt::Display for ExecBindingCircuitError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Template(error) => write!(f, "Exec binding template: {error}"),
      Self::Hash(error) => write!(f, "Exec binding hash: {error}"),
      Self::R1cs(error) => write!(f, "Exec binding R1CS: {error}"),
      Self::Internal(error) => write!(f, "Exec binding: {error}"),
    }
  }
}
impl std::error::Error for ExecBindingCircuitError {}
impl From<R1csError> for ExecBindingCircuitError {
  fn from(error: R1csError) -> Self {
    Self::R1cs(error)
  }
}
impl From<F128StatementCircuitError> for ExecBindingCircuitError {
  fn from(error: F128StatementCircuitError) -> Self {
    Self::Hash(error)
  }
}

/// Constrain S = H4(P,B,I,O), Q = H5(P,B,O), the complete approved public
/// vector, its native Flock digest, and the exact pre-challenge statement
/// payloads. P, registry, counts, circuit, and every fixed word are constants.
/// B and O stay variable so approving another guest does not change the key;
/// I is private but participates in the very same S verified by Flock.
pub fn constrain_exec_binding(
  builder: &mut R1csBuilder,
  public: Stage4PublicInputVariablesV1,
  template: &ExecBindingV0,
  inputs: ExecBindingCircuitInputsV0<'_>,
) -> Result<ExecBindingCircuitOutputV0, ExecBindingCircuitError> {
  template
    .validate(template.public_template.len(), inputs.byte_payloads.len())
    .map_err(|error| ExecBindingCircuitError::Template(error.to_string()))?;
  bind_constant_digest(
    builder,
    &inputs.byte_payloads[0],
    template.registry_digest,
    "Exec registry",
  )?;
  let counts =
    template.counts.iter().flat_map(|n| n.to_le_bytes()).collect::<Vec<_>>();
  bind_constant_bytes(builder, &inputs.byte_payloads[1], &counts)?;
  bind_constant_digest(
    builder,
    &inputs.byte_payloads[3],
    template.circuit_digest,
    "Exec circuit",
  )?;

  let p = template
    .profile_digest
    .as_chunks::<4>()
    .0
    .iter()
    .map(|word| Word32::constant(u32::from_le_bytes(*word)))
    .collect::<Vec<_>>();
  let b = alloc_digest(builder, inputs.commitments.program)?;
  let i = alloc_digest(builder, inputs.commitments.input)?;
  let o = alloc_digest(builder, inputs.commitments.output)?;
  let s = hash_components(builder, 4, &[&p, &b, &i, &o])?;
  let q = hash_components(builder, 5, &[&p, &b, &o])?;
  let statement_digest = digest_bytes(&s);
  let public_digest = digest_bytes(&q);
  if statement_digest
    != inputs.commitments.statement_digest(template.profile_digest)
    || public_digest
      != inputs.commitments.public_digest(template.profile_digest)
  {
    return Err(ExecBindingCircuitError::Internal(
      "commitment hash differential",
    ));
  }
  let public_bits = q
    .iter()
    .flat_map(Word32::expressions)
    .collect::<Vec<_>>()
    .try_into()
    .map_err(|_| ExecBindingCircuitError::Internal("Q digest bit width"))?;
  constrain_stage4_public_input_expressions(builder, public, &public_bits);

  let mut public_values = Vec::with_capacity(template.public_template.len());
  for word in &template.public_template {
    let value = match word {
      ExecPublicWordV0::Fixed(value) => {
        alloc_f128_constant(builder, *value, ConstraintPhase::Wiring)?
      },
      ExecPublicWordV0::StatementLow | ExecPublicWordV0::StatementHigh => {
        let half = usize::from(matches!(word, ExecPublicWordV0::StatementHigh));
        let value = alloc_f128_private(
          builder,
          statement_digest[16 * half..16 * (half + 1)]
            .try_into()
            .expect("S limb"),
          ConstraintPhase::Statement,
        )?;
        for (bit, expression) in s[4 * half..4 * (half + 1)]
          .iter()
          .flat_map(Word32::expressions)
          .enumerate()
        {
          builder.enforce_zero(
            ConstraintPhase::Statement,
            expression.minus(&LinearCombination::from_variable(
              value.bit_variables()[bit],
            )),
          );
        }
        value
      },
    };
    public_values.push(value);
  }
  let digest = constrain_public_values_digest(builder, &public_values)?;
  let native = native_public_values_digest(
    &public_values.iter().map(|value| *value.value()).collect::<Vec<_>>(),
  );
  if digest_bytes(&digest) != native {
    return Err(ExecBindingCircuitError::Internal(
      "Flock public digest differential",
    ));
  }
  bind_computed_digest(
    builder,
    &digest,
    &inputs.byte_payloads[4],
    native,
    "Exec public vector",
    ConstraintPhase::Wiring,
  )?;
  Ok(ExecBindingCircuitOutputV0 {
    topology_digest: template.topology_digest(),
    public_values,
    statement_digest,
    public_digest,
  })
}

fn alloc_digest(
  builder: &mut R1csBuilder,
  digest: [u8; 32],
) -> Result<Vec<Word32>, R1csError> {
  digest
    .as_chunks::<4>()
    .0
    .iter()
    .map(|word| {
      alloc_word_in_phase(
        builder,
        u32::from_le_bytes(*word),
        ConstraintPhase::Statement,
      )
    })
    .collect()
}

fn hash_components(
  builder: &mut R1csBuilder,
  tag: u8,
  components: &[&[Word32]],
) -> Result<[Word32; 8], F128StatementCircuitError> {
  let mut prefix = *b"IxBy/commit/v0\0\0";
  prefix[15] = tag;
  let mut words = prefix
    .as_chunks::<4>()
    .0
    .iter()
    .map(|word| Word32::constant(u32::from_le_bytes(*word)))
    .collect::<Vec<_>>();
  for component in components {
    words.extend_from_slice(component);
  }
  let bytes = words.len() * 4;
  constrain_chunk(builder, &words, bytes, true, ConstraintPhase::Statement)
}

fn bind_constant_bytes(
  builder: &mut R1csBuilder,
  payload: &[F128TranscriptWordV1],
  expected: &[u8],
) -> Result<(), ExecBindingCircuitError> {
  if payload.len() != expected.len().div_ceil(16) {
    return Err(ExecBindingCircuitError::Internal("counts payload width"));
  }
  for (word_index, word) in payload.iter().enumerate() {
    let mut bytes = [0; 16];
    let start = 16 * word_index;
    let count = 16.min(expected.len() - start);
    bytes[..count].copy_from_slice(&expected[start..start + count]);
    if word.value() != &bytes {
      return Err(ExecBindingCircuitError::Internal("counts payload value"));
    }
    for (bit, expression) in word.bit_expressions().iter().enumerate() {
      let expected = u64::from((bytes[bit / 8] >> (bit % 8)) & 1);
      builder.enforce_zero(
        ConstraintPhase::Wiring,
        expression
          .clone()
          .minus(&LinearCombination::from_constant(Fr::from(expected))),
      );
    }
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    CanonicalR1csV1, Stage4PublicInputsV1, Variable, Witness,
    alloc_stage4_public_inputs,
  };

  fn template() -> ExecBindingV0 {
    let mut public_template = vec![ExecPublicWordV0::Fixed([0; 16]); 67];
    public_template[14] = ExecPublicWordV0::StatementLow;
    public_template[66] = ExecPublicWordV0::StatementHigh;
    public_template[31] = ExecPublicWordV0::Fixed([0xff; 16]);
    ExecBindingV0 {
      profile_digest: [1; 32],
      registry_digest: [2; 32],
      circuit_digest: [3; 32],
      counts: vec![1, 2, 3],
      public_template,
    }
  }

  fn commitments(seed: u8) -> ExecCommitmentsV0 {
    ExecCommitmentsV0 {
      program: [seed; 32],
      input: [seed + 1; 32],
      output: [seed + 2; 32],
    }
  }

  fn payload_bytes(
    template: &ExecBindingV0,
    commitments: ExecCommitmentsV0,
  ) -> Vec<Vec<u8>> {
    let s = commitments.statement_digest(template.profile_digest);
    let public = template
      .public_template
      .iter()
      .map(|word| match word {
        ExecPublicWordV0::Fixed(value) => *value,
        ExecPublicWordV0::StatementLow => s[..16].try_into().unwrap(),
        ExecPublicWordV0::StatementHigh => s[16..].try_into().unwrap(),
      })
      .collect::<Vec<_>>();
    vec![
      template.registry_digest.to_vec(),
      template.counts.iter().flat_map(|n| n.to_le_bytes()).collect(),
      vec![0; 32],
      template.circuit_digest.to_vec(),
      native_public_values_digest(&public).to_vec(),
    ]
  }

  fn emit(
    builder: &mut R1csBuilder,
    template: &ExecBindingV0,
    commitments: ExecCommitmentsV0,
    bytes: &[Vec<u8>],
    q: [u8; 32],
  ) -> Result<
    (ExecBindingCircuitOutputV0, Vec<Variable>),
    ExecBindingCircuitError,
  > {
    let public = alloc_stage4_public_inputs(
      builder,
      Stage4PublicInputsV1::from_statement_digest(q),
    )?;
    let mut mutation_targets = public.variables().to_vec();
    let payloads = bytes
      .iter()
      .enumerate()
      .map(|(index, bytes)| {
        bytes
          .chunks(16)
          .enumerate()
          .map(|(word, chunk)| {
            let mut padded = [0; 16];
            padded[..chunk.len()].copy_from_slice(chunk);
            let value =
              alloc_f128_private(builder, padded, ConstraintPhase::Transcript)?;
            if index != 2 {
              // CAP is checked by PCS, not by this binding-only test.
              mutation_targets.push(value.bit_variables()[0]);
              if index == 1 && word == 1 {
                mutation_targets.push(value.bit_variables()[127]);
              }
            }
            Ok(F128TranscriptWordV1::from_f128_variables(&value))
          })
          .collect::<Result<Vec<_>, R1csError>>()
      })
      .collect::<Result<Vec<_>, _>>()?;
    let output = constrain_exec_binding(
      builder,
      public,
      template,
      ExecBindingCircuitInputsV0 { commitments, byte_payloads: &payloads },
    )?;
    for word in &output.public_values {
      mutation_targets.push(word.bit_variables()[0]);
    }
    Ok((output, mutation_targets))
  }

  fn compile(
    seed: u8,
  ) -> (CanonicalR1csV1, Witness, ExecBindingCircuitOutputV0, Vec<Variable>) {
    let template = template();
    let commitments = commitments(seed);
    let bytes = payload_bytes(&template, commitments);
    let mut builder = R1csBuilder::new();
    let (output, targets) = emit(
      &mut builder,
      &template,
      commitments,
      &bytes,
      commitments.public_digest(template.profile_digest),
    )
    .unwrap();
    let (r1cs, witness) = builder.finish().unwrap();
    (r1cs, witness, output, targets)
  }

  #[test]
  fn binding_enforces_private_i_public_q_every_fixed_word_and_prefix() {
    let (r1cs, witness, output, targets) = compile(9);
    assert_eq!(r1cs.public_variables(), 2);
    assert_eq!(
      output.statement_digest,
      commitments(9).statement_digest([1; 32])
    );
    assert_eq!(output.public_digest, commitments(9).public_digest([1; 32]));
    for variable in targets {
      let mut changed = witness.clone();
      changed
        .set(
          variable,
          changed.assignment()[variable.index() as usize] + Fr::from(1u64),
        )
        .unwrap();
      assert!(matches!(
        r1cs.check(&changed),
        Err(R1csError::Unsatisfied { .. })
      ));
    }
  }

  #[test]
  fn guest_input_and_output_values_do_not_choose_binding_topology() {
    let (first, _, _, _) = compile(9);
    let (second, _, _, _) = compile(19);
    assert_eq!(first.digest(), second.digest());
    let template = template();
    let commitments = commitments(19);
    let mut builder = R1csBuilder::new_projection();
    emit(
      &mut builder,
      &template,
      commitments,
      &payload_bytes(&template, commitments),
      commitments.public_digest(template.profile_digest),
    )
    .unwrap();
    let projected = builder.finish_projection().unwrap();
    assert_eq!(projected.census(), &second.census());
    assert_ne!(projected.digest(), [0; 32]);
  }

  #[test]
  fn wrong_components_or_approved_prefix_cannot_retarget_the_binding() {
    let template = template();
    let valid = commitments(9);
    let bytes = payload_bytes(&template, valid);
    let q = valid.public_digest(template.profile_digest);
    for index in 0..7 {
      let mut binding = template.clone();
      let mut components = valid;
      match index {
        0 => components.program[0] ^= 1,
        1 => components.input[0] ^= 1,
        2 => components.output[0] ^= 1,
        3 => binding.profile_digest[0] ^= 1,
        4 => binding.registry_digest[0] ^= 1,
        5 => binding.circuit_digest[0] ^= 1,
        _ => binding.counts.swap(0, 1),
      }
      let mut builder = R1csBuilder::new();
      let rejected =
        emit(&mut builder, &binding, components, &bytes, q).is_err();
      assert!(rejected || builder.finish().is_err());
    }
  }
}
