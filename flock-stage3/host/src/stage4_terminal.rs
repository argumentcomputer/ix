use crate::{Stage3StatementV1, Stage4FlockVerifierWitnessV1};
use anyhow::{Result, bail};
use flock_prover::{
  circuit::{Circuit, SigmaAssertion},
  field::F128,
  matrix_fold::{
    FoldMatrix, JaggedTable, MatrixClaim, Weight, bilinear, discharge_jagged,
  },
  pcs::jagged::JaggedParams,
  schedule::Registry,
};
use ix_fflonk::{FflonkProofV1, FflonkVerificationKeyV1, verify_fflonk};
use ix_stage4_trace::F128MatrixSideV1;
use ix_terminal_circuit::{
  F128CircuitStructureRootClaimPublicInputV1, F128JaggedRootClaimPublicInputV1,
  F128RootMatrixClaimPublicInputV1, Stage4PublicInputsV1,
  Stage4RelationPublicInputsV1, Stage4RelationWitnessV1, Stage4TraceWitnessV1,
  Stage4TranscriptWitnessV1,
};

impl Stage4FlockVerifierWitnessV1 {
  /// Public values shared by the canonical circuit and terminal verifier.
  pub fn terminal_public_inputs(&self) -> Stage4RelationPublicInputsV1 {
    let accumulator = self.matrix_accumulator();
    let structure = accumulator.circuit_structure_root_claim();
    let jagged = accumulator.jagged_root_claim();
    Stage4RelationPublicInputsV1 {
      statement: Stage4PublicInputsV1::from_statement_digest(
        self.stage3_statement_digest(),
      ),
      matrices: accumulator
        .root_claims()
        .iter()
        .map(|root| F128RootMatrixClaimPublicInputV1 {
          matrix: root.matrix(),
          row_point: root.row_point().to_vec(),
          column_point: root.column_point().to_vec(),
          value: *root.value(),
        })
        .collect(),
      structure: F128CircuitStructureRootClaimPublicInputV1 {
        matrix: structure.matrix(),
        row_point: structure.row_point().to_vec(),
        column_point: structure.column_point().to_vec(),
        value: *structure.value(),
      },
      jagged: F128JaggedRootClaimPublicInputV1 {
        matrix: jagged.matrix(),
        row_point: jagged.row_point().to_vec(),
        column_point: jagged.column_point().to_vec(),
        value: *jagged.value(),
      },
    }
  }

  /// Borrow the native export without cloning its tapes or defining another
  /// relation in the host. All composition lives in `ix-terminal-circuit`.
  pub fn terminal_relation_witness(&self) -> Stage4RelationWitnessV1<'_> {
    let transcript = self.transcript();
    let accumulator = self.matrix_accumulator();
    Stage4RelationWitnessV1 {
      statement_binding: self.statement_binding(),
      stage3_statement: self.stage3_statement_bytes(),
      public_values: self.public_values(),
      transcript: Stage4TranscriptWitnessV1 {
        trace: transcript.chained_blake3(),
        observed_values: transcript.observed_values(),
        byte_payloads: transcript.byte_payloads(),
        challenges: transcript.challenges(),
      },
      algebra: Stage4TraceWitnessV1 {
        trace: transcript.f128_algebra(),
        private_values: transcript.f128_private_values(),
      },
      wiring: Stage4TraceWitnessV1 {
        trace: self.wiring().trace(),
        private_values: self.wiring().private_values(),
      },
      merged_pcs: self.merged_pcs().trace(),
      multipoint: Stage4TraceWitnessV1 {
        trace: self.multipoint_assist().trace(),
        private_values: self.multipoint_assist().private_values(),
      },
      inner_ligerito: Stage4TraceWitnessV1 {
        trace: self.inner_ligerito().trace(),
        private_values: self.inner_ligerito().private_values(),
      },
      inner_ligerito_private_digests: self.inner_ligerito().private_digests(),
      accumulator_transcript: Stage4TranscriptWitnessV1 {
        trace: accumulator.chained_blake3(),
        observed_values: accumulator.observed_values(),
        byte_payloads: accumulator.byte_payloads(),
        challenges: accumulator.challenges(),
      },
      matrix_fold: accumulator.trace(),
      structure_fold: accumulator.circuit_structure_trace(),
      jagged_fold: accumulator.jagged_trace(),
    }
  }
}

/// Static tables from the same trusted setup as the terminal FFLONK key.
/// These must be retained by the verifier, rather than supplied with a proof.
pub struct Stage4TerminalContextV1<'a> {
  registry: &'a Registry,
  circuit: &'a Circuit,
  jagged: &'a JaggedParams,
}

impl<'a> Stage4TerminalContextV1<'a> {
  pub fn new(
    registry: &'a Registry,
    circuit: &'a Circuit,
    jagged: &'a JaggedParams,
  ) -> Self {
    Self { registry, circuit, jagged }
  }

  /// Discharge every public root in the exact order compiled into the key.
  /// This checks the terminal claims only; acceptance also requires FFLONK.
  pub fn check_public_inputs(
    &self,
    expected: &Stage3StatementV1,
    public: &Stage4RelationPublicInputsV1,
  ) -> Result<()> {
    if public.statement.statement_digest() != expected.digest() {
      bail!(
        "Stage 4 public statement does not match the expected Stage 3 statement"
      );
    }
    if public.matrices.len() != 2 * self.registry.num_boolean() {
      bail!("Stage 4 terminal matrix root count mismatch");
    }
    let registry_digest = self.registry.digest();
    for (index, root) in public.matrices.iter().enumerate() {
      let table = index / 2;
      let ty = &self.registry.boolean_types()[table];
      let (side, matrix) = if index % 2 == 0 {
        (F128MatrixSideV1::A, &ty.a_0)
      } else {
        (F128MatrixSideV1::B, &ty.b_0)
      };
      let variables = matrix.n_rows().checked_ilog2();
      if root.matrix.registry_digest != registry_digest
        || usize::try_from(root.matrix.table).ok() != Some(table)
        || root.matrix.side != side
        || variables != Some(root.matrix.variables)
        || !matrix.n_rows().is_power_of_two()
        || matrix.n_rows() != matrix.n_cols()
        || root.row_point.len() != root.matrix.variables as usize
        || root.column_point.len() != root.matrix.variables as usize
      {
        bail!(
          "Stage 4 terminal matrix root {index} identity or shape mismatch"
        );
      }
      let claim = claim(&root.row_point, &root.column_point, root.value);
      if bilinear(&claim.row, &claim.col, matrix) != claim.value {
        bail!("Stage 4 terminal matrix root {index} evaluation mismatch");
      }
    }

    let root = &public.structure;
    let matrix = SigmaAssertion::matrix(self.circuit);
    if root.matrix.circuit_digest != self.circuit.digest()
      || matrix.n_rows().checked_ilog2() != Some(root.matrix.row_variables)
      || matrix.n_cols().checked_ilog2() != Some(root.matrix.column_variables)
      || !matrix.n_rows().is_power_of_two()
      || !matrix.n_cols().is_power_of_two()
      || root.row_point.len() != root.matrix.row_variables as usize
      || root.column_point.len() != root.matrix.column_variables as usize
    {
      bail!("Stage 4 terminal structure root identity or shape mismatch");
    }
    let structure = claim(&root.row_point, &root.column_point, root.value);
    if bilinear(&structure.row, &structure.col, &matrix) != structure.value {
      bail!("Stage 4 terminal structure root evaluation mismatch");
    }
    let root = &public.jagged;
    let table = JaggedTable::from_params(self.jagged);
    if root.matrix.circuit_digest != self.circuit.digest()
      || root.matrix.row_variables as usize != table.k
      || root.matrix.column_variables as usize != table.n_col_vars()
      || root.row_point.len() != table.k
      || root.column_point.len() != table.n_col_vars()
    {
      bail!("Stage 4 terminal jagged root identity or shape mismatch");
    }
    if !discharge_jagged(
      &claim(&root.row_point, &root.column_point, root.value),
      &table,
    ) {
      bail!("Stage 4 terminal jagged root evaluation mismatch");
    }
    Ok(())
  }
}

fn decode(word: [u8; 16]) -> F128 {
  F128::new(
    u64::from_le_bytes(word[..8].try_into().expect("eight bytes")),
    u64::from_le_bytes(word[8..].try_into().expect("eight bytes")),
  )
}

fn claim(
  row: &[[u8; 16]],
  column: &[[u8; 16]],
  value: [u8; 16],
) -> MatrixClaim {
  MatrixClaim {
    row: Weight::eq(row.iter().copied().map(decode).collect()),
    col: Weight::eq(column.iter().copied().map(decode).collect()),
    value: decode(value),
  }
}

/// Accept a terminal proof only after verifying its external statement,
/// every deferred root, and the FFLONK equation over those same public fields.
/// `context` and `key` are trusted outputs of the same canonical circuit setup.
pub fn verify_stage4_terminal(
  context: &Stage4TerminalContextV1<'_>,
  key: &FflonkVerificationKeyV1,
  expected: &Stage3StatementV1,
  proof: &FflonkProofV1,
  public: &Stage4RelationPublicInputsV1,
) -> Result<()> {
  context.check_public_inputs(expected, public)?;
  if !verify_fflonk(key, proof, &public.field_elements())? {
    bail!("Stage 4 terminal FFLONK proof rejected");
  }
  Ok(())
}

/// Exercise terminal acceptance over the real root vector using a small
/// public-binding circuit. This is a verifier-boundary test; proving the full
/// Flock relation still requires the production backend.
#[cfg(test)]
pub(crate) fn assert_fflonk_boundary(
  context: &Stage4TerminalContextV1<'_>,
  expected: &Stage3StatementV1,
  public: &Stage4RelationPublicInputsV1,
) {
  use ark_bls12_381::{Fr, G1Affine, G2Affine};
  use ark_ec::{AffineRepr, CurveGroup};
  use ark_ff::{Field, PrimeField};
  use ix_fflonk::{
    FflonkBlindingV1, KzgUniversalSrsV1, arithmetize_r1cs, preprocess_fflonk,
    prove_fflonk, required_fflonk_srs_degree,
  };
  use ix_terminal_circuit::{ConstraintPhase, LinearCombination, R1csBuilder};

  let fields = public.field_elements();
  let mut builder = R1csBuilder::new();
  let variables = fields
    .iter()
    .map(|&value| builder.alloc_public(value).unwrap())
    .collect::<Vec<_>>();
  let mut private_variables = Vec::with_capacity(fields.len());
  for (variable, value) in variables.iter().copied().zip(&fields) {
    let private = builder.alloc_private(*value).unwrap();
    private_variables.push(private);
    builder.enforce_zero(
      ConstraintPhase::Statement,
      LinearCombination::from_variable(variable)
        .minus(&LinearCombination::from_variable(private)),
    );
  }
  let (r1cs, witness) = builder.finish().unwrap();
  let arithmetization = arithmetize_r1cs(&r1cs).unwrap();
  let degree =
    required_fflonk_srs_degree(arithmetization.census().domain_size).unwrap();
  // Deterministic toxic waste is confined to this test fixture.
  let tau = Fr::from(29u64);
  let mut scalar = Fr::ONE;
  let powers = (0..=degree)
    .map(|_| {
      let point = G1Affine::generator().mul_bigint(scalar.into_bigint());
      scalar *= tau;
      point.into_affine()
    })
    .collect();
  let tau_g2 =
    G2Affine::generator().mul_bigint(tau.into_bigint()).into_affine();
  let srs =
    KzgUniversalSrsV1::new(powers, G2Affine::generator(), tau_g2).unwrap();
  let preprocessed = preprocess_fflonk(&srs, arithmetization).unwrap();
  let blinding = FflonkBlindingV1 {
    wire_evaluations: core::array::from_fn(|i| Fr::from(i as u64 + 31)),
    z_coefficients: [Fr::from(41u64), Fr::from(43u64), Fr::from(47u64)],
  };
  let output =
    prove_fflonk(&srs, &preprocessed, &r1cs, &witness, blinding).unwrap();
  assert_eq!(output.public_inputs, fields);
  let key = preprocessed.verification_key();
  let proof = FflonkProofV1::from_bytes(&output.proof.to_bytes()).unwrap();
  verify_stage4_terminal(context, &key, expected, &proof, public).unwrap();

  let mut corrupt = proof.clone();
  corrupt.evaluations[0] += Fr::ONE;
  assert!(
    verify_stage4_terminal(context, &key, expected, &corrupt, public).is_err()
  );

  // A different, correctly evaluated root must still fail the proof binding.
  let mut changed = public.clone();
  let root = &mut changed.matrices[0];
  root.row_point[0][0] ^= 1;
  let root_claim = claim(&root.row_point, &root.column_point, root.value);
  let value = bilinear(
    &root_claim.row,
    &root_claim.col,
    &context.registry.boolean_types()[0].a_0,
  );
  root.value[..8].copy_from_slice(&value.lo.to_le_bytes());
  root.value[8..].copy_from_slice(&value.hi.to_le_bytes());
  context.check_public_inputs(expected, &changed).unwrap();
  assert!(
    verify_stage4_terminal(context, &key, expected, &proof, &changed).is_err()
  );

  // Even a valid proof of the public-binding circuit cannot authorize an
  // incorrect root. This checks that terminal acceptance runs both verifiers.
  let mut incorrect = public.clone();
  let root = &mut incorrect.matrices[0];
  root.value[0] ^= 1;
  let field_index = 2 + root.row_point.len() + root.column_point.len();
  let incorrect_fields = incorrect.field_elements();
  let mut incorrect_witness = witness;
  for variable in [variables[field_index], private_variables[field_index]] {
    incorrect_witness.set(variable, incorrect_fields[field_index]).unwrap();
  }
  let incorrect_output =
    prove_fflonk(&srs, &preprocessed, &r1cs, &incorrect_witness, blinding)
      .unwrap();
  assert!(
    verify_fflonk(&key, &incorrect_output.proof, &incorrect_fields).unwrap()
  );
  assert!(
    verify_stage4_terminal(
      context,
      &key,
      expected,
      &incorrect_output.proof,
      &incorrect,
    )
    .is_err()
  );
}
