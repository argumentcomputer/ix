use super::*;
use crate::{
  CanonicalR1csV1, Witness, alloc_f128_private,
  f128::{native_f128_add as add, native_f128_multiply as multiply},
};
use ark_bls12_381::Fr;
use ark_ff::Field;
use ix_stage4_trace::{
  BinaryLinearMapLimitsV0, BinaryLinearMapV0, BinaryLinearReferenceV0 as Ref,
  F128CircuitStructureMatrixIdV1, F128FixedTableLimitsV0, F128FixedTableV0,
  F128JaggedMatrixIdV1, F128MatrixFoldTraceV1, F128MatrixSideV1,
  F128StaticMatrixIdV1,
};

const A: [(u64, [u8; 16]); 2] = [(0, [7; 16]), (3, [9; 16])];
const B: [(u64, [u8; 16]); 2] =
  [(0, 1u128.to_le_bytes()), (3, 1u128.to_le_bytes())];
const S: [(u64, [u8; 16]); 1] = [(1, [0xa5; 16])];
const J: [(u64, [u8; 16]); 1] = [(0, 1u128.to_le_bytes())];

fn tables() -> F128RootTableSetV0 {
  let diagram = |bits, entries: &[(u64, [u8; 16])]| {
    F128FixedMatrixProgramV0::DecisionDiagram(
      F128FixedTableV0::compile(
        &(0..bits).rev().collect::<Vec<_>>(),
        entries.iter().copied(),
        F128FixedTableLimitsV0 { entries: 100, nodes: 100 },
      )
      .unwrap(),
    )
  };
  let a = F128StaticMatrixIdV1 {
    registry_digest: [3; 32],
    table: 0,
    side: F128MatrixSideV1::A,
    variables: 1,
  };
  let b = F128StaticMatrixIdV1 { side: F128MatrixSideV1::B, ..a };
  F128RootTableSetV0::new(
    [3; 32],
    [5; 32],
    vec![
      (a, diagram(2, &A)),
      (
        b,
        F128FixedMatrixProgramV0::BinaryLinear(
          BinaryLinearMapV0::compile(
            2,
            vec![],
            vec![Ref::Input(0), Ref::Input(1)],
            BinaryLinearMapLimitsV0 { inputs: 2, xors: 0, outputs: 2 },
          )
          .unwrap(),
        ),
      ),
    ],
    (
      F128CircuitStructureMatrixIdV1 {
        circuit_digest: [5; 32],
        row_variables: 1,
        column_variables: 1,
      },
      diagram(2, &S),
    ),
    (
      F128JaggedMatrixIdV1 {
        circuit_digest: [5; 32],
        row_variables: 0,
        column_variables: 1,
      },
      diagram(1, &J),
    ),
  )
  .unwrap()
}

fn root(
  builder: &mut R1csBuilder,
  row: &[[u8; 16]],
  column: &[[u8; 16]],
  entries: &[(u64, [u8; 16])],
  forge: bool,
) -> (Vec<F128VariablesV1>, Vec<F128VariablesV1>, F128VariablesV1) {
  let mut expected = entries.iter().fold([0; 16], |sum, &(index, value)| {
    let term =
      row.iter().chain(column).enumerate().fold(value, |p, (bit, &x)| {
        multiply(
          p,
          if index >> bit & 1 == 0 { add(x, 1u128.to_le_bytes()) } else { x },
        )
      });
    add(sum, term)
  });
  if forge {
    expected[0] ^= 1;
  }
  let row = row
    .iter()
    .map(|&x| alloc_f128_private(builder, x, PHASE).unwrap())
    .collect();
  let column = column
    .iter()
    .map(|&x| alloc_f128_private(builder, x, PHASE).unwrap())
    .collect();
  let claim = alloc_f128_private(builder, expected, PHASE).unwrap();
  (row, column, claim)
}

fn roots(
  builder: &mut R1csBuilder,
  tables: &F128RootTableSetV0,
  seed: u8,
  forged: Option<usize>,
) -> (
  Vec<F128RootMatrixClaimVariablesV1>,
  F128CircuitStructureRootClaimVariablesV1,
  F128JaggedRootClaimVariablesV1,
) {
  let mut matrices = Vec::new();
  for (i, entries) in [&A[..], &B[..]].into_iter().enumerate() {
    let (row_point, column_point, value) =
      root(builder, &[[seed; 16]], &[[0xd1; 16]], entries, forged == Some(i));
    matrices.push(F128RootMatrixClaimVariablesV1 {
      matrix: tables.matrices()[i].0,
      row_point,
      column_point,
      value,
    });
  }
  let (row_point, column_point, value) =
    root(builder, &[[0xee; 16]], &[[seed; 16]], &S, forged == Some(2));
  let structure = F128CircuitStructureRootClaimVariablesV1 {
    matrix: tables.structure().0,
    row_point,
    column_point,
    value,
  };
  let (row_point, column_point, value) =
    root(builder, &[], &[[seed; 16]], &J, forged == Some(3));
  let jagged = F128JaggedRootClaimVariablesV1 {
    matrix: tables.jagged().0,
    row_point,
    column_point,
    value,
  };
  (matrices, structure, jagged)
}

fn materialize(
  seed: u8,
  forged: Option<usize>,
) -> Result<(CanonicalR1csV1, Witness, Vec<F128VariablesV1>), R1csError> {
  let tables = tables();
  let mut builder = R1csBuilder::new();
  let (matrices, structure, jagged) =
    roots(&mut builder, &tables, seed, forged);
  let outputs =
    constrain_f128_matrix_root_tables(&mut builder, &tables, &matrices)
      .unwrap();
  let s =
    constrain_f128_structure_root_table(&mut builder, &tables, &structure)
      .unwrap();
  let j =
    constrain_f128_jagged_root_table(&mut builder, &tables, &jagged).unwrap();
  let claims = matrices
    .into_iter()
    .map(|r| r.value)
    .chain([structure.value, jagged.value])
    .collect::<Vec<_>>();
  if forged.is_none() {
    for (a, b) in claims.iter().zip(outputs.iter().chain([&s, &j])) {
      assert_eq!(a.value(), b.value());
    }
  }
  // A false claim reaches the constraint checker: it is not rejected by a
  // native table-value comparison standing in for the equality constraint.
  let (r1cs, witness) = builder.finish()?;
  Ok((r1cs, witness, claims))
}

#[test]
fn every_root_family_is_constrained_without_public_root_inputs() {
  let mut shape = None;
  for seed in [0, 1, 0x71] {
    let (r1cs, witness, claims) = materialize(seed, None).unwrap();
    assert_eq!(r1cs.public_variables(), 0);
    r1cs.check(&witness).unwrap();
    for claim in claims {
      for &bit in claim.bit_variables() {
        let mut bad = witness.clone();
        bad.set(bit, Fr::ONE - bad.assignment()[bit.index() as usize]).unwrap();
        assert!(r1cs.check(&bad).is_err());
      }
    }
    if let Some(digest) = shape {
      assert_eq!(r1cs.digest(), digest);
    } else {
      shape = Some(r1cs.digest());
    }
  }
  for family in 0..4 {
    assert!(materialize(0x31, Some(family)).is_err());
  }
}

#[test]
fn missing_duplicated_reordered_or_malformed_roots_fail_before_emission() {
  let tables = tables();
  let (matrices, structure, jagged) =
    roots(&mut R1csBuilder::new(), &tables, 7, None);
  for case in 0..6 {
    let mut bad = matrices.clone();
    match case {
      0 => {
        bad.pop();
      },
      1 => bad.push(bad[0].clone()),
      2 => bad.swap(0, 1),
      3 => bad[1] = bad[0].clone(),
      4 => bad[1].matrix.registry_digest[0] ^= 1,
      5 => bad[1].column_point.clear(),
      _ => unreachable!(),
    }
    let mut builder = R1csBuilder::new_projection();
    assert!(
      constrain_f128_matrix_root_tables(&mut builder, &tables, &bad).is_err()
    );
    assert_eq!(builder.finish_projection().unwrap().census().constraints, 0);
  }
  for change_identity in [false, true] {
    let mut s = structure.clone();
    let mut j = jagged.clone();
    if change_identity {
      s.matrix.circuit_digest[0] ^= 1;
      j.matrix.circuit_digest[0] ^= 1;
    } else {
      s.row_point.clear();
      j.column_point.clear();
    }
    let mut builder = R1csBuilder::new_projection();
    assert!(
      constrain_f128_structure_root_table(&mut builder, &tables, &s).is_err()
    );
    assert!(
      constrain_f128_jagged_root_table(&mut builder, &tables, &j).is_err()
    );
    assert_eq!(builder.finish_projection().unwrap().census().constraints, 0);
  }
}

#[test]
fn root_plan_preflight_checks_binding_and_each_fold_identity() {
  let tables = tables();
  // Identity-only fixtures: the independent fold validators still need to
  // check all sumcheck/transcript topology before these could be executed.
  let binding = ExecBindingV0 {
    profile_digest: [0; 32],
    registry_digest: [3; 32],
    circuit_digest: [5; 32],
    counts: vec![],
    public_template: vec![],
  };
  let matrices = F128MatrixAccumulatorTraceV1 {
    registry_digest: [3; 32],
    registry_digest_payload: 0,
    prior_count_payload: 1,
    prior_accumulators: 0,
    folds: tables
      .matrices()
      .iter()
      .map(|(id, _)| F128MatrixFoldTraceV1 {
        matrix: *id,
        claims: vec![],
        lambda_challenges: vec![],
        column_rounds: vec![],
        bridge_observations: vec![],
        mu_challenges: vec![],
        row_rounds: vec![],
        value_observation: 0,
      })
      .collect(),
  };
  let structure = F128CircuitStructureAccumulatorTraceV1 {
    matrix: tables.structure().0,
    circuit_digest_payload: 0,
    claims: vec![],
    lambda_challenges: vec![],
    column_rounds: vec![],
    bridge_observations: vec![],
    mu_challenges: vec![],
    row_rounds: vec![],
    value_observation: 0,
  };
  let jagged = F128JaggedAccumulatorTraceV1 {
    matrix: tables.jagged().0,
    circuit_digest_payload: 0,
    shape_observation: 0,
    claims: vec![],
    lambda_challenges: vec![],
    column_rounds: vec![],
    bridge_observations: vec![],
    mu_challenges: vec![],
    row_rounds: vec![],
    value_observation: 0,
  };
  validate_exec_root_tables(&tables, &binding, &matrices, &structure, &jagged)
    .unwrap();
  for case in 0..7 {
    let (mut b, mut m, mut s, mut j) =
      (binding.clone(), matrices.clone(), structure.clone(), jagged.clone());
    match case {
      0 => b.registry_digest[0] ^= 1,
      1 => b.circuit_digest[0] ^= 1,
      2 => m.registry_digest[0] ^= 1,
      3 => m.folds.swap(0, 1),
      4 => {
        m.folds.pop();
      },
      5 => s.matrix.column_variables += 1,
      6 => j.matrix.circuit_digest[0] ^= 1,
      _ => unreachable!(),
    }
    assert!(validate_exec_root_tables(&tables, &b, &m, &s, &j).is_err());
  }
}
