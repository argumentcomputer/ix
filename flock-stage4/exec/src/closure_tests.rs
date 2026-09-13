use super::{hash, memory_summary, output, program, prove, setup};
use crate::{
  ExecRootClosedCensusLimitsV0, ExecRootClosedCensusOutcomeV0,
  ExecRootClosureCompilationLimitsV0, ExecSetupR1csLimitsV0,
  census_exec_root_closed_observed, census_exec_root_closed_setup_observed,
  compile_exec_replay, compile_exec_root_closure,
};
use flock_prover::field::F128;
use ix_stage4_trace::{
  BinaryLinearMapLimitsV0, BinaryLinearReferenceV0 as Ref,
  BinaryLinearValidationLimitsV0, ExecCommitmentsV0,
  F128FixedMatrixProgramV0 as Program, F128FixedTableLimitsV0,
  F128FixedTableNodeV0 as Node,
};
use ix_terminal_circuit::{
  Constraint, R1csBuilder, R1csError, R1csShapeLimitsV0, Stage4PublicInputsV1,
};
use std::time::Instant;
use std::{cell::RefCell, rc::Rc};

const LIMITS: ExecRootClosureCompilationLimitsV0 =
  ExecRootClosureCompilationLimitsV0 {
    diagrams: F128FixedTableLimitsV0 { entries: 64_000_000, nodes: 2_000_000 },
    linear_program: BinaryLinearMapLimitsV0 {
      inputs: 16_384,
      outputs: 16_384,
      xors: 100_000,
    },
    linear_validation: BinaryLinearValidationLimitsV0 {
      coefficient_words: 64_000_000,
      source_entries: 48_000_000,
    },
  };

fn decode(bytes: &[u8; 16]) -> F128 {
  F128::new(
    u64::from_le_bytes(bytes[..8].try_into().unwrap()),
    u64::from_le_bytes(bytes[8..].try_into().unwrap()),
  )
}

// Test-only native-field evaluator, independent of the R1CS implementations.
// Comparison with native fold roots is a differential, NOT root discharge.
fn evaluate(table: &Program, row: &[[u8; 16]], col: &[[u8; 16]]) -> F128 {
  let row: Vec<_> = row.iter().map(decode).collect();
  let col: Vec<_> = col.iter().map(decode).collect();
  match table {
    Program::DecisionDiagram(table) => {
      let point = [row, col].concat();
      assert_eq!(point.len(), table.order().len());
      let mut values = Vec::new();
      for node in table.nodes() {
        let value = match *node {
          Node::Constant(bytes) => decode(&bytes),
          Node::Branch { coordinate, low, high } => {
            let low = values[low as usize];
            low + point[coordinate as usize] * (low + values[high as usize])
          },
          Node::Davio { coordinate, base, slope, complement } => {
            let factor = point[coordinate as usize]
              + if complement { F128::ONE } else { F128::ZERO };
            values[base as usize] + factor * values[slope as usize]
          },
        };
        values.push(value);
      }
      values[table.root() as usize]
    },
    Program::BinaryLinear(map) => {
      let inputs = (0..map.inputs())
        .map(|i| {
          col.iter().enumerate().fold(F128::ONE, |p, (bit, x)| {
            p * (*x + if i >> bit & 1 == 0 { F128::ONE } else { F128::ZERO })
          })
        })
        .collect::<Vec<_>>();
      let resolve = |r, ops: &[F128]| match r {
        Ref::Zero => F128::ZERO,
        Ref::Input(i) => inputs[i as usize],
        Ref::Xor(i) => ops[i as usize],
      };
      let mut operations = Vec::new();
      for &(a, b) in map.xors() {
        operations.push(resolve(a, &operations) + resolve(b, &operations));
      }
      let mut values = map
        .outputs()
        .iter()
        .map(|&r| resolve(r, &operations))
        .collect::<Vec<_>>();
      for x in row {
        values = values
          .as_chunks::<2>()
          .0
          .iter()
          .map(|p| p[0] + x * (p[0] + p[1]))
          .collect();
      }
      assert_eq!(values.len(), 1);
      values[0]
    },
  }
}

// Reconstruct Q from the caller's expected program/result, independently of
// any replay witness (and with no proof-input commitment needed).
fn expected_public(
  profile: [u8; 32],
  branch: bool,
  value: bool,
) -> Stage4PublicInputsV1 {
  let program = hash(1, &profile, &program(branch));
  let output = hash(3, &program, &output(value));
  Stage4PublicInputsV1::from_statement_digest(
    ExecCommitmentsV0 { program, input: [0; 32], output }
      .public_digest(profile),
  )
}

// A deliberately small EXACT prefix comparison, not a full-circuit digest.
// Nontrivial hashing/field/fold/Merkle/root matrix equality is covered by the
// materialized component tests; this also checks the real setup entry point.
fn captured_prefix(
  shape_only: bool,
  emit: impl FnOnce(&mut R1csBuilder) -> anyhow::Result<()>,
) -> Vec<Constraint> {
  const LIMIT: usize = 4096;
  let rows = Rc::new(RefCell::new(Vec::new()));
  let target = Rc::clone(&rows);
  let observer = move |c: &Constraint| {
    target.borrow_mut().push(c.clone());
    if target.borrow().len() == LIMIT {
      Err(R1csError::ResourceLimit {
        resource: "test R1CS prefix",
        limit: (LIMIT - 1) as u64,
        actual: LIMIT as u64,
      })
    } else {
      Ok(())
    }
  };
  let mut builder = if shape_only {
    R1csBuilder::new_shape_projection_observed_fallible(observer)
  } else {
    R1csBuilder::new_projection_observed_fallible(observer)
  };
  assert!(emit(&mut builder).is_err());
  assert!(matches!(
    builder.finish_projection(),
    Err(R1csError::ResourceLimit { resource: "test R1CS prefix", .. })
  ));
  let rows = Rc::try_unwrap(rows).unwrap().into_inner();
  assert_eq!(rows.len(), LIMIT);
  rows
}

#[test]
#[ignore = "real Exec proofs, setup-owned closure tables and bounded emission; not a full closed census/proof"]
fn setup_owned_closure_matches_all_real_fold_roots() {
  let setup = setup();
  let replay = compile_exec_replay(&setup).unwrap();
  let started = Instant::now();
  // BOTH complete root plans are built before the first guest/proof exists.
  let closure = compile_exec_root_closure(&replay, LIMITS).unwrap();
  let rebuilt = compile_exec_root_closure(&replay, LIMITS).unwrap();
  assert_eq!(closure.digest(), rebuilt.digest());
  assert_eq!(closure.tables(), rebuilt.tables());
  assert!(std::ptr::eq(closure.replay_setup(), &replay));
  let slots = closure.setup_source_slots().unwrap();
  assert_eq!(slots, rebuilt.setup_source_slots().unwrap());
  drop(rebuilt);
  let slot_bytes = slots.payload_bytes().unwrap();
  assert!(slot_bytes > 0);
  let setup_prefix =
    captured_prefix(true, |builder| closure.emit_setup(builder, slot_bytes));
  let setup_censuses = [0, 4, 1000].map(|limit| {
    census_exec_root_closed_setup_observed(
      &closure,
      slot_bytes,
      ExecRootClosedCensusLimitsV0 { required_domain_rows: limit },
      |_| {},
    )
    .unwrap()
  });
  let matrix_limits = R1csShapeLimitsV0 {
    variables: 1_000_000,
    constraints: 1000,
    nonzero_terms: 1_000_000,
  };
  let limited = |source_payload_bytes| ExecSetupR1csLimitsV0 {
    source_payload_bytes,
    r1cs: matrix_limits,
  };
  let refused = closure.build_setup_r1cs(limited(slot_bytes - 1)).unwrap_err();
  assert!(
    matches!(refused.downcast_ref::<R1csError>(), Some(R1csError::ResourceLimit {
    resource: "Exec setup source-slot payload bytes", limit, actual,
  }) if *limit == slot_bytes - 1 && *actual == slot_bytes)
  );
  let refused = closure.build_setup_r1cs(limited(slot_bytes)).unwrap_err();
  assert!(matches!(
    refused.downcast_ref::<R1csError>(),
    Some(R1csError::ResourceLimit {
      resource: "R1CS constraints",
      limit: 1000,
      actual: 1001,
    })
  ));
  let mut wrong_mode = R1csBuilder::new_projection();
  assert!(closure.emit_setup(&mut wrong_mode, slot_bytes).is_err());
  assert_eq!(wrong_mode.finish_projection().unwrap().census().constraints, 0);
  let mut under_budget = R1csBuilder::new_shape_projection();
  assert!(closure.emit_setup(&mut under_budget, slot_bytes - 1).is_err());
  let empty = under_budget.finish_projection().unwrap();
  assert_eq!(empty.public_variables(), 0);
  assert_eq!(empty.census().constraints, 0);
  assert!(
    census_exec_root_closed_setup_observed(
      &closure,
      slot_bytes,
      ExecRootClosedCensusLimitsV0 {
        required_domain_rows: ix_fflonk::FFLONK_MAX_BASE_DOMAIN + 1
      },
      |_| {}
    )
    .is_err()
  );
  eprintln!(
    "closed composition compiled twice before proofs in {:.3}s; composition {:?}; tables {:?}; {}",
    started.elapsed().as_secs_f64(),
    closure.digest(),
    closure.tables().digest(),
    memory_summary()
  );
  eprintln!(
    "proof-free source slots before any guest/proof: {slots:?}; payload {slot_bytes} bytes; matched bounded materialization/refusal"
  );
  assert_eq!(closure.tables().matrices().len(), 46);
  assert_eq!(
    closure
      .tables()
      .matrices()
      .iter()
      .filter(|(_, p)| matches!(p, Program::BinaryLinear(_)))
      .count(),
    2
  );
  for (branch, value) in [(false, false), (true, false), (true, true)] {
    let (commitments, bytes) = prove(&setup, branch, value);
    let mut witness = replay.replay(commitments, &bytes).unwrap();
    let public = expected_public(setup.identities().profile, branch, value);
    let assigned_prefix = captured_prefix(false, |builder| {
      closure.constrain(builder, public, &witness).map(|_| ())
    });
    assert_eq!(setup_prefix, assigned_prefix);
    for (limit, expected) in [0, 4, 1000].into_iter().zip(&setup_censuses) {
      let actual = census_exec_root_closed_observed(
        &closure,
        public,
        &witness,
        ExecRootClosedCensusLimitsV0 { required_domain_rows: limit },
        |_| {},
      )
      .unwrap();
      assert_eq!(&actual, expected);
    }
    assert_eq!(public.statement_digest(), witness.public_digest());
    let roots = witness.matrix_accumulator();
    assert_eq!(roots.root_claims().len(), closure.tables().matrices().len());
    for ((id, table), root) in
      closure.tables().matrices().iter().zip(roots.root_claims())
    {
      assert_eq!(*id, root.matrix());
      assert_eq!(
        evaluate(table, root.row_point(), root.column_point()),
        decode(root.value())
      );
    }
    let root = roots.circuit_structure_root_claim();
    assert_eq!(closure.tables().structure().0, root.matrix());
    assert_eq!(
      evaluate(
        &closure.tables().structure().1,
        root.row_point(),
        root.column_point()
      ),
      decode(root.value())
    );
    let root = roots.jagged_root_claim();
    assert_eq!(closure.tables().jagged().0, root.matrix());
    assert_eq!(
      evaluate(
        &closure.tables().jagged().1,
        root.row_point(),
        root.column_point()
      ),
      decode(root.value())
    );
    // Tiny budgets exercise the actual closed entry point but do not purport
    // to reach the root constraints or complete the entire verifier circuit.
    for limit in [0, 4, 1000] {
      let result = census_exec_root_closed_observed(
        &closure,
        public,
        &witness,
        ExecRootClosedCensusLimitsV0 { required_domain_rows: limit },
        |_| {},
      )
      .unwrap();
      let ExecRootClosedCensusOutcomeV0::RejectedBudget {
        prefix,
        required_rows,
        ..
      } = result
      else {
        panic!("a bounded prefix must not become a complete census");
      };
      assert!(required_rows > limit);
      if limit == 0 {
        assert_eq!(prefix.plonk.r1cs_constraints, 0);
      } else {
        assert!(prefix.plonk.r1cs_constraints > 0);
      }
    }
    assert!(
      census_exec_root_closed_observed(
        &closure,
        public,
        &witness,
        ExecRootClosedCensusLimitsV0 {
          required_domain_rows: ix_fflonk::FFLONK_MAX_BASE_DOMAIN + 1,
        },
        |_| {},
      )
      .is_err()
    );
    // Inspect the first actual transcript constraint: its first private bit
    // is wire 3, immediately after Q's two limbs, with no public root slots.
    let failure =
      R1csError::ObserverFailure("test first-constraint stop".into());
    let refused = failure.clone();
    let mut builder = R1csBuilder::new_projection_observed_fallible(move |c| {
      assert!(
        [&c.a, &c.b, &c.c]
          .iter()
          .flat_map(|lc| lc.terms())
          .any(|(v, _)| v.index() == 3)
      );
      Err(refused.clone())
    });
    assert!(closure.constrain(&mut builder, public, &witness).is_err());
    assert_eq!(builder.finish_projection(), Err(failure));
    // Test-only corruption of the opaque replay identity cannot emit even a
    // prefix. Neither mutation is possible through the public witness API.
    witness.topology_digest[0] ^= 1;
    let mut builder = R1csBuilder::new_projection();
    assert!(closure.constrain(&mut builder, public, &witness).is_err());
    let empty = builder.finish_projection().unwrap();
    assert_eq!(empty.public_variables(), 0);
    assert_eq!(empty.census().constraints, 0);
    witness.topology_digest[0] ^= 1;
    witness.binding.registry_digest[0] ^= 1;
    let mut builder = R1csBuilder::new_projection();
    assert!(closure.constrain(&mut builder, public, &witness).is_err());
    assert_eq!(builder.finish_projection().unwrap(), empty);
    eprintln!(
      "closed-table native differential branch={branch} value={value}: all 48 roots and bounded-entry negatives passed; {}",
      memory_summary()
    );
  }
}

#[test]
#[ignore = "full root-closed emission with hard supported-domain cutoff; a rejected prefix is NOT a full census/proof"]
fn root_closed_supported_domain_admission_census() {
  let setup = setup();
  let replay = compile_exec_replay(&setup).unwrap();
  let closure = compile_exec_root_closure(&replay, LIMITS).unwrap();
  let (commitments, bytes) = prove(&setup, false, false);
  let witness = replay.replay(commitments, &bytes).unwrap();
  let public = expected_public(setup.identities().profile, false, false);
  let start = Instant::now();
  eprintln!(
    "starting bounded full root-closed emission: composition {:?}; tables {:?}; {}",
    closure.digest(),
    closure.tables().digest(),
    memory_summary()
  );
  let result = census_exec_root_closed_observed(
    &closure,
    public,
    &witness,
    ExecRootClosedCensusLimitsV0 {
      required_domain_rows: ix_fflonk::FFLONK_MAX_BASE_DOMAIN,
    },
    move |progress| {
      eprintln!(
        "root-closed prefix {:.3}s: {progress:?}; {}",
        start.elapsed().as_secs_f64(),
        memory_summary()
      );
    },
  )
  .unwrap();
  eprintln!(
    "root-closed domain admission finished in {:.3}s (NOT a proof): {result:#?}; {}",
    start.elapsed().as_secs_f64(),
    memory_summary()
  );
  match result {
    ExecRootClosedCensusOutcomeV0::Complete(census) => {
      assert_eq!(census.public_scalar_bytes, 64);
      assert_eq!(census.r1cs.census().constraints_by_phase.len(), 7);
      assert!(
        ix_fflonk::plan_fflonk_capacity(&census.plonk)
          .unwrap()
          .supported_polynomial_fft_domain
      );
    },
    ExecRootClosedCensusOutcomeV0::RejectedBudget {
      limit,
      required_rows,
      prefix,
    } => {
      assert_eq!(limit, ix_fflonk::FFLONK_MAX_BASE_DOMAIN);
      assert!(required_rows > limit);
      assert!(prefix.plonk.r1cs_constraints > 0);
    },
  }
}

#[test]
#[ignore = "bounded WHOLE proof-free root-closed emission; potentially minutes; no guest, Flock proof, R1CS assignment, key or terminal proof"]
fn proof_free_root_closed_supported_domain_admission_census() {
  let setup = setup();
  let replay = compile_exec_replay(&setup).unwrap();
  let closure = compile_exec_root_closure(&replay, LIMITS).unwrap();
  let slots = closure.setup_source_slots().unwrap();
  let slot_bytes = slots.payload_bytes().unwrap();
  assert!(slot_bytes <= 32_000_000);
  let start = Instant::now();
  eprintln!(
    "starting WHOLE proof-free root-closed setup emission: composition {:?}; tables {:?}; slots {slots:?}; source payload {slot_bytes} bytes; {}",
    closure.digest(),
    closure.tables().digest(),
    memory_summary()
  );
  let result = census_exec_root_closed_setup_observed(
    &closure,
    slot_bytes,
    ExecRootClosedCensusLimitsV0 {
      required_domain_rows: ix_fflonk::FFLONK_MAX_BASE_DOMAIN,
    },
    move |progress| {
      eprintln!(
        "proof-free root-closed prefix {:.3}s: {progress:?}; {}",
        start.elapsed().as_secs_f64(),
        memory_summary()
      )
    },
  )
  .unwrap();
  eprintln!(
    "proof-free root-closed setup admission finished in {:.3}s (NOT a key/proof): {result:#?}; {}",
    start.elapsed().as_secs_f64(),
    memory_summary()
  );
  match result {
    ExecRootClosedCensusOutcomeV0::Complete(census) => {
      assert_eq!(census.public_scalar_bytes, 64);
      assert_eq!(census.r1cs.census().constraints_by_phase.len(), 7);
      assert!(
        ix_fflonk::plan_fflonk_capacity(&census.plonk)
          .unwrap()
          .supported_polynomial_fft_domain
      );
    },
    ExecRootClosedCensusOutcomeV0::RejectedBudget {
      limit,
      required_rows,
      prefix,
    } => {
      assert_eq!(limit, ix_fflonk::FFLONK_MAX_BASE_DOMAIN);
      assert!(required_rows > limit);
      // Current lowering must reach exactly the recorded f57a0194 native
      // witness census cutoff. This is a prefix COUNT differential, not a
      // complete R1CS identity or completed circuit. Component tests compare
      // actual matrices and assignments. Deliberate cost changes need a new
      // recorded baseline rather than silently reusing these figures.
      assert_eq!(prefix.plonk.r1cs_constraints, 643_831_813);
      assert_eq!(prefix.plonk.constraint_rows, 1_073_741_821);
      assert_eq!(prefix.plonk.auxiliary_wires, 429_910_008);
      assert_eq!(
        prefix.last_phase,
        Some(ix_terminal_circuit::ConstraintPhase::MatrixFold)
      );
    },
  }
}
