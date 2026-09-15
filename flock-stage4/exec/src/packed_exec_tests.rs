//! Explicit packed-BLAKE3 Exec backend integration. Native proof/replay,
//! exact root differentials and WHOLE bounded census have separate tests.
//! None generates a terminal key or proves the closed FFLONK relation.

use super::{
  CAPACITY,
  capacity_tests::SMALL,
  closure_tests::{LIMITS, captured_prefix, decode, evaluate},
  hash, input, memory_summary, output, program,
};
use crate::{
  ExecRootClosedCensusLimitsV0, ExecRootClosedCensusOutcomeV0,
  census_exec_root_closed_setup_observed, compile_exec_replay,
  compile_exec_root_closure,
};
use flock_prover::union::UnionInstance;
use ix_stage4_trace::{ExecCommitmentsV0, F128FixedMatrixProgramV0 as Program};
use ix_terminal_circuit::Stage4PublicInputsV1;
use ixby_flock::{
  blake3_backend::Blake3Backend,
  ixby::{
    decode::PrimitiveSet,
    exec::{
      CompiledExec, SemanticProfile, compile_exec_profile_with_backend,
      expected_statement,
    },
    machine::MachineCapacities,
  },
};
use std::time::Instant;

fn setup(capacity: MachineCapacities) -> CompiledExec {
  compile_exec_profile_with_backend(
    SemanticProfile::scalar(capacity).unwrap(),
    capacity,
    PrimitiveSet::scalar(),
    Blake3Backend::PackedWordsV0,
  )
  .unwrap()
}

#[test]
#[ignore = "proof-free packed Exec setup/replay/closure for two explicit capacities; not a complete constraint census"]
fn packed_exec_geometry_and_exact_root_programs_are_setup_owned() {
  for (name, capacity) in [("baseline", CAPACITY), ("small", SMALL)] {
    let started = Instant::now();
    let setup = setup(capacity);
    let union = UnionInstance::new(
      &setup.verifier_shape().registry,
      setup.verifier_shape().counts.clone(),
    );
    let params = setup.pcs_params();
    let config = params.ligerito_verifier_config().unwrap();
    assert_eq!(params.profile.as_str(), "fast128");
    assert_eq!(config.queries, vec![244, 79, 48]);
    assert_eq!(config.grinding_bits, vec![16, 16, 16]);
    let replay = compile_exec_replay(&setup).unwrap();
    let rebuilt = compile_exec_replay(&setup).unwrap();
    assert_eq!(replay.identities(), rebuilt.identities());
    drop(rebuilt);
    // A caller cannot apply the old formula to a packed registry, even if
    // it supplies ample coefficient budgets. No missing-table fallback.
    assert!(
      crate::compile_exec_blake3_root_maps(
        &replay,
        LIMITS.linear_program,
        LIMITS.linear_validation
      )
      .is_err()
    );
    let closure = compile_exec_root_closure(&replay, LIMITS).unwrap();
    let again = compile_exec_root_closure(&replay, LIMITS).unwrap();
    assert_eq!(closure.digest(), again.digest());
    assert_eq!(closure.tables(), again.tables());
    assert_eq!(closure.tables().matrices().len(), 64);
    assert!(
      closure
        .tables()
        .matrices()
        .iter()
        .all(|(_, p)| matches!(p, Program::DecisionDiagram(_)))
    );
    assert!(matches!(
      closure.tables().structure().1,
      Program::CofactorBasis(_)
    ));
    assert!(matches!(closure.tables().jagged().1, Program::DecisionDiagram(_)));
    let slots = closure.setup_source_slots().unwrap();
    eprintln!(
      "packed {name}: setup {:?}; implementation {:?}; replay {:?}; closure {:?}; tables {:?}; nu={}, virtual_m={}, dense_m={}, dense_words={}, live_lanes={}; slots {slots:?}; source_bytes={}; {:.3}s; {}",
      setup.identities().digest(),
      setup.identities().implementation,
      replay.identities().digest(),
      closure.digest(),
      closure.tables().digest(),
      union.n_log(),
      union.m_total(),
      params.m,
      union.dense_words(),
      params.num_ntts(),
      slots.payload_bytes().unwrap(),
      started.elapsed().as_secs_f64(),
      memory_summary()
    );
    eprintln!(
      "packed {name} replay: Boolean {:?}; wiring {:?}; PCS {:?}; inner {:?}; matrix fold {:?}; structure fold {:?}; jagged fold {:?}",
      replay.boolean.trace.census(),
      replay.wiring.census(),
      replay.pcs.frontend.census(),
      replay.main.inner.census(),
      replay.folds.matrices.census(),
      replay.folds.structure.census(),
      replay.folds.jagged.census()
    );
  }
}

#[test]
#[ignore = "real packed small-class Exec proofs, complete replay, all 66 roots and setup/assigned prefix; not FFLONK proving"]
fn packed_small_exec_replay_and_all_closed_roots_match_native() {
  let setup = setup(SMALL);
  let replay = compile_exec_replay(&setup).unwrap();
  let closure = compile_exec_root_closure(&replay, LIMITS).unwrap();
  let slots = closure.setup_source_slots().unwrap();
  let prefix = captured_prefix(true, |b| {
    closure.emit_setup(b, slots.payload_bytes().unwrap())
  });
  let identity = closure.digest();
  for (literal, value) in [(false, false), (false, true), (true, false)] {
    let started = Instant::now();
    let mut code = program(false);
    let result = if literal {
      code.truncate(code.len() - 6);
      code.extend([1, 1, 0, 1]);
      true
    } else {
      value
    };
    let input = input(value);
    let output = output(result);
    let expected = expected_statement(setup.profile(), &code, &input, &output);
    let program = hash(1, &setup.identities().profile, &code);
    let commitments = ExecCommitmentsV0 {
      program,
      input: hash(2, &program, &input),
      output: hash(3, &program, &output),
    };
    assert_eq!(
      commitments.statement_digest(setup.identities().profile),
      expected.0
    );
    let bytes = setup.prove(expected, &code, &input).unwrap();
    let witness = replay.replay(commitments, &bytes).unwrap();
    assert_eq!(closure.digest(), identity);
    let public = Stage4PublicInputsV1::from_statement_digest(
      commitments.public_digest(setup.identities().profile),
    );
    assert_eq!(
      captured_prefix(false, |b| closure
        .constrain(b, public, &witness)
        .map(|_| ())),
      prefix
    );
    let roots = witness.matrix_accumulator();
    assert_eq!(roots.root_claims().len(), 64);
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
    for field in 0..3 {
      let mut wrong = commitments;
      [&mut wrong.program, &mut wrong.input, &mut wrong.output][field][0] ^= 1;
      assert!(replay.replay(wrong, &bytes).is_err());
    }
    let mut wrong = bytes.clone();
    let last = wrong.len() - 1;
    wrong[last] ^= 1;
    assert!(replay.replay(commitments, &wrong).is_err());
    eprintln!(
      "packed small Exec literal={literal} input={value} output={result}: {} bundle bytes; all 66 roots and exact 4096-row setup prefix match; {:.3}s; {}",
      bytes.len(),
      started.elapsed().as_secs_f64(),
      memory_summary()
    );
  }
}

#[test]
#[ignore = "WHOLE packed small-class proof-free closed census with hard 2^30 cutoff; no key or proof"]
fn packed_small_exec_whole_root_closed_admission_census() {
  let setup = setup(SMALL);
  let replay = compile_exec_replay(&setup).unwrap();
  let closure = compile_exec_root_closure(&replay, LIMITS).unwrap();
  let slots = closure.setup_source_slots().unwrap();
  let payload = slots.payload_bytes().unwrap();
  assert!(payload <= 32_000_000);
  let started = Instant::now();
  eprintln!(
    "starting WHOLE packed small-class census: setup {:?}; composition {:?}; tables {:?}; slots {slots:?}; payload {payload}; {}",
    setup.identities().digest(),
    closure.digest(),
    closure.tables().digest(),
    memory_summary()
  );
  let result = census_exec_root_closed_setup_observed(
    &closure,
    payload,
    ExecRootClosedCensusLimitsV0 {
      required_domain_rows: ix_fflonk::FFLONK_MAX_BASE_DOMAIN,
    },
    move |prefix| {
      eprintln!(
        "packed small-class whole prefix {:.3}s: {prefix:?}; {}",
        started.elapsed().as_secs_f64(),
        memory_summary()
      )
    },
  )
  .unwrap();
  eprintln!(
    "packed small-class WHOLE closed admission: {result:#?}; {:.3}s; {}",
    started.elapsed().as_secs_f64(),
    memory_summary()
  );
  match result {
    ExecRootClosedCensusOutcomeV0::Complete(census) => {
      assert_eq!(census.public_scalar_bytes, 64);
      assert_eq!(census.r1cs.census().constraints_by_phase.len(), 7);
      let capacity = ix_fflonk::plan_fflonk_capacity(&census.plonk).unwrap();
      assert!(capacity.supported_polynomial_fft_domain);
      eprintln!(
        "packed small-class PAYLOAD MINIMA, not RSS/prover admission: {capacity:#?}"
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
