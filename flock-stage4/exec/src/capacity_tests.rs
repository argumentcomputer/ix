//! Setup-only comparison of explicit generic machine capacity classes.
//! This does not adopt a smaller profile, relax PCS security, or estimate a
//! complete closed circuit by subtracting independent component censuses.

use super::{CAPACITY, hash, input, memory_summary, output, program};
use flock_prover::union::UnionInstance;
use ixby_flock::ixby::{
  control::ControlCapacities,
  decode::{InputCapacities, PrimitiveSet, ProgramCapacities},
  exec::{
    CompiledExec, SemanticProfile, compile_exec_profile, expected_statement,
  },
  machine::MachineCapacities,
};
use std::time::Instant;

const SMALL: MachineCapacities = MachineCapacities {
  program: ProgramCapacities {
    bytes: 64,
    functions: 1,
    blocks: 1,
    operands: 1,
  },
  control: ControlCapacities { locals: 1, continuations: 1, arguments: 1 },
  input: InputCapacities { bytes: 32, values: 1 },
  output_bytes: 32,
  steps: 4,
};

fn small_setup() -> CompiledExec {
  compile_exec_profile(
    SemanticProfile::scalar(SMALL).unwrap(),
    SMALL,
    PrimitiveSet::scalar(),
  )
  .unwrap()
}

#[test]
#[ignore = "bounded setup-only capacity comparison under pinned Fast128; no guest, proof, terminal census or key"]
fn explicit_capacity_classes_keep_pinned_security_schedule() {
  let mut identities = Vec::new();
  for (name, capacity) in [("baseline", CAPACITY), ("small", SMALL)] {
    let started = Instant::now();
    let setup = compile_exec_profile(
      SemanticProfile::scalar(capacity).unwrap(),
      capacity,
      PrimitiveSet::scalar(),
    )
    .unwrap();
    let shape = setup.verifier_shape();
    let union = UnionInstance::new(&shape.registry, shape.counts.clone());
    let params = setup.pcs_params();
    let config = params.ligerito_verifier_config().unwrap();
    // Read the configuration owned by the admitted setup. Never install a
    // smaller query schedule or a test-only configuration for this probe.
    assert_eq!(params.profile.as_str(), "fast128");
    assert_eq!(params.m, union.dense_m());
    assert_eq!(params.log_batch_size, config.initial_k);
    let replay = crate::compile_exec_replay(&setup).unwrap();
    let rebuilt = crate::compile_exec_replay(&setup).unwrap();
    assert_eq!(replay.identities(), rebuilt.identities());
    drop(rebuilt);
    eprintln!(
      "capacity {name}: {capacity:?}; setup {:?}; replay {:?}; {:.3}s; nu {}; dense words {}; committed words {}; m {}; live lanes {}; queries {:?}; query grinding {:?}; {}",
      setup.identities().digest(),
      replay.identities().digest(),
      started.elapsed().as_secs_f64(),
      union.n_log(),
      union.dense_words(),
      union.committed_words(),
      params.m,
      params.num_ntts(),
      config.queries,
      config.grinding_bits,
      memory_summary(),
    );
    eprintln!(
      "capacity {name}: Boolean {:?}; wiring {:?}; PCS {:?}; inner {:?}; matrix fold {:?}; structure fold {:?}; jagged fold {:?}",
      replay.boolean.trace.census(),
      replay.wiring.census(),
      replay.pcs.frontend.census(),
      replay.main.inner.census(),
      replay.folds.matrices.census(),
      replay.folds.structure.census(),
      replay.folds.jagged.census(),
    );
    for (slot, ty) in shape.registry.boolean_types().iter().enumerate() {
      let a: usize = ty.a_0.rows.iter().map(Vec::len).sum();
      let b: usize = ty.b_0.rows.iter().map(Vec::len).sum();
      eprintln!(
        "capacity {name} Boolean slot {slot}: k_log {}; useful bits {}; count {}; A nonzeros {a}; B nonzeros {b}",
        ty.k_log, ty.useful_bits, shape.counts[slot],
      );
    }
    identities.push(setup.identities());
  }
  // Capacity changes are explicit setup/profile upgrades, not an ordinary
  // guest update. Primitive semantics remain the same in this diagnostic.
  assert_ne!(identities[0].profile, identities[1].profile);
  assert_ne!(identities[0].capacity, identities[1].capacity);
  assert_ne!(identities[0].digest(), identities[1].digest());
  assert_eq!(identities[0].primitives, identities[1].primitives);
  assert_eq!(identities[0].implementation, identities[1].implementation);
}

#[test]
#[ignore = "real small-class Exec proofs and all native root differentials; not a full terminal census or proof"]
fn small_capacity_guests_match_complete_setup_owned_replay() {
  use super::closure_tests::{LIMITS, captured_prefix, decode, evaluate};
  use ix_stage4_trace::ExecCommitmentsV0;
  use ix_terminal_circuit::Stage4PublicInputsV1;

  let setup = small_setup();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let closure = crate::compile_exec_root_closure(&replay, LIMITS).unwrap();
  let rebuilt = small_setup();
  assert_eq!(setup.identities(), rebuilt.identities());
  drop(rebuilt);
  let identity = closure.digest();
  let slots = closure.setup_source_slots().unwrap();
  let prefix = captured_prefix(true, |builder| {
    closure.emit_setup(builder, slots.payload_bytes().unwrap())
  });
  eprintln!(
    "small-class native setup: composition {identity:?}; tables {:?}; slots {slots:?}; {}",
    closure.tables().digest(),
    memory_summary(),
  );
  // Local return with two different inputs, then a DIFFERENT image returning
  // a literal. The generic setup was built before any guest existed.
  for (literal, value) in [(false, false), (false, true), (true, false)] {
    let started = Instant::now();
    let mut code = program(false);
    let result = if literal {
      // Replace `ret local(0)` with canonical `ret literal(Bool.true)`.
      code.truncate(code.len() - 6);
      code.extend([1, 1, 0, 1]);
      true
    } else {
      value
    };
    assert!(code.len() <= SMALL.program.bytes);
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
      expected.0,
    );
    let bytes = setup.prove(expected, &code, &input).unwrap();
    let witness = replay.replay(commitments, &bytes).unwrap();
    assert_eq!(closure.digest(), identity);
    let public = Stage4PublicInputsV1::from_statement_digest(
      commitments.public_digest(setup.identities().profile),
    );
    assert_eq!(
      captured_prefix(false, |builder| {
        closure.constrain(builder, public, &witness).map(|_| ())
      }),
      prefix,
    );
    let roots = witness.matrix_accumulator();
    assert_eq!(roots.root_claims().len(), closure.tables().matrices().len());
    for ((id, table), root) in
      closure.tables().matrices().iter().zip(roots.root_claims())
    {
      assert_eq!(*id, root.matrix());
      assert_eq!(
        evaluate(table, root.row_point(), root.column_point()),
        decode(root.value()),
      );
    }
    let root = roots.circuit_structure_root_claim();
    assert_eq!(closure.tables().structure().0, root.matrix());
    assert_eq!(
      evaluate(
        &closure.tables().structure().1,
        root.row_point(),
        root.column_point(),
      ),
      decode(root.value()),
    );
    let root = roots.jagged_root_claim();
    assert_eq!(closure.tables().jagged().0, root.matrix());
    assert_eq!(
      evaluate(
        &closure.tables().jagged().1,
        root.row_point(),
        root.column_point(),
      ),
      decode(root.value()),
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
      "small-class native literal={literal} input={value} result={result}: bundle {} bytes; all 48 roots and exact 4096-row setup prefix match; {:.3}s; {}",
      bytes.len(),
      started.elapsed().as_secs_f64(),
      memory_summary(),
    );
  }
}

#[test]
#[ignore = "WHOLE small-class proof-free closed census with hard 2^30 cutoff; no terminal matrices, key or proof"]
fn small_capacity_complete_root_closed_admission_census() {
  use crate::{
    ExecRootClosedCensusLimitsV0, ExecRootClosedCensusOutcomeV0,
    census_exec_root_closed_setup_observed,
  };

  let setup = small_setup();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let closure =
    crate::compile_exec_root_closure(&replay, super::closure_tests::LIMITS)
      .unwrap();
  let slots = closure.setup_source_slots().unwrap();
  let payload = slots.payload_bytes().unwrap();
  assert!(payload <= 32_000_000);
  let started = Instant::now();
  eprintln!(
    "starting WHOLE small-class proof-free root-closed census: setup {:?}; composition {:?}; tables {:?}; slots {slots:?}; payload {payload}; {}",
    setup.identities().digest(),
    closure.digest(),
    closure.tables().digest(),
    memory_summary(),
  );
  let result = census_exec_root_closed_setup_observed(
    &closure,
    payload,
    ExecRootClosedCensusLimitsV0 {
      required_domain_rows: ix_fflonk::FFLONK_MAX_BASE_DOMAIN,
    },
    move |prefix| {
      eprintln!(
        "small-class root-closed prefix {:.3}s: {prefix:?}; {}",
        started.elapsed().as_secs_f64(),
        memory_summary(),
      );
    },
  )
  .unwrap();
  eprintln!(
    "small-class root-closed admission: {result:#?}; {:.3}s; {}",
    started.elapsed().as_secs_f64(),
    memory_summary(),
  );
  match result {
    ExecRootClosedCensusOutcomeV0::Complete(census) => {
      assert_eq!(census.public_scalar_bytes, 64);
      assert_eq!(census.r1cs.census().constraints_by_phase.len(), 7);
      let capacity = ix_fflonk::plan_fflonk_capacity(&census.plonk).unwrap();
      assert!(capacity.supported_polynomial_fft_domain);
      eprintln!("small-class capacity PAYLOAD MINIMA (not RSS): {capacity:#?}");
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
