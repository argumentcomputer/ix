//! Complete direct-original-claim composition tests. Prefix comparisons,
//! native proofs and WHOLE censuses are separately labelled; none is a
//! terminal FFLONK proof or evidence of whole-pipeline resource admission.

use super::{
  capacity_tests::SMALL,
  closure_tests::{LIMITS, captured_prefix},
  hash, input, memory_summary, output, program,
};
use crate::{
  CompiledExecReplay, ExecOriginalClosureArithmeticV0,
  ExecOriginalClosureLimitsV0, ExecRootClosedCensusLimitsV0,
  ExecRootClosedCensusOutcomeV0, ExecSetupR1csLimitsV0,
  census_exec_original_claims_observed,
  census_exec_original_claims_setup_observed,
  compile_exec_original_claims_closure,
  compile_exec_original_claims_closure_with_arithmetic, compile_exec_replay,
};
use ix_stage4_trace::{
  ExecCommitmentsV0, F128JaggedDirectLimitsV0, F128StructuredMatricesLimitsV0,
};
use ix_terminal_circuit::{
  ExecOriginalClaimsWitnessV0, R1csBuilder, R1csError, R1csShapeLimitsV0,
  Stage4PublicInputsV1, Stage4TraceWitnessV1, Stage4TranscriptWitnessV1,
  constrain_exec_original_claims_closed, validate_exec_original_claim_tables,
};
use ixby_flock::{
  blake3_backend::Blake3Backend,
  ixby::{
    decode::PrimitiveSet,
    exec::{
      CompiledExec, SemanticProfile, compile_exec_profile_with_backend,
      expected_statement,
    },
  },
};
use std::time::Instant;

const DIRECT_LIMITS: ExecOriginalClosureLimitsV0 =
  ExecOriginalClosureLimitsV0 {
    matrices: F128StructuredMatricesLimitsV0 {
      tables: 64,
      source_entries: 2_000_000,
      blocks: 100_000,
      coefficient_terms: 2_000_000,
      shared_nodes: 1_000_000,
      temporary_nodes: 1_000_000,
    },
    source_tables: LIMITS.diagrams,
    structure: LIMITS.structure_basis,
    jagged: F128JaggedDirectLimitsV0 {
      runs: 100_000,
      combo_terms: 100_000,
      row_nodes: 1_000_000,
      equality_nodes: 1_000_000,
    },
  };
fn setup() -> CompiledExec {
  compile_exec_profile_with_backend(
    SemanticProfile::scalar(SMALL).unwrap(),
    SMALL,
    PrimitiveSet::scalar(),
    Blake3Backend::PackedWordsV0,
  )
  .unwrap()
}

fn prove(
  setup: &CompiledExec,
  literal: bool,
  value: bool,
) -> (ExecCommitmentsV0, Stage4PublicInputsV1, Vec<u8>) {
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
  let public = Stage4PublicInputsV1::from_statement_digest(
    commitments.public_digest(setup.identities().profile),
  );
  (commitments, public, setup.prove(expected, &code, &input).unwrap())
}

// Each mutation must fail the table preflight BEFORE even the two public
// variables or transcript sources are allocated. Empty values are deliberate:
// the failure must occur before a missing source could explain rejection.
fn preflight_negatives(
  replay: &CompiledExecReplay<'_>,
  tables: &ix_stage4_trace::F128OriginalClaimTablesV0,
) {
  validate_exec_original_claim_tables(
    tables,
    replay.binding(),
    &replay.boolean.trace,
    &replay.wiring,
    &replay.pcs.multipoint,
  )
  .unwrap();
  let empty = R1csBuilder::new_projection().finish_projection().unwrap();
  for case in 0..16 {
    let mut binding = replay.binding().clone();
    let mut algebra = replay.boolean.trace.clone();
    let mut wiring = replay.wiring.clone();
    let mut multipoint = replay.pcs.multipoint.clone();
    match case {
      0 => binding.registry_digest[0] ^= 1,
      1 => binding.circuit_digest[0] ^= 1,
      2 => {
        algebra.deferred_matrix_claims.pop();
      },
      3 => algebra
        .deferred_matrix_claims
        .push(algebra.deferred_matrix_claims[0].clone()),
      4 => algebra.deferred_matrix_claims.swap(0, 2),
      5 => algebra.deferred_matrix_claims[0].matrix.registry_digest[0] ^= 1,
      6 => {
        algebra.deferred_matrix_claims[0].row.low.pop();
      },
      7 => {
        algebra.deferred_matrix_claims[0].column.point.pop();
      },
      8 => {
        algebra.deferred_matrix_claims[1].row.low[0] =
          ix_stage4_trace::F128ReferenceV1::Input(
            ix_stage4_trace::F128InputSourceV1::Constant([9; 16]),
          )
      },
      9 => wiring.circuit_digest[0] ^= 1,
      10 => wiring.structure_base_variables = u32::MAX,
      11 => wiring.row_variables += 1,
      12 => multipoint.matrix.circuit_digest[0] ^= 1,
      13 => {
        multipoint.group_column_addresses.pop();
      },
      14 => multipoint.group_column_addresses.swap(0, 1),
      15 => multipoint.matrix.row_variables += 1,
      _ => unreachable!(),
    }
    let mut builder = R1csBuilder::new_projection();
    assert!(
      constrain_exec_original_claims_closed(
        &mut builder,
        Stage4PublicInputsV1::from_statement_digest([0; 32]),
        tables,
        ExecOriginalClaimsWitnessV0 {
          statement_binding: &binding,
          commitments: ExecCommitmentsV0 {
            program: [0; 32],
            input: [0; 32],
            output: [0; 32]
          },
          transcript: Stage4TranscriptWitnessV1 {
            trace: replay.main.hash.setup_topology(),
            observed_values: &[],
            challenges: &[],
            byte_payloads: &[]
          },
          algebra: Stage4TraceWitnessV1 {
            trace: &algebra,
            private_values: &[]
          },
          wiring: Stage4TraceWitnessV1 { trace: &wiring, private_values: &[] },
          merged_pcs: &replay.pcs.frontend,
          multipoint: Stage4TraceWitnessV1 {
            trace: &multipoint,
            private_values: &[]
          },
          inner_ligerito: Stage4TraceWitnessV1 {
            trace: &replay.main.inner,
            private_values: &[]
          },
          inner_ligerito_private_digests: &[],
        }
      )
      .is_err(),
      "preflight mutation {case}"
    );
    assert_eq!(
      builder.finish_projection().unwrap(),
      empty,
      "preflight mutation {case} emitted constraints"
    );
  }
}

#[test]
#[ignore = "bounded proof-free ownership, malformed preflights and 3 actual native Exec replay prefixes; not whole census or terminal proof"]
fn packed_small_original_claim_closure_is_owned_and_matches_native_prefixes() {
  let setup = setup();
  let replay = compile_exec_replay(&setup).unwrap();
  let closure =
    compile_exec_original_claims_closure(&replay, DIRECT_LIMITS).unwrap();
  let rebuilt =
    compile_exec_original_claims_closure(&replay, DIRECT_LIMITS).unwrap();
  assert_eq!(closure.digest(), rebuilt.digest());
  assert_eq!(closure.tables(), rebuilt.tables());
  assert!(std::ptr::eq(closure.replay_setup(), &replay));
  drop(rebuilt);
  preflight_negatives(&replay, closure.tables());
  for family in 0..4 {
    let mut limits = DIRECT_LIMITS;
    match family {
      0 => limits.matrices.tables = 63,
      1 => limits.source_tables.entries = 0,
      2 => limits.structure.state_slots = 0,
      3 => limits.jagged.combo_terms = 0,
      _ => unreachable!(),
    }
    assert!(compile_exec_original_claims_closure(&replay, limits).is_err());
  }
  let slots = closure.setup_source_slots().unwrap();
  let bytes = slots.payload_bytes().unwrap();
  assert!(bytes > 0);
  let legacy = crate::compile_exec_root_closure(&replay, LIMITS).unwrap();
  assert!(
    legacy.setup_source_slots().unwrap().payload_bytes().unwrap() > bytes
  );
  assert_ne!(closure.digest(), legacy.digest());
  let prefix =
    captured_prefix(true, |builder| closure.emit_setup(builder, bytes));
  // The extracted common main emitter retains EXACT original row order.
  assert_eq!(
    prefix,
    captured_prefix(true, |builder| legacy.emit_setup(
      builder,
      legacy.setup_source_slots().unwrap().payload_bytes().unwrap()
    ))
  );
  let limits = ExecSetupR1csLimitsV0 {
    source_payload_bytes: bytes - 1,
    r1cs: R1csShapeLimitsV0 {
      variables: 100_000,
      constraints: 1000,
      nonzero_terms: 1_000_000,
    },
  };
  let err = closure.build_setup_r1cs(limits).unwrap_err();
  assert!(matches!(
    err.downcast_ref::<R1csError>(),
    Some(R1csError::ResourceLimit {
      resource: "Exec setup source-slot payload bytes",
      ..
    })
  ));
  let err = closure
    .build_setup_r1cs(ExecSetupR1csLimitsV0 {
      source_payload_bytes: bytes,
      ..limits
    })
    .unwrap_err();
  assert!(matches!(
    err.downcast_ref::<R1csError>(),
    Some(R1csError::ResourceLimit {
      resource: "R1CS constraints",
      actual: 1001,
      ..
    })
  ));
  let mut wrong_mode = R1csBuilder::new_projection();
  assert!(closure.emit_setup(&mut wrong_mode, bytes).is_err());
  assert_eq!(
    wrong_mode.finish_projection().unwrap(),
    R1csBuilder::new_projection().finish_projection().unwrap()
  );
  let caps = [0, 4, 1000].map(|cap| {
    census_exec_original_claims_setup_observed(
      &closure,
      bytes,
      ExecRootClosedCensusLimitsV0 { required_domain_rows: cap },
      |_| {},
    )
    .unwrap()
  });
  for (literal, value) in [(false, false), (false, true), (true, false)] {
    let (commitments, public, proof) = prove(&setup, literal, value);
    let witness = replay.replay(commitments, &proof).unwrap();
    assert_eq!(
      captured_prefix(false, |builder| closure
        .constrain(builder, public, &witness)
        .map(|_| ())),
      prefix
    );
    for (cap, expected) in [0, 4, 1000].into_iter().zip(&caps) {
      assert_eq!(
        &census_exec_original_claims_observed(
          &closure,
          public,
          &witness,
          ExecRootClosedCensusLimitsV0 { required_domain_rows: cap },
          |_| {}
        )
        .unwrap(),
        expected
      );
    }
    eprintln!(
      "native direct composition literal={literal} value={value}: {} proof bytes, matching bounded setup/native prefixes; {}",
      proof.len(),
      memory_summary()
    );
  }
  eprintln!(
    "direct original claims ownership/preflight/native PREFIX tests PASS, composition={}, tables={}, source_slots={slots:?}, source_bytes={bytes}. NOT a complete census, terminal key, or proof.",
    blake3::Hash::from(closure.digest()),
    blake3::Hash::from(closure.tables().digest())
  );
}

#[test]
#[ignore = "bounded WHOLE original-claim-closed setup census, followed by whole native replay census ONLY if setup fits the supported domain; not R1CS materialization, key or proof"]
fn packed_small_whole_original_claims_closed_census() {
  whole_census(ExecOriginalClosureArithmeticV0::UncachedV0);
}

#[test]
#[ignore = "bounded WHOLE prepared-F128 original-claim-closed setup census, followed by whole native replay census ONLY if setup fits; not materialization, key or proof"]
fn packed_small_whole_prepared_original_claims_closed_census() {
  whole_census(ExecOriginalClosureArithmeticV0::PreparedF128Fifo1024V0);
}

#[test]
#[ignore = "bounded WHOLE prepared/ranged-F128 closed setup census, followed by whole native replay census ONLY if setup fits; not materialization, key or proof"]
fn packed_small_whole_ranged_original_claims_closed_census() {
  whole_census(ExecOriginalClosureArithmeticV0::PreparedRangedF128Fifo1024V1);
}

fn whole_census(arithmetic: ExecOriginalClosureArithmeticV0) {
  let started = Instant::now();
  let setup = setup();
  let replay = compile_exec_replay(&setup).unwrap();
  let closure = compile_exec_original_claims_closure_with_arithmetic(
    &replay,
    DIRECT_LIMITS,
    arithmetic,
  )
  .unwrap();
  let slots = closure.setup_source_slots().unwrap();
  let limits = ExecRootClosedCensusLimitsV0 {
    required_domain_rows: ix_fflonk::FFLONK_MAX_BASE_DOMAIN,
  };
  let config = setup.pcs_params().ligerito_verifier_config().unwrap();
  assert_eq!(config.queries, [244, 79, 48]);
  assert_eq!(config.grinding_bits, [16, 16, 16]);
  eprintln!(
    "WHOLE direct original-claim closed census: arithmetic={arithmetic:?}, composition={}, tables={}, matrices={}, structure=3 jagged=3; source_slots={slots:?}, bytes={}; pinned queries {:?}, grinding {:?}; {}",
    blake3::Hash::from(closure.digest()),
    blake3::Hash::from(closure.tables().digest()),
    closure.tables().matrices().outputs().len(),
    slots.payload_bytes().unwrap(),
    config.queries,
    config.grinding_bits,
    memory_summary()
  );
  let outcome = census_exec_original_claims_setup_observed(
    &closure,
    slots.payload_bytes().unwrap(),
    limits,
    move |p| {
      eprintln!(
        "whole direct setup {:?}: {} R1CS, {} PLONK; {:.2}s; {}",
        p.last_phase,
        p.plonk.r1cs_constraints,
        p.plonk.constraint_rows,
        started.elapsed().as_secs_f64(),
        memory_summary()
      );
    },
  )
  .unwrap();
  match outcome {
    ExecRootClosedCensusOutcomeV0::Complete(expected) => {
      eprintln!(
        "COMPLETE WHOLE direct SETUP census: {expected:?}; {:.3}s; {}. No complete witness, key, or proof.",
        started.elapsed().as_secs_f64(),
        memory_summary()
      );
      let (commitments, public, proof) = prove(&setup, false, true);
      let witness = replay.replay(commitments, &proof).unwrap();
      let assigned_started = Instant::now();
      let actual = census_exec_original_claims_observed(
        &closure,
        public,
        &witness,
        limits,
        move |p| {
          eprintln!(
            "whole direct assigned {:?}: {} R1CS, {} PLONK; {:.2}s; {}",
            p.last_phase,
            p.plonk.r1cs_constraints,
            p.plonk.constraint_rows,
            assigned_started.elapsed().as_secs_f64(),
            memory_summary()
          );
        },
      )
      .unwrap();
      let ExecRootClosedCensusOutcomeV0::Complete(actual) = actual else {
        panic!("whole assigned census diverged from complete setup: {actual:?}")
      };
      assert_eq!(actual, expected);
      eprintln!(
        "COMPLETE WHOLE direct SETUP==ASSIGNED R1CS/PLONK census; {:.3}s total; {}. No materialized complete witness, terminal key or proof.",
        started.elapsed().as_secs_f64(),
        memory_summary()
      );
    },
    ExecRootClosedCensusOutcomeV0::RejectedBudget {
      prefix,
      limit,
      required_rows,
    } => {
      assert!(required_rows > limit);
      assert_eq!(limit, ix_fflonk::FFLONK_MAX_BASE_DOMAIN);
      eprintln!(
        "REFUSED WHOLE direct closed SETUP at {prefix:?}; required_rows={required_rows} > limit={limit}; {:.3}s; {}. This is an incomplete prefix, NO full circuit size/digest/domain/key/proof.",
        started.elapsed().as_secs_f64(),
        memory_summary()
      );
    },
  }
}

#[test]
#[ignore = "bounded prepared-F128 setup ownership and actual native Exec replay prefixes; not whole census, terminal key or proof"]
fn packed_small_prepared_original_closure_owns_arithmetic_for_both_emitters() {
  owns_arithmetic(ExecOriginalClosureArithmeticV0::PreparedF128Fifo1024V0);
}

#[test]
#[ignore = "bounded ranged-F128 setup ownership and actual native Exec replay prefixes; not whole census, terminal key or proof"]
fn packed_small_ranged_original_closure_owns_arithmetic_for_both_emitters() {
  owns_arithmetic(
    ExecOriginalClosureArithmeticV0::PreparedRangedF128Fifo1024V1,
  );
}

fn owns_arithmetic(arithmetic: ExecOriginalClosureArithmeticV0) {
  let setup = setup();
  let replay = compile_exec_replay(&setup).unwrap();
  let plain =
    compile_exec_original_claims_closure(&replay, DIRECT_LIMITS).unwrap();
  let prepared = compile_exec_original_claims_closure_with_arithmetic(
    &replay,
    DIRECT_LIMITS,
    arithmetic,
  )
  .unwrap();
  assert_eq!(plain.arithmetic(), ExecOriginalClosureArithmeticV0::UncachedV0);
  assert_ne!(plain.digest(), prepared.digest());
  assert_eq!(prepared.arithmetic(), arithmetic);
  assert_eq!(plain.tables(), prepared.tables());
  assert_eq!(
    plain.setup_source_slots().unwrap(),
    prepared.setup_source_slots().unwrap()
  );
  let bytes = prepared.setup_source_slots().unwrap().payload_bytes().unwrap();
  let prefix = captured_prefix(true, |builder| {
    let result = prepared.emit_setup(builder, bytes);
    assert_eq!(builder.f128_preparation_cache_capacity(), Some(1024));
    assert_eq!(
      builder.f128_prepared_product_encoding(),
      Some(match arithmetic {
        ExecOriginalClosureArithmeticV0::PreparedF128Fifo1024V0 =>
          ix_terminal_circuit::F128PreparedProductV1::BooleanCarriesV0,
        ExecOriginalClosureArithmeticV0::PreparedRangedF128Fifo1024V1 =>
          ix_terminal_circuit::F128PreparedProductV1::PolynomialCarriesV1,
        ExecOriginalClosureArithmeticV0::UncachedV0 =>
          panic!("this test selects cached arithmetic"),
      })
    );
    result
  });
  let empty = R1csBuilder::new_shape_projection().finish_projection().unwrap();
  for capacity in [1, 1024] {
    for encoding in [
      ix_terminal_circuit::F128PreparedProductV1::BooleanCarriesV0,
      ix_terminal_circuit::F128PreparedProductV1::PolynomialCarriesV1,
    ] {
      for closure in [&plain, &prepared] {
        let mut builder = R1csBuilder::new_shape_projection();
        builder
          .enable_f128_preparation_cache_with_product(capacity, encoding)
          .unwrap();
        assert!(closure.emit_setup(&mut builder, bytes).is_err());
        assert_eq!(builder.finish_projection().unwrap(), empty);
      }
    }
  }
  let mut builder = R1csBuilder::new_shape_projection();
  assert!(prepared.emit_setup(&mut builder, bytes - 1).is_err());
  assert_eq!(builder.f128_preparation_cache_capacity(), None);
  assert_eq!(builder.finish_projection().unwrap(), empty);
  let caps = [4, 1000].map(|cap| {
    census_exec_original_claims_setup_observed(
      &prepared,
      bytes,
      ExecRootClosedCensusLimitsV0 { required_domain_rows: cap },
      |_| {},
    )
    .unwrap()
  });
  for (literal, value) in [(false, false), (false, true), (true, false)] {
    let (commitments, public, proof) = prove(&setup, literal, value);
    let witness = replay.replay(commitments, &proof).unwrap();
    // Preconfigured arithmetic is also rejected by the assigned emitter,
    // before any constraint or allocation, for both available encodings.
    for encoding in [
      ix_terminal_circuit::F128PreparedProductV1::BooleanCarriesV0,
      ix_terminal_circuit::F128PreparedProductV1::PolynomialCarriesV1,
    ] {
      for closure in [&plain, &prepared] {
        let mut builder = R1csBuilder::new_projection();
        builder
          .enable_f128_preparation_cache_with_product(1024, encoding)
          .unwrap();
        assert!(closure.constrain(&mut builder, public, &witness).is_err());
        assert_eq!(builder.finish_projection().unwrap(), empty);
      }
    }
    assert_eq!(
      captured_prefix(false, |builder| {
        let result = prepared.constrain(builder, public, &witness).map(|_| ());
        assert_eq!(builder.f128_preparation_cache_capacity(), Some(1024));
        result
      }),
      prefix,
    );
    for (cap, expected) in [4, 1000].into_iter().zip(&caps) {
      assert_eq!(
        &census_exec_original_claims_observed(
          &prepared,
          public,
          &witness,
          ExecRootClosedCensusLimitsV0 { required_domain_rows: cap },
          |_| {},
        )
        .unwrap(),
        expected,
      );
    }
  }
  eprintln!(
    "{arithmetic:?} ownership, rejected ambient cache selection, and 3 native/setup PREFIX comparisons PASS; composition={}; tables={}; not complete census/key/proof",
    blake3::Hash::from(prepared.digest()),
    blake3::Hash::from(prepared.tables().digest()),
  );
}

#[test]
#[ignore = "actual approved setup and native proof with false/prefix-census and resource preflights; no whole materialization or Stage 4 proof"]
fn packed_small_streamed_materialization_rejects_false_census_and_limits() {
  use crate::{
    ExecRootClosedCensusV0, check_exec_original_claims_streamed_observed,
    materialize_exec_original_claims_setup_observed,
  };
  use ark_ff::AdditiveGroup;
  use ix_fflonk::{PlonkGateProjectionV1, plan_plonk_stream_memory};
  let setup = setup();
  let replay = compile_exec_replay(&setup).unwrap();
  let closure = compile_exec_original_claims_closure_with_arithmetic(
    &replay,
    DIRECT_LIMITS,
    ExecOriginalClosureArithmeticV0::PreparedRangedF128Fifo1024V1,
  )
  .unwrap();
  // A caller can write composition metadata around another complete census,
  // but cannot make it match the actual closed relation's streamed matrices.
  let projection = PlonkGateProjectionV1::new();
  let mut builder =
    R1csBuilder::new_shape_projection_observed(projection.observer());
  builder.alloc_public(ark_bls12_381::Fr::ZERO).unwrap();
  builder.alloc_public(ark_bls12_381::Fr::ZERO).unwrap();
  let r1cs = builder.finish_projection().unwrap();
  let plonk = projection.finish(&r1cs).unwrap();
  let fake = ExecRootClosedCensusV0 {
    composition_digest: closure.digest(),
    r1cs,
    plonk,
    public_scalar_bytes: 64,
  };
  let source = closure.setup_source_slots().unwrap().payload_bytes().unwrap();
  let bytes = plan_plonk_stream_memory(fake.r1cs.variables(), &fake.plonk)
    .unwrap()
    .peak_payload_bytes;
  for (source_limit, plonk_limit) in
    [(source - 1, bytes), (source, bytes - 1), (source, bytes)]
  {
    let result = materialize_exec_original_claims_setup_observed(
      &closure,
      &fake,
      source_limit,
      plonk_limit,
      |_| panic!("no row may escape these preflights"),
    );
    assert!(result.is_err());
    if source_limit == source && plonk_limit == bytes {
      assert_eq!(
        result.unwrap_err().downcast_ref::<R1csError>(),
        Some(&R1csError::StreamMismatch)
      );
    }
  }
  for change in 0..3 {
    let mut bad = fake.clone();
    match change {
      0 => bad.composition_digest[0] ^= 1,
      1 => bad.public_scalar_bytes += 1,
      2 => bad.plonk.domain_size = 0,
      _ => unreachable!(),
    }
    assert!(
      materialize_exec_original_claims_setup_observed(
        &closure,
        &bad,
        source,
        bytes,
        |_| panic!("metadata preflight")
      )
      .is_err()
    );
  }
  let (commitments, public, proof) = prove(&setup, false, true);
  let witness = replay.replay(commitments, &proof).unwrap();
  for limit in [95, 96] {
    let result = check_exec_original_claims_streamed_observed(
      &closure,
      &fake,
      public,
      &witness,
      limit,
      |_| panic!("no checked prefix may escape"),
    );
    assert!(result.is_err());
    if limit == 96 {
      assert_eq!(
        result.unwrap_err().downcast_ref::<R1csError>(),
        Some(&R1csError::StreamMismatch)
      );
    }
  }
  eprintln!(
    "streamed closed-Exec false census, metadata/source/array bounds and checked-assignment preflights PASS; no complete materialization/key/proof"
  );
}

#[test]
#[ignore = "bounded WHOLE proof-free census then every R1CS constraint checked against the complete native-replay assignment; about 23 GiB assignment payload, no PLONK gate arena, SRS, key or Stage 4 proof"]
fn packed_small_whole_ranged_original_claims_checked_assignment() {
  use crate::check_exec_original_claims_streamed_observed;
  let started = Instant::now();
  let setup = setup();
  let replay = compile_exec_replay(&setup).unwrap();
  let closure = compile_exec_original_claims_closure_with_arithmetic(
    &replay,
    DIRECT_LIMITS,
    ExecOriginalClosureArithmeticV0::PreparedRangedF128Fifo1024V1,
  )
  .unwrap();
  let slots = closure.setup_source_slots().unwrap();
  let config = setup.pcs_params().ligerito_verifier_config().unwrap();
  assert_eq!(config.queries, [244, 79, 48]);
  assert_eq!(config.grinding_bits, [16, 16, 16]);
  assert_eq!(closure.tables().matrices().outputs().len(), 64);
  eprintln!(
    "WHOLE checked-assignment preparation: composition={}, tables={}, all 64 matrix/3 structure/3 jagged claims; pinned queries {:?}, grinding {:?}; {}",
    blake3::Hash::from(closure.digest()),
    blake3::Hash::from(closure.tables().digest()),
    config.queries,
    config.grinding_bits,
    memory_summary()
  );
  // Recompute a complete, setup-owned census in this process. No imported
  // count record or digest is treated as evidence of completed emission.
  let outcome = census_exec_original_claims_setup_observed(
    &closure,
    slots.payload_bytes().unwrap(),
    ExecRootClosedCensusLimitsV0 {
      required_domain_rows: ix_fflonk::FFLONK_MAX_BASE_DOMAIN,
    },
    move |p| {
      eprintln!(
        "checked-assignment setup {:?}: {} R1CS, {} PLONK; {:.2}s; {}",
        p.last_phase,
        p.plonk.r1cs_constraints,
        p.plonk.constraint_rows,
        started.elapsed().as_secs_f64(),
        memory_summary()
      );
    },
  )
  .unwrap();
  let ExecRootClosedCensusOutcomeV0::Complete(expected) = outcome else {
    panic!(
      "whole checked assignment requires a complete supported census: {outcome:?}"
    )
  };
  let bytes = u64::from(expected.r1cs.variables())
    .checked_mul(size_of::<ark_bls12_381::Fr>() as u64)
    .unwrap();
  // This test is a bounded witness-satisfaction job, not large-key admission.
  assert!(bytes <= 24 * (1u64 << 30));
  eprintln!(
    "COMPLETE checked-assignment SETUP census: {expected:?}; assignment payload {bytes} bytes; {:.3}s; {}. No checked witness yet.",
    started.elapsed().as_secs_f64(),
    memory_summary()
  );
  let (commitments, public, proof) = prove(&setup, false, true);
  let witness = replay.replay(commitments, &proof).unwrap();
  let checked_started = Instant::now();
  let checked = check_exec_original_claims_streamed_observed(
    &closure,
    &expected,
    public,
    &witness,
    bytes,
    move |p| {
      eprintln!(
        "whole CHECKED assignment {:?}: {} satisfied R1CS constraints; {:.2}s; {}",
        p.phase,
        p.r1cs_constraints,
        checked_started.elapsed().as_secs_f64(),
        memory_summary()
      );
    },
  )
  .unwrap();
  assert_eq!(checked.assignment().len(), expected.r1cs.variables() as usize);
  assert_eq!(checked.public_inputs(), &public.field_elements());
  eprintln!(
    "COMPLETE WHOLE CHECKED assignment: {} satisfied R1CS constraints, {} variables, {} bytes; full setup projection {}; canonical matrix identity {}; {:.3}s checking, {:.3}s total; {}. No PLONK gate arena, SRS, terminal key or Stage 4 proof.",
    expected.r1cs.census().constraints,
    checked.assignment().len(),
    bytes,
    blake3::Hash::from(expected.r1cs.digest()),
    blake3::Hash::from(checked.r1cs_digest()),
    checked_started.elapsed().as_secs_f64(),
    started.elapsed().as_secs_f64(),
    memory_summary()
  );
}
