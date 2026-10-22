use ix_proof_compression::foreign::KzgCircuitExt;

use ix_proof_compression::kzg::KzgConfig;
use ix_proof_compression::kzg::Scalar;
use ix_proof_compression::kzg::Srs;
use ix_proof_compression::kzg::pcs::KzgProverData;
use multi_stark::config::ProofConfig;
use multi_stark::lookup::LookupValues;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::prover::Stage1;
use multi_stark::system::System;
use multi_stark::system::SystemWitness;
use multi_stark::traits::Algebra;
use multi_stark::traits::Field;
use multi_stark::traits::Pcs;
use p3_matrix::Matrix;
use std::sync::Arc;

#[test]
fn streamed_lookup_proof_matches_dense_and_checkpoint_roundtrip() {
  let mut builder = CircuitBuilder::<Scalar>::new();
  let table =
    builder.fixed_table("small", vec![vec![Scalar::ONE], vec![Scalar::TWO]]);
  let x = builder.input("x");
  for _ in 0..30 {
    builder.lookup(table, &[x]);
  }
  let square = builder.mul(x, x);
  builder.expose_public(square);
  let circuit = builder.finish();
  let mut witness = circuit.witness();
  witness.set(x, Scalar::TWO).unwrap();
  let assignment = witness.generate().unwrap();
  let lowered =
    circuit.lower_to_multi_stark_sharded(Scalar::from_u8(93), 16).unwrap();
  let claims = lowered.claims(assignment.public_values()).unwrap();
  let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
  let config = KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(16, b"streamed-lookup-test")),
    2,
  );
  let (mut system, key) =
    System::new(config, lowered.kzg_circuit_inputs(16, 2).unwrap());
  let dense = system.prove_multiple_claims(
    &key,
    &refs,
    SystemWitness::from_stage_1(lowered.traces(&assignment).unwrap(), &system),
  );
  system.verify_multiple_claims(&refs, &dense).unwrap();
  let (consumed, key) = System::new_without_preprocessed(
    system.config.clone(),
    lowered.kzg_circuit_inputs(16, 2).unwrap(),
  );
  assert_eq!(consumed.preprocessed_commit, system.preprocessed_commit);
  assert!(consumed.circuits.iter().all(|c| c.preprocessed.is_none()));
  system = consumed;
  let mut parts = Vec::new();
  let mut logs = Vec::new();
  let mut lookups = Vec::new();
  for (trace, circuit) in
    lowered.traces(&assignment).unwrap().into_iter().zip(&mut system.circuits)
  {
    let h = trace.height();
    logs.push(h.ilog2() as usize);
    lookups.push(LookupValues::shape_only(
      h,
      &circuit.graph.lookups.iter().map(|l| l.args.len()).collect::<Vec<_>>(),
    ));
    let (_, data) = system
      .config
      .pcs()
      .commit(vec![(system.config.pcs().natural_domain_for_degree(h), trace)]);
    let mut bytes = Vec::new();
    data.write_checkpoint(&mut bytes).unwrap();
    let roundtrip = KzgProverData::read_checkpoint(bytes.as_slice()).unwrap();
    assert!(KzgProverData::read_checkpoint(&bytes[..bytes.len() - 1]).is_err());
    bytes.push(0);
    assert!(KzgProverData::read_checkpoint(bytes.as_slice()).is_err());
    parts.push(roundtrip);
    circuit.preprocessed = None;
  }
  system.config =
    system.config.with_streaming_lookups().with_streaming_quotient();
  let count = system.circuits.len();
  let (commitment, data) = KzgProverData::concatenate(parts);
  let stage = Stage1 {
    active: vec![true; count],
    active_indices: (0..count).collect(),
    log_degrees: logs,
    stage_1_trace_commit: commitment,
    stage_1_trace_data: data,
    lookups,
  };
  let streamed = system.prove_committed(&key, &refs, stage);
  system.verify_multiple_claims(&refs, &streamed).unwrap();
  assert_eq!(streamed.to_bytes().unwrap(), dense.to_bytes().unwrap());
  let mut wrong = claims;
  wrong[1][3] += Scalar::ONE;
  assert!(
    system
      .verify_multiple_claims(
        &wrong.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        &streamed
      )
      .is_err()
  );
}

#[test]
fn streamed_chunks_preserve_global_rows_and_quotient_cosets() {
  use multi_stark::expr::Expr;
  use multi_stark::lookup::Lookup;
  use multi_stark::system::CircuitInputs;
  let x = Expr::main(0);
  let next = Expr::main_next(0);
  let message = vec![x.clone(), next.clone(), Expr::preprocessed_next(0)];
  let mult = Expr::IsFirstRow + Expr::IsLastRow;
  let circuit = CircuitInputs {
    main_width: 1,
    preprocessed: Some(p3_matrix::dense::RowMajorMatrix::new_col(
      (0..1 << 17).map(|i| Scalar::from_usize(i % 97)).collect(),
    )),
    constraints: vec![
      x.clone()
        * x.clone()
        * x.clone()
        * (x.clone() * x.clone() - Expr::constant(Scalar::ONE)),
      x.clone() + next,
    ],
    lookups: vec![
      Lookup::push(mult.clone(), message.clone()),
      Lookup::pull(mult, message),
    ],
    lookup_group_size: 2,
    ..Default::default()
  };
  let empty = CircuitInputs {
    main_width: 1,
    constraints: vec![Expr::main(0)],
    ..Default::default()
  };
  let config = KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(1 << 17, b"chunk-and-coset-test")),
    4,
  );
  let (mut system, key) = System::new(config, [circuit, empty]);
  let traces = vec![
    p3_matrix::dense::RowMajorMatrix::new_col(
      (0..1 << 17)
        .map(|i| if i % 2 == 0 { Scalar::ONE } else { Scalar::NEG_ONE })
        .collect(),
    ),
    p3_matrix::dense::RowMajorMatrix::new_col(vec![Scalar::ZERO; 8]),
  ];
  let dense = system.prove_multiple_claims(
    &key,
    &[],
    SystemWitness::from_stage_1(traces.clone(), &system),
  );
  system.config =
    system.config.with_streaming_lookups().with_streaming_quotient();
  let streamed = system.prove_multiple_claims(
    &key,
    &[],
    SystemWitness::from_stage_1(traces, &system),
  );
  assert_eq!(streamed.to_bytes().unwrap(), dense.to_bytes().unwrap());
  system.verify_multiple_claims(&[], &streamed).unwrap();
}

#[test]
fn fixed_column_passes_preserve_weights_wide_constraints_and_lookup_carry() {
  use multi_stark::expr::Expr;
  use multi_stark::lookup::Lookup;
  use multi_stark::system::CircuitInputs;
  use p3_matrix::dense::RowMajorMatrix;
  let mut constraints: Vec<_> =
    (0..20).map(|i| Expr::preprocessed_next(i) - Expr::main_next(i)).collect();
  // One constraint exceeds the per-pass column budget.
  constraints.push((0..12).fold(Expr::constant(Scalar::ZERO), |sum, i| {
    sum + Expr::preprocessed(i) - Expr::main(i)
  }));
  let lookups: Vec<_> = (0..5)
    .map(|i| {
      Lookup::push(Expr::constant(Scalar::ONE), vec![Expr::preprocessed(i * 4)])
    })
    .collect();
  let values: Vec<_> =
    (0..16 * 20).map(|i| Scalar::from_usize(i % 31)).collect();
  let first = CircuitInputs {
    main_width: 20,
    preprocessed: Some(RowMajorMatrix::new(values.clone(), 20)),
    constraints: constraints.clone(),
    lookups: lookups.clone(),
    lookup_group_size: 2,
    ..Default::default()
  };
  let second = CircuitInputs {
    lookups: lookups
      .into_iter()
      .map(|l| Lookup::pull(l.multiplicity, l.args))
      .collect(),
    ..first.clone()
  };
  let config =
    KzgConfig::new(Arc::new(Srs::unsafe_dev_setup(16, b"fixed-passes")), 4);
  let (mut system, key) = System::new(config, [first, second]);
  let traces = vec![RowMajorMatrix::new(values, 20); 2];
  let dense = system.prove_multiple_claims(
    &key,
    &[],
    SystemWitness::from_stage_1(traces.clone(), &system),
  );
  system.config =
    system.config.with_streaming_lookups().with_streaming_quotient();
  let streamed = system.prove_multiple_claims(
    &key,
    &[],
    SystemWitness::from_stage_1(traces, &system),
  );
  assert_eq!(streamed.to_bytes().unwrap(), dense.to_bytes().unwrap());
  system.verify_multiple_claims(&[], &streamed).unwrap();
}
