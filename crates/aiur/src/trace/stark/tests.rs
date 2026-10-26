use super::*;
use crate::trace::tests::{activate, raw_artifact};
use crate::{Program, bytecode::CheckedProgram, trace::TraceArtifact};
use serde_json::{Value as Json, json};

fn f() -> Json {
  json!({"kind":"field"})
}
fn v(i: usize) -> Json {
  json!({"var":i})
}
fn k(x: u64) -> Json {
  json!({"const":x})
}
fn step(action: Json) -> Json {
  json!({"guard":k(1), "action":action})
}
fn writes(n: usize) -> Vec<Json> {
  (0..n).map(|i| json!({"column":i,"source":i,"guard":k(1)})).collect()
}
fn parameters() -> Parameters {
  Parameters { log_blowup: 1, num_queries: 32 }
}

#[test]
fn batch_memory_partition_and_persisted_key() {
  use multi_stark::batch::Retention;
  let (program, artifact) = fixture();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = Backend::for_batch(&plan, parameters()).unwrap();
  let record = program.execute("root", vec![3]).unwrap();
  let mut witness = backend.generate(&record, "root", &[3]).unwrap();
  let memory = witness.traces.last_mut().unwrap();
  assert_eq!(memory.width, 4);
  // Two unused but consecutive cells force a memory boundary across shards.
  memory
    .values
    .extend([0, 1, 1, 42, 0, 1, 2, 43, 0, 0, 0, 0].map(Val::from_u64));
  let retained = backend
    .prove_batch_stage_1(
      "root",
      &[3],
      &[9],
      witness.traces.clone(),
      2,
      Retention::Retain,
    )
    .unwrap();
  let proof = backend
    .prove_batch("root", &[3], &[9], witness, 2, Retention::Regenerate)
    .unwrap();
  assert_eq!(proof.proofs.len(), 2);
  assert_eq!(proof.to_bytes().unwrap(), retained.to_bytes().unwrap());
  let bytes = backend.verifying_key_bytes().unwrap();
  let key = VerifyingKey::from_bytes(&bytes).unwrap();
  assert_eq!(key.to_bytes(), bytes);
  let claim = backend.claim("root", &[3], &[9]).unwrap();
  key.verify(&[claim], &proof).unwrap();
  assert!(backend.verify_batch("root", &[3], &[8], &proof).is_err());
  let mut bad = proof.clone();
  bad.preamble.messages[1].args[2] += Val::ONE;
  assert!(backend.verify_batch("root", &[3], &[9], &bad).is_err());
  let mut bad = proof.clone();
  bad.preamble.messages.extend(proof.preamble.messages.clone());
  assert!(backend.verify_batch("root", &[3], &[9], &bad).is_err());
  let mut bad = proof.clone();
  bad.preamble.headers[1].claims = bad.preamble.headers[0].claims.clone();
  assert!(backend.verify_batch("root", &[3], &[9], &bad).is_err());
}

fn compare_generated<B: WitnessField>(
  backend: &Backend<'_, '_, B>,
  record: &Execution<B>,
  entry: &str,
  args: &[B::Element],
) {
  let trace =
    backend.plan.generate_reference(record, entry, args, true).unwrap();
  let expected = backend.witness(record, &trace).unwrap();
  let got = backend.generate(record, entry, args).unwrap();
  let stage_1 = backend.generate_stage_1(record, entry, args).unwrap();
  for (full, main) in got.traces.iter().zip(&stage_1) {
    assert_eq!(full.width, main.width);
    assert_eq!(full.values, main.values);
  }
  assert_eq!(expected.traces.len(), got.traces.len());
  for (a, b) in expected.traces.iter().zip(&got.traces) {
    assert_eq!(a.width, b.width);
    assert_eq!(a.values, b.values);
  }
  // Compare every nonzero message directly to the independent dense graph
  // evaluator, including constants, shared expressions and fixed columns.
  use multi_stark::eval::VarValues;
  for (ci, (circuit, matrix)) in
    backend.system.circuits.iter().zip(&got.traces).enumerate()
  {
    for r in 0..matrix.height() {
      let row = &matrix.values[r * matrix.width..(r + 1) * matrix.width];
      let fixed = circuit
        .preprocessed
        .as_ref()
        .map_or(&[][..], |f| &f.values[r * f.width..(r + 1) * f.width]);
      let view = VarValues {
        main: [row, row],
        preprocessed: [fixed, fixed],
        stage2: [&[], &[]],
        publics: &[],
        is_first_row: Val::ZERO,
        is_last_row: Val::ZERO,
        is_transition: Val::ONE,
      };
      let mut buf = vec![];
      circuit.graph.sweep_lookup_prefix(&view, &mut buf);
      let expected = circuit.graph.lookup_values(&buf);
      let mut emitted = vec![false; expected.len()];
      backend.lookup_plans[ci].evaluate(row, fixed, |slot, count, args| {
        assert_eq!(count, expected[slot].multiplicity);
        assert_eq!(args, &expected[slot].args[..args.len()]);
        assert!(
          expected[slot].args[args.len()..].iter().all(|v| *v == Val::ZERO)
        );
        emitted[slot] = true;
      });
      for (emitted, expected) in emitted.into_iter().zip(expected) {
        assert_eq!(emitted, expected.multiplicity != Val::ZERO);
      }
    }
  }
  let proof = backend.prove(entry, args, &record.output, got).unwrap();
  backend.verify(entry, args, &record.output, &proof).unwrap();
}

#[test]
fn fused_rows_and_lookups_match_reference_and_verify() {
  let (mut program, artifact) = fixture();
  // An unused wide type gets an empty bucket and never widens scalar rows.
  let wide: Type =
    serde_json::from_value(json!({"kind":"tuple","items":[f(),f(),f(),f()]}))
      .unwrap();
  let layout = wide.layout(&program.program.enums, &mut vec![]).unwrap();
  program.memory_layouts.insert(wide, layout);
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  let shapes = backend.statistics();
  assert_eq!(
    shapes.iter().find(|s| s.name == "<ROM:1>").unwrap().stage1_width,
    4
  );
  assert_eq!(
    shapes.iter().find(|s| s.name == "<ROM:4>").unwrap().stage1_width,
    7
  );
  for arg in [2, 3, 4] {
    let record = program.execute("root", vec![arg]).unwrap();
    compare_generated(&backend, &record, "root", &[arg]);
  }
  for unit in [false, true] {
    let (program, artifact) = identity(unit);
    let plan = TracePlan::new(&program, activate(artifact)).unwrap();
    let backend = Backend::new(&plan, parameters()).unwrap();
    let args = if unit { vec![] } else { vec![7] };
    let record = program.execute("id", args.clone()).unwrap();
    compare_generated(&backend, &record, "id", &args);
  }
}

#[test]
fn erased_rom_views_use_existing_width_buckets() {
  let (program, mut artifact) = fixture();
  for chip in &mut artifact.chips {
    for cell in &mut chip.memory {
      cell.r#type = Type::Tuple { items: vec![Type::Field; cell.values.len()] };
      assert!(!program.memory_layouts.contains_key(&cell.r#type));
    }
  }
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  let record = program.execute("root", vec![3]).unwrap();
  compare_generated(&backend, &record, "root", &[3]);
}

/// root(x) = load(store(leaf(x))); leaf(x) = fixed_square_table[x].
/// The table has three rows, so its preprocessed domain also tests padding.
fn fixture() -> (CheckedProgram, TraceArtifact) {
  let program: Program = serde_json::from_value(json!({
        "version":1,"modulus":Val::ORDER_U64,"enums":[],
        "functions":[
            {"name":"root","params":[f()],"result":f(),"registers":4,"code":[
                {"op":"call","function":1,"args":[0],"dest":[1]},
                {"op":"store","type":f(),"value":[1],"dest":2},
                {"op":"load","type":f(),"pointer":2,"dest":[3]},
                {"op":"ret","value":[3]}]},
            {"name":"leaf","params":[f()],"result":f(),"registers":2,"code":[
                {"op":"call","function":2,"args":[0],"dest":[1]},
                {"op":"ret","value":[1]}]}
        ],
        "maps":[{"name":"square","params":[f()],"result":f(),"input":0,"output":1}],
        "tables":[
            {"name":"xs","type":{"kind":"tuple","items":[f()]},"rows":[[2],[3],[4]]},
            {"name":"ys","type":f(),"rows":[[4],[9],[16]]}
        ],
        "entries":[{"name":"root","function":0,"inputs":[f()],"output":f()}]
    }))
    .unwrap();
  let artifact = raw_artifact(json!({
      "version":1,"modulus":Val::ORDER_U64,
      "functions":[
          {"name":"root","chip":"root","witnesses":4,"inputs":[0],"output":[3],
              "steps":[
                  step(json!({"op":"call","name":"leaf","args":[v(0)],"dest":[1]})),
                  step(json!({"op":"store","type":f(),"values":[v(1)],"dest":2})),
                  step(json!({"op":"load","type":f(),"address":v(2),"dest":[3]}))],
              "writes":writes(4)},
          {"name":"leaf","chip":"leaf","witnesses":2,"inputs":[0],"output":[1],
              "steps":[step(json!({"op":"call","name":"square","args":[v(0)],"dest":[1]}))],"writes":writes(2)}
      ],
      "chips":[
          {"name":"root","width":4,"inputs":[0],"output":[v(3)],"constraints":[],
              "sends":[{"channel":"leaf","args":[v(0)],"result":[1],"enable":k(1)}],
              "memory":[
                  {"type":f(),"address":v(2),"values":[v(1)],"enable":k(1)},
                  {"type":f(),"address":v(2),"values":[v(3)],"enable":k(1)}]},
          {"name":"leaf","width":2,"inputs":[0],"output":[v(1)],"constraints":[],"memory":[],
              "sends":[{"channel":"square","args":[v(0)],"result":[1],"enable":k(1)}]}
      ]
  }));
  (program.check().unwrap(), artifact)
}

#[test]
fn proves_calls_fixed_maps_and_rom_and_verifies_without_record() {
  let (program, artifact) = fixture();
  let plan = TracePlan::new(&program, activate(artifact.clone())).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  let record = program.execute("root", vec![3]).unwrap();
  let trace = plan.generate(&record, "root", &[3], true).unwrap();
  let witness = backend.witness(&record, &trace).unwrap();
  assert_eq!(witness.traces[2].height(), 4);
  assert_eq!(
    witness.traces[3].values,
    [Val::from_u64(2), Val::ONE, Val::ZERO, Val::from_u64(9)]
  );
  let proof = backend.prove("root", &[3], &[9], witness).unwrap();
  drop(trace);
  drop(record);
  drop(backend);
  let bytes = proof.to_bytes().unwrap();
  let proof = Proof::from_bytes(&bytes).unwrap();
  // Independent verifier setup reads only the trusted program/circuits/tables.
  let backend = Backend::new(&plan, parameters()).unwrap();
  backend.verify("root", &[3], &[9], &proof).unwrap();
  for (entry, args, output) in [
    ("root", vec![4], vec![9]),
    ("root", vec![3], vec![8]),
    ("missing", vec![3], vec![9]),
    ("root", vec![], vec![9]),
    ("root", vec![Val::ORDER_U64], vec![9]),
  ] {
    assert!(backend.verify(entry, &args, &output, &proof).is_err());
  }
  // A fixed-table commitment belongs to verification, not to the witness.
  let mut different = program.program().clone();
  different.tables[1].rows[1][0] = 10;
  let different = different.check().unwrap();
  let different_plan = TracePlan::new(&different, activate(artifact)).unwrap();
  let different_backend = Backend::new(&different_plan, parameters()).unwrap();
  assert!(different_backend.verify("root", &[3], &[9], &proof).is_err());
  let mut wrong_height = proof.clone();
  wrong_height.log_degrees[2] = 1;
  assert!(
    backend
      .verify("root", &[3], &[9], &wrong_height)
      .unwrap_err()
      .contains("fixed table height")
  );
  let mut inactive = proof;
  inactive.active[2] = false;
  inactive.log_degrees.remove(2);
  assert!(
    backend
      .verify("root", &[3], &[9], &inactive)
      .unwrap_err()
      .contains("inactive fixed table")
  );
}

#[test]
fn map_overrides_populate_witnesses_but_cannot_replace_certifying_tables() {
  use crate::maps::MapOverrides;
  use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
  };

  let (program, mut artifact) = fixture();
  // Retain the square result as an intermediate: population must call the
  // binding rather than simply copying the recorded function return value.
  artifact.functions[1].witnesses = 3;
  artifact.functions[1].output = vec![2];
  artifact.functions[1].steps.push(
    serde_json::from_value(step(json!({
        "op":"assign","dest":[2],"values":[v(1)]
    })))
    .unwrap(),
  );
  artifact.functions[1].writes =
    serde_json::from_value(json!(writes(3))).unwrap();
  artifact.chips[1].width = 3;
  artifact.chips[1].output = vec![Polynomial::Var(2)];
  artifact.chips[1]
    .constraints
    .push(Polynomial::Sub(Box::new([Polynomial::Var(1), Polynomial::Var(2)])));
  let plan = TracePlan::new(&program, activate(artifact.clone())).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  let original = program.execute("root", vec![3]).unwrap();
  let reference =
    plan.generate_reference(&original, "root", &[3], true).unwrap();
  for (correct, fixed) in
    [(true, false), (false, false), (true, true), (false, true)]
  {
    let calls = Arc::new(AtomicUsize::new(0));
    let captured = calls.clone();
    let mut maps = MapOverrides::new();
    let provider = move |x: u64| {
      captured.fetch_add(1, Ordering::Relaxed);
      let row = x
        .checked_sub(2)
        .filter(|&row| row < 3)
        .map(|row| row as usize)
        .ok_or_else(|| "no table entry for map input".to_owned())?;
      Ok((row, [x * x + u64::from(!correct)]))
    };
    if fixed {
      maps.insert_fixed::<1, 1>("square", move |[x]| provider(x)).unwrap();
    } else {
      maps
        .insert("square", 1, 1, move |args, out| {
          let (row, output) = provider(args[0])?;
          out.copy_from_slice(&output);
          Ok(row)
        })
        .unwrap();
    }
    let prepared =
      program.prepare_hints(&[]).unwrap().with_map_overrides(&maps).unwrap();
    // Binding checks row numbers for every immutable table input once.
    calls.store(0, Ordering::Relaxed);
    let record = prepared.execute("root", vec![3]).unwrap();
    assert_eq!(record.output, [if correct { 9 } else { 10 }]);
    assert_eq!(calls.load(Ordering::Relaxed), 1);
    drop(prepared);
    drop(maps);
    let trace = plan.generate(&record, "root", &[3], true).unwrap();
    assert_eq!(calls.load(Ordering::Relaxed), 2);
    assert_eq!(plan.check(&record, &trace, "root", &[3]).is_ok(), correct);
    if correct {
      assert_eq!(record.queries, original.queries);
      assert_eq!(trace, reference);
    }
    let witness = backend.generate(&record, "root", &[3]).unwrap();
    assert_eq!(calls.load(Ordering::Relaxed), 3);
    let proof = backend.prove("root", &[3], &record.output, witness).unwrap();
    // Construct a verifier from the program/artifact alone, with no overrides.
    let verifier_program = program.program().clone().check().unwrap();
    let verifier_plan =
      TracePlan::new(&verifier_program, activate(artifact.clone())).unwrap();
    let verifier = Backend::new(&verifier_plan, parameters()).unwrap();
    assert_eq!(
      verifier.verify("root", &[3], &record.output, &proof).is_ok(),
      correct
    );
    // A different prepared program must not donate its static map bindings.
    assert!(verifier_plan.generate(&record, "root", &[3], true).is_err());
  }
}

#[test]
fn an_accelerator_cannot_certify_a_missing_input_by_returning_a_valid_row() {
  let (program, artifact) = fixture();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  let mut maps = crate::maps::MapOverrides::<u64>::new();
  maps
    .insert_fixed::<1, 1>("square", |[x]| {
      // Correct numbering on all three table rows (2, 3, 4), so binding
      // succeeds. Deliberately aliases the missing input 5 to the row for 2.
      let row = if x == 5 { 0 } else { x as usize - 2 };
      Ok((row, [x * x]))
    })
    .unwrap();
  let record = program
    .prepare_hints(&[])
    .unwrap()
    .with_map_overrides(&maps)
    .unwrap()
    .execute("root", vec![5])
    .unwrap();
  assert_eq!(record.output, [25]);
  let trace = plan.generate(&record, "root", &[5], true).unwrap();
  assert!(plan.check(&record, &trace, "root", &[5]).is_err());
  let witness = backend.generate(&record, "root", &[5]).unwrap();
  let proof = backend.prove("root", &[5], &[25], witness).unwrap();
  assert!(backend.verify("root", &[5], &[25], &proof).is_err());
}

#[test]
fn proof_rejects_corrupt_counts_memory_and_fixed_lookup() {
  let (program, artifact) = fixture();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  let record = program.execute("root", vec![3]).unwrap();
  let trace = plan.generate(&record, "root", &[3], true).unwrap();
  let witness = backend.witness(&record, &trace).unwrap();
  let reject = |traces: Vec<RowMajorMatrix<Val>>| {
    // Recompute every lookup from the malicious main trace and actually
    // run the STARK, without relying on witness-construction diagnostics.
    let witness = SystemWitness::from_stage_1(traces, &backend.system);
    let proof = backend.prove("root", &[3], &[9], witness).unwrap();
    assert!(backend.verify("root", &[3], &[9], &proof).is_err());
  };
  let mut bad = witness.traces.clone();
  bad[0].values[5] += Val::ONE; // excess root provide count
  reject(bad);
  let mut bad = witness.traces.clone();
  bad[2].values[1] = Val::ZERO; // missing fixed square(3) provider
  reject(bad);
  let mut bad = witness.traces.clone();
  bad[3].values[3] += Val::ONE; // wrong ROM payload
  reject(bad);
  let mut bad = witness.traces.clone();
  let mut rom_row = bad[3].values.clone();
  rom_row[0] = Val::ONE;
  bad[3].values = [rom_row.clone(), rom_row.clone()].concat();
  reject(bad); // balanced value lookups, but duplicate local addresses
  let mut bad = witness.traces.clone();
  let mut padding = rom_row.clone();
  padding[1] = Val::ZERO;
  bad[3].values = [rom_row, padding].concat();
  reject(bad); // balanced lookups, but padding illegally supplies a cell
}

#[test]
fn recorded_lookup_counts_are_checked_by_the_proof() {
  let (program, artifact) = fixture();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  let record = program.execute("root", vec![3]).unwrap();
  let trace = plan.generate(&record, "root", &[3], true).unwrap();
  for corrupt_memory in [false, true] {
    let mut bad = record.clone();
    if corrupt_memory {
      *bad.memory.multiplicity_mut(0) += 1;
    } else {
      bad.queries.tables[2].bump(0).unwrap();
    }
    let witness = backend.witness(&bad, &trace).unwrap();
    let proof = backend.prove("root", &[3], &[9], witness).unwrap();
    assert!(backend.verify("root", &[3], &[9], &proof).is_err());
  }
  let mut bad = record.clone();
  // A fixed row that was never queried must still be checked before its
  // integer multiplicity is converted to a field element.
  bad.queries.tables[2].static_map.as_mut().unwrap().counts[0] = Val::ORDER_U64;
  assert!(backend.witness(&bad, &trace).is_err());
  let mut bad = record;
  *bad.memory.multiplicity_mut(0) = Val::ORDER_U64;
  assert!(backend.witness(&bad, &trace).is_err());
}

/// Interleave widths 0, 1 and 2, including different types of width 1.
/// The final scalar may share an interned cell with an earlier store.
fn mixed_memory() -> (CheckedProgram, TraceArtifact) {
  let unit = json!({"kind":"tuple","items":[]});
  let pair = json!({"kind":"tuple","items":[f(),f()]});
  let singleton = json!({"kind":"tuple","items":[f()]});
  let mut code = vec![];
  let mut steps = vec![];
  let mut memory = vec![];
  for (ty, values, pointer, dest) in [
    (f(), vec![0], 3, vec![9]),
    (pair, vec![0, 1], 4, vec![10, 11]),
    (unit, vec![], 5, vec![]),
    (singleton, vec![1], 6, vec![12]),
    (f(), vec![1], 7, vec![13]),
    (f(), vec![2], 8, vec![14]),
  ] {
    code.push(json!({"op":"store","type":ty,"value":values,"dest":pointer}));
    code.push(json!({"op":"load","type":ty,"pointer":pointer,"dest":dest}));
    let values: Vec<_> = values.into_iter().map(v).collect();
    steps.push(step(
      json!({"op":"store","type":ty,"values":values,"dest":pointer}),
    ));
    steps.push(step(
      json!({"op":"load","type":ty,"address":v(pointer),"dest":dest}),
    ));
    memory.push(
      json!({"type":ty,"address":v(pointer),"values":values,"enable":k(1)}),
    );
    let loaded: Vec<_> = dest.into_iter().map(v).collect();
    memory.push(
      json!({"type":ty,"address":v(pointer),"values":loaded,"enable":k(1)}),
    );
  }
  code.push(json!({"op":"ret","value":[14]}));
  let program: Program = serde_json::from_value(json!({
        "version":1,"modulus":Val::ORDER_U64,"enums":[],"maps":[],"tables":[],
        "functions":[{"name":"root","params":[f(),f(),f()],"result":f(),"registers":15,"code":code}],
        "entries":[{"name":"root","function":0,"inputs":[f(),f(),f()],"output":f()}]
    })).unwrap();
  let artifact = raw_artifact(json!({
      "version":1,"modulus":Val::ORDER_U64,
      "functions":[{"name":"root","chip":"root","witnesses":15,"inputs":[0,1,2],
          "output":[14],"steps":steps,"writes":writes(15)}],
      "chips":[{"name":"root","width":15,"inputs":[0,1,2],"output":[v(14)],
          "constraints":[],"sends":[],"memory":memory}]
  }));
  let mut program = program.check().unwrap();
  let unused: Type =
    serde_json::from_value(json!({"kind":"tuple","items":[f(),f(),f(),f()]}))
      .unwrap();
  program.memory_layouts.insert(
    unused.clone(),
    unused.layout(&program.program.enums, &mut vec![]).unwrap(),
  );
  (program, artifact)
}

#[test]
fn width_local_rom_shares_types_and_preserves_functionality() {
  let (program, artifact) = mixed_memory();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  let index =
    |name: &str| backend.names.iter().position(|n| n == name).unwrap();
  assert!(!backend.names.iter().any(|n| n == "<ROM:addresses>"));
  for args in [[3, 0, 7], [3, 0, 3], [3, 3, 3]] {
    let record = program.execute("root", args.to_vec()).unwrap();
    compare_generated(&backend, &record, "root", &args);
    let witness = backend.generate(&record, "root", &args).unwrap();
    let scalar = &witness.traces[index("<ROM:1>")];
    assert_eq!(witness.traces[index("<ROM:0>")].values[2], Val::ZERO);
    assert_eq!(scalar.width, 4);
    assert_eq!(witness.traces[index("<ROM:2>")].width, 5);
    assert_eq!(witness.traces[index("<ROM:2>")].values[2], Val::ZERO);
    assert_eq!(witness.traces[index("<ROM:4>")].height(), 0);
    // Field and singleton tuple stores of the same words share a row.
    let distinct = args.iter().collect::<std::collections::BTreeSet<_>>().len();
    assert_eq!(record.memory.len(), distinct + 2);
    assert_eq!(scalar.height(), distinct.next_power_of_two());
    if args == [3, 3, 3] {
      assert_eq!(scalar.values[0], Val::from_u64(8));
    }
  }

  let args = [3, 0, 7];
  let record = program.execute("root", args.to_vec()).unwrap();
  let witness = backend.generate(&record, "root", &args).unwrap();
  let reject = |traces: Vec<RowMajorMatrix<Val>>| {
    let forged = SystemWitness::from_stage_1(traces, &backend.system);
    let proof = backend.prove("root", &args, &[7], forged).unwrap();
    assert!(backend.verify("root", &args, &[7], &proof).is_err());
  };
  let scalar = index("<ROM:1>");
  let pair = index("<ROM:2>");

  // The two widths already reuse address zero. Neither can supply the
  // other's message, even when the longer payload only adds a zero suffix.
  let mut bad = witness.traces.clone();
  bad[pair].values[0] = Val::ZERO;
  bad[scalar].values[0] += Val::from_u64(2);
  reject(bad);

  // Conflicting payloads at one width-local address are forbidden even
  // when every lookup balances: redirect both the store and load together.
  let mut bad = witness.traces.clone();
  bad[0].values[6] = Val::ZERO;
  bad[0].values[7] = Val::ZERO;
  bad[scalar].values[6] = Val::ZERO;
  reject(bad);

  let mut bad = witness.traces.clone();
  bad[pair].values.clear();
  reject(bad);
  // Zero-use rows still cannot duplicate an existing local address.
  let mut bad = witness.traces.clone();
  let mut duplicate = bad[scalar].values[..4].to_vec();
  duplicate[0] = Val::ZERO;
  bad[scalar].values[12..16].copy_from_slice(&duplicate);
  reject(bad);

  // An unreachable cell in an otherwise unused width is harmless. Its
  // nominal interpretations need not be canonical until a stored pointer
  // with the appropriate type reaches it.
  let mut extra = witness.traces.clone();
  let unused = index("<ROM:4>");
  extra[unused].values = vec![Val::ZERO; 7];
  extra[unused].values[1] = Val::ONE;
  let extra = SystemWitness::from_stage_1(extra, &backend.system);
  let proof = backend.prove("root", &args, &[7], extra).unwrap();
  backend.verify("root", &args, &[7], &proof).unwrap();
}

fn identity(unit: bool) -> (CheckedProgram, TraceArtifact) {
  let ty = if unit { json!({"kind":"tuple","items":[]}) } else { f() };
  let n = usize::from(!unit);
  let program: Program = serde_json::from_value(json!({
      "version":1,"modulus":Val::ORDER_U64,"enums":[],"maps":[],"tables":[],
      "functions":[{"name":"id","params":[ty],"result":ty,"registers":n,
          "code":[{"op":"ret","value":(0..n).collect::<Vec<_>>()}]}],
      "entries":[{"name":"id","function":0,"inputs":[ty],"output":ty}]
  }))
  .unwrap();
  let artifact = raw_artifact(json!({
      "version":1,"modulus":Val::ORDER_U64,
      "functions":[{"name":"id","chip":"id","witnesses":n,"inputs":(0..n).collect::<Vec<_>>(),
          "output":(0..n).collect::<Vec<_>>(),"steps":[],"writes":writes(n)}],
      "chips":[{"name":"id","width":n,"inputs":(0..n).collect::<Vec<_>>(),
          "output":(0..n).map(v).collect::<Vec<_>>(),"constraints":[],"sends":[],"memory":[]}]
  }));
  (program.check().unwrap(), artifact)
}

#[test]
fn proves_zero_width_and_height_one_without_auxiliary_tables() {
  for unit in [true, false] {
    let (program, artifact) = identity(unit);
    let plan = TracePlan::new(&program, activate(artifact)).unwrap();
    let backend = Backend::new(&plan, parameters()).unwrap();
    let args: Vec<_> = if unit { vec![] } else { vec![7] };
    let record = program.execute("id", args.clone()).unwrap();
    let trace = plan.generate(&record, "id", &args, true).unwrap();
    let witness = backend.witness(&record, &trace).unwrap();
    assert_eq!(witness.traces[0].height(), 1);
    assert_eq!(witness.traces[0].width, if unit { 2 } else { 3 });
    let proof = backend.prove("id", &args, &args, witness).unwrap();
    backend.verify("id", &args, &args, &proof).unwrap();
  }
}

#[test]
fn zero_padding_verifies_but_inactive_providers_and_nonboolean_rows_do_not() {
  let (program, artifact) = identity(false);
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  let record = program.execute("id", vec![7]).unwrap();
  let mut trace = plan.generate(&record, "id", &[7], true).unwrap();
  let matrix = &mut trace.matrices[0];
  matrix.height = 2;
  matrix.values.extend([0, 0]);
  matrix.multiplicities.push(0);
  plan.check(&record, &trace, "id", &[7]).unwrap();
  let witness = backend.witness(&record, &trace).unwrap();
  assert_eq!(
    witness.traces[0].values,
    [Val::from_u64(7), Val::ONE, Val::ONE, Val::ZERO, Val::ZERO, Val::ZERO]
  );
  let proof = backend.prove("id", &[7], &[7], witness.clone()).unwrap();
  backend.verify("id", &[7], &[7], &proof).unwrap();

  // These forgeries keep the public lookup balance exactly correct. Only
  // the selector/count constraints prevent the inactive row from proving it.
  for rows in [[7, 1, 0, 7, 0, 1], [7, 2, 1, 0, 0, 0]] {
    let mut bad = witness.traces.clone();
    bad[0].values = rows.into_iter().map(Val::from_u64).collect();
    let forged = SystemWitness::from_stage_1(bad, &backend.system);
    let proof = backend.prove("id", &[7], &[7], forged).unwrap();
    assert!(backend.verify("id", &[7], &[7], &proof).is_err());
  }

  trace.matrices[0].multiplicities = vec![0, 1];
  trace.matrices[0].values[2] = 7;
  assert!(plan.check(&record, &trace, "id", &[7]).is_err());
  assert!(backend.witness(&record, &trace).is_err());
}

#[test]
fn checks_field_parameters_domains_and_shapes_before_proving() {
  let (program, artifact) = identity(false);
  let plan = TracePlan::new(&program, activate(artifact.clone())).unwrap();
  assert!(
    Backend::new(&plan, Parameters { log_blowup: 0, num_queries: 32 }).is_err()
  );
  assert!(
    Backend::new(&plan, Parameters { log_blowup: 1, num_queries: 0 }).is_err()
  );
  let backend = Backend::new(&plan, parameters()).unwrap();
  assert!(backend.check_shape(&[true], &[32]).is_err());
  assert!(backend.check_shape(&[true], &[]).is_err());
  assert!(backend.check_shape(&[true], &[0, 0]).is_err());
  assert!(backend.check_shape(&[false], &[]).is_err());
  let record = program.execute("id", vec![7]).unwrap();
  let mut trace = plan.generate(&record, "id", &[7], true).unwrap();
  trace.matrices[0].multiplicities[0] = Val::ORDER_U64;
  assert!(backend.witness(&record, &trace).is_err());
  let mut small = program.program().clone();
  small.modulus = 97;
  let small = small.check().unwrap();
  let mut artifact = artifact;
  artifact.modulus = 97;
  let plan = TracePlan::new(&small, activate(artifact)).unwrap();
  assert!(Backend::new(&plan, parameters()).is_err());
}

#[test]
fn arithmetic_constraints_are_enforced_even_when_lookups_balance() {
  let (program, mut artifact) = identity(false);
  let mut program = program.program().clone();
  program.functions[0].registers = 2;
  program.functions[0].code = serde_json::from_value(json!([
      {"op":"binary","operator":"mul","left":0,"right":0,"dest":1},
      {"op":"ret","value":[1]}
  ]))
  .unwrap();
  let program = program.check().unwrap();
  artifact.functions[0].witnesses = 2;
  artifact.functions[0].output = vec![1];
  artifact.functions[0].writes =
    serde_json::from_value(json!(writes(2))).unwrap();
  artifact.chips[0].width = 2;
  artifact.chips[0].output = vec![Polynomial::Var(1)];
  artifact.chips[0].constraints = serde_json::from_value(json!([
      {"sub":[v(1),{"mul":[v(0),v(0)]}]}
  ]))
  .unwrap();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  let record = program.execute("id", vec![7]).unwrap();
  let trace = plan.generate(&record, "id", &[7], true).unwrap();
  let witness = backend.witness(&record, &trace).unwrap();
  let proof = backend.prove("id", &[7], &[49], witness.clone()).unwrap();
  backend.verify("id", &[7], &[49], &proof).unwrap();
  let mut bad = witness.traces;
  bad[0].values[1] = Val::from_u64(48);
  let witness = SystemWitness::from_stage_1(bad, &backend.system);
  let proof = backend.prove("id", &[7], &[48], witness).unwrap();
  assert!(backend.verify("id", &[7], &[48], &proof).is_err());
}

#[test]
fn shares_fixed_columns_and_handles_empty_maps_and_inactive_chips() {
  let (program, mut artifact) = identity(true);
  let mut program = program.program().clone();
  let mut unused = program.functions[0].clone();
  unused.name = "unused".into();
  program.functions.push(unused);
  let mut unused = artifact.functions[0].clone();
  unused.name = "unused".into();
  unused.chip = "unused".into();
  artifact.functions.push(unused);
  let mut unused = artifact.chips[0].clone();
  unused.name = "unused".into();
  artifact.chips.push(unused);
  let unit = json!({"kind":"tuple","items":[]});
  let input = json!({"kind":"tuple","items":[unit]});
  program.tables = serde_json::from_value(json!([
      {"name":"unit_input","type":input,"rows":[[]]},
      {"name":"unit_output","type":unit,"rows":[[]]},
      {"name":"empty_input","type":input,"rows":[]},
      {"name":"empty_output","type":unit,"rows":[]}
  ]))
  .unwrap();
  program.maps = serde_json::from_value(json!([
      {"name":"a","params":[unit],"result":unit,"input":0,"output":1},
      {"name":"b","params":[unit],"result":unit,"input":0,"output":1},
      {"name":"empty","params":[unit],"result":unit,"input":2,"output":3}
  ]))
  .unwrap();
  let program = program.check().unwrap();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  assert_eq!(backend.statistics()[2].stage1_width, 2);
  assert_eq!(backend.statistics()[2].preprocessed_width, 1);
  let record = program.execute("id", vec![]).unwrap();
  compare_generated(&backend, &record, "id", &[]);
  let trace = plan.generate(&record, "id", &[], true).unwrap();
  let witness = backend.witness(&record, &trace).unwrap();
  let proof = backend.prove("id", &[], &[], witness).unwrap();
  assert_eq!(proof.active, [true, false, true, false]);
  backend.verify("id", &[], &[], &proof).unwrap();
}

#[test]
fn fixed_tables_share_height_without_sharing_domains_or_row_order() {
  let (program, mut artifact) = fixture();
  let mut program = program.program().clone();
  program.tables.extend(
        serde_json::from_value::<Vec<crate::bytecode::Table>>(json!([
            {"name":"pairs","type":{"kind":"tuple","items":[f(),f()]},"rows":[[4,4],[2,2],[3,3]]},
            {"name":"sums","type":f(),"rows":[[8],[4],[6]]}
        ]))
        .unwrap(),
    );
  program.maps.push(
    serde_json::from_value(json!({
        "name":"sum","params":[f(),f()],"result":f(),"input":2,"output":3
    }))
    .unwrap(),
  );
  program.functions[1].registers = 4;
  program.functions[1].code = serde_json::from_value(json!([
      {"op":"call","function":2,"args":[0],"dest":[1]},
      {"op":"call","function":3,"args":[0,0],"dest":[2]},
      {"op":"binary","operator":"add","left":1,"right":2,"dest":3},
      {"op":"ret","value":[3]}
  ]))
  .unwrap();
  artifact.functions[1].witnesses = 4;
  artifact.functions[1].output = vec![3];
  artifact.functions[1].writes =
    serde_json::from_value(json!(writes(4))).unwrap();
  artifact.functions[1].steps.extend(
    serde_json::from_value::<Vec<crate::trace::PopulationStep>>(json!([
      step(json!({"op":"call","name":"sum","args":[v(0),v(0)],"dest":[2]})),
      step(json!({"op":"assign","dest":[3],"values":[{"add":[v(1),v(2)]}]}))
    ]))
    .unwrap(),
  );
  artifact.chips[1].width = 4;
  artifact.chips[1].output = vec![Polynomial::Var(3)];
  artifact.chips[1].constraints = serde_json::from_value(json!([
      {"sub":[v(3),{"add":[v(1),v(2)]}]}
  ]))
  .unwrap();
  artifact.chips[1].sends.push(
    serde_json::from_value(json!({
        "channel":"sum","args":[v(0),v(0)],"result":[2],"enable":k(1)
    }))
    .unwrap(),
  );
  let program = program.check().unwrap();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  assert_eq!(backend.tables.len(), 1);
  assert_eq!(backend.statistics()[2].stage1_width, 2);
  assert_eq!(backend.statistics()[2].preprocessed_width, 6);
  let record = program.execute("root", vec![3]).unwrap();
  assert_eq!(record.output, [15]);
  compare_generated(&backend, &record, "root", &[3]);
  let witness = backend.generate(&record, "root", &[3]).unwrap();
  // square(3) is row 1; sum(3,3) is row 2, in the same physical chip.
  assert_eq!(
    witness.traces[2].values,
    [
      Val::ZERO,
      Val::ZERO,
      Val::ONE,
      Val::ZERO,
      Val::ZERO,
      Val::ONE,
      Val::ZERO,
      Val::ZERO
    ]
  );
  let proof = backend.prove("root", &[3], &[15], witness.clone()).unwrap();
  backend.verify("root", &[3], &[15], &proof).unwrap();
  let mut bad = witness.traces;
  bad[2].values[3] = Val::ONE;
  bad[2].values[5] = Val::ZERO;
  let proof = backend
    .prove(
      "root",
      &[3],
      &[15],
      SystemWitness::from_stage_1(bad, &backend.system),
    )
    .unwrap();
  assert!(backend.verify("root", &[3], &[15], &proof).is_err());
}

#[test]
fn native_field_witnesses_and_proofs_match_the_integer_backend() {
  let (raw, artifact) = fixture();
  let native = raw.program().clone().check_field::<Val>().unwrap();
  let raw_plan = TracePlan::new(&raw, activate(artifact.clone())).unwrap();
  let plan = TracePlan::new(&native, activate(artifact)).unwrap();
  let raw_record = raw.execute("root", vec![3]).unwrap();
  let args = [Val::from_u64(3)];
  let mut overrides = crate::maps::MapOverrides::<Val>::new();
  overrides
    .insert("square", 1, 1, |input, output| {
      // Only the row index needs an integer; the answer uses field arithmetic.
      output[0] = input[0] * input[0];
      input[0]
        .as_canonical_u64()
        .checked_sub(2)
        .filter(|&row| row < 3)
        .map(|row| row as usize)
        .ok_or_else(|| "no table entry for map input".into())
    })
    .unwrap();
  let record = native
    .prepare_hints(&[])
    .unwrap()
    .with_map_overrides(&overrides)
    .unwrap()
    .execute("root", args.to_vec())
    .unwrap();
  let trace = plan.generate(&record, "root", &args, true).unwrap();
  assert_eq!(
    trace,
    plan.generate_reference(&record, "root", &args, true).unwrap()
  );
  plan.check(&record, &trace, "root", &args).unwrap();
  assert_eq!(
    serde_json::to_value(&trace).unwrap(),
    serde_json::to_value(
      raw_plan.generate(&raw_record, "root", &[3], true).unwrap()
    )
    .unwrap()
  );
  let raw_backend = Backend::new(&raw_plan, parameters()).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  let expected = raw_backend.generate(&raw_record, "root", &[3]).unwrap();
  let witness = backend.generate(&record, "root", &args).unwrap();
  for (a, b) in expected.traces.iter().zip(&witness.traces) {
    assert_eq!(a.width, b.width);
    assert_eq!(a.values, b.values);
  }
  let proof = backend.prove("root", &args, &record.output, witness).unwrap();
  backend.verify("root", &args, &record.output, &proof).unwrap();
  raw_backend.verify("root", &[3], &[9], &proof).unwrap();
  assert!(backend.verify("root", &args, &[Val::from_u64(10)], &proof).is_err());
  compare_generated(&backend, &record, "root", &args);
}

#[test]
fn resource_plan_matches_generated_trace_and_selects_retention() {
  use super::planning::{Options, RetentionPolicy};
  let (program, artifact) = fixture();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = Backend::for_batch(&plan, parameters()).unwrap();
  let record = program.execute("root", vec![3]).unwrap();
  let actual = backend.generate_stage_1(&record, "root", &[3]).unwrap();
  let generous =
    Options { max_ram_bytes: Some(u64::MAX), ..Default::default() };
  let measured = backend.plan_batch(&record, &generous).unwrap();
  assert_eq!(
    measured.stage1_cells,
    actual.iter().map(|m| m.values.len() as u64).sum::<u64>()
  );
  assert!(measured.fits);
  let heights: Vec<_> =
    backend
      .system
      .circuits
      .iter()
      .map(|c| {
        if c.preprocessed_height == 0 { 32768 } else { c.preprocessed_height }
      })
      .collect();
  let retained = backend
    .plan_heights(
      &heights,
      &Options { max_rows: Some(256), ..generous.clone() },
      0,
    )
    .unwrap();
  let regenerated = backend
    .plan_heights(
      &heights,
      &Options {
        max_rows: Some(256),
        retention: RetentionPolicy::Regenerate,
        ..generous.clone()
      },
      0,
    )
    .unwrap();
  assert_eq!(retained.shards, 128);
  assert_eq!(retained.retention, RetentionPolicy::Retain);
  assert!(retained.proving_peak_bytes > regenerated.proving_peak_bytes);
  let automatic = backend
    .plan_heights(
      &heights,
      &Options {
        max_rows: Some(256),
        max_ram_bytes: Some(
          regenerated.proving_peak_bytes.max(regenerated.generation_peak_bytes),
        ),
        ..Default::default()
      },
      0,
    )
    .unwrap();
  assert!(automatic.fits);
  assert_eq!(automatic.retention, RetentionPolicy::Regenerate);
  let impossible = backend
    .plan_heights(
      &heights,
      &Options { max_ram_bytes: Some(1), ..Default::default() },
      0,
    )
    .unwrap();
  assert!(!impossible.fits);
  assert!(impossible.suggested_parts > 1);
  let floor = backend.plan_fixed(&generous, 0).unwrap();
  assert_eq!(floor.shards, 1);
  assert!(floor.stage1_cells < regenerated.stage1_cells);
  assert!(
    !backend
      .plan_fixed(
        &Options {
          max_ram_bytes: Some(floor.proving_peak_bytes - 1),
          ..Default::default()
        },
        0
      )
      .unwrap()
      .fits
  );
  let mut wrong = heights;
  let table = backend
    .system
    .circuits
    .iter()
    .position(|c| c.preprocessed_height > 0)
    .unwrap();
  wrong[table] *= 2;
  assert!(backend.plan_heights(&wrong, &generous, 0).is_err());
  #[cfg(not(feature = "cuda"))]
  assert!(
    Options { device: Some(0), ..Default::default() }.validate().is_err()
  );
}
#[test]
fn lean_grouped_layout_shares_rows_and_preserves_proofs() {
  #[derive(serde::Deserialize)]
  struct Package {
    program: crate::Program,
    trace: crate::trace::TraceArtifact,
  }
  let package: Package = serde_json::from_str(include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/grouping.json"
  )))
  .unwrap();
  assert_eq!(package.trace.groups.len(), 1);
  let group = &package.trace.groups[0];
  assert_eq!(group.members.len(), 3);
  let selectors: Vec<_> = group.members.iter().map(|m| m.selector).collect();
  let program = package.program.check().unwrap();
  let mut plain = package.trace.clone();
  plain.groups.clear();
  let ungrouped = TracePlan::new(&program, plain).unwrap();
  let plan = TracePlan::new(&program, package.trace).unwrap();
  let backend = Backend::for_batch(&plan, parameters()).unwrap();
  let plain_backend = Backend::for_batch(&ungrouped, parameters()).unwrap();
  assert_eq!(plain_backend.statistics().len(), backend.statistics().len() + 2);
  assert!(backend.statistics().iter().all(|c| c.quotient_degree <= 2));
  let entry = "Grouped::run";
  let record = program.execute(entry, vec![3]).unwrap();
  assert_eq!(record.output, vec![140]);
  let reference = ungrouped.generate(&record, entry, &[3], true).unwrap();
  ungrouped.check(&record, &reference, entry, &[3]).unwrap();
  let converted = backend.witness(&record, &reference).unwrap();
  let direct = backend.generate(&record, entry, &[3]).unwrap();
  for (a, b) in converted.traces.iter().zip(&direct.traces) {
    assert_eq!(a.width, b.width);
    assert_eq!(a.values, b.values);
  }
  let ci =
    backend.names.iter().position(|n| n == "arithmetic_and_memory").unwrap();
  assert_eq!(direct.traces[ci].height(), 8);
  assert!(
    direct.traces[ci].values[5 * direct.traces[ci].width..]
      .iter()
      .all(|&v| v == Val::ZERO)
  );
  let expected_cells: u64 =
    direct.traces.iter().map(|t| t.values.len() as u64).sum();
  let budget =
    backend.plan_batch(&record, &planning::Options::default()).unwrap();
  assert_eq!(budget.stage1_cells, expected_cells);
  let proof = backend
    .prove_batch(
      entry,
      &[3],
      &record.output,
      direct.clone(),
      2,
      multi_stark::batch::Retention::Retain,
    )
    .unwrap();
  backend.verify_batch(entry, &[3], &record.output, &proof).unwrap();
  for attack in 0..3 {
    let mut forged = direct.traces.clone();
    let width = forged[ci].width;
    let row = &mut forged[ci].values[..width];
    let active = selectors.iter().position(|&s| row[s] == Val::ONE).unwrap();
    match attack {
      0 => row[selectors[active]] = Val::TWO,
      1 => row[selectors[(active + 1) % selectors.len()]] = Val::ONE,
      _ => {
        // An inactive padding row cannot impersonate a provider.
        forged[ci].values[5 * width + width - 1] = Val::ONE;
      },
    }
    assert!(
      backend
        .prove_batch_stage_1(
          entry,
          &[3],
          &record.output,
          forged,
          8,
          multi_stark::batch::Retention::Retain
        )
        .is_err()
    );
  }
}
