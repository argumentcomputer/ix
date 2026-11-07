use super::*;
use serde_json::{Value as Json, json};

/// Small raw fixtures remain readable in their original column layout. The
/// integration tests also exercise the actual, proved Lean activation export.
pub(crate) fn raw_artifact(mut value: Json) -> TraceArtifact {
  for chip in value["chips"].as_array_mut().unwrap() {
    chip["activation"] = chip["width"].clone();
  }
  serde_json::from_value(value).unwrap()
}

pub(crate) fn activate(mut artifact: TraceArtifact) -> TraceArtifact {
  let field = PrimeField::new(artifact.modulus).unwrap();
  for chip in &mut artifact.chips {
    let id = chip.width;
    chip.activation = id;
    chip.width += 1;
    let zero = vec![0; id];
    let active = Polynomial::Var(id);
    let inactive =
      Polynomial::Sub(Box::new([Polynomial::Const(1), active.clone()]));
    let lift = |p: Polynomial| {
      let constant = p.eval(&zero, field);
      Polynomial::Sub(Box::new([
        p,
        Polynomial::Mul(Box::new([
          Polynomial::Const(constant),
          inactive.clone(),
        ])),
      ]))
    };
    chip.constraints =
      std::mem::take(&mut chip.constraints).into_iter().map(lift).collect();
    chip
      .constraints
      .push(Polynomial::Mul(Box::new([active, inactive.clone()])));
    for send in &mut chip.sends {
      send.enable = lift(send.enable.clone());
      chip.constraints.push(Polynomial::Mul(Box::new([
        inactive.clone(),
        send.enable.clone(),
      ])));
    }
    for cell in &mut chip.memory {
      cell.enable = lift(cell.enable.clone());
      chip.constraints.push(Polynomial::Mul(Box::new([
        inactive.clone(),
        cell.enable.clone(),
      ])));
    }
  }
  artifact.version = 2;
  artifact
}

fn field() -> Json {
  json!({"kind":"field"})
}
fn var(id: usize) -> Json {
  json!({"var":id})
}
fn constant(value: u64) -> Json {
  json!({"const":value})
}
fn step(action: Json) -> Json {
  json!({"guard":constant(1),"action":action})
}
fn write(column: usize) -> Json {
  json!({"column":column,"source":column,"guard":constant(1)})
}
fn setup(
  functions: Json,
  plans: Json,
  chips: Json,
  params: Json,
  output: Json,
) -> (CheckedProgram, TraceArtifact) {
  let program: crate::Program = serde_json::from_value(json!({
        "version":1,"modulus":97,"functions":functions,"enums":[],"maps":[],"tables":[],
        "entries":[{"name":"main","function":0,"inputs":params,"output":output}]
    }))
    .unwrap();
  let artifact = raw_artifact(
    json!({"version":1,"modulus":97,"functions":plans,"chips":chips}),
  );
  (program.check().unwrap(), artifact)
}
fn square() -> (CheckedProgram, TraceArtifact) {
  setup(
    json!([{"name":"main","params":[field()],"result":field(),"registers":2,
        "code":[{"op":"binary","operator":"mul","left":0,"right":0,"dest":1},{"op":"ret","value":[1]}]}]),
    json!([{"name":"main","chip":"main","witnesses":2,"inputs":[0],"output":[1],
            "steps":[step(json!({"op":"assign","dest":[1],"values":[{"mul":[var(0),var(0)]}]}))],"writes":[write(0),write(1)]}]),
    json!([{"name":"main","width":2,"inputs":[0],"output":[var(1)],
            "constraints":[{"sub":[var(1),{"mul":[var(0),var(0)]}]}],"sends":[],"memory":[]}]),
    json!([field()]),
    field(),
  )
}

#[test]
fn detects_corrupt_rows_counts_shapes_and_plan_indices() {
  let (program, artifact) = square();
  let record = program.execute("main", vec![7]).unwrap();
  let plan = TracePlan::new(&program, activate(artifact.clone())).unwrap();
  let trace = plan.generate(&record, "main", &[7], true).unwrap();
  assert_eq!(
    trace,
    plan.generate_reference(&record, "main", &[7], true).unwrap()
  );
  assert_eq!(trace.matrices[0].values, [7, 49, 1]);
  plan.check(&record, &trace, "main", &[7]).unwrap();
  let mut bad = trace.clone();
  bad.matrices[0].values[1] = 48;
  assert!(
    plan.check(&record, &bad, "main", &[7]).unwrap_err().contains("constraint")
  );
  let mut bad = trace.clone();
  bad.matrices[0].multiplicities[0] += 1;
  assert!(
    plan.check(&record, &bad, "main", &[7]).unwrap_err().contains("unbalanced")
  );
  let mut bad = trace.clone();
  bad.matrices[0].height = usize::MAX;
  assert!(plan.check(&record, &bad, "main", &[7]).is_err());
  let mut bad = trace.clone();
  bad.matrices[0].values[0] = 97;
  assert!(plan.check(&record, &bad, "main", &[7]).is_err());
  let mut bad = artifact.clone();
  bad.functions[0].writes[0].column = 2;
  assert!(TracePlan::new(&program, activate(bad)).is_err());
  let mut bad = artifact;
  bad.functions[0].writes[0].guard = Polynomial::Const(97);
  assert!(TracePlan::new(&program, activate(bad)).is_err());
  let mut bad = record;
  bad.output[0] = 48;
  assert!(plan.generate(&bad, "main", &[7], true).is_err());

  // A record from another field can have identical callable widths. It must
  // still be rejected before its words reach field arithmetic.
  let mut foreign = program.program().clone();
  foreign.modulus = 101;
  let foreign = foreign.check().unwrap().execute("main", vec![100]).unwrap();
  assert!(plan.generate(&foreign, "main", &[100], true).is_err());
}

#[test]
fn zero_width_rows_keep_their_height_and_root_count() {
  let unit = json!({"kind":"tuple","items":[]});
  let (program, artifact) = setup(
    json!([{"name":"main","params":[],"result":unit,"registers":0,
        "code":[{"op":"ret","value":[]}]}]),
    json!([{"name":"main","chip":"main","witnesses":0,"inputs":[],"output":[],"steps":[],"writes":[]}]),
    json!([{"name":"main","width":0,"inputs":[],"output":[],"constraints":[],"sends":[],"memory":[]}]),
    json!([]),
    unit,
  );
  let record = program.execute("main", vec![]).unwrap();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let trace = plan.generate(&record, "main", &[], true).unwrap();
  assert_eq!(trace.matrices[0].height, 1);
  assert_eq!(trace.matrices[0].values, [1]);
  assert_eq!(trace.matrices[0].multiplicities, [1]);
  plan.check(&record, &trace, "main", &[]).unwrap();
}

#[test]
fn hint_providers_survive_preparation_and_replay_for_each_trace() {
  let mut code = vec![
    json!({"op":"hint","channel":"square","type":field(),
        "key_type":field(),"key":[0],"dest":[1]});
    10
  ];
  code.extend([
    json!({"op":"binary","operator":"mul","left":1,"right":1,"dest":2}),
    json!({"op":"ret","value":[2]}),
  ]);
  let (program, artifact) = setup(
    json!([{"name":"main","params":[field()],"result":field(),"registers":3,
        "code":code}]),
    json!([{"name":"main","chip":"main","witnesses":3,"inputs":[0],"output":[2],
            "steps":[step(json!({"op":"hint","channel":"square","instruction":9,"type":field(),"key_type":field(),"key":[var(0)],"dest":[1]}))],
            "writes":[write(0),write(1)]}]),
    json!([{"name":"main","width":2,"inputs":[0],"output":[{"mul":[var(1),var(1)]}],
            "constraints":[],"sends":[],"memory":[]}]),
    json!([field()]),
    field(),
  );
  let hints = serde_json::from_value::<Vec<crate::hints::HintEntry>>(json!([
        {"channel":"square","type":field(),"key_type":field(),"key":[7],"output":[7]}]))
    .unwrap();
  let record = program.execute_with_hints("main", vec![7], &hints).unwrap();
  let mut mismatched = artifact.clone();
  let Action::Hint { channel, .. } =
    &mut mismatched.functions[0].steps[0].action
  else {
    panic!()
  };
  *channel = "other".into();
  assert!(
    TracePlan::new(&program, activate(mismatched))
      .err()
      .unwrap()
      .contains("hint site mismatch")
  );
  let invoked = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
  let mut channels = crate::hints::HintChannels::new();
  let calls = invoked.clone();
  channels
    .insert_fixed::<1, 1>(
      "square",
      crate::bytecode::Type::Field,
      crate::bytecode::Type::Field,
      move |key| {
        calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Ok(key)
      },
    )
    .unwrap();
  let from_code = program
    .prepare_hint_channels(&[], &channels)
    .unwrap()
    .execute("main", vec![7])
    .unwrap();
  assert_eq!(from_code.queries, record.queries);
  drop(channels);
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let good = plan.generate(&record, "main", &[7], true).unwrap();
  plan.check(&record, &good, "main", &[7]).unwrap();
  for replay in [
    plan.generate(&from_code, "main", &[7], true),
    plan.generate_reference(&from_code, "main", &[7], true),
  ] {
    plan.check(&from_code, &replay.unwrap(), "main", &[7]).unwrap();
  }
  // Execution consumed ten hints; the live trace recipe needs only the last.
  assert_eq!(invoked.load(std::sync::atomic::Ordering::Relaxed), 12);
  assert_eq!(plan.generate(&from_code, "main", &[7], true).unwrap(), good);
  assert_eq!(invoked.load(std::sync::atomic::Ordering::Relaxed), 13);
  // Repeated/parallel row generation may reorder calls. The same captured
  // provider must work after its registry and PreparedHints have been dropped.
  std::thread::scope(|scope| {
    let workers: Vec<_> = (0..4)
      .map(|_| {
        scope.spawn(|| plan.generate(&from_code, "main", &[7], true).unwrap())
      })
      .collect();
    for worker in workers {
      assert_eq!(worker.join().unwrap(), good);
    }
  });
  assert_eq!(invoked.load(std::sync::atomic::Ordering::Relaxed), 17);
  // A record cannot substitute providers bound to another checked program,
  // even if its function signatures and instruction sites happen to match.
  let foreign = program.program().clone().check().unwrap();
  let foreign_record =
    foreign.execute_with_hints("main", vec![7], &hints).unwrap();
  assert!(
    plan
      .generate(&foreign_record, "main", &[7], true)
      .unwrap_err()
      .contains("another program")
  );
}

#[test]
fn replay_validates_provider_answers_and_propagates_errors() {
  use crate::hints::HintChannels;
  use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
  };
  let (program, artifact) = setup(
    json!([{"name":"main","params":[field()],"result":field(),"registers":3,
        "code":[
            {"op":"hint","channel":"identity","type":field(),"key_type":field(),"key":[0],"dest":[1]},
            {"op":"binary","operator":"mul","left":1,"right":1,"dest":2},
            {"op":"ret","value":[2]}]}]),
    json!([{"name":"main","chip":"main","witnesses":3,"inputs":[0],"output":[2],
            "steps":[step(json!({"op":"hint","channel":"identity","instruction":0,"type":field(),"key_type":field(),"key":[var(0)],"dest":[1]}))],
            "writes":[write(0),write(1)]}]),
    json!([{"name":"main","width":2,"inputs":[0],"output":[{"mul":[var(1),var(1)]}],
            "constraints":[],"sends":[],"memory":[]}]),
    json!([field()]),
    field(),
  );
  // Deliberately break repeatability after execution to exercise the checks
  // on newly generated advice. A provider contract is not a trust boundary.
  let mode = Arc::new(AtomicUsize::new(0));
  let mut channels = HintChannels::new();
  let state = mode.clone();
  channels
    .insert("identity", Type::Field, Type::Field, move |key, output| {
      assert_eq!(output, [0]);
      match state.load(Ordering::Relaxed) {
        0 => output.copy_from_slice(key),
        1 => return Err("provider unavailable".into()),
        _ => output[0] = 97, // noncanonical in the runtime-prime backend
      }
      Ok(())
    })
    .unwrap();
  let prepared = program.prepare_hint_channels(&[], &channels).unwrap();
  let record = prepared.execute("main", vec![7]).unwrap();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  for state in [1, 2] {
    mode.store(state, Ordering::Relaxed);
    for result in [
      plan.generate(&record, "main", &[7], true),
      plan.generate_reference(&record, "main", &[7], true),
    ] {
      let error = result.unwrap_err();
      if state == 1 {
        assert!(error.contains("provider unavailable"));
      }
    }
  }
  mode.store(0, Ordering::Relaxed);
  let trace = plan.generate(&record, "main", &[7], true).unwrap();
  plan.check(&record, &trace, "main", &[7]).unwrap();
  assert_eq!(
    trace,
    plan.generate_reference(&record, "main", &[7], true).unwrap()
  );
}

#[test]
fn zero_padding_emits_no_requirements_and_preserves_execution_counts() {
  let call = |name: &str, arg: Json, dest: usize| {
    step(json!({"op":"call","name":name,"args":[arg],"dest":[dest]}))
  };
  let send = |name: &str, arg: Json, dest: usize| json!({"channel":name,"args":[arg],"result":[dest],"enable":constant(1)});
  let (program, artifact) = setup(
    json!([
        {"name":"main","params":[field()],"result":field(),"registers":6,"code":[
            {"op":"call","function":1,"args":[0],"dest":[1]},
            {"op":"literal","dest":2,"value":1},{"op":"call","function":1,"args":[2],"dest":[3]},
            {"op":"literal","dest":4,"value":2},{"op":"call","function":1,"args":[4],"dest":[5]},
            {"op":"ret","value":[5]}]},
        {"name":"middle","params":[field()],"result":field(),"registers":2,"code":[
            {"op":"call","function":2,"args":[0],"dest":[1]},{"op":"ret","value":[1]}]},
        {"name":"leaf","params":[field()],"result":field(),"registers":1,"code":[{"op":"ret","value":[0]}]}
    ]),
    json!([
        {"name":"main","chip":"main","witnesses":4,"inputs":[0],"output":[3],
            "steps":[call("middle",var(0),1),call("middle",constant(1),2),call("middle",constant(2),3)],
            "writes":[write(0),write(1),write(2),write(3)]},
        {"name":"middle","chip":"middle","witnesses":2,"inputs":[0],"output":[1],
            "steps":[call("leaf",var(0),1)],"writes":[write(0),write(1)]},
        {"name":"leaf","chip":"leaf","witnesses":2,"inputs":[0],"output":[1],"steps":[],"writes":[write(0)]}
    ]),
    json!([
        {"name":"main","width":4,"inputs":[0],"output":[var(3)],"constraints":[],"memory":[],
            "sends":[send("middle",var(0),1),send("middle",constant(1),2),send("middle",constant(2),3)]},
        {"name":"middle","width":2,"inputs":[0],"output":[var(1)],"constraints":[],"memory":[],"sends":[send("leaf",var(0),1)]},
        {"name":"leaf","width":1,"inputs":[0],"output":[var(0)],"constraints":[],"memory":[],"sends":[]}
    ]),
    json!([field()]),
    field(),
  );
  let record = program.execute("main", vec![0]).unwrap();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let plain = plan.generate(&record, "main", &[0], false).unwrap();
  let padded = plan.generate(&record, "main", &[0], true).unwrap();
  assert_eq!(plain.matrices[2].multiplicities, [1, 1, 1]);
  assert_eq!(padded.matrices[1].multiplicities, [1, 1, 1, 0]);
  assert_eq!(padded.matrices[2].multiplicities, [1, 1, 1, 0]);
  for matrix in &padded.matrices[1..] {
    assert!(matrix.row(3).iter().all(|&word| word == 0));
  }
  assert_eq!(
    padded,
    plan.generate_reference(&record, "main", &[0], true).unwrap()
  );
  plan.check(&record, &padded, "main", &[0]).unwrap();
  let mut wrong = padded;
  wrong.matrices[2].multiplicities[0] = 2;
  assert!(plan.check(&record, &wrong, "main", &[0]).is_err());
}
