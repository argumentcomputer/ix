use super::*;
use crate::{
  budget::{BudgetError, RecordPool},
  execute::Partition,
};
use multi_stark::batch::Retention;

#[test]
fn cached_helpers_preserve_cross_record_cycle_edges() {
  let unit = json!({"kind":"tuple", "items":[]});
  let program = serde_json::from_value::<Program>(json!({
    "version":1,"modulus":Val::ORDER_U64,"enums":[],"maps":[],"tables":[],
    "functions":[
      {"name":"owned","params":[f()],"result":unit,"registers":1,"code":[
        {"op":"call","function":1,"args":[],"dest":[]},
        {"op":"ret","value":[]}]},
      {"name":"helper","params":[],"result":unit,"registers":1,"code":[
        {"op":"literal","dest":0,"value":2},
        {"op":"call","function":0,"args":[0],"dest":[]},
        {"op":"ret","value":[]}]}
    ],"entries":[]
  }))
  .unwrap()
  .check()
  .unwrap();
  let record = program
    .prepare_hints(&[])
    .unwrap()
    .execute_partition(
      None,
      Partition {
        function: 0,
        owned: vec![vec![0], vec![1]],
        memory_start: 0,
        memory_end: 100,
      },
      None,
    )
    .unwrap();
  // owned(1) hits the helper memoized by owned(0). Omitting its edge would
  // hide a cycle if the other record's owned(2) depends on owned(1).
  let edges: std::collections::HashSet<_> = record.partition_edges().collect();
  assert_eq!(
    edges,
    [(&[0][..], &[2][..]), (&[1][..], &[2][..])].into_iter().collect()
  );
  assert_eq!(record.deferred_calls().collect::<Vec<_>>(), [(&[2][..], 1)]);
}

#[test]
fn reservation_limits_growth_and_follows_record_storage() {
  let (program, _) = fixture();
  let hints = program.prepare_hints(&[]).unwrap();
  let pool = RecordPool::new(1 << 20, 128).with_record_limit(256);
  let reservation = pool.try_admit().unwrap().unwrap();
  let error =
    hints.execute_reserved("root", vec![3], &reservation).unwrap_err();
  assert!(matches!(error.resource, Some(BudgetError::Exceeded { .. })));
  drop(reservation);
  assert_eq!(pool.stats().reserved, 0);

  let pool = RecordPool::new(8 << 20, 1 << 20);
  let reservation = pool.try_admit().unwrap().unwrap();
  let record = hints.execute_reserved("root", vec![3], &reservation).unwrap();
  reservation.finish_execution();
  let charged = reservation.bytes();
  assert!(charged > 0);
  let memory = record.memory;
  drop(record.queries);
  drop(reservation);
  assert_eq!(pool.stats().reserved, charged);
  drop(memory);
  assert_eq!(pool.stats().reserved, 0);
}

#[test]
fn unit_call_partitions_balance_one_claim_with_disjoint_roms() {
  let unit = json!({"kind":"tuple", "items":[]});
  let program: Program = serde_json::from_value(json!({
    "version":1,"modulus":Val::ORDER_U64,"enums":[], "maps":[],"tables":[],
    "functions":[
      {"name":"root","params":[f()],"result":f(),"registers":3,"code":[
        {"op":"call","function":1,"args":[0],"dest":[]},
        {"op":"store","type":f(),"value":[0],"dest":1},
        {"op":"load","type":f(),"pointer":1,"dest":[2]},
        {"op":"ret","value":[2]}]},
      {"name":"leaf","params":[f()],"result":unit,"registers":3,"code":[
        {"op":"store","type":f(),"value":[0],"dest":1},
        {"op":"load","type":f(),"pointer":1,"dest":[2]},
        {"op":"assert_eq","left":[0],"right":[2]},
        {"op":"ret","value":[]}]}
    ], "entries":[{"name":"root","function":0,"inputs":[f()],"output":f()}]
  }))
  .unwrap();
  let functions: Vec<_> = ["root","leaf"].iter().map(|&name| {
    let mut steps = vec![];
    if name == "root" { steps.push(step(json!({"op":"call","name":"leaf","args":[v(0)],"dest":[]}))); }
    steps.extend([
      step(json!({"op":"store","type":f(),"values":[v(0)],"dest":1})),
      step(json!({"op":"load","type":f(),"address":v(1),"dest":[2]}))]);
    json!({"name":name,"chip":name,"witnesses":3,"inputs":[0],
      "output":if name == "root" {vec![2]} else {vec![]},"steps":steps,"writes":writes(3)})
  }).collect();
  let chips: Vec<_> = ["root","leaf"].iter().map(|&name| json!({
    "name":name,"width":3,"inputs":[0],"output":if name == "root" {vec![v(2)]} else {vec![]},
    "constraints":[{"sub":[v(0),v(2)]}],
    "sends":if name == "root" {vec![json!({"channel":"leaf","args":[v(0)],"result":[],"enable":k(1)})]} else {vec![]},
    "memory":[{"type":f(),"address":v(1),"values":[v(0)],"enable":k(1)},
      {"type":f(),"address":v(1),"values":[v(2)],"enable":k(1)}]
  })).collect();
  let artifact = activate(raw_artifact(
    json!({"version":1,"modulus":Val::ORDER_U64,"functions":functions,"chips":chips}),
  ));
  let program = program.check().unwrap();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend = Backend::for_batch(&plan, parameters()).unwrap();
  let hints = program.prepare_hints(&[]).unwrap();
  let caller = hints
    .execute_partition(
      Some(("root", vec![3])),
      Partition {
        function: 1,
        owned: vec![],
        memory_start: 0,
        memory_end: 100,
      },
      None,
    )
    .unwrap();
  assert_eq!(caller.output, [3]);
  assert_eq!(caller.deferred_calls().collect::<Vec<_>>(), [(&[3][..], 1)]);
  let mut owner = hints
    .execute_partition(
      None,
      Partition {
        function: 1,
        owned: vec![vec![3]],
        memory_start: 100,
        memory_end: 200,
      },
      None,
    )
    .unwrap();
  assert!(backend.generate_record_stage_1(&owner).is_err());
  assert!(owner.absorb_deferred(1, &[4], 1).is_err());
  owner.absorb_deferred(1, &[3], 1).unwrap();
  assert_eq!(owner.memory.get(0).unwrap().address, 100);
  let intervals = [
    backend.record_shape(&caller).unwrap(),
    backend.record_shape(&owner).unwrap(),
  ]
  .into_iter()
  .flat_map(|s| s.memory_intervals)
  .collect::<Vec<_>>();
  assert_eq!(intervals, [(1, 0, 1), (1, 100, 101)]);
  let shapes = [
    backend.record_shape(&caller).unwrap(),
    backend.record_shape(&owner).unwrap(),
  ];
  let records: Vec<_> =
    shapes.iter().map(|s| (s.heights.as_slice(), 1)).collect();
  let regen_options = planning::Options {
    max_ram_bytes: Some(1 << 30),
    retention: planning::RetentionPolicy::Regenerate,
    ..Default::default()
  };
  let regen_plan = backend.plan_stream(&records, &regen_options).unwrap();
  let retain_options = planning::Options {
    retention: planning::RetentionPolicy::Retain,
    ..regen_options.clone()
  };
  let retain_plan = backend.plan_stream(&records, &retain_options).unwrap();
  assert!(retain_plan.peak_bytes > regen_plan.peak_bytes);
  let tight = planning::Options {
    max_ram_bytes: Some(regen_plan.peak_bytes),
    retention: planning::RetentionPolicy::Auto,
    ..Default::default()
  };
  let auto = backend.plan_stream(&records, &tight).unwrap();
  assert!(auto.fits);
  assert_eq!(auto.retention, planning::RetentionPolicy::Regenerate);
  assert!(
    !backend
      .plan_stream(
        &records,
        &planning::Options {
          retention: planning::RetentionPolicy::Retain,
          ..tight
        }
      )
      .unwrap()
      .fits
  );
  let traces = [
    backend.generate_stage_1(&caller, "root", &[3]).unwrap(),
    backend.generate_record_stage_1(&owner).unwrap(),
  ];
  let prove = |retention| {
    backend.prove_streamed_stage_1(
      "root",
      &[3],
      &[3],
      StreamPlan { shards: 2, memory_intervals: intervals.clone(), retention },
      |i| Ok(traces[i].clone()),
    )
  };
  let retained = prove(Retention::Retain).unwrap();
  let regenerated = prove(Retention::Regenerate).unwrap();
  assert_eq!(retained.to_bytes().unwrap(), regenerated.to_bytes().unwrap());
  backend.verify_batch("root", &[3], &[3], &regenerated).unwrap();
  assert!(backend.verify_batch("root", &[4], &[3], &regenerated).is_err());
  let mut bad = regenerated.clone();
  bad.preamble.messages[2].args[2] = Val::ZERO;
  assert!(backend.verify_batch("root", &[3], &[3], &bad).is_err());
  assert!(
    backend
      .prove_streamed_stage_1(
        "root",
        &[3],
        &[3],
        StreamPlan {
          shards: 2,
          memory_intervals: intervals,
          retention: Retention::Regenerate
        },
        |_| Err("replay failed".into())
      )
      .is_err()
  );
  assert!(
    hints
      .execute_partition(
        Some(("root", vec![3])),
        Partition {
          function: 0,
          owned: vec![],
          memory_start: 0,
          memory_end: 100
        },
        None
      )
      .is_err()
  );
}
