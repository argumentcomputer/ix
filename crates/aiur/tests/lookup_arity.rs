use aiur::{
  Program,
  artifact::Package,
  field::PrimeField,
  trace::{
    FunctionGroup, GroupLookup, GroupMember, Polynomial, TraceArtifact,
    TracePlan, check_constant_prefix_lookup_arities,
  },
};
use rustc_hash::FxHashMap;
use serde_json::json;

#[test]
fn ungrouped_constant_prefix_arity_mismatch_is_rejected() {
  let field = PrimeField::new(97).unwrap();
  let mut arities = FxHashMap::default();
  let short = [Polynomial::Const(1), Polynomial::Const(0), Polynomial::Var(0)];
  let trailing_zero = [
    Polynomial::Const(1),
    Polynomial::Const(0),
    Polynomial::Var(0),
    Polynomial::Const(0),
  ];
  let err = check_constant_prefix_lookup_arities(
    field,
    &mut arities,
    [(false, short.as_slice()), (false, trailing_zero.as_slice())],
  )
  .unwrap_err();
  assert!(err.contains("inconsistent ungrouped lookup arity"), "{err}");

  let mut rom_arities = FxHashMap::default();
  let rom_a = [
    Polynomial::Const(2),
    Polynomial::Const(1),
    Polynomial::Var(0),
    Polynomial::Var(1),
  ];
  let rom_b = [
    Polynomial::Const(2),
    Polynomial::Const(1),
    Polynomial::Var(0),
    Polynomial::Var(1),
    Polynomial::Const(0),
  ];
  let err = check_constant_prefix_lookup_arities(
    field,
    &mut rom_arities,
    [(false, rom_a.as_slice()), (false, rom_b.as_slice())],
  )
  .unwrap_err();
  assert!(err.contains("inconsistent ungrouped lookup arity"), "{err}");
}

#[test]
fn grouped_call_zero_padding_is_accepted_and_truncation_is_rejected() {
  let field = PrimeField::new(97).unwrap();
  let ungrouped_call = [
    Polynomial::Const(1),
    Polynomial::Const(3),
    Polynomial::Var(0),
    Polynomial::Var(1),
  ];
  let padded_grouped_call = [
    Polynomial::Const(1),
    Polynomial::Const(3),
    Polynomial::Var(0),
    Polynomial::Var(1),
    Polynomial::Const(0),
    Polynomial::Const(0),
  ];
  let mut arities = FxHashMap::default();
  check_constant_prefix_lookup_arities(
    field,
    &mut arities,
    [
      (false, ungrouped_call.as_slice()),
      (true, padded_grouped_call.as_slice()),
    ],
  )
  .unwrap();

  let truncated_grouped_call =
    [Polynomial::Const(1), Polynomial::Const(3), Polynomial::Var(0)];
  let mut arities = FxHashMap::default();
  let err = check_constant_prefix_lookup_arities(
    field,
    &mut arities,
    [
      (false, ungrouped_call.as_slice()),
      (true, truncated_grouped_call.as_slice()),
    ],
  )
  .unwrap_err();
  assert!(err.contains("truncated grouped CALL lookup arity"), "{err}");
}

#[test]
fn trace_plan_accepts_honest_grouped_depth_and_memory_fixtures() {
  for bytes in [
    &include_bytes!("fixtures/grouping.ixa")[..],
    &include_bytes!("fixtures/depth.ixa")[..],
    &include_bytes!("fixtures/memory.ixa")[..],
  ] {
    let package = Package::decode(bytes).unwrap();
    let (program, trace) = package.traced().unwrap();
    let mut program = program.check().unwrap();
    program.track_depth(&trace).unwrap();
    TracePlan::new(&program, trace).unwrap();
  }
}

#[test]
fn trace_plan_rejects_mismatched_single_member_group_and_bad_tags() {
  let package =
    Package::decode(include_bytes!("fixtures/grouping.ixa")).unwrap();
  let (program, base_trace) = package.traced().unwrap();
  let mut program = program.check().unwrap();
  program.track_depth(&base_trace).unwrap();
  assert!(!base_trace.groups.is_empty());

  // Tampered group receive with non-CALL constant channel tag.
  let mut bad_recv_tag = base_trace.clone();
  bad_recv_tag.groups[0].receive[0] = Polynomial::Const(2);
  let err = TracePlan::new(&program, bad_recv_tag).err().unwrap();
  assert!(err.contains("non-CALL channel tag"), "{err}");

  // Tampered group send with invalid constant channel tag.
  let mut bad_send_tag = base_trace.clone();
  bad_send_tag.groups[0].sends.push(GroupLookup {
    enable: Polynomial::Const(1),
    args: vec![Polynomial::Const(9), Polynomial::Const(0)],
  });
  let err = TracePlan::new(&program, bad_send_tag).err().unwrap();
  assert!(err.contains("invalid channel tag"), "{err}");

  // Group colliding with an existing chip name.
  let mut dup_name = base_trace.clone();
  dup_name.groups[0].name = dup_name.chips[0].name.clone();
  let err = TracePlan::new(&program, dup_name).err().unwrap();
  assert!(err.contains("duplicate circuit or group name"), "{err}");

  // Single-member group carrying a constant-prefixed CALL with trailing zero.
  let mut single_mismatch = base_trace.clone();
  single_mismatch.groups.clear();
  let target_chip = &single_mismatch.chips[0];
  let target_id = u64::try_from(
    program
      .program()
      .functions
      .iter()
      .position(|f| f.name == target_chip.name)
      .unwrap(),
  )
  .unwrap();
  let canonical_arity = 2 + target_chip.inputs.len() + target_chip.output.len();
  let mut padded_receive =
    vec![Polynomial::Const(1), Polynomial::Const(target_id)];
  padded_receive.resize(canonical_arity + 1, Polynomial::Const(0));
  single_mismatch.groups.push(FunctionGroup {
    name: "single_mismatch_group".into(),
    width: target_chip.width,
    activation: Polynomial::Var(target_chip.activation),
    constraints: vec![],
    receive: padded_receive,
    sends: vec![],
    members: vec![GroupMember {
      name: target_chip.name.clone(),
      columns: (0..target_chip.width).collect(),
      selector: target_chip.activation,
      writes: vec![],
    }],
  });
  let err = TracePlan::new(&program, single_mismatch).err().unwrap();
  assert!(err.contains("inconsistent ungrouped lookup arity"), "{err}");
}

#[test]
fn trace_plan_rejects_chip_named_after_static_map() {
  let field = json!({"kind":"field"});
  let tuple1 = json!({"kind":"tuple","items":[field]});
  let source = json!({
    "version": 1,
    "modulus": 97,
    "enums": [],
    "tables": [
      {"name": "in_tbl", "type": tuple1, "rows": [[0], [1]]},
      {"name": "out_tbl", "type": field, "rows": [[1], [0]]}
    ],
    "maps": [
      {"name": "flip_map", "params": [field], "result": field, "input": 0, "output": 1}
    ],
    "functions": [{
      "name": "main",
      "params": [field],
      "result": field,
      "registers": 1,
      "code": [{"op": "ret", "value": [0]}]
    }],
    "entries": [{"name": "main", "function": 0, "inputs": [field], "output": field}]
  });
  let program: Program = serde_json::from_value(source).unwrap();
  let checked = program.check().unwrap();
  let artifact: TraceArtifact = serde_json::from_value(json!({
    "version": 3,
    "modulus": 97,
    "functions": [{
      "name": "main",
      "chip": "main",
      "witnesses": 1,
      "inputs": [0],
      "output": [0],
      "steps": [],
      "writes": [{"column": 0, "source": 0, "guard": {"const": 1}}]
    }],
    "chips": [
      {
        "name": "main",
        "width": 2,
        "activation": 1,
        "inputs": [0],
        "output": [{"var": 0}],
        "constraints": [],
        "sends": [],
        "memory": []
      },
      {
        "name": "flip_map",
        "width": 2,
        "activation": 1,
        "inputs": [0],
        "output": [{"var": 0}],
        "constraints": [],
        "sends": [],
        "memory": []
      }
    ]
  }))
  .unwrap();
  let err = TracePlan::new(&checked, artifact).err().unwrap();
  assert!(err.contains("static map"), "{err}");
}
