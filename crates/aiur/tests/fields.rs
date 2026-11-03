//! The interpreter must work with native elements, independently of their
//! storage size or arithmetic library, and preserve the integer wire contract.
use aiur::{
  Execution, Program,
  field::{FieldBackend, NativeField, PrimeField64},
  hints::HintChannels,
  maps::MapOverrides,
};
use multi_stark::p3_goldilocks::Goldilocks;
use serde::Serialize;
use serde_json::{Value, json};

// An independent four-byte element/backend. This deliberately implements no
// Plonky3 traits: the execution core only needs the FieldBackend contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize)]
#[serde(transparent)]
struct Small(u32);
impl std::fmt::Display for Small {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.0.fmt(f)
  }
}
#[derive(Clone, Copy, Debug)]
struct SmallField;
impl FieldBackend for SmallField {
  type Element = Small;
  fn modulus(self) -> u64 {
    97
  }
  fn from_u64(self, x: u64) -> Small {
    Small((x % 97) as u32)
  }
  fn to_u64(self, x: Small) -> u64 {
    u64::from(x.0)
  }
  fn add(self, a: Small, b: Small) -> Small {
    Small((a.0 + b.0) % 97)
  }
  fn sub(self, a: Small, b: Small) -> Small {
    Small((a.0 + 97 - b.0) % 97)
  }
  fn neg(self, a: Small) -> Small {
    Small((97 - a.0) % 97)
  }
  fn mul(self, a: Small, b: Small) -> Small {
    Small(a.0 * b.0 % 97)
  }
  fn inverse(self, a: Small) -> Option<Small> {
    (1..97).map(Small).find(|&b| self.mul(a, b) == Small(1))
  }
}

fn snapshot<B: FieldBackend>(record: &Execution<B>) -> Value {
  json!({"output": record.output,
        "queries": record.queries.iter().collect::<Vec<_>>(),
        "memory": record.memory, "instructions": record.instructions})
}

fn program(
  modulus: u64,
  functions: Value,
  params: Value,
  result: Value,
) -> Program {
  serde_json::from_value(json!({
        "version": 2, "modulus": modulus, "enums": [], "tables": [], "maps": [],
        "functions": functions,
        "entries": [{"name": "main", "function": 0, "inputs": params, "output": result}]
    }))
    .unwrap()
}

fn differential<B: FieldBackend>(field: B) {
  let f = json!({"kind":"field"});
  let tuple = json!({"kind":"tuple", "items":[f,f,f,f]});
  let mut source = program(
    field.modulus(),
    json!([
        {"name":"main", "params":[f], "result":tuple, "registers":11, "code":[
            {"op":"call","function":1,"args":[0],"dest":[1]},
            {"op":"call","function":1,"args":[0],"dest":[2]},
            {"op":"store","type":f,"value":[1],"dest":3},
            {"op":"store","type":f,"value":[2],"dest":4},
            {"op":"load","type":f,"pointer":3,"dest":[5]},
            {"op":"literal","value":2,"dest":6},
            {"op":"binary","operator":"div","left":0,"right":6,"dest":7},
            {"op":"neg","source":7,"dest":8},
            {"op":"binary","operator":"add","left":7,"right":8,"dest":9},
            {"op":"hint","channel":"double","type":f,"key_type":f,"key":[0],"dest":[10]},
            {"op":"assert_eq","left":[1],"right":[5]},
            {"op":"ret","value":[2,7,9,10]}]},
        {"name":"leaf","params":[f],"result":f,"registers":2,"code":[
            {"op":"call","function":2,"args":[0],"dest":[1]},
            {"op":"ret","value":[1]}]}
    ]),
    json!([f]),
    tuple,
  );
  source.tables = serde_json::from_value(json!([
        {"name":"xs","type":{"kind":"tuple","items":[f]},"rows":[[2],[0],[1],[3]]},
        {"name":"squares","type":f,"rows":[[4],[0],[1],[9]]}
    ]))
    .unwrap();
  source.maps = serde_json::from_value(json!([
      {"name":"square","params":[f],"result":f,"input":0,"output":1}
  ]))
  .unwrap();
  let raw = source.clone().check().unwrap();
  let native = source.check_with(field).unwrap();
  let mut raw_channels = HintChannels::new();
  raw_channels
    .insert(
      "double",
      aiur::bytecode::Type::Field,
      aiur::bytecode::Type::Field,
      |x, y| {
        y[0] = 2 * x[0];
        Ok(())
      },
    )
    .unwrap();
  let mut channels = HintChannels::new();
  channels
    .insert(
      "double",
      aiur::bytecode::Type::Field,
      aiur::bytecode::Type::Field,
      move |x: &[B::Element], y: &mut [B::Element]| {
        y[0] = field.add(x[0], x[0]);
        Ok(())
      },
    )
    .unwrap();
  let mut maps = MapOverrides::new();
  maps
    .insert("square", 1, 1, move |x: &[B::Element], y: &mut [B::Element]| {
      y[0] = field.mul(x[0], x[0]);
      // The immutable input rows are [2, 0, 1, 3], in that order.
      [2, 0, 1, 3]
        .iter()
        .position(|&v| x[0] == field.from_u64(v))
        .ok_or_else(|| "no table entry for map input".into())
    })
    .unwrap();
  let raw = raw.prepare_hint_channels(&[], &raw_channels).unwrap();
  let fallback = native.prepare_hint_channels(&[], &channels).unwrap();
  let accelerated = native
    .prepare_hint_channels(&[], &channels)
    .unwrap()
    .with_map_overrides(&maps)
    .unwrap();
  for x in 0..4 {
    let expected = raw.execute("main", vec![x]).unwrap();
    for got in [&fallback, &accelerated] {
      let got = got.execute("main", vec![field.from_u64(x)]).unwrap();
      assert_eq!(snapshot(&got), snapshot(&expected));
      assert_eq!(got.memory.len(), 1);
      assert_eq!(got.memory.get(0).unwrap().multiplicity, 3);
    }
  }
  assert!(field.decode(&[field.modulus()]).is_err());
}

#[test]
fn native_and_independent_fields_preserve_queries_memory_hints_and_tables() {
  differential(NativeField::<Goldilocks>::new());
  differential(SmallField);
  assert_eq!(std::mem::size_of::<Small>(), 4);
}

#[test]
fn native_arithmetic_matches_integer_reduction_at_boundaries() {
  let f = json!({"kind":"field"});
  let result = json!({"kind":"tuple", "items":[f,f,f,f,f]});
  let source = program(
    Goldilocks::ORDER_U64,
    json!([
        {"name":"arithmetic","params":[f,f],"result":result,"registers":7,"code":[
            {"op":"binary","operator":"add","left":0,"right":1,"dest":2},
            {"op":"binary","operator":"sub","left":0,"right":1,"dest":3},
            {"op":"binary","operator":"mul","left":0,"right":1,"dest":4},
            {"op":"binary","operator":"div","left":0,"right":1,"dest":5},
            {"op":"neg","source":0,"dest":6},
            {"op":"ret","value":[2,3,4,5,6]}]}
    ]),
    json!([f, f]),
    result,
  );
  let raw = source.clone().check().unwrap();
  let native = source.check_field::<Goldilocks>().unwrap();
  let p = Goldilocks::ORDER_U64;
  for a in [0, 1, 2, p / 2, p - 2, p - 1] {
    for b in [1, 2, 3, p / 2, p - 2, p - 1] {
      let expected = raw.execute("main", vec![a, b]).unwrap();
      let got = native
        .execute("main", native.field().decode(&[a, b]).unwrap())
        .unwrap();
      assert_eq!(snapshot(&got), snapshot(&expected));
    }
  }
  assert!(
    native.execute("main", native.field().decode(&[1, 0]).unwrap()).is_err()
  );
  assert!(raw.program().clone().check_with(SmallField).is_err());
}

#[test]
fn equal_native_representations_share_function_and_memory_rows() {
  let f = json!({"kind":"field"});
  let source = program(
    Goldilocks::ORDER_U64,
    json!([
        {"name":"root","params":[f,f],"result":f,"registers":6,"code":[
            {"op":"call","function":1,"args":[0],"dest":[2]},
            {"op":"call","function":1,"args":[1],"dest":[3]},
            {"op":"store","type":f,"value":[0],"dest":4},
            {"op":"store","type":f,"value":[1],"dest":5},
            {"op":"assert_eq","left":[4],"right":[5]},
            {"op":"ret","value":[2]}]},
        {"name":"identity","params":[f],"result":f,"registers":1,"code":[
            {"op":"ret","value":[0]}]}
    ]),
    json!([f, f]),
    f,
  );
  let native = source.check_field::<Goldilocks>().unwrap();
  let record = native
    .execute(
      "main",
      vec![Goldilocks::new(1), Goldilocks::new(Goldilocks::ORDER_U64 + 1)],
    )
    .unwrap();
  assert_eq!(record.queries.len(), 2);
  assert_eq!(
    record
      .queries
      .iter()
      .find(|(q, _)| q.function == 1)
      .unwrap()
      .1
      .multiplicity,
    2
  );
  assert_eq!(record.memory.len(), 1);
  assert_eq!(record.memory.get(0).unwrap().multiplicity, 2);
}

#[test]
fn multiplicities_remain_integers_above_the_field_order() {
  let f = json!({"kind":"field"});
  let mut code =
    vec![json!({"op":"call","function":1,"args":[0],"dest":[1]}); 100];
  code.push(json!({"op":"ret","value":[1]}));
  let source = program(
    97,
    json!([
        {"name":"root","params":[f],"result":f,"registers":2,"code":code},
        {"name":"leaf","params":[f],"result":f,"registers":1,"code":[{"op":"ret","value":[0]}]}
    ]),
    json!([f]),
    f,
  );
  let native = source.check_with(SmallField).unwrap();
  let record = native.execute("main", vec![Small(5)]).unwrap();
  assert_eq!(
    record
      .queries
      .iter()
      .find(|(q, _)| q.function == 1)
      .unwrap()
      .1
      .multiplicity,
    100
  );
  assert_eq!(record.output, [Small(5)]);
}

#[test]
fn native_and_independent_fields_populate_the_same_trace() {
  fn check<B: FieldBackend>(field: B) {
    let f = json!({"kind":"field"});
    let source = program(
      field.modulus(),
      json!([
          {"name":"main","params":[f],"result":f,"registers":5,"code":[
              {"op":"literal","dest":1,"value":1},
              {"op":"binary","operator":"add","left":0,"right":1,"dest":2},
              {"op":"literal","dest":3,"value":2},
              {"op":"binary","operator":"div","left":2,"right":3,"dest":4},
              {"op":"ret","value":[4]}]}
      ]),
      json!([f]),
      f,
    );
    let artifact: aiur::trace::TraceArtifact = serde_json::from_value(json!({
            "version":2, "modulus":field.modulus(),
            "functions":[{"name":"main","chip":"main","witnesses":4,
                "inputs":[0],"output":[3],
                "steps":[
                    {"guard":{"const":1},"action":{"op":"assign","dest":[1],
                        "values":[{"add":[{"var":0},{"const":1}]}]}},
                    {"guard":{"const":1},"action":{"op":"inverse","dest":2,"value":{"const":2}}}],
                "writes":(0..4).map(|i| json!({"column":i,"source":i,"guard":{"const":1}})).collect::<Vec<_>>() }],
            "chips":[{"name":"main","width":5,"activation":4,"inputs":[0],"output":[{"var":3}],
                "constraints":[
                    {"mul":[{"var":4},{"sub":[{"var":3},{"mul":[{"var":1},{"var":2}]}]}]},
                    {"mul":[{"var":4},{"sub":[{"var":1},{"add":[{"var":0},{"const":1}]}]}]},
                    {"mul":[{"var":4},{"sub":[{"mul":[{"var":2},{"const":2}]},{"const":1}]}]},
                    {"mul":[{"var":4},{"sub":[{"var":4},{"const":1}]}]}],
                "sends":[],"memory":[]}]
        })).unwrap();
    let raw = source.clone().check().unwrap();
    let native = source.check_with(field).unwrap();
    let plan = aiur::trace::TracePlan::new(&native, artifact.clone()).unwrap();
    let raw_plan = aiur::trace::TracePlan::new(&raw, artifact).unwrap();
    for x in [0, 1, 2, field.modulus() - 1] {
      let args = [field.from_u64(x)];
      let record = native.execute("main", args.to_vec()).unwrap();
      let trace = plan.generate(&record, "main", &args, true).unwrap();
      assert_eq!(
        trace,
        plan.generate_reference(&record, "main", &args, true).unwrap()
      );
      plan.check(&record, &trace, "main", &args).unwrap();
      let raw_record = raw.execute("main", vec![x]).unwrap();
      assert_eq!(
        serde_json::to_value(trace).unwrap(),
        serde_json::to_value(
          raw_plan.generate(&raw_record, "main", &[x], true).unwrap()
        )
        .unwrap()
      );
    }
  }
  check(NativeField::<Goldilocks>::new());
  check(SmallField);
}
