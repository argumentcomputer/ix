//! The exported population description, evaluated independently, gives the
//! prover's physical rows.
use super::*;
use crate::Execution;
use crate::trace::describe::{ExternalReads, HintSite, PopulationDescription};
use rustc_hash::FxHashMap;

struct RecordReads<'r> {
  program: &'r CheckedProgram,
  record: &'r Execution,
  memory: FxHashMap<Vec<u64>, usize>,
}

impl<'r> RecordReads<'r> {
  fn new(program: &'r CheckedProgram, record: &'r Execution) -> Self {
    let memory = record
      .memory
      .iter()
      .map(|m| (m.cell.value.to_vec(), m.address))
      .collect();
    Self { program, record, memory }
  }
}

impl ExternalReads for RecordReads<'_> {
  fn call(
    &mut self,
    callee: &str,
    args: &[u64],
    output: &mut [u64],
  ) -> Result<(), String> {
    let id = self
      .program
      .program
      .functions
      .iter()
      .position(|f| f.name == callee)
      .ok_or("unknown callee")?;
    let table = &self.record.queries.tables[id];
    let query = table.lookup(args).1.ok_or("missing recorded callee")?;
    output.copy_from_slice(table.output(query).output);
    Ok(())
  }
  fn map(
    &mut self,
    map: usize,
    args: &[u64],
    output: &mut [u64],
  ) -> Result<(), String> {
    let program = &self.program.program;
    let map = &program.maps[map];
    let row = program.tables[map.input]
      .rows
      .iter()
      .position(|row| row == args)
      .ok_or("no table entry for map input")?;
    output.copy_from_slice(&program.tables[map.output].rows[row]);
    Ok(())
  }
  fn store(&mut self, _: usize, values: &[u64]) -> Result<u64, String> {
    self
      .memory
      .get(values)
      .map(|&a| a as u64)
      .ok_or("missing recorded store".into())
  }
  fn load(
    &mut self,
    width: usize,
    address: u64,
    output: &mut [u64],
  ) -> Result<(), String> {
    let cell = &self
      .record
      .memory
      .get_by_width(width, address as usize)
      .ok_or("missing recorded load")?
      .cell;
    output.copy_from_slice(cell.value);
    Ok(())
  }
  fn hint(
    &mut self,
    site: &HintSite,
    key: &[u64],
    output: &mut [u64],
  ) -> Result<(), String> {
    let function = self
      .program
      .program
      .functions
      .iter()
      .position(|f| f.name == site.function)
      .ok_or("unknown hint function")?;
    self.record.hints.sites[function][site.instruction]
      .as_ref()
      .ok_or("missing hint site")?
      .evaluate(key, output, self.program.field)
  }
}

/// Every row the reference evaluator derives from `description` equals the
/// prover's stage-one row, including placement and zero padding.
fn assert_rows_match(
  program: &CheckedProgram,
  plan: &TracePlan<'_>,
  description: &PopulationDescription,
  record: &Execution,
  entry: &str,
  args: &[u64],
) {
  let backend = host_lookups(plan);
  let traces = backend.generate_stage_1(record, entry, args).unwrap();
  assert_eq!(description.circuits.len(), backend.members.len());
  let mut reads = RecordReads::new(program, record);
  for (ci, circuit) in description.circuits.iter().enumerate() {
    let members: Vec<_> = circuit.members.iter().map(|m| m.function).collect();
    assert_eq!(members, backend.members[ci]);
    let trace = &traces[ci];
    assert_eq!(trace.width, circuit.width);
    let mut r = 0;
    for member in &circuit.members {
      let function = &description.functions[member.function];
      let table = &record.queries.tables[member.function];
      for query in 0..table.len() {
        let mut row = vec![0u64; circuit.width];
        let output = table.output(query);
        function
          .evaluate(
            description.modulus,
            table.input(query),
            output.output,
            &mut reads,
            |column, value| row[member.columns[column]] = value,
          )
          .unwrap();
        member.finish(description.modulus, &mut row, output.multiplicity);
        let expected: Vec<_> = trace
          .row_slice(r)
          .unwrap()
          .iter()
          .map(|v| v.as_canonical_u64())
          .collect();
        assert_eq!(row, expected, "{} row {r}", circuit.name);
        r += 1;
      }
    }
    for padding in r..trace.height() {
      assert!(
        trace.row_slice(padding).unwrap().iter().all(|v| *v == Val::ZERO)
      );
    }
  }
}

fn check(
  program: &CheckedProgram,
  artifact: TraceArtifact,
  entry: &str,
  args: &[u64],
  hints: &[crate::hints::HintEntry],
) -> PopulationDescription {
  let plan = TracePlan::new(program, artifact.clone()).unwrap();
  let description = plan.describe().unwrap();
  let json = serde_json::to_string(&description).unwrap();
  let decoded: PopulationDescription = serde_json::from_str(&json).unwrap();
  assert_eq!(decoded, description);
  assert_eq!(plan.describe().unwrap().fingerprint(), description.fingerprint());
  // The description is a property of the plan, not of the field backend.
  let native = program.program().clone().check_field::<Val>().unwrap();
  let native_plan = TracePlan::new(&native, artifact).unwrap();
  assert_eq!(native_plan.describe().unwrap(), description);
  let record = program.execute_with_hints(entry, args.to_vec(), hints).unwrap();
  assert_rows_match(program, &plan, &description, &record, entry, args);
  description
}

#[test]
fn description_rows_match_calls_maps_and_memory() {
  let (program, artifact) = fixture();
  let description = check(&program, activate(artifact), "root", &[3], &[]);
  assert_eq!(description.maps[0].name, "square");
  let (program, artifact) = mixed_memory();
  check(&program, activate(artifact), "root", &[5, 6, 7], &[]);
}

#[test]
fn description_rows_match_grouped_placements() {
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
  let program = package.program.check().unwrap();
  let description =
    check(&program, package.trace.clone(), "Grouped::run", &[3], &[]);
  assert!(description.circuits.iter().any(|c| c.members.len() == 3));
  let mut plain = package.trace;
  plain.groups.clear();
  let ungrouped = check(&program, plain, "Grouped::run", &[3], &[]);
  assert_ne!(ungrouped.fingerprint(), description.fingerprint());
}

/// Guarded inverses, choices, failure witnesses and hints, with an inactive
/// hint that has no provider answer.
#[test]
fn description_rows_match_guards_witnesses_and_hints() {
  let program: Program = serde_json::from_value(json!({
    "version":1,"modulus":Val::ORDER_U64,"enums":[],
    "maps":[{"name":"sq","params":[f()],"result":f(),"input":0,"output":1}],
    "tables":[
      {"name":"xs","type":{"kind":"tuple","items":[f()]},"rows":[[4],[9]]},
      {"name":"ys","type":f(),"rows":[[16],[81]]}],
    "functions":[{"name":"root","params":[f()],"result":f(),"registers":2,"code":[
      {"op":"hint","channel":"half","type":f(),"key_type":f(),"key":[0],"dest":[1]},
      {"op":"ret","value":[0]}]}],
    "entries":[{"name":"root","function":0,"inputs":[f()],"output":f()}]
  }))
  .unwrap();
  let program = program.check().unwrap();
  let sub = |a: Json, b: Json| json!({"sub":[a, b]});
  let artifact = activate(raw_artifact(json!({
    "version":1,"modulus":Val::ORDER_U64,
    "functions":[{"name":"root","chip":"root","witnesses":10,"inputs":[0],"output":[1],
      "steps":[
        step(json!({"op":"choose","dest":[2,3],"tests":[[sub(v(0), k(4))],[]]})),
        {"guard":v(3),"action":{"op":"inverse","dest":4,"value":sub(v(0), k(4))}},
        {"guard":v(3),"action":{"op":"failure","dest":[5,6],
          "differences":[sub(v(0), k(4)), k(1)]}},
        {"guard":v(2),"action":{"op":"hint","channel":"half","instruction":0,
          "type":f(),"key_type":f(),"key":[v(0)],"dest":[7]}},
        step(json!({"op":"assign","dest":[8],"values":[{"mul":[v(7), v(4)]}]})),
        step(json!({"op":"call","name":"sq","args":[v(0)],"dest":[9]}))],
      "writes":writes(10)}],
    "chips":[{"name":"root","width":10,"inputs":[0],"output":[v(1)],
      "constraints":[],"sends":[],"memory":[]}]
  })));
  let hints: Vec<crate::hints::HintEntry> = serde_json::from_value(json!([
    {"channel":"half","type":f(),"key_type":f(),"key":[4],"output":[2]},
    {"channel":"half","type":f(),"key_type":f(),"key":[9],"output":[5]}]))
  .unwrap();
  for x in [4, 9] {
    let description = check(&program, artifact.clone(), "root", &[x], &hints);
    assert!(description.functions[0].kernels.iter().any(|k| matches!(
      &k.node,
      crate::trace::describe::NodeDescription::Map { map: 0, .. }
    )));
  }
}
