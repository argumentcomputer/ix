//! A generated executor of a program with depth circuits records every
//! query's call height as the interpreter does, through mutual recursion
//! (`even`/`odd`, `owned`/`link`), cache hits within an SCC (`fib`, and in
//! `tests/fixtures/heights.json` cache hits that set a height) and calls
//! from outside an SCC (`run`, `top`), so its record proves.
use aiur::artifact::Package;
use aiur::bytecode::CheckedProgram;
use aiur::execute::Execution;
use aiur::native::{outcome_diff, record_diff};
use aiur::trace::{
  TraceArtifact, TracePlan,
  stark::{Backend, Parameters},
};

#[allow(warnings, clippy::all, clippy::pedantic)]
mod generated {
  include!(concat!(env!("OUT_DIR"), "/depth.rs"));
}
use generated::Depth;

fn fixture() -> (CheckedProgram, TraceArtifact) {
  let (program, trace) =
    Package::decode(include_bytes!("../../aiur/tests/fixtures/depth.ixa"))
      .and_then(Package::traced)
      .unwrap();
  let mut program = program.check().unwrap();
  program.track_depth(&trace).unwrap();
  (program, trace)
}

fn parameters() -> Parameters {
  Parameters {
    log_blowup: 1,
    num_queries: 220,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
  }
}

/// The count of `function(args)` in `record`, if it was queried.
fn multiplicity(
  record: &Execution,
  function: usize,
  args: &[u64],
) -> Option<u64> {
  record
    .queries
    .iter()
    .find(|(key, _)| key.function == function && key.args == args)
    .map(|(_, output)| output.multiplicity)
}

/// Every query's height and count agree, read through the public record.
fn same_heights(program: &CheckedProgram, a: &Execution, b: &Execution) {
  assert_eq!(a.queries.len(), b.queries.len());
  for (key, output) in a.queries.iter() {
    let name = program.callable_name(key.function).unwrap();
    assert_eq!(
      multiplicity(b, key.function, &key.args),
      Some(output.multiplicity),
      "{name}{:?}",
      key.args
    );
    assert_eq!(
      a.query_depth(key.function, &key.args),
      b.query_depth(key.function, &key.args),
      "{name}{:?}",
      key.args
    );
  }
}

/// The argument at distance `n` (`n <= 190`, below the multiplicative order
/// `192` of `2` in Goldilocks) from `target` under `x -> x * 2`.
fn at_distance(target: u64, n: u32) -> u64 {
  const P: u128 = 0xffff_ffff_0000_0001;
  const INV2: u128 = (P + 1) / 2;
  let mut x = u128::from(target) % P;
  for _ in 0..n {
    x = (x * INV2) % P;
  }
  u64::try_from(x).unwrap()
}

fn at(n: u32) -> u64 {
  at_distance(4096, n)
}

fn owned_at(n: u32) -> u64 {
  at_distance(64, n)
}

#[test]
fn native_heights_match_the_interpreter() {
  let (program, _) = fixture();
  assert!(program.records_depth());
  let prepared = program.prepare_hints(&[]).unwrap();
  let native = prepared.bind_native::<Depth>().unwrap();
  let run_inputs = [0, 1, 2, 3, 7, 12, 30].map(at);
  let fib_inputs = [0, 1, 2, 10].map(at);
  let top_inputs = [0, 1, 5, 9].map(owned_at);
  let cases: &[(&str, &[u64])] = &[
    ("Depth::run", &run_inputs),
    ("Depth::fib", &fib_inputs),
    ("Depth::top", &top_inputs),
    ("Depth::loop", &[0, 3]),
  ];
  let mut successes = 0;
  for (entry, inputs) in cases {
    for &x in *inputs {
      let a = prepared.execute(entry, vec![x]);
      let b = native.execute(entry, vec![x]);
      outcome_diff(&a, &b).unwrap_or_else(|e| panic!("{entry}({x}): {e}"));
      if let (Ok(a), Ok(b)) = (&a, &b) {
        same_heights(&program, a, b);
        successes += 1;
      }
    }
  }
  assert_eq!(successes, 15);

  let record = native.execute("Depth::run", vec![at(12)]).unwrap();
  let fib = program.callable_id("Depth::fib").unwrap();
  let even = program.callable_id("Depth::even").unwrap();
  let odd = program.callable_id("Depth::odd").unwrap();
  // fib at distance n calls distance n - 1, then hits the cache for n - 2.
  assert_eq!(record.query_depth(fib, &[at(12)]), Some(11));
  assert_eq!(record.query_depth(fib, &[at(1)]), Some(0));
  assert_eq!(multiplicity(&record, fib, &[at(10)]), Some(2));
  // even and odd share an SCC: every call between them adds one.
  assert_eq!(record.query_depth(even, &[at(12)]), Some(12));
  assert_eq!(record.query_depth(odd, &[at(11)]), Some(11));

  let top = native.execute("Depth::top", vec![owned_at(5)]).unwrap();
  let owned = program.callable_id("Depth::owned").unwrap();
  let link = program.callable_id("Depth::link").unwrap();
  assert_eq!(top.query_depth(owned, &[owned_at(5)]), Some(10));
  assert_eq!(top.query_depth(link, &[owned_at(4)]), Some(9));
  let top_id = program.callable_id("Depth::top").unwrap();
  assert_eq!(top.query_depth(top_id, &[owned_at(5)]), Some(0));
}

/// Without depth circuits nothing is recorded, and the comparison sees the
/// missing heights.
#[test]
fn untracked_records_differ_from_tracked_ones() {
  let (program, _) = fixture();
  let untracked = program.program().clone().check().unwrap();
  assert!(!untracked.records_depth());
  let prepared = untracked.prepare_hints(&[]).unwrap();
  let native = prepared.bind_native::<Depth>().unwrap();
  let x = at(12);
  let plain = native.execute("Depth::run", vec![x]).unwrap();
  record_diff(&prepared.execute("Depth::run", vec![x]).unwrap(), &plain)
    .unwrap();
  let tracked = program.execute("Depth::run", vec![x]).unwrap();
  let error = record_diff(&tracked, &plain).unwrap_err();
  assert!(error.contains("heights"), "{error}");
}

#[test]
fn native_record_proves_like_the_interpreters() {
  let (program, trace) = fixture();
  let plan = TracePlan::new(&program, trace).unwrap();
  let prepared = program.prepare_hints(&[]).unwrap();
  let native = prepared.bind_native::<Depth>().unwrap();
  let entry = "Depth::run";
  let x = at(12);
  let interpreted = prepared.execute(entry, vec![x]).unwrap();
  let generated = native.execute(entry, vec![x]).unwrap();
  assert_eq!(generated.output, [145]);
  let trace = plan.generate(&generated, entry, &[x], true).unwrap();
  plan.check(&generated, &trace, entry, &[x]).unwrap();
  assert_eq!(trace, plan.generate(&interpreted, entry, &[x], true).unwrap());

  let backend = Backend::new(&plan, parameters()).unwrap();
  let witness = backend.generate(&generated, entry, &[x]).unwrap();
  let reference = backend.generate(&interpreted, entry, &[x]).unwrap();
  for (a, b) in witness.traces.iter().zip(&reference.traces) {
    assert_eq!(a.values, b.values);
  }
  let proof = backend.prove(entry, &[x], &generated.output, witness).unwrap();
  backend.verify(entry, &[x], &generated.output, &proof).unwrap();
}

#[allow(warnings, clippy::all, clippy::pedantic)]
mod heights {
  include!(concat!(env!("OUT_DIR"), "/heights.rs"));
}

/// `tests/fixtures/heights.json`, recording heights as if its functions'
/// circuits had depth words in the SCCs `ranks` (`None`: no depth word).
/// `revfib(n)` calls `revfib(n - 2)` before `revfib(n - 1)`, so the latter's
/// height comes from cache hits alone; `outer(n)` calls `revfib(n)` twice,
/// `even(n)`, and then `odd(n + 1)`, whose call to `even(n)` is a cache hit.
fn heights(ranks: [Option<u64>; 4]) -> CheckedProgram {
  use serde_json::json;
  let program: aiur::Program =
    serde_json::from_slice(include_bytes!("fixtures/heights.json")).unwrap();
  let mut program = program.check().unwrap();
  let names = ["revfib", "even", "odd", "outer"];
  let functions: Vec<_> = names
    .iter()
    .map(|name| {
      json!({
        "name": name, "chip": name, "witnesses": 0, "inputs": [],
        "output": [], "steps": [], "writes": []
      })
    })
    .collect();
  let chips: Vec<_> = names
    .iter()
    .zip(ranks)
    .map(|(name, rank)| {
      json!({
        "name": name, "width": 1, "activation": 0, "inputs": [],
        "output": [], "constraints": [], "sends": [], "memory": [],
        "depth": { "column": rank.map(|_| 0), "rank": rank.unwrap_or(0) }
      })
    })
    .collect();
  let trace: TraceArtifact = serde_json::from_value(json!({
    "version": 1,
    "modulus": program.field().modulus(),
    "functions": functions,
    "chips": chips,
  }))
  .unwrap();
  program.track_depth(&trace).unwrap();
  program
}

/// Runs every entry of the heights fixture natively and interpreted, and
/// returns the native record of `outer(6)`.
fn native_heights(program: &CheckedProgram) -> Execution {
  use aiur::field::FieldBackend;
  let prepared = program.prepare_hints(&[]).unwrap();
  let native = prepared.bind_native::<heights::Heights>().unwrap();
  for entry in ["revfib", "even", "outer"] {
    for x in [0, 1, 2, 3, 6, 11] {
      let args = vec![program.field().from_u64(x)];
      let a = prepared.execute(entry, args.clone()).unwrap();
      let b = native.execute(entry, args).unwrap();
      record_diff(&a, &b).unwrap_or_else(|e| panic!("{entry}({x}): {e}"));
      same_heights(program, &a, &b);
    }
  }
  native.execute("outer", vec![6]).unwrap()
}

#[test]
fn cache_hits_within_an_scc_raise_heights() {
  let (revfib, even, odd, outer) = (0, 1, 2, 3);
  let separate = native_heights(&heights([Some(0), Some(1), Some(1), None]));
  // revfib(n) has height n - 1; revfib(5)'s callees were both cached.
  assert_eq!(separate.query_depth(revfib, &[6]), Some(5));
  assert_eq!(separate.query_depth(revfib, &[5]), Some(4));
  assert_eq!(separate.query_depth(even, &[6]), Some(6));
  // odd(7) only hits the cache for even(6).
  assert_eq!(separate.query_depth(odd, &[7]), Some(7));
  assert_eq!(separate.query_depth(outer, &[6]), Some(0));

  let shared = native_heights(&heights([Some(0); 4]));
  assert_eq!(shared.query_depth(outer, &[6]), Some(8));
  assert_eq!(shared.query_depth(revfib, &[5]), Some(4));

  // Calls between different SCCs never raise a height.
  let split = native_heights(&heights([Some(0), Some(1), Some(2), Some(3)]));
  assert_eq!(split.query_depth(revfib, &[6]), Some(5));
  assert_eq!(split.query_depth(even, &[6]), Some(0));
  assert_eq!(split.query_depth(odd, &[7]), Some(0));
  assert_eq!(split.query_depth(outer, &[6]), Some(0));
}

/// A generated executor records the same row references
/// ([`aiur::refs`]) as the interpreter, and recording them changes no other
/// part of the record.
#[test]
fn native_records_the_interpreters_row_references() {
  let (mut program, trace) = fixture();
  program.record_refs(|_| true, &aiur::trace::lookup_aliases(&trace));
  assert!(program.records_refs());
  let (plain, _) = fixture();
  let prepared = program.prepare_hints(&[]).unwrap();
  let native = prepared.bind_native::<Depth>().unwrap();
  for (entry, x) in [("Depth::run", 12), ("Depth::top", 5)] {
    let a = prepared.execute(entry, vec![x]).unwrap();
    let b = native.execute(entry, vec![x]).unwrap();
    record_diff(&a, &b).unwrap_or_else(|e| panic!("{entry}({x}): {e}"));
    assert!(a.storage_usage().query_refs_bytes > 0, "{entry}: no references");
    let without = plain.execute(entry, vec![x]).unwrap();
    let error = record_diff(&a, &without).unwrap_err();
    assert!(error.contains("references"), "{entry}: {error}");
  }
}
