//! Compiled writers (`AIUR_GPU_TRACE=compiled`) against host population on
//! `aiur`'s fixtures: every compiled tile's words, and proof bytes, which
//! also cover the range tables the gap limbs use.
#![cfg(feature = "cuda")]
use aiur::{
  bytecode::CheckedProgram,
  trace::{
    TraceArtifact, TracePlan,
    stark::{Backend, Parameters},
  },
};
use multi_stark::batch::Retention;
use std::{path::Path, sync::Mutex};

/// `AIUR_GPU_TRACE` is read when a backend is built.
static ENVIRONMENT: Mutex<()> = Mutex::new(());

const PARAMETERS: Parameters = Parameters {
  log_blowup: 1,
  num_queries: 220,
  commit_proof_of_work_bits: 0,
  query_proof_of_work_bits: 0,
};

fn fixture(name: &str, depth: bool) -> (CheckedProgram, TraceArtifact) {
  let path =
    format!("{}/../aiur/tests/fixtures/{name}.ixa", env!("CARGO_MANIFEST_DIR"));
  let (package, _) = aiur::artifact::Package::load(Path::new(&path)).unwrap();
  let (program, trace) = package.traced().unwrap();
  let mut program = program.check().unwrap();
  if depth {
    program.track_depth(&trace).unwrap();
  }
  (program, trace)
}

fn backend<'p, 'a>(plan: &'p TracePlan<'a>, mode: &str) -> Backend<'p, 'a> {
  let _guard = ENVIRONMENT.lock().unwrap_or_else(|e| e.into_inner());
  // SAFETY: tests that read or write the environment hold the lock.
  unsafe { std::env::set_var("AIUR_GPU_TRACE", mode) };
  Backend::for_batch(plan, PARAMETERS).unwrap()
}

/// Checks the compiled tiles of `circuits` (at least) against the host,
/// then proves `entry(arg)` with host and compiled population for each
/// shard height in `rows` and compares the bytes.
fn compiled_matches_host(
  name: &str,
  depth: bool,
  entry: &str,
  args: &[u64],
  circuits: &[&str],
  rows: &[usize],
) {
  aiur::trace::stark::compiled::register(match name {
    "depth" => &aiur_tracegen_tests::depth::BUNDLE,
    "memory" => &aiur_tracegen_tests::memory::BUNDLE,
    _ => &aiur_tracegen_tests::grouping::BUNDLE,
  });
  let (program, trace) = fixture(name, depth);
  let plan = TracePlan::new(&program, trace).unwrap();
  let record = program.execute(entry, args.to_vec()).unwrap();
  let compiled = backend(&plan, "compiled");
  let (_, tiles, _) = compiled.check_device_tiles(&record).unwrap();
  for circuit in circuits {
    assert!(
      tiles
        .iter()
        .any(|t| t.circuit == *circuit && t.provider == "gpu_codegen"),
      "{circuit} has no compiled writer"
    );
  }
  for tile in &tiles {
    assert_eq!((tile.mismatches, tile.noncanonical), (0, 0), "{tile:?}");
  }
  let host = backend(&plan, "cpu");
  for &rows in rows {
    let layout = host.uniform_layout(&record, rows).unwrap();
    let prove = |backend: &Backend<'_, '_>, retention| {
      backend
        .prove_incremental(
          &record,
          entry,
          args,
          &record.output,
          &layout,
          retention,
        )
        .unwrap()
        .to_bytes()
        .unwrap()
    };
    let expected = prove(&host, Retention::Retain);
    for retention in [Retention::Retain, Retention::Regenerate] {
      assert_eq!(
        prove(&compiled, retention),
        expected,
        "{name} with {rows} rows, {retention:?}"
      );
    }
  }
}

/// Exact slots (`even`/`odd`, `owned`/`link`), gap slots with two limbs
/// (`fib`) and external slots (`run`).
#[test]
fn compiled_depth_circuits_match_host_population() {
  compiled_matches_host(
    "depth",
    true,
    "Depth::run",
    &[12],
    &["Depth::fib", "Depth::even", "Depth::odd", "Depth::run"],
    &[4, 64],
  );
}

/// Stores and loads of widths 0, 1 and 2, with cells shared across types.
#[test]
fn compiled_memory_circuits_match_host_population() {
  for args in [[3, 0, 7], [3, 3, 3]] {
    compiled_matches_host("memory", false, "root", &args, &["root"], &[2, 8]);
  }
}

/// A grouped circuit with ROM stores and loads.
#[test]
fn compiled_grouped_circuits_match_host_population() {
  compiled_matches_host(
    "grouping",
    false,
    "Grouped::run",
    &[3],
    &["arithmetic_and_memory"],
    &[2, 8],
  );
}
