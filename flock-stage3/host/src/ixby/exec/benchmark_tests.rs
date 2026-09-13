//! Stage 3 ONLY: complete direct scalar Exec proof/verification measurements.
//! No Stage 4 compiler, census, witness, SRS or compression is called here.
//! JSONL records are prefixed so they remain extractable from test output.

use super::{
  tests::{CAPACITY, cases},
  *,
};
use std::{
  io::{Read, Write},
  process::{Command, Stdio},
  time::{Duration, Instant},
};

const CHILD: &str = "IXBY_EXEC_BENCH_VERIFY_CHILD";
const PHASES: [ExecProvingPhaseV0; 5] = [
  ExecProvingPhaseV0::InputAssignment,
  ExecProvingPhaseV0::ExecutionWitness,
  ExecProvingPhaseV0::RowDriverPreparation,
  ExecProvingPhaseV0::NativeFlockProving,
  ExecProvingPhaseV0::ProofEncoding,
];

fn setup(backend: Blake3Backend) -> CompiledExec {
  compile_exec_profile_with_backend(
    SemanticProfile::scalar(CAPACITY).unwrap(),
    CAPACITY,
    PrimitiveSet::scalar(),
    backend,
  )
  .unwrap()
}

fn nanos(duration: Duration) -> u64 {
  duration.as_nanos().try_into().unwrap()
}

// Linux VmHWM is the cumulative process high-water mark, NOT a per-call or
// process-tree peak. The external benchmark supervisor samples the tree.
fn memory() -> (u64, u64) {
  let status = std::fs::read_to_string("/proc/self/status")
    .expect("this opt-in memory benchmark requires Linux procfs");
  let bytes = |key: &str| {
    let mut words = status
      .lines()
      .find_map(|line| line.strip_prefix(key))
      .expect("procfs memory field")
      .split_whitespace();
    let kib: u64 = words.next().unwrap().parse().unwrap();
    assert_eq!(words.next(), Some("kB"));
    kib.checked_mul(1024).unwrap()
  };
  (bytes("VmRSS:"), bytes("VmHWM:"))
}

fn bound(value: Option<&str>, default: usize, maximum: usize) -> Result<usize> {
  let n = value.map(str::parse).transpose()?.unwrap_or(default);
  ensure!((1..=maximum).contains(&n), "benchmark bound must be 1..={maximum}");
  Ok(n)
}

fn environment_bound(name: &str, default: usize, maximum: usize) -> usize {
  let value = std::env::var(name).ok();
  bound(value.as_deref(), default, maximum).expect("explicit benchmark bound")
}

fn verifier_child(backend: Blake3Backend) {
  let mut bytes = Vec::new();
  std::io::stdin().take(proof::MAX_BYTES + 33).read_to_end(&mut bytes).unwrap();
  assert!((32..=proof::MAX_BYTES as usize + 32).contains(&bytes.len()));
  let expected = ExecStatementDigest(bytes[..32].try_into().unwrap());
  let started = Instant::now();
  let compiled = setup(backend);
  let setup_ns = nanos(started.elapsed());
  let started = Instant::now();
  compiled.verify(expected, &bytes[32..]).unwrap();
  let verify_ns = nanos(started.elapsed());
  let (rss, high_water) = memory();
  eprintln!(
    "IXBY_EXEC_FRESH_V0 {setup_ns} {verify_ns} {rss} {high_water} {} {}",
    blake3::Hash::from_bytes(compiled.identities().digest()),
    rayon::current_num_threads()
  );
}

struct Fresh {
  total_ns: u64,
  setup_ns: u64,
  verify_ns: u64,
  rss_bytes: u64,
  high_water_bytes: u64,
}

fn fresh(
  test: &str,
  expected: ExecStatementDigest,
  proof: &[u8],
  identity: [u8; 32],
) -> Fresh {
  let started = Instant::now();
  let threads = rayon::current_num_threads();
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args(["--ignored", "--exact", test, "--test-threads=1", "--nocapture"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env(CHILD, "1")
    .env("RAYON_NUM_THREADS", threads.to_string())
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
  let mut input = child.stdin.take().unwrap();
  // This is the entire verifier input. No guest, input bytes, output bytes,
  // witness, trace, public-vector dump or parent-side native result is sent.
  input.write_all(&expected.0).unwrap();
  input.write_all(proof).unwrap();
  drop(input);
  let result = child.wait_with_output().unwrap();
  let total_ns = nanos(started.elapsed());
  assert!(
    result.status.success(),
    "fresh verifier failed: {}",
    String::from_utf8_lossy(&result.stderr)
  );
  let stderr = String::from_utf8(result.stderr).unwrap();
  let mut rows =
    stderr.lines().filter_map(|line| line.strip_prefix("IXBY_EXEC_FRESH_V0 "));
  let fields: Vec<_> = rows
    .next()
    .expect("one fresh-verifier record")
    .split_whitespace()
    .collect();
  assert!(rows.next().is_none());
  assert_eq!(fields.len(), 6);
  assert_eq!(fields[4], blake3::Hash::from_bytes(identity).to_hex().as_str());
  assert_eq!(fields[5].parse::<usize>().unwrap(), threads);
  Fresh {
    total_ns,
    setup_ns: fields[0].parse().unwrap(),
    verify_ns: fields[1].parse().unwrap(),
    rss_bytes: fields[2].parse().unwrap(),
    high_water_bytes: fields[3].parse().unwrap(),
  }
}

fn run(backend: Blake3Backend, test: &str) {
  if std::env::var_os(CHILD).is_some() {
    verifier_child(backend);
    return;
  }
  let cases = cases();
  assert_eq!(cases.len(), 39, "update the labelled corpus if it changes");
  let case_count =
    environment_bound("IXBY_EXEC_BENCH_CASES", cases.len(), cases.len());
  let repetitions = environment_bound("IXBY_EXEC_BENCH_REPETITIONS", 3, 8);
  let started = Instant::now();
  let compiled = setup(backend);
  let setup_ns = nanos(started.elapsed());
  let identity = compiled.identities();
  let union =
    UnionInstance::new(&compiled.shape.registry, compiled.shape.counts.clone());
  let config = compiled.params.ligerito_verifier_config().unwrap();
  assert_eq!(config.queries, [244, 79, 48]);
  assert_eq!(config.grinding_bits, [16, 16, 16]);
  let (rss, high_water) = memory();
  eprintln!(
    "IXBY_EXEC_BENCH_V0 {{\"kind\":\"setup\",\"backend\":\"{backend:?}\",\"identity\":\"{}\",\"profile\":\"{}\",\"cases\":{case_count},\"corpus_cases\":39,\"repetitions\":{repetitions},\"rayon_threads\":{},\"setup_ns\":{setup_ns},\"rss_bytes\":{rss},\"process_high_water_bytes\":{high_water},\"steps\":{},\"program_bytes_capacity\":{},\"input_bytes_capacity\":{},\"output_bytes_capacity\":{},\"nu\":{},\"virtual_m\":{},\"dense_m\":{},\"dense_words\":{},\"live_pcs_lanes\":{},\"table_rows\":{:?},\"queries\":{:?},\"grinding_bits\":{:?}}}",
    blake3::Hash::from_bytes(identity.digest()),
    blake3::Hash::from_bytes(identity.profile),
    rayon::current_num_threads(),
    CAPACITY.steps,
    CAPACITY.program.bytes,
    CAPACITY.input.bytes,
    CAPACITY.output_bytes,
    compiled.nu,
    union.m_total(),
    compiled.params.m,
    union.dense_words(),
    compiled.params.num_ntts(),
    compiled.shape.counts,
    config.queries,
    config.grinding_bits
  );
  for (case, (code, args, output)) in cases.iter().take(case_count).enumerate()
  {
    let expected = expected_statement(compiled.profile(), code, args, output);
    for repetition in 0..repetitions {
      let mut phases = Vec::with_capacity(PHASES.len());
      let began = Instant::now();
      let mut previous = began;
      let proof = compiled
        .prove_observed(expected, code, args, |phase| {
          let now = Instant::now();
          phases.push((phase, nanos(now.duration_since(previous))));
          previous = now;
        })
        .unwrap();
      let prove_ns = nanos(began.elapsed());
      assert_eq!(
        phases.iter().map(|(phase, _)| *phase).collect::<Vec<_>>(),
        PHASES
      );
      let (prove_rss, prove_high_water) = memory();
      let began = Instant::now();
      compiled.verify(expected, &proof).unwrap();
      let warm_verify_ns = nanos(began.elapsed());
      let fresh = fresh(test, expected, &proof, identity.digest());
      assert_eq!(compiled.identities(), identity);
      eprintln!(
        "IXBY_EXEC_BENCH_V0 {{\"kind\":\"sample\",\"backend\":\"{backend:?}\",\"case\":{case},\"repetition\":{repetition},\"program_hash\":\"{}\",\"input_hash\":\"{}\",\"output_hash\":\"{}\",\"statement\":\"{}\",\"program_bytes\":{},\"input_bytes\":{},\"output_bytes\":{},\"proof_bytes\":{},\"expected_statement_bytes\":32,\"prove_total_ns\":{prove_ns},\"input_assignment_ns\":{},\"execution_witness_ns\":{},\"row_driver_preparation_ns\":{},\"native_proving_including_dense_witness_ns\":{},\"proof_encoding_ns\":{},\"prove_rss_bytes\":{prove_rss},\"process_high_water_bytes\":{prove_high_water},\"warm_verify_ns\":{warm_verify_ns},\"fresh_process_total_ns\":{},\"fresh_setup_ns\":{},\"fresh_verify_ns\":{},\"fresh_rss_bytes\":{},\"fresh_process_high_water_bytes\":{}}}",
        blake3::hash(code),
        blake3::hash(args),
        blake3::hash(output),
        blake3::Hash::from_bytes(expected.0),
        code.len(),
        args.len(),
        output.len(),
        proof.len(),
        phases[0].1,
        phases[1].1,
        phases[2].1,
        phases[3].1,
        phases[4].1,
        fresh.total_ns,
        fresh.setup_ns,
        fresh.verify_ns,
        fresh.rss_bytes,
        fresh.high_water_bytes
      );
    }
  }
  let (rss, high_water) = memory();
  eprintln!(
    "IXBY_EXEC_BENCH_V0 {{\"kind\":\"complete\",\"backend\":\"{backend:?}\",\"samples\":{},\"rss_bytes\":{rss},\"process_high_water_bytes\":{high_water},\"stage4_called\":false}}",
    case_count * repetitions
  );
}

#[test]
#[ignore = "bounded Stage 3-only legacy scalar execution benchmark with real proofs and fresh verifier children; no Stage 4"]
fn legacy_scalar_exec_benchmark() {
  run(
    Blake3Backend::LegacyOptionF,
    "ixby::exec::benchmark_tests::legacy_scalar_exec_benchmark",
  );
}

#[test]
#[ignore = "bounded Stage 3-only packed scalar execution benchmark with real proofs and fresh verifier children; no Stage 4"]
fn packed_scalar_exec_benchmark() {
  run(
    Blake3Backend::PackedWordsV0,
    "ixby::exec::benchmark_tests::packed_scalar_exec_benchmark",
  );
}

#[test]
fn benchmark_bounds_and_failed_prover_progress_are_explicit() {
  assert_eq!(bound(None, 3, 8).unwrap(), 3);
  for value in ["0", "9", "-1", "", "bad"] {
    assert!(bound(Some(value), 3, 8).is_err());
  }
  assert_eq!(bound(Some("8"), 3, 8).unwrap(), 8);
  let compiled = setup(Blake3Backend::PackedWordsV0);
  let (code, args, _) = &cases()[0];
  let mut phases = Vec::new();
  assert!(
    compiled
      .prove_observed(ExecStatementDigest([0; 32]), code, args, |phase| phases
        .push(phase))
      .is_err()
  );
  assert_eq!(phases, [ExecProvingPhaseV0::InputAssignment]);
  phases.clear();
  assert!(
    compiled
      .prove_observed(
        ExecStatementDigest([0; 32]),
        &vec![0; CAPACITY.program.bytes + 1],
        args,
        |phase| phases.push(phase)
      )
      .is_err()
  );
  assert!(phases.is_empty());
}
