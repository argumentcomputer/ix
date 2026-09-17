//! Opt-in retained CSLib workload, with byte 8 of each artifact changed from
//! semantics 0 to 2. Bodies are unchanged; old proofs must be regenerated.
//! Source files are used only by the prover
//! and native differential; the independent chain verifier needs only proofs.
use super::*;
use crate::ixby::ixbf;
use std::{
  fs::{File, OpenOptions},
  io::{BufReader, Seek, SeekFrom},
  path::{Path, PathBuf},
  time::Instant,
};

const PROGRAM_BYTES: usize = 1_016_587;
const PROGRAM_HASH: &str =
  "f2f6da19991985ba4575773a62943b213d94f3678c5b95f85fb9af1025fd26d1";
const INPUT_HASH: &str =
  "84418860c872d76e77c9b7fa466d091a6f995cd1ed7a1872fb5349131aea17c3";
const OUTPUT_HASH: &str =
  "246c11e011f9a481b944ee3cdc7dc14d57b28f467e9bb6f442c30baa433a0766";

fn path(variable: &str) -> PathBuf {
  std::env::var_os(variable)
    .unwrap_or_else(|| {
      panic!("set {variable} to the explicit retained artifact")
    })
    .into()
}
fn read_pinned(variable: &str, length: usize, hash: &str) -> Vec<u8> {
  let mut bytes = Vec::new();
  File::open(path(variable))
    .unwrap()
    .take(length as u64 + 1)
    .read_to_end(&mut bytes)
    .unwrap();
  assert_eq!(bytes.len(), length);
  assert_eq!(blake3::hash(&bytes).to_hex().as_str(), hash);
  bytes
}
fn new_file(path: &Path) -> File {
  OpenOptions::new().write(true).create_new(true).open(path).unwrap()
}

fn expected_identity(
  length: usize,
  hash: &str,
  context: [F128; 15],
) -> Vec<F128> {
  let mut expected = vec![F128::new(length as u64, 0)];
  let root = blake3::Hash::from_hex(hash).unwrap();
  expected.extend(
    root
      .as_bytes()
      .as_chunks::<16>()
      .0
      .iter()
      .map(|w| crate::hash::pack_bytes(w)),
  );
  expected.extend(context);
  expected
}

/// Prover advice only. The joint verifier below derives its context from
/// actual cryptographic verification of the entire Program chain instead.
fn last_boundary_advice(file: &Path) -> [F128; 30] {
  let mut input = BufReader::new(File::open(file).unwrap());
  let mut magic = [0; 8];
  input.read_exact(&mut magic).unwrap();
  assert_eq!(&magic, CHAIN_MAGIC);
  let mut state = None;
  let mut batches = 0;
  loop {
    let mut size = [0; 4];
    input.read_exact(&mut size).unwrap();
    let size = u32::from_le_bytes(size);
    if size == 0 {
      break;
    }
    assert!(batches < MAX_BATCHES && u64::from(size) <= MAX_BYTES);
    state = Some(read_words(&mut input, 30).unwrap().try_into().unwrap());
    input.seek(SeekFrom::Current(i64::from(size))).unwrap();
    batches += 1;
  }
  let mut trailing = [0];
  assert_eq!(input.read(&mut trailing).unwrap(), 0);
  state.expect("nonempty Program chain advice")
}

#[test]
#[ignore = "requires the pinned CSLib program/input/output; runs every batch and proves complete transport grammars"]
fn retained_cslib_batches_match_reference_and_prove_transports() {
  let bytes = read_pinned("IXBY_STREAM_PROGRAM", PROGRAM_BYTES, PROGRAM_HASH);
  let s = setup(GrammarKind::Program);
  let mut stream = witness::BatchWitness::new(
    config(GrammarKind::Program),
    DEPTH,
    &bytes,
    [F128::ZERO; 15],
  )
  .unwrap();
  let mut steps = 0;
  let mut batches = 0;
  let mut events = [0usize; 18];
  let mut pages = std::collections::BTreeSet::new();
  let started = Instant::now();
  while let Some(advice) = stream.next_batch(STEPS).unwrap() {
    witness(&s, &advice);
    steps += advice.steps;
    batches += 1;
    pages.insert(advice.first_chunk);
    for (sum, count) in events.iter_mut().zip(advice.events) {
      *sum += count;
    }
  }
  assert_eq!(steps, 37_878);
  let final_state = *stream.state();
  // Neither independent grammar model nor typed host parser chose the schedule.
  let reference = test_parse_program(&bytes, 100_000).unwrap();
  assert_eq!(final_state[..28], reference);
  let artifact =
    ixbf::decode_program(&bytes, ixbf::DecodeLimits::default()).unwrap();
  assert_eq!(
    events[RecordKind::Constructor as usize],
    artifact.constructors().len()
  );
  assert_eq!(events[RecordKind::Function as usize], artifact.functions().len());
  assert_eq!(events[RecordKind::Block as usize], artifact.inventory().blocks);
  assert_eq!(events[14], 608);
  assert_eq!(events[16], 3);
  eprintln!(
    "CSLib parser native/constraint census: bytes={} steps={steps} batches={batches} source_pages={} compression_rows={} elapsed={:.3}s events={events:?}",
    bytes.len(),
    pages.len(),
    batches * 3 * (16 + DEPTH),
    started.elapsed().as_secs_f64()
  );
  let context = DISPATCH_CONTEXT_INDICES.map(|i| final_state[i]);
  for (kind, variable, length, hash) in [
    (GrammarKind::Input, "IXBY_STREAM_INPUT", 4_813_238, INPUT_HASH),
    (GrammarKind::Output, "IXBY_STREAM_OUTPUT", 49, OUTPUT_HASH),
  ] {
    let bytes = read_pinned(variable, length, hash);
    let s = setup(kind);
    let frames = prove_chain(&s, kind, &bytes, context);
    assert_eq!(frames.len(), 1);
    let expected = test_parse_transport(kind, &bytes, &reference, 100).unwrap();
    assert_eq!(frames[0].0[..28], expected);
    if kind == GrammarKind::Input {
      ixbf::decode_input(&artifact, &bytes, ixbf::DecodeLimits::default())
        .unwrap();
    } else {
      ixbf::decode_output(&artifact, &bytes, ixbf::DecodeLimits::default())
        .unwrap();
    }
    if let Some(directory) = std::env::var_os("IXBY_STREAM_PROOF_DIR") {
      let stem = if kind == GrammarKind::Input { "input" } else { "output" };
      let directory = PathBuf::from(directory);
      new_file(&directory.join(format!("{stem}.chain")))
        .write_all(&encode_chain(&frames))
        .unwrap();
      write_words(
        &mut new_file(&directory.join(format!("{stem}.expected"))),
        &chain_expected(&bytes, context),
      )
      .unwrap();
    }
  }
}

#[test]
#[ignore = "proves a disjoint shard of all pinned CSLib grammar batches into a fresh proof directory"]
fn retained_cslib_program_proof_shard() {
  let bytes = read_pinned("IXBY_STREAM_PROGRAM", PROGRAM_BYTES, PROGRAM_HASH);
  let workers: usize =
    std::env::var("IXBY_STREAM_SHARDS").unwrap().parse().unwrap();
  let worker: usize =
    std::env::var("IXBY_STREAM_SHARD").unwrap().parse().unwrap();
  assert!((1..=64).contains(&workers) && worker < workers);
  let directory = path("IXBY_STREAM_PROOF_DIR");
  assert!(directory.is_dir());
  let kind = GrammarKind::Program;
  let s = setup(kind);
  let mut stream =
    witness::BatchWitness::new(config(kind), DEPTH, &bytes, [F128::ZERO; 15])
      .unwrap();
  let mut batches = 0;
  let mut proved = 0;
  let mut steps = 0;
  while let Some(advice) = stream.next_batch(STEPS).unwrap() {
    assert!(batches < MAX_BATCHES);
    steps += advice.steps;
    if batches % workers == worker {
      let started = Instant::now();
      let w = witness(&s, &advice);
      let proof = prove(kind, &s, &w, &advice.statement, Attack::None);
      let mut output =
        new_file(&directory.join(format!("program-{batches:06}.frame")));
      output
        .write_all(&u32::try_from(proof.len()).unwrap().to_le_bytes())
        .unwrap();
      write_words(&mut output, &advice.final_state).unwrap();
      output.write_all(&proof).unwrap();
      output.sync_all().unwrap();
      proved += 1;
      eprintln!(
        "CSLib shard={worker}/{workers} batch={batches} page={} steps={} proof_bytes={} seconds={:.3}",
        advice.first_chunk,
        advice.steps,
        proof.len(),
        started.elapsed().as_secs_f64()
      );
    }
    batches += 1;
  }
  assert_eq!(steps, 37_878);
  assert!(stream.done() && proved > 0);
  writeln!(new_file(&directory.join(format!("shard-{worker:02}.done"))),
    "source={PROGRAM_HASH}\nworker={worker}\nworkers={workers}\nbatches={batches}\nsteps={steps}\nproved={proved}").unwrap();
}

#[test]
#[ignore = "verifies a complete CSLib Program parser chain using only the expected public identity and proof file"]
fn retained_cslib_program_chain_verifies_without_original_artifacts() {
  let mut input =
    BufReader::new(File::open(path("IXBY_STREAM_CHAIN")).unwrap());
  let expected =
    expected_identity(PROGRAM_BYTES, PROGRAM_HASH, [F128::ZERO; 15]);
  let started = Instant::now();
  let final_state =
    verify_chain(GrammarKind::Program, &expected, &mut input).unwrap();
  assert_eq!(final_state[grammar::CTORS], F128::new(146, 0));
  assert_eq!(final_state[grammar::FUNCTIONS], F128::new(681, 0));
  assert_eq!(final_state[grammar::FUEL], F128::new(16_000_000_000, 0));
  eprintln!(
    "CSLib complete original-file grammar proof chain verified without source files in {:.3}s; this is not an execution or registry-admission proof",
    started.elapsed().as_secs_f64()
  );
}

#[test]
#[ignore = "proves the pinned CSLib transports using untrusted Program boundary advice; requires a fresh output directory"]
fn retained_cslib_transport_proofs_from_program_boundary_advice() {
  let advice = last_boundary_advice(&path("IXBY_STREAM_CHAIN"));
  let context = DISPATCH_CONTEXT_INDICES.map(|i| advice[i]);
  let directory = path("IXBY_STREAM_PROOF_DIR");
  assert!(directory.is_dir());
  for (kind, variable, length, hash, stem) in [
    (GrammarKind::Input, "IXBY_STREAM_INPUT", 4_813_238, INPUT_HASH, "input"),
    (GrammarKind::Output, "IXBY_STREAM_OUTPUT", 49, OUTPUT_HASH, "output"),
  ] {
    let bytes = read_pinned(variable, length, hash);
    let frames = prove_chain(&setup(kind), kind, &bytes, context);
    assert_eq!(frames.len(), 1);
    let encoded = encode_chain(&frames);
    let mut output = new_file(&directory.join(format!("{stem}.chain")));
    output.write_all(&encoded).unwrap();
    output.sync_all().unwrap();
    eprintln!("CSLib {stem} complete grammar chain: {} bytes", encoded.len());
  }
}

#[test]
#[ignore = "verifies all three original CSLib grammars from proof files alone, deriving transport context from the verified Program chain"]
fn retained_cslib_all_grammars_verify_with_program_bound_context() {
  let started = Instant::now();
  let expected =
    expected_identity(PROGRAM_BYTES, PROGRAM_HASH, [F128::ZERO; 15]);
  let state = verify_chain(
    GrammarKind::Program,
    &expected,
    &mut BufReader::new(File::open(path("IXBY_STREAM_CHAIN")).unwrap()),
  )
  .unwrap();
  let context = DISPATCH_CONTEXT_INDICES.map(|i| state[i]);
  for (kind, variable, length, hash) in [
    (GrammarKind::Input, "IXBY_STREAM_INPUT_CHAIN", 4_813_238, INPUT_HASH),
    (GrammarKind::Output, "IXBY_STREAM_OUTPUT_CHAIN", 49, OUTPUT_HASH),
  ] {
    let expected = expected_identity(length, hash, context);
    verify_chain(
      kind,
      &expected,
      &mut BufReader::new(File::open(path(variable)).unwrap()),
    )
    .unwrap();
  }
  eprintln!(
    "All three original CSLib grammars verified in {:.3}s with transport context derived from the verified Program chain; no source files, registry admission or execution",
    started.elapsed().as_secs_f64()
  );
}
