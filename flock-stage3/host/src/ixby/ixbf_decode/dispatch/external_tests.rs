//! AST-free dispatch over retained original files. Each new control row and
//! selected codec/grammar row is checked against its Boolean relation. These
//! large-source differentials are NOT the 1 KiB source-authenticated proof.
use super::super::{
  GrammarKind, RecordKind, external_tests as fixtures, grammar,
};
use super::model_tests::*;
use crate::ixby::ixbf;
use flock_prover::field::F128;
use std::ffi::OsStr;

fn check_program(model: &Model, bytes: &[u8]) -> Parsed {
  let parsed = model.parse(bytes, [F128::ZERO; 15], 100_000).unwrap();
  // The independent model is read only AFTER dispatch. It cannot select a
  // decoder, source cursor, event, payload length or next grammar state.
  let artifact =
    ixbf::decode_program(bytes, ixbf::DecodeLimits::default()).unwrap();
  let header = fixtures::expected_header(&artifact);
  assert_eq!(
    &parsed.state[grammar::LIMITS..grammar::LIMITS + 10],
    &header[..10]
  );
  assert_eq!(parsed.state[grammar::FUEL], header[10]);
  assert_eq!(parsed.state[grammar::ENTRY], header[11]);
  assert_eq!(parsed.state[grammar::CTORS], header[12]);
  assert_eq!(
    parsed.state[grammar::FUNCTIONS],
    F128::new(artifact.functions().len() as u64, 0)
  );
  assert_eq!(
    parsed.state[grammar::FUNCTION_INDEX],
    parsed.state[grammar::FUNCTIONS]
  );
  assert_eq!(
    parsed.state[grammar::ENTRY_ARITY],
    fixtures::word(&artifact.functions()[artifact.entry()].arity)
  );
  let inventory = artifact.inventory();
  assert_eq!(
    parsed.events[RecordKind::Constructor as usize],
    inventory.constructors
  );
  assert_eq!(parsed.events[RecordKind::Function as usize], inventory.functions);
  assert_eq!(parsed.events[RecordKind::Block as usize], inventory.blocks);
  assert_eq!(
    parsed.events[RecordKind::Operation as usize],
    inventory.operations.iter().sum()
  );
  assert_eq!(
    parsed.events[RecordKind::Scalar as usize],
    inventory.scalars.iter().map(|s| s.literals).sum()
  );
  assert_eq!(parsed.events[14], inventory.scalars[0].literals);
  assert_eq!(parsed.events[13], 1);
  assert_eq!(parsed.events[17], 1);
  parsed
}
fn check_forest(parsed: &Parsed, forest: &ixbf::ValueForest<'_>) {
  assert_eq!(
    parsed.state[grammar::SEEN],
    F128::new(forest.nodes().len() as u64, 0)
  );
  assert_eq!(parsed.events[RecordKind::Value as usize], forest.nodes().len());
  let mut scalars = 0;
  let mut nats = 0;
  let mut strings = 0;
  let mut bytes = 0;
  for node in forest.nodes() {
    if let ixbf::ValueKind::Scalar(s) = &node.kind {
      scalars += 1;
      match s {
        ixbf::Scalar::Nat(_) => nats += 1,
        ixbf::Scalar::String(s) => strings += usize::from(!s.is_empty()),
        ixbf::Scalar::Bytes(b) => bytes += usize::from(!b.is_empty()),
        _ => {},
      }
    }
  }
  assert_eq!(parsed.events[11], scalars);
  assert_eq!(parsed.events[14], nats);
  assert_eq!(parsed.events[15], strings);
  assert_eq!(parsed.events[16], bytes);
}

#[test]
#[ignore = "requires the independent compiler corpus and exact retained Init program/input/output"]
fn original_corpus_and_full_init_dispatch_without_an_ast_schedule() {
  let model = Model::new(config(GrammarKind::Program), true);
  let directory = fixtures::path("IXBY_IXBF_CORPUS");
  let mut files: Vec<_> = std::fs::read_dir(&directory)
    .unwrap()
    .map(|e| e.unwrap().path())
    .filter(|p| p.is_file() && p.extension() == Some(OsStr::new("ixby")))
    .collect();
  files.sort();
  assert!(files.len() >= 81);
  let mut census = [0; 18];
  let mut steps = 0;
  for file in &files {
    let parsed = check_program(&model, &fixtures::read(file));
    for (total, n) in census.iter_mut().zip(parsed.events) {
      *total += n;
    }
    steps += parsed.steps;
  }
  eprintln!(
    "AST-free corpus dispatcher: files={} steps={steps} events={census:?}",
    files.len()
  );
  let image = fixtures::read(&fixtures::path("IXBY_IXBF_STAGE2_IMAGE"));
  assert_eq!(
    blake3::hash(&image).to_hex().as_str(),
    "a661dfede7c18bfb915d031393ffb258e65c21940d48039cdf44ab16428fe301"
  );
  let parsed = check_program(&model, &image);
  assert_eq!(parsed.events[3], 146);
  assert_eq!(parsed.events[4], 681);
  assert_eq!(parsed.events[5], 6763);
  assert_eq!(parsed.events[14], 608);
  // Six ByteArray scalars include three empty payloads; their count record
  // completes the grammar event without a zero-progress payload row.
  assert_eq!(parsed.events[16], 3);
  assert_eq!(parsed.steps, 37_879);
  eprintln!(
    "AST-free exact Init dispatcher: bytes={} steps={} events={:?}",
    image.len(),
    parsed.steps,
    parsed.events
  );
  let artifact =
    ixbf::decode_program(&image, ixbf::DecodeLimits::default()).unwrap();
  for (kind, variable, expected_hash) in [
    (
      GrammarKind::Input,
      "IXBY_IXBF_INIT_INPUT",
      "713a6a0b72dbaad673192c38c6e10115b1386482394cc22a945837c1a03f11c8",
    ),
    (
      GrammarKind::Output,
      "IXBY_IXBF_INIT_OUTPUT",
      "3e6cb8264cfb6d253c41f22aa05221805a58f857d73877305adfed0781115a28",
    ),
  ] {
    let bytes = fixtures::read(&fixtures::path(variable));
    assert_eq!(blake3::hash(&bytes).to_hex().as_str(), expected_hash);
    let output = Model::new(config(kind), true)
      .parse(&bytes, context(&parsed.state), 100_000)
      .unwrap();
    if kind == GrammarKind::Input {
      check_forest(
        &output,
        ixbf::decode_input(&artifact, &bytes, ixbf::DecodeLimits::default())
          .unwrap()
          .values(),
      );
    } else {
      check_forest(
        &output,
        ixbf::decode_output(&artifact, &bytes, ixbf::DecodeLimits::default())
          .unwrap()
          .values(),
      );
    }
    eprintln!(
      "AST-free exact Init {kind:?}: bytes={} steps={} events={:?}",
      bytes.len(),
      output.steps,
      output.events
    );
  }
}
