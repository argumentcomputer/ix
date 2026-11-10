//! Emission from the grouped fixture shared with `aiur`'s own tests.
use aiur_tracegen::cuda::{Selection, emit};

use aiur::trace::TraceArtifact;

const FIXTURE: &str =
  concat!(env!("CARGO_MANIFEST_DIR"), "/../aiur/tests/fixtures/grouping.ixa");

fn fixture() -> (aiur::Program, TraceArtifact) {
  let (package, _) =
    aiur::artifact::Package::load(std::path::Path::new(FIXTURE)).unwrap();
  package.traced().unwrap()
}

fn describe(
  (program, trace): (aiur::Program, TraceArtifact),
) -> aiur_tracegen::Described {
  aiur_tracegen::describe(&program.check().unwrap(), trace).unwrap()
}

#[test]
fn emits_supported_circuits_and_explains_the_rest() {
  let artifact = describe(fixture());
  let emitted = emit(&artifact, &Selection::All, "fixture").unwrap();
  assert!(!emitted.circuits.is_empty());
  assert!(
    emitted
      .skipped
      .iter()
      .any(|(_, reason)| reason.starts_with("reads the ROM"))
  );
  for circuit in &emitted.circuits {
    assert!(circuit.symbol.starts_with("aiur_tracegen_fixture_"));
    assert!(
      circuit.source.contains(&format!("extern \"C\" int {}(", circuit.symbol))
    );
  }
  // Emission is deterministic, so cached objects are reused.
  let again = emit(&artifact, &Selection::All, "fixture").unwrap();
  assert_eq!(again.circuits, emitted.circuits);
  // A named circuit must be supported.
  let (skipped, _) = &emitted.skipped[0];
  assert!(
    emit(&artifact, &Selection::Named(vec![skipped.clone()]), "fixture")
      .is_err()
  );
  assert!(
    emit(&artifact, &Selection::Named(vec!["missing".into()]), "fixture")
      .is_err()
  );
  let named = Selection::Named(vec![emitted.circuits[0].name.clone()]);
  assert_eq!(emit(&artifact, &named, "fixture").unwrap().circuits.len(), 1);
  assert!(emit(&artifact, &Selection::All, "not an identifier").is_err());
}

#[test]
fn fingerprint_covers_plans_and_placement() {
  let original = describe(fixture());
  let (program, mut trace) = fixture();
  trace.groups.clear();
  assert_ne!(original.fingerprint, describe((program, trace)).fingerprint);
  let (program, mut trace) = fixture();
  trace.functions[1].writes.reverse();
  assert_ne!(original.fingerprint, describe((program, trace)).fingerprint);
  assert_eq!(original.fingerprint, describe(fixture()).fingerprint);
}

#[test]
fn sources_carry_the_preamble_and_fingerprint() {
  let described = describe(fixture());
  let files =
    aiur_tracegen::bundle::sources(&described, "fixture", "// Header.\n")
      .unwrap();
  let emitted = emit(&described, &Selection::All, "fixture").unwrap();
  assert_eq!(files.len(), emitted.circuits.len() + 1);
  let fingerprint =
    format!("// Population fingerprint {}", described.fingerprint);
  for (name, contents) in &files {
    assert!(contents.starts_with("// Header.\n"), "{name}");
    assert!(contents.lines().nth(1).unwrap().starts_with(&fingerprint));
  }
  let (_, binding) = files.last().unwrap();
  assert!(binding.contains("pub static BUNDLE"));
  for circuit in &emitted.circuits {
    assert!(binding.contains(&circuit.symbol));
  }
  assert!(
    aiur_tracegen::bundle::sources(&described, "fixture", "not a comment\n")
      .is_err()
  );
}
