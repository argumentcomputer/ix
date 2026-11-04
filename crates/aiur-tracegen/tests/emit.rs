//! Emission from the grouped fixture shared with `aiur`'s own tests.
use aiur_tracegen::cuda::{Selection, emit};

use aiur::artifact::{Metadata, Package};

const FIXTURE: &str =
  concat!(env!("CARGO_MANIFEST_DIR"), "/../aiur/tests/fixtures/grouping.json");

fn fixture() -> Package {
  let (program, trace) =
    aiur::artifact::from_json(&std::fs::read(FIXTURE).unwrap()).unwrap();
  Package { program, trace, metadata: Metadata::default() }
}

fn encoded(package: &Package) -> Vec<u8> {
  aiur::artifact::encode(package).unwrap()
}

#[test]
fn emits_supported_circuits_and_explains_the_rest() {
  let artifact = aiur_tracegen::describe(&encoded(&fixture())).unwrap();
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
  let bytes = encoded(&fixture());
  let original = aiur_tracegen::describe(&bytes).unwrap();
  let mut package = fixture();
  package.trace.groups.clear();
  let ungrouped = aiur_tracegen::describe(&encoded(&package)).unwrap();
  assert_ne!(original.fingerprint, ungrouped.fingerprint);
  let mut package = fixture();
  package.trace.functions[1].writes.reverse();
  let reordered = aiur_tracegen::describe(&encoded(&package)).unwrap();
  assert_ne!(original.fingerprint, reordered.fingerprint);
  let mut package = fixture();
  package.metadata.name = "renamed".into();
  assert_eq!(
    original.fingerprint,
    aiur_tracegen::describe(&encoded(&package)).unwrap().fingerprint
  );
  assert_eq!(
    original.fingerprint,
    aiur_tracegen::describe(&bytes).unwrap().fingerprint
  );
}

#[test]
fn rejects_json_input_with_a_conversion_hint() {
  let error =
    aiur_tracegen::describe_file(std::path::Path::new(FIXTURE)).err().unwrap();
  assert!(error.contains("aiur-artifact convert"), "{error}");
}
