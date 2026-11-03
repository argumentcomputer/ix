//! Emission from the grouped fixture shared with `aiur`'s own tests.
use aiur_tracegen::cuda::{Selection, emit};

const FIXTURE: &str =
  concat!(env!("CARGO_MANIFEST_DIR"), "/../aiur/tests/fixtures/grouping.json");

#[test]
fn emits_supported_circuits_and_explains_the_rest() {
  let bytes = std::fs::read(FIXTURE).unwrap();
  let artifact = aiur_tracegen::describe(&bytes).unwrap();
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
  let bytes = std::fs::read(FIXTURE).unwrap();
  let original = aiur_tracegen::describe(&bytes).unwrap();
  let mut package: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
  package["trace"]["groups"] = serde_json::json!([]);
  let ungrouped =
    aiur_tracegen::describe(&serde_json::to_vec(&package).unwrap()).unwrap();
  assert_ne!(original.fingerprint, ungrouped.fingerprint);
  let mut package: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
  let writes =
    package["trace"]["functions"][1]["writes"].as_array_mut().unwrap();
  writes.reverse();
  let reordered =
    aiur_tracegen::describe(&serde_json::to_vec(&package).unwrap()).unwrap();
  assert_ne!(original.fingerprint, reordered.fingerprint);
  assert_eq!(
    original.fingerprint,
    aiur_tracegen::describe(&bytes).unwrap().fingerprint
  );
}
