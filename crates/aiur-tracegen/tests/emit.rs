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
  assert!(emitted.skipped.is_empty(), "{:?}", emitted.skipped);
  // The memory circuit's stores and loads read ROM slots after its callees.
  let memory = emitted
    .circuits
    .iter()
    .find(|c| c.name == "arithmetic_and_memory")
    .unwrap();
  assert!(!memory.roms.is_empty());
  assert!(memory.source.contains("callees[slots.v[ROMS + 0u]]"));
  assert!(memory.source.contains(&format!(
    "callee_count != {}u",
    memory.callees.len() + memory.roms.len()
  )));
  for circuit in &emitted.circuits {
    assert!(circuit.symbol.starts_with("aiur_tracegen_fixture_"));
    assert!(
      circuit.source.contains(&format!("extern \"C\" int {}(", circuit.symbol))
    );
  }
  // Emission is deterministic, so cached objects are reused.
  let again = emit(&artifact, &Selection::All, "fixture").unwrap();
  assert_eq!(again.circuits, emitted.circuits);
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

fn depth_fixture() -> aiur_tracegen::Described {
  let path =
    concat!(env!("CARGO_MANIFEST_DIR"), "/../aiur/tests/fixtures/depth.ixa");
  let (package, _) =
    aiur::artifact::Package::load(std::path::Path::new(path)).unwrap();
  let (program, trace) = package.traced().unwrap();
  let mut program = program.check().unwrap();
  program.track_depth(&trace).unwrap();
  aiur_tracegen::describe(&program, trace).unwrap()
}

#[test]
fn depth_circuits_compile_with_their_depth_sections() {
  use aiur::trace::describe::DepthSlotKind;
  let described = depth_fixture();
  let d = &described.description;
  let emitted = emit(&described, &Selection::All, "depth").unwrap();
  assert!(
    !emitted.skipped.iter().any(|(_, r)| r.contains("depth")),
    "{:?}",
    emitted.skipped
  );
  let kinds: Vec<&DepthSlotKind> = d
    .circuits
    .iter()
    .flat_map(|c| &c.members)
    .flat_map(|m| &m.depth.slots)
    .map(|s| &s.kind)
    .collect();
  assert!(kinds.iter().any(|k| matches!(k, DepthSlotKind::Exact)));
  assert!(kinds.iter().any(|k| matches!(k, DepthSlotKind::External { .. })));
  assert!(
    kinds
      .iter()
      .any(|k| matches!(k, DepthSlotKind::Gap { limbs } if limbs.len() == 2))
  );
  for circuit in &d.circuits {
    let depth = circuit.members.iter().any(|m| !m.depth.is_empty());
    let Some(unit) = emitted.circuits.iter().find(|c| c.name == circuit.name)
    else {
      assert!(!depth, "{} was not compiled", circuit.name);
      continue;
    };
    for member in &circuit.members {
      let depth = &member.depth;
      if let Some(column) = depth.column {
        assert!(unit.source.contains(&format!("row[{column}] = depth;")));
      }
      for slot in &depth.slots {
        for callee in &slot.callees {
          assert!(unit.callees.contains(callee), "{}", circuit.name);
        }
        match &slot.kind {
          DepthSlotKind::Exact => {
            assert!(unit.source.contains("height + 1 != depth"));
          },
          DepthSlotKind::External { column } => {
            assert!(unit.source.contains(&format!("row[{column}] = height;")));
          },
          DepthSlotKind::Gap { limbs } => {
            for limb in limbs {
              assert!(unit.source.contains(&format!(
                "row[{}] = rest & 0x{:x}ull;",
                limb.column,
                (1u64 << limb.width) - 1
              )));
            }
          },
        }
      }
    }
  }
  let fib = Selection::Named(vec!["Depth::fib".into()]);
  assert_eq!(emit(&described, &fib, "depth").unwrap().circuits.len(), 1);
}

#[test]
fn fingerprint_covers_depth_sections() {
  let original = depth_fixture();
  let mut changed = original.description.clone();
  let member = changed
    .circuits
    .iter_mut()
    .flat_map(|c| &mut c.members)
    .find(|m| !m.depth.slots.is_empty())
    .unwrap();
  member.depth.slots.reverse();
  member.depth.slots.pop();
  assert_ne!(
    aiur::trace::describe::compiled_fingerprint(&changed),
    original.fingerprint
  );
}
