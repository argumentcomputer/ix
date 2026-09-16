use super::*;
mod countdown;
mod fixture;
fn profile() -> FunctionalProfile {
  FunctionalProfile::new([1, 0, 1, 1, 1, 0, 8, 4096, 64, 64], 24).unwrap()
}
#[test]
fn invalid_execution_counts_are_rejected_before_setup_or_advice() {
  for (index, count) in [(0, 0), (6, MAX_PAGED_CHAIN_LEAVES + 1), (3, 2)] {
    let mut counts = [1; 11];
    counts[index] = count;
    assert!(
      PagedTreeCompiler::new(profile(), BatchClass::Small, counts).is_err()
    );
  }
  let mut compiler =
    PagedTreeCompiler::new(profile(), BatchClass::Small, [1; 11]).unwrap();
  assert!(compiler.children.is_empty());
  assert!(compiler.compile_component(Component::Execution, 2).is_err());
  assert!(compiler.compile_components(3, 3).is_err());
  assert!(compiler.compile_components(0, 12).is_err());
  assert!(compiler.children.is_empty());
}
#[test]
#[ignore = "proof-free complete original-format execution setup census"]
fn complete_execution_setup_geometry() {
  let mut compiler =
    PagedTreeCompiler::new(profile(), BatchClass::Small, [1; 11]).unwrap();
  let started = std::time::Instant::now();
  let node = compiler.compile_complete().unwrap();
  eprintln!(
    "complete execution setup {:?}: {:?}; identity {}",
    started.elapsed(),
    node.geometry(),
    blake3::Hash::from(node.identity())
  );
  assert_eq!(node.geometry().application_words, 2);
  assert_eq!(node.geometry().leaves, 12);
}
