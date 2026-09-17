use super::*;
use ixby_flock::ixby::ixbf_decode::{
  GrammarKind, stream::batch::GrammarBatchStatement,
};

#[test]
#[ignore = "requires retained CSLib frames in IXBY_CSLIB_FRAME_DIR"]
fn retained_pair_native_constraints_and_roots() {
  let setup = CompiledGrammarBatch::compile(GrammarKind::Program).unwrap();
  let started = std::time::Instant::now();
  let relation = GrammarPairRelation::compile(&setup).unwrap();
  eprintln!(
    "native pair census {:?}, compiled in {:?}",
    relation.census(),
    started.elapsed()
  );
  eprintln!("native pair Flock geometry {:?}", relation.geometry().unwrap());
  let directory =
    std::path::PathBuf::from(std::env::var_os("IXBY_CSLIB_FRAME_DIR").unwrap());
  let root = ::blake3::Hash::from_hex(
    "f2f6da19991985ba4575773a62943b213d94f3678c5b95f85fb9af1025fd26d1",
  )
  .unwrap();
  let length = 1_016_587;
  let mut initial = [F128::ZERO; 30];
  initial[0] = F128::new(0, length);
  let mut children = Vec::new();
  for i in 0..2 {
    let frame =
      std::fs::read(directory.join(format!("program-{i:06}.frame"))).unwrap();
    let size = u32::from_le_bytes(frame[..4].try_into().unwrap()) as usize;
    assert_eq!(frame.len(), 4 + 480 + size);
    let end = std::array::from_fn(|i| {
      ixby_flock::hash::pack_bytes(&frame[4 + 16 * i..4 + 16 * i + 16])
    });
    let statement =
      GrammarBatchStatement::new(length, *root.as_bytes(), initial, end)
        .unwrap();
    children.push(relation.replay().replay(&statement, &frame[484..]).unwrap());
    initial = end;
  }
  let started = std::time::Instant::now();
  let witness = relation.advice([&children[0], &children[1]]).unwrap();
  eprintln!(
    "native pair honest constraints and {} root claims checked in {:?}",
    relation.roots.len(),
    started.elapsed()
  );
  // Reusing the first child changes the full boundary, even though both child
  // proofs independently verify. The parent relation rejects that splice.
  assert!(relation.advice([&children[0], &children[0]]).is_err());
  let public = witness
    .graph
    .published
    .iter()
    .map(|&i| witness.values[i])
    .collect::<Vec<_>>();
  let mut changed = public.clone();
  changed[APPLICATION_WORDS] += F128::ONE;
  assert!(relation.check_roots(&changed).is_err());
}
