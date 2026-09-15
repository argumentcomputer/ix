use super::*;
use crate::{
  boolean::BooleanR1csPlan,
  hash::{Blake3Gate, IV, pack_bytes, pack8},
  ixby::bits::{fill_words, read_words},
  sizing::{CircuitEmitter, CountedGate, CountingEmitter},
};
use blake3::hazmat::{
  HasherExt, Mode, merge_subtrees_non_root, merge_subtrees_root,
};
use flock_prover::{
  circuit::builder::{GateType, ShapeBuilder},
  field::F128,
};

pub(super) fn pattern(length: usize) -> Vec<u8> {
  (0..length).map(|i| (i * 17 + i / 7 + i / 1024 * 53 + 11) as u8).collect()
}
pub(super) fn words(bytes: &[u8]) -> Vec<F128> {
  assert_eq!(bytes.len() % 16, 0);
  bytes.as_chunks::<16>().0.iter().map(|w| pack_bytes(w)).collect()
}
pub(super) fn digest(bytes: &[u8]) -> [F128; 2] {
  words(blake3::hash(bytes).as_bytes()).try_into().unwrap()
}

#[derive(Clone)]
pub(super) struct ChunkAdvice {
  pub bytes: [F128; SOURCE_CHUNK_WORDS],
  pub siblings: Vec<[F128; 2]>,
}
impl ChunkAdvice {
  pub(super) fn inputs(&self) -> Vec<F128> {
    let mut out = self.bytes.to_vec();
    out.extend(self.siblings.iter().flatten().copied());
    out
  }
}

/// Independent untrusted proof preparation using the pinned native crate's
/// non-root subtree API. Neither this tree nor its source is used by a verifier.
pub(super) struct NativeTree {
  pub bytes: Vec<u8>,
  levels: Vec<Vec<[u8; 32]>>,
}
impl NativeTree {
  pub(super) fn new(bytes: Vec<u8>) -> Self {
    let mut leaves: Vec<_> = bytes
      .chunks(1024)
      .enumerate()
      .map(|(i, chunk)| {
        blake3::Hasher::new()
          .set_input_offset((i * 1024) as u64)
          .update(chunk)
          .finalize_non_root()
      })
      .collect();
    // Empty files have no non-root chaining value. All sibling paths are
    // empty, and their actual root is the constrained empty-chunk compression.
    if leaves.is_empty() {
      leaves.push([0; 32]);
    }
    let mut levels = vec![leaves];
    while levels.last().unwrap().len() > 1 {
      let previous = levels.last().unwrap();
      if previous.len() == 2 {
        assert_eq!(
          merge_subtrees_root(&previous[0], &previous[1], Mode::Hash),
          blake3::hash(&bytes)
        );
      }
      levels.push(
        previous
          .chunks(2)
          .map(|pair| {
            if pair.len() == 1 {
              pair[0]
            } else {
              merge_subtrees_non_root(&pair[0], &pair[1], Mode::Hash)
            }
          })
          .collect(),
      );
    }
    Self { bytes, levels }
  }
  pub(super) fn proof(&self, index: usize, depth: usize) -> ChunkAdvice {
    assert!(index < self.levels[0].len());
    let start = index * 1024;
    let end = (start + 1024).min(self.bytes.len());
    let mut bytes = [0; 1024];
    bytes[..end - start].copy_from_slice(&self.bytes[start..end]);
    let siblings = (0..depth)
      .map(|level| {
        self
          .levels
          .get(level)
          .and_then(|nodes| nodes.get((index >> level) ^ 1))
          .map(|cv| words(cv).try_into().unwrap())
          .unwrap_or([F128::ZERO; 2])
      })
      .collect();
    ChunkAdvice { bytes: words(&bytes).try_into().unwrap(), siblings }
  }
  pub(super) fn read_advice(
    &self,
    depth: usize,
    offset: u64,
  ) -> [ChunkAdvice; 3] {
    let last = last_index(self.bytes.len() as u64) as usize;
    let first = ((offset >> 10) as usize).min(last);
    [first, (first + 1).min(last), last].map(|index| self.proof(index, depth))
  }
}

fn check<G: GateType<Hint = ()> + CountedGate>(
  gate: &G,
  plan: &BooleanR1csPlan,
  input: &[F128],
) -> Vec<F128> {
  check_r1cs(gate, plan, &plan.block_r1cs(3), input)
}

fn check_r1cs<G: GateType<Hint = ()> + CountedGate>(
  gate: &G,
  plan: &BooleanR1csPlan,
  r1cs: &flock_prover::r1cs::BlockR1cs,
  input: &[F128],
) -> Vec<F128> {
  let mut row = vec![false; plan.k()];
  plan.fill_row(&mut row, |bits| fill_words(input, bits));
  let mut native = Vec::new();
  gate.eval(input, &(), &mut native);
  assert_eq!(
    read_words(&row, gate.input_count(), gate.output_count()),
    native,
    "native/constraint output mismatch for {input:?}"
  );
  assert!(super::super::tests::satisfies(r1cs, &row));
  native
}

pub(super) fn chunk_root(
  depth: usize,
  length: u64,
  index: u64,
  proof: &ChunkAdvice,
) -> ([F128; 2], bool) {
  let block = SourceBlockGate::new(3, depth).unwrap();
  let path = SourcePathGate::new(3, depth).unwrap();
  let compression = Blake3Gate { nu: 3 };
  let mut cv = pack8(&IV);
  let mut valid = true;
  for position in 0..16 {
    let mut input = vec![
      F128::new(length, 0),
      F128::new(index, 0),
      F128::new(position as u64, 0),
    ];
    input.extend_from_slice(&proof.bytes[position * 4..position * 4 + 4]);
    let mut control = Vec::new();
    block.eval(&input, &(), &mut control);
    valid &= control[2] == F128::ZERO;
    let mut input = cv.to_vec();
    input.extend_from_slice(&proof.bytes[position * 4..position * 4 + 4]);
    input.push(control[0]);
    let mut output = Vec::new();
    compression.eval(&input, &(), &mut output);
    if control[1] == F128::new(1, 0) {
      cv.copy_from_slice(&output[..2]);
    }
  }
  for level in 0..depth {
    let input = [
      F128::new(length, 0),
      F128::new(index, 0),
      F128::new(level as u64, 0),
      cv[0],
      cv[1],
      proof.siblings[level][0],
      proof.siblings[level][1],
    ];
    let mut control = Vec::new();
    path.eval(&input, &(), &mut control);
    valid &= control[6] == F128::ZERO;
    let mut input = pack8(&IV).to_vec();
    input.extend_from_slice(&control[..5]);
    let mut output = Vec::new();
    compression.eval(&input, &(), &mut output);
    if control[5] == F128::new(1, 0) {
      cv.copy_from_slice(&output[..2]);
    }
  }
  (cv, valid)
}

#[test]
fn chunk_and_path_parameters_match_constraints_at_boundaries_and_full_u64_width()
 {
  for depth in [0, 4, 14, 54] {
    let gate = SourceBlockGate::new(3, depth).unwrap();
    let r1cs = gate.r1cs();
    for length in
      [0u64, 1, 63, 64, 65, 1023, 1024, 1025, 8192, (1 << 34) + 1, u64::MAX]
    {
      let last = last_index(length);
      for index in [0, last, last + 1] {
        for position in 0..16 {
          let mut input = [F128::ZERO; 7];
          input[0] = F128::new(length, 0);
          input[1] = F128::new(index, 0);
          input[2] = F128::new(position, 0);
          check_r1cs(&gate, gate.plan(), &r1cs, &input);
        }
      }
    }
    let path = SourcePathGate::new(3, depth).unwrap();
    let r1cs = path.r1cs();
    eprintln!(
      "source controls depth {depth}: block k_log={}, useful_bits={}; path k_log={}, useful_bits={}",
      gate.plan().k_log(),
      gate.plan().useful_bits(),
      path.plan().k_log(),
      path.plan().useful_bits()
    );
    for length in [0u64, 1024, 1025, 2048, 4097, 8192, (1 << 34) + 1, u64::MAX]
    {
      for index in [0, last_index(length), last_index(length) + 1] {
        for level in [0, 1, 3, 13, 53, 54, 63, 64, u64::MAX] {
          check_r1cs(
            &path,
            path.plan(),
            &r1cs,
            &[
              F128::new(length, 0),
              F128::new(index, 0),
              F128::new(level, 0),
              F128::new(17, 29),
              F128::new(31, 37),
              F128::ZERO,
              F128::ZERO,
            ],
          );
        }
      }
    }
  }
  let gate = SourceBlockGate::new(3, 14).unwrap();
  let r1cs = gate.r1cs();
  for block in [0usize, 1, 15] {
    for len in 0..=64 {
      let mut message = pattern(64);
      message[len..].fill(0);
      let mut input = vec![
        F128::new((64 * block + len) as u64, 0),
        F128::ZERO,
        F128::new(block as u64, 0),
      ];
      input.extend(words(&message));
      assert_eq!(
        check_r1cs(&gate, gate.plan(), &r1cs, &input).last(),
        Some(&F128::ZERO)
      );
    }
  }
  for byte in 0..64 {
    let mut message = [0; 64];
    message[byte] = 1;
    let mut input = vec![F128::new(byte as u64, 0), F128::ZERO, F128::ZERO];
    input.extend(words(&message));
    assert_eq!(
      check_r1cs(&gate, gate.plan(), &r1cs, &input).last(),
      Some(&F128::new(1, 0))
    );
  }
}

#[test]
fn native_chunk_paths_reproduce_standard_hashes_for_every_leaf_of_uneven_trees()
{
  let mut lengths: Vec<_> = (0..=129).collect();
  lengths.extend((1..=33).flat_map(|n| [n * 1024 - 1, n * 1024, n * 1024 + 1]));
  for length in lengths {
    let tree = NativeTree::new(pattern(length));
    let expected = digest(&tree.bytes);
    for index in 0..=last_index(length as u64) {
      let proof = tree.proof(index as usize, 6);
      assert_eq!(
        chunk_root(6, length as u64, index, &proof),
        (expected, true),
        "length={length}, index={index}"
      );
    }
  }
  // An early chunk path CANNOT authenticate the length: 8 full chunks and
  // 5 full chunks have the same root height, and an opaque right sibling
  // can hide the actual suffix. The final-chunk check is indispensable.
  let tree = NativeTree::new(pattern(8192));
  let root = digest(&tree.bytes);
  assert_eq!(chunk_root(4, 5120, 0, &tree.proof(0, 4)), (root, true));
  let (wrong, valid) = chunk_root(4, 5120, 4, &tree.proof(4, 4));
  assert!(!valid || wrong != root);
  let mut forged_final = tree.proof(4, 4);
  forged_final.siblings[0] = [F128::ZERO; 2];
  forged_final.siblings[1] = [F128::ZERO; 2];
  let (wrong, valid) = chunk_root(4, 5120, 4, &forged_final);
  assert!(valid);
  assert_ne!(wrong, root);
}

#[test]
fn windows_select_original_bytes_across_every_chunk_offset_and_zero_exact_padding()
 {
  let tree = NativeTree::new(pattern(3077));
  for count in [0usize, 1, 17, 32, 96, 272, 592, 1024] {
    let capacity = SourceCapacity::new(14, count).unwrap();
    let gate = SourceWindowGate::new(3, capacity).unwrap();
    let r1cs = gate.r1cs();
    let offsets: Vec<_> = if count == 32 {
      (0..1024).collect()
    } else {
      vec![0, 1, 15, 16, 511, 512, 1007, 1023, 1024, 2047, 3072, 3077]
    };
    for offset in offsets {
      let advice = tree.read_advice(14, offset);
      for take in [0, count / 2, count] {
        let mut input = vec![
          F128::new(offset, tree.bytes.len() as u64),
          F128::new(take as u64, 0),
        ];
        input.extend(advice[0].bytes);
        input.extend(advice[1].bytes);
        let output = check_r1cs(&gate, gate.plan(), &r1cs, &input);
        assert_eq!(*output.last().unwrap(), F128::ZERO);
        let mut expected = vec![0; capacity.window_words() * 16];
        let copied = take.min(tree.bytes.len() - offset as usize);
        expected[..copied].copy_from_slice(
          &tree.bytes[offset as usize..offset as usize + copied],
        );
        assert_eq!(&output[4..output.len() - 1], words(&expected));
      }
    }
    if count == 32 {
      for available in 0..=32 {
        let offset = tree.bytes.len() as u64 - available;
        let advice = tree.read_advice(14, offset);
        for take in 0..=32 {
          let mut input = vec![
            F128::new(offset, tree.bytes.len() as u64),
            F128::new(take, 0),
          ];
          input.extend(advice[0].bytes);
          input.extend(advice[1].bytes);
          let output = check_r1cs(&gate, gate.plan(), &r1cs, &input);
          let copied = available.min(take) as usize;
          let mut expected = [0; 32];
          expected[..copied].copy_from_slice(
            &tree.bytes[offset as usize..offset as usize + copied],
          );
          assert_eq!(&output[4..6], words(&expected));
          assert_eq!(output[6], F128::ZERO);
        }
      }
    }
    eprintln!(
      "source window {count}: k_log={}, useful_bits={}",
      gate.plan().k_log(),
      gate.plan().useful_bits()
    );
  }
}

#[test]
fn malformed_source_controls_padding_and_all_output_bits_are_bound() {
  let block = SourceBlockGate::new(3, 14).unwrap();
  let path = SourcePathGate::new(3, 14).unwrap();
  let window =
    SourceWindowGate::new(3, SourceCapacity::new(14, 32).unwrap()).unwrap();
  let block_input = [
    F128::new(1, 0),
    F128::ZERO,
    F128::ZERO,
    F128::new(17, 0),
    F128::ZERO,
    F128::ZERO,
    F128::ZERO,
  ];
  let path_input = [
    F128::new(2048, 0),
    F128::ZERO,
    F128::ZERO,
    F128::new(17, 29),
    F128::new(31, 37),
    F128::new(41, 43),
    F128::new(47, 53),
  ];
  let mut window_input = vec![F128::new(1023, 2048), F128::new(32, 0)];
  window_input.extend(words(&pattern(2048)));
  for (plan, input, inputs, outputs) in [
    (block.plan(), block_input.to_vec(), 7, 3),
    (path.plan(), path_input.to_vec(), 7, 7),
    (window.plan(), window_input.clone(), 130, 7),
  ] {
    let mut row = vec![false; plan.k()];
    plan.fill_row(&mut row, |bits| fill_words(&input, bits));
    let r1cs = plan.block_r1cs(3);
    super::super::tests::output_bits_are_bound(
      &r1cs,
      &mut row,
      128 * inputs,
      128 * outputs,
    );
    row[plan.k() - 1] = true;
    assert!(!super::super::tests::satisfies(&r1cs, &row));
  }
  for (word, value) in [
    (0, F128::new(1, 1)),
    (1, F128::new(1, 0)),
    (2, F128::new(16, 0)),
    (3, F128::new(17 | (1 << 8), 0)),
    (6, F128::new(0, 1 << 63)),
  ] {
    let mut bad = block_input;
    bad[word] = value;
    assert_eq!(
      *check(&block, block.plan(), &bad).last().unwrap(),
      F128::new(1, 0)
    );
  }
  for (word, value) in [
    (0, F128::new(2048, 1)),
    (1, F128::new(2, 0)),
    (2, F128::new(14, 0)),
    (2, F128::new(0, 1)),
  ] {
    let mut bad = path_input;
    bad[word] = value;
    assert_eq!(
      *check(&path, path.plan(), &bad).last().unwrap(),
      F128::new(1, 0)
    );
  }
  for (word, value) in [
    (0, F128::new(2049, 2048)),
    (0, F128::new(0, (1 << 24) + 1)),
    (1, F128::new(33, 0)),
    (1, F128::new(32, 1)),
  ] {
    let mut bad = window_input.clone();
    bad[word] = value;
    assert_eq!(
      *check(&window, window.plan(), &bad).last().unwrap(),
      F128::new(1, 0)
    );
  }
  let wide =
    SourceWindowGate::new(3, SourceCapacity::new(54, 32).unwrap()).unwrap();
  let r1cs = wide.r1cs();
  for length in [0, 1 << 32, 1 << 63, u64::MAX] {
    for offset in [0, length.saturating_sub(17), length] {
      let mut input = window_input.clone();
      input[0] = F128::new(offset, length);
      assert_eq!(
        check_r1cs(&wide, wide.plan(), &r1cs, &input).last(),
        Some(&F128::ZERO)
      );
    }
  }
}

#[test]
fn source_witness_drivers_clear_recycled_padding() {
  let block = SourceBlockGate::new(3, 14).unwrap();
  let path = SourcePathGate::new(3, 14).unwrap();
  let window =
    SourceWindowGate::new(3, SourceCapacity::new(14, 32).unwrap()).unwrap();
  let br = SourceBlockRow([F128::ZERO; 7]);
  let pr = SourcePathRow([F128::ZERO; 7]);
  let wr = SourceWindowRow(vec![F128::ZERO; 130]);
  for count in [0, 1, 5] {
    let rows = vec![br.clone(); count];
    crate::ixby::test_support::padding(
      block.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| block.generate_witness_into(&rows, dst),
    );
    let rows = vec![pr.clone(); count];
    crate::ixby::test_support::padding(
      path.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| path.generate_witness_into(&rows, dst),
    );
    let rows = vec![wr.clone(); count];
    crate::ixby::test_support::padding(
      window.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| window.generate_witness_into(&rows, dst),
    );
  }
}

pub(super) fn proof_wires(
  b: &mut impl CircuitEmitter,
  depth: usize,
) -> SourceChunkProofWires {
  SourceChunkProofWires {
    bytes: std::array::from_fn(|_| b.input()),
    siblings: (0..depth).map(|_| [b.input(), b.input()]).collect(),
  }
}

#[test]
fn source_counting_is_lazy_capacity_owned_and_matches_the_complete_reader() {
  fn emit(
    b: &mut impl CircuitEmitter,
    nu: usize,
    capacity: SourceCapacity,
  ) -> SourceReadSlots {
    let slots = SourceReadSlots::declare(b, nu, capacity).unwrap();
    let root = [b.input(), b.input()];
    let cursor = b.input();
    let take = b.input();
    let proofs: [_; 3] =
      std::array::from_fn(|_| proof_wires(b, capacity.depth()));
    let out = slots.read(b, cursor, take, root, &proofs);
    b.publish(out.file_length);
    for word in out.words {
      b.publish(word);
    }
    slots
  }
  for (depth, count, nu) in
    [(0, 0, 6), (14, 32, 7), (14, 272, 7), (54, 1024, 8)]
  {
    let capacity = SourceCapacity::new(depth, count).unwrap();
    let mut counter = CountingEmitter::new();
    let slots = emit(&mut counter, nu, capacity);
    assert!(slots.window_gate().1.plan.get().is_none());
    assert!(slots.block_gate().1.plan.get().is_none());
    assert!(slots.path_gate().1.plan.get().is_none());
    let mut b = ShapeBuilder::new(nu);
    emit(&mut b, nu, capacity);
    let shape = b.finish().unwrap();
    counter.ensure_matches(&shape).unwrap();
    assert_eq!(counter.registry(nu).1, shape.counts);
  }
  assert!(SourceCapacity::new(55, 0).is_err());
  assert!(SourceCapacity::new(14, 1025).is_err());
  assert!(SourceCapacity::new(54, 1024).unwrap().admits_length(u64::MAX));
  assert!(SourceCapacity::new(14, 32).unwrap().admits_length(1 << 24));
  assert!(!SourceCapacity::new(14, 32).unwrap().admits_length((1 << 24) + 1));
  assert!(
    SourceWindowGate::new(2, SourceCapacity::new(0, 0).unwrap()).is_err()
  );
  assert!(SourceBlockGate::new(21, 0).is_err());
  assert!(SourcePathGate::new(2, 0).is_err());
}
