use super::{proof_tests, *};
use crate::{
  ixby::{
    bits::{fill_words, read_words},
    ixbf_decode::{GrammarKind, dispatch, source},
  },
  sizing::CountedGate,
};
use flock_prover::{circuit::builder::GateType, field::F128};

pub(super) fn natural(bytes: &mut Vec<u8>, mut value: u128) {
  loop {
    let byte = (value & 127) as u8;
    value >>= 7;
    bytes.push(byte | if value == 0 { 0 } else { 128 });
    if value == 0 {
      break;
    }
  }
}
pub(super) fn program(scalar: Option<&[u8]>, arity: u128) -> Vec<u8> {
  let mut bytes = b"IXBF\x01\0\0\0\x02\0\0\0".to_vec();
  for value in [
    8,
    8,
    8,
    8,
    8,
    8,
    32,
    4096,
    65536,
    16777216,
    1u128 << 100,
    0,
    0,
    1,
    arity,
    0,
    1,
    arity,
    1,
  ] {
    natural(&mut bytes, value);
  }
  if let Some(scalar) = scalar {
    bytes.push(1);
    bytes.extend_from_slice(scalar);
  } else {
    bytes.push(2);
  }
  bytes
}
pub(super) fn transport(kind: GrammarKind, scalars: &[Vec<u8>]) -> Vec<u8> {
  let mut bytes =
    if kind == GrammarKind::Input { b"IXFI" } else { b"IXFO" }.to_vec();
  bytes.extend_from_slice(b"\x01\0\0\0\x02\0\0\0");
  if kind == GrammarKind::Input {
    natural(&mut bytes, scalars.len() as u128);
  } else {
    assert_eq!(scalars.len(), 1);
  }
  for scalar in scalars {
    bytes.push(0);
    bytes.extend_from_slice(scalar);
  }
  bytes
}
pub(super) fn string(length: usize) -> Vec<u8> {
  let mut bytes = vec![1];
  natural(&mut bytes, length as u128);
  let start = bytes.len();
  bytes.resize(start + length, b'a');
  if length >= 35 {
    bytes[start + 31..start + 35].copy_from_slice("𐀀".as_bytes());
  }
  bytes
}
pub(super) fn bytes(length: usize) -> Vec<u8> {
  let mut bytes = vec![6];
  natural(&mut bytes, length as u128);
  bytes.extend((0..length).map(|i| (i * 17 + i / 1024 * 53) as u8));
  bytes
}
pub(super) fn wide_nat() -> Vec<u8> {
  let mut bytes = vec![0];
  bytes.extend([255; 585]);
  bytes.push(1);
  bytes
}

fn check(g: &StreamGate, input: &[F128]) -> Vec<F128> {
  let mut actual = Vec::new();
  g.eval(input, &(), &mut actual);
  let plan = g.plan();
  let mut bits = vec![false; plan.k()];
  plan.fill_row(&mut bits, |bits| fill_words(input, bits));
  assert_eq!(read_words(&bits, g.input_count(), g.output_count()), actual);
  assert!(super::super::tests::satisfies(&plan.block_r1cs(3), &bits));
  actual
}

#[test]
fn cache_read_and_padding_controls_match_constraints_at_full_word_boundaries() {
  for depth in [0, 3, 14, 54] {
    let capacity = source::SourceCapacity::new(depth, 592).unwrap();
    let cache = StreamGate::new(3, capacity, StreamOp::Cache).unwrap();
    let read = StreamGate::new(3, capacity, StreamOp::Read).unwrap();
    for length in [0u64, 1, 64, 1024, 1025, 8192, 8193, 16_777_216, u64::MAX] {
      let last = source::last_index(length);
      for first in [0, last, last + 1, u64::MAX] {
        check(&cache, &[F128::new(length, 0), F128::new(first, 0)]);
        for (offset, take) in [
          (0, 0),
          (0, 272),
          (1023, 592),
          (length, 0),
          (length, 96),
          (length.wrapping_add(1), 0),
        ] {
          check(
            &read,
            &[
              F128::new(offset, length),
              F128::new(take, 0),
              F128::new(length, 0),
              F128::new(first, 0),
            ],
          );
        }
      }
    }
    for op in StreamOp::ALL {
      let gate = StreamGate::new(3, capacity, op).unwrap();
      let mut good = vec![F128::ZERO; gate.input_count()];
      match op {
        StreamOp::Cache => good[0].lo = 8192,
        StreamOp::Read => {
          good[0] = F128::new(17, 8192);
          good[1].lo = 592;
          good[2].lo = 8192;
        },
        StreamOp::Prepare => {
          good[0].lo = 3;
          good[1] = F128::new(17, 8192);
          for (i, word) in good[2..].iter_mut().enumerate() {
            *word = F128::new(i as u64, !i as u64);
          }
        },
      }
      for at in 0..good.len() {
        for bit in [0, 7, 31, 63, 64, 127] {
          let mut changed = good.clone();
          if bit < 64 {
            changed[at].lo ^= 1 << bit;
          } else {
            changed[at].hi ^= 1 << (bit - 64);
          }
          check(&gate, &changed);
        }
      }
      for low in [0, 1, u64::MAX] {
        if op == StreamOp::Prepare {
          good[0].lo = low;
          check(&gate, &good);
        }
      }
    }
  }
}

#[test]
fn control_outputs_and_recycled_padding_are_fully_constrained() {
  let capacity = source::SourceCapacity::new(14, 592).unwrap();
  for op in StreamOp::ALL {
    let gate = StreamGate::new(3, capacity, op).unwrap();
    let mut input = vec![F128::ZERO; gate.input_count()];
    match op {
      StreamOp::Cache => input[0].lo = 4097,
      StreamOp::Read => {
        input[0] = F128::new(1023, 4097);
        input[1].lo = 592;
        input[2].lo = 4097;
      },
      StreamOp::Prepare => {
        input[0].lo = 2;
        input[1] = F128::new(15, 4097);
        input[2].lo = 16;
        input[30] = F128::new(35, 3);
      },
    }
    let out = check(&gate, &input);
    assert_eq!(out.last(), Some(&F128::ZERO));
    let plan = gate.plan();
    let table = plan.block_r1cs(3);
    let mut bits = vec![false; plan.k()];
    plan.fill_row(&mut bits, |bits| fill_words(&input, bits));
    for bit in
      gate.input_count() * 128..(gate.input_count() + gate.output_count()) * 128
    {
      bits[bit] ^= true;
      assert!(!super::super::tests::satisfies(&table, &bits));
      bits[bit] ^= true;
    }
    eprintln!(
      "stream {op:?}: inputs={} outputs={} useful={} k={}",
      gate.input_count(),
      gate.output_count(),
      plan.useful_bits(),
      plan.k()
    );
    for count in [0, 1, 3] {
      let rows = vec![StreamRow(input.clone()); count];
      crate::ixby::test_support::padding(
        plan,
        &rows,
        |row, bits| fill_words(&row.0, bits),
        |dst| gate.generate_witness_into(&rows, dst),
      );
    }
  }
}

#[test]
fn witness_batches_preserve_utf8_obligations_and_skip_only_opaque_byte_payloads()
 {
  let cfg = proof_tests::config(GrammarKind::Program);
  let mut image = program(Some(&string(2400)), 1);
  image[1023..1027].copy_from_slice("𐀀".as_bytes());
  let expected = dispatch::test_parse_program(&image, 1000).unwrap();
  for steps in [1, 2, 17, 32, 128] {
    let mut parser =
      witness::BatchWitness::new(cfg, 14, &image, [F128::ZERO; 15]).unwrap();
    let mut state = *parser.state();
    let mut batches = 0;
    let mut strings = 0;
    let mut partial = false;
    while let Some(batch) = parser.next_batch(steps).unwrap() {
      assert_eq!(batch.initial, state);
      assert!(batch.steps <= steps && batch.steps > 0);
      for (i, index) in [
        batch.first_chunk,
        (batch.first_chunk + 1).min(source::last_index(image.len() as u64)),
        source::last_index(image.len() as u64),
      ]
      .into_iter()
      .enumerate()
      {
        let proof = source::test_chunk_advice(&image, index as usize, 14);
        assert_eq!(&batch.private[35 + i * 92..35 + (i + 1) * 92], proof);
      }
      state = batch.final_state;
      partial |= state[29] != F128::ZERO;
      strings += batch.events[15];
      batches += 1;
    }
    assert!(batches >= 3 && partial);
    assert_eq!(strings, 1);
    assert_eq!(state[..28], expected);
  }
  let opaque = program(Some(&bytes(4_900_000)), 1);
  let mut parser =
    witness::BatchWitness::new(cfg, 14, &opaque, [F128::ZERO; 15]).unwrap();
  let batch = parser.next_batch(32).unwrap().unwrap();
  assert_eq!(batch.events[16], 1);
  assert!(parser.done());
  assert_eq!(batch.private.len(), 311, "advice size independent of file bytes");
  let mut bad = image.clone();
  bad[2200] = 255;
  let mut parser =
    witness::BatchWitness::new(cfg, 14, &bad, [F128::ZERO; 15]).unwrap();
  let mut accepted = false;
  while let Ok(Some(_)) = parser.next_batch(32) {
    accepted = parser.done();
  }
  assert!(!accepted);
}

#[test]
fn actual_batch_wiring_rejects_wrong_cache_length_count_bytes_and_padding() {
  let kind = GrammarKind::Program;
  let s = proof_tests::setup(kind);
  let image = program(Some(&bytes(8192)), 1);
  let mut parser = witness::BatchWitness::new(
    proof_tests::config(kind),
    14,
    &image,
    [F128::ZERO; 15],
  )
  .unwrap();
  let batch = parser.next_batch(32).unwrap().unwrap();
  proof_tests::witness(&s, &batch);
  let rejects = |private: Vec<F128>| {
    assert!(
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        s.shape.run(&s.emission.inputs.assign(&private).unwrap(), &[])
      }))
      .is_err()
    );
  };
  for at in [1, 2, 33, 35, 35 + 64, 35 + 92, 35 + 184] {
    let mut bad = batch.private.clone();
    bad[at].lo ^= 1;
    rejects(bad);
  }
  for value in [F128::new(33, 0), F128::new(1, 1), F128::new(u64::MAX, 0)] {
    let mut bad = batch.private.clone();
    bad[34] = value;
    rejects(bad);
  }
  let mut bad = batch.private.clone();
  bad[0].lo -= 3 * 1024;
  bad[3].hi = bad[0].lo;
  rejects(bad);
  let mut bad = batch.private.clone();
  bad[3].lo += 1;
  rejects(bad);
  let mut bad = batch.private.clone();
  bad[0].hi = 1;
  rejects(bad);
  // A genuine zero-step batch preserves every carried word; a whole-file
  // verifier must reject it as nonprogress instead of treating it as EOF.
  let mut paused = batch.private.clone();
  paused[34] = F128::ZERO;
  let w = s.shape.run(&s.emission.inputs.assign(&paused).unwrap(), &[]);
  let mut expected = batch.statement[..33].to_vec();
  expected.extend(batch.initial);
  assert_eq!(w.public, s.emission.public.instantiate(&expected).unwrap());
}
