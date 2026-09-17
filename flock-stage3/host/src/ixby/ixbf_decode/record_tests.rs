use super::*;
use crate::{
  ixby::bits::{fill_words, read_words},
  sizing::CountedGate,
};
use flock_prover::{field::F128, r1cs::BlockR1cs};
use num_bigint::BigUint;

pub(super) fn word(value: u128) -> F128 {
  F128::new(value as u64, (value >> 64) as u64)
}

pub(super) fn integers(values: &[u128]) -> Vec<u8> {
  values
    .iter()
    .flat_map(|value| tests::natural_bytes(&BigUint::from(*value)))
    .collect()
}

pub(super) fn input(
  source: &[u8],
  offset: usize,
  bounds: [F128; 3],
) -> [F128; RECORD_INPUTS] {
  assert!(offset <= source.len());
  let mut lookahead = [0; RECORD_LOOKAHEAD_BYTES];
  let take = (source.len() - offset).min(RECORD_LOOKAHEAD_BYTES);
  lookahead[..take].copy_from_slice(&source[offset..offset + take]);
  let mut input = [F128::ZERO; RECORD_INPUTS];
  input[0] = F128::new(offset as u64, source.len() as u64);
  input[1] = F128::new(1, 0);
  input[2..5].copy_from_slice(&bounds);
  for (target, bytes) in
    input[5..].iter_mut().zip(lookahead.as_chunks::<16>().0)
  {
    *target = crate::hash::pack_bytes(bytes);
  }
  input
}

pub(super) fn bits(
  gate: &RecordDecodeGate,
  input: &[F128; RECORD_INPUTS],
) -> Vec<bool> {
  let mut row = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut row, |bits| fill_words(input, bits));
  assert_eq!(
    read_words(&row, gate.input_count(), gate.output_count()),
    record::evaluate(gate.kind(), input),
    "{:?} integer differential",
    gate.kind(),
  );
  row
}

fn reject(
  gate: &RecordDecodeGate,
  r1cs: &BlockR1cs,
  input: &[F128; RECORD_INPUTS],
) {
  let mut row = bits(gate, input);
  assert!(tests::satisfies(r1cs, &row));
  let residual = (RECORD_INPUTS + RECORD_FIELDS + 1) * 128;
  assert!(
    row[residual],
    "{:?} accepted invalid record: {input:?}",
    gate.kind()
  );
  row[residual] = false;
  assert!(!tests::satisfies(r1cs, &row));
}

pub(super) struct Fixture {
  pub bytes: Vec<u8>,
  pub consumed: usize,
  pub bounds: [F128; 3],
  pub fields: [F128; RECORD_FIELDS],
}

pub(super) fn fixture(kind: RecordKind) -> Fixture {
  let mut bounds = [0; 3];
  let mut fields = [0; RECORD_FIELDS];
  let mut bytes = match kind {
    RecordKind::Metadata => {
      fields[0] = (1 << 100) + 19;
      integers(&[fields[0]])
    },
    RecordKind::Count => {
      bounds[0] = 3;
      fields[0] = 2;
      vec![2]
    },
    RecordKind::Index => {
      bounds[0] = 4;
      fields[0] = 3;
      vec![3]
    },
    RecordKind::Constructor => {
      bounds[0] = 5;
      fields[..5].copy_from_slice(&[
        u128::MAX,
        1 << 127,
        (1 << 65) + 2,
        u128::MAX,
        3,
      ]);
      let mut bytes = fields[0].to_le_bytes().to_vec();
      bytes.extend(fields[1].to_le_bytes());
      bytes.extend(integers(&fields[2..5]));
      bytes
    },
    RecordKind::Function => {
      bounds = [4, 5, 8];
      fields[..3].copy_from_slice(&[3, 1, 2]);
      integers(&fields[..3])
    },
    RecordKind::Block => {
      bounds[0] = 128;
      fields[..2].copy_from_slice(&[127, 7]);
      vec![127, 7]
    },
    RecordKind::Alternative => {
      bounds = [4, 5, 0];
      fields[..2].copy_from_slice(&[3, 4]);
      vec![3, 4]
    },
    RecordKind::Input => {
      bounds = [4, 2, 8];
      fields[0] = 2;
      b"IXFI\x01\0\0\0\x02\0\0\0\x02".to_vec()
    },
    RecordKind::Output => {
      bounds[0] = 8;
      fields[0] = 1;
      b"IXFO\x01\0\0\0\x02\0\0\0".to_vec()
    },
    RecordKind::Value => {
      bounds = [8, 10, 7];
      fields[..2].copy_from_slice(&[2, 9]);
      fields[5] = 2;
      vec![2, 9, 2]
    },
    RecordKind::Operand => {
      bounds[0] = 128;
      fields[1] = 127;
      vec![0, 127]
    },
    RecordKind::Scalar => {
      fields[0] = 5;
      fields[1] = u128::from(0xffff_ffff_0000_0000u64) | (19 << 64);
      let mut bytes = vec![5];
      bytes.extend(fields[1].to_le_bytes());
      bytes
    },
    RecordKind::Operation => {
      bounds = [8, 4, 10];
      fields[..5].copy_from_slice(&[1, 42, 0, 3, 3]);
      vec![1, 42, 3]
    },
  };
  let consumed = bytes.len();
  // Deliberately nonzero following data, not padding. It is not a claim that
  // the omitted surrounding body/forest is admitted by this record relation.
  bytes.extend([0x81, 0xff, 0x03, 0x19]);
  Fixture {
    bytes,
    consumed,
    bounds: bounds.map(word),
    fields: fields.map(word),
  }
}

#[test]
fn all_record_kinds_preserve_original_fields_cursors_and_following_bytes() {
  for kind in RecordKind::ALL {
    let gate = RecordDecodeGate::new(3, kind).unwrap();
    let r1cs = gate.r1cs();
    let fixture = fixture(kind);
    for offset in [0, 15, 16, 17, 31, 32, 63] {
      if offset != 0 && matches!(kind, RecordKind::Input | RecordKind::Output) {
        continue;
      }
      let mut source = vec![0xa5; offset];
      source.extend(&fixture.bytes);
      let input = input(&source, offset, fixture.bounds);
      let row = bits(&gate, &input);
      assert!(tests::satisfies(&r1cs, &row));
      let output = record::evaluate(kind, &input);
      assert_eq!(output[..RECORD_FIELDS], fixture.fields, "{kind:?}");
      assert_eq!(
        output[RECORD_FIELDS],
        F128::new((offset + fixture.consumed) as u64, source.len() as u64)
      );
      assert_eq!(output[RECORD_FIELDS + 1], F128::ZERO, "{kind:?}");
    }
    eprintln!(
      "record {kind:?}: k_log={}, useful_bits={}",
      gate.plan().k_log(),
      gate.plan().useful_bits()
    );
  }
}

#[test]
fn record_outputs_disabled_rows_reserved_bits_and_source_padding_are_bound() {
  for kind in RecordKind::ALL {
    let gate = RecordDecodeGate::new(3, kind).unwrap();
    let r1cs = gate.r1cs();
    let fixture = fixture(kind);
    let good = input(&fixture.bytes, 0, fixture.bounds);
    let mut row = bits(&gate, &good);
    tests::output_bits_are_bound(
      &r1cs,
      &mut row,
      RECORD_INPUTS * 128,
      gate.output_count() * 128,
    );
    row[gate.plan().k() - 1] = true;
    assert!(!tests::satisfies(&r1cs, &row));
    for bit in 1..128 {
      let mut changed = good;
      if bit < 64 {
        changed[1].lo |= 1 << bit;
      } else {
        changed[1].hi |= 1 << (bit - 64);
      }
      reject(&gate, &r1cs, &changed);
    }
    for byte in [fixture.bytes.len(), RECORD_LOOKAHEAD_BYTES - 1] {
      let mut changed = good;
      let word = 5 + byte / 16;
      if byte % 16 < 8 {
        changed[word].lo ^= 1 << (8 * (byte % 16));
      } else {
        changed[word].hi ^= 1 << (8 * (byte % 16 - 8));
      }
      reject(&gate, &r1cs, &changed);
    }
    let mut disabled = [F128::ZERO; RECORD_INPUTS];
    disabled[0] = F128::new(17, 23);
    disabled[2..5].copy_from_slice(&fixture.bounds);
    let row = bits(&gate, &disabled);
    assert!(tests::satisfies(&r1cs, &row));
    let output = record::evaluate(kind, &disabled);
    assert_eq!(output[..RECORD_FIELDS], [F128::ZERO; RECORD_FIELDS]);
    assert_eq!(output[RECORD_FIELDS], disabled[0]);
    assert_eq!(output[RECORD_FIELDS + 1], F128::ZERO);
    disabled[5].lo = 1;
    reject(&gate, &r1cs, &disabled);
  }
}

#[test]
fn record_semantic_bounds_bad_tags_and_noncanonical_metadata_reject() {
  let mut cases: Vec<(RecordKind, Vec<u8>, [u128; 3])> = vec![
    (RecordKind::Metadata, vec![0x80, 0], [0; 3]),
    (RecordKind::Metadata, vec![0x80; 19], [0; 3]),
    (
      RecordKind::Metadata,
      tests::natural_bytes(&(BigUint::from(1u8) << 128usize)),
      [0; 3],
    ),
    (RecordKind::Metadata, vec![0], [1, 0, 0]),
    (RecordKind::Count, vec![3, 2, 2, 2], [2, 0, 0]),
    (RecordKind::Count, vec![3, 2, 2], [3, 0, 0]),
    (RecordKind::Index, vec![4], [4, 0, 0]),
    (RecordKind::Function, vec![4, 0, 1, 2], [3, 8, 8]),
    (RecordKind::Function, vec![4, 0, 1, 2], [8, 3, 8]),
    (RecordKind::Function, vec![0, 0, 2, 2, 2], [8, 8, 1]),
    (RecordKind::Function, vec![0, 0, 0], [8, 8, 8]),
    (RecordKind::Function, vec![0, 2, 2, 2, 2], [8, 8, 8]),
    (RecordKind::Function, vec![0, 0, 3, 2, 2], [8, 8, 8]),
    (RecordKind::Block, vec![4, 1], [3, 0, 0]),
    (RecordKind::Block, vec![0, 8], [3, 0, 0]),
    (RecordKind::Alternative, vec![4, 0], [4, 5, 0]),
    (RecordKind::Alternative, vec![0, 5], [4, 5, 0]),
    (RecordKind::Value, vec![4], [8, 10, 8]),
    (RecordKind::Value, vec![2, 10, 0], [8, 10, 8]),
    (RecordKind::Value, vec![2, 0, 3, 3, 3, 3], [2, 10, 8]),
    (RecordKind::Value, vec![2, 0, 3, 3, 3, 3], [8, 10, 2]),
    (RecordKind::Value, vec![2, 0, 3, 3, 3], [8, 10, 8]),
    (RecordKind::Operand, vec![3], [128, 0, 0]),
    (RecordKind::Operand, vec![0, 127], [127, 0, 0]),
    (RecordKind::Operand, vec![0, 0x80, 0], [128, 0, 0]),
    (RecordKind::Scalar, vec![7], [0; 3]),
    (RecordKind::Scalar, vec![2, 2], [0; 3]),
    (RecordKind::Operation, vec![8], [8, 4, 10]),
    (RecordKind::Operation, vec![1, 58, 2, 2, 2], [8, 4, 10]),
    (RecordKind::Operation, vec![1, 42, 2, 2, 2], [8, 4, 10]),
    (RecordKind::Operation, vec![1, 0, 3, 2, 2, 2], [8, 4, 10]),
    (RecordKind::Operation, vec![2, 4, 0], [8, 4, 10]),
    (RecordKind::Operation, vec![4, 10, 0], [8, 4, 10]),
    (RecordKind::Operation, vec![5, 10, 0], [8, 4, 10]),
    (RecordKind::Operation, vec![6, 3, 2, 2, 2], [2, 4, 10]),
    (RecordKind::Operation, vec![6, 3, 2, 2], [8, 4, 10]),
  ];
  for kind in [RecordKind::Input, RecordKind::Output] {
    let fixture = fixture(kind);
    for byte in 0..12 {
      let mut bytes = fixture.bytes.clone();
      bytes[byte] ^= 1;
      let bounds = fixture
        .bounds
        .map(|word| u128::from(word.lo) | (u128::from(word.hi) << 64));
      cases.push((kind, bytes, bounds));
    }
    let mut bounds = fixture.bounds.map(|word| u128::from(word.lo));
    bounds[0] = 0;
    cases.push((kind, fixture.bytes, bounds));
  }
  for bounds in [[4, 1, 8], [4, 2, 1]] {
    cases.push((RecordKind::Input, fixture(RecordKind::Input).bytes, bounds));
  }
  let constructor = fixture(RecordKind::Constructor);
  cases.push((RecordKind::Constructor, constructor.bytes, [2, 0, 0]));
  for tag in [4, 5] {
    let mut bytes = vec![tag];
    bytes.extend(0xffff_ffff_0000_0001u64.to_le_bytes());
    if tag == 5 {
      bytes.extend(0u64.to_le_bytes());
    }
    cases.push((RecordKind::Scalar, bytes, [0; 3]));
  }
  let mut extension = vec![5];
  extension.extend(0u64.to_le_bytes());
  extension.extend(0xffff_ffff_0000_0001u64.to_le_bytes());
  cases.push((RecordKind::Scalar, extension, [0; 3]));
  for kind in RecordKind::ALL {
    let gate = RecordDecodeGate::new(3, kind).unwrap();
    let r1cs = gate.r1cs();
    for (_, bytes, bounds) in cases.iter().filter(|(case, _, _)| *case == kind)
    {
      reject(&gate, &r1cs, &input(bytes, 0, bounds.map(word)));
    }
    let fixture = fixture(kind);
    for length in 0..fixture.consumed {
      reject(&gate, &r1cs, &input(&fixture.bytes[..length], 0, fixture.bounds));
    }
  }
}

#[test]
fn every_functional_primitive_and_scalar_prefix_has_its_exact_abi() {
  let gate = RecordDecodeGate::new(3, RecordKind::Operation).unwrap();
  let r1cs = gate.r1cs();
  for primitive in crate::ixby::ixbf::Primitive::ALL {
    let arity = primitive.arity();
    let mut bytes = vec![1, primitive.opcode(), arity as u8];
    bytes.extend(vec![2; arity]);
    let input = input(&bytes, 0, [word(8), word(8), word(8)]);
    let output = record::evaluate(gate.kind(), &input);
    assert_eq!(output[1], word(u128::from(primitive.opcode())));
    assert_eq!(output[3], word(arity as u128));
    assert_eq!(output[4], word(arity as u128));
    assert_eq!(output[RECORD_FIELDS], F128::new(3, bytes.len() as u64));
    assert_eq!(output[RECORD_FIELDS + 1], F128::ZERO);
    assert!(tests::satisfies(&r1cs, &bits(&gate, &input)));
  }
  let gate = RecordDecodeGate::new(3, RecordKind::Scalar).unwrap();
  let r1cs = gate.r1cs();
  for (tag, payload) in [
    (0, 0),
    (1, 0),
    (2, 0),
    (2, 1),
    (3, u32::MAX as u128),
    (4, 0xffff_ffff_0000_0000),
    (5, 17 | (19 << 64)),
    (6, 0),
  ] {
    let size = match tag {
      2 => 1,
      3 => 4,
      4 => 8,
      5 => 16,
      _ => 0,
    };
    let mut bytes = vec![tag];
    bytes.extend(&payload.to_le_bytes()[..size]);
    bytes.extend([0x81, 0xff]);
    let input = input(&bytes, 0, [F128::ZERO; 3]);
    let output = record::evaluate(gate.kind(), &input);
    assert_eq!(output[0], word(u128::from(tag)));
    assert_eq!(output[1], word(payload));
    assert_eq!(
      output[RECORD_FIELDS],
      F128::new(1 + size as u64, bytes.len() as u64)
    );
    assert_eq!(output[RECORD_FIELDS + 1], F128::ZERO);
    assert!(tests::satisfies(&r1cs, &bits(&gate, &input)));
  }
}

#[test]
fn record_count_emission_is_lazy_and_recycled_buffers_are_fully_overwritten() {
  use crate::sizing::{CircuitEmitter, CountingEmitter};
  use flock_prover::circuit::builder::ShapeBuilder;
  fn emit(b: &mut impl CircuitEmitter, gate: RecordDecodeGate) {
    let slot = RecordDecodeSlot::declare(b, gate);
    for _ in 0..3 {
      let cursor = b.input();
      let enabled = b.input();
      let bounds = std::array::from_fn(|_| b.input());
      let bytes = std::array::from_fn(|_| b.input());
      let output = slot.decode(b, cursor, enabled, bounds, bytes);
      for field in output.fields {
        b.publish(field);
      }
      b.publish(output.next);
    }
  }
  for kind in RecordKind::ALL {
    let gate = RecordDecodeGate::new(3, kind).unwrap();
    let mut count = CountingEmitter::new();
    emit(&mut count, gate.clone());
    assert!(gate.plan.get().is_none());
    let mut b = ShapeBuilder::new(3);
    emit(&mut b, gate.clone());
    let shape = b.finish().unwrap();
    count.ensure_matches(&shape).unwrap();
    assert_eq!(count.registry(3).1, shape.counts);
    let fixture = fixture(kind);
    let good = RecordDecodeRow(input(&fixture.bytes, 0, fixture.bounds));
    for rows in [vec![], vec![good.clone()], vec![good; 5]] {
      crate::ixby::test_support::padding(
        gate.plan(),
        &rows,
        |row, bits| fill_words(&row.0, bits),
        |dst| gate.generate_witness_into(&rows, dst),
      );
    }
  }
  assert!(RecordDecodeGate::new(2, RecordKind::Metadata).is_err());
  assert!(RecordDecodeGate::new(21, RecordKind::Metadata).is_err());
}

#[test]
fn metadata_widths_file_overflow_and_arbitrary_advice_never_truncate() {
  let gate = RecordDecodeGate::new(3, RecordKind::Metadata).unwrap();
  let r1cs = gate.r1cs();
  for bit in 0..128 {
    let value = 1u128 << bit;
    let bytes = integers(&[value]);
    let mut input = input(&bytes, 0, [F128::ZERO; 3]);
    input[0] = F128::new(u64::MAX - bytes.len() as u64, u64::MAX);
    assert!(tests::satisfies(&r1cs, &bits(&gate, &input)));
    let output = record::evaluate(gate.kind(), &input);
    assert_eq!(output[0], word(value));
    assert_eq!(output[RECORD_FIELDS], F128::new(u64::MAX, u64::MAX));
    assert_eq!(output[RECORD_FIELDS + 1], F128::ZERO);
    input[0].lo += 1;
    reject(&gate, &r1cs, &input);
  }
  for kind in [RecordKind::Input, RecordKind::Output] {
    let gate = RecordDecodeGate::new(3, kind).unwrap();
    let r1cs = gate.r1cs();
    let fixture = fixture(kind);
    let mut bytes = vec![0];
    bytes.extend(fixture.bytes);
    reject(&gate, &r1cs, &input(&bytes, 1, fixture.bounds));
  }
  // Deterministic raw-advice differential includes malformed tags, huge
  // offsets/lengths, nonminimal integers and altered enable/unused fields.
  let mut random = 0x126f_472a_7b51_3d0du64;
  for kind in RecordKind::ALL {
    let gate = RecordDecodeGate::new(3, kind).unwrap();
    let r1cs = gate.r1cs();
    let fixture = fixture(kind);
    let good = input(&fixture.bytes, 0, fixture.bounds);
    for _ in 0..64 {
      let mut input = good;
      for _ in 0..4 {
        random ^= random << 13;
        random ^= random >> 7;
        random ^= random << 17;
        let index = random as usize % RECORD_INPUTS;
        if random & 1 == 0 {
          input[index].lo ^= random;
        } else {
          input[index].hi ^= random;
        }
      }
      assert!(tests::satisfies(&r1cs, &bits(&gate, &input)), "{kind:?}");
    }
  }
}
