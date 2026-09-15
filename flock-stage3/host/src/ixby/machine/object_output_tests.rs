use super::*;
use crate::ixby::{
  control::{Control, ControlState},
  decode::test_support::{Value as V, advice, byte_record, output},
  object_value::test_support::{
    CONTROL, declarations, flip, handle, id, layout, record,
  },
  value::{BYTES_TAG, ValueWords},
};

const CAPACITY: usize = 192;

fn gate() -> OutputEncodeGate {
  OutputEncodeGate::new(3, CONTROL, CAPACITY)
    .unwrap()
    .with_objects(layout(), ByteCapacity::new(17).unwrap())
}

fn inputs(value: ValueWords) -> Vec<F128> {
  let mut inputs = ControlState {
    control: Control::Halted(value),
    remaining: 0,
    continuation: vec![],
  }
  .words(CONTROL)
  .unwrap();
  inputs.extend(declarations());
  inputs.extend(record(false, &[]));
  inputs.extend(record(true, &[V::Word(11).words(), V::Ext(17, 19).words()]));
  inputs.extend(record(true, &[handle(1), handle(1)]));
  inputs.resize(
    CONTROL.state_words()
      + layout().declaration_words()
      + layout().entries() * layout().record_words(),
    F128::ZERO,
  );
  inputs.extend(byte_record(17, Some(&[1, 2, 3])));
  inputs.resize(gate().input_count(), F128::ZERO);
  inputs
}

fn check(
  gate: &OutputEncodeGate,
  r1cs: &BlockR1cs,
  inputs: &[F128],
  good: bool,
) {
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(inputs, bits));
  let residual = 128 * (gate.input_count() + gate.output_count() - 1);
  assert_eq!(bits[residual], !good);
  assert!(r1cs.satisfies(&bits));
  bits[residual] ^= true;
  assert!(!r1cs.satisfies(&bits));
}

#[test]
fn constructor_output_serializes_shared_objects_as_inline_trees_and_exact_scalars()
 {
  let gate = gate();
  let r1cs = gate.r1cs();
  let pair = V::Ctor(id(true), vec![V::Word(11), V::Ext(17, 19)]);
  let mut cases = vec![
    (handle(0), V::Ctor(id(false), vec![])),
    (handle(1), pair.clone()),
    (handle(2), V::Ctor(id(true), vec![pair.clone(), pair])),
    ([F128::new(BYTES_TAG, 0), F128::ZERO], V::Bytes(vec![1, 2, 3])),
  ];
  for scalar in [
    V::Bool(0),
    V::Bool(1),
    V::Word(u32::MAX),
    V::Field(0xffff_ffff_0000_0000),
    V::Ext(17, 19),
    V::Erased,
  ] {
    cases.push((scalar.words(), scalar));
  }
  for (value, expected) in cases {
    let inputs = inputs(value);
    let mut actual = Vec::new();
    gate.eval(&inputs, &(), &mut actual);
    let mut expected = advice(CAPACITY, &output(&expected));
    expected.push(F128::ZERO);
    assert_eq!(actual, expected);
    check(&gate, &r1cs, &inputs, true);
  }
}

#[test]
fn constructor_output_rejects_cycles_bad_records_byte_padding_and_resource_overflow()
 {
  let gate = gate();
  let r1cs = gate.r1cs();
  let base = inputs(handle(2));
  let arena = CONTROL.state_words() + layout().declaration_words();
  let record1 = arena + layout().record_words();
  let record2 = arena + 2 * layout().record_words();
  for (word, bit) in [
    (record1, 64),                    // required presence
    (record1, 32),                    // arity differs from declaration
    (record1, 65),                    // noncanonical metadata
    (record1 + 2, 63),                // noncanonical Word32 payload
    (1 + CONTROL.frame_words(), 127), // full cell tag is constrained
    (2 + CONTROL.frame_words(), 127), // full handle is constrained
    (1, 0),                           // halted frame must be empty
    (0, 0),                           // not a halted state
  ] {
    let mut bad = base.clone();
    flip(&mut bad[word], bit);
    check(&gate, &r1cs, &bad, false);
  }
  let mut cycle = base.clone();
  cycle[record2 + 2] = F128::new(2, 0);
  check(&gate, &r1cs, &cycle, false);
  let mut dangling = base.clone();
  dangling[record2 + 2] = F128::new(layout().entries() as u64, 0);
  check(&gate, &r1cs, &dangling, false);
  let too_short = OutputEncodeGate::new(3, CONTROL, 190)
    .unwrap()
    .with_objects(layout(), ByteCapacity::new(17).unwrap());
  check(&too_short, &too_short.r1cs(), &base, false); // exact output length is 191
  let mut small = layout();
  small.capacity =
    crate::ixby::object_value::ObjectCapacity::new(2, 3, 6).unwrap();
  let fewer_nodes = OutputEncodeGate::new(3, CONTROL, CAPACITY)
    .unwrap()
    .with_objects(small, ByteCapacity::new(17).unwrap());
  check(&fewer_nodes, &fewer_nodes.r1cs(), &base, false); // sharing still costs seven nodes
  let byte_input = inputs([F128::new(BYTES_TAG, 0), F128::ZERO]);
  let byte_at = arena + layout().entries() * layout().record_words();
  for (word, bit) in
    [(byte_at, 32), (byte_at, 33), (byte_at + 1, 24), (byte_at + 2, 127)]
  {
    let mut bad = byte_input.clone();
    flip(&mut bad[word], bit);
    check(&gate, &r1cs, &bad, false);
  }
  let mut oversized = byte_input;
  oversized[byte_at].lo = 18 | (1u64 << 32);
  check(&gate, &r1cs, &oversized, false);
}

#[test]
fn constructor_output_words_and_recycled_padding_are_constrained() {
  let gate = gate();
  let r1cs = gate.r1cs();
  let row = OutputEncodeRow(inputs(handle(2)));
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&row.0, bits));
  assert!(r1cs.satisfies(&bits));
  for word in 0..gate.output_count() {
    for bit in [0, 7, 31, 32, 63, 64, 95, 127] {
      let at = 128 * (gate.input_count() + word) + bit;
      bits[at] ^= true;
      assert!(!r1cs.satisfies(&bits));
      bits[at] ^= true;
    }
  }
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
}
