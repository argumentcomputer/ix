//! Independent physical fixtures, not witness/admission implementations.
use super::{ObjectCapacity, ObjectLayout};
use crate::{
  boolean::BooleanR1csPlan,
  ixby::{
    bits::{evaluate_words, fill_words},
    control::ControlCapacities,
    decode::{
      InputCapacities, ProgramCapacities,
      test_support::{CtorId, meta},
    },
    machine::MachineCapacities,
    value::{CTOR_TAG, ValueWords},
  },
};
use flock_prover::field::F128;

pub(crate) const CONTROL: ControlCapacities =
  ControlCapacities { locals: 4, continuations: 1, arguments: 2 };
pub(crate) const CAPACITY: MachineCapacities = MachineCapacities {
  program: ProgramCapacities {
    bytes: 256,
    functions: 1,
    blocks: 3,
    operands: 2,
  },
  control: CONTROL,
  input: InputCapacities { bytes: 192, values: 1 },
  output_bytes: 192,
  steps: 3,
};

pub(crate) fn layout() -> ObjectLayout {
  ObjectLayout::new(CAPACITY, ObjectCapacity::new(2, 3, 7).unwrap()).unwrap()
}

pub(crate) fn id(pair: bool) -> CtorId {
  CtorId {
    block: [if pair { 0x91 } else { 0x11 }; 32],
    member: u32::MAX,
    tag: 0x8000_0000,
  }
}

pub(crate) fn declarations() -> Vec<F128> {
  let mut words = vec![F128::new(2, 0)];
  for pair in [false, true] {
    let id = id(pair);
    for bytes in id.block.as_chunks::<16>().0 {
      words.push(F128::new(
        u64::from_le_bytes(bytes[..8].try_into().unwrap()),
        u64::from_le_bytes(bytes[8..].try_into().unwrap()),
      ));
    }
    words.push(meta(id.member, id.tag, 0, 0));
    words.push(meta(if pair { 2 } else { 0 }, 1, 0, 0));
  }
  words
}

pub(crate) fn handle(index: u32) -> ValueWords {
  [F128::new(CTOR_TAG, 0), F128::new(index.into(), 0)]
}

pub(crate) fn record(pair: bool, fields: &[ValueWords]) -> Vec<F128> {
  assert_eq!(fields.len(), if pair { 2 } else { 0 });
  let mut words = vec![meta(u32::from(pair), fields.len() as u32, 1, 0)];
  for field in fields {
    words.extend(field);
  }
  words.resize(layout().record_words(), F128::ZERO);
  words
}

pub(crate) fn flip(word: &mut F128, bit: usize) {
  if bit < 64 {
    word.lo ^= 1 << bit;
  } else {
    word.hi ^= 1 << (bit - 64);
  }
}

pub(crate) fn result(
  plan: &BooleanR1csPlan,
  inputs: &[F128],
  outputs: usize,
) -> Vec<F128> {
  evaluate_words(plan, inputs, outputs)
}

/// Check the real Boolean relation, including the connected-zero residual.
pub(crate) fn check(
  plan: &BooleanR1csPlan,
  inputs: &[F128],
  outputs: usize,
  good: bool,
) {
  let r1cs = plan.block_r1cs(3);
  let mut bits = vec![false; r1cs.n()];
  plan.fill_row(&mut bits[..plan.k()], |bits| fill_words(inputs, bits));
  let residual = 128 * (inputs.len() + outputs - 1);
  assert_eq!(bits[residual], !good);
  assert!(r1cs.satisfies(&bits));
  bits[residual] ^= true;
  assert!(!r1cs.satisfies(&bits));
}
