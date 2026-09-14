//! Exact metadata relations between decoded records. Registry indices and
//! lookup contents must come from authenticated parsing/access, not host hints.
//! These checks do not prove lookup provenance or complete grammar coverage.

use super::synthesis::Builder;
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::bits::{add, fill_words, subtract},
  sizing::{CircuitEmitter, CountedGate},
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{GateType, SlotId, SlotWitness, Wire},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};
use std::sync::{Arc, OnceLock};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum RecordLinkKind {
  /// left = [reference index, argument count, 0, 0, 0],
  /// right = [record index, function arity, 0, 0, 0].
  ExactArity,
  /// Same fields, with strict undersaturation for a closure/PAP.
  PartialArity,
  /// left = [target index, source locals, added locals, 0, 0],
  /// right = [block index, target locals, local limit, 0, 0].
  /// Checks exact u128 addition, no overflow, and the target's local limit.
  SuccessorFrame,
  /// Both sides = [block digest limb0, limb1, member, tag, child/field count].
  /// Compares the complete 512-bit identity and the exact arity.
  ConstructorValue,
  /// Same declaration fields; the first four words must differ. Changing only
  /// field count never makes a duplicate constructor identity distinct.
  DistinctConstructors,
}

impl RecordLinkKind {
  pub const ALL: [Self; 5] = [
    Self::ExactArity,
    Self::PartialArity,
    Self::SuccessorFrame,
    Self::ConstructorValue,
    Self::DistinctConstructors,
  ];
}

/// Input = enable (0 or 1), five left words, five right words. Disabled rows
/// require all words zero. Active rows check the documented relation and zero
/// unused fields. The sole output is a validity residual, pinned by the slot.
#[derive(Clone, Debug)]
pub struct RecordLinkGate {
  pub(super) nu: usize,
  pub(super) kind: RecordLinkKind,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct RecordLinkRow(pub(super) [F128; 11]);

impl RecordLinkGate {
  pub fn new(nu: usize, kind: RecordLinkKind) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "functional record-link row domain");
    Ok(Self { nu, kind, plan: Arc::new(OnceLock::new()) })
  }
  pub fn kind(&self) -> RecordLinkKind {
    self.kind
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build_plan(self.kind))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[RecordLinkRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(
      self.plan(),
      rows,
      self.nu,
      dst,
      |row, bits| fill_words(&row.0, bits),
    )
  }
}

impl CountedGate for RecordLinkGate {
  fn input_count(&self) -> usize {
    11
  }
  fn output_count(&self) -> usize {
    1
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for RecordLinkGate {
  type Row = RecordLinkRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..11).map(IoWord::input).chain([IoWord::output(11)]).collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> Self::Row {
    let input = input.try_into().expect("fixed record-link input width");
    output.push(evaluate(self.kind, input));
    RecordLinkRow(*input)
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct RecordLinkSlot {
  slot: SlotId,
  zero: Wire,
}

impl RecordLinkSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: RecordLinkGate) -> Self {
    Self { slot: b.slot(gate), zero: b.fixed_public_input(F128::ZERO) }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn check(
    &self,
    b: &mut impl CircuitEmitter,
    enabled: Wire,
    left: [Wire; 5],
    right: [Wire; 5],
  ) {
    let mut input = vec![enabled];
    input.extend(left);
    input.extend(right);
    let output = b.gate(self.slot, &input);
    b.connect(output[0], self.zero);
  }
}

fn build_plan(kind: RecordLinkKind) -> BooleanR1csPlan {
  let columns = if matches!(
    kind,
    RecordLinkKind::ExactArity
      | RecordLinkKind::ConstructorValue
      | RecordLinkKind::DistinctConstructors
  ) {
    1 << 12
  } else {
    1 << 13
  };
  let mut b = Builder::new(11, 1, columns);
  b.violations.extend(1..128);
  let disabled = b.not(0);
  b.require_zero(disabled, &(128..1408).collect::<Vec<_>>());
  let left: [Vec<_>; 5] = std::array::from_fn(|index| {
    (128 + index * 128..256 + index * 128).collect()
  });
  let right: [Vec<_>; 5] = std::array::from_fn(|index| {
    (768 + index * 128..896 + index * 128).collect()
  });
  match kind {
    RecordLinkKind::ExactArity
    | RecordLinkKind::PartialArity
    | RecordLinkKind::SuccessorFrame => {
      let same = b.equal(&left[0], &right[0]);
      b.require(0, same);
      let used = if kind == RecordLinkKind::SuccessorFrame { 3 } else { 2 };
      for side in [&left, &right] {
        for field in &side[used..] {
          b.require_zero(b.one, field);
        }
      }
      if kind == RecordLinkKind::ExactArity {
        let same = b.equal(&left[1], &right[1]);
        b.require(0, same);
      } else if kind == RecordLinkKind::PartialArity {
        let (_, less) = subtract(&mut b.b, b.one, b.zero, &left[1], &right[1]);
        b.require(0, less);
      } else {
        let (next, carry) = add(&mut b.b, b.one, b.zero, &left[1], &left[2]);
        b.violations.push(b.b.and(0, carry));
        let same = b.equal(&next, &right[1]);
        b.require(0, same);
        let (_, borrow) =
          subtract(&mut b.b, b.one, b.zero, &right[2], &right[1]);
        b.violations.push(b.b.and(0, borrow));
      }
    },
    RecordLinkKind::ConstructorValue => {
      for (left, right) in left.iter().zip(&right) {
        let same = b.equal(left, right);
        b.require(0, same);
      }
    },
    RecordLinkKind::DistinctConstructors => {
      let same = b.equal(&left[..4].concat(), &right[..4].concat());
      let different = b.not(same);
      b.require(0, different);
    },
  }
  b.finish(11)
}

/// Independent full-width integer differential; never a verifier oracle.
pub(super) fn evaluate(kind: RecordLinkKind, input: &[F128; 11]) -> F128 {
  let enabled = input[0].lo & 1 != 0;
  let mut bad = input[0].lo > 1 || input[0].hi != 0;
  let words: Vec<_> = input[1..]
    .iter()
    .map(|word| u128::from(word.lo) | (u128::from(word.hi) << 64))
    .collect();
  let (left, right) = words.split_at(5);
  if !enabled {
    bad |= words.iter().any(|word| *word != 0);
  }
  let unused = match kind {
    RecordLinkKind::ExactArity | RecordLinkKind::PartialArity => 2,
    RecordLinkKind::SuccessorFrame => 3,
    _ => 5,
  };
  bad |= left[unused..].iter().chain(&right[unused..]).any(|word| *word != 0);
  if enabled {
    bad |= match kind {
      RecordLinkKind::ExactArity => left[0] != right[0] || left[1] != right[1],
      RecordLinkKind::PartialArity => {
        left[0] != right[0] || left[1] >= right[1]
      },
      RecordLinkKind::SuccessorFrame => {
        left[0] != right[0]
          || left[1].checked_add(left[2]) != Some(right[1])
          || right[1] > right[2]
      },
      RecordLinkKind::ConstructorValue => left != right,
      RecordLinkKind::DistinctConstructors => left[..4] == right[..4],
    };
  }
  F128::new(u64::from(bad), 0)
}
