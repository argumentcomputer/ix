use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  },
  ixby::bits::{
    any, equal, equal_constant, fill_words, require, require_zero, subtract,
  },
  sizing::CountedGate,
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{GateType, SlotWitness},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};
use std::sync::{Arc, OnceLock};

/// Records are [address:u64, time:u64, kind, value_lo:F128, value_hi:F128].
/// Seed (0) and seal (3) must come from authenticated boundary openings.
/// Read (1) preserves the preceding value; write (2) replaces it. Padding (4)
/// is canonical and appears only after every real address has been sealed.
pub const RECORD_WORDS: usize = 5;
pub const SEED: u64 = 0;
pub const READ: u64 = 1;
pub const WRITE: u64 = 2;
pub const SEAL: u64 = 3;
pub const PAD: u64 = 4;

#[derive(Clone)]
pub struct AuditGate {
  nu: usize,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct AuditRow(pub(super) Vec<F128>);
impl AuditGate {
  pub fn new(nu: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "memory audit row domain");
    Ok(Self { nu, plan: Arc::new(OnceLock::new()) })
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(build)
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[AuditRow],
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
  pub(super) fn evaluate(input: &[F128]) -> F128 {
    assert_eq!(input.len(), 12);
    let previous = &input[..5];
    let current = &input[5..10];
    let first = input[10].lo & 1 != 0;
    let last = input[11].lo & 1 != 0;
    let valid_flags = input[10].hi == 0
      && input[10].lo <= 1
      && input[11].hi == 0
      && input[11].lo <= 1;
    let kind = current[2];
    let pad = kind == F128::new(PAD, 0);
    let seed = kind == F128::new(SEED, 0);
    let seal = kind == F128::new(SEAL, 0);
    let read = kind == F128::new(READ, 0);
    let mut valid = valid_flags
      && current[0].hi == 0
      && current[1].hi == 0
      && kind.hi == 0
      && kind.lo <= PAD;
    if pad {
      valid &= [0, 1, 3, 4].iter().all(|&i| current[i] == F128::ZERO);
    } else if seed {
      valid &= current[1] == F128::ZERO;
    } else if seal {
      valid &= current[1] == F128::new(u64::MAX, 0);
    } else {
      valid &= current[1].lo != 0 && current[1].lo != u64::MAX;
    }
    if first {
      valid &= seed || pad;
    } else if previous[2] == F128::new(PAD, 0) {
      valid &= pad;
    } else if pad {
      valid &= previous[2] == F128::new(SEAL, 0);
    } else if current[0] == previous[0] {
      valid &= !seed
        && previous[2] != F128::new(SEAL, 0)
        && previous[1].lo < current[1].lo;
      if read || seal {
        valid &= current[3..5] == previous[3..5];
      }
    } else {
      valid &= previous[0].lo < current[0].lo
        && previous[2] == F128::new(SEAL, 0)
        && seed;
    }
    if last {
      valid &= seal || pad;
    }
    F128::new(u64::from(!valid), 0)
  }
}
impl CountedGate for AuditGate {
  fn input_count(&self) -> usize {
    12
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
impl GateType for AuditGate {
  type Row = AuditRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..12).map(IoWord::input).chain([IoWord::output(12)]).collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> AuditRow {
    output.push(Self::evaluate(input));
    AuditRow(input.to_vec())
  }
  fn witness(&self, _: &[AuditRow], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

fn word(at: usize) -> Vec<usize> {
  (128 * at..128 * (at + 1)).collect()
}
fn constant(
  b: &mut BooleanR1csBuilder,
  one: usize,
  at: usize,
  value: u64,
) -> usize {
  let bits = word(at);
  let low = equal_constant(b, one, &bits[..64], value);
  let high = equal_constant(b, one, &bits[64..], 0);
  b.and(low, high)
}
fn build() -> BooleanR1csPlan {
  let mut b = BooleanR1csBuilder::new(14, 13 * 128);
  for bit in 0..12 * 128 {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let mut bad = Vec::new();
  bad.extend(5 * 128 + 64..6 * 128);
  bad.extend(6 * 128 + 64..7 * 128);
  bad.extend(10 * 128 + 1..11 * 128);
  bad.extend(11 * 128 + 1..12 * 128);
  let first = 10 * 128;
  let last = 11 * 128;
  let next = b.xor(&[first, one], one);
  let kinds =
    (0..=PAD).map(|v| constant(&mut b, one, 7, v)).collect::<Vec<_>>();
  let valid_kind = any(&mut b, one, &kinds);
  require(&mut b, one, &mut bad, one, valid_kind);
  let [seed, read, write, seal, pad] = <[usize; 5]>::try_from(kinds).unwrap();
  let nonpad = b.xor(&[pad, one], one);
  for at in [5, 6, 8, 9] {
    require_zero(&mut b, one, &mut bad, pad, &word(at));
  }
  let time_zero = constant(&mut b, one, 6, 0);
  let time_max = constant(&mut b, one, 6, u64::MAX);
  require(&mut b, one, &mut bad, seed, time_zero);
  require(&mut b, one, &mut bad, seal, time_max);
  let access = any(&mut b, one, &[read, write]);
  require_zero(&mut b, one, &mut bad, access, &[time_zero, time_max]);
  let start = any(&mut b, one, &[seed, pad]);
  require(&mut b, one, &mut bad, first, start);
  let end = any(&mut b, one, &[seal, pad]);
  require(&mut b, one, &mut bad, last, end);

  let previous_pad = constant(&mut b, one, 2, PAD);
  let previous_seal = constant(&mut b, one, 2, SEAL);
  let previous_nonpad = b.xor(&[previous_pad, one], one);
  let after_pad = b.and(next, previous_pad);
  require(&mut b, one, &mut bad, after_pad, pad);
  let has_previous = b.and(next, previous_nonpad);
  let ending = b.and(has_previous, pad);
  require(&mut b, one, &mut bad, ending, previous_seal);
  let data = b.and(has_previous, nonpad);
  let same = equal(&mut b, one, &word(0), &word(5));
  let different = b.xor(&[same, one], one);
  let same_data = b.and(data, same);
  require_zero(&mut b, one, &mut bad, same_data, &[seed, previous_seal]);
  let increasing_time =
    subtract(&mut b, one, zero, &word(1)[..64], &word(6)[..64]).1;
  require(&mut b, one, &mut bad, same_data, increasing_time);
  let preserve = any(&mut b, one, &[read, seal]);
  let preserve = b.and(same_data, preserve);
  for (left, right) in [(3, 8), (4, 9)] {
    let eq = equal(&mut b, one, &word(left), &word(right));
    require(&mut b, one, &mut bad, preserve, eq);
  }
  let new_address = b.and(data, different);
  let increasing_address =
    subtract(&mut b, one, zero, &word(0)[..64], &word(5)[..64]).1;
  for condition in [increasing_address, previous_seal, seed] {
    require(&mut b, one, &mut bad, new_address, condition);
  }
  let invalid = any(&mut b, one, &bad);
  b.write_xor(12 * 128, &[invalid], one);
  for bit in 1..128 {
    b.write_xor(12 * 128 + bit, &[zero], one);
  }
  b.finish()
}
