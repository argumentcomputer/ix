use super::switch::SWITCHES_PER_ROW;
use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_packed_rows_into,
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

/// The same exact whole-record switch as `SwitchGate`, expressed over bits.
/// Only bit zero of each selector may be set; no fingerprint replaces a word.
#[derive(Clone)]
pub struct BooleanSwitchGate {
  nu: usize,
  words: usize,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct BooleanSwitchRow(pub(crate) Vec<F128>);

impl BooleanSwitchGate {
  pub fn new(nu: usize, words: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "Boolean switch row domain");
    ensure!((1..=32).contains(&words), "memory record word capacity");
    Ok(Self { nu, words, plan: Arc::new(OnceLock::new()) })
  }
  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| {
      let input = self.input_count();
      let reserved =
        (input + self.output_count() + SWITCHES_PER_ROW * self.words) * 128;
      let columns = reserved + 1;
      let mut b = BooleanR1csBuilder::new(
        columns.next_power_of_two().ilog2() as usize,
        reserved,
      );
      let one = b.alloc_constant_one();
      for lane in 0..SWITCHES_PER_ROW {
        let at = lane * (1 + 2 * self.words) * 128;
        b.free_boolean_at(at);
        for bit in 1..128 {
          b.assert_zero_at(at + bit, one);
        }
        for word in 0..self.words {
          for bit in 0..128 {
            let left = at + (1 + word) * 128 + bit;
            let right = left + self.words * 128;
            b.free_boolean_at(left);
            b.free_boolean_at(right);
            let delta =
              (input + self.output_count() + lane * self.words + word) * 128
                + bit;
            b.write_product_of_parities(delta, &[at], &[left, right]);
            let out = (input + 2 * lane * self.words + word) * 128 + bit;
            b.write_xor(out, &[left, delta], one);
            b.write_xor(out + self.words * 128, &[right, delta], one);
          }
        }
      }
      b.finish()
    })
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[BooleanSwitchRow],
    dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    let plan = self.plan();
    let useful_bits = (self.input_count()
      + self.output_count()
      + SWITCHES_PER_ROW * self.words)
      * 128
      + 1;
    generate_boolean_packed_rows_into(
      plan.k_log(),
      useful_bits,
      rows,
      self.nu,
      dst,
      |row, z, a, b| self.fill_packed(row, z, a, b),
    )
  }
  fn fill_packed(
    &self,
    row: &BooleanSwitchRow,
    z: &mut [F128],
    a: &mut [F128],
    b: &mut [F128],
  ) {
    let input = self.input_count();
    let output = self.output_count();
    let all = F128::new(u64::MAX, u64::MAX);
    assert_eq!(row.0.len(), input);
    z[..input].copy_from_slice(&row.0);
    a[..input].copy_from_slice(&row.0);
    b[..input].copy_from_slice(&row.0);
    for lane in 0..SWITCHES_PER_ROW {
      let at = lane * (1 + 2 * self.words);
      let selector = row.0[at];
      assert!(selector == F128::ZERO || selector == F128::ONE);
      b[at] += F128::new(u64::MAX - 1, u64::MAX);
      let mask = if selector == F128::ONE { all } else { F128::ZERO };
      for word in 0..self.words {
        let left = row.0[at + 1 + word];
        let right = row.0[at + 1 + self.words + word];
        let delta =
          if selector == F128::ONE { left + right } else { F128::ZERO };
        let d = input + output + lane * self.words + word;
        z[d] = delta;
        a[d] = mask;
        b[d] = left + right;
        let out = input + 2 * lane * self.words + word;
        for (column, value) in
          [(out, left + delta), (out + self.words, right + delta)]
        {
          z[column] = value;
          a[column] = value;
          b[column] = all;
        }
      }
    }
    let one = input + output + SWITCHES_PER_ROW * self.words;
    z[one] = F128::ONE;
    a[one] = F128::ONE;
    b[one] = F128::ONE;
  }
}
impl CountedGate for BooleanSwitchGate {
  fn input_count(&self) -> usize {
    SWITCHES_PER_ROW * (1 + 2 * self.words)
  }
  fn output_count(&self) -> usize {
    SWITCHES_PER_ROW * 2 * self.words
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for BooleanSwitchGate {
  type Row = BooleanSwitchRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..self.input_count())
        .map(IoWord::input)
        .chain(
          (self.input_count()..self.input_count() + self.output_count())
            .map(IoWord::output),
        )
        .collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), out: &mut Vec<F128>) -> Self::Row {
    assert_eq!(input.len(), self.input_count());
    for lane in input.chunks_exact(1 + 2 * self.words) {
      assert!(lane[0] == F128::ZERO || lane[0] == F128::ONE);
      let (left, right) = lane[1..].split_at(self.words);
      let (first, second) =
        if lane[0] == F128::ZERO { (left, right) } else { (right, left) };
      out.extend_from_slice(first);
      out.extend_from_slice(second);
    }
    BooleanSwitchRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ixby::bits::{fill_words, read_words};

  #[test]
  fn boolean_switch_constraints_bind_every_word_and_all_selector_bits() {
    // Check matrices directly, bypassing the native evaluator's selector check.
    for words in [1, 5, 6, 26] {
      let gate = BooleanSwitchGate::new(3, words).unwrap();
      let element = super::super::SwitchGate::new(words).unwrap();
      let mut input = Vec::new();
      for lane in 0..SWITCHES_PER_ROW {
        input.push(F128::new((lane % 2) as u64, 0));
        input.extend((0..2 * words).map(|word| {
          F128::new(((lane + 17) * (word + 19)) as u64, !(word as u64))
        }));
      }
      let mut expected = Vec::new();
      element.eval(&input, &(), &mut expected);
      let table = gate.r1cs();
      let mut bits = vec![false; table.n()];
      gate
        .plan()
        .fill_row(&mut bits[..gate.plan().k()], |b| fill_words(&input, b));
      assert!(table.satisfies(&bits));
      assert_eq!(
        read_words(&bits, gate.input_count(), gate.output_count()),
        expected
      );
      let rejects_row = |bits: &[bool], row: usize| {
        let parity =
          |columns: &[usize]| columns.iter().fold(false, |s, &c| s ^ bits[c]);
        (parity(&table.a_0.rows[row]) & parity(&table.b_0.rows[row]))
          != bits[row]
      };
      // Alter a bit in each complete output word, with derived columns
      // held fixed, to exercise wiring on both halves of each record.
      for word in gate.input_count()..gate.input_count() + gate.output_count() {
        let at = word * 128 + 127;
        bits[at] ^= true;
        assert!(rejects_row(&bits, at));
        bits[at] ^= true;
      }
      for lane in 0..SWITCHES_PER_ROW {
        for bit in 1..128 {
          let at = lane * (1 + 2 * words) * 128 + bit;
          bits[at] = true;
          assert!(rejects_row(&bits, at));
          bits[at] = false;
        }
      }
    }
  }

  #[test]
  fn packed_switch_clears_small_row_domains() {
    let gate = BooleanSwitchGate::new(3, 6).unwrap();
    let rows = vec![BooleanSwitchRow(vec![F128::ZERO; gate.input_count()]); 7];
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |r, b| fill_words(&r.0, b),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }

  #[test]
  fn packed_switch_witness_matches_sparse_matrices_and_recycled_padding() {
    use crate::boolean::generate_boolean_witness;
    for words in [1, 5, 6, 26] {
      let gate = BooleanSwitchGate::new(6, words).unwrap();
      let rows: Vec<_> = (0..9)
        .map(|row| {
          let mut input = Vec::new();
          for lane in 0..SWITCHES_PER_ROW {
            input.push(F128::new(((row + lane) % 2) as u64, 0));
            input.extend((0..2 * words).map(|word| {
              F128::new(
                ((row + 17) * (lane + 19) * (word + 23)) as u64,
                !((row + lane + word) as u64),
              )
            }));
          }
          BooleanSwitchRow(input)
        })
        .collect();
      for count in [0, 1, 7, 8, 9] {
        let expected =
          generate_boolean_witness(gate.plan(), &rows[..count], 6, |r, b| {
            fill_words(&r.0, b)
          });
        let poison = F128::new(u64::MAX, u64::MAX);
        for elide in [false, true] {
          let mut z = vec![poison; expected.0.len()];
          let mut a = z.clone();
          let mut b = z.clone();
          let stripe = gate.generate_witness_into(
            &rows[..count],
            SlotWitnessDest {
              z: &mut z,
              a: &mut a,
              b: &mut b,
              elide_padding_writes: elide,
            },
          );
          if elide {
            let columns = gate.plan().useful_bits().div_ceil(128);
            for (got, want) in
              [(&z, &expected.0), (&a, &expected.1), (&b, &expected.2)]
            {
              for (column, chunk) in got.as_chunks::<64>().0.iter().enumerate()
              {
                for (row, &value) in chunk.iter().enumerate() {
                  assert_eq!(
                    value,
                    if column < columns && row < count.div_ceil(8) * 8 {
                      want[column * 64 + row]
                    } else {
                      poison
                    }
                  );
                }
              }
            }
            let live = count.div_ceil(8) * gate.plan().k();
            assert_eq!(stripe[..live], expected.3[..live]);
          } else {
            assert_eq!((z, a, b, stripe), expected);
          }
        }
      }
    }
  }
}
