//! Small builder for custom block-diagonal Boolean R1CS tables.
//!
//! Flock fixes `C = I`, so every constraint row also names its output
//! variable. This builder allocates derived variables in dependency order,
//! records their `(linear A) * (linear B) = output` operations once, and uses
//! that same record for both the sparse matrices and native witness filling.

use std::sync::OnceLock;

use flock_prover::{
  bits::transpose_8_u64s_to_64_bytes,
  field::F128,
  lincheck::pack_z_lincheck,
  r1cs::{BlockR1cs, SparseBinaryMatrix, WitnessLayout},
  schedule::{TableClass, TableType},
  scratch,
  union::SlotWitnessDest,
};
use rayon::prelude::*;

/// Move a freshly built Boolean R1CS into a union table without cloning its
/// sparse matrices. `TableType::from_block_r1cs` accepts a borrow and must
/// deep-copy all three matrices, which is especially costly for BLAKE3.
pub(crate) fn table_from_block_r1cs(r1cs: BlockR1cs) -> TableType {
  TableType {
    k_log: r1cs.k_log,
    useful_bits: r1cs.useful_bits,
    a_0: r1cs.a_0,
    b_0: r1cs.b_0,
    c_0: r1cs.c_0,
    const_pin: r1cs.const_pin,
    class: TableClass::Boolean,
    io_schema: Vec::new(),
  }
}

#[derive(Clone, Debug)]
struct BooleanOperation {
  output: usize,
  a: Vec<usize>,
  b: Vec<usize>,
}

/// A finished Boolean table plan, independent of its outer row capacity.
#[derive(Clone, Debug)]
pub(crate) struct BooleanR1csPlan {
  k_log: usize,
  useful_bits: usize,
  a_rows: Vec<Vec<usize>>,
  b_rows: Vec<Vec<usize>>,
  operations: Vec<BooleanOperation>,
  const_pin: Option<usize>,
}

impl BooleanR1csPlan {
  pub(crate) fn k_log(&self) -> usize {
    self.k_log
  }

  pub(crate) fn k(&self) -> usize {
    1usize << self.k_log
  }

  #[cfg(test)]
  pub(crate) fn useful_bits(&self) -> usize {
    self.useful_bits
  }

  pub(crate) fn block_r1cs(&self, nu: usize) -> BlockR1cs {
    assert!(nu >= 3, "Flock lincheck requires at least eight rows");
    let k = self.k();
    BlockR1cs {
      m: self.k_log + nu,
      k_log: self.k_log,
      k_skip: 6,
      useful_bits: self.useful_bits,
      a_0: sparse_matrix(k, self.a_rows.clone()),
      b_0: sparse_matrix(k, self.b_rows.clone()),
      c_0: sparse_matrix(k, (0..k).map(|row| vec![row]).collect()),
      layout: WitnessLayout::BatchMajor,
      const_pin: self.const_pin,
      digest_cache: OnceLock::new(),
      csc_cache: OnceLock::new(),
    }
  }

  /// Fill fixed/free columns, then derive every internal/output column from
  /// the same operation list that created the R1CS matrices.
  pub(crate) fn fill_row(
    &self,
    bits: &mut [bool],
    fill_free: impl FnOnce(&mut [bool]),
  ) {
    assert_eq!(bits.len(), self.k());
    bits.fill(false);
    if let Some(column) = self.const_pin {
      bits[column] = true;
    }
    fill_free(bits);
    for operation in &self.operations {
      let a = parity(bits, &operation.a);
      let b = parity(bits, &operation.b);
      bits[operation.output] = a & b;
    }
  }
}

/// Mutable construction half of [`BooleanR1csPlan`].
pub(crate) struct BooleanR1csBuilder {
  k_log: usize,
  k: usize,
  next_column: usize,
  a_rows: Vec<Vec<usize>>,
  b_rows: Vec<Vec<usize>>,
  assigned: Vec<bool>,
  operations: Vec<BooleanOperation>,
  const_pin: Option<usize>,
}

impl BooleanR1csBuilder {
  /// Reserve `[0, reserved_columns)` for word-aligned circuit I/O.
  pub(crate) fn new(k_log: usize, reserved_columns: usize) -> Self {
    assert!(k_log >= 7, "BatchMajor Boolean tables need k_log >= 7");
    let k = 1usize << k_log;
    assert!(reserved_columns <= k);
    Self {
      k_log,
      k,
      next_column: reserved_columns,
      a_rows: vec![Vec::new(); k],
      b_rows: vec![Vec::new(); k],
      assigned: vec![false; k],
      operations: Vec::new(),
      const_pin: None,
    }
  }

  /// Mark a supplied bit as free Boolean advice (`x * x = x`).
  pub(crate) fn free_boolean_at(&mut self, column: usize) {
    self.set_constraint(column, vec![column], vec![column], false);
  }

  /// Require a supplied Boolean advice bit to be zero.
  ///
  /// With `one = 1`, the constraint `x * (x + one) = x` accepts `x = 0`
  /// and rejects `x = 1`. This is useful for word-aligned gates whose logical
  /// input occupies only one lane of an `F128` word.
  pub(crate) fn assert_zero_at(&mut self, column: usize, one: usize) {
    self.set_constraint(column, vec![column], vec![column, one], false);
  }

  /// Allocate one supplied Boolean advice bit after the reserved I/O region.
  pub(crate) fn alloc_free_boolean(&mut self) -> usize {
    let column = self.alloc_column();
    self.free_boolean_at(column);
    column
  }

  /// Allocate the table's one constant-one column and bind it through
  /// Flock's count-aware lincheck pin.
  pub(crate) fn alloc_constant_one(&mut self) -> usize {
    assert!(self.const_pin.is_none(), "constant-one column already allocated");
    let column = self.alloc_free_boolean();
    self.const_pin = Some(column);
    column
  }

  pub(crate) fn and(&mut self, lhs: usize, rhs: usize) -> usize {
    self.alloc_gate(vec![lhs], vec![rhs])
  }

  /// Multiply two non-empty GF(2) linear forms.
  ///
  /// This is useful for compact full adders: `z * (x + y)` is one R1CS
  /// constraint and does not need an intermediate column for `x + y`.
  pub(crate) fn product_of_parities(
    &mut self,
    lhs: &[usize],
    rhs: &[usize],
  ) -> usize {
    assert!(!lhs.is_empty());
    assert!(!rhs.is_empty());
    self.alloc_gate(lhs.to_vec(), rhs.to_vec())
  }

  /// Derive a pre-reserved output from two GF(2) linear forms.
  pub(crate) fn write_product_of_parities(
    &mut self,
    output: usize,
    lhs: &[usize],
    rhs: &[usize],
  ) {
    assert!(!lhs.is_empty());
    assert!(!rhs.is_empty());
    self.set_constraint(output, lhs.to_vec(), rhs.to_vec(), true);
  }

  /// XOR a non-empty set of bits using multiplication by the pinned one.
  pub(crate) fn xor(&mut self, inputs: &[usize], one: usize) -> usize {
    assert!(!inputs.is_empty());
    self.alloc_gate(inputs.to_vec(), vec![one])
  }

  /// Derive a pre-reserved output bit instead of allocating a new column.
  pub(crate) fn write_xor(
    &mut self,
    output: usize,
    inputs: &[usize],
    one: usize,
  ) {
    assert!(!inputs.is_empty());
    self.set_constraint(output, inputs.to_vec(), vec![one], true);
  }

  pub(crate) fn finish(self) -> BooleanR1csPlan {
    BooleanR1csPlan {
      k_log: self.k_log,
      useful_bits: self.next_column,
      a_rows: self.a_rows,
      b_rows: self.b_rows,
      operations: self.operations,
      const_pin: self.const_pin,
    }
  }

  fn alloc_gate(&mut self, a: Vec<usize>, b: Vec<usize>) -> usize {
    let output = self.alloc_column();
    self.set_constraint(output, a, b, true);
    output
  }

  fn alloc_column(&mut self) -> usize {
    assert!(self.next_column < self.k, "Boolean R1CS table exceeded 2^k_log");
    let column = self.next_column;
    self.next_column += 1;
    column
  }

  fn set_constraint(
    &mut self,
    output: usize,
    a: Vec<usize>,
    b: Vec<usize>,
    derive: bool,
  ) {
    assert!(output < self.k);
    assert!(!self.assigned[output], "Boolean column {output} assigned twice");
    assert!(a.iter().chain(&b).all(|&column| column < self.k));
    self.a_rows[output] = a.clone();
    self.b_rows[output] = b.clone();
    self.assigned[output] = true;
    if derive {
      self.operations.push(BooleanOperation { output, a, b });
    }
  }
}

/// Produce Flock's BatchMajor `(z, A z, B z, lincheck stripe)` tuple from a
/// row filler that supplies only the plan's free columns.
pub(crate) fn generate_boolean_witness<T>(
  plan: &BooleanR1csPlan,
  rows: &[T],
  nu: usize,
  fill_free: impl Fn(&T, &mut [bool]),
) -> (Vec<F128>, Vec<F128>, Vec<F128>, Vec<u8>) {
  let capacity = 1usize << nu;
  assert!(rows.len() <= capacity);
  let r1cs = plan.block_r1cs(nu);
  let k = plan.k();
  let mut z = vec![false; r1cs.n()];
  for (outer, row) in rows.iter().enumerate() {
    plan.fill_row(&mut z[outer * k..(outer + 1) * k], |bits| {
      fill_free(row, bits)
    });
  }
  let a = r1cs.apply_a(&z);
  let b = r1cs.apply_b(&z);
  assert!(
    a.iter()
      .zip(&b)
      .zip(&z)
      .all(|((a_bit, b_bit), z_bit)| (*a_bit & *b_bit) == *z_bit),
    "custom Boolean witness does not satisfy its R1CS"
  );
  let stripe = pack_z_lincheck(&z, r1cs.m, r1cs.k_log);
  (
    pack_batch_major(&z, plan.k_log(), nu),
    pack_batch_major(&a, plan.k_log(), nu),
    pack_batch_major(&b, plan.k_log(), nu),
    stripe,
  )
}

/// Generate a partial-count Boolean witness directly into one union slot.
///
/// The allocating compatibility driver above constructs three logical
/// `capacity * k` bit-vectors, applies both sparse matrices over every dummy
/// row, repacks all three vectors, and then makes the union copy them again.
/// Stage 3 tables are deliberately sparse, so that work is overwhelmingly
/// padding. This driver evaluates only declared rows, eight at a time (the
/// lincheck stripe's native grouping), and writes their packed words directly
/// into Flock's pooled union buffers.
pub(crate) fn generate_boolean_witness_into<T: Sync>(
  plan: &BooleanR1csPlan,
  rows: &[T],
  nu: usize,
  dst: SlotWitnessDest<'_>,
  fill_free: impl Fn(&T, &mut [bool]) + Send + Sync,
) -> Vec<u8> {
  generate_boolean_rows_into(
    plan.k_log,
    plan.useful_bits,
    &plan.a_rows,
    &plan.b_rows,
    rows,
    nu,
    dst,
    |row, bits| plan.fill_row(bits, |bits| fill_free(row, bits)),
  )
}

/// Low-level form of [`generate_boolean_witness_into`] for Boolean tables
/// whose matrices and row filler predate [`BooleanR1csPlan`].
#[allow(clippy::too_many_arguments)]
pub(crate) fn generate_boolean_rows_into<T: Sync>(
  k_log: usize,
  useful_bits: usize,
  a_rows: &[Vec<usize>],
  b_rows: &[Vec<usize>],
  rows: &[T],
  nu: usize,
  dst: SlotWitnessDest<'_>,
  fill_row: impl Fn(&T, &mut [bool]) + Send + Sync,
) -> Vec<u8> {
  const GROUP_ROWS: usize = 8;
  const ZERO_CHUNK_WORDS: usize = 1 << 16;

  assert!(nu >= 3, "Flock lincheck requires at least eight rows");
  assert!(k_log >= 7, "BatchMajor Boolean tables need k_log >= 7");
  let capacity = 1usize << nu;
  let k = 1usize << k_log;
  assert!(rows.len() <= capacity);
  assert!(useful_bits <= k);
  assert_eq!(a_rows.len(), k);
  assert_eq!(b_rows.len(), k);

  let chunks = k / 128;
  let slot_words = capacity * chunks;
  let useful_chunks = useful_bits.div_ceil(128);
  let useful_words = useful_bits.div_ceil(64);
  let stored_words = 2 * useful_chunks;
  let SlotWitnessDest { z, a, b, elide_padding_writes } = dst;
  for buffer in [&*z, &*a, &*b] {
    assert_eq!(buffer.len(), slot_words, "Boolean slot destination length");
  }

  // When padding is observable, initialize it once with parallel contiguous
  // stores. The merged union path marks it unread, so production normally
  // skips this multi-gigabyte memset entirely.
  if !elide_padding_writes {
    rayon::join(
      || {
        z.par_chunks_mut(ZERO_CHUNK_WORDS)
          .for_each(|chunk| chunk.fill(F128::ZERO));
      },
      || {
        rayon::join(
          || {
            a.par_chunks_mut(ZERO_CHUNK_WORDS)
              .for_each(|chunk| chunk.fill(F128::ZERO));
          },
          || {
            b.par_chunks_mut(ZERO_CHUNK_WORDS)
              .for_each(|chunk| chunk.fill(F128::ZERO));
          },
        );
      },
    );
  }

  let stripe_len = capacity * k / GROUP_ROWS;
  let mut stripe = scratch::take_u8(stripe_len);
  if !elide_padding_writes {
    stripe.par_chunks_mut(1 << 20).for_each(|chunk| chunk.fill(0));
  }

  let z_ptr = SendPtr(z.as_mut_ptr());
  let a_ptr = SendPtr(a.as_mut_ptr());
  let b_ptr = SendPtr(b.as_mut_ptr());
  let stripe_ptr = SendPtr(stripe.as_mut_ptr());
  let groups = rows.len().div_ceil(GROUP_ROWS);

  (0..groups).into_par_iter().for_each_init(
    || BooleanGroupScratch::new(k, stored_words),
    |scratch, group| {
      scratch.clear_words();
      let first_row = group * GROUP_ROWS;
      let live = rows.len().saturating_sub(first_row).min(GROUP_ROWS);
      for lane in 0..live {
        scratch.z_bits.fill(false);
        scratch.a_bits.fill(false);
        scratch.b_bits.fill(false);
        fill_row(&rows[first_row + lane], &mut scratch.z_bits);
        for column in 0..useful_bits {
          let a_bit = parity(&scratch.z_bits, &a_rows[column]);
          let b_bit = parity(&scratch.z_bits, &b_rows[column]);
          scratch.a_bits[column] = a_bit;
          scratch.b_bits[column] = b_bit;
          assert_eq!(
            a_bit & b_bit,
            scratch.z_bits[column],
            "custom Boolean witness does not satisfy column {column}",
          );
        }
        for word in 0..useful_words {
          let bit = word * 64;
          scratch.z_words[word][lane] = pack_bool_word(&scratch.z_bits, bit);
          scratch.a_words[word][lane] = pack_bool_word(&scratch.a_bits, bit);
          scratch.b_words[word][lane] = pack_bool_word(&scratch.b_bits, bit);
        }
      }

      // Every group owns disjoint row positions in every chunk-column and a
      // disjoint `k`-byte stripe block. The raw pointers avoid materializing
      // and then copying a second capacity-sized set of slot buffers.
      for chunk in 0..useful_chunks {
        for lane in 0..live {
          let at = (chunk << nu) + first_row + lane;
          let word = 2 * chunk;
          unsafe {
            z_ptr.get().add(at).write(F128::new(
              scratch.z_words[word][lane],
              scratch.z_words[word + 1][lane],
            ));
            a_ptr.get().add(at).write(F128::new(
              scratch.a_words[word][lane],
              scratch.a_words[word + 1][lane],
            ));
            b_ptr.get().add(at).write(F128::new(
              scratch.b_words[word][lane],
              scratch.b_words[word + 1][lane],
            ));
          }
        }
      }

      let stripe_base = group * k;
      for (word, lanes) in scratch.z_words.iter().take(useful_words).enumerate()
      {
        let out = unsafe {
          std::slice::from_raw_parts_mut(
            stripe_ptr.get().add(stripe_base + word * 64),
            64,
          )
        };
        transpose_8_u64s_to_64_bytes(lanes, out);
      }
      if elide_padding_writes {
        let tail_start = stripe_base + useful_words * 64;
        let tail_len = k - useful_words * 64;
        if tail_len != 0 {
          unsafe {
            std::slice::from_raw_parts_mut(
              stripe_ptr.get().add(tail_start),
              tail_len,
            )
            .fill(0);
          }
        }
      }
    },
  );

  stripe
}

struct BooleanGroupScratch {
  z_bits: Vec<bool>,
  a_bits: Vec<bool>,
  b_bits: Vec<bool>,
  z_words: Vec<[u64; 8]>,
  a_words: Vec<[u64; 8]>,
  b_words: Vec<[u64; 8]>,
}

impl BooleanGroupScratch {
  fn new(k: usize, stored_words: usize) -> Self {
    Self {
      z_bits: vec![false; k],
      a_bits: vec![false; k],
      b_bits: vec![false; k],
      z_words: vec![[0; 8]; stored_words],
      a_words: vec![[0; 8]; stored_words],
      b_words: vec![[0; 8]; stored_words],
    }
  }

  fn clear_words(&mut self) {
    self.z_words.fill([0; 8]);
    self.a_words.fill([0; 8]);
    self.b_words.fill([0; 8]);
  }
}

#[derive(Clone, Copy)]
struct SendPtr<T>(*mut T);

unsafe impl<T> Send for SendPtr<T> {}
unsafe impl<T> Sync for SendPtr<T> {}

impl<T> SendPtr<T> {
  fn get(self) -> *mut T {
    self.0
  }
}

fn pack_bool_word(bits: &[bool], start: usize) -> u64 {
  bits[start..start + 64]
    .iter()
    .enumerate()
    .fold(0, |word, (bit, value)| word | (u64::from(*value) << bit))
}

pub(crate) fn write_f128(bits: &mut [bool], offset: usize, value: F128) {
  assert!(offset + 128 <= bits.len());
  for local in 0..64 {
    bits[offset + local] = (value.lo >> local) & 1 == 1;
    bits[offset + 64 + local] = (value.hi >> local) & 1 == 1;
  }
}

fn parity(bits: &[bool], columns: &[usize]) -> bool {
  columns.iter().fold(false, |value, &column| value ^ bits[column])
}

fn sparse_matrix(k: usize, rows: Vec<Vec<usize>>) -> SparseBinaryMatrix {
  SparseBinaryMatrix { num_rows: k, num_cols: k, rows }
}

fn pack_batch_major(bits: &[bool], k_log: usize, nu: usize) -> Vec<F128> {
  let capacity = 1usize << nu;
  let k = 1usize << k_log;
  assert_eq!(bits.len(), capacity * k);
  let chunks = k / 128;
  let mut packed = vec![F128::ZERO; chunks * capacity];
  for chunk in 0..chunks {
    for outer in 0..capacity {
      let start = outer * k + chunk * 128;
      let mut lo = 0u64;
      let mut hi = 0u64;
      for local in 0..64 {
        lo |= u64::from(bits[start + local]) << local;
        hi |= u64::from(bits[start + 64 + local]) << local;
      }
      packed[(chunk << nu) + outer] = F128::new(lo, hi);
    }
  }
  packed
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn one_description_builds_matrices_and_witness() {
    let mut builder = BooleanR1csBuilder::new(7, 3);
    builder.free_boolean_at(0);
    builder.free_boolean_at(1);
    let one = builder.alloc_constant_one();
    let product = builder.and(0, 1);
    builder.write_xor(2, &[product, 0], one);
    let plan = builder.finish();
    let r1cs = plan.block_r1cs(3);

    for (x, y) in [(false, false), (false, true), (true, false), (true, true)] {
      let mut row = vec![false; plan.k()];
      plan.fill_row(&mut row, |bits| {
        bits[0] = x;
        bits[1] = y;
      });
      assert_eq!(row[2], (x & y) ^ x);
      let mut witness = vec![false; r1cs.n()];
      witness[..plan.k()].copy_from_slice(&row);
      assert!(r1cs.satisfies(&witness));
    }
  }

  #[test]
  fn in_place_partial_driver_matches_allocating_driver() {
    let mut builder = BooleanR1csBuilder::new(7, 3);
    builder.free_boolean_at(0);
    builder.free_boolean_at(1);
    let one = builder.alloc_constant_one();
    let product = builder.and(0, 1);
    builder.write_xor(2, &[product, 0], one);
    let plan = builder.finish();
    let rows = [(false, false), (true, false), (false, true), (true, true)];
    let nu = 4;
    let fill = |row: &(bool, bool), bits: &mut [bool]| {
      bits[0] = row.0;
      bits[1] = row.1;
    };
    let expected = generate_boolean_witness(&plan, &rows, nu, fill);

    let words = 1usize << (nu + plan.k_log() - 7);
    let mut z = vec![F128::ZERO; words];
    let mut a = vec![F128::ZERO; words];
    let mut b = vec![F128::ZERO; words];
    let stripe = generate_boolean_witness_into(
      &plan,
      &rows,
      nu,
      SlotWitnessDest {
        z: &mut z,
        a: &mut a,
        b: &mut b,
        elide_padding_writes: false,
      },
      fill,
    );

    assert_eq!(z, expected.0);
    assert_eq!(a, expected.1);
    assert_eq!(b, expected.2);
    assert_eq!(stripe, expected.3);
  }
}
