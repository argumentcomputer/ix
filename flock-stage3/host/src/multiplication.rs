//! Boolean R1CS relation for multiplication in the Goldilocks base field.
//!
//! For canonical `a`, `b`, and `c`, the gate proves that a private 64-bit
//! quotient `q` satisfies the exact non-negative integer identity
//!
//! ```text
//! a * b + (q << 32) = c + q + (q << 64).
//! ```
//!
//! This is `a*b = c + q*(2^64 - 2^32 + 1)`, so canonical `c` is exactly
//! `a*b mod p`. The multiplication bits are reduced with a carry-save tree
//! before one ripple pass; this is substantially smaller than adding 64
//! shifted partial-product rows sequentially.

use std::sync::OnceLock;

use flock_prover::{
  circuit::builder::{GateType, SlotWitness},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};

use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness,
    generate_boolean_witness_into, write_f128,
  },
  goldilocks::GOLDILOCKS_MODULUS,
};

const MUL_K_LOG: usize = 16;
const LEFT_BASE: usize = 0;
const RIGHT_BASE: usize = 128;
const RESULT_BASE: usize = 256;
const LOW_RESIDUAL_BASE: usize = 384;
const HIGH_RESIDUAL_BASE: usize = 512;
const TOP_RESIDUAL_BASE: usize = 640;
const RESERVED_COLUMNS: usize = 768;

// Both sides of the quotient identity are below 2^129 for all 64-bit
// inputs. Comparing 130 sum bits is therefore an exact integer comparison,
// not merely equality modulo a power of two.
const INTEGER_SUM_BITS: usize = 130;

/// One row of two independent Goldilocks multiplications packed by u64 lane.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct GoldilocksMulPairRow {
  left: F128,
  right: F128,
}

/// Two lane-wise Goldilocks multiplications with explicit equation outputs.
///
/// The result is the first output. Callers must connect all residual words
/// to zero and route the two inputs and result through the shared canonical
/// Goldilocks table.
#[derive(Clone, Copy, Debug)]
pub(crate) struct GoldilocksMulPairGate {
  pub(crate) nu: usize,
}

impl GateType for GoldilocksMulPairGate {
  type Row = GoldilocksMulPairRow;
  type Hint = ();

  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(build_goldilocks_mul_r1cs(self.nu))
      .with_io_schema(vec![
        IoWord::input(0),
        IoWord::input(1),
        IoWord::output(2),
        IoWord::output(3),
        IoWord::output(4),
        IoWord::output(5),
      ])
  }

  fn eval(
    &self,
    inputs: &[F128],
    _hint: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let left = inputs[0];
    let right = inputs[1];
    outputs.extend_from_slice(&[
      F128::new(
        goldilocks_mul(left.lo, right.lo),
        goldilocks_mul(left.hi, right.hi),
      ),
      F128::ZERO,
      F128::ZERO,
      F128::ZERO,
    ]);
    GoldilocksMulPairRow { left, right }
  }

  fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

struct GoldilocksMulPlan {
  boolean: BooleanR1csPlan,
  quotient_bits: [[usize; 64]; 2],
}

pub(crate) fn build_goldilocks_mul_r1cs(nu: usize) -> BlockR1cs {
  goldilocks_mul_plan().boolean.block_r1cs(nu)
}

pub(crate) fn generate_goldilocks_mul_witness(
  rows: &[GoldilocksMulPairRow],
  nu: usize,
) -> (Vec<F128>, Vec<F128>, Vec<F128>, Vec<u8>) {
  let plan = goldilocks_mul_plan();
  generate_boolean_witness(&plan.boolean, rows, nu, |row, bits| {
    fill_goldilocks_mul_row(plan, *row, bits)
  })
}

pub(crate) fn generate_goldilocks_mul_witness_into(
  rows: &[GoldilocksMulPairRow],
  nu: usize,
  dst: SlotWitnessDest<'_>,
) -> Vec<u8> {
  let plan = goldilocks_mul_plan();
  generate_boolean_witness_into(&plan.boolean, rows, nu, dst, |row, bits| {
    fill_goldilocks_mul_row(plan, *row, bits)
  })
}

fn goldilocks_mul_plan() -> &'static GoldilocksMulPlan {
  static PLAN: OnceLock<GoldilocksMulPlan> = OnceLock::new();
  PLAN.get_or_init(build_goldilocks_mul_plan)
}

fn build_goldilocks_mul_plan() -> GoldilocksMulPlan {
  let mut builder = BooleanR1csBuilder::new(MUL_K_LOG, RESERVED_COLUMNS);
  for column in LEFT_BASE..RESULT_BASE + 128 {
    builder.free_boolean_at(column);
  }
  let one = builder.alloc_constant_one();
  let quotient_bits = std::array::from_fn(|_| {
    std::array::from_fn(|_| builder.alloc_free_boolean())
  });

  for (lane, quotient) in quotient_bits.iter().enumerate() {
    let lane_offset = lane * 64;
    let left: [usize; 64] =
      std::array::from_fn(|bit| LEFT_BASE + lane_offset + bit);
    let right: [usize; 64] =
      std::array::from_fn(|bit| RIGHT_BASE + lane_offset + bit);
    let result: [usize; 64] =
      std::array::from_fn(|bit| RESULT_BASE + lane_offset + bit);

    let mut left_columns = vec![Vec::new(); INTEGER_SUM_BITS + 1];
    for (left_bit, &left_column) in left.iter().enumerate() {
      for (right_bit, &right_column) in right.iter().enumerate() {
        let product = builder.and(left_column, right_column);
        left_columns[left_bit + right_bit].push(product);
      }
    }
    for (bit, &quotient_bit) in quotient.iter().enumerate() {
      left_columns[bit + 32].push(quotient_bit);
    }

    let mut right_columns = vec![Vec::new(); INTEGER_SUM_BITS + 1];
    for bit in 0..64 {
      right_columns[bit].push(result[bit]);
      right_columns[bit].push(quotient[bit]);
      right_columns[bit + 64].push(quotient[bit]);
    }

    let left_sum =
      sum_bit_columns(&mut builder, left_columns, one, INTEGER_SUM_BITS);
    let right_sum =
      sum_bit_columns(&mut builder, right_columns, one, INTEGER_SUM_BITS);
    for bit in 0..INTEGER_SUM_BITS {
      let residual = if bit < 128 {
        if bit < 64 {
          LOW_RESIDUAL_BASE + lane_offset + bit
        } else {
          HIGH_RESIDUAL_BASE + lane_offset + bit - 64
        }
      } else {
        TOP_RESIDUAL_BASE + lane_offset + bit - 128
      };
      let terms: Vec<_> =
        [left_sum[bit], right_sum[bit]].into_iter().flatten().collect();
      if !terms.is_empty() {
        builder.write_xor(residual, &terms, one);
      }
    }
  }

  GoldilocksMulPlan { boolean: builder.finish(), quotient_bits }
}

/// Convert a set of same-weight Boolean terms into canonical binary bits.
fn sum_bit_columns(
  builder: &mut BooleanR1csBuilder,
  mut columns: Vec<Vec<usize>>,
  one: usize,
  output_bits: usize,
) -> Vec<Option<usize>> {
  assert!(columns.len() > output_bits);

  // Carry-save reduction leaves at most two bits in each weight column.
  for bit in 0..output_bits {
    while columns[bit].len() > 2 {
      let third = columns[bit].pop().unwrap();
      let second = columns[bit].pop().unwrap();
      let first = columns[bit].pop().unwrap();
      let (sum, carry) = full_adder(builder, first, second, third, one);
      columns[bit].push(sum);
      columns[bit + 1].push(carry);
    }
  }

  // Add the final two carry-save rows with one ripple pass.
  let mut result = Vec::with_capacity(output_bits);
  let mut carry = None;
  for column in columns.iter().take(output_bits) {
    let mut terms = column.clone();
    if let Some(carry_bit) = carry.take() {
      terms.push(carry_bit);
    }
    match terms.as_slice() {
      [] => result.push(None),
      &[only] => result.push(Some(only)),
      &[first, second] => {
        let (sum, next_carry) = half_adder(builder, first, second, one);
        result.push(Some(sum));
        carry = Some(next_carry);
      },
      &[first, second, third] => {
        let (sum, next_carry) = full_adder(builder, first, second, third, one);
        result.push(Some(sum));
        carry = Some(next_carry);
      },
      _ => unreachable!("carry-save column contains more than two bits"),
    }
  }
  // The represented integers are strictly below 2^129. Any structurally
  // allocated carry at weight 2^130 is therefore the constant-zero Boolean
  // function; all of its source operations remain constrained in the table.
  result
}

fn half_adder(
  builder: &mut BooleanR1csBuilder,
  first: usize,
  second: usize,
  one: usize,
) -> (usize, usize) {
  (builder.xor(&[first, second], one), builder.and(first, second))
}

fn full_adder(
  builder: &mut BooleanR1csBuilder,
  first: usize,
  second: usize,
  third: usize,
  one: usize,
) -> (usize, usize) {
  let sum = builder.xor(&[first, second, third], one);
  let first_and_second = builder.and(first, second);
  let third_and_difference =
    builder.product_of_parities(&[third], &[first, second]);
  let carry = builder.xor(&[first_and_second, third_and_difference], one);
  (sum, carry)
}

fn fill_goldilocks_mul_row(
  plan: &GoldilocksMulPlan,
  row: GoldilocksMulPairRow,
  bits: &mut [bool],
) {
  let result = F128::new(
    goldilocks_mul(row.left.lo, row.right.lo),
    goldilocks_mul(row.left.hi, row.right.hi),
  );
  write_f128(bits, LEFT_BASE, row.left);
  write_f128(bits, RIGHT_BASE, row.right);
  write_f128(bits, RESULT_BASE, result);
  for (lane, quotient_columns) in plan.quotient_bits.iter().enumerate() {
    let (left, right) = if lane == 0 {
      (row.left.lo, row.right.lo)
    } else {
      (row.left.hi, row.right.hi)
    };
    let quotient = (left as u128 * right as u128) / GOLDILOCKS_MODULUS as u128;
    for (bit, &column) in quotient_columns.iter().enumerate() {
      bits[column] = (quotient >> bit) & 1 == 1;
    }
  }
}

pub(crate) fn goldilocks_mul(left: u64, right: u64) -> u64 {
  ((left as u128 * right as u128) % GOLDILOCKS_MODULUS as u128) as u64
}

#[cfg(test)]
mod tests {
  use std::panic::{AssertUnwindSafe, catch_unwind};

  use flock_prover::circuit::builder::ShapeBuilder;
  use multi_stark::{
    p3_field::{PrimeCharacteristicRing, PrimeField64},
    p3_goldilocks::Goldilocks,
  };

  use super::*;

  #[test]
  fn modular_mul_matches_reference_goldilocks() {
    let boundary = [
      0,
      1,
      2,
      (1u64 << 32) - 1,
      1u64 << 32,
      GOLDILOCKS_MODULUS - 2,
      GOLDILOCKS_MODULUS - 1,
    ];
    for &left in &boundary {
      for &right in &boundary {
        let expected = (Goldilocks::from_u64(left)
          * Goldilocks::from_u64(right))
        .as_canonical_u64();
        assert_eq!(goldilocks_mul(left, right), expected);
      }
    }

    let mut state = 0xbb67_ae85_84ca_a73bu64;
    for _ in 0..256 {
      state = state
        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
        .wrapping_add(0x94d0_49bb_1331_11eb);
      let left = state % GOLDILOCKS_MODULUS;
      state ^= state.rotate_left(23);
      let right = state % GOLDILOCKS_MODULUS;
      let expected = (Goldilocks::from_u64(left) * Goldilocks::from_u64(right))
        .as_canonical_u64();
      assert_eq!(goldilocks_mul(left, right), expected);
    }
  }

  #[test]
  fn modular_mul_r1cs_rejects_wrong_result_and_quotient() {
    let plan = build_goldilocks_mul_plan();
    eprintln!(
      "Goldilocks multiplication table uses {} Boolean columns",
      plan.boolean.useful_bits()
    );
    let r1cs = plan.boolean.block_r1cs(3);
    let cases = [
      GoldilocksMulPairRow {
        left: F128::new(0, GOLDILOCKS_MODULUS - 1),
        right: F128::new(GOLDILOCKS_MODULUS - 1, GOLDILOCKS_MODULUS - 1),
      },
      GoldilocksMulPairRow {
        left: F128::new(1 << 32, 0x1234_5678_9abc_def0),
        right: F128::new(GOLDILOCKS_MODULUS - 2, 0xfedc_ba98_7654_3210),
      },
    ];
    for row in cases {
      let mut logical = vec![false; plan.boolean.k()];
      plan.boolean.fill_row(&mut logical, |bits| {
        fill_goldilocks_mul_row(&plan, row, bits)
      });
      let mut witness = vec![false; r1cs.n()];
      witness[..plan.boolean.k()].copy_from_slice(&logical);
      assert!(r1cs.satisfies(&witness));

      let mut wrong_result = witness.clone();
      wrong_result[RESULT_BASE + 17] ^= true;
      assert!(!r1cs.satisfies(&wrong_result));

      let mut wrong_quotient = witness;
      wrong_quotient[plan.quotient_bits[0][31]] ^= true;
      assert!(!r1cs.satisfies(&wrong_quotient));
    }
  }

  #[test]
  fn multiplication_gate_pins_equation_residuals() {
    let nu = 3;
    let mut builder = ShapeBuilder::new(nu);
    let slot = builder.slot(GoldilocksMulPairGate { nu });
    let left = builder.input();
    let right = builder.input();
    let zero = builder.fixed_public_input(F128::ZERO);
    let outputs = builder.gate(slot, &[left, right]);
    builder.connect(outputs[1], zero);
    builder.connect(outputs[2], zero);
    builder.connect(outputs[3], zero);
    let shape = builder.finish().unwrap();
    shape.run(
      &[
        F128::new(3, GOLDILOCKS_MODULUS - 1),
        F128::new(7, GOLDILOCKS_MODULUS - 1),
        F128::ZERO,
      ],
      &[],
    );

    let invalid = catch_unwind(AssertUnwindSafe(|| {
      shape.run(
        &[F128::new(GOLDILOCKS_MODULUS, 1), F128::new(1, 1), F128::ZERO],
        &[],
      )
    }));
    // The multiplication identity itself accepts any u64 representation;
    // canonicality is deliberately a shared, separately wired gate.
    assert!(invalid.is_ok());
  }

  #[test]
  fn modular_mul_batch_witness_zeroes_dummy_rows() {
    let rows =
      [GoldilocksMulPairRow { left: F128::new(3, 5), right: F128::new(7, 11) }];
    let plan = build_goldilocks_mul_plan();
    let (z, a, b, stripe) = generate_goldilocks_mul_witness(&rows, 3);
    let chunks = plan.boolean.k() / 128;
    assert_eq!(z.len(), chunks * 8);
    assert_eq!(a.len(), z.len());
    assert_eq!(b.len(), z.len());
    assert_eq!(stripe.len(), plan.boolean.k());
    for chunk in 0..chunks {
      for outer in rows.len()..8 {
        assert_eq!(z[(chunk << 3) + outer], F128::ZERO);
        assert_eq!(a[(chunk << 3) + outer], F128::ZERO);
        assert_eq!(b[(chunk << 3) + outer], F128::ZERO);
      }
    }
  }
}
