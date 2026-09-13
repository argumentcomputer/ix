use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
    write_f128,
  },
  goldilocks::GOLDILOCKS_MODULUS as P,
  ixby::{
    bits::{
      add, any, equal, equal_constant, fill_words, not, or, read_words,
      require, require_zero, subtract,
    },
    decode::PrimitiveSet,
    value::{BOOL_TAG, EXT_TAG, FIELD_TAG, WORD32_TAG, scalar_cell},
  },
  multiplication::goldilocks_mul,
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

#[derive(Clone, Debug)]
pub struct PrimitivePrepareGate {
  nu: usize,
  operands: usize,
  registry: PrimitiveSet,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct PrimitivePrepareRow {
  pub(super) input: Vec<F128>,
  pub(super) inverse: F128,
}

impl PrimitivePrepareGate {
  pub fn new(
    nu: usize,
    operands: usize,
    registry: PrimitiveSet,
  ) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "primitive row-domain admission");
    ensure!((1..=4).contains(&operands), "primitive operand capacity");
    Ok(Self { nu, operands, registry, plan: Arc::new(OnceLock::new()) })
  }
  pub fn operands(&self) -> usize {
    self.operands
  }
  pub(super) fn nu(&self) -> usize {
    self.nu
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build(self))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[PrimitivePrepareRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(self.plan(), rows, self.nu, dst, fill_free)
  }
}

pub(super) fn fill_free(row: &PrimitivePrepareRow, bits: &mut [bool]) {
  fill_words(&row.input, bits);
  write_f128(bits, 128 * (row.input.len() + 4), row.inverse);
}

impl CountedGate for PrimitivePrepareGate {
  fn input_count(&self) -> usize {
    2 + 2 * self.operands
  }
  /// Result tag/direct payload, arithmetic operands, inverse advice, expected
  /// inverse product, operation flags, validity residual.
  fn output_count(&self) -> usize {
    8
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for PrimitivePrepareGate {
  type Row = PrimitivePrepareRow;
  type Hint = ();
  fn table(&self) -> TableType {
    let mut schema: Vec<_> =
      (0..self.input_count()).map(IoWord::input).collect();
    schema.extend(
      (self.input_count()..self.input_count() + self.output_count())
        .map(IoWord::output),
    );
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(schema)
  }
  fn eval(&self, input: &[F128], _: &(), outputs: &mut Vec<F128>) -> Self::Row {
    assert_eq!(input.len(), self.input_count());
    let opcode = (input[1].lo >> 32) as u32;
    let inverse =
      if (input[0].lo >> 32) as u32 == 2 && matches!(opcode, 17 | 24) {
        inverse(input[3])
      } else {
        F128::ZERO
      };
    let row = PrimitivePrepareRow { input: input.to_vec(), inverse };
    let mut bits = vec![false; self.plan().k()];
    self.plan().fill_row(&mut bits, |bits| fill_free(&row, bits));
    outputs.extend(read_words(&bits, input.len(), self.output_count()));
    row
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

fn inverse(value: F128) -> F128 {
  // Total witness computation even for malformed raw cells. Canonicality,
  // types and the inverse equation are enforced separately by the relation.
  let a = value.lo % P;
  let b = value.hi % P;
  let norm = ((u128::from(goldilocks_mul(a, a)) + u128::from(P)
    - u128::from(goldilocks_mul(7, goldilocks_mul(b, b))))
    % u128::from(P)) as u64;
  let mut acc = 1;
  let mut base = norm;
  let mut exponent = P - 2;
  while exponent != 0 {
    if exponent & 1 != 0 {
      acc = goldilocks_mul(acc, base);
    }
    base = goldilocks_mul(base, base);
    exponent >>= 1;
  }
  F128::new(
    goldilocks_mul(a, acc),
    goldilocks_mul(if b == 0 { 0 } else { P - b }, acc),
  )
}

fn sum_flags(
  b: &mut BooleanR1csBuilder,
  one: usize,
  flags: &[usize],
  codes: &[usize],
) -> usize {
  b.xor(&codes.iter().map(|code| flags[*code]).collect::<Vec<_>>(), one)
}

fn choose(
  b: &mut BooleanR1csBuilder,
  one: usize,
  sources: &[(usize, &[usize])],
  width: usize,
) -> Vec<usize> {
  (0..width)
    .map(|bit| {
      let products: Vec<_> = sources
        .iter()
        .map(|(flag, source)| b.and(*flag, source[bit]))
        .collect();
      b.xor(&products, one)
    })
    .collect()
}

fn build(gate: &PrimitivePrepareGate) -> BooleanR1csPlan {
  let inputs = gate.input_count();
  let reserved = 128 * (inputs + gate.output_count());
  let mut b = BooleanR1csBuilder::new(14, reserved);
  for bit in 0..inputs * 128 {
    b.free_boolean_at(bit);
  }
  let inverse: Vec<_> = (128 * (inputs + 4)..128 * (inputs + 5)).collect();
  for bit in &inverse {
    b.free_boolean_at(*bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let active = equal_constant(&mut b, one, &(32..64).collect::<Vec<_>>(), 2);
  let code: Vec<_> = (160..192).collect();
  let count: Vec<_> = (192..224).collect();
  let mut flags = vec![zero; 29];
  for opcode in gate.registry.opcodes() {
    let matched = equal_constant(&mut b, one, &code, u64::from(opcode));
    flags[opcode as usize] = b.and(active, matched);
  }
  let mut violations = Vec::new();
  let valid = b.xor(&flags, one);
  require(&mut b, one, &mut violations, active, valid);
  let unary = sum_flags(&mut b, one, &flags, &[13, 17, 24, 27, 28]);
  let binary = b.xor(&[valid, unary], one);
  let one_arg = equal_constant(&mut b, one, &count, 1);
  let two_args = equal_constant(&mut b, one, &count, 2);
  require(&mut b, one, &mut violations, unary, one_arg);
  require(&mut b, one, &mut violations, binary, two_args);
  if gate.operands < 2 {
    violations.push(binary);
  }
  let mut args = Vec::new();
  let mut tags = Vec::new();
  for index in 0..2 {
    let enabled = if index == 0 { valid } else { binary };
    let raw: Vec<_> = if index < gate.operands {
      (128 * (2 + 2 * index)..128 * (4 + 2 * index)).collect()
    } else {
      vec![zero; 256]
    };
    let masked: Vec<_> = raw.iter().map(|bit| b.and(enabled, *bit)).collect();
    tags.push(scalar_cell(&mut b, one, &mut violations, enabled, &masked));
    args.push(masked[128..].to_vec());
    if index == 1 && index < gate.operands {
      require_zero(&mut b, one, &mut violations, unary, &raw);
    }
  }
  for index in 2..gate.operands {
    require_zero(
      &mut b,
      one,
      &mut violations,
      active,
      &(128 * (2 + 2 * index)..128 * (4 + 2 * index)).collect::<Vec<_>>(),
    );
  }
  for (codes, tag) in [
    (&[0, 3, 4, 5, 9, 10, 13][..], 1),
    (&[14, 15, 16, 17, 18, 26][..], 2),
    (&[21, 22, 23, 24, 25, 27, 28][..], 3),
  ] {
    let first = sum_flags(&mut b, one, &flags, codes);
    require(&mut b, one, &mut violations, first, tags[0][tag]);
    let second = b.and(first, binary);
    require(&mut b, one, &mut violations, second, tags[1][tag]);
  }
  let arithmetic_add = sum_flags(&mut b, one, &flags, &[14, 15, 21, 22]);
  let arithmetic_sub = sum_flags(&mut b, one, &flags, &[15, 22]);
  let arithmetic_mul = sum_flags(&mut b, one, &flags, &[16, 23]);
  let arithmetic_inv = sum_flags(&mut b, one, &flags, &[17, 24]);
  let arithmetic =
    b.xor(&[arithmetic_add, arithmetic_mul, arithmetic_inv], one);
  let lhs: Vec<_> = args[0].iter().map(|bit| b.and(arithmetic, *bit)).collect();
  let mut candidate = vec![zero; 128];
  candidate[2] = arithmetic_inv; // EXT_TAG = 4, gated to zero when inactive.
  candidate.extend_from_slice(&inverse);
  scalar_cell(&mut b, one, &mut violations, arithmetic_inv, &candidate);
  let lhs_nonzero = any(&mut b, one, &lhs);
  let expected_inverse = b.and(arithmetic_inv, lhs_nonzero);
  let inverse_zero = not(&mut b, one, expected_inverse);
  require_zero(&mut b, one, &mut violations, inverse_zero, &inverse);
  let mut negated = Vec::new();
  let modulus: Vec<_> =
    (0..64).map(|bit| if P & (1 << bit) == 0 { zero } else { one }).collect();
  for lane in args[1].as_chunks::<64>().0 {
    let nonzero = any(&mut b, one, lane);
    let difference = subtract(&mut b, one, zero, &modulus, lane).0;
    negated.extend(difference.iter().map(|bit| b.and(nonzero, *bit)));
  }
  let positive = b.xor(&[arithmetic_add, arithmetic_sub, arithmetic_mul], one);
  let rhs = choose(
    &mut b,
    one,
    &[
      (positive, &args[1]),
      (arithmetic_sub, &negated),
      (arithmetic_inv, &inverse),
    ],
    128,
  );
  let word_add = add(&mut b, one, zero, &args[0][..32], &args[1][..32]).0;
  let word_and: Vec<_> = args[0][..32]
    .iter()
    .zip(&args[1][..32])
    .map(|(a, c)| b.and(*a, *c))
    .collect();
  let word_or: Vec<_> = args[0][..32]
    .iter()
    .zip(&args[1][..32])
    .map(|(a, c)| or(&mut b, one, *a, *c))
    .collect();
  let word_xor: Vec<_> = args[0][..32]
    .iter()
    .zip(&args[1][..32])
    .map(|(a, c)| b.xor(&[*a, *c], one))
    .collect();
  let same = equal(&mut b, one, &args[0], &args[1]);
  let less = subtract(&mut b, one, zero, &args[0][..32], &args[1][..32]).1;
  let equality = sum_flags(&mut b, one, &flags, &[9, 18, 25]);
  let bool_eq = b.and(equality, same);
  let bool_lt = b.and(flags[10], less);
  let mut direct = vec![zero; 128];
  let result_word = choose(
    &mut b,
    one,
    &[
      (flags[0], &word_add),
      (flags[3], &word_and),
      (flags[4], &word_or),
      (flags[5], &word_xor),
    ],
    32,
  );
  direct[..32].copy_from_slice(&result_word);
  direct[0] = b.xor(&[direct[0], bool_eq, bool_lt], one);
  for (bit, target) in direct.iter_mut().enumerate() {
    let mut sources = vec![*target];
    if bit < 64 {
      sources.push(b.and(flags[13], args[0][bit]));
      sources.push(b.and(flags[26], args[0][bit]));
      sources.push(b.and(flags[27], args[0][bit]));
      sources.push(b.and(flags[28], args[0][64 + bit]));
    } else {
      sources.push(b.and(flags[26], args[1][bit - 64]));
    }
    *target = b.xor(&sources, one);
  }
  let mut tag = vec![zero; 128];
  for (value, codes) in [
    (WORD32_TAG, &[0, 3, 4, 5][..]),
    (BOOL_TAG, &[9, 10, 18, 25][..]),
    (FIELD_TAG, &[13, 14, 15, 16, 17, 27, 28][..]),
    (EXT_TAG, &[21, 22, 23, 24, 26][..]),
  ] {
    let flag = sum_flags(&mut b, one, &flags, codes);
    for (bit, target) in tag.iter_mut().enumerate().take(3) {
      if value & (1 << bit) != 0 {
        *target = b.xor(&[*target, flag], one);
      }
    }
  }
  for (word, bits) in [(0, &tag), (1, &direct), (2, &lhs), (3, &rhs)] {
    for (bit, source) in bits.iter().enumerate() {
      b.write_xor(128 * (inputs + word) + bit, &[*source], one);
    }
  }
  b.write_xor(128 * (inputs + 5), &[expected_inverse], one);
  for (bit, source) in
    [arithmetic_add, arithmetic_mul, arithmetic_inv].iter().enumerate()
  {
    b.write_xor(128 * (inputs + 6) + bit, &[*source], one);
  }
  let violation = any(&mut b, one, &violations);
  b.write_xor(128 * (inputs + 7), &[violation], one);
  b.finish()
}
