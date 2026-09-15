use crate::{ConstraintPhase, R1csBuilder, R1csError, Variable};
use flock_prover::field::F128;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct F128VariablesV1 {
  value: [u8; 16],
  bits: [Variable; 128],
}
impl F128VariablesV1 {
  pub(crate) const fn value(&self) -> &[u8; 16] {
    &self.value
  }
  pub(crate) const fn bit_variables(&self) -> &[Variable; 128] {
    &self.bits
  }
  pub(crate) const fn from_constrained_bits(
    value: [u8; 16],
    bits: [Variable; 128],
  ) -> Self {
    Self { value, bits }
  }
  pub(crate) fn word(&self, b: &mut R1csBuilder) -> usize {
    b.pack(&self.bits)
  }
}
pub(crate) fn bytes(value: F128) -> [u8; 16] {
  let mut bytes = [0; 16];
  bytes[..8].copy_from_slice(&value.lo.to_le_bytes());
  bytes[8..].copy_from_slice(&value.hi.to_le_bytes());
  bytes
}
fn variable(b: &R1csBuilder, word: usize) -> F128VariablesV1 {
  F128VariablesV1 {
    value: bytes(b.values[word]),
    bits: R1csBuilder::bits(word),
  }
}
pub(crate) fn native_f128_add(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
  bytes(ixby_flock::hash::pack_bytes(&a) + ixby_flock::hash::pack_bytes(&b))
}
pub(crate) fn native_f128_multiply(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
  bytes(ixby_flock::hash::pack_bytes(&a) * ixby_flock::hash::pack_bytes(&b))
}
pub(crate) fn native_f128_inverse(a: [u8; 16]) -> Option<[u8; 16]> {
  let a = ixby_flock::hash::pack_bytes(&a);
  (a != F128::ZERO).then(|| bytes(a.inv()))
}
pub(crate) fn alloc_f128_private(
  b: &mut R1csBuilder,
  value: [u8; 16],
  _: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let word = b.alloc(ixby_flock::hash::pack_bytes(&value));
  Ok(variable(b, word))
}
pub(crate) fn alloc_f128_constant(
  b: &mut R1csBuilder,
  value: [u8; 16],
  _: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  // Constants expose constant bits, so bit operations never allocate advice.
  b.constant(ixby_flock::hash::pack_bytes(&value));
  Ok(F128VariablesV1 {
    value,
    bits: std::array::from_fn(|i| {
      Variable::Constant((value[i / 8] >> (i % 8)) & 1 != 0)
    }),
  })
}
pub(crate) fn constrain_f128_add(
  b: &mut R1csBuilder,
  a: &F128VariablesV1,
  c: &F128VariablesV1,
  _: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let a = a.word(b);
  let c = c.word(b);
  let word = b.add(a, c);
  Ok(variable(b, word))
}
pub(crate) fn constrain_f128_multiply(
  b: &mut R1csBuilder,
  a: &F128VariablesV1,
  c: &F128VariablesV1,
  _: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let a = a.word(b);
  let c = c.word(b);
  let word = b.multiply(a, c);
  Ok(variable(b, word))
}
pub(crate) fn constrain_f128_inverse(
  b: &mut R1csBuilder,
  a: &F128VariablesV1,
  _: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let a = a.word(b);
  let word = b.inverse(a);
  Ok(variable(b, word))
}
pub(crate) fn constrain_f128_multiply_constant(
  b: &mut R1csBuilder,
  a: &F128VariablesV1,
  c: [u8; 16],
  p: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let c = alloc_f128_constant(b, c, p)?;
  constrain_f128_multiply(b, a, &c, p)
}
pub(crate) fn constrain_f128_frobenius(
  b: &mut R1csBuilder,
  a: &F128VariablesV1,
  power: usize,
  p: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let mut value = a.clone();
  for _ in 0..power % 128 {
    value = constrain_f128_multiply(b, &value, &value, p)?;
  }
  Ok(value)
}
pub(crate) fn enforce_f128_equal(
  b: &mut R1csBuilder,
  a: &F128VariablesV1,
  c: &F128VariablesV1,
  _: ConstraintPhase,
) {
  let a = a.word(b);
  let c = c.word(b);
  b.equal(a, c);
}
pub(crate) fn enforce_f128_equal_constant(
  b: &mut R1csBuilder,
  a: &F128VariablesV1,
  c: [u8; 16],
  _: ConstraintPhase,
) {
  let a = a.word(b);
  let c = b.constant(ixby_flock::hash::pack_bytes(&c));
  b.equal(a, c);
}
pub(crate) fn transpose_f128_variables(
  values: &[F128VariablesV1],
) -> Result<Vec<F128VariablesV1>, R1csError> {
  if values.len() != 128 {
    return Err(R1csError::InternalShape);
  }
  Ok(
    (0..128)
      .map(|bit| {
        let mut value = [0; 16];
        for (i, source) in values.iter().enumerate() {
          value[i / 8] |= ((source.value[bit / 8] >> (bit % 8)) & 1) << (i % 8);
        }
        F128VariablesV1 {
          value,
          bits: std::array::from_fn(|i| values[i].bits[bit]),
        }
      })
      .collect(),
  )
}
