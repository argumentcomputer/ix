//! Reusable constrained Karatsuba operand decomposition. Every stored bit
//! expression and packed Fr wire is derived from the original constrained
//! operand, never supplied as advice. Reuse is meaningful only in the SAME
//! builder and for that exact operand's wires, like all F128 wire APIs.

use super::*;
use std::collections::VecDeque;

/// Hard per-builder bound for the optional operand-preparation cache.
pub const F128_PREPARATION_CACHE_MAX_CAPACITY: usize = 1024;

/// The queue alone determines eviction; randomized map iteration is never
/// used to choose circuit topology. Keys are exact bit WIRES, not values.
pub(crate) struct F128PreparationCache {
  capacity: usize,
  order: VecDeque<[Variable; F128_BITS]>,
  operands: HashMap<[Variable; F128_BITS], Arc<F128PreparedOperandV0>>,
}

impl F128PreparationCache {
  pub(crate) fn new(capacity: usize) -> Self {
    Self { capacity, order: VecDeque::new(), operands: HashMap::new() }
  }

  pub(crate) fn capacity(&self) -> usize {
    self.capacity
  }

  fn get(
    &self,
    source: &F128VariablesV1,
  ) -> Option<Arc<F128PreparedOperandV0>> {
    self.operands.get(source.bit_variables()).cloned()
  }

  fn insert(&mut self, prepared: Arc<F128PreparedOperandV0>) {
    let key = *prepared.source.bit_variables();
    // Existing entries retain FIFO order. This is deliberately not an LRU.
    if self.operands.contains_key(&key) {
      return;
    }
    if self.order.len() == self.capacity {
      let evicted = self.order.pop_front().expect("nonempty bounded cache");
      self.operands.remove(&evicted);
    }
    self.order.push_back(key);
    self.operands.insert(key, prepared);
  }
}

pub(super) fn cached_prepare_f128_operand(
  builder: &mut R1csBuilder,
  source: &F128VariablesV1,
  phase: ConstraintPhase,
) -> Result<Arc<F128PreparedOperandV0>, R1csError> {
  builder.check_status()?;
  if let Some(prepared) =
    builder.f128_preparation_cache().and_then(|cache| cache.get(source))
  {
    return Ok(prepared);
  }
  let prepared = Arc::new(prepare_f128_operand(builder, source, phase)?);
  builder
    .f128_preparation_cache()
    .ok_or(R1csError::InternalShape)?
    .insert(prepared.clone());
  Ok(prepared)
}

#[derive(Clone, Debug)]
struct PreparedLeaf {
  bits: Vec<BitWire>,
  packed: Variable,
}

/// Immutable circuit-local preparation for repeated multiplications. A
/// private operand whose value happens to be zero is still prepared normally.
#[derive(Clone, Debug)]
pub struct F128PreparedOperandV0 {
  source: F128VariablesV1,
  leaves: Vec<PreparedLeaf>,
}

impl F128PreparedOperandV0 {
  pub fn source(&self) -> &F128VariablesV1 {
    &self.source
  }
}

/// Constrain the operand's shared XOR decomposition and 27 radix-32 packs.
/// Preparing a single-use operand adds R1CS equations but should not add
/// ordinary dense-operand PLONK rows: it replaces lowering's affine packs.
/// Saving from reuse must be measured; this is not a whole-verifier upgrade.
pub fn prepare_f128_operand(
  builder: &mut R1csBuilder,
  source: &F128VariablesV1,
  phase: ConstraintPhase,
) -> Result<F128PreparedOperandV0, R1csError> {
  builder.check_status()?;
  let mut leaves = Vec::new();
  if !source.constant {
    prepare(builder, &import_variables(source), &mut leaves, phase)?;
    if leaves.len() != 27 {
      return Err(R1csError::InternalShape);
    }
  }
  builder.check_status()?;
  Ok(F128PreparedOperandV0 { source: source.clone(), leaves })
}

fn prepare(
  builder: &mut R1csBuilder,
  bits: &[BitWire],
  leaves: &mut Vec<PreparedLeaf>,
  phase: ConstraintPhase,
) -> Result<(), R1csError> {
  if bits.len() == PACKED_PRODUCT_BITS {
    let value = bits.iter().enumerate().fold(0u128, |value, (index, bit)| {
      value | (u128::from(bit.value) << (PACKED_COEFFICIENT_BITS * index))
    });
    let packed = builder.alloc_private(Fr::from(value))?;
    builder.enforce_zero(
      phase,
      LinearCombination::from_variable(packed)
        .minus(&pack_polynomial_bits(bits)),
    );
    leaves.push(PreparedLeaf { bits: bits.to_vec(), packed });
    return builder.check_status();
  }
  if bits.len() <= PACKED_PRODUCT_BITS || !bits.len().is_power_of_two() {
    return Err(R1csError::InternalShape);
  }
  let half = bits.len() / 2;
  let sum = (0..half)
    .map(|i| xor2(builder, &bits[i], &bits[i + half], phase))
    .collect::<Result<Vec<_>, _>>()?;
  prepare(builder, &bits[..half], leaves, phase)?;
  prepare(builder, &bits[half..], leaves, phase)?;
  prepare(builder, &sum, leaves, phase)
}

/// Multiply two operands using only their previously constrained packs and
/// the unchanged bounded integer-convolution, reconstruction and field
/// reduction constraints. Constant/square shortcuts retain their exact rules.
pub fn constrain_f128_multiply_prepared(
  builder: &mut R1csBuilder,
  left: &F128PreparedOperandV0,
  right: &F128PreparedOperandV0,
  phase: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  builder.check_status()?;
  if left.source.constant
    || right.source.constant
    || left.source.bit_variables == right.source.bit_variables
  {
    return constrain_f128_multiply(
      builder,
      &left.source,
      &right.source,
      phase,
    );
  }
  if left.leaves.len() != 27 || right.leaves.len() != 27 {
    return Err(R1csError::InternalShape);
  }
  let mut cursor = 0;
  let product = multiply(builder, left, right, F128_BITS, &mut cursor, phase)?;
  if cursor != 27 {
    return Err(R1csError::InternalShape);
  }
  let output = export_product(
    builder,
    left.source.value,
    right.source.value,
    product,
    phase,
  )?;
  builder.check_status()?;
  Ok(output)
}

fn multiply(
  builder: &mut R1csBuilder,
  left: &F128PreparedOperandV0,
  right: &F128PreparedOperandV0,
  width: usize,
  cursor: &mut usize,
  phase: ConstraintPhase,
) -> Result<Vec<BitWire>, R1csError> {
  if width == PACKED_PRODUCT_BITS {
    let a = &left.leaves[*cursor];
    let b = &right.leaves[*cursor];
    *cursor += 1;
    return packed_polynomial_product_with_prepared(
      builder,
      &a.bits,
      &b.bits,
      Some(a.packed),
      Some(b.packed),
      phase,
    );
  }
  let half = width / 2;
  let low = multiply(builder, left, right, half, cursor, phase)?;
  let high = multiply(builder, left, right, half, cursor, phase)?;
  let sum = multiply(builder, left, right, half, cursor, phase)?;
  let mut output = vec![BitWire::constant(false); 2 * width - 1];
  output[..low.len()].clone_from_slice(&low);
  output[width..].clone_from_slice(&high);
  for i in 0..sum.len() {
    let middle = xor2(builder, &sum[i], &low[i], phase)?;
    let middle = xor2(builder, &middle, &high[i], phase)?;
    output[i + half] = xor2(builder, &output[i + half], &middle, phase)?;
  }
  Ok(output)
}

#[cfg(test)]
#[path = "f128_prepared_tests.rs"]
mod tests;
