use crate::{
  CanonicalR1csV1, ConstraintPhase, LinearCombination, R1csBuilder, R1csError,
  Variable, Witness,
};
use ark_bls12_381::Fr;
use ark_ff::{AdditiveGroup, Field};
use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex, OnceLock};

pub const F128_BITS: usize = 128;

/// Canonical little-endian bit wires for one Flock `GF(2^128)` element.
///
/// The basis is the polynomial basis used by GHASH: bit `i` is the
/// coefficient of `x^i`, reduced modulo `x^128 + x^7 + x^2 + x + 1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128VariablesV1 {
  value: [u8; 16],
  bit_variables: [Variable; F128_BITS],
}

impl F128VariablesV1 {
  pub const fn value(&self) -> &[u8; 16] {
    &self.value
  }

  pub const fn bit_variables(&self) -> &[Variable; F128_BITS] {
    &self.bit_variables
  }

  pub(crate) const fn from_constrained_bits(
    value: [u8; 16],
    bit_variables: [Variable; F128_BITS],
  ) -> Self {
    Self { value, bit_variables }
  }
}

/// Build a standalone multiplication relation in the exact Flock field.
pub fn build_f128_multiplication_r1cs(
  left: [u8; 16],
  right: [u8; 16],
  phase: ConstraintPhase,
) -> Result<(CanonicalR1csV1, Witness, F128VariablesV1), R1csError> {
  let mut builder = R1csBuilder::new();
  let left = alloc_f128_private(&mut builder, left, phase)?;
  let right = alloc_f128_private(&mut builder, right, phase)?;
  let output = constrain_f128_multiply(&mut builder, &left, &right, phase)?;
  let (r1cs, witness) = builder.finish()?;
  Ok((r1cs, witness, output))
}

/// Allocate a bit-decomposed private `GF(2^128)` value.
pub fn alloc_f128_private(
  builder: &mut R1csBuilder,
  value: [u8; 16],
  phase: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let bits = value_bits(&value)
    .into_iter()
    .map(|value| alloc_checked_bit(builder, value, phase))
    .collect::<Result<Vec<_>, _>>()?;
  export_variables(builder, value, bits, phase)
}

pub(crate) fn alloc_f128_constant(
  builder: &mut R1csBuilder,
  value: [u8; 16],
  phase: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let variables = alloc_f128_private(builder, value, phase)?;
  enforce_f128_equal_constant(builder, &variables, value, phase);
  Ok(variables)
}

/// Reinterpret a 128-by-128 bit matrix by swapping its axes.
///
/// This is wiring, not advice: output bit `i` of element `b` is literally
/// input element `i`'s bit `b`, matching Flock's TensorAlgebra transpose.
pub(crate) fn transpose_f128_variables(
  values: &[F128VariablesV1],
) -> Result<Vec<F128VariablesV1>, R1csError> {
  if values.len() != F128_BITS {
    return Err(R1csError::InternalShape);
  }
  (0..F128_BITS)
    .map(|source_bit| {
      let mut value = [0u8; 16];
      for (output_bit, input) in values.iter().enumerate() {
        if value_bits(input.value())[source_bit] {
          value[output_bit / 8] |= 1 << (output_bit % 8);
        }
      }
      let bit_variables = core::array::from_fn(|output_bit| {
        values[output_bit].bit_variables()[source_bit]
      });
      Ok(F128VariablesV1::from_constrained_bits(value, bit_variables))
    })
    .collect()
}

/// Constrain characteristic-two addition (bitwise XOR).
pub fn constrain_f128_add(
  builder: &mut R1csBuilder,
  left: &F128VariablesV1,
  right: &F128VariablesV1,
  phase: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let left_bits = import_variables(left);
  let right_bits = import_variables(right);
  let bits = left_bits
    .iter()
    .zip(&right_bits)
    .map(|(left, right)| xor2(builder, left, right, phase))
    .collect::<Result<Vec<_>, _>>()?;
  export_variables(builder, xor_values(left.value, right.value), bits, phase)
}

/// Constrain multiplication modulo `x^128 + x^7 + x^2 + x + 1`.
///
/// Karatsuba reduces the product to 27 sixteen-bit polynomial products.
/// Each leaf packs coefficients in radix 32 for one native Fr multiplication,
/// with Boolean coefficient decompositions recovering the characteristic-two
/// result. Reconstruction retains shared XOR wires instead of flattening the
/// tensor into large, overlapping parity sums.
pub fn constrain_f128_multiply(
  builder: &mut R1csBuilder,
  left: &F128VariablesV1,
  right: &F128VariablesV1,
  phase: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let left_bits = import_variables(left);
  let right_bits = import_variables(right);
  let mut coefficients =
    karatsuba_product(builder, &left_bits, &right_bits, phase)?;
  // Descending polynomial reduction: x^128 = x^7 + x^2 + x + 1.
  for degree in (F128_BITS..coefficients.len()).rev() {
    let high = coefficients[degree].clone();
    for shift in [0usize, 1, 2, 7] {
      let target = degree - F128_BITS + shift;
      coefficients[target] =
        xor2(builder, &coefficients[target], &high, phase)?;
    }
  }
  coefficients.truncate(F128_BITS);
  let value = multiply_values(left.value, right.value);
  debug_assert_eq!(wire_values(&coefficients), value_bits(&value));
  export_variables(builder, value, coefficients, phase)
}

/// Constrain multiplication by a shape-time constant as one binary-linear
/// map, avoiding the bilinear Karatsuba tensor used for two witness values.
pub fn constrain_f128_multiply_constant(
  builder: &mut R1csBuilder,
  value: &F128VariablesV1,
  constant: [u8; 16],
  phase: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  if constant == [0; 16] {
    return alloc_f128_constant(builder, [0; 16], phase);
  }
  if constant == one_value() {
    return Ok(value.clone());
  }
  let plan = constant_multiplication_plan(constant);
  constrain_binary_linear_map(builder, value, &plan, phase)
}

/// Constrain the Frobenius map `x -> x^(2^power)` in `GF(2^128)`.
///
/// Frobenius is binary-linear, so every power is a fixed XOR network over
/// the already canonical input bits. Powers are reduced modulo 128.
pub fn constrain_f128_frobenius(
  builder: &mut R1csBuilder,
  value: &F128VariablesV1,
  power: usize,
  phase: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let power = power % F128_BITS;
  if power == 0 {
    return Ok(value.clone());
  }
  constrain_binary_linear_map(builder, value, &frobenius_plans()[power], phase)
}

/// Witness and constrain a nonzero multiplicative inverse.
pub fn constrain_f128_inverse(
  builder: &mut R1csBuilder,
  value: &F128VariablesV1,
  phase: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let inverse_value = inverse_value(value.value)
    .ok_or(R1csError::NonInvertibleBinaryFieldElement)?;
  let inverse = alloc_f128_private(builder, inverse_value, phase)?;
  let product = constrain_f128_multiply(builder, value, &inverse, phase)?;
  enforce_f128_equal_constant(builder, &product, one_value(), phase);
  Ok(inverse)
}

/// Enforce equality using the injective 128-bit integer packing into Fr.
pub fn enforce_f128_equal(
  builder: &mut R1csBuilder,
  left: &F128VariablesV1,
  right: &F128VariablesV1,
  phase: ConstraintPhase,
) {
  builder.enforce_zero(
    phase,
    packed_f128_variables(left).minus(&packed_f128_variables(right)),
  );
}

pub(crate) fn enforce_f128_equal_constant(
  builder: &mut R1csBuilder,
  value: &F128VariablesV1,
  expected: [u8; 16],
  phase: ConstraintPhase,
) {
  let packed = u128::from_le_bytes(expected);
  let low = u64::try_from(packed & u128::from(u64::MAX))
    .expect("masked value fits u64");
  let high = u64::try_from(packed >> 64).expect("upper half fits u64");
  let expected =
    Fr::from(low) + Fr::from(high) * Fr::from(u128::from(1u64) << 64);
  builder.enforce_zero(
    phase,
    packed_f128_variables(value)
      .minus(&LinearCombination::from_constant(expected)),
  );
}

pub(crate) fn packed_f128_variables(
  value: &F128VariablesV1,
) -> LinearCombination {
  let mut coefficient = Fr::ONE;
  let terms = value.bit_variables.iter().copied().map(|variable| {
    let term = (variable, coefficient);
    coefficient.double_in_place();
    term
  });
  LinearCombination::from_terms(terms)
}

#[derive(Clone, Debug)]
struct BitWire {
  value: bool,
  expression: LinearCombination,
  variable: Option<Variable>,
  constant: bool,
}

impl BitWire {
  fn constant(value: bool) -> Self {
    Self {
      value,
      expression: LinearCombination::from_constant(Fr::from(u64::from(value))),
      variable: None,
      constant: true,
    }
  }

  fn not(&self) -> Self {
    Self {
      value: !self.value,
      expression: LinearCombination::one().minus(&self.expression),
      variable: None,
      constant: self.constant,
    }
  }
}

fn alloc_checked_bit(
  builder: &mut R1csBuilder,
  value: bool,
  phase: ConstraintPhase,
) -> Result<BitWire, R1csError> {
  let variable = builder.alloc_private(Fr::from(u64::from(value)))?;
  builder.enforce_boolean(phase, variable);
  Ok(BitWire {
    value,
    expression: LinearCombination::from_variable(variable),
    variable: Some(variable),
    constant: false,
  })
}

fn alloc_derived_bit(
  builder: &mut R1csBuilder,
  value: bool,
) -> Result<BitWire, R1csError> {
  let variable = builder.alloc_private(Fr::from(u64::from(value)))?;
  Ok(BitWire {
    value,
    expression: LinearCombination::from_variable(variable),
    variable: Some(variable),
    constant: false,
  })
}

fn materialize_bit(
  builder: &mut R1csBuilder,
  bit: &BitWire,
  phase: ConstraintPhase,
) -> Result<BitWire, R1csError> {
  if bit.variable.is_some() {
    return Ok(bit.clone());
  }
  let output = alloc_derived_bit(builder, bit.value)?;
  builder.enforce_zero(phase, output.expression.clone().minus(&bit.expression));
  Ok(output)
}

fn xor2(
  builder: &mut R1csBuilder,
  left: &BitWire,
  right: &BitWire,
  phase: ConstraintPhase,
) -> Result<BitWire, R1csError> {
  if left.constant {
    return Ok(if left.value { right.not() } else { right.clone() });
  }
  if right.constant {
    return Ok(if right.value { left.not() } else { left.clone() });
  }
  let output = alloc_derived_bit(builder, left.value ^ right.value)?;
  let inverse_two = Fr::from(2u64).inverse().expect("two is invertible in Fr");
  builder.enforce(
    phase,
    left.expression.clone(),
    right.expression.clone(),
    left
      .expression
      .clone()
      .plus(&right.expression)
      .minus(&output.expression)
      .scale(inverse_two),
  );
  Ok(output)
}

fn xor_many(
  builder: &mut R1csBuilder,
  inputs: &[BitWire],
  phase: ConstraintPhase,
) -> Result<BitWire, R1csError> {
  inputs.iter().try_fold(BitWire::constant(false), |left, right| {
    xor2(builder, &left, right, phase)
  })
}

const PACKED_PRODUCT_BITS: usize = 16;
const PACKED_COEFFICIENT_BITS: usize = 5;

fn karatsuba_product(
  builder: &mut R1csBuilder,
  left: &[BitWire],
  right: &[BitWire],
  phase: ConstraintPhase,
) -> Result<Vec<BitWire>, R1csError> {
  if left.len() != right.len() || !left.len().is_power_of_two() {
    return Err(R1csError::InternalShape);
  }
  if left.len() <= PACKED_PRODUCT_BITS {
    return packed_polynomial_product(builder, left, right, phase);
  }
  let half = left.len() / 2;
  let left_sum = (0..half)
    .map(|i| xor2(builder, &left[i], &left[i + half], phase))
    .collect::<Result<Vec<_>, _>>()?;
  let right_sum = (0..half)
    .map(|i| xor2(builder, &right[i], &right[i + half], phase))
    .collect::<Result<Vec<_>, _>>()?;
  let low = karatsuba_product(builder, &left[..half], &right[..half], phase)?;
  let high = karatsuba_product(builder, &left[half..], &right[half..], phase)?;
  let sum = karatsuba_product(builder, &left_sum, &right_sum, phase)?;
  let mut output = vec![BitWire::constant(false); 2 * left.len() - 1];
  output[..low.len()].clone_from_slice(&low);
  output[left.len()..].clone_from_slice(&high);
  for i in 0..sum.len() {
    let middle = xor2(builder, &sum[i], &low[i], phase)?;
    let middle = xor2(builder, &middle, &high[i], phase)?;
    output[i + half] = xor2(builder, &output[i + half], &middle, phase)?;
  }
  Ok(output)
}

/// Integer convolution in radix 32. At most 16 Boolean products contribute
/// to any coefficient, so no digit carries into the next coefficient.
/// Both packed operands are below 2^80, and both sides of the equality are
/// below 2^160 < Fr::MODULUS. Boolean digit decompositions therefore make
/// the native Fr equality an exact integer equality, without modular aliases.
fn packed_polynomial_product(
  builder: &mut R1csBuilder,
  left: &[BitWire],
  right: &[BitWire],
  phase: ConstraintPhase,
) -> Result<Vec<BitWire>, R1csError> {
  if left.is_empty()
    || left.len() != right.len()
    || left.len() > PACKED_PRODUCT_BITS
  {
    return Err(R1csError::InternalShape);
  }
  let pack =
    |bits: &[BitWire]| {
      LinearCombination::from_terms(bits.iter().enumerate().flat_map(
        |(index, bit)| {
          let place = Fr::from(1u128 << (PACKED_COEFFICIENT_BITS * index));
          bit.expression.terms().iter().map(move |&(variable, coefficient)| {
            (variable, coefficient * place)
          })
        },
      ))
    };
  let mut terms = Vec::new();
  let mut output = Vec::with_capacity(2 * left.len() - 1);
  let mut place = Fr::ONE;
  for degree in 0..2 * left.len() - 1 {
    let start = degree.saturating_sub(left.len() - 1);
    let end = degree.min(left.len() - 1);
    let coefficient = (start..=end)
      .filter(|&i| left[i].value && right[degree - i].value)
      .count();
    let maximum = end - start + 1;
    let width = usize::BITS - maximum.leading_zeros();
    let mut bit_place = place;
    for index in 0..width {
      let bit =
        alloc_checked_bit(builder, (coefficient >> index) & 1 == 1, phase)?;
      terms.extend(
        bit
          .expression
          .terms()
          .iter()
          .map(|&(variable, value)| (variable, value * bit_place)),
      );
      if index == 0 {
        output.push(bit);
      }
      bit_place.double_in_place();
    }
    place *= Fr::from(1u64 << PACKED_COEFFICIENT_BITS);
  }
  builder.enforce(
    phase,
    pack(left),
    pack(right),
    LinearCombination::from_terms(terms),
  );
  Ok(output)
}

#[derive(Clone)]
struct BinaryLinearMapPlan {
  basis_images: Vec<[u8; 16]>,
  output_inputs: Vec<Vec<usize>>,
  network: OnceLock<BinaryXorNetwork>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BinaryXorNetwork {
  pairs: Vec<(usize, usize)>,
  outputs: Vec<Vec<usize>>,
}

impl BinaryLinearMapPlan {
  fn network(&self) -> &BinaryXorNetwork {
    self.network.get_or_init(|| shared_xor_network(&self.output_inputs))
  }
}

/// Factor the most frequent shared pair until every remaining pair is used
/// once. Each substitution saves at least one XOR. Explicit lexicographic
/// tie-breaking makes the network independent of HashMap iteration order.
fn shared_xor_network(output_inputs: &[Vec<usize>]) -> BinaryXorNetwork {
  let mut outputs = output_inputs.to_vec();
  let mut counts = HashMap::<(usize, usize), usize>::new();
  for terms in &outputs {
    for (index, &left) in terms.iter().enumerate() {
      for &right in &terms[index + 1..] {
        *counts.entry((left, right)).or_default() += 1;
      }
    }
  }
  let mut pairs = Vec::new();
  while let Some((&(left, right), _)) = counts
    .iter()
    .filter(|(_, count)| **count >= 2)
    .max_by(|(left_pair, left_count), (right_pair, right_count)| {
      left_count.cmp(right_count).then_with(|| right_pair.cmp(left_pair))
    })
  {
    let output = F128_BITS + pairs.len();
    pairs.push((left, right));
    for terms in &mut outputs {
      if terms.binary_search(&left).is_err()
        || terms.binary_search(&right).is_err()
      {
        continue;
      }
      for &term in terms.iter() {
        if term == left || term == right {
          continue;
        }
        for removed in [left, right] {
          decrement_pair(&mut counts, (removed.min(term), removed.max(term)));
        }
        *counts.entry((term, output)).or_default() += 1;
      }
      decrement_pair(&mut counts, (left, right));
      terms.retain(|&term| term != left && term != right);
      terms.push(output);
    }
  }
  BinaryXorNetwork { pairs, outputs }
}

fn decrement_pair(
  counts: &mut HashMap<(usize, usize), usize>,
  pair: (usize, usize),
) {
  let count = counts.get_mut(&pair).expect("pair occurs in the current row");
  *count -= 1;
  if *count == 0 {
    counts.remove(&pair);
  }
}

fn constrain_binary_linear_map(
  builder: &mut R1csBuilder,
  value: &F128VariablesV1,
  plan: &BinaryLinearMapPlan,
  phase: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  if plan.basis_images.len() != F128_BITS
    || plan.output_inputs.len() != F128_BITS
  {
    return Err(R1csError::InternalShape);
  }
  let mut signals = import_variables(value).to_vec();
  let network = plan.network();
  for &(left, right) in &network.pairs {
    signals.push(xor2(builder, &signals[left], &signals[right], phase)?);
  }
  let output_bits = network
    .outputs
    .iter()
    .map(|sources| {
      let terms = sources
        .iter()
        .map(|&source| {
          signals.get(source).cloned().ok_or(R1csError::InternalShape)
        })
        .collect::<Result<Vec<_>, _>>()?;
      xor_many(builder, &terms, phase)
    })
    .collect::<Result<Vec<_>, _>>()?;
  let input_value_bits = value_bits(value.value());
  let expected = input_value_bits
    .iter()
    .zip(&plan.basis_images)
    .filter(|(bit, _)| **bit)
    .fold([0u8; 16], |accumulator, (_, image)| xor_values(accumulator, *image));
  debug_assert_eq!(wire_values(&output_bits), value_bits(&expected));
  export_variables(builder, expected, output_bits, phase)
}

fn plan_from_basis_images(basis_images: Vec<[u8; 16]>) -> BinaryLinearMapPlan {
  debug_assert_eq!(basis_images.len(), F128_BITS);
  let image_bits = basis_images.iter().map(value_bits).collect::<Vec<_>>();
  let output_inputs = (0..F128_BITS)
    .map(|output_bit| {
      image_bits
        .iter()
        .enumerate()
        .filter_map(|(input_bit, bits)| bits[output_bit].then_some(input_bit))
        .collect()
    })
    .collect();
  BinaryLinearMapPlan { basis_images, output_inputs, network: OnceLock::new() }
}

fn constant_multiplication_plan(
  constant: [u8; 16],
) -> Arc<BinaryLinearMapPlan> {
  static PLANS: OnceLock<Mutex<BTreeMap<[u8; 16], Arc<BinaryLinearMapPlan>>>> =
    OnceLock::new();
  let plans = PLANS.get_or_init(|| Mutex::new(BTreeMap::new()));
  if let Some(plan) =
    plans.lock().expect("linear-map cache lock").get(&constant)
  {
    return Arc::clone(plan);
  }
  let basis_images = (0..F128_BITS)
    .map(|bit| multiply_values(bit_basis_value(bit), constant))
    .collect();
  let plan = Arc::new(plan_from_basis_images(basis_images));
  Arc::clone(
    plans
      .lock()
      .expect("linear-map cache lock")
      .entry(constant)
      .or_insert(plan),
  )
}

fn frobenius_plans() -> &'static [BinaryLinearMapPlan] {
  static PLANS: OnceLock<Vec<BinaryLinearMapPlan>> = OnceLock::new();
  PLANS.get_or_init(|| {
    let mut images = (0..F128_BITS).map(bit_basis_value).collect::<Vec<_>>();
    let mut plans = Vec::with_capacity(F128_BITS);
    for _ in 0..F128_BITS {
      plans.push(plan_from_basis_images(images.clone()));
      for image in &mut images {
        *image = multiply_values(*image, *image);
      }
    }
    plans
  })
}

fn bit_basis_value(bit: usize) -> [u8; 16] {
  let mut value = [0u8; 16];
  value[bit / 8] = 1 << (bit % 8);
  value
}

fn import_variables(value: &F128VariablesV1) -> [BitWire; F128_BITS] {
  let bits = value_bits(&value.value);
  core::array::from_fn(|index| BitWire {
    value: bits[index],
    expression: LinearCombination::from_variable(value.bit_variables[index]),
    variable: Some(value.bit_variables[index]),
    constant: false,
  })
}

fn export_variables(
  builder: &mut R1csBuilder,
  value: [u8; 16],
  bits: Vec<BitWire>,
  phase: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let bits: [BitWire; F128_BITS] =
    bits.try_into().map_err(|_| R1csError::InternalShape)?;
  let bit_variables = bits
    .iter()
    .map(|bit| materialize_bit(builder, bit, phase))
    .collect::<Result<Vec<_>, _>>()?
    .into_iter()
    .map(|bit| bit.variable.ok_or(R1csError::InternalShape))
    .collect::<Result<Vec<_>, _>>()?
    .try_into()
    .map_err(|_| R1csError::InternalShape)?;
  Ok(F128VariablesV1::from_constrained_bits(value, bit_variables))
}

fn value_bits(value: &[u8; 16]) -> [bool; F128_BITS] {
  core::array::from_fn(|bit| (value[bit / 8] >> (bit % 8)) & 1 == 1)
}

fn wire_values(bits: &[BitWire]) -> [bool; F128_BITS] {
  core::array::from_fn(|index| bits[index].value)
}

fn xor_values(left: [u8; 16], right: [u8; 16]) -> [u8; 16] {
  core::array::from_fn(|index| left[index] ^ right[index])
}

pub(crate) fn native_f128_add(left: [u8; 16], right: [u8; 16]) -> [u8; 16] {
  xor_values(left, right)
}

fn one_value() -> [u8; 16] {
  let mut one = [0u8; 16];
  one[0] = 1;
  one
}

fn multiply_values(left: [u8; 16], right: [u8; 16]) -> [u8; 16] {
  let left = u128::from_le_bytes(left);
  let right = u128::from_le_bytes(right);
  let left_low =
    u64::try_from(left & u128::from(u64::MAX)).expect("masked value fits u64");
  let left_high = u64::try_from(left >> 64).expect("upper half fits u64");
  let right_low =
    u64::try_from(right & u128::from(u64::MAX)).expect("masked value fits u64");
  let right_high = u64::try_from(right >> 64).expect("upper half fits u64");
  let p00 = carryless_mul64(left_low, right_low);
  let p01 = carryless_mul64(left_low, right_high);
  let p10 = carryless_mul64(left_high, right_low);
  let p11 = carryless_mul64(left_high, right_high);
  let low64 = |value: u128| {
    u64::try_from(value & u128::from(u64::MAX)).expect("masked value fits u64")
  };
  let high64 =
    |value: u128| u64::try_from(value >> 64).expect("upper half fits u64");
  let r0 = low64(p00);
  let r1 = high64(p00) ^ low64(p01) ^ low64(p10);
  let r2 = high64(p01) ^ high64(p10) ^ low64(p11);
  let r3 = high64(p11);
  reduce_ghash(r0, r1, r2, r3)
}

pub(crate) fn native_f128_multiply(
  left: [u8; 16],
  right: [u8; 16],
) -> [u8; 16] {
  multiply_values(left, right)
}

fn carryless_mul64(left: u64, right: u64) -> u128 {
  let mut product = 0u128;
  for bit in 0..64 {
    if (left >> bit) & 1 == 1 {
      product ^= u128::from(right) << bit;
    }
  }
  product
}

fn reduce_ghash(r0: u64, r1: u64, r2: u64, r3: u64) -> [u8; 16] {
  let shift1_low = r2 << 1;
  let shift1_high = (r3 << 1) | (r2 >> 63);
  let shift2_low = r2 << 2;
  let shift2_high = (r3 << 2) | (r2 >> 62);
  let shift7_low = r2 << 7;
  let shift7_high = (r3 << 7) | (r2 >> 57);
  let folded_low = r2 ^ shift1_low ^ shift2_low ^ shift7_low;
  let folded_high = r3 ^ shift1_high ^ shift2_high ^ shift7_high;
  let overflow = (r3 >> 63) ^ (r3 >> 62) ^ (r3 >> 57);
  let correction =
    overflow ^ (overflow << 1) ^ (overflow << 2) ^ (overflow << 7);
  let value = u128::from(r0 ^ folded_low ^ correction)
    | (u128::from(r1 ^ folded_high) << 64);
  value.to_le_bytes()
}

fn inverse_value(value: [u8; 16]) -> Option<[u8; 16]> {
  if value == [0; 16] {
    return None;
  }
  // x^(2^128 - 2): bits 1..127 of the exponent are all one.
  let mut result = one_value();
  let mut power = value;
  for bit in 0..128 {
    if bit != 0 {
      result = multiply_values(result, power);
    }
    power = multiply_values(power, power);
  }
  Some(result)
}

pub(crate) fn native_f128_inverse(value: [u8; 16]) -> Option<[u8; 16]> {
  inverse_value(value)
}

#[cfg(test)]
mod tests {
  use super::*;

  fn value(low: u64, high: u64) -> [u8; 16] {
    (u128::from(low) | (u128::from(high) << 64)).to_le_bytes()
  }

  fn polynomial_oracle(left: [u8; 16], right: [u8; 16]) -> [u8; 16] {
    let left = value_bits(&left);
    let right = value_bits(&right);
    let mut product = [false; 255];
    for (left_index, &left_bit) in left.iter().enumerate() {
      for (right_index, &right_bit) in right.iter().enumerate() {
        product[left_index + right_index] ^= left_bit & right_bit;
      }
    }
    for degree in (128..255).rev() {
      if product[degree] {
        product[degree] = false;
        for shift in [0usize, 1, 2, 7] {
          product[degree - 128 + shift] ^= true;
        }
      }
    }
    let mut output = [0u8; 16];
    for (bit, &set) in product[..128].iter().enumerate() {
      output[bit / 8] |= u8::from(set) << (bit % 8);
    }
    output
  }

  fn witness_word(witness: &Witness, word: &F128VariablesV1) -> [u8; 16] {
    let mut value = [0u8; 16];
    for (index, variable) in word.bit_variables().iter().enumerate() {
      let bit = witness.assignment()[variable.index() as usize];
      assert!(bit == Fr::ZERO || bit == Fr::ONE);
      value[index / 8] |= u8::from(bit == Fr::ONE) << (index % 8);
    }
    value
  }

  #[test]
  fn native_multiplication_matches_polynomial_oracle() {
    let vectors = [
      (value(0, 0), value(7, 9)),
      (value(1, 0), value(u64::MAX, u64::MAX)),
      (value(2, 0), value(0, 1u64 << 63)),
      (
        value(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210),
        value(0x0f1e_2d3c_4b5a_6978, 0x8877_6655_4433_2211),
      ),
    ];
    for (left, right) in vectors {
      assert_eq!(multiply_values(left, right), polynomial_oracle(left, right));
    }
  }

  #[test]
  fn multiplication_relation_is_sound_and_value_independent() {
    let left = value(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210);
    let right = value(0x0f1e_2d3c_4b5a_6978, 0x8877_6655_4433_2211);
    let (first, mut witness, output) =
      build_f128_multiplication_r1cs(left, right, ConstraintPhase::Zerocheck)
        .unwrap();
    let census = first.census();
    assert_eq!(census.private_variables, 5_925);
    assert_eq!(census.constraints, 5_952);
    assert_eq!(census.nonzero_terms, 27_196);
    assert_eq!(*output.value(), multiply_values(left, right));
    first.check(&witness).unwrap();
    let bit = output.bit_variables()[0];
    let wrong = !value_bits(output.value())[0];
    witness.set(bit, Fr::from(u64::from(wrong))).unwrap();
    assert!(first.check(&witness).is_err());

    let (second, _, _) = build_f128_multiplication_r1cs(
      value(3, 5),
      value(7, 11),
      ConstraintPhase::Zerocheck,
    )
    .unwrap();
    assert_eq!(first.digest(), second.digest());
    assert_eq!(first.census(), second.census());
  }

  #[test]
  fn packed_multiplication_witness_bits_match_carryless_oracle() {
    let mut vectors =
      vec![(0u128, u128::MAX), (1, u128::MAX), (u128::MAX, u128::MAX)];
    for bit in [0, 15, 16, 31, 32, 63, 64, 111, 112, 127] {
      vectors.push((1u128 << bit, 1u128 << 127));
      vectors.push(((1u128 << bit).wrapping_sub(1), u128::MAX));
    }
    let mut state = 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210u128;
    for _ in 0..32 {
      state ^= state << 13;
      state ^= state >> 7;
      state ^= state << 17;
      vectors.push((state, state.rotate_left(37)));
    }
    for (left, right) in vectors {
      let left = left.to_le_bytes();
      let right = right.to_le_bytes();
      let (r1cs, witness, output) =
        build_f128_multiplication_r1cs(left, right, ConstraintPhase::Pcs)
          .unwrap();
      let expected = polynomial_oracle(left, right);
      let actual = witness_word(&witness, &output);
      assert_eq!(actual, expected, "left={left:02x?}, right={right:02x?}");
      assert_eq!(*output.value(), expected);
      r1cs.check(&witness).unwrap();
    }
  }

  #[test]
  fn shared_linear_networks_preserve_every_input_basis_vector() {
    let constant = constant_multiplication_plan([0xa5; 16]);
    for plan in [1, 7, 31, 63, 127]
      .map(|power| &frobenius_plans()[power])
      .into_iter()
      .chain([constant.as_ref()])
    {
      let network = plan.network();
      let mut masks =
        (0..F128_BITS).map(|bit| 1u128 << bit).collect::<Vec<_>>();
      for &(left, right) in &network.pairs {
        masks.push(masks[left] ^ masks[right]);
      }
      for (output_bit, sources) in network.outputs.iter().enumerate() {
        let actual =
          sources.iter().fold(0u128, |mask, &source| mask ^ masks[source]);
        let expected = plan.basis_images.iter().enumerate().fold(
          0u128,
          |mask, (input_bit, image)| {
            mask
              | (u128::from((image[output_bit / 8] >> (output_bit % 8)) & 1)
                << input_bit)
          },
        );
        assert_eq!(actual, expected);
      }
      let original_cost: usize =
        plan.output_inputs.iter().map(|row| row.len().saturating_sub(1)).sum();
      let factored_cost = network.pairs.len()
        + network
          .outputs
          .iter()
          .map(|row| row.len().saturating_sub(1))
          .sum::<usize>();
      assert!(factored_cost <= original_cost);
      assert_eq!(*network, shared_xor_network(&plan.output_inputs));
    }
  }

  #[test]
  fn addition_and_inversion_satisfy_field_identities() {
    let mut builder = R1csBuilder::new();
    let left = alloc_f128_private(
      &mut builder,
      value(0x55aa, 0x1234),
      ConstraintPhase::Lincheck,
    )
    .unwrap();
    let right = alloc_f128_private(
      &mut builder,
      value(0x0f0f, 0xabcd),
      ConstraintPhase::Lincheck,
    )
    .unwrap();
    let sum = constrain_f128_add(
      &mut builder,
      &left,
      &right,
      ConstraintPhase::Lincheck,
    )
    .unwrap();
    assert_eq!(*sum.value(), xor_values(left.value, right.value));
    let inverse =
      constrain_f128_inverse(&mut builder, &left, ConstraintPhase::Lincheck)
        .unwrap();
    assert_eq!(multiply_values(left.value, *inverse.value()), one_value());
    let (r1cs, witness) = builder.finish().unwrap();
    r1cs.check(&witness).unwrap();
  }

  #[test]
  fn zero_has_no_constrained_inverse() {
    let mut builder = R1csBuilder::new();
    let zero =
      alloc_f128_private(&mut builder, [0; 16], ConstraintPhase::Pcs).unwrap();
    assert_eq!(
      constrain_f128_inverse(&mut builder, &zero, ConstraintPhase::Pcs),
      Err(R1csError::NonInvertibleBinaryFieldElement),
    );
  }

  #[test]
  fn constant_multiplication_and_frobenius_are_linear_maps() {
    let input = value(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210);
    let constant = value(0x0f1e_2d3c_4b5a_6978, 0x8877_6655_4433_2211);
    let mut builder = R1csBuilder::new();
    let input_variables =
      alloc_f128_private(&mut builder, input, ConstraintPhase::Pcs).unwrap();
    let product = constrain_f128_multiply_constant(
      &mut builder,
      &input_variables,
      constant,
      ConstraintPhase::Pcs,
    )
    .unwrap();
    let power = constrain_f128_frobenius(
      &mut builder,
      &input_variables,
      17,
      ConstraintPhase::Pcs,
    )
    .unwrap();
    assert_eq!(*product.value(), multiply_values(input, constant));
    let expected_power =
      (0..17).fold(input, |value, _| multiply_values(value, value));
    assert_eq!(*power.value(), expected_power);
    let (r1cs, witness) = builder.finish().unwrap();
    assert_eq!(
      witness_word(&witness, &product),
      multiply_values(input, constant)
    );
    assert_eq!(witness_word(&witness, &power), expected_power);
    r1cs.check(&witness).unwrap();
  }
}
