//! Goldilocks constraints over the selected KZG curve's scalar field.
//! Each modular relation has a bounded quotient; small integer relations lift directly.

use num_bigint::{BigInt, BigUint, Sign};
use p3_field::PrimeField64;

#[cfg(test)]
use crate::kzg::field::Scalar;
use crate::kzg::{
  curve::{Bn254, KzgCurve},
  field::CurveScalar,
};
use multi_stark::plonkish::Assignment;
use multi_stark::plonkish::Circuit;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::plonkish::CircuitId;
use multi_stark::plonkish::CircuitStats;
use multi_stark::plonkish::Gate;
use multi_stark::plonkish::LoweringError;
use multi_stark::plonkish::MultiStarkCircuit;
use multi_stark::plonkish::Table;
use multi_stark::plonkish::Value;
use multi_stark::plonkish::ValueSource as Recipe;
use multi_stark::plonkish::Witness;
use multi_stark::plonkish::WitnessError;
use multi_stark::system::CircuitInputs;
use multi_stark::traits::Algebra;
use multi_stark::traits::Field;
use multi_stark::types::Val;
use p3_matrix::Matrix;

const P: u64 = <Val as PrimeField64>::ORDER_U64;

mod interval;
mod quotient;

pub trait KzgCircuitExt<C: KzgCurve = Bn254> {
  fn kzg_circuit_inputs(
    &self,
    max_trace_len: usize,
    quotient_budget: usize,
  ) -> Result<Vec<CircuitInputs<CurveScalar<C>>>, LoweringError>;
  fn kzg_circuit_input(
    &self,
    index: usize,
    max_trace_len: usize,
    quotient_budget: usize,
  ) -> Result<Option<CircuitInputs<CurveScalar<C>>>, LoweringError>;
}
impl<C: KzgCurve> KzgCircuitExt<C> for MultiStarkCircuit<CurveScalar<C>> {
  /// Minimize KZG commitment/evaluation bytes by choosing lookup groups per
  /// trace, within the supplied trace cap and quotient budget.
  fn kzg_circuit_inputs(
    &self,
    max_trace_len: usize,
    quotient_budget: usize,
  ) -> Result<Vec<CircuitInputs<CurveScalar<C>>>, LoweringError> {
    let mut inputs = self.circuit_inputs();
    for input in &mut inputs {
      tune_kzg_input::<C>(input, max_trace_len, quotient_budget)?;
    }
    Ok(inputs)
  }

  /// Generate and tune one circuit's preprocessing, without materializing the others.
  fn kzg_circuit_input(
    &self,
    index: usize,
    max_trace_len: usize,
    quotient_budget: usize,
  ) -> Result<Option<CircuitInputs<CurveScalar<C>>>, LoweringError> {
    let Some(mut input) = self.circuit_input(index) else {
      return Ok(None);
    };
    tune_kzg_input::<C>(&mut input, max_trace_len, quotient_budget)?;
    Ok(Some(input))
  }
}

fn tune_kzg_input<C: KzgCurve>(
  input: &mut CircuitInputs<CurveScalar<C>>,
  max_trace_len: usize,
  quotient_budget: usize,
) -> Result<(), LoweringError> {
  use multi_stark::graph::ExtensionParams;
  use multi_stark::lookup::MAX_LOOKUP_GROUP;
  use multi_stark::lookup::logup_max_degree;
  use multi_stark::lookup::stage2_width;
  let fixed = input.preprocessed.as_ref().expect("lowering has fixed columns");
  if fixed.height() > max_trace_len {
    return Err(LoweringError::InvalidTraceHeight);
  }
  let graph =
    input.compile_graph(&ExtensionParams::base()).expect("valid lowering");
  let commitment_bytes = C::G1_COMPRESSED_BYTES;
  let best = (1..=MAX_LOOKUP_GROUP)
    .filter_map(|group| {
      let degree = graph
        .max_constraint_degree
        .max(logup_max_degree(&graph, group)) as usize;
      let quotient = (degree.max(2) - 1).next_power_of_two();
      if quotient > quotient_budget {
        return None;
      }
      let width = stage2_width(input.lookups.len(), group, 1);
      let bytes =
        width * (commitment_bytes + 64) + quotient * (commitment_bytes + 32);
      Some(((bytes, quotient, group), group))
    })
    .min_by_key(|(cost, _)| *cost)
    .ok_or(LoweringError::QuotientBudgetTooSmall)?;
  input.lookup_group_size = best.1;
  Ok(())
}
/// A fixed translation. Public values retain their original order and canonical encoding.
pub struct GoldilocksCircuit<C: KzgCurve = Bn254> {
  pub circuit: Circuit<CurveScalar<C>>,
  pub inputs: GoldilocksInputs,
}

/// Retain this mapping when consuming the circuit for lowering, to reuse its key.
pub struct GoldilocksInputs {
  source_owner: CircuitId,
  wires: Vec<Value>,
  is_input: Vec<bool>,
  scheduled: bool,
}

impl GoldilocksInputs {
  /// Whether the translated circuit accepted a parallel witness schedule.
  /// False for counting builders, serial translations and expanded hashes.
  pub fn scheduled(&self) -> bool {
    self.scheduled
  }
}

fn signed(value: Val) -> i128 {
  let n = value.as_canonical_u64();
  if n > P / 2 { i128::from(n) - i128::from(P) } else { i128::from(n) }
}

fn scalar<C: KzgCurve>(n: &BigInt) -> CurveScalar<C> {
  let (sign, limbs) = n.to_u64_digits();
  let radix = CurveScalar::<C>::from_u64(u64::MAX) + CurveScalar::<C>::ONE;
  let v = limbs.iter().rev().fold(CurveScalar::<C>::ZERO, |a, &b| {
    a * radix + CurveScalar::<C>::from_u64(b)
  });
  if sign == Sign::Minus { -v } else { v }
}

fn integer<C: KzgCurve>(value: CurveScalar<C>) -> BigInt {
  let bytes: Vec<_> =
    value.canonical_limbs_le().into_iter().flat_map(u64::to_le_bytes).collect();
  BigInt::from_biguint(Sign::Plus, BigUint::from_bytes_le(&bytes))
}

#[cfg(test)]
fn interval(coefficients: [i128; 5], bounds: [u64; 3]) -> (BigInt, BigInt) {
  let [a, b, c] = bounds.map(BigInt::from);
  let maxima = [&a * &b, a, b, c];
  let mut low = BigInt::from(coefficients[4]);
  let mut high = low.clone();
  for (coefficient, maximum) in coefficients.into_iter().zip(maxima) {
    let term = coefficient * maximum;
    if coefficient < 0 {
      low += term;
    } else {
      high += term;
    }
  }
  (low, high)
}

fn small_interval(
  coefficients: [i128; 5],
  bounds: [u64; 3],
) -> Option<(i128, i128)> {
  let [a, b, c] = bounds.map(i128::from);
  let maxima =
    [if coefficients[0] == 0 { 0 } else { a.checked_mul(b)? }, a, b, c];
  let (mut low, mut high) = (coefficients[4], coefficients[4]);
  for (coefficient, maximum) in coefficients.into_iter().zip(maxima) {
    let term = coefficient.checked_mul(maximum)?;
    if coefficient < 0 {
      low = low.checked_add(term)?;
    } else {
      high = high.checked_add(term)?;
    }
  }
  Some((low, high))
}

fn boolean_gate(gate: &Gate<Val>) -> bool {
  gate.wires[0] == gate.wires[1]
    && gate.coefficients
      == [Val::ONE, Val::NEG_ONE, Val::ZERO, Val::ZERO, Val::ZERO]
}

fn signed_scalar<C: KzgCurve>(n: i128) -> CurveScalar<C> {
  let value = CurveScalar::<C>::from_u64(
    u64::try_from(n.unsigned_abs()).expect("signed Goldilocks coefficient"),
  );
  if n < 0 { -value } else { value }
}

fn arithmetic_range(
  gate: &Gate<Val>,
  bounds: [u64; 3],
) -> Option<(i128, i128)> {
  let mut coefficients = gate.coefficients.map(signed);
  coefficients[3] = 0;
  if coefficients == [-1, 1, 0, 0, 0] && bounds[1] <= 1 {
    Some((0, i128::from(bounds[0])))
  } else {
    small_interval(coefficients, bounds)
  }
}

fn selection_range(
  source: &Circuit<Val>,
  gate: &Gate<Val>,
  bounds: &[u64],
) -> Option<(i128, i128)> {
  if gate.coefficients
    != [Val::ZERO, Val::ONE, Val::ONE, Val::NEG_ONE, Val::ZERO]
  {
    return None;
  }
  let Recipe::Arithmetic(yes) = source.value_source(gate.wires[0]).unwrap()
  else {
    return None;
  };
  let Recipe::Arithmetic(no) = source.value_source(gate.wires[1]).unwrap()
  else {
    return None;
  };
  let yes = &source.gates()[yes];
  let no = &source.gates()[no];
  if yes.coefficients
    != [Val::ONE, Val::ZERO, Val::ZERO, Val::NEG_ONE, Val::ZERO]
    || no.coefficients
      != [Val::NEG_ONE, Val::ONE, Val::ZERO, Val::NEG_ONE, Val::ZERO]
    || yes.wires[0] != no.wires[1]
    || bounds[yes.wires[0].index()] > 1
  {
    return None;
  }
  // bit*a + (1-bit)*b lies in [0,max(a,b)], not [0,a+b].
  Some((
    0,
    i128::from(bounds[yes.wires[1].index()].max(bounds[no.wires[0].index()])),
  ))
}

fn root(parents: &mut [usize], mut i: usize) -> usize {
  while parents[i] != i {
    parents[i] = parents[parents[i]];
    i = parents[i];
  }
  i
}

/// Propagate only independently enforced bounds through equality and acyclic
/// integer arithmetic. An unbounded equality cycle cannot justify its own range.
fn propagate_bounds(
  source: &Circuit<Val>,
  bounds: &mut [u64],
  checked: &mut [bool],
  integer_gates: &mut [bool],
) {
  let mut parents: Vec<_> = (0..source.num_values()).collect();
  for gate in source.gates() {
    if gate.coefficients
      == [Val::ZERO, Val::ONE, Val::NEG_ONE, Val::ZERO, Val::ZERO]
    {
      let a = root(&mut parents, gate.wires[0].index());
      let b = root(&mut parents, gate.wires[1].index());
      parents[a.max(b)] = a.min(b);
    }
  }
  for (i, recipe) in source.value_sources().enumerate() {
    if let Recipe::Constant(value) = recipe {
      bounds[i] = value.as_canonical_u64();
      checked[i] = true;
    }
    let r = root(&mut parents, i);
    parents[i] = r;
    if checked[i] {
      bounds[r] = bounds[r].min(bounds[i]);
      checked[r] = true;
    }
  }
  for (i, recipe) in source.value_sources().enumerate() {
    let Recipe::Arithmetic(index) = recipe else {
      continue;
    };
    let gate = &source.gates()[index];
    let [a, b, c] = gate.wires.map(|w| parents[w.index()]);
    let [qm, qa, qb, _, _] = gate.coefficients;
    if (qm != Val::ZERO || qa != Val::ZERO) && !checked[a]
      || (qm != Val::ZERO || qb != Val::ZERO) && !checked[b]
    {
      continue;
    }
    if let Some((low, high)) =
      arithmetic_range(gate, [bounds[a], bounds[b], bounds[c]])
      && low >= 0
      && high < i128::from(P)
    {
      let r = parents[i];
      bounds[r] = bounds[r].min(u64::try_from(high).unwrap());
      checked[r] = true;
      integer_gates[index] = true;
    }
  }
  // Roots have the smallest index in their component, so this in-place
  // expansion never overwrites another component's root.
  for (i, &r) in parents.iter().enumerate() {
    bounds[i] = bounds[r];
    checked[i] = checked[r];
  }
}

/// Width of the shared range-check lookup table (`2^20` rows, matching
/// `recursive::native_field` and fitting cleanly inside `TABLE_HEIGHT = 2^22`).
const RANGE_BITS: usize = 20;
const RANGE_MASK: u64 = (1u64 << RANGE_BITS) - 1;
/// High-limb width paired with `u20` to enforce exact 32-bit canonical words
/// (`20 + 12 = 32`).
const CANONICAL_HIGH_BITS: usize = 32 - RANGE_BITS;
const CANONICAL_HIGH_MASK: u64 = (1u64 << CANONICAL_HIGH_BITS) - 1;

#[inline]
fn extract_u20_limb(words: [u64; 4], i: usize) -> u64 {
  let bit = i * RANGE_BITS;
  let word = bit / 64;
  let shift = bit % 64;
  let low = words[word] >> shift;
  let high = if shift > 64 - RANGE_BITS && word + 1 < words.len() {
    words[word + 1] << (64 - shift)
  } else {
    0
  };
  (low | high) & RANGE_MASK
}

/// Range checks use one shared 20-bit table. Rounding up the bit count remains
/// sound: even the largest gate and quotient products (`<= 7 * 20 = 140` bits)
/// satisfy `2^140 * P < 2^204 < Fr`.
fn range<C: KzgCurve>(
  b: &mut CircuitBuilder<CurveScalar<C>>,
  table: Table,
  value: Value,
  bits: usize,
) {
  if bits == 0 {
    let zero = b.constant(CurveScalar::<C>::ZERO);
    b.assert_equal(value, zero);
    return;
  }
  if bits == 1 {
    b.assert_bool(value);
    return;
  }
  match bits.div_ceil(RANGE_BITS) {
    1 => b.lookup(table, &[value]),
    2 => range_limbs::<C, 2>(b, table, value),
    3 => range_limbs::<C, 3>(b, table, value),
    4 => range_limbs::<C, 4>(b, table, value),
    5 => range_limbs::<C, 5>(b, table, value),
    6 => range_limbs::<C, 6>(b, table, value),
    7 => range_limbs::<C, 7>(b, table, value),
    _ => panic!("Goldilocks range exceeds quotient bound"),
  }
}

fn range_limbs<C: KzgCurve, const N: usize>(
  b: &mut CircuitBuilder<CurveScalar<C>>,
  table: Table,
  value: Value,
) {
  let limbs = b.hint_many_pure::<N>("integer limbs", &[value], |v| {
    let words = v[0].canonical_limbs_le();
    Ok(std::array::from_fn(|i| {
      CurveScalar::<C>::from_u64(extract_u20_limb(words, i))
    }))
  });
  for limb in limbs {
    b.lookup(table, &[limb]);
  }
  let radix = CurveScalar::<C>::from_u32(1 << RANGE_BITS);
  let mut coefficient = CurveScalar::<C>::ONE;
  let mut acc = limbs[0];
  for &limb in &limbs[1..N - 1] {
    coefficient *= radix;
    acc = b.affine(
      [acc, limb],
      [CurveScalar::<C>::ONE, coefficient],
      CurveScalar::<C>::ZERO,
    );
  }
  coefficient *= radix;
  b.constrain_gate(
    [acc, limbs[N - 1], value],
    [
      CurveScalar::<C>::ZERO,
      CurveScalar::<C>::ONE,
      coefficient,
      -CurveScalar::<C>::ONE,
      CurveScalar::<C>::ZERO,
    ],
  );
}

/// Canonical Goldilocks check (`value < 2^64 - 2^32 + 1`): decomposes `value`
/// into exact 32-bit `lo = lo0 + 2^20·lo1` and `hi = hi0 + 2^20·hi1` with
/// `lo0, hi0 ∈ u20` and `lo1, hi1 ∈ u12`, then enforces `hi = 0xffffffff ⇒ lo = 0`.
fn canonical<C: KzgCurve>(
  b: &mut CircuitBuilder<CurveScalar<C>>,
  u20: Table,
  u12: Table,
  value: Value,
) {
  let [lo0, lo1, hi0, hi1, inv, max_hi] =
    b.hint_many_pure::<6>("Goldilocks canonical", &[value], |v| {
      let x = v[0].canonical_low_u64();
      let lo = x & u64::from(u32::MAX);
      let hi = x >> 32;
      let delta =
        CurveScalar::<C>::from_u64(hi) - CurveScalar::<C>::from_u32(u32::MAX);
      let (inv, max_hi) = match delta.try_inverse() {
        Some(inv) => (inv, CurveScalar::<C>::ZERO),
        None => (CurveScalar::<C>::ZERO, CurveScalar::<C>::ONE),
      };
      Ok([
        CurveScalar::<C>::from_u64(lo & RANGE_MASK),
        CurveScalar::<C>::from_u64((lo >> RANGE_BITS) & CANONICAL_HIGH_MASK),
        CurveScalar::<C>::from_u64(hi & RANGE_MASK),
        CurveScalar::<C>::from_u64((hi >> RANGE_BITS) & CANONICAL_HIGH_MASK),
        inv,
        max_hi,
      ])
    });
  b.lookup(u20, &[lo0]);
  b.lookup(u12, &[lo1]);
  b.lookup(u20, &[hi0]);
  b.lookup(u12, &[hi1]);
  let radix = CurveScalar::<C>::from_u32(1 << RANGE_BITS);
  let lo = b.affine(
    [lo0, lo1],
    [CurveScalar::<C>::ONE, radix],
    CurveScalar::<C>::ZERO,
  );
  let hi = b.affine(
    [hi0, hi1],
    [CurveScalar::<C>::ONE, radix],
    CurveScalar::<C>::ZERO,
  );
  b.constrain_gate(
    [lo, hi, value],
    [
      CurveScalar::<C>::ZERO,
      CurveScalar::<C>::ONE,
      CurveScalar::<C>::from_u64(1 << 32),
      -CurveScalar::<C>::ONE,
      CurveScalar::<C>::ZERO,
    ],
  );
  // x < 0xffffffff00000001 iff the high word is not 0xffffffff or lo = 0.
  b.assert_bool(max_hi);
  b.constrain_gate(
    [hi, inv, max_hi],
    [
      CurveScalar::<C>::ONE,
      CurveScalar::<C>::ZERO,
      -CurveScalar::<C>::from_u32(u32::MAX),
      CurveScalar::<C>::ONE,
      -CurveScalar::<C>::ONE,
    ],
  );
  let zero = b.constant(CurveScalar::<C>::ZERO);
  b.constrain_gate(
    [max_hi, lo, zero],
    [
      CurveScalar::<C>::ONE,
      CurveScalar::<C>::ZERO,
      CurveScalar::<C>::ZERO,
      CurveScalar::<C>::ZERO,
      CurveScalar::<C>::ZERO,
    ],
  );
}

impl<C: KzgCurve> GoldilocksCircuit<C> {
  pub fn new(source: &Circuit<Val>) -> Self {
    let mut b = CircuitBuilder::<CurveScalar<C>>::new();
    let inputs = Self::translate(source, &mut b, false);
    Self { circuit: b.finish(), inputs }
  }

  /// Count first, then reserve the exact IR lengths to avoid geometric growth
  /// during large translations. This runs the translation twice.
  pub fn new_preallocated(source: &Circuit<Val>) -> Self {
    let stats = Self::estimate(source);
    let mut b = CircuitBuilder::<CurveScalar<C>>::new();
    b.reserve(stats);
    let inputs = Self::translate(source, &mut b, false);
    debug_assert_eq!(b.stats(), stats);
    Self { circuit: b.finish(), inputs }
  }

  /// Exact translated frontend counts without storing the expanded circuit.
  /// Retains a wire mapping and range bounds proportional to source values.
  pub fn estimate(source: &Circuit<Val>) -> CircuitStats {
    let mut b = CircuitBuilder::<CurveScalar<C>>::counting();
    Self::translate(source, &mut b, false);
    b.stats()
  }

  /// Count the scalar translation with generic hash gates, without storing it.
  pub fn estimate_with_expanded_hashes(source: &Circuit<Val>) -> CircuitStats {
    let mut b = CircuitBuilder::<CurveScalar<C>>::counting();
    Self::translate(source, &mut b, true);
    b.stats()
  }

  /// Expand compact hash calls only after translating the surrounding
  /// Goldilocks arithmetic. The original hash bytes remain constrained.
  pub fn new_with_expanded_hashes(source: &Circuit<Val>) -> Self {
    let mut b = CircuitBuilder::<CurveScalar<C>>::new();
    let inputs = Self::translate(source, &mut b, true);
    Self { circuit: b.finish(), inputs }
  }

  fn translate(
    source: &Circuit<Val>,
    b: &mut CircuitBuilder<CurveScalar<C>>,
    expand_hashes: bool,
  ) -> GoldilocksInputs {
    Self::translate_with_chunk_size(source, b, expand_hashes, 1 << 16)
  }

  pub(super) fn translate_with_chunk_size(
    source: &Circuit<Val>,
    b: &mut CircuitBuilder<CurveScalar<C>>,
    expand_hashes: bool,
    chunk_size: usize,
  ) -> GoldilocksInputs {
    Self::translate_inner(source, b, expand_hashes, chunk_size, |b, index| {
      b.input_indexed("goldilocks", index)
    })
  }

  fn translate_inner(
    source: &Circuit<Val>,
    b: &mut CircuitBuilder<CurveScalar<C>>,
    expand_hashes: bool,
    chunk_size: usize,
    mut input: impl FnMut(&mut CircuitBuilder<CurveScalar<C>>, usize) -> Value,
  ) -> GoldilocksInputs {
    let mut chunks =
      (cfg!(feature = "parallel") && chunk_size > 0 && !expand_hashes)
        .then(Vec::new);
    let record_chunk =
      |b: &CircuitBuilder<CurveScalar<C>>, chunks: &mut Option<Vec<usize>>| {
        if let Some(ends) = chunks {
          let end = b.stats().values;
          if end - ends.last().copied().unwrap_or(0) >= chunk_size {
            ends.push(end);
          }
        }
      };
    let range_table = b.fixed_table(
      "u20",
      (0..1u32 << RANGE_BITS)
        .map(|v| vec![CurveScalar::<C>::from_u32(v)])
        .collect(),
    );
    let canonical_high_table = b.fixed_table(
      "u12",
      (0..1u32 << CANONICAL_HIGH_BITS)
        .map(|v| vec![CurveScalar::<C>::from_u32(v)])
        .collect(),
    );
    let mut bounds = vec![P - 1; source.num_values()];
    let mut checked = vec![false; source.num_values()];
    let mut integer_gates = vec![false; source.gates().len()];
    // x²-x=0 has exactly the same roots in both fields. These gates are
    // lifted directly below, independently enforcing this bound.
    for gate in source.gates() {
      if boolean_gate(gate) {
        bounds[gate.wires[0].index()] = 1;
        checked[gate.wires[0].index()] = true;
      }
    }
    let table_bounds: Vec<Vec<u64>> = source
      .tables()
      .iter()
      .map(|table| {
        (0..table.width())
          .map(|column| {
            table
              .rows()
              .iter()
              .map(|row| row[column].as_canonical_u64())
              .max()
              .unwrap()
          })
          .collect()
      })
      .collect();
    // Membership checks give independently enforced bounds.
    for lookup in source.lookups() {
      for (column, value) in lookup.values.iter().enumerate() {
        let maximum = table_bounds[lookup.table.index()][column];
        bounds[value.index()] = bounds[value.index()].min(maximum);
        checked[value.index()] = true;
      }
    }
    drop(table_bounds);
    {
      for (_, hash_input, hash_output) in source.blake3_domain_calls() {
        for value in hash_input.iter().chain(hash_output) {
          bounds[value.index()] = bounds[value.index()].min(255);
          checked[value.index()] = true;
        }
      }
    }
    propagate_bounds(source, &mut bounds, &mut checked, &mut integer_gates);
    let mut wires = Vec::with_capacity(source.num_values());
    let mut inputs = Vec::with_capacity(source.num_values());
    for (i, recipe) in source.value_sources().enumerate() {
      if let Recipe::Constant(value) = recipe {
        let n = value.as_canonical_u64();
        bounds[i] = n;
        checked[i] = true;
        wires.push(b.constant(CurveScalar::<C>::from_u64(n)));
        inputs.push(false);
      } else {
        // Acyclic arithmetic with no modular wrap derives a range from
        // earlier wires. The translated gate enforces that equality.
        if let Recipe::Arithmetic(gate) = recipe {
          let gate_index = gate;
          let gate = &source.gates()[gate_index];
          let output_range =
            selection_range(source, gate, &bounds).or_else(|| {
              arithmetic_range(gate, gate.wires.map(|w| bounds[w.index()]))
            });
          if let Some((low, high)) = output_range
            && low >= 0
            && high < i128::from(P)
          {
            bounds[i] = bounds[i].min(u64::try_from(high).unwrap());
            checked[i] = true;
            integer_gates[gate_index] = true;
          }
        }
        let value = input(b, i);
        if !checked[i] {
          canonical(b, range_table, canonical_high_table, value);
        }
        wires.push(value);
        inputs.push(true);
      }
      record_chunk(b, &mut chunks);
    }
    drop(checked);
    let tables: Vec<_> = source
      .tables()
      .iter()
      .map(|table| {
        b.fixed_table(
          table.name(),
          table
            .rows()
            .iter()
            .map(|row| {
              row
                .iter()
                .map(|v| CurveScalar::<C>::from_u64(v.as_canonical_u64()))
                .collect()
            })
            .collect(),
        )
      })
      .collect();
    for lookup in source.lookups() {
      b.lookup(
        tables[lookup.table.index()],
        &lookup.values.iter().map(|v| wires[v.index()]).collect::<Vec<_>>(),
      );
    }
    {
      if expand_hashes {
        use multi_stark::plonkish::gadgets::ByteGadgets;
        use multi_stark::plonkish::gadgets::blake3_domain;
        let bytes = ByteGadgets::new(b);
        for (domain, hash_input, hash_output) in source.blake3_domain_calls() {
          let input: Vec<_> = hash_input
            .iter()
            .map(|v| bytes.constrain_byte(b, wires[v.index()]))
            .collect();
          let digest = blake3_domain(b, &bytes, domain, &input);
          for (actual, expected) in digest.iter().zip(*hash_output) {
            b.assert_equal(actual.value(), wires[expected.index()]);
          }
        }
      } else {
        b.enable_compact_blake3();
        for (domain, hash_input, hash_output) in source.blake3_domain_calls() {
          b.constrain_blake3_domain(
            domain,
            hash_input.iter().map(|v| wires[v.index()]).collect(),
            &(*hash_output).map(|v| wires[v.index()]),
          );
        }
      }
    }
    for (gate, integer) in source.gates().iter().zip(integer_gates) {
      constrain_gate(b, range_table, gate, &wires, &bounds, integer);
      record_chunk(b, &mut chunks);
    }
    drop(bounds);
    for value in source.public_values() {
      b.expose_public(wires[value.index()]);
    }
    let mut scheduled = false;
    if let Some(mut ends) = chunks {
      if ends.last() != Some(&b.stats().values) {
        ends.push(b.stats().values);
      }
      let chunk_count = ends.len();
      let started = std::time::Instant::now();
      let certified = b.try_parallel_witness_prefix(ends);
      tracing::info!(
        chunks = chunk_count,
        certified,
        certificate_seconds = started.elapsed().as_secs_f64(),
        "Goldilocks witness schedule checked"
      );
      scheduled = certified;
    }
    GoldilocksInputs {
      source_owner: source.id(),
      wires,
      is_input: inputs,
      scheduled,
    }
  }

  pub fn assign(
    &self,
    source: &Assignment<Val>,
    witness: &mut Witness<'_, CurveScalar<C>>,
  ) -> Result<(), WitnessError> {
    self.inputs.assign(source, witness)
  }
}

impl GoldilocksInputs {
  pub fn assign<C: KzgCurve>(
    &self,
    source: &Assignment<Val>,
    witness: &mut Witness<'_, CurveScalar<C>>,
  ) -> Result<(), WitnessError> {
    let values = source.values(self.source_owner)?;
    for (i, &input) in self.is_input.iter().enumerate() {
      if input {
        witness.set(
          self.wires[i],
          CurveScalar::<C>::from_u64(values[i].as_canonical_u64()),
        )?;
      }
    }
    Ok(())
  }
}

fn constrain_gate<C: KzgCurve>(
  b: &mut CircuitBuilder<CurveScalar<C>>,
  table: Table,
  gate: &Gate<Val>,
  wires: &[Value],
  bounds: &[u64],
  integer_relation: bool,
) {
  let coefficients = gate.coefficients.map(signed);
  let values = gate.wires.map(|v| wires[v.index()]);
  if integer_relation
    || boolean_gate(gate)
    || small_interval(coefficients, gate.wires.map(|v| bounds[v.index()]))
      .is_some_and(|(low, high)| low > -i128::from(P) && high < i128::from(P))
  {
    b.constrain_gate(values, coefficients.map(signed_scalar));
    return;
  }
  let interval::GatePlan::Quotient { offset, bits } = interval::GatePlan::new(
    coefficients,
    gate.wires.map(|v| bounds[v.index()]),
  ) else {
    b.constrain_gate(values, coefficients.map(signed_scalar));
    return;
  };
  let hint = quotient::QuotientHint::from_limbs(coefficients, offset);
  let [qm, qa, qb, qc, k] = coefficients.map(signed_scalar);
  let k_plus_offset = k + CurveScalar::<C>::from_limbs_le(offset.0);
  let [quotient, t1] =
    b.hint_many_pure::<2>("Goldilocks quotient", &values, move |v| {
      let q = hint.evaluate(v)?;
      let t = qm * v[0] * v[1] + qa * v[0] + qb * v[1] + k_plus_offset;
      Ok([q, t])
    });
  range(b, table, quotient, bits);
  b.constrain_gate(
    [values[0], values[1], t1],
    [qm, qa, qb, -CurveScalar::<C>::ONE, k_plus_offset],
  );
  b.constrain_gate(
    [t1, values[2], quotient],
    [
      CurveScalar::<C>::ZERO,
      CurveScalar::<C>::ONE,
      qc,
      -CurveScalar::<C>::from_u64(P),
      CurveScalar::<C>::ZERO,
    ],
  );
}

#[cfg(test)]
#[path = "foreign/tests/independent_witness.rs"]
mod independent_witness_tests;
#[cfg(test)]
#[path = "foreign/tests/indexed_names.rs"]
mod indexed_names_tests;
#[cfg(test)]
#[path = "foreign/tests/translation_intervals.rs"]
mod interval_tests;
#[cfg(test)]
#[path = "foreign/tests/quotient_hints.rs"]
mod quotient_tests;
#[cfg(test)]
#[path = "foreign/tests/range_hints.rs"]
mod range_tests;

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn census_matches_materialized_translation() {
    for compact in [false, true] {
      let mut b = CircuitBuilder::<Val>::new();
      if compact {
        b.enable_compact_blake3();
      }
      let x = b.input("x");
      let y = b.input("y");
      let bit = b.is_zero(x);
      let product = b.mul(x, y);
      let selected = b.select(bit, product, y);
      let five = b.constant(Val::from_u8(5));
      let folded = b.add(five, five);
      let output = b.add(selected, folded);
      let table = b.fixed_table(
        "byte",
        (0..=255).map(|i| vec![Val::from_u16(i)]).collect(),
      );
      b.lookup(table, &[y]);
      if compact {
        for len in [0, 1, 64, 65, 1024, 1025, 2049] {
          b.constrain_blake3(vec![y; len], &[y; 32]);
        }
      }
      b.expose_public(output);
      let source = b.finish();
      let regular = GoldilocksCircuit::<Bn254>::new(&source);
      let reserved = GoldilocksCircuit::<Bn254>::new_preallocated(&source);
      assert_eq!(
        GoldilocksCircuit::<Bn254>::estimate(&source),
        regular.circuit.stats()
      );
      assert_eq!(regular.circuit.stats(), reserved.circuit.stats());
      assert_eq!(
        GoldilocksCircuit::<Bn254>::estimate_with_expanded_hashes(&source),
        GoldilocksCircuit::<Bn254>::new_with_expanded_hashes(&source)
          .circuit
          .stats()
      );
      let bls_regular =
        GoldilocksCircuit::<crate::kzg::curve::Bls12381>::new(&source);
      assert_eq!(
        GoldilocksCircuit::<crate::kzg::curve::Bls12381>::estimate(&source),
        bls_regular.circuit.stats()
      );
      assert_eq!(bls_regular.circuit.stats(), regular.circuit.stats());
      for (a, b) in regular.circuit.gates().iter().zip(reserved.circuit.gates())
      {
        assert_eq!(a.coefficients, b.coefficients);
        assert_eq!(a.wires.map(|v| v.index()), b.wires.map(|v| v.index()));
      }
    }
  }

  #[test]
  fn selection_preserves_integer_bounds_and_rejects_aliases() {
    for maximum in [255, P - 1] {
      let mut b = CircuitBuilder::<Val>::new();
      let bit = b.input("bit");
      let yes = b.input("yes");
      let no = b.input("no");
      if maximum == 255 {
        let table = b.fixed_table(
          "byte",
          (0..=255).map(|v| vec![Val::from_u16(v)]).collect(),
        );
        b.lookup(table, &[yes]);
        b.lookup(table, &[no]);
      }
      let bit_handle = b.assert_bool(bit);
      let out = b.select(bit_handle, yes, no);
      b.expose_public(out);
      let source = b.finish();
      let mapped = GoldilocksCircuit::<Bn254>::new(&source);
      if maximum == 255 {
        assert_eq!(mapped.circuit.stats().lookups, 2);
        assert_eq!(mapped.circuit.stats().gates, source.stats().gates + 1);
      } else {
        // Only the two branches need canonical checks; selection
        // intermediates and output inherit their enforced ranges.
        assert_eq!(mapped.circuit.stats().lookups, 8);
      }
      for choice in [0, 1] {
        for (a, c) in [(0, maximum), (maximum, 0), (maximum, maximum - 1)] {
          let mut witness = source.witness();
          witness.set(bit, Val::from_u8(choice)).unwrap();
          witness.set(yes, Val::from_u64(a)).unwrap();
          witness.set(no, Val::from_u64(c)).unwrap();
          let assignment = witness.generate().unwrap();
          let mut witness = mapped.circuit.witness();
          mapped.assign(&assignment, &mut witness).unwrap();
          let assignment = witness.generate().unwrap();
          assert_eq!(
            assignment.public_values(),
            [Scalar::from_u64(if choice == 1 { a } else { c })]
          );
          // Alter each source wire by p, preserving its Goldilocks
          // residue. Scalar constraints must still reject it.
          for (i, &is_input) in mapped.inputs.is_input.iter().enumerate() {
            if is_input {
              let mut forged =
                assignment.values(mapped.circuit.id()).unwrap().to_vec();
              forged[mapped.inputs.wires[i].index()] += Scalar::from_u64(P);
              assert!(mapped.circuit.check_values(&forged).is_err());
            }
          }
        }
      }
    }
  }

  #[test]
  fn boolean_bounds_are_enforced_without_integer_range_gadgets() {
    let mut b = CircuitBuilder::<Val>::new();
    let x = b.input("bit");
    b.assert_bool(x);
    let y = b.affine([x, x], [Val::from_u8(15), Val::ZERO], Val::from_u8(3));
    b.expose_public(y);
    let source = b.finish();
    let mapped = GoldilocksCircuit::<Bn254>::new(&source);
    assert_eq!(mapped.circuit.stats().lookups, 0);
    for bit in [0, 1] {
      let mut witness = source.witness();
      witness.set(x, Val::from_u8(bit)).unwrap();
      let assignment = witness.generate().unwrap();
      let mut witness = mapped.circuit.witness();
      mapped.assign(&assignment, &mut witness).unwrap();
      let output = witness.generate().unwrap();
      assert_eq!(output.public_values(), [Scalar::from_u8(bit * 15 + 3)]);
    }
    for invalid in [2, P, P + 1, u64::MAX] {
      let mut witness = mapped.circuit.witness();
      for (i, &is_input) in mapped.inputs.is_input.iter().enumerate() {
        if is_input {
          witness
            .set(
              mapped.inputs.wires[i],
              Scalar::from_u64(if i == x.index() { invalid } else { 3 }),
            )
            .unwrap();
        }
      }
      assert!(witness.generate().is_err());
    }
  }

  #[test]
  fn equality_ranges_need_an_independent_bound() {
    for bounded in [false, true] {
      let mut b = CircuitBuilder::<Val>::new();
      let x = b.input("x");
      let bit = b.input("bit");
      b.assert_bool(bit);
      let y = b.mul(x, bit);
      b.assert_equal(x, y); // At bit=1 this cycle implies no range.
      if bounded {
        let byte = b.input("byte");
        let table = b.fixed_table(
          "byte",
          (0..=255).map(|v| vec![Val::from_u16(v)]).collect(),
        );
        b.lookup(table, &[byte]);
        b.assert_equal(y, byte);
      }
      let source = b.finish();
      let mapped = GoldilocksCircuit::<Bn254>::new(&source);
      if bounded {
        assert_eq!(mapped.circuit.stats().lookups, 1);
      }
      for n in [7, P, P + 7] {
        let mut witness = mapped.circuit.witness();
        for (i, &is_input) in mapped.inputs.is_input.iter().enumerate() {
          if is_input {
            witness
              .set(
                mapped.inputs.wires[i],
                Scalar::from_u64(if i == bit.index() { 1 } else { n }),
              )
              .unwrap();
          }
        }
        assert_eq!(witness.generate().is_ok(), n == 7);
      }
    }
  }

  #[test]
  fn modular_arithmetic_and_canonical_boundaries() {
    let mut b = CircuitBuilder::<Val>::new();
    let x = b.input("x");
    let y = b.input("y");
    let product = b.mul(x, y);
    let result = b.sub(product, x);
    b.expose_public(result);
    let source = b.finish();
    let mapped = GoldilocksCircuit::<Bn254>::new(&source);
    for (a, c) in
      [(0, 0), (1, 2), (P - 1, P - 1), (P - 1, 2), (1 << 63, 1 << 63)]
    {
      let mut witness = source.witness();
      witness.set(x, Val::from_u64(a)).unwrap();
      witness.set(y, Val::from_u64(c)).unwrap();
      let assignment = witness.generate().unwrap();
      let mut witness = mapped.circuit.witness();
      mapped.assign(&assignment, &mut witness).unwrap();
      let output = witness.generate().unwrap();
      assert_eq!(
        output.public_values(),
        &[Scalar::from_u64(assignment.public_values()[0].as_canonical_u64())]
      );
      let quotient = mapped
        .circuit
        .gates()
        .iter()
        .find_map(|gate| {
          gate.wires.iter().zip(&gate.coefficients[1..4]).find_map(
            |(&wire, &coefficient)| {
              (coefficient == -Scalar::from_u64(P)
                && matches!(
                  mapped.circuit.value_source(wire),
                  Ok(Recipe::Hint)
                ))
              .then_some(wire)
            },
          )
        })
        .expect("constrained modular quotient");
      let mut forged = output.values(mapped.circuit.id()).unwrap().to_vec();
      forged[quotient.index()] += Scalar::ONE;
      assert!(mapped.circuit.check_values(&forged).is_err());
    }
    // Bypass the source witness API: noncanonical scalar inputs (including
    // `P`, `u64::MAX`, and `2^64`) must fail the translated constraints.
    let two_pow_64 = Scalar::from_u64(1 << 32) * Scalar::from_u64(1 << 32);
    for invalid in [
      Scalar::from_u64(P),
      Scalar::from_u64(u64::MAX),
      two_pow_64,
      two_pow_64 + Scalar::ONE,
    ] {
      let mut witness = mapped.circuit.witness();
      for (i, &is_input) in mapped.inputs.is_input.iter().enumerate() {
        if is_input {
          let value = if i == x.index() { invalid } else { Scalar::ZERO };
          witness.set(mapped.inputs.wires[i], value).unwrap();
        }
      }
      assert!(witness.generate().is_err());
    }
    // Forging a 12-bit canonical high limb to `2^12` while keeping every
    // packing and canonical gate satisfied must be rejected by the `u12` table
    // even though `2^12 ∈ u20`.
    let mut witness = source.witness();
    witness.set(x, Val::from_u64(1 << 32)).unwrap();
    witness.set(y, Val::ZERO).unwrap();
    let assignment = witness.generate().unwrap();
    let mut witness = mapped.circuit.witness();
    mapped.assign(&assignment, &mut witness).unwrap();
    let output = witness.generate().unwrap();
    // Canonical hint outputs for `x` are `[lo0, lo1, hi0, hi1, inv, max_hi]`,
    // followed by `lo` and `hi` affine wires.
    let lo1_wire = mapped
      .circuit
      .lookups()
      .iter()
      .find(|l| mapped.circuit.tables()[l.table.index()].name() == "u12")
      .expect("canonical u12 lookup")
      .values[0]
      .index();
    let mut forged = output.values(mapped.circuit.id()).unwrap().to_vec();
    forged[lo1_wire] = Scalar::from_u32(1 << 12); // lo1 = 2^12 (fails u12)
    forged[lo1_wire + 1] = Scalar::ZERO; // hi0 = 0
    forged[lo1_wire + 3] = (-Scalar::from_u32(u32::MAX)).try_inverse().unwrap(); // inv
    forged[lo1_wire + 5] = Scalar::from_u64(1 << 32); // lo = 2^32
    forged[lo1_wire + 6] = Scalar::ZERO; // hi = 0
    assert_eq!(
      mapped.circuit.check_values(&forged),
      Err(WitnessError::LookupMissing { table: "u12".into() })
    );
  }

  #[test]
  fn arbitrary_gate_coefficients_and_lookup_bounds() {
    let mut b = CircuitBuilder::<Val>::new();
    let x = b.input("x");
    let y = b.input("y");
    let table =
      b.fixed_table("small", (0..16).map(|i| vec![Val::from_u8(i)]).collect());
    b.lookup(table, &[x]);
    b.lookup(table, &[y]);
    let product = b.mul(x, y);
    let coefficient = Val::from_u64(P / 2);
    b.constrain_gate(
      [x, y, product],
      [coefficient, Val::ZERO, Val::ZERO, -coefficient, Val::ZERO],
    );
    b.expose_public(product);
    let source = b.finish();
    let mapped = GoldilocksCircuit::<Bn254>::new(&source);
    let mut witness = source.witness();
    witness.set(x, Val::from_u8(15)).unwrap();
    witness.set(y, Val::from_u8(13)).unwrap();
    let assignment = witness.generate().unwrap();
    let mut witness = mapped.circuit.witness();
    mapped.assign(&assignment, &mut witness).unwrap();
    let output = witness.generate().unwrap();
    assert_eq!(output.public_values(), &[Scalar::from_u8(195)]);
    let mut forged = output.values(mapped.circuit.id()).unwrap().to_vec();
    forged[mapped.inputs.wires[product.index()].index()] += Scalar::ONE;
    assert!(mapped.circuit.check_values(&forged).is_err());
  }

  #[test]
  fn lookup_tuning_respects_the_quotient_budget() {
    fn check<C: KzgCurve>() {
      let mut b = CircuitBuilder::<CurveScalar<C>>::new();
      let x = b.input("x");
      let y = b.mul(x, x);
      b.expose_public(y);
      let compiled =
        b.finish().lower_to_multi_stark(CurveScalar::<C>::from_u8(1)).unwrap();
      let height = compiled.main_height();
      let tuned = compiled.kzg_circuit_inputs(height, 4).unwrap();
      assert_eq!(tuned[0].lookup_group_size, 4);
      assert!(matches!(
        compiled.kzg_circuit_inputs(height, 1),
        Err(LoweringError::QuotientBudgetTooSmall)
      ));
    }
    check::<Bn254>();
    check::<crate::kzg::curve::Bls12381>();
  }

  #[test]
  fn bls12_381_modular_arithmetic_and_canonical_boundaries() {
    use crate::kzg::curve::Bls12381;
    type BlsScalar = CurveScalar<Bls12381>;
    let mut b = CircuitBuilder::<Val>::new();
    let x = b.input("x");
    let y = b.input("y");
    let product = b.mul(x, y);
    let result = b.sub(product, x);
    b.expose_public(result);
    let source = b.finish();
    let mapped = GoldilocksCircuit::<Bls12381>::new(&source);
    for (a, c) in [(0, 0), (1, 2), (P - 1, P - 1), (P - 1, 2)] {
      let mut witness = source.witness();
      witness.set(x, Val::from_u64(a)).unwrap();
      witness.set(y, Val::from_u64(c)).unwrap();
      let assignment = witness.generate().unwrap();
      let mut witness = mapped.circuit.witness();
      mapped.assign(&assignment, &mut witness).unwrap();
      let output = witness.generate().unwrap();
      assert_eq!(
        output.public_values(),
        &[BlsScalar::from_u64(
          assignment.public_values()[0].as_canonical_u64()
        )]
      );
    }
    let mut witness = mapped.circuit.witness();
    for (i, &is_input) in mapped.inputs.is_input.iter().enumerate() {
      if is_input {
        let value =
          if i == x.index() { BlsScalar::from_u64(P) } else { BlsScalar::ZERO };
        witness.set(mapped.inputs.wires[i], value).unwrap();
      }
    }
    assert!(witness.generate().is_err());
  }

  #[test]
  fn domain_separated_blake3_translates_compact_and_expanded_for_both_curves() {
    use crate::kzg::curve::Bls12381;
    use multi_stark::plonkish::gadgets::{
      Blake3Domain, ByteGadgets, blake3_domain,
    };

    let mut b = CircuitBuilder::<Val>::new();
    b.enable_compact_blake3();
    let bytes = ByteGadgets::new(&mut b);
    let input: Vec<_> =
      (0..16).map(|i| bytes.input(&mut b, &format!("b{i}"))).collect();
    for domain in [Blake3Domain::MerkleLeaf, Blake3Domain::TranscriptSingle] {
      let digest = blake3_domain(&mut b, &bytes, domain, &input);
      for byte in digest {
        b.expose_public(byte.value());
      }
    }
    let source = b.finish();
    let msg: Vec<u8> = (0..16).map(|i| i * 9 + 3).collect();
    let mut w = source.witness();
    for (wire, &byte) in input.iter().zip(&msg) {
      w.set(wire.value(), Val::from_u8(byte)).unwrap();
    }
    let assignment = w.generate().unwrap();
    let expected: Vec<u8> = [
      Blake3Domain::MerkleLeaf.hash_bytes(&msg),
      Blake3Domain::TranscriptSingle.hash_bytes(&msg),
    ]
    .into_iter()
    .flatten()
    .collect();
    assert_eq!(
      assignment.public_values(),
      expected.iter().map(|&x| Val::from_u8(x)).collect::<Vec<_>>()
    );

    fn check_curve<C: KzgCurve>(
      source: &Circuit<Val>,
      assignment: &Assignment<Val>,
      expected: &[u8],
    ) {
      let expected_scalars: Vec<_> =
        expected.iter().map(|&x| CurveScalar::<C>::from_u8(x)).collect();
      for mapped in [
        GoldilocksCircuit::<C>::new_preallocated(source),
        GoldilocksCircuit::<C>::new_with_expanded_hashes(source),
      ] {
        let mut w = mapped.circuit.witness();
        mapped.assign(assignment, &mut w).unwrap();
        let out = w.generate().unwrap();
        assert_eq!(out.public_values(), expected_scalars);
      }
    }
    check_curve::<Bn254>(&source, &assignment, &expected);
    check_curve::<Bls12381>(&source, &assignment, &expected);
  }
}
