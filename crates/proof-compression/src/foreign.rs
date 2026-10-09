//! Goldilocks constraints over the BLS12-381 scalar field.
//! Each modular relation has a bounded quotient; small integer relations lift directly.

use num_bigint::{BigInt, BigUint, Sign};
use p3_field::PrimeField64;

use crate::kzg::field::Scalar;
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

pub trait KzgCircuitExt {
  fn kzg_circuit_inputs(
    &self,
    srs_len: usize,
    quotient_budget: usize,
  ) -> Result<Vec<CircuitInputs<Scalar>>, LoweringError>;
  fn kzg_circuit_input(
    &self,
    index: usize,
    srs_len: usize,
    quotient_budget: usize,
  ) -> Result<Option<CircuitInputs<Scalar>>, LoweringError>;
}
impl KzgCircuitExt for MultiStarkCircuit<Scalar> {
  /// Minimize KZG commitment/evaluation bytes by choosing lookup groups per
  /// trace, within the supplied quotient budget. Include the actual SRS length
  /// because smaller traces also need shifted degree commitments.
  fn kzg_circuit_inputs(
    &self,
    srs_len: usize,
    quotient_budget: usize,
  ) -> Result<Vec<CircuitInputs<Scalar>>, LoweringError> {
    let mut inputs = self.circuit_inputs();
    for input in &mut inputs {
      tune_kzg_input(input, srs_len, quotient_budget)?;
    }
    Ok(inputs)
  }

  /// Generate and tune one circuit's preprocessing, without materializing the others.
  fn kzg_circuit_input(
    &self,
    index: usize,
    srs_len: usize,
    quotient_budget: usize,
  ) -> Result<Option<CircuitInputs<Scalar>>, LoweringError> {
    let Some(mut input) = self.circuit_input(index) else {
      return Ok(None);
    };
    tune_kzg_input(&mut input, srs_len, quotient_budget)?;
    Ok(Some(input))
  }
}

fn tune_kzg_input(
  input: &mut CircuitInputs<Scalar>,
  srs_len: usize,
  quotient_budget: usize,
) -> Result<(), LoweringError> {
  use multi_stark::graph::ExtensionParams;
  use multi_stark::lookup::MAX_LOOKUP_GROUP;
  use multi_stark::lookup::logup_max_degree;
  use multi_stark::lookup::stage2_width;
  let fixed = input.preprocessed.as_ref().expect("lowering has fixed columns");
  if fixed.height() > srs_len {
    return Err(LoweringError::InvalidTraceHeight);
  }
  let graph = input
    .compile_graph(&ExtensionParams {
      degree: 1,
      w: Scalar::ZERO,
      karatsuba: false,
    })
    .expect("valid lowering");
  let commitment_bytes = if fixed.height() == srs_len { 48 } else { 96 };
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
pub struct GoldilocksCircuit {
  pub circuit: Circuit<Scalar>,
  pub inputs: GoldilocksInputs,
}

/// Retain this mapping when consuming the circuit for lowering, to reuse its key.
pub struct GoldilocksInputs {
  source_owner: CircuitId,
  wires: Vec<Value>,
  is_input: Vec<bool>,
}

fn signed(value: Val) -> i128 {
  let n = value.as_canonical_u64();
  if n > P / 2 { i128::from(n) - i128::from(P) } else { i128::from(n) }
}

fn scalar(n: &BigInt) -> Scalar {
  let (sign, limbs) = n.to_u64_digits();
  let radix = Scalar::from_u64(u64::MAX) + Scalar::ONE;
  let v = limbs
    .iter()
    .rev()
    .fold(Scalar::ZERO, |a, &b| a * radix + Scalar::from_u64(b));
  if sign == Sign::Minus { -v } else { v }
}

fn integer(value: Scalar) -> BigInt {
  let bytes: Vec<_> =
    value.canonical_limbs_le().into_iter().flat_map(u64::to_le_bytes).collect();
  BigInt::from_biguint(Sign::Plus, BigUint::from_bytes_le(&bytes))
}

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

fn signed_scalar(n: i128) -> Scalar {
  let value = Scalar::from_u64(
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

/// Range checks use one shared 16-bit table. Rounding up the bit count remains
/// sound: even the largest gate and quotient products are below 2^209 < Fr.
fn range(
  b: &mut CircuitBuilder<Scalar>,
  table: Table,
  value: Value,
  bits: usize,
) {
  if bits == 0 {
    let zero = b.constant(Scalar::ZERO);
    b.assert_equal(value, zero);
    return;
  }
  if bits == 1 {
    b.assert_bool(value);
    return;
  }
  let count = bits.div_ceil(16);
  let mut terms = Vec::with_capacity(count);
  let radix = Scalar::from_u32(1 << 16);
  let mut coefficient = Scalar::ONE;
  for i in 0..count {
    let limb = b.hint("integer limb", &[value], move |v| {
      let limbs = v[0].canonical_limbs_le();
      Ok(Scalar::from_u64((limbs[i / 4] >> (16 * (i % 4))) & 0xffff))
    });
    b.lookup(table, &[limb]);
    terms.push((coefficient, limb));
    coefficient *= radix;
  }
  let packed = b.linear_combination(&terms, Scalar::ZERO);
  b.assert_equal(value, packed);
}

fn canonical(b: &mut CircuitBuilder<Scalar>, table: Table, value: Value) {
  let hi = b.hint("Goldilocks high word", &[value], |v| {
    Ok(Scalar::from_u64(v[0].canonical_low_u64() >> 32))
  });
  let lo = b.hint("Goldilocks low word", &[value], |v| {
    Ok(Scalar::from_u32(
      u32::try_from(v[0].canonical_low_u64() & u64::from(u32::MAX)).unwrap(),
    ))
  });
  range(b, table, hi, 32);
  range(b, table, lo, 32);
  let packed =
    b.affine([hi, lo], [Scalar::from_u64(1 << 32), Scalar::ONE], Scalar::ZERO);
  b.assert_equal(value, packed);
  // x < 0xffffffff00000001 iff the high word is not 0xffffffff or lo = 0.
  let delta = b.affine(
    [hi, hi],
    [Scalar::ONE, Scalar::ZERO],
    -Scalar::from_u32(u32::MAX),
  );
  let max_hi = b.is_zero(delta);
  let invalid = b.mul(max_hi.value(), lo);
  let zero = b.constant(Scalar::ZERO);
  b.assert_equal(invalid, zero);
}

impl GoldilocksCircuit {
  pub fn new(source: &Circuit<Val>) -> Self {
    let mut b = CircuitBuilder::<Scalar>::new();
    let inputs = Self::translate(source, &mut b, false);
    Self { circuit: b.finish(), inputs }
  }

  /// Count first, then reserve the exact IR lengths to avoid geometric growth
  /// during large translations. This runs the translation twice.
  pub fn new_preallocated(source: &Circuit<Val>) -> Self {
    let stats = Self::estimate(source);
    let mut b = CircuitBuilder::<Scalar>::new();
    b.reserve(stats);
    let inputs = Self::translate(source, &mut b, false);
    debug_assert_eq!(b.stats(), stats);
    Self { circuit: b.finish(), inputs }
  }

  /// Exact translated frontend counts without storing the expanded circuit.
  /// Retains a wire mapping and range bounds proportional to source values.
  pub fn estimate(source: &Circuit<Val>) -> CircuitStats {
    let mut b = CircuitBuilder::<Scalar>::counting();
    Self::translate(source, &mut b, false);
    b.stats()
  }

  /// Count the scalar translation with generic hash gates, without storing it.
  pub fn estimate_with_expanded_hashes(source: &Circuit<Val>) -> CircuitStats {
    let mut b = CircuitBuilder::<Scalar>::counting();
    Self::translate(source, &mut b, true);
    b.stats()
  }

  /// Expand compact hash calls only after translating the surrounding
  /// Goldilocks arithmetic. The original hash bytes remain constrained.
  pub fn new_with_expanded_hashes(source: &Circuit<Val>) -> Self {
    let mut b = CircuitBuilder::<Scalar>::new();
    let inputs = Self::translate(source, &mut b, true);
    Self { circuit: b.finish(), inputs }
  }

  fn translate(
    source: &Circuit<Val>,
    b: &mut CircuitBuilder<Scalar>,
    expand_hashes: bool,
  ) -> GoldilocksInputs {
    let range_table = b.fixed_table(
      "u16",
      (0..=u16::MAX).map(|v| vec![Scalar::from_u16(v)]).collect(),
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
    {
      for (hash_input, hash_output) in source.blake3_calls() {
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
        wires.push(b.constant(Scalar::from_u64(n)));
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
        let value = b.input(format!("goldilocks[{i}]"));
        if !checked[i] {
          canonical(b, range_table, value);
        }
        wires.push(value);
        inputs.push(true);
      }
    }
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
                .map(|v| Scalar::from_u64(v.as_canonical_u64()))
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
        use multi_stark::plonkish::gadgets::blake3;
        let bytes = ByteGadgets::new(b);
        for (hash_input, hash_output) in source.blake3_calls() {
          let input: Vec<_> = hash_input
            .iter()
            .map(|v| bytes.constrain_byte(b, wires[v.index()]))
            .collect();
          let digest = blake3(b, &bytes, &input);
          for (actual, expected) in digest.iter().zip(*hash_output) {
            b.assert_equal(actual.value(), wires[expected.index()]);
          }
        }
      } else {
        b.enable_compact_blake3();
        for (hash_input, hash_output) in source.blake3_calls() {
          b.constrain_blake3(
            hash_input.iter().map(|v| wires[v.index()]).collect(),
            &(*hash_output).map(|v| wires[v.index()]),
          );
        }
      }
    }
    for (gate, integer) in source.gates().iter().zip(integer_gates) {
      constrain_gate(b, range_table, gate, &wires, &bounds, integer);
    }
    for value in source.public_values() {
      b.expose_public(wires[value.index()]);
    }
    GoldilocksInputs { source_owner: source.id(), wires, is_input: inputs }
  }

  pub fn assign(
    &self,
    source: &Assignment<Val>,
    witness: &mut Witness<'_, Scalar>,
  ) -> Result<(), WitnessError> {
    self.inputs.assign(source, witness)
  }
}

impl GoldilocksInputs {
  pub fn assign(
    &self,
    source: &Assignment<Val>,
    witness: &mut Witness<'_, Scalar>,
  ) -> Result<(), WitnessError> {
    let values = source.values(self.source_owner)?;
    for (i, &input) in self.is_input.iter().enumerate() {
      if input {
        witness
          .set(self.wires[i], Scalar::from_u64(values[i].as_canonical_u64()))?;
      }
    }
    Ok(())
  }
}

fn constrain_gate(
  b: &mut CircuitBuilder<Scalar>,
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
  let (low, high) =
    interval(coefficients, gate.wires.map(|v| bounds[v.index()]));
  let p = BigInt::from(P);
  if low > -&p && high < p {
    b.constrain_gate(values, coefficients.map(|c| scalar(&BigInt::from(c))));
    return;
  }
  let shift =
    if low < BigInt::from(0) { (-low + &p - 1) / &p } else { BigInt::from(0) };
  let offset = &shift * &p;
  let max_q = (high + &offset) / &p;
  let bits = usize::try_from(max_q.bits()).expect("quotient fits usize");
  assert!(bits <= 130, "Goldilocks gate quotient bound");
  let hint_offset = offset.clone();
  let quotient = b.hint("Goldilocks quotient", &values, move |v| {
    let [a, c, d] = [integer(v[0]), integer(v[1]), integer(v[2])];
    let [qm, qa, qb, qc, k] = coefficients;
    let sum = qm * &a * &c + qa * a + qb * c + qc * d + k + &hint_offset;
    if &sum % P != BigInt::from(0) {
      return Err("invalid Goldilocks gate".into());
    }
    Ok(scalar(&(sum / P)))
  });
  range(b, table, quotient, bits);
  let [qm, qa, qb, qc, k] = coefficients.map(|c| scalar(&BigInt::from(c)));
  let product = b.mul(values[0], values[1]);
  let residual = b.linear_combination(
    &[
      (qm, product),
      (qa, values[0]),
      (qb, values[1]),
      (qc, values[2]),
      (-Scalar::from_u64(P), quotient),
    ],
    k + scalar(&offset),
  );
  let zero = b.constant(Scalar::ZERO);
  b.assert_equal(residual, zero);
}

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
      let regular = GoldilocksCircuit::new(&source);
      let reserved = GoldilocksCircuit::new_preallocated(&source);
      assert_eq!(GoldilocksCircuit::estimate(&source), regular.circuit.stats());
      assert_eq!(regular.circuit.stats(), reserved.circuit.stats());
      assert_eq!(
        GoldilocksCircuit::estimate_with_expanded_hashes(&source),
        GoldilocksCircuit::new_with_expanded_hashes(&source).circuit.stats()
      );
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
      let mapped = GoldilocksCircuit::new(&source);
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
    let mapped = GoldilocksCircuit::new(&source);
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
      let mapped = GoldilocksCircuit::new(&source);
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
    let mapped = GoldilocksCircuit::new(&source);
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
    // Bypass the source witness API: noncanonical scalar inputs must fail
    // the actual translated constraints, not just a conversion helper.
    for invalid in [P, u64::MAX] {
      let mut witness = mapped.circuit.witness();
      for (i, &is_input) in mapped.inputs.is_input.iter().enumerate() {
        if is_input {
          let value = if i == x.index() {
            Scalar::from_u64(invalid)
          } else {
            Scalar::ZERO
          };
          witness.set(mapped.inputs.wires[i], value).unwrap();
        }
      }
      assert!(witness.generate().is_err());
    }
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
    let mapped = GoldilocksCircuit::new(&source);
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
    let mut b = CircuitBuilder::<Scalar>::new();
    let x = b.input("x");
    let y = b.mul(x, x);
    b.expose_public(y);
    let compiled = b.finish().lower_to_multi_stark(Scalar::from_u8(1)).unwrap();
    let height = compiled.main_height();
    let tuned = compiled.kzg_circuit_inputs(height, 4).unwrap();
    assert_eq!(tuned[0].lookup_group_size, 4);
    assert!(matches!(
      compiled.kzg_circuit_inputs(height, 1),
      Err(LoweringError::QuotientBudgetTooSmall)
    ));
  }
}
