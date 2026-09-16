//! The mixed union's element PIOP, compiled from fixed table geometry.
//! Affine constants and the small arithmetic tables are evaluated in this DAG;
//! only the large wiring and jagged tables leave the child as deferred work.
use super::{
  VerifierSetup,
  algebra::{Addresses, Algebra, Symbol},
  boolean::BooleanBlueprint,
};
use anyhow::{Result, ensure};
use flock_prover::{
  element_r1cs::{SparseF128Matrix, union::region_slots},
  field::F128,
  union::UnionInstance,
};
use ix_stage4_trace::{
  F128AlgebraTraceV1, F128InputSourceV1 as Source, F128PackedDirectClaimV1,
  F128VerifierPhaseV1 as Phase,
};

pub(crate) struct ElementBlueprint {
  pub(crate) trace: F128AlgebraTraceV1,
  pub(crate) pcs_claims: Vec<F128PackedDirectClaimV1>,
  pub(super) end: Addresses,
}

pub(super) fn observed_words(union: &UnionInstance<'_>) -> usize {
  if union.has_element() {
    let e = union.m_elem() - 7;
    2 * e + 3 + 2 * (e - union.n_log())
  } else {
    0
  }
}

pub(crate) fn compile_element(
  setup: &impl VerifierSetup,
  boolean: &BooleanBlueprint,
) -> Result<Option<ElementBlueprint>> {
  let shape = setup.verifier_shape();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  if !union.has_element() {
    return Ok(None);
  }
  let (nu, e) = (union.n_log(), union.m_elem() - 7);
  ensure!(e >= nu, "element region dimensions");
  let mut address = boolean.end;
  address.observe_index();
  address.observe_index(); // parent merge of the wiring child
  let mut a = Algebra::new(Phase::Zerocheck);
  let zero = a.constant(F128::ZERO);
  let one = a.constant(F128::ONE);
  let tau = (0..e).map(|_| address.challenge()).collect::<Vec<_>>();
  let mut running = zero;
  let mut r = Vec::with_capacity(e);
  for t in tau {
    let g1 = address.observe();
    let g_inf = address.observe();
    let rho = address.challenge();
    let one_plus_t = a.add(one, t);
    let inverse = a.inv(one_plus_t);
    let weighted_one = a.mul(t, g1);
    let numerator = a.add(running, weighted_one);
    let g0 = a.mul(numerator, inverse);
    let one_plus_rho = a.add(one, rho);
    let at_zero = a.mul(g0, one_plus_rho);
    let at_one = a.mul(g1, rho);
    let infinity_rho = a.mul(g_inf, rho);
    let at_infinity = a.mul(infinity_rho, one_plus_rho);
    let finite = a.add(at_zero, at_one);
    running = a.add(finite, at_infinity);
    r.push(rho);
  }
  let ea = address.observe();
  let eb = address.observe();
  let ec = address.observe();
  let product = a.mul(ea, eb);
  let endpoint = a.add(product, ec);
  a.equal(running, endpoint);
  a.set_phase(Phase::Lincheck);
  let slots = region_slots(&union);
  let mut a_sum = zero;
  let mut b_sum = zero;
  let mut row_tables = Vec::new();
  for slot in &slots {
    let k = slot.layout.kappa;
    let eq = eq_table(&mut a, &r[nu..nu + k]);
    let weight = prefix(&mut a, &r[nu + k..], slot.layout.region_prefix(nu));
    let ca = dot_constants(&mut a, &eq, slot.ty.a_const());
    let cb = dot_constants(&mut a, &eq, slot.ty.b_const());
    let ca = a.mul(weight, ca);
    let cb = a.mul(weight, cb);
    a_sum = a.add(a_sum, ca);
    b_sum = a.add(b_sum, cb);
    row_tables.push((eq, weight));
  }
  let va = a.add(ea, a_sum);
  let vb = a.add(eb, b_sum);
  let alpha = address.challenge();
  let alpha_vb = a.mul(alpha, vb);
  running = a.add(va, alpha_vb);
  let mut column = Vec::with_capacity(e - nu);
  for _ in 0..e - nu {
    let q1 = address.observe();
    let q_inf = address.observe();
    let rho = address.challenge();
    let q0 = a.add(running, q1);
    let sum = a.add(q0, q1);
    let linear = a.add(sum, q_inf);
    let ir = a.mul(q_inf, rho);
    let quadratic = a.mul(ir, rho);
    let linear = a.mul(linear, rho);
    let nonconstant = a.add(quadratic, linear);
    running = a.add(nonconstant, q0);
    column.push(rho);
  }
  column.reverse();
  let mut matrix_sum = zero;
  for (slot, (row_eq, row_weight)) in slots.iter().zip(row_tables) {
    let k = slot.layout.kappa;
    let col_eq = eq_table(&mut a, &column[..k]);
    let col_weight =
      prefix(&mut a, &column[k..], slot.layout.region_prefix(nu));
    let ma = bilinear(&mut a, &row_eq, &col_eq, slot.ty.a_0());
    let mb = bilinear(&mut a, &row_eq, &col_eq, slot.ty.b_0());
    let alpha_mb = a.mul(alpha, mb);
    let combined = a.add(ma, alpha_mb);
    let row_scaled = a.mul(row_weight, combined);
    let term = a.mul(col_weight, row_scaled);
    matrix_sum = a.add(matrix_sum, term);
  }
  // Element evaluations are observed after the two 128-word ring switches.
  let c_value = a.input(Source::ObservedValue(address.observed + 256));
  let lc_value = a.input(Source::ObservedValue(address.observed + 257));
  a.equal(ec, c_value);
  let reported = a.mul(matrix_sum, lc_value);
  a.equal(running, reported);
  let prefix = union
    .element_prefix_coords()
    .into_iter()
    .map(|v| a.constant(v))
    .collect::<Vec<_>>();
  let mut c_point = r.clone();
  c_point.extend_from_slice(&prefix);
  let mut lc_point = r[..nu].to_vec();
  lc_point.extend(column);
  lc_point.extend(prefix);
  let pcs_claims = vec![
    F128PackedDirectClaimV1 {
      point: c_point.into_iter().map(|v| v.0).collect(),
      value: c_value.0,
    },
    F128PackedDirectClaimV1 {
      point: lc_point.into_iter().map(|v| v.0).collect(),
      value: lc_value.0,
    },
  ];
  a.trace.validate(
    0,
    usize::try_from(address.observed + 258)?,
    usize::try_from(address.challenges)?,
    0,
  )?;
  Ok(Some(ElementBlueprint { trace: a.trace, pcs_claims, end: address }))
}

fn eq_table(a: &mut Algebra, point: &[Symbol]) -> Vec<Symbol> {
  let one = a.constant(F128::ONE);
  let mut table = vec![one];
  for &coordinate in point {
    let complement = a.add(one, coordinate);
    let mut next = Vec::with_capacity(2 * table.len());
    for &v in &table {
      next.push(a.mul(v, complement));
    }
    for &v in &table {
      next.push(a.mul(v, coordinate));
    }
    table = next;
  }
  table
}
fn prefix(a: &mut Algebra, point: &[Symbol], bits: usize) -> Symbol {
  let one = a.constant(F128::ONE);
  let mut value = one;
  for (i, &coordinate) in point.iter().enumerate() {
    let factor =
      if (bits >> i) & 1 == 1 { coordinate } else { a.add(one, coordinate) };
    value = a.mul(value, factor);
  }
  value
}
fn dot_constants(
  a: &mut Algebra,
  weights: &[Symbol],
  values: &[F128],
) -> Symbol {
  let mut result = a.constant(F128::ZERO);
  for (&weight, &value) in weights.iter().zip(values) {
    if value == F128::ZERO {
      continue;
    }
    let constant = a.constant(value);
    let term = a.mul(weight, constant);
    result = a.add(result, term);
  }
  result
}
fn bilinear(
  a: &mut Algebra,
  row: &[Symbol],
  column: &[Symbol],
  matrix: &SparseF128Matrix,
) -> Symbol {
  let zero = a.constant(F128::ZERO);
  let mut result = zero;
  for (&weight, entries) in row.iter().zip(&matrix.rows) {
    if entries.is_empty() {
      continue;
    }
    let mut marginal = zero;
    for &(index, coefficient) in entries {
      let constant = a.constant(coefficient);
      let term = a.mul(column[index], constant);
      marginal = a.add(marginal, term);
    }
    let term = a.mul(weight, marginal);
    result = a.add(result, term);
  }
  result
}
