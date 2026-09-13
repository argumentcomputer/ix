//! Proof-free RS zerocheck/union-lincheck DAG and its exact PCS claim wires.

use super::algebra::{Addresses, Algebra, Symbol};
use anyhow::{Result, ensure};
use flock_prover::{
  field::{F128, PHI_8_TABLE},
  union::UnionInstance,
  zerocheck::{
    multilinear::subspace_denominator_pair,
    univariate_skip_optimized::{
      medium_challenges_ghash, small_challenges_ghash,
    },
  },
};
use ix_stage4_trace::{
  F128AlgebraTraceV1, F128DeferredMatrixClaimV1, F128InputSourceV1 as Source,
  F128MatrixSideV1, F128MergedPcsBooleanClaimV1, F128StaticMatrixIdV1,
  F128StructuredWeightV1, F128VerifierPhaseV1 as Phase,
};
use ixby_flock::ixby::exec::CompiledExec;

pub(crate) struct BooleanBlueprint {
  pub(crate) trace: F128AlgebraTraceV1,
  pub(crate) pcs_claims: Vec<F128MergedPcsBooleanClaimV1>,
}

pub(crate) fn compile_boolean(
  setup: &CompiledExec,
) -> Result<BooleanBlueprint> {
  let shape = setup.verifier_shape();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  ensure!(
    !union.has_element() && union.num_boolean() != 0,
    "Boolean Exec blueprint required"
  );
  let mu = shape.circuit.cells().mu();
  let nu = union.n_log();
  let m = union.m_bool();
  ensure!(m >= 13 && m >= nu + 7, "Boolean blueprint dimensions");
  // Inline tape indexing puts the complete wiring child before this parent
  // phase, regardless of the native verifier's execution scheduling.
  let mut address = Addresses {
    observed: u64::try_from(7 + mu * mu.saturating_sub(1) + 4 * mu)?,
    challenges: u64::try_from(6 + 2 * mu + mu * mu.saturating_sub(1) / 2)?,
  };
  let mut a = Algebra::new(Phase::Zerocheck);
  for _ in 0..6 {
    address.challenge();
  }
  let r_outer = (0..m - 13).map(|_| address.challenge()).collect::<Vec<_>>();
  let ab = (0..64).map(|_| address.observe()).collect::<Vec<_>>();
  let c = (0..64).map(|_| address.observe()).collect::<Vec<_>>();
  let z = address.challenge();
  let c_eval = interpolate_lambda(&mut a, &c, z);
  let combined =
    ab.iter().zip(&c).map(|(&ab, &c)| a.add(ab, c)).collect::<Vec<_>>();
  let combined_eval = interpolate_combined(&mut a, &combined, z);
  let mut running = a.add(combined_eval, c_eval);
  let mut r_rest = small_challenges_ghash()
    .into_iter()
    .chain(medium_challenges_ghash())
    .map(|value| a.constant(value))
    .collect::<Vec<_>>();
  r_rest.extend(r_outer);
  ensure!(r_rest.len() == m - 6, "zerocheck rest point");
  let mut mlv = Vec::with_capacity(m - 6);
  for &r_eq in &r_rest {
    let g1 = address.observe();
    let g_inf = address.observe();
    let rho = address.challenge();
    mlv.push(rho);
    let one = a.constant(F128::ONE);
    let one_plus = a.add(one, r_eq);
    let weighted_g1 = a.mul(r_eq, g1);
    let numerator = a.add(running, weighted_g1);
    let inverse = a.inv(one_plus);
    let g0 = a.mul(numerator, inverse);
    let one_plus_rho = a.add(one, rho);
    let term_zero = a.mul(g0, one_plus_rho);
    let term_one = a.mul(g1, rho);
    let infinity_at_rho = a.mul(g_inf, rho);
    let term_inf = a.mul(infinity_at_rho, one_plus_rho);
    let finite = a.add(term_zero, term_one);
    running = a.add(finite, term_inf);
  }
  let final_a = address.observe();
  let final_b = address.observe();
  let expected = a.mul(final_a, final_b);
  a.equal(running, expected);
  a.set_phase(Phase::Lincheck);
  let inner_rest = m - nu - 6;
  let mut x_inner = vec![mlv[0]];
  x_inner.extend_from_slice(&mlv[1 + nu..]);
  let x_outer = mlv[1..1 + nu].to_vec();
  ensure!(x_inner.len() == inner_rest, "lincheck inner point");
  let alpha = address.challenge();
  let alpha_a = a.mul(alpha, final_a);
  let mut target = a.add(alpha_a, final_b);
  let mut betas = Vec::with_capacity(union.num_boolean());
  for (ty, &count) in shape.registry.boolean_types().iter().zip(&shape.counts) {
    if ty.const_pin.is_some() {
      let beta = address.challenge();
      let prefix = prefix_sum(&mut a, &x_outer, count)?;
      let term = a.mul(beta, prefix);
      target = a.add(target, term);
      betas.push(Some(beta));
    } else {
      betas.push(None);
    }
  }
  let mut running = target;
  let mut rr = Vec::with_capacity(inner_rest);
  for _ in 0..inner_rest {
    let q1 = address.observe();
    let q_inf = address.observe();
    let r = address.challenge();
    let q0 = a.add(running, q1);
    let q0_plus_q1 = a.add(q0, q1);
    let c1 = a.add(q0_plus_q1, q_inf);
    let infinity_r = a.mul(q_inf, r);
    let infinity_squared = a.mul(infinity_r, r);
    let linear = a.mul(c1, r);
    let nonconstant = a.add(infinity_squared, linear);
    running = a.add(nonconstant, q0);
    rr.push(r);
  }
  let z_partial = (0..64).map(|_| address.observe()).collect::<Vec<_>>();
  rr.reverse();
  let inner_skip = address.challenge();
  let inner_weights = lagrange_weights(&mut a, inner_skip);
  let w = inner_product(&mut a, &inner_weights, &z_partial);
  let original_weights = lagrange_weights(&mut a, z);
  let mut reported = a.constant(F128::ZERO);
  for (table, ((ty, slot), beta)) in shape
    .registry
    .boolean_types()
    .iter()
    .zip(shape.registry.slots())
    .zip(betas)
    .enumerate()
  {
    let inner = ty
      .k_log
      .checked_sub(6)
      .ok_or_else(|| anyhow::anyhow!("matrix skip dimension"))?;
    ensure!(
      inner <= x_inner.len() && inner <= rr.len(),
      "matrix point dimension"
    );
    let advice_a = a.input(Source::PrivateValue(2 * table as u64));
    let advice_b = a.input(Source::PrivateValue(2 * table as u64 + 1));
    let row_prefix = prefix_weight(&mut a, &x_inner[inner..], slot.prefix);
    let col_prefix = prefix_weight(&mut a, &rr[inner..], slot.prefix);
    let alpha_a = a.mul(alpha, advice_a);
    let pair = a.add(alpha_a, advice_b);
    let row_scaled = a.mul(row_prefix, pair);
    let term = a.mul(col_prefix, row_scaled);
    reported = a.add(reported, term);
    if let (Some(column), Some(beta)) = (ty.const_pin, beta) {
      let high = prefix_weight(&mut a, &rr[..inner], column >> 6);
      let weight = a.mul(z_partial[column & 63], high);
      let beta_weight = a.mul(beta, weight);
      let pin_term = a.mul(col_prefix, beta_weight);
      reported = a.add(reported, pin_term);
    }
    let matrix = F128StaticMatrixIdV1 {
      registry_digest: setup.identities().registry,
      table: table as u64,
      side: F128MatrixSideV1::A,
      variables: u32::try_from(ty.k_log)?,
    };
    let row = F128StructuredWeightV1 {
      low: original_weights.iter().map(|v| v.0).collect(),
      point: x_inner[..inner].iter().map(|v| v.0).collect(),
    };
    let column = F128StructuredWeightV1 {
      low: z_partial.iter().map(|v| v.0).collect(),
      point: rr[..inner].iter().map(|v| v.0).collect(),
    };
    a.trace.deferred_matrix_claims.extend([
      F128DeferredMatrixClaimV1 {
        phase: Phase::Lincheck,
        matrix,
        row: row.clone(),
        column: column.clone(),
        value: advice_a.0,
      },
      F128DeferredMatrixClaimV1 {
        phase: Phase::Lincheck,
        matrix: F128StaticMatrixIdV1 { side: F128MatrixSideV1::B, ..matrix },
        row,
        column,
        value: advice_b.0,
      },
    ]);
  }
  a.equal(reported, running);
  let frozen = union
    .m_total()
    .checked_sub(m)
    .ok_or_else(|| anyhow::anyhow!("Boolean region dimension"))?;
  let zero = a.constant(F128::ZERO);
  let mut ab_outer = vec![rr[0]];
  ab_outer.extend_from_slice(&x_outer);
  ab_outer.extend_from_slice(&rr[1..]);
  ab_outer.extend(std::iter::repeat_n(zero, frozen));
  let mut c_outer = r_rest;
  c_outer.extend(std::iter::repeat_n(zero, frozen));
  let pcs_claims = vec![
    F128MergedPcsBooleanClaimV1 {
      z_skip: inner_skip.0,
      skip_weights: inner_weights.iter().map(|v| v.0).collect(),
      x_outer: ab_outer.iter().map(|v| v.0).collect(),
      value: w.0,
    },
    F128MergedPcsBooleanClaimV1 {
      z_skip: z.0,
      skip_weights: original_weights.iter().map(|v| v.0).collect(),
      x_outer: c_outer.iter().map(|v| v.0).collect(),
      value: c_eval.0,
    },
  ];
  a.trace.validate(
    0,
    usize::try_from(address.observed)?,
    usize::try_from(address.challenges)?,
    2 * union.num_boolean(),
  )?;
  Ok(BooleanBlueprint { trace: a.trace, pcs_claims })
}

fn prefix_weight(a: &mut Algebra, point: &[Symbol], bits: usize) -> Symbol {
  let one = a.constant(F128::ONE);
  let mut weight = one;
  for (index, &coordinate) in point.iter().enumerate() {
    let factor = if (bits >> index) & 1 == 1 {
      coordinate
    } else {
      a.add(one, coordinate)
    };
    weight = a.mul(weight, factor);
  }
  weight
}

fn prefix_sum(
  a: &mut Algebra,
  point: &[Symbol],
  count: usize,
) -> Result<Symbol> {
  let capacity = 1usize
    .checked_shl(u32::try_from(point.len())?)
    .ok_or_else(|| anyhow::anyhow!("pin prefix capacity"))?;
  ensure!(count <= capacity, "pin prefix exceeds capacity");
  let one = a.constant(F128::ONE);
  if count == capacity {
    return Ok(one);
  }
  let mut result = a.constant(F128::ZERO);
  let mut high = one;
  for index in (0..point.len()).rev() {
    let zero_weight = a.add(one, point[index]);
    if (count >> index) & 1 == 1 {
      let term = a.mul(high, zero_weight);
      result = a.add(result, term);
      high = a.mul(high, point[index]);
    } else {
      high = a.mul(high, zero_weight);
    }
  }
  Ok(result)
}

fn coset_scale(
  a: &mut Algebra,
  nodes: &[F128],
  dimension: usize,
  point: Symbol,
) -> Symbol {
  let mut vanishing = a.constant(F128::ONE);
  for &node in nodes {
    let node = a.constant(node);
    let delta = a.add(point, node);
    vanishing = a.mul(vanishing, delta);
  }
  let denominator = a.constant(subspace_denominator_pair(dimension).1);
  a.mul(vanishing, denominator)
}

fn interpolate_lambda(
  a: &mut Algebra,
  values: &[Symbol],
  point: Symbol,
) -> Symbol {
  let nodes = &PHI_8_TABLE[64..128];
  let scale = coset_scale(a, nodes, 6, point);
  interpolate_scaled(a, nodes, values, point, scale)
}
fn interpolate_combined(
  a: &mut Algebra,
  values: &[Symbol],
  point: Symbol,
) -> Symbol {
  let nodes = &PHI_8_TABLE[..128];
  let scale = coset_scale(a, nodes, 7, point);
  interpolate_scaled(a, &nodes[64..], values, point, scale)
}
fn interpolate_scaled(
  a: &mut Algebra,
  nodes: &[F128],
  values: &[Symbol],
  point: Symbol,
  scale: Symbol,
) -> Symbol {
  let mut result = a.constant(F128::ZERO);
  for (&node, &value) in nodes.iter().zip(values) {
    let node = a.constant(node);
    let delta = a.add(point, node);
    let inverse = a.inv(delta);
    let weight = a.mul(scale, inverse);
    let term = a.mul(weight, value);
    result = a.add(result, term);
  }
  result
}
fn lagrange_weights(a: &mut Algebra, point: Symbol) -> Vec<Symbol> {
  let nodes = &PHI_8_TABLE[..64];
  let scale = coset_scale(a, nodes, 6, point);
  nodes
    .iter()
    .map(|&node| {
      let node = a.constant(node);
      let delta = a.add(point, node);
      let inverse = a.inv(delta);
      a.mul(scale, inverse)
    })
    .collect()
}
fn inner_product(a: &mut Algebra, left: &[Symbol], right: &[Symbol]) -> Symbol {
  let mut result = a.constant(F128::ZERO);
  for (&left, &right) in left.iter().zip(right) {
    let term = a.mul(left, right);
    result = a.add(result, term);
  }
  result
}
