//! Exact symbolic Product-GKR DAG. No proof, guest, witness values, or native
//! verifier invocation is an input to this compiler.

use anyhow::{Result, ensure};
use flock_prover::{
  circuit::SigmaAssertion, field::F128, matrix_fold::FoldMatrix,
  union::UnionInstance,
};
use ix_stage4_trace::{
  F128InputSourceV1 as Source, F128ReferenceV1 as Reference,
  F128VerifierPhaseV1 as Phase, F128WiringTraceV1,
};
use ixby_flock::ixby::{exec::CompiledExec, io::PublicWord};

use super::algebra::{Addresses, Algebra, Symbol, encode};

pub(crate) fn compile_wiring(
  setup: &CompiledExec,
) -> Result<F128WiringTraceV1> {
  let shape = setup.verifier_shape();
  let circuit = &shape.circuit;
  let cells = circuit.cells();
  let (nu, mu) = (cells.nu(), cells.mu());
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  ensure!(
    !union.has_element() && union.num_boolean() != 0,
    "Boolean Exec blueprint required"
  );
  // Flock's one-sided fork samples two parent seed words, then observes them
  // as the child's first two words. Payload observations do not occupy F128
  // value addresses. Grinding nonces likewise occupy only the byte tape.
  let mut addresses = Addresses { observed: 2, challenges: 2 };
  let mut a = Algebra::new(Phase::Wiring);
  let one = a.constant(F128::ONE);
  let zero = a.constant(F128::ZERO);
  let alpha = addresses.challenge();
  let beta = addresses.challenge();
  let top_lhs = addresses.observe();
  let top_rhs = addresses.observe();
  a.equal(top_lhs, top_rhs);
  let (mut claim_l, mut claim_r) = (top_lhs, top_rhs);
  let mut point: Vec<Symbol> = Vec::new();
  for layer in 0..mu {
    let lambda = addresses.challenge();
    let lambda_claim = a.mul(lambda, claim_r);
    let mut running = a.add(claim_l, lambda_claim);
    let mut next = Vec::with_capacity(layer + 1);
    for &r_eq in &point {
      let g_one = addresses.observe();
      let g_inf = addresses.observe();
      let one_plus_r_eq = a.add(one, r_eq);
      let r_eq_g_one = a.mul(r_eq, g_one);
      let numerator = a.add(running, r_eq_g_one);
      let inverse = a.inv(one_plus_r_eq);
      let g_zero = a.mul(numerator, inverse);
      let rho = addresses.challenge();
      let one_plus_rho = a.add(one, rho);
      let zero_term = a.mul(g_zero, one_plus_rho);
      let one_term = a.mul(g_one, rho);
      let infinity_rho = a.mul(g_inf, rho);
      let infinity_term = a.mul(infinity_rho, one_plus_rho);
      let finite = a.add(zero_term, one_term);
      running = a.add(finite, infinity_term);
      next.push(rho);
    }
    let vl0 = addresses.observe();
    let vl1 = addresses.observe();
    let vr0 = addresses.observe();
    let vr1 = addresses.observe();
    let left = a.mul(vl0, vl1);
    let right = a.mul(vr0, vr1);
    let batched = a.mul(lambda, right);
    let gate = a.add(left, batched);
    a.equal(running, gate);
    let close = addresses.challenge();
    let one_plus_close = a.add(one, close);
    let left_zero = a.mul(one_plus_close, vl0);
    let left_one = a.mul(close, vl1);
    claim_l = a.add(left_zero, left_one);
    let right_zero = a.mul(one_plus_close, vr0);
    let right_one = a.mul(close, vr1);
    claim_r = a.add(right_zero, right_one);
    next.push(close);
    point = next;
  }
  ensure!(point.len() == mu, "symbolic Product-GKR endpoint");
  let f_eval = addresses.observe();
  let g_eval = addresses.observe();
  let sigma = addresses.observe();
  let closing = [addresses.challenge(), addresses.challenge()];
  let masked_id = a.input(Source::PrivateValue(0));
  let live = a.input(Source::PrivateValue(1));
  let beta_plus_one = a.add(beta, one);
  let live_tail = a.mul(beta_plus_one, live);
  let tail = a.add(live_tail, one);
  let alpha_masked = a.mul(alpha, masked_id);
  let lhs_no_tail = a.add(f_eval, alpha_masked);
  let lhs = a.add(lhs_no_tail, tail);
  a.equal(claim_l, lhs);
  let alpha_sigma = a.mul(alpha, sigma);
  let rhs_no_tail = a.add(g_eval, alpha_sigma);
  let rhs = a.add(rhs_no_tail, tail);
  a.equal(claim_r, rhs);

  // The parent Boolean PIOP observes 2*64 skipped-row values, two scalars per
  // multilinear round, two endpoints, two per lincheck round, and 64 skipped
  // column values. Fork merge then observes two digest words. The merged PCS
  // observes two 128-element ring-switch slices before the gather messages.
  let zero_rounds = union
    .m_bool()
    .checked_sub(6)
    .ok_or_else(|| anyhow::anyhow!("zerocheck blueprint dimension"))?;
  let linear_rounds = union
    .m_bool()
    .checked_sub(nu + 6)
    .ok_or_else(|| anyhow::anyhow!("lincheck blueprint dimension"))?;
  let boolean_observed = 128 + 2 * zero_rounds + 2 + 2 * linear_rounds + 64;
  let gather_start =
    addresses.observed + u64::try_from(boolean_observed + 2 + 256)?;
  let gather_observations = (0..cells.num_gate_slots())
    .map(|index| gather_start + index as u64)
    .collect::<Vec<_>>();
  let gather = gather_observations
    .iter()
    .map(|&index| a.input(Source::ObservedValue(index)))
    .collect::<Vec<_>>();
  let slot_weights = eq_table(&mut a, &point[nu..]);
  let mut recombined = zero;
  for (weight, value) in slot_weights.iter().copied().zip(gather) {
    let term = a.mul(weight, value);
    recombined = a.add(recombined, term);
  }
  let rows = 1usize
    .checked_shl(u32::try_from(nu)?)
    .ok_or_else(|| anyhow::anyhow!("row capacity overflow"))?;
  let public = setup.public_template().words();
  let row_weights =
    partial_eq_table(&mut a, &point[..nu], public.len().min(rows))?;
  for index in 0..public.len() {
    let slot = cells.num_gate_slots() + index / rows;
    let row = index % rows;
    let cell_weight = a.mul(slot_weights[slot], row_weights[row]);
    let value = a.input(Source::PublicValue(index as u64));
    let term = a.mul(cell_weight, value);
    recombined = a.add(recombined, term);
  }
  a.equal(recombined, f_eval);
  a.equal(f_eval, g_eval);
  let fixed_public_values = public
    .iter()
    .map(|word| match word {
      PublicWord::Fixed(value) => Some(encode(*value)),
      PublicWord::Output(_) => None,
    })
    .collect();
  let zero_row = vec![F128::ZERO; nu];
  let mut gather_high_bits = Vec::with_capacity(cells.num_gate_slots());
  let mut packed = None;
  for gate in 0..cells.num_gate_slots() {
    let coords = cells.gate_claim_point(gate, &zero_row);
    packed.get_or_insert(coords.len());
    ensure!(
      coords.len() >= nu && packed == Some(coords.len()),
      "gather point dimensions"
    );
    gather_high_bits.push(
      coords[nu..]
        .iter()
        .map(|value| {
          ensure!(
            *value == F128::ZERO || *value == F128::ONE,
            "fixed gather coordinate"
          );
          Ok(*value == F128::ONE)
        })
        .collect::<Result<Vec<_>>>()?,
    );
  }
  let matrix = SigmaAssertion::matrix(circuit);
  let structure_base = matrix
    .n_cols()
    .checked_ilog2()
    .and_then(|n| n.checked_sub(3))
    .ok_or_else(|| anyhow::anyhow!("structure matrix dimensions"))?;
  let trace = F128WiringTraceV1 {
    circuit_digest: circuit.digest(),
    public_value_count: public.len() as u64,
    row_variables: u32::try_from(nu)?,
    cell_variables: u32::try_from(mu)?,
    packed_claim_variables: u32::try_from(packed.unwrap_or(nu))?,
    structure_base_variables: structure_base,
    fixed_public_values,
    rho_challenges: point
      .iter()
      .map(|s| challenge_index(*s))
      .collect::<Result<Vec<_>>>()?,
    closing_digest_challenges: [
      challenge_index(closing[0])?,
      challenge_index(closing[1])?,
    ],
    masked_id_private_value: 0,
    live_private_value: 1,
    sigma_eval_observation: match sigma.0 {
      Reference::Input(Source::ObservedValue(index)) => index,
      _ => unreachable!(),
    },
    gather_observations,
    gather_high_bits,
    algebra: a.trace,
  };
  trace.validate(
    public.len(),
    usize::try_from(gather_start)? + cells.num_gate_slots(),
    usize::try_from(addresses.challenges)?,
    2,
  )?;
  Ok(trace)
}

fn challenge_index(symbol: Symbol) -> Result<u64> {
  match symbol.0 {
    Reference::Input(Source::Challenge(index)) => Ok(index),
    _ => anyhow::bail!("non-challenge symbolic coordinate"),
  }
}

fn eq_table(a: &mut Algebra, point: &[Symbol]) -> Vec<Symbol> {
  let one = a.constant(F128::ONE);
  let mut table = vec![one];
  for &coordinate in point {
    let one_plus = a.add(one, coordinate);
    let mut next = Vec::with_capacity(2 * table.len());
    for &value in &table {
      next.push(a.mul(value, one_plus));
    }
    for &value in &table {
      next.push(a.mul(value, coordinate));
    }
    table = next;
  }
  table
}

fn partial_eq_table(
  a: &mut Algebra,
  point: &[Symbol],
  count: usize,
) -> Result<Vec<Symbol>> {
  // Keep operation ordering identical to the native export; fixed count, not
  // witness values, selects this bounded partial expansion.
  if count == 0 {
    return Ok(Vec::new());
  }
  ensure!(
    count <= 1usize.checked_shl(u32::try_from(point.len())?).unwrap_or(0),
    "partial eq capacity"
  );
  let low_variables =
    if count <= 1 { 0 } else { usize::try_from((count - 1).ilog2())? + 1 };
  let mut table = eq_table(a, &point[..low_variables]);
  table.truncate(count);
  let one = a.constant(F128::ONE);
  let mut high_zero = one;
  for &coordinate in &point[low_variables..] {
    let factor = a.add(one, coordinate);
    high_zero = a.mul(high_zero, factor);
  }
  if low_variables != point.len() {
    for value in &mut table {
      *value = a.mul(*value, high_zero);
    }
  }
  Ok(table)
}
