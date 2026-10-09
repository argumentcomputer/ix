//! Fixed-profile ordinary KZG verification with publicly bound pairing inputs.
#[cfg(test)]
use crate::foreign::KzgCircuitExt;

use crate::kzg::KzgCommitment;
use crate::kzg::KzgConfig;
use crate::kzg::Scalar;
use crate::kzg::Srs;
use crate::recursive::native_curve::Affine;
use crate::recursive::native_curve::PointInput;
use crate::recursive::native_field::Builder;
use crate::recursive::native_field::FqGadget;
use crate::recursive::native_msm;
use crate::recursive::native_msm::Base;
use crate::recursive::native_transcript;
use crate::recursive::native_transcript::Transcript;
use ark_bls12_381::{Bls12_381, G1Affine, G2Affine};
use ark_ec::{CurveGroup, pairing::Pairing};
use ark_ff::Zero;
use ark_serialize::CanonicalSerialize;
use multi_stark::config::ProofConfig;
use multi_stark::expr::RowOffset;
use multi_stark::expr::Source;
use multi_stark::graph::Node;
use multi_stark::plonkish::Circuit;
use multi_stark::plonkish::Value;
use multi_stark::plonkish::gadgets::ByteGadgets;
use multi_stark::plonkish::gadgets::ByteValue;
use multi_stark::prover::Proof;
use multi_stark::system::System;
use multi_stark::traits::Algebra;
use multi_stark::traits::Field;
use multi_stark::traits::Pcs;
use multi_stark::traits::TwoAdicField;
use std::collections::BTreeMap;

type Commitment = (Vec<Vec<usize>>, Vec<Vec<usize>>);
type Openings = Vec<Vec<Vec<Value>>>;

pub struct Built {
  pub circuit: Circuit<Scalar>,
  pub inputs: Vec<(Value, Scalar)>,
  pub points: Vec<G1Affine>,
  pub pairing_outputs: Vec<Affine>,
  pub pairing_keys: Vec<G2Affine>,
  pub degree_output_count: usize,
  pub terms: Vec<Vec<(usize, Value)>>,
}
struct Context {
  b: Builder,
  f: FqGadget,
  bytes: ByteGadgets,
  inputs: Vec<(Value, Scalar)>,
  bases: Vec<Base>,
  points: Vec<G1Affine>,
  encodings: Vec<[ByteValue; 48]>,
  scalar_encodings: BTreeMap<usize, [ByteValue; 32]>,
}
impl Context {
  fn new() -> Self {
    let mut b = Builder::new();
    let f = FqGadget::new(&mut b);
    let bytes = ByteGadgets::new(&mut b);
    Self {
      b,
      f,
      bytes,
      inputs: vec![],
      bases: vec![],
      points: vec![],
      encodings: vec![],
      scalar_encodings: BTreeMap::new(),
    }
  }
  fn scalar(&mut self, name: &str, value: Scalar) -> Value {
    let v = self.b.input(name);
    self.inputs.push((v, value));
    v
  }
  fn point(&mut self, value: G1Affine, fixed: bool) -> usize {
    let id = self.points.len();
    let p = if fixed {
      let point = Affine {
        x: self.f.constant(&mut self.b, value.x),
        y: self.f.constant(
          &mut self.b,
          if value.infinity { ark_bls12_381::Fq::from(0u8) } else { value.y },
        ),
      };
      let flag = self.b.constant(Scalar::from_bool(value.infinity));
      let infinity = self.b.assert_bool(flag);
      PointInput { point, infinity }
    } else {
      let p = PointInput::new(&mut self.b, &self.f, &format!("point{id}"));
      self.inputs.extend(p.inputs(value));
      p
    };
    let encoded = if fixed {
      let mut encoded = vec![];
      value.serialize_compressed(&mut encoded).unwrap();
      std::array::from_fn(|i| self.bytes.constant(&mut self.b, encoded[i]))
    } else {
      native_transcript::point_bytes(&mut self.b, &self.bytes, p)
    };
    self.bases.push(Base::new(p, fixed.then_some(value)));
    self.points.push(value);
    self.encodings.push(encoded);
    if id % 64 == 63 {
      eprintln!("Allocated {} curve points: {:?}", id + 1, self.b.stats());
    }
    id
  }
  fn commitment(&mut self, c: &KzgCommitment, fixed: bool) -> Commitment {
    (
      c.0
        .iter()
        .map(|row| row.iter().map(|&p| self.point(p, fixed)).collect())
        .collect(),
      c.1
        .iter()
        .map(|row| row.iter().map(|&p| self.point(p, fixed)).collect())
        .collect(),
    )
  }
  fn openings(&mut self, name: &str, values: &[Vec<Vec<Scalar>>]) -> Openings {
    values
      .iter()
      .enumerate()
      .map(|(i, rows)| {
        rows
          .iter()
          .enumerate()
          .map(|(j, row)| {
            row
              .iter()
              .enumerate()
              .map(|(k, &v)| self.scalar(&format!("{name}.{i}.{j}.{k}"), v))
              .collect()
          })
          .collect()
      })
      .collect()
  }
  fn observe_scalar(&mut self, t: &mut Transcript, v: Value) {
    let bytes = *self.scalar_encodings.entry(v.index()).or_insert_with(|| {
      native_transcript::scalar_bytes(&mut self.b, &self.bytes, v)
    });
    t.observe(&bytes);
  }
  fn observe_constant(&mut self, t: &mut Transcript, v: usize) {
    let v = self.b.constant(Scalar::from_usize(v));
    self.observe_scalar(t, v);
  }
  fn observe_commitment(&mut self, t: &mut Transcript, c: &Commitment) {
    for rows in [&c.0, &c.1] {
      t.constant(&mut self.b, &self.bytes, &(rows.len() as u64).to_le_bytes());
      for row in rows {
        t.constant(&mut self.b, &self.bytes, &(row.len() as u64).to_le_bytes());
        for &id in row {
          t.observe(&self.encodings[id]);
        }
      }
    }
  }
  fn sample(&mut self, t: &mut Transcript) -> Value {
    t.sample(&mut self.b, &self.bytes)
  }
}
fn fp(
  b: &mut Builder,
  gamma: Value,
  args: impl DoubleEndedIterator<Item = Value>,
) -> Value {
  let mut acc = b.constant(Scalar::ZERO);
  for arg in args.rev() {
    acc = b.mul_add(acc, gamma, arg);
  }
  acc
}
fn combine(b: &mut Builder, terms: Vec<(usize, Value)>) -> Vec<(usize, Value)> {
  let mut unique = BTreeMap::<usize, Value>::new();
  for (id, v) in terms {
    if let Some(old) = unique.get_mut(&id) {
      *old = b.add(*old, v);
    } else {
      unique.insert(id, v);
    }
  }
  unique.into_iter().collect()
}

pub fn build(
  system: &System<KzgConfig>,
  srs: &Srs,
  proof: &Proof<KzgConfig>,
  claims: &[Vec<Scalar>],
  public_locations: &[(usize, usize)],
) -> Result<Built, String> {
  let quotients =
    system.verify_shape(proof).map_err(|e| format!("shape: {e:?}"))?;
  if !proof.active.iter().all(|&v| v)
    || system
      .preprocessed_indices
      .iter()
      .enumerate()
      .any(|(i, &s)| s != Some(i))
  {
    return Err(
      "wrapper requires every circuit active and one fixed matrix per circuit"
        .into(),
    );
  }
  let logs = &proof.log_degrees;
  let mut c = Context::new();
  let fixed = c.commitment(
    system.preprocessed_commit.as_ref().ok_or("missing fixed commitment")?,
    true,
  );
  let main = c.commitment(&proof.commitments.stage_1_trace, false);
  let stage2 = c.commitment(&proof.commitments.stage_2_trace, false);
  let quotient = c.commitment(&proof.commitments.quotient_chunks, false);
  let witnesses: Vec<_> =
    proof.opening_proof.0.iter().map(|&p| c.point(p, false)).collect();
  let generator = c.point(srs.g1[0], true);
  eprintln!("Curve inputs complete: {:?}", c.b.stats());
  let accs: Vec<_> = proof
    .intermediate_accumulators
    .iter()
    .enumerate()
    .map(|(i, &v)| c.scalar(&format!("acc{i}"), v))
    .collect();
  c.b.assert_zero(*accs.last().ok_or("empty accumulators")?);
  let main_open = c.openings("main", &proof.stage_1_opened_values);
  let stage2_open = c.openings("stage2", &proof.stage_2_opened_values);
  let quotient_open = c.openings("quotient", &proof.quotient_opened_values);
  let fixed_open = c.openings(
    "fixed",
    proof
      .preprocessed_opened_values
      .as_ref()
      .ok_or("missing fixed openings")?,
  );
  let mut claim_vars: Vec<Vec<_>> = claims
    .iter()
    .map(|row| row.iter().map(|&v| c.b.constant(v)).collect())
    .collect();
  for &(i, j) in public_locations {
    let v = c.scalar(&format!("claim.{i}.{j}"), claims[i][j]);
    c.f.range(&mut c.b, v, 64);
    c.b.expose_public(v);
    claim_vars[i][j] = v;
  }
  let mut seed = b"multi-stark/kzg/v3".to_vec();
  seed.extend((system.config.max_log_degree() as u64).to_le_bytes());
  seed.extend((system.config.pcs().max_quotient_degree() as u64).to_le_bytes());
  srs.g1[0].serialize_compressed(&mut seed).unwrap();
  srs.g2.serialize_compressed(&mut seed).unwrap();
  srs.g1[1].serialize_compressed(&mut seed).unwrap();
  srs.tau_g2.serialize_compressed(&mut seed).unwrap();
  let mut t = Transcript::new(&mut c.b, &c.bytes, &seed);
  c.observe_constant(&mut t, system.circuits.len());
  for circuit in &system.circuits {
    for v in [
      circuit.constraint_count(),
      circuit.max_constraint_degree(),
      circuit.preprocessed_height,
      circuit.preprocessed_width,
      circuit.main_width,
      circuit.stage_2_width,
      circuit.lookup_group_size,
    ] {
      c.observe_constant(&mut t, v);
    }
  }
  for _ in logs {
    c.observe_constant(&mut t, 1);
  }
  c.observe_commitment(&mut t, &fixed);
  c.observe_commitment(&mut t, &main);
  for &log in logs {
    c.observe_constant(&mut t, usize::from(log));
  }
  c.observe_constant(&mut t, claims.len());
  for row in &claim_vars {
    c.observe_constant(&mut t, row.len());
    for &v in row {
      c.observe_scalar(&mut t, v);
    }
  }
  let beta = c.sample(&mut t);
  c.observe_scalar(&mut t, beta);
  let gamma = c.sample(&mut t);
  c.observe_scalar(&mut t, gamma);
  let mut initial_acc = c.b.constant(Scalar::ZERO);
  for row in &claim_vars {
    let hash = fp(&mut c.b, gamma, row.iter().copied());
    let message = c.b.add(beta, hash);
    let inv = c.b.inverse(message);
    initial_acc = c.b.add(initial_acc, inv);
  }
  c.observe_commitment(&mut t, &stage2);
  for &v in &accs {
    c.observe_scalar(&mut t, v);
  }
  let alpha = c.sample(&mut t);
  c.observe_commitment(&mut t, &quotient);
  let zeta = c.sample(&mut t);
  c.b.inverse(zeta); // fixes distinct-point batch shape (all generators differ).
  let rounds = [
    (&main, &main_open),
    (&stage2, &stage2_open),
    (&quotient, &quotient_open),
    (&fixed, &fixed_open),
  ];
  for (commit, _) in rounds {
    c.observe_commitment(&mut t, commit);
    for &log in logs {
      t.constant(&mut c.b, &c.bytes, &u64::from(log).to_le_bytes());
    }
  }
  let degree_challenge = c.sample(&mut t);
  let mut degree_groups = BTreeMap::<u8, Vec<(usize, Value)>>::new();
  let mut shifted = vec![];
  let mut weight = c.b.constant(Scalar::ONE);
  for (commit, _) in rounds {
    for (i, &log) in logs.iter().enumerate() {
      if usize::from(log) < system.config.max_log_degree() {
        if commit.0[i].len() != commit.1[i].len() {
          return Err("shifted commitment width".into());
        }
        for (&p, &s) in commit.0[i].iter().zip(&commit.1[i]) {
          degree_groups.entry(log).or_default().push((p, weight));
          shifted.push((s, weight));
          weight = c.b.mul(weight, degree_challenge);
        }
      } else if !commit.1[i].is_empty() {
        return Err("unexpected shifted commitments".into());
      }
    }
  }
  let mut batches: Vec<(Scalar, Vec<usize>, Vec<Value>)> = vec![];
  for (commit, openings) in rounds {
    for (i, rows) in openings.iter().enumerate() {
      for (row_index, row) in rows.iter().enumerate() {
        for &v in row {
          c.observe_scalar(&mut t, v);
        }
        let g = if row_index == 0 {
          Scalar::ONE
        } else {
          Scalar::two_adic_generator(usize::from(logs[i]))
        };
        let index = if let Some(index) =
          batches.iter().position(|(key, _, _)| *key == g)
        {
          index
        } else {
          batches.push((g, vec![], vec![]));
          batches.len() - 1
        };
        batches[index].1.extend_from_slice(&commit.0[i]);
        batches[index].2.extend_from_slice(row);
      }
    }
  }
  if witnesses.len() != batches.len() {
    return Err("opening witness count".into());
  }
  let v = c.sample(&mut t);
  for &id in &witnesses {
    t.observe(&c.encodings[id]);
  }
  let r = c.sample(&mut t);
  eprintln!("Transcript complete: {:?}", c.b.stats());
  let mut lhs = vec![];
  let mut rhs = vec![];
  let mut r_power = c.b.constant(Scalar::ONE);
  for ((g, points, values), &witness) in batches.iter().zip(&witnesses) {
    let mut v_power = c.b.constant(Scalar::ONE);
    let mut y = c.b.constant(Scalar::ZERO);
    for (&id, &value) in points.iter().zip(values) {
      let coefficient = c.b.mul(v_power, r_power);
      lhs.push((id, coefficient));
      y = c.b.mul_add(v_power, value, y);
      v_power = c.b.mul(v_power, v);
    }
    let weighted_y = c.b.mul(y, r_power);
    let minus_y = c.b.scale(weighted_y, Scalar::NEG_ONE);
    lhs.push((generator, minus_y));
    let z = c.b.scale(zeta, *g);
    let coeff = c.b.mul(z, r_power);
    lhs.push((witness, coeff));
    rhs.push((witness, r_power));
    r_power = c.b.mul(r_power, r);
  }
  // All AIR roots and logUp constraints, in the native folding order.
  let mut acc = initial_acc;
  for (i, circuit) in system.circuits.iter().enumerate() {
    let one = c.b.constant(Scalar::ONE);
    let mut z_n = zeta;
    for _ in 0..logs[i] {
      z_n = c.b.mul(z_n, z_n);
    }
    let vanishing = c.b.sub(z_n, one);
    let inv_vanishing = c.b.inverse(vanishing);
    let g = Scalar::two_adic_generator(usize::from(logs[i]));
    let transition =
      c.b.affine([zeta, zeta], [Scalar::ONE, Scalar::ZERO], -g.inverse());
    let first_denom = c.b.sub(zeta, one);
    let inv_first = c.b.inverse(first_denom);
    let first = c.b.mul(vanishing, inv_first);
    let inv_last = c.b.inverse(transition);
    let last = c.b.mul(vanishing, inv_last);
    let publics = [beta, gamma, acc, accs[i]];
    let mut values = Vec::with_capacity(circuit.graph.nodes.len());
    for node in &circuit.graph.nodes {
      let value = match *node {
        Node::Const(v) => c.b.constant(v),
        Node::Var(col) => {
          let rows = match col.source {
            Source::Main => &main_open[i],
            Source::Preprocessed => &fixed_open[i],
            Source::Stage2 => &stage2_open[i],
          };
          rows[usize::from(col.offset == RowOffset::Next)][col.index as usize]
        },
        Node::Public(j) => publics[j as usize],
        Node::IsFirstRow => first,
        Node::IsLastRow => last,
        Node::IsTransition => transition,
        Node::Add(a, b) => c.b.add(values[a.index()], values[b.index()]),
        Node::Sub(a, b) => c.b.sub(values[a.index()], values[b.index()]),
        Node::Mul(a, b) => c.b.mul(values[a.index()], values[b.index()]),
        Node::Neg(a) => c.b.scale(values[a.index()], Scalar::NEG_ONE),
      };
      values.push(value);
    }
    let mut constraints: Vec<_> =
      circuit.graph.zeros.iter().map(|id| values[id.index()]).collect();
    let delta = c.b.sub(accs[i], acc);
    let delta =
      c.b.scale(delta, (Scalar::from_usize(1usize << logs[i]) * g).inverse());
    let injection = c.b.mul(last, delta);
    let groups: Vec<_> =
      circuit.graph.lookups.chunks(circuit.lookup_group_size.max(1)).collect();
    if groups.is_empty() {
      let difference = c.b.sub(stage2_open[i][1][0], stage2_open[i][0][0]);
      constraints.push(c.b.add(difference, injection));
    }
    for (j, group) in groups.iter().enumerate() {
      let target = if j + 1 < groups.len() {
        stage2_open[i][0][j + 1]
      } else {
        c.b.add(stage2_open[i][1][0], injection)
      };
      let difference = c.b.sub(target, stage2_open[i][0][j]);
      let messages: Vec<_> = group
        .iter()
        .map(|lookup| {
          let fingerprint = fp(
            &mut c.b,
            gamma,
            lookup.args.iter().map(|id| values[id.index()]),
          );
          c.b.add(beta, fingerprint)
        })
        .collect();
      let mut product = one;
      for &message in &messages {
        product = c.b.mul(product, message);
      }
      let mut numerator = c.b.constant(Scalar::ZERO);
      for (k, lookup) in group.iter().enumerate() {
        let mut term = values[lookup.multiplicity.index()];
        for (l, &message) in messages.iter().enumerate() {
          if k != l {
            term = c.b.mul(term, message);
          }
        }
        numerator = c.b.add(numerator, term);
      }
      let left = c.b.mul(product, difference);
      constraints.push(c.b.sub(left, numerator));
    }
    if constraints.len() != circuit.constraint_count() {
      return Err("constraint count mismatch".into());
    }
    let mut composition = c.b.constant(Scalar::ZERO);
    for value in constraints {
      composition = c.b.mul_add(composition, alpha, value);
    }
    let mut quotient = c.b.constant(Scalar::ZERO);
    if quotient_open[i][0].len() != quotients[i] {
      return Err("quotient width mismatch".into());
    }
    for &value in quotient_open[i][0].iter().rev() {
      quotient = c.b.mul_add(quotient, z_n, value);
    }
    let composition = c.b.mul(composition, inv_vanishing);
    c.b.assert_equal(composition, quotient);
    acc = accs[i];
  }
  eprintln!("AIR checks complete: {:?}", c.b.stats());
  let mut terms = vec![];
  let mut keys = vec![];
  if !shifted.is_empty() {
    terms.push(combine(&mut c.b, shifted));
    keys.push(srs.g2);
  }
  for (log, group) in degree_groups {
    let group = group
      .into_iter()
      .map(|(id, v)| (id, c.b.scale(v, Scalar::NEG_ONE)))
      .collect();
    terms.push(combine(&mut c.b, group));
    keys.push(srs.degree_keys[usize::from(log)]);
  }
  let degree_output_count = terms.len();
  terms.push(combine(&mut c.b, lhs));
  keys.push(srs.g2);
  let rhs = rhs
    .into_iter()
    .map(|(id, v)| (id, c.b.scale(v, Scalar::NEG_ONE)))
    .collect();
  terms.push(combine(&mut c.b, rhs));
  keys.push(srs.tau_g2);
  let mut outputs = vec![];
  for (i, terms) in terms.iter().enumerate() {
    eprintln!("MSM {i}/{}: {} bases", keys.len(), terms.len());
    let point = native_msm::msm(
      &mut c.b,
      &c.f,
      &c.bytes,
      &mut c.bases,
      terms,
      &format!("pairing{i}"),
    );
    // Canonicalize before exposing the compressed pairing input.
    let x = c.f.hint(&mut c.b, "output x", &[point.x], |v| Ok(v[0]));
    c.f.equal(&mut c.b, x, point.x);
    c.f.canonical(&mut c.b, x);
    let y = c.f.hint(&mut c.b, "output y", &[point.y], |v| Ok(v[0]));
    c.f.equal(&mut c.b, y, point.y);
    c.f.canonical(&mut c.b, y);
    let point = Affine { x, y };
    let zero = c.b.constant(Scalar::ZERO);
    let infinity = c.b.assert_bool(zero);
    let encoded = native_transcript::point_bytes(
      &mut c.b,
      &c.bytes,
      PointInput { point, infinity },
    );
    for chunk in encoded.as_chunks::<24>().0 {
      let mut coefficient = Scalar::ONE;
      let terms: Vec<_> = chunk
        .iter()
        .map(|v| {
          let term = (coefficient, v.value());
          coefficient *= Scalar::from_u16(256);
          term
        })
        .collect();
      let packed = c.b.linear_combination(&terms, Scalar::ZERO);
      c.b.expose_public(packed);
    }
    outputs.push(point);
    eprintln!("MSM {i} complete: {:?}", c.b.stats());
  }
  Ok(Built {
    circuit: c.b.finish(),
    inputs: c.inputs,
    points: c.points,
    pairing_outputs: outputs,
    pairing_keys: keys,
    degree_output_count,
    terms,
  })
}

impl Built {
  #[cfg(test)]
  pub fn check(&self) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
    self.check_and_assign().map(|(report, _)| report)
  }

  pub fn check_and_assign(
    &self,
  ) -> Result<
    (serde_json::Value, multi_stark::plonkish::Assignment<Scalar>),
    Box<dyn std::error::Error>,
  > {
    let mut w = self.circuit.witness();
    for &(v, n) in &self.inputs {
      w.set(v, n)?;
    }
    let start = std::time::Instant::now();
    let a = w.generate()?;
    eprintln!("Complete circuit witness checked: {:?}", start.elapsed());
    let mut outputs = vec![];
    for (point, terms) in self.pairing_outputs.iter().zip(&self.terms) {
      let x = crate::recursive::native_field::fq_value(
        &point.x.0.map(|v| a.value(v).unwrap()),
      );
      let y = crate::recursive::native_field::fq_value(
        &point.y.0.map(|v| a.value(v).unwrap()),
      );
      let point = G1Affine::new_unchecked(x, y);
      let expected = terms
        .iter()
        .map(|&(id, s)| self.points[id] * a.value(s).unwrap().0)
        .sum::<ark_bls12_381::G1Projective>()
        .into_affine();
      if point != expected {
        return Err("MSM differs from native computation".into());
      }
      outputs.push(point);
    }
    for range in
      [0..self.degree_output_count, self.degree_output_count..outputs.len()]
    {
      if !Bls12_381::multi_pairing(
        outputs[range.clone()].to_vec(),
        self.pairing_keys[range].to_vec(),
      )
      .is_zero()
      {
        return Err("external pairing check failed".into());
      }
    }
    let stats = self.circuit.stats();
    Ok((
      serde_json::json!({"gates":stats.gates,"lookups":stats.lookups,"values":stats.values,"rows":stats.gates+stats.lookups+stats.publics+1,"public_values":stats.publics,"pairing_points":outputs.len(),"msm_terms":self.terms.iter().map(Vec::len).collect::<Vec<_>>(),"witness_seconds":start.elapsed().as_secs_f64(),"circuit_satisfied":true,"external_pairings_pass":true,"outer_proof_generated":false}),
      a,
    ))
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::system::SystemWitness;
  use std::sync::Arc;
  #[test]
  fn complete_wrapper_fixture_and_changed_claim() {
    let mut b = Builder::new();
    let table =
      b.fixed_table("small", vec![vec![Scalar::ONE], vec![Scalar::TWO]]);
    let x = b.input("x");
    for _ in 0..30 {
      b.lookup(table, &[x]);
    }
    let square = b.mul(x, x);
    b.expose_public(square);
    let circuit = b.finish();
    let mut w = circuit.witness();
    w.set(x, Scalar::TWO).unwrap();
    let a = w.generate().unwrap();
    let lowered =
      circuit.lower_to_multi_stark_sharded(Scalar::from_u8(93), 32).unwrap();
    let claims = lowered.claims(a.public_values()).unwrap();
    let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
    let srs = Arc::new(Srs::unsafe_dev_setup(32, b"native-wrapper-test"));
    let (system, key) = System::new(
      KzgConfig::new(srs.clone(), 2),
      lowered.kzg_circuit_inputs(32, 2).unwrap(),
    );
    let proof = system.prove_multiple_claims(
      &key,
      &refs,
      SystemWitness::from_stage_1(lowered.traces(&a).unwrap(), &system),
    );
    system.verify_multiple_claims(&refs, &proof).unwrap();
    let mut built = build(&system, &srs, &proof, &claims, &[(1, 3)]).unwrap();
    eprintln!("{}", built.check().unwrap());
    let public = built.circuit.public_values()[0];
    let slot = built.inputs.iter().position(|&(v, _)| v == public).unwrap();
    built.inputs[slot].1 += Scalar::ONE;
    assert!(built.check().is_err());
    built.inputs[slot].1 -= Scalar::ONE;
    let slot = built.inputs.len() - 2;
    built.inputs[slot].1 += Scalar::ONE;
    assert!(built.check().is_err());
  }
}
