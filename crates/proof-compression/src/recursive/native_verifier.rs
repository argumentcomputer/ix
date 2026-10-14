//! Fixed-profile ordinary KZG verification with publicly bound pairing inputs.
use crate::{
  kzg::{KzgCommitment, KzgConfig, Scalar},
  recursive::{
    native_curve::{Affine, PointInput},
    native_field::{Builder, FqGadget},
    native_msm::{self, Base},
    native_transcript::{self, Transcript},
  },
};
use ark_bls12_381::{Bls12_381, G1Affine, G2Affine};
use ark_ec::{CurveGroup, pairing::Pairing};
use ark_ff::Zero;
use ark_serialize::CanonicalSerialize;
use multi_stark::{
  config::ProofConfig,
  expr::{RowOffset, Source},
  graph::Node,
  plonkish::{
    Circuit, CircuitStats, Value,
    gadgets::{ByteGadgets, ByteValue},
  },
  prover::Proof,
  system::System,
  traits::{Algebra, Field, TwoAdicField},
};
use std::collections::BTreeMap;

mod bindings;
#[cfg(test)]
mod parallel_prefix_tests;
mod plan;
#[cfg(test)]
mod reuse_tests;
mod shape;

pub(crate) use bindings::{Bindings, Compiled};
use bindings::{PointBinding, PointSource, ScalarSource};
pub(crate) use plan::{ClaimSchema, ClaimSlot, LayoutPolicy, Plan};
use shape::{MatrixShape, Round, Shape};

type Commitment = Vec<Vec<usize>>;
type Openings = Vec<Vec<Vec<Value>>>;

/// A compiled circuit paired with one request's assignments and proof points.
pub struct Built {
  pub circuit: Circuit<Scalar>,
  pub inputs: Vec<(Value, Scalar)>,
  pub points: Vec<G1Affine>,
  pub pairing_outputs: Vec<PointInput>,
  pub pairing_keys: Vec<G2Affine>,
  pub terms: Vec<Vec<(usize, Value)>>,
}

#[derive(Clone, Copy)]
pub struct Profile<'a> {
  pub circuits: &'a [multi_stark::system::Circuit<Scalar>],
  pub fixed: &'a KzgCommitment,
  pub transcript_seed: &'a [u8],
  pub generator: G1Affine,
  pub g2: G2Affine,
  pub tau_g2: G2Affine,
  pub max_log_degree: usize,
}

pub struct Counts {
  pub stats: CircuitStats,
  pub table_dimensions: Vec<(usize, usize)>,
  pub msm_terms: Vec<usize>,
}

struct Construction {
  context: Context,
  pairing_outputs: Vec<PointInput>,
  pairing_keys: Vec<G2Affine>,
  terms: Vec<Vec<(usize, Value)>>,
}

impl Construction {
  fn finish(self, plan: &Plan<'_>) -> Compiled {
    #[cfg(test)]
    let stats = self.context.b.stats();
    Compiled {
      circuit: self.context.b.finish(),
      bindings: Bindings {
        identity: plan.identity,
        shape: plan.shape.clone(),
        claims: plan.claims.clone(),
        scalars: self.context.inputs,
        points: self.context.points,
        pairing_outputs: self.pairing_outputs,
        pairing_keys: self.pairing_keys,
        terms: self.terms,
        #[cfg(test)]
        stats,
      },
    }
  }

  fn counts(&self) -> Counts {
    Counts {
      stats: self.context.b.stats(),
      table_dimensions: self.context.b.table_dimensions().collect(),
      msm_terms: self.terms.iter().map(Vec::len).collect(),
    }
  }
}

struct Context {
  b: Builder,
  f: FqGadget,
  bytes: ByteGadgets,
  inputs: Vec<(Value, ScalarSource)>,
  bases: Vec<Base>,
  points: Vec<PointBinding>,
  point_ends: Vec<usize>,
  encodings: Vec<[ByteValue; 48]>,
  scalar_encodings: BTreeMap<usize, [ByteValue; 32]>,
}
impl Context {
  fn new(mut b: Builder) -> Self {
    let f = FqGadget::new(&mut b);
    let bytes = ByteGadgets::new(&mut b);
    Self {
      b,
      f,
      bytes,
      inputs: vec![],
      bases: vec![],
      points: vec![],
      point_ends: vec![],
      encodings: vec![],
      scalar_encodings: BTreeMap::new(),
    }
  }
  fn scalar(&mut self, name: &str, source: ScalarSource) -> Value {
    let v = self.b.input(name);
    self.inputs.push((v, source));
    v
  }
  fn point(&mut self, source: PointSource) -> usize {
    let id = self.points.len();
    let source = match source {
      PointSource::Fixed(value) if value.infinity => {
        PointSource::Fixed(G1Affine::identity())
      },
      other => other,
    };
    let fixed =
      if let PointSource::Fixed(value) = source { Some(value) } else { None };
    let p = if let Some(value) = fixed {
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
      PointInput::new(&mut self.b, &self.f, &format!("point{id}"))
    };
    let encoded = if let Some(value) = fixed {
      let mut encoded = vec![];
      value.serialize_compressed(&mut encoded).unwrap();
      std::array::from_fn(|i| self.bytes.constant(&mut self.b, encoded[i]))
    } else {
      native_transcript::point_bytes(&mut self.b, &self.bytes, p)
    };
    self.bases.push(Base::new(p, fixed));
    self.points.push(PointBinding { source, point: p });
    self.encodings.push(encoded);
    let end = self.b.stats().values;
    if self.point_ends.last() != Some(&end) {
      self.point_ends.push(end);
    }
    if id % 64 == 63 {
      eprintln!("Allocated {} curve points: {:?}", id + 1, self.b.stats());
    }
    id
  }
  fn seal_point_prefix(&mut self) -> bool {
    self.b.try_parallel_witness_prefix(std::mem::take(&mut self.point_ends))
  }
  fn fixed_commitment(&mut self, c: &KzgCommitment) -> Commitment {
    c.0
      .iter()
      .map(|row| {
        row.iter().map(|&p| self.point(PointSource::Fixed(p))).collect()
      })
      .collect()
  }
  fn commitment(&mut self, round: Round, shape: &MatrixShape) -> Commitment {
    shape
      .widths
      .iter()
      .enumerate()
      .map(|(matrix, &width)| {
        (0..width)
          .map(|column| {
            self.point(PointSource::Commitment { round, matrix, column })
          })
          .collect()
      })
      .collect()
  }
  fn openings(
    &mut self,
    name: &str,
    round: Round,
    shape: &MatrixShape,
  ) -> Openings {
    shape
      .widths
      .iter()
      .zip(&shape.opening_rows)
      .enumerate()
      .map(|(matrix, (&width, &rows))| {
        (0..rows)
          .map(|row| {
            (0..width)
              .map(|column| {
                self.scalar(
                  &format!("{name}.{matrix}.{row}.{column}"),
                  ScalarSource::Opening { round, matrix, row, column },
                )
              })
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
    t.constant(&mut self.b, &self.bytes, &(c.len() as u64).to_le_bytes());
    for row in c {
      t.constant(&mut self.b, &self.bytes, &(row.len() as u64).to_le_bytes());
      for &id in row {
        t.observe(&self.encodings[id]);
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

#[cfg(test)]
pub fn build(
  system: &System<KzgConfig>,
  srs: &crate::kzg::Srs,
  proof: &Proof<KzgConfig>,
  claims: &[Vec<Scalar>],
  public_locations: &[(usize, usize)],
) -> Result<Built, String> {
  let configured = system.config.pcs().verifier_params();
  if srs.g1.get(..2) != Some(configured.g1.as_slice())
    || srs.g2 != configured.g2
    || srs.tau_g2 != configured.tau_g2
  {
    return Err(
      "wrapper SRS differs from the authenticated configuration".into(),
    );
  }
  let plan = Plan::new(
    system,
    &proof.log_degrees,
    ClaimSchema::from_claims(claims, public_locations)?,
    LayoutPolicy::legacy(),
  )?;
  plan.build(proof, claims)
}

/// Count the ordinary wrapper constraints without retaining an IR or generating
/// a witness. This measures a profile; it does not verify its proof or its SRS.
pub fn count(
  profile: &Profile<'_>,
  proof: &Proof<KzgConfig>,
  claims: &[Vec<Scalar>],
  public_locations: &[(usize, usize)],
) -> Result<Counts, String> {
  let plan = Plan::from_profile(
    profile,
    &proof.log_degrees,
    ClaimSchema::from_claims(claims, public_locations)?,
    LayoutPolicy::legacy(),
  )?;
  plan.validate_request(proof, claims)?;
  plan.count()
}

fn construct(
  profile: &Profile<'_>,
  shape: &Shape,
  claims: &ClaimSchema,
  builder: Builder,
) -> Result<Construction, String> {
  let circuits = profile.circuits;
  let quotients: Vec<_> =
    circuits.iter().map(|c| c.quotient_degree()).collect();
  let logs = &shape.logs;
  let mut c = Context::new(builder);
  let fixed = c.fixed_commitment(profile.fixed);
  let main = c.commitment(Round::Main, &shape.rounds[Round::Main.index()]);
  let stage2 =
    c.commitment(Round::Stage2, &shape.rounds[Round::Stage2.index()]);
  let quotient =
    c.commitment(Round::Quotient, &shape.rounds[Round::Quotient.index()]);
  let witnesses: Vec<_> = (0..shape.opening_generators.len())
    .map(|index| c.point(PointSource::Witness(index)))
    .collect();
  let generator = c.point(PointSource::Fixed(profile.generator));
  let prefix_blocks = c.point_ends.len();
  let prefix_values = c.b.stats().values;
  let parallel_prefix = c.seal_point_prefix();
  eprintln!("Curve inputs complete: {:?}", c.b.stats());
  eprintln!(
    "Point witness prefix: admitted={parallel_prefix}, blocks={prefix_blocks}, values={prefix_values}"
  );
  let accs: Vec<_> = (0..logs.len())
    .map(|i| c.scalar(&format!("acc{i}"), ScalarSource::Accumulator(i)))
    .collect();
  c.b.assert_zero(*accs.last().ok_or("empty accumulators")?);
  let main_open =
    c.openings("main", Round::Main, &shape.rounds[Round::Main.index()]);
  let stage2_open =
    c.openings("stage2", Round::Stage2, &shape.rounds[Round::Stage2.index()]);
  let quotient_open = c.openings(
    "quotient",
    Round::Quotient,
    &shape.rounds[Round::Quotient.index()],
  );
  let fixed_open =
    c.openings("fixed", Round::Fixed, &shape.rounds[Round::Fixed.index()]);
  let mut claim_vars: Vec<Vec<_>> = claims
    .rows
    .iter()
    .map(|row| {
      row
        .iter()
        .map(|slot| match slot {
          ClaimSlot::Constant(value) => Some(c.b.constant(*value)),
          ClaimSlot::PublicU64 => None,
        })
        .collect()
    })
    .collect();
  for &(i, j) in &claims.public_locations {
    let v = c.scalar(
      &format!("claim.{i}.{j}"),
      ScalarSource::Claim { row: i, column: j },
    );
    c.f.range(&mut c.b, v, 64);
    c.b.expose_public(v);
    claim_vars[i][j] = Some(v);
  }
  let claim_vars: Vec<Vec<_>> = claim_vars
    .into_iter()
    .map(|row| {
      row
        .into_iter()
        .map(|value| value.expect("validated public claim schema"))
        .collect()
    })
    .collect();
  let mut t = Transcript::new(&mut c.b, &c.bytes, profile.transcript_seed);
  c.observe_constant(&mut t, circuits.len());
  for circuit in circuits {
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
  c.observe_constant(&mut t, claims.rows.len());
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
        batches[index].1.extend_from_slice(&commit[i]);
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
  for (i, circuit) in circuits.iter().enumerate() {
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
  terms.push(combine(&mut c.b, lhs));
  keys.push(profile.g2);
  let rhs = rhs
    .into_iter()
    .map(|(id, v)| (id, c.b.scale(v, Scalar::NEG_ONE)))
    .collect();
  terms.push(combine(&mut c.b, rhs));
  keys.push(profile.tau_g2);
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
    let point = point.canonical(&mut c.b, &c.f);
    let encoded = native_transcript::point_bytes(&mut c.b, &c.bytes, point);
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
  Ok(Construction {
    context: c,
    pairing_outputs: outputs,
    pairing_keys: keys,
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
    bindings::check_outputs(
      &a,
      &self.points,
      &self.pairing_outputs,
      &self.pairing_keys,
      &self.terms,
    )?;
    Ok((
      bindings::report(
        self.circuit.stats(),
        &self.terms,
        start.elapsed().as_secs_f64(),
      ),
      a,
    ))
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{foreign::KzgCircuitExt, kzg::Srs};
  use multi_stark::system::SystemWitness;
  use std::sync::Arc;

  #[test]
  fn complete_wrapper_fixture_and_changed_claim() {
    wrapper_fixture(false);
  }

  #[test]
  fn public_degree_wrapper_fixture_and_changed_claim() {
    wrapper_fixture(true);
  }

  #[test]
  fn constant_column_proof_has_canonical_identity_pairing_outputs() {
    use multi_stark::{expr::Expr, system::CircuitInputs};
    use p3_matrix::dense::RowMajorMatrix;
    let srs = Arc::new(Srs::unsafe_dev_setup_prefix(
      4,
      6,
      b"identity-wrapper-public-test",
    ));
    let trace = RowMajorMatrix::new_col(vec![Scalar::from_u8(7); 4]);
    let (system, key) = System::new(
      KzgConfig::new(srs.clone(), 2),
      [CircuitInputs {
        main_width: 1,
        preprocessed: Some(trace.clone()),
        constraints: vec![Expr::main(0) - Expr::preprocessed(0)],
        ..Default::default()
      }],
    );
    let proof = system.prove_multiple_claims(
      &key,
      &[],
      SystemWitness::from_stage_1(vec![trace], &system),
    );
    system.verify_multiple_claims(&[], &proof).unwrap();
    assert!(proof.opening_proof.0.iter().all(|p| p.infinity));
    let built = build(&system, &srs, &proof, &[], &[]).unwrap();
    let (_, assignment) = built.check_and_assign().unwrap();
    for point in &built.pairing_outputs {
      assert_eq!(
        assignment.value(point.infinity.value()).unwrap(),
        Scalar::ONE
      );
      assert!(
        point
          .point
          .x
          .0
          .into_iter()
          .chain(point.point.y.0)
          .all(|v| assignment.value(v).unwrap() == Scalar::ZERO)
      );
    }
    assert_eq!(
      assignment.public_values(),
      [
        Scalar::from_u8(0xc0),
        Scalar::ZERO,
        Scalar::from_u8(0xc0),
        Scalar::ZERO
      ]
    );
  }

  fn wrapper_fixture(public_degree: bool) {
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
    let srs = if public_degree {
      Srs::unsafe_dev_setup_prefix(32, 62, b"native-wrapper-public-test")
    } else {
      Srs::unsafe_dev_setup(32, b"native-wrapper-test")
    };
    let srs = Arc::new(srs);
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
    let profile = Profile {
      circuits: &system.circuits,
      fixed: system.preprocessed_commit.as_ref().unwrap(),
      transcript_seed: system.config.transcript_seed(),
      generator: srs.g1[0],
      g2: srs.g2,
      tau_g2: srs.tau_g2,
      max_log_degree: system.config.max_log_degree(),
    };
    let counted = count(&profile, &proof, &claims, &[(1, 3)]).unwrap();
    let encoded =
      crate::kzg::compact::FixedProofCodec::new(&system, &proof.log_degrees)
        .unwrap()
        .encode(&proof)
        .unwrap();
    assert_eq!(
      Shape::new(&profile, &proof.log_degrees)
        .unwrap()
        .checked_compact_len()
        .unwrap(),
      encoded.len()
    );
    assert_eq!(counted.stats, built.circuit.stats());
    assert_eq!(
      counted.table_dimensions,
      built
        .circuit
        .tables()
        .iter()
        .map(|table| (table.rows().len(), table.width()))
        .collect::<Vec<_>>()
    );
    assert_eq!(
      counted.msm_terms,
      built.terms.iter().map(Vec::len).collect::<Vec<_>>()
    );
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
