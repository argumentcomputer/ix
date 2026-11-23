//! Shared verifier layouts, graph validation and native differential vectors.
use super::*;
use crate::kzg::{
  curve::{Bn254, G1AffineOf, G1ProjectiveOf, KzgCurve},
  field::CurveScalar,
};
use ark_ec::CurveGroup;
use ark_ff::{BigInteger, PrimeField, Zero};
use multi_stark::{
  config::ProofConfig,
  eval::VarValues,
  expr::{RowOffset, Source},
  graph::{ConstraintGraph, Node},
  prover::{Proof, observe_claims, sample_lookup_challenges},
  system::System,
  traits::{Algebra, EvaluationDomain, Pcs, Transcript},
};
use serde_json::{Value as Json, json};
use std::fmt::Write as _;
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
pub(super) mod codegen;
pub(super) fn hex(bytes: &[u8]) -> String {
  let mut out = String::with_capacity(bytes.len() * 2);
  for byte in bytes {
    write!(&mut out, "{byte:02x}").unwrap();
  }
  out
}

pub(super) fn hex_json(bytes: &[u8]) -> String {
  format!("0x{}", hex(bytes))
}

pub(super) fn scalar<C: KzgCurve>(value: CurveScalar<C>) -> String {
  hex_json(&value.0.into_bigint().to_bytes_be())
}

pub(super) fn fq<C: KzgCurve>(value: C::Fq) -> Vec<u8> {
  value.into_bigint().to_bytes_be()
}

pub(super) fn g1<C: KzgCurve>(point: G1AffineOf<C>) -> Vec<u8> {
  C::encode_g1_evm(point)
}

pub(super) fn proof_points<C: KzgCurve>(
  proof: &Proof<KzgConfig<C>>,
) -> Vec<G1AffineOf<C>> {
  [
    &proof.commitments.stage_1_trace,
    &proof.commitments.stage_2_trace,
    &proof.commitments.quotient_chunks,
  ]
  .into_iter()
  .flat_map(|c| c.0.iter().flatten().copied())
  .chain(proof.opening_proof.0.iter().copied())
  .collect()
}

#[derive(Clone, Copy)]
pub(super) struct GraphMatrix {
  pub(super) index: usize,
  pub(super) width: usize,
  pub(super) rows: usize,
}

/// Opening windows indexed by the graph's three variable sources.
#[derive(Clone, Copy)]
pub(super) struct GraphInputs {
  pub(super) main: GraphMatrix,
  pub(super) preprocessed: GraphMatrix,
  pub(super) stage2: GraphMatrix,
  pub(super) public_count: usize,
  pub(super) matrix_count: usize,
}

impl GraphInputs {
  pub(super) fn for_circuit<C: KzgCurve>(
    system: &System<KzgConfig<C>>,
    index: usize,
  ) -> Result<Self> {
    let count = system.circuits.len();
    let c = system.circuits.get(index).ok_or("missing circuit")?;
    Ok(Self {
      main: GraphMatrix {
        index,
        width: c.main_width,
        rows: 1 + usize::from(system.opens_next_row(index, Source::Main)),
      },
      preprocessed: GraphMatrix {
        index: 3 * count + index,
        width: c.preprocessed_width,
        rows: 1
          + usize::from(system.opens_next_row(index, Source::Preprocessed)),
      },
      stage2: GraphMatrix {
        index: count + index,
        width: c.stage_2_width,
        rows: 2,
      },
      public_count: c.num_publics,
      matrix_count: 4 * count,
    })
  }

  pub(super) fn matrix(self, source: Source) -> GraphMatrix {
    match source {
      Source::Main => self.main,
      Source::Preprocessed => self.preprocessed,
      Source::Stage2 => self.stage2,
    }
  }
}

/// Validated arithmetic with variable references resolved into opening windows.
#[derive(Clone, Copy)]
pub(super) enum GraphInstruction<C: KzgCurve = Bn254> {
  Constant(CurveScalar<C>),
  Opening { matrix: usize, offset: usize },
  Public(usize),
  First,
  Last,
  Transition,
  Add(usize, usize),
  Sub(usize, usize),
  Mul(usize, usize),
  Neg(usize),
}

pub(super) struct GraphProgram<C: KzgCurve = Bn254> {
  pub(super) instructions: Vec<GraphInstruction<C>>,
}

impl<C: KzgCurve> GraphProgram<C> {
  pub(super) fn compile(
    graph: &ConstraintGraph<CurveScalar<C>>,
    inputs: GraphInputs,
  ) -> Result<Self> {
    if inputs.public_count != 4 {
      return Err("Solidity graph requires four circuit public scalars".into());
    }
    for m in [inputs.main, inputs.preprocessed, inputs.stage2] {
      if m.index >= inputs.matrix_count || !(1..=2).contains(&m.rows) {
        return Err("invalid Solidity graph opening window".into());
      }
    }
    let mut program =
      Self { instructions: Vec::with_capacity(graph.nodes.len()) };
    for (index, node) in graph.nodes.iter().enumerate() {
      let child = |id: multi_stark::graph::NodeId| -> Result<usize> {
        let child = id.index();
        if child >= index {
          return Err("graph child must precede its parent".into());
        }
        Ok(child)
      };
      let instruction = match *node {
        Node::Const(value) => GraphInstruction::Constant(value),
        Node::Var(col) => {
          let matrix = inputs.matrix(col.source);
          let row = usize::from(col.offset == RowOffset::Next);
          let column = usize::try_from(col.index)?;
          if row >= matrix.rows || column >= matrix.width {
            return Err("graph column lies outside its opening window".into());
          }
          let offset = row
            .checked_mul(matrix.width)
            .and_then(|base| base.checked_add(column))
            .ok_or("graph opening offset overflow")?;
          GraphInstruction::Opening { matrix: matrix.index, offset }
        },
        Node::Public(index) => {
          let index = usize::try_from(index)?;
          if index >= inputs.public_count {
            return Err("graph public index out of range".into());
          }
          GraphInstruction::Public(index)
        },
        Node::IsFirstRow => GraphInstruction::First,
        Node::IsLastRow => GraphInstruction::Last,
        Node::IsTransition => GraphInstruction::Transition,
        Node::Add(a, b) => GraphInstruction::Add(child(a)?, child(b)?),
        Node::Sub(a, b) => GraphInstruction::Sub(child(a)?, child(b)?),
        Node::Mul(a, b) => GraphInstruction::Mul(child(a)?, child(b)?),
        Node::Neg(a) => GraphInstruction::Neg(child(a)?),
      };
      program.instructions.push(instruction);
    }
    for root in
      graph.zeros.iter().chain(graph.lookups.iter().flat_map(|lookup| {
        std::iter::once(&lookup.multiplicity).chain(&lookup.args)
      }))
    {
      if root.index() >= graph.nodes.len() {
        return Err("graph root out of range".into());
      }
    }
    Ok(program)
  }

  #[cfg(any(feature = "plonk", feature = "groth16"))]
  pub(super) fn evaluate<
    A: Algebra<CurveScalar<C>> + Copy + From<CurveScalar<C>>,
  >(
    &self,
    opening: impl Fn(usize, usize) -> A,
    publics: &[A],
    first: A,
    last: A,
    transition: A,
  ) -> Vec<A> {
    let mut values: Vec<A> = Vec::with_capacity(self.instructions.len());
    for instruction in &self.instructions {
      values.push(match *instruction {
        GraphInstruction::Constant(value) => A::from(value),
        GraphInstruction::Opening { matrix, offset } => opening(matrix, offset),
        GraphInstruction::Public(index) => publics[index],
        GraphInstruction::First => first,
        GraphInstruction::Last => last,
        GraphInstruction::Transition => transition,
        GraphInstruction::Add(a, b) => values[a] + values[b],
        GraphInstruction::Sub(a, b) => values[a] - values[b],
        GraphInstruction::Mul(a, b) => values[a] * values[b],
        GraphInstruction::Neg(a) => -values[a],
      });
    }
    values
  }
}

struct Batch<C: KzgCurve> {
  z: CurveScalar<C>,
  commitments: Vec<G1AffineOf<C>>,
  values: Vec<CurveScalar<C>>,
}

pub(super) fn diagnostics<C: KzgCurve>(
  system: &System<KzgConfig<C>>,
  proof: &Proof<KzgConfig<C>>,
  claims: &[Vec<CurveScalar<C>>],
) -> Result<Json> {
  let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
  system
    .verify_multiple_claims(&refs, proof)
    .map_err(|e| format!("native proof: {e:?}"))?;
  let mut t = system.config.initialise_challenger();
  system.observe_shape(&mut t);
  for &active in &proof.active {
    t.observe_field(CurveScalar::<C>::from_bool(active));
  }
  t.observe_commitment(
    system.preprocessed_commit.clone().ok_or("missing fixed commitment")?,
  );
  t.observe_commitment(proof.commitments.stage_1_trace.clone());
  for &log in &proof.log_degrees {
    t.observe_field(CurveScalar::<C>::from_u8(log));
  }
  observe_claims::<KzgConfig<C>>(&mut t, &refs);
  let (beta, gamma) = sample_lookup_challenges::<KzgConfig<C>>(&mut t);
  let mut accumulator = claims
    .iter()
    .map(|row| {
      (beta
        + row
          .iter()
          .rev()
          .fold(CurveScalar::<C>::ZERO, |acc, value| acc * gamma + *value))
      .inverse()
    })
    .fold(CurveScalar::<C>::ZERO, |a, b| a + b);
  let public_accumulator = accumulator;
  t.observe_commitment(proof.commitments.stage_2_trace.clone());
  for &a in &proof.intermediate_accumulators {
    t.observe_challenge(a);
  }
  let alpha = t.sample_challenge();
  t.observe_commitment(proof.commitments.quotient_chunks.clone());
  let zeta = t.sample_challenge();
  let rounds = [
    (&proof.commitments.stage_1_trace, &proof.stage_1_opened_values),
    (&proof.commitments.stage_2_trace, &proof.stage_2_opened_values),
    (&proof.commitments.quotient_chunks, &proof.quotient_opened_values),
    (
      system.preprocessed_commit.as_ref().unwrap(),
      proof.preprocessed_opened_values.as_ref().unwrap(),
    ),
  ];
  for (commit, _) in &rounds {
    t.observe_commitment((*commit).clone());
    for &log in &proof.log_degrees {
      t.observe_canonical(&u64::from(log));
    }
  }
  let mut batches: Vec<Batch<C>> = vec![];
  for (commit, values) in &rounds {
    for (i, rows) in values.iter().enumerate() {
      let domain = system
        .config
        .pcs()
        .natural_domain_for_degree(1 << proof.log_degrees[i]);
      for (row, values) in rows.iter().enumerate() {
        let z = if row == 0 { zeta } else { domain.next_point(zeta) };
        for &v in values {
          t.observe_challenge(v);
        }
        let index = match batches.iter().position(|b| b.z == z) {
          Some(index) => index,
          None => {
            batches.push(Batch { z, commitments: vec![], values: vec![] });
            batches.len() - 1
          },
        };
        batches[index].commitments.extend_from_slice(&commit.0[i]);
        batches[index].values.extend_from_slice(values);
      }
    }
  }
  let v = t.sample_challenge();
  for witness in &proof.opening_proof.0 {
    t.observe_canonical(witness);
  }
  let r = t.sample_challenge();
  if batches.len() != proof.opening_proof.0.len() {
    return Err("opening count mismatch".into());
  }
  let mut left = G1ProjectiveOf::<C>::zero();
  let mut right = G1ProjectiveOf::<C>::zero();
  let mut rp = CurveScalar::<C>::ONE;
  let generator = system.config.pcs().verifier_params().g1[0];
  for (batch, witness) in batches.iter().zip(&proof.opening_proof.0) {
    let mut folded = G1ProjectiveOf::<C>::zero();
    let mut y = CurveScalar::<C>::ZERO;
    let mut vp = CurveScalar::<C>::ONE;
    for (c, value) in batch.commitments.iter().zip(&batch.values) {
      folded += *c * vp.0;
      y += *value * vp;
      vp *= v;
    }
    left += (folded - generator * y.0 + *witness * batch.z.0) * rp.0;
    right += *witness * rp.0;
    rp *= r;
  }
  let mut compositions = vec![];
  let mut quotients = vec![];
  for (i, c) in system.circuits.iter().enumerate() {
    let n = 1usize << proof.log_degrees[i];
    let domain = system.config.pcs().natural_domain_for_degree(n);
    let sels = domain.selectors_at_point(zeta);
    let next = proof.intermediate_accumulators[i];
    let publics = [beta, gamma, accumulator, next];
    let fixed = &proof.preprocessed_opened_values.as_ref().unwrap()[i];
    let main = &proof.stage_1_opened_values[i];
    let stage2 = &proof.stage_2_opened_values[i];
    let view = VarValues {
      preprocessed: [&fixed[0], fixed.get(1).map_or(&[][..], Vec::as_slice)],
      main: [&main[0], main.get(1).map_or(&[][..], Vec::as_slice)],
      stage2: [&stage2[0], &stage2[1]],
      publics: &publics,
      is_first_row: sels.is_first_row,
      is_last_row: sels.is_last_row,
      is_transition: sels.is_transition,
    };
    let mut values = vec![];
    c.graph.sweep(&view, &mut values);
    let mut constraints = c.graph.constraint_values(&values);
    let ext = multi_stark::system::extension_params::<KzgConfig<C>>();
    let delta = (next - accumulator)
      * (CurveScalar::<C>::from_usize(n) * domain.generator()).inverse();
    multi_stark::lookup::logup_constraint_values(
      &c.graph.lookups,
      &values,
      &stage2[0],
      &stage2[1],
      &publics,
      &[delta],
      sels.is_last_row,
      ext.modulus,
      ext.degree,
      c.lookup_group_size.max(1),
      &mut constraints,
    );
    let composition = constraints
      .into_iter()
      .fold(CurveScalar::<C>::ZERO, |acc, value| acc * alpha + value);
    let zn = zeta.exp_power_of_2(usize::from(proof.log_degrees[i]));
    let quotient = proof.quotient_opened_values[i][0]
      .iter()
      .zip(zn.powers())
      .map(|(&value, power)| value * power)
      .fold(CurveScalar::<C>::ZERO, |a, b| a + b);
    if composition * sels.inv_vanishing != quotient {
      return Err("diagnostic quotient mismatch".into());
    }
    compositions.push(scalar(composition));
    quotients.push(scalar(quotient));
    accumulator = next;
  }
  Ok(json!({
    "challenges": ([beta, gamma, alpha, zeta, v, r].map(scalar)),
    "publicAccumulator": scalar(public_accumulator),
    "outerL": hex_json(&g1::<C>(left.into_affine())),
    "outerR": hex_json(&g1::<C>(right.into_affine())),
    "compositions": compositions,
    "quotients": quotients,
  }))
}
