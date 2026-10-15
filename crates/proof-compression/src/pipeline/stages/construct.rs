//! Production circuit layouts and ownership of lowered witnesses.
use super::{Prepared, Result};
use crate::{
  foreign::{GoldilocksCircuit, GoldilocksInputs},
  fri::{self, VerifierInputs, VerifierKey, VerifierPlan},
  kzg::{KzgConfig, Scalar},
};
use multi_stark::{
  plonkish::{Assignment, Circuit, MultiStarkCircuit},
  system::CircuitInputs,
  traits::Field,
  types::Val,
};
use std::path::Path;

pub(in crate::pipeline) const FRI_NAMESPACE: u8 = 107;
pub(in crate::pipeline) const FIRST_NAMESPACE: u8 = 93;
pub(in crate::pipeline) const RECURSIVE_NAMESPACE: u8 = 94;
pub(in crate::pipeline) const TABLE_HEIGHT: usize = 1 << 22;
pub(in crate::pipeline) const RECURSIVE_HEIGHT: usize = 1 << 27;

#[tracing::instrument(level = "info", skip_all, name = "compression/lower")]
pub(in crate::pipeline) fn lower_fri(
  circuit: Circuit<Val>,
  height: usize,
) -> Result<MultiStarkCircuit<Val>> {
  Ok(
    circuit
      .lower_to_multi_stark_sharded(Val::from_u8(FRI_NAMESPACE), height)?,
  )
}

pub(in crate::pipeline) fn fri_definitions(
  compiled: &MultiStarkCircuit<Val>,
) -> Vec<CircuitInputs<Val>> {
  let mut definitions = compiled.circuit_inputs();
  for definition in &mut definitions {
    definition.lookup_group_size = 3;
  }
  definitions
}

#[tracing::instrument(level = "info", skip_all, name = "compression/lower")]
pub(in crate::pipeline) fn lower_first(
  circuit: Circuit<Scalar>,
  height: usize,
  table_height: usize,
) -> Result<MultiStarkCircuit<Scalar>> {
  Ok(
    circuit
      .lower_to_multi_stark_sharded(Scalar::from_u8(FIRST_NAMESPACE), height)?
      .merge_table_traces(table_height)?,
  )
}

#[tracing::instrument(level = "info", skip_all, name = "compression/lower")]
pub(in crate::pipeline) fn lower_recursive(
  circuit: Circuit<Scalar>,
  max_height: usize,
) -> Result<MultiStarkCircuit<Scalar>> {
  let height = circuit.multi_stark_layout()?.main_height;
  if height > max_height.min(RECURSIVE_HEIGHT) {
    return Err(
      "recursive computation exceeds its single-trace height cap".into(),
    );
  }
  let compiled = circuit
    .lower_to_multi_stark_sharded(Scalar::from_u8(RECURSIVE_NAMESPACE), height)?
    .merge_table_traces(height)?;
  if compiled.num_circuits() != 2 || compiled.main_heights() != [height] {
    return Err("expected one computation trace and one merged table".into());
  }
  Ok(compiled)
}

pub(in crate::pipeline) fn max_height<F: Field>(
  compiled: &MultiStarkCircuit<F>,
) -> Result<usize> {
  (0..compiled.num_circuits())
    .map(|i| compiled.trace_dimensions(i).map(|(height, _)| height))
    .max()
    .flatten()
    .ok_or_else(|| "empty compiled circuit".into())
}

/// Owns the frontend allocations until commitment has copied their columns.
pub(in crate::pipeline) struct Lowered {
  pub(in crate::pipeline) compiled: MultiStarkCircuit<Scalar>,
  pub(in crate::pipeline) assignment: Assignment<Scalar>,
}

impl Lowered {
  pub(in crate::pipeline) fn commit(
    self,
    config: KzgConfig,
    preprocessing: Option<&Path>,
    prefetch_bytes: usize,
  ) -> Result<super::super::prover::Committed> {
    let committed = super::super::prover::Committed::prepare(
      config,
      &self.compiled.trace_shards(&self.assignment)?,
      preprocessing,
      prefetch_bytes,
    )?;
    drop(self);
    Ok(committed)
  }
}

/// The FRI verifier circuit and assignment recipe, independent of a witness.
pub(in crate::pipeline) struct FriConstruction {
  pub(in crate::pipeline) circuit: Circuit<Val>,
  inputs: VerifierInputs,
}

impl FriConstruction {
  #[tracing::instrument(
    level = "info",
    skip_all,
    name = "compression/build_circuit"
  )]
  pub(in crate::pipeline) fn build(
    plan: &VerifierPlan<'_>,
    schema: fri::Statement<fri::StatementSlot>,
  ) -> Result<Self> {
    let (circuit, inputs) = plan.build(schema, Default::default())?;
    Ok(Self { circuit, inputs })
  }

  #[tracing::instrument(
    level = "info",
    skip_all,
    name = "compression/source_witness"
  )]
  pub(in crate::pipeline) fn assign(
    self,
    plan: &VerifierPlan<'_>,
    proof: &multi_stark::prover::Proof<
      multi_stark::types::GoldilocksBlake3Config,
    >,
    claims: Vec<Vec<Val>>,
  ) -> Result<Prepared<Val>> {
    let expanded = plan.expand_witness(fri::ProofEnvelope::Ordinary {
      proof,
      claims: &claims,
    })?;
    let mut witness = self.circuit.witness();
    self.inputs.assign_statement(
      &mut witness,
      &fri::Statement { claims, messages: vec![] },
    )?;
    expanded.assign_proof(&mut witness, &self.inputs)?;
    let assignment = witness.generate()?;
    Ok(Prepared { circuit: self.circuit, assignment })
  }
}

pub(in crate::pipeline) fn fri_profile(
  key: &VerifierKey,
  claims: &[Vec<Val>],
) -> Result<fri::ProofProfile> {
  Ok(fri::ProofProfile {
    envelope: fri::Envelope::Ordinary,
    active: vec![true; key.system().circuits.len()],
    log_degrees: key
      .system()
      .circuits
      .iter()
      .map(|c| {
        Ok(u8::try_from(
          c.preprocessed_height
            .checked_ilog2()
            .ok_or("missing trace height")?,
        )?)
      })
      .collect::<Result<_>>()?,
    claim_lengths: claims.iter().map(Vec::len).collect(),
    message_lengths: vec![],
    max_field_retries: fri::DEFAULT_FIELD_RETRIES,
  })
}

#[tracing::instrument(level = "info", skip_all, name = "compression/translate")]
pub(in crate::pipeline) fn translate(
  source: &Circuit<Val>,
) -> GoldilocksCircuit {
  GoldilocksCircuit::new_preallocated(source)
}

#[tracing::instrument(level = "info", skip_all, name = "compression/witness")]
pub(in crate::pipeline) fn assign_foreign(
  inputs: &GoldilocksInputs,
  circuit: &Circuit<Scalar>,
  assignment: &Assignment<Val>,
) -> Result<Assignment<Scalar>> {
  let mut witness = circuit.witness();
  inputs.assign(assignment, &mut witness)?;
  Ok(witness.generate()?)
}

pub(in crate::pipeline) fn prepare_first(
  prepared: Prepared<Val>,
  height: usize,
  table_height: usize,
) -> Result<Lowered> {
  let translated = translate(&prepared.circuit);
  drop(prepared.circuit);
  let compiled = lower_first(translated.circuit, height, table_height)?;
  let assignment = assign_foreign(
    &translated.inputs,
    compiled.circuit(),
    &prepared.assignment,
  )?;
  Ok(Lowered { compiled, assignment })
}

pub(in crate::pipeline) fn recursive_layout()
-> crate::recursive::native_verifier::LayoutPolicy {
  crate::recursive::native_verifier::LayoutPolicy {
    namespace: Scalar::from_u8(RECURSIVE_NAMESPACE),
    max_computation_height: RECURSIVE_HEIGHT,
    max_table_height: RECURSIVE_HEIGHT,
  }
}

pub(in crate::pipeline) fn recursive_plan<'a>(
  system: &'a multi_stark::system::System<KzgConfig>,
  logs: &[u8],
  schema: crate::recursive::native_verifier::ClaimSchema,
) -> Result<crate::recursive::native_verifier::Plan<'a>> {
  Ok(crate::recursive::native_verifier::Plan::new(
    system,
    logs,
    schema,
    recursive_layout(),
  )?)
}
