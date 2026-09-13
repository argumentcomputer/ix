//! Experimental proof-free compiler and proof API for the first-order scalar
//! machine. Only profile/capacity/primitive setup determines the topology.
//! The real Flock relation connects canonical bytes to execution and all four
//! commitments. Its native constraint-to-`Codec.Evaluates` refinement remains
//! a separate, unfinished formal obligation; this is not a Stage 4 proof.

#[cfg(test)]
mod backend_tests;
mod profile;
mod proof;
#[cfg(test)]
mod proof_tests;
#[cfg(test)]
mod tests;
mod witness;

pub use profile::{
  ExecIdentities, ExecStatementDigest, SemanticProfile, expected_statement,
};
pub use proof::VerifiedExecProof;

use super::{
  commitment::{ByteBuffer, ByteCommitmentSlots, CommitmentCapacities},
  decode::PrimitiveSet,
  io::{InputLayout, LayoutEmitter, PublicLayout},
  machine::{MachineCapacities, ScalarMachineSlots},
};
use crate::{
  blake3_backend::Blake3Backend,
  sizing::{CircuitEmitter, CountingEmitter},
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{CircuitShape, ShapeBuilder},
  hash::HashKind,
  lincheck::LincheckCircuit,
  pcs::{
    PcsParams,
    ligerito::{LigeritoProfile, embedded_initial_k_or_default},
  },
  r1cs::BlockR1cs,
  union::UnionInstance,
};

/// No deserializer or public fields: an approved artifact is produced only
/// from proof-free setup, never reconstructed from metadata in an Exec proof.
pub struct CompiledExec {
  machine: ScalarMachineSlots,
  commitments: ByteCommitmentSlots,
  input: InputLayout,
  public: PublicLayout,
  shape: CircuitShape,
  tables: Vec<BlockR1cs>,
  params: PcsParams,
  profile: SemanticProfile,
  capacity: MachineCapacities,
  identities: ExecIdentities,
  nu: usize,
}

impl CompiledExec {
  pub fn identities(&self) -> ExecIdentities {
    self.identities
  }
  pub fn profile(&self) -> SemanticProfile {
    self.profile
  }
  pub fn capacity(&self) -> MachineCapacities {
    self.capacity
  }
  pub fn blake3_backend(&self) -> Blake3Backend {
    self.commitments.hashes()[0].compression().backend()
  }
  pub fn public_template(&self) -> &PublicLayout {
    &self.public
  }
  pub fn verifier_shape(&self) -> &CircuitShape {
    &self.shape
  }
  pub fn pcs_params(&self) -> &PcsParams {
    &self.params
  }
  /// Read-only native replay inputs; no proof-supplied table is accepted.
  pub fn lincheck_circuits(&self) -> Vec<&dyn LincheckCircuit> {
    self
      .tables
      .iter()
      .map(|table| table.csc_lincheck_circuit() as &dyn LincheckCircuit)
      .collect()
  }
  pub fn transcript_domain(&self) -> Vec<u8> {
    let mut domain = profile::TRANSCRIPT_DOMAIN.to_vec();
    domain.extend_from_slice(&self.identities.digest());
    domain
  }
}

/// Setup accepts no guest image, Stage 2 key/AIR, proof, trace, or advice.
/// All table dimensions are admitted before physical circuit allocation.
pub fn compile_exec_profile(
  profile: SemanticProfile,
  capacity: MachineCapacities,
  primitives: PrimitiveSet,
) -> Result<CompiledExec> {
  compile_exec_profile_with_backend(
    profile,
    capacity,
    primitives,
    Blake3Backend::LegacyOptionF,
  )
}

/// Explicit implementation/key upgrade; does not change semantic profile
/// bytes, guest opcodes or the BLAKE3 commitment function. The selected
/// implementation is bound into setup and the proof transcript. Neither
/// guest updates nor proof headers may select it on the verifier's behalf.
pub fn compile_exec_profile_with_backend(
  profile: SemanticProfile,
  capacity: MachineCapacities,
  primitives: PrimitiveSet,
  backend: Blake3Backend,
) -> Result<CompiledExec> {
  profile.admit_scalar(capacity)?;
  let mut count = CountingEmitter::new();
  let (_, _, counted_input, counted_public) =
    emit(&mut count, 8, profile, capacity, primitives, backend)?;
  let nu = count.required_nu(8)?;
  ensure!(nu <= 20, "scalar row domain admission");
  let (registry, counts) = count.registry(nu);
  let counted_identity = registry.digest();
  let params = parameters(&UnionInstance::new(&registry, counts))?;
  // The count registry holds inner matrices only, not a union witness.
  drop(registry);
  let mut builder = ShapeBuilder::new(nu);
  let (machine, commitments, input, public) =
    emit(&mut builder, nu, profile, capacity, primitives, backend)?;
  let shape = builder
    .finish()
    .map_err(|error| anyhow::anyhow!("Exec circuit compilation: {error:?}"))?;
  count.ensure_matches(&shape)?;
  ensure!(
    counted_input == input && counted_public == public,
    "count/emit layout mismatch"
  );
  ensure!(
    shape.registry.digest() == counted_identity,
    "count/emit registry mismatch"
  );
  ensure!(
    public.outputs() == 2,
    "Exec digest must be the only variable public output"
  );
  let mut identities =
    ExecIdentities::new(profile, capacity, primitives, nu, &params, backend);
  identities.registry = shape.registry.digest();
  identities.circuit = shape.circuit.digest();
  identities.public_template = public.digest();
  identities.input_layout = input.digest();
  let tables = witness::tables(&machine, &commitments, &shape, nu)?;
  Ok(CompiledExec {
    machine,
    commitments,
    input,
    public,
    shape,
    tables,
    params,
    profile,
    capacity,
    identities,
    nu,
  })
}

fn parameters(union: &UnionInstance<'_>) -> Result<PcsParams> {
  let m = union.dense_m();
  ensure!((22..=35).contains(&m), "Exec PCS outside pinned baseline registry");
  let profile = LigeritoProfile::Fast128;
  let log_batch_size = embedded_initial_k_or_default(m, profile);
  Ok(PcsParams {
    m,
    profile,
    log_batch_size,
    log_inv_rate: profile.log_inv_rate(),
    num_lanes: union.commit_lanes(log_batch_size),
    merkle_hash: HashKind::Blake3,
  })
}

fn emit(
  builder: &mut impl CircuitEmitter,
  nu: usize,
  profile: SemanticProfile,
  c: MachineCapacities,
  primitives: PrimitiveSet,
  backend: Blake3Backend,
) -> Result<(ScalarMachineSlots, ByteCommitmentSlots, InputLayout, PublicLayout)>
{
  let mut b = LayoutEmitter::new(builder);
  let machine = ScalarMachineSlots::declare(&mut b, nu, c, primitives)?;
  let commitments = ByteCommitmentSlots::declare_with_backend(
    &mut b,
    nu,
    &profile.to_bytes(),
    CommitmentCapacities {
      program: c.program.bytes,
      input: c.input.bytes,
      output: c.output_bytes,
    },
    backend,
  )?;
  let code: Vec<_> =
    (0..1 + c.program.data_words()).map(|_| b.input()).collect();
  let input: Vec<_> =
    (0..1 + c.input.data_words()).map(|_| b.input()).collect();
  let output = machine.execute(&mut b, &code, &input);
  let statement = commitments.bind(
    &mut b,
    ByteBuffer { length: code[0], words: &code[1..] },
    ByteBuffer { length: input[0], words: &input[1..] },
    ByteBuffer { length: output[0], words: &output[1..] },
  );
  for limb in statement.digest {
    b.publish(limb);
  }
  let (input, public) = b.finish();
  Ok((machine, commitments, input, public))
}
