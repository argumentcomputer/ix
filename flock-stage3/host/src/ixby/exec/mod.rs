//! Experimental proof-free compiler and proof API for scalar and
//! byte/constructor/exact-Nat/application machines. Only approved setup determines topology.
//! The real Flock relation connects canonical bytes to execution and all four
//! commitments. Its native constraint-to-`Codec.Evaluates` refinement remains
//! a separate, unfinished formal obligation; this is not a Stage 4 proof.

#[cfg(test)]
mod application_fixtures;
#[cfg(test)]
mod application_proof_tests;
#[cfg(test)]
mod application_tests;
#[cfg(test)]
mod backend_tests;
#[cfg(test)]
mod benchmark_tests;
#[cfg(test)]
mod byte_tests;
#[cfg(test)]
mod crypto_tests;
#[cfg(test)]
mod nat_fixtures;
#[cfg(test)]
mod nat_tests;
#[cfg(test)]
mod object_fixtures;
#[cfg(test)]
mod object_tests;
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
pub use proof::{ExecProvingPhaseV0, VerifiedExecProof};

use super::{
  byte_value::ByteCapacity,
  commitment::{ByteBuffer, ByteCommitmentSlots, CommitmentCapacities},
  decode::PrimitiveSet,
  io::{InputLayout, LayoutEmitter, PublicLayout},
  machine::{MachineCapacities, ScalarMachineSlots},
  nat_value::NatCapacity,
  object_value::ObjectCapacity,
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
  pub fn byte_capacity(&self) -> Option<ByteCapacity> {
    self.machine.byte_capacity()
  }
  pub fn object_capacity(&self) -> Option<ObjectCapacity> {
    self.machine.object_capacity()
  }
  pub fn nat_capacity(&self) -> Option<NatCapacity> {
    self.machine.nat_capacity()
  }
  pub fn applications(&self) -> bool {
    self.machine.applications.is_some()
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
    let mut domain = if self.applications() {
      profile::APPLICATION_TRANSCRIPT_DOMAIN.to_vec()
    } else if self.nat_capacity().is_some() {
      profile::NAT_TRANSCRIPT_DOMAIN.to_vec()
    } else if self.object_capacity().is_some() {
      profile::OBJECT_TRANSCRIPT_DOMAIN.to_vec()
    } else if self.byte_capacity().is_some() {
      profile::BYTE_TRANSCRIPT_DOMAIN.to_vec()
    } else {
      profile::TRANSCRIPT_DOMAIN.to_vec()
    };
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
  ensure!(
    primitives == primitives.scalar_subset(),
    "expanded primitive registry requires byte-profile compilation"
  );
  compile(profile, capacity, primitives, backend, (None, None, None, false))
}

/// Byte-capable first-order executor with an explicitly approved per-array
/// bound and implementation. Setup still accepts no guest/proof/trace/advice.
pub fn compile_exec_byte_profile(
  profile: SemanticProfile,
  capacity: MachineCapacities,
  bytes: ByteCapacity,
  primitives: PrimitiveSet,
  backend: Blake3Backend,
) -> Result<CompiledExec> {
  profile.admit_bytes(capacity, bytes)?;
  compile(
    profile,
    capacity,
    primitives,
    backend,
    (Some(bytes), None, None, false),
  )
}

/// Explicit bounded constructor setup. All 35 crypto primitives and the
/// existing first-order control remain available; PAP/application are not
/// admitted. No guest, trace, heap, or proof chooses the setup geometry.
pub fn compile_exec_object_profile(
  profile: SemanticProfile,
  capacity: MachineCapacities,
  bytes: ByteCapacity,
  objects: ObjectCapacity,
  primitives: PrimitiveSet,
  backend: Blake3Backend,
) -> Result<CompiledExec> {
  profile.admit_objects(capacity, bytes, objects)?;
  compile(
    profile,
    capacity,
    primitives,
    backend,
    (Some(bytes), Some(objects), None, false),
  )
}

/// Explicit revision-1 setup for exact Nats, existing crypto operations and
/// optional immutable constructors. Nat/Word32 remain separate types. All
/// capacities and opcode availability are selected by the approving verifier.
pub fn compile_exec_nat_profile(
  profile: SemanticProfile,
  capacity: MachineCapacities,
  values: (ByteCapacity, Option<ObjectCapacity>, NatCapacity),
  primitives: PrimitiveSet,
  backend: Blake3Backend,
) -> Result<CompiledExec> {
  profile.admit_nat(capacity, values.0, values.1, values.2)?;
  compile(
    profile,
    capacity,
    primitives,
    backend,
    (Some(values.0), values.1, Some(values.2), false),
  )
}

/// Explicit higher-order implementation upgrade with immutable closures/PAPs,
/// let/tail application and bounded apply-rest continuations. Semantic v0/v1
/// codec bytes are unchanged; the approving verifier selects this setup class.
pub fn compile_exec_application_profile(
  profile: SemanticProfile,
  capacity: MachineCapacities,
  values: (ByteCapacity, ObjectCapacity, Option<NatCapacity>),
  primitives: PrimitiveSet,
  backend: Blake3Backend,
) -> Result<CompiledExec> {
  ensure!(
    capacity.control.arguments == capacity.program.operands,
    "application argument/operand capacities must agree"
  );
  match values.2 {
    None => profile.admit_objects(capacity, values.0, values.1)?,
    Some(nats) => {
      profile.admit_nat(capacity, values.0, Some(values.1), nats)?
    },
  }
  compile(
    profile,
    capacity,
    primitives,
    backend,
    (Some(values.0), Some(values.1), values.2, true),
  )
}

type NativeValues =
  (Option<ByteCapacity>, Option<ObjectCapacity>, Option<NatCapacity>, bool);

fn compile(
  profile: SemanticProfile,
  capacity: MachineCapacities,
  primitives: PrimitiveSet,
  backend: Blake3Backend,
  values: NativeValues,
) -> Result<CompiledExec> {
  let (bytes, objects, nats, applications) = values;
  ensure!(
    nats.is_some() || primitives == primitives.crypto_subset(),
    "Nat primitives require revision-1 setup"
  );
  let mut count = CountingEmitter::new();
  let (_, _, counted_input, counted_public) =
    emit_values(&mut count, 8, profile, capacity, primitives, backend, values)?;
  let nu = count.required_nu(8)?;
  ensure!(nu <= 20, "scalar row domain admission");
  let (registry, counts) = count.registry(nu);
  let counted_identity = registry.digest();
  let params = parameters(&UnionInstance::new(&registry, counts))?;
  // The count registry holds inner matrices only, not a union witness.
  drop(registry);
  let mut builder = ShapeBuilder::new(nu);
  let (machine, commitments, input, public) = emit_values(
    &mut builder,
    nu,
    profile,
    capacity,
    primitives,
    backend,
    values,
  )?;
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
  let mut identities = match (bytes, objects) {
    (None, None) => {
      ExecIdentities::new(profile, capacity, primitives, nu, &params, backend)
    },
    (Some(bytes), None) => ExecIdentities::new_byte(
      profile, capacity, primitives, nu, &params, backend, bytes,
    ),
    (Some(bytes), Some(objects)) => ExecIdentities::new_objects(
      profile,
      capacity,
      primitives,
      nu,
      &params,
      backend,
      (bytes, objects),
    ),
    (None, Some(_)) => unreachable!("object setup requires byte values"),
  };
  identities.registry = shape.registry.digest();
  if let Some(nats) = nats {
    identities = identities.with_nats(nats);
  }
  if applications {
    identities = identities.with_applications();
  }
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

fn emit_values(
  builder: &mut impl CircuitEmitter,
  nu: usize,
  profile: SemanticProfile,
  c: MachineCapacities,
  primitives: PrimitiveSet,
  backend: Blake3Backend,
  values: NativeValues,
) -> Result<(ScalarMachineSlots, ByteCommitmentSlots, InputLayout, PublicLayout)>
{
  let (bytes, objects, nats, applications) = values;
  let mut b = LayoutEmitter::new(builder);
  // Preserve the scalar declaration order and therefore its existing keys.
  let scalar = if bytes.is_none() {
    Some(ScalarMachineSlots::declare(&mut b, nu, c, primitives)?)
  } else {
    None
  };
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
  let machine = match (bytes, objects) {
    (Some(bytes), Some(objects)) if applications => {
      ScalarMachineSlots::declare_with_applications(
        &mut b,
        nu,
        c,
        primitives,
        (bytes, objects, nats),
        &commitments.hashes()[0],
      )?
    },
    (Some(bytes), objects) if nats.is_some() => {
      ScalarMachineSlots::declare_with_nats(
        &mut b,
        nu,
        c,
        primitives,
        (bytes, objects, nats.unwrap()),
        &commitments.hashes()[0],
      )?
    },
    (None, None) => scalar.unwrap(),
    (Some(bytes), None) => ScalarMachineSlots::declare_with_bytes(
      &mut b,
      nu,
      c,
      primitives,
      bytes,
      &commitments.hashes()[0],
    )?,
    (Some(bytes), Some(objects)) => ScalarMachineSlots::declare_with_objects(
      &mut b,
      nu,
      c,
      primitives,
      (bytes, objects),
      &commitments.hashes()[0],
    )?,
    (None, Some(_)) => unreachable!("object setup requires byte values"),
  };
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
