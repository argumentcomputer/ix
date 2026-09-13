use super::super::{decode::PrimitiveSet, machine::MachineCapacities};
use crate::blake3_backend::Blake3Backend;
use anyhow::{Result, ensure};
use flock_prover::{field::F128, pcs::PcsParams};

/// Exact experimental `Codec.encodeProfile` envelope, not backend parameters.
/// Its fields are private so invalid profiles cannot reach setup accidentally.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticProfile([u32; 14]);

impl SemanticProfile {
  pub fn new(parameters: [u32; 14]) -> Result<Self> {
    ensure!(
      parameters[7] == 0 && parameters[8] == 0,
      "excluded Nat/String families"
    );
    Ok(Self(parameters))
  }

  /// Semantic bounds for the currently supported first-order scalar class.
  /// The physical input and output buffers must have the same byte capacity.
  pub fn scalar(c: MachineCapacities) -> Result<Self> {
    let parameters = [
      c.program.functions,
      0,
      c.program.blocks,
      c.control.locals,
      c.program.operands,
      c.control.continuations,
      c.input.values.max(1),
      0,
      0,
      0,
      c.program.bytes,
      c.input.bytes,
      1,
      c.steps,
    ]
    .map(u32::try_from)
    .into_iter()
    .collect::<std::result::Result<Vec<_>, _>>()?;
    let profile = Self::new(parameters.try_into().unwrap())?;
    profile.admit_scalar(c)?;
    Ok(profile)
  }

  pub fn parameters(self) -> [u32; 14] {
    self.0
  }

  pub fn to_bytes(self) -> [u8; 68] {
    let mut bytes = [0; 68];
    bytes[..4].copy_from_slice(b"IXBP");
    // Wire and semantic revisions are both zero.
    for (index, value) in self.0.iter().enumerate() {
      bytes[12 + 4 * index..16 + 4 * index]
        .copy_from_slice(&value.to_le_bytes());
    }
    bytes
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    ensure!(bytes.len() == 68, "profile envelope length");
    ensure!(
      &bytes[..4] == b"IXBP" && bytes[4..12] == [0; 8],
      "profile domain/revision"
    );
    let parameters = std::array::from_fn(|i| {
      u32::from_le_bytes(bytes[12 + 4 * i..16 + 4 * i].try_into().unwrap())
    });
    Self::new(parameters)
  }

  pub(super) fn admit_scalar(self, c: MachineCapacities) -> Result<()> {
    let p = self.0.map(|n| n as usize);
    ensure!(
      p[0] == c.program.functions && p[1] == 0 && p[2] == c.program.blocks,
      "scalar program profile mismatch"
    );
    ensure!(
      p[3] == c.control.locals
        && p[4] == c.program.operands
        && p[5] == c.control.continuations,
      "scalar control profile mismatch"
    );
    ensure!(
      p[6] == c.input.values.max(1) && p[9] == 0 && p[12] == 1,
      "scalar value profile mismatch"
    );
    ensure!(
      p[10] == c.program.bytes
        && p[11] == c.input.bytes
        && p[11] == c.output_bytes
        && p[13] == c.steps,
      "scalar byte/fuel profile mismatch"
    );
    Ok(())
  }
}

/// The expected full `(P,B,I,O)` digest. It is supplied by the caller, not
/// extracted from the proof's public vector. This is not the final Ixon API.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecStatementDigest(pub [u8; 32]);

impl ExecStatementDigest {
  pub fn limbs(self) -> [F128; 2] {
    [
      crate::hash::pack_bytes(&self.0[..16]),
      crate::hash::pack_bytes(&self.0[16..]),
    ]
  }
}

/// Native commitment calculation for a caller that knows the exact artifacts.
/// Computing this value does NOT establish canonical admission or execution.
pub fn expected_statement(
  profile: SemanticProfile,
  program: &[u8],
  input: &[u8],
  output: &[u8],
) -> ExecStatementDigest {
  let p = hash(0, &[], &profile.to_bytes());
  let b = hash(1, &p, program);
  let i = hash(2, &b, input);
  let o = hash(3, &b, output);
  ExecStatementDigest(hash(4, &[], &[p, b, i, o].concat()))
}

fn hash(tag: u8, parent: &[u8], bytes: &[u8]) -> [u8; 32] {
  let mut h = blake3::Hasher::new();
  h.update(b"IxBy/commit/v0\0");
  h.update(&[tag]);
  h.update(parent);
  h.update(bytes);
  *h.finalize().as_bytes()
}

pub(super) const TRANSCRIPT_DOMAIN: &[u8] = b"ix:ixby:scalar-exec:v0";
const UPSTREAM: &[u8] = b"b310f35f35f68095537150a1c8c0a43caca9a29e";
const IMPLEMENTATION: &[u8] = b"IxBy/Flock/fixed-scalar-machine/v0";
const PACKED_IMPLEMENTATION: &[u8] =
  b"IxBy/Flock/fixed-scalar-machine/packed-blake3/v0";

/// Distinct verifier-owned identities. The final digest binds their ordered
/// tuple; callers must approve it, not accept a proof-selected setup identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecIdentities {
  pub protocol: [u8; 32],
  pub implementation: [u8; 32],
  pub profile: [u8; 32],
  pub capacity: [u8; 32],
  pub primitives: [u8; 32],
  pub registry: [u8; 32],
  pub circuit: [u8; 32],
  pub public_template: [u8; 32],
  pub input_layout: [u8; 32],
}

impl ExecIdentities {
  pub fn digest(self) -> [u8; 32] {
    let mut bytes = b"IxBy/Flock/exec-setup/v0\0".to_vec();
    for digest in [
      self.protocol,
      self.implementation,
      self.profile,
      self.capacity,
      self.primitives,
      self.registry,
      self.circuit,
      self.public_template,
      self.input_layout,
    ] {
      bytes.extend_from_slice(&digest);
    }
    *blake3::hash(&bytes).as_bytes()
  }

  pub(super) fn new(
    profile: SemanticProfile,
    c: MachineCapacities,
    primitives: PrimitiveSet,
    nu: usize,
    params: &PcsParams,
    backend: Blake3Backend,
  ) -> Self {
    let mut protocol = b"IxBy/Flock/protocol/v0\0".to_vec();
    protocol.extend_from_slice(UPSTREAM);
    protocol.extend_from_slice(TRANSCRIPT_DOMAIN);
    // F128, Fast128, BLAKE3 Merkle, chained-BLAKE3 transcript.
    protocol.extend_from_slice(&[1, 1, 1, 1]);
    for n in [nu, params.m, params.log_batch_size, params.log_inv_rate] {
      protocol.extend_from_slice(&(n as u64).to_le_bytes());
    }
    protocol.push(u8::from(params.num_lanes.is_some()));
    protocol
      .extend_from_slice(&(params.num_lanes.unwrap_or(0) as u64).to_le_bytes());
    let mut capacity = b"IxBy/Flock/scalar-capacity/v0\0".to_vec();
    for n in [
      c.program.bytes,
      c.program.functions,
      c.program.blocks,
      c.program.operands,
      c.control.locals,
      c.control.continuations,
      c.control.arguments,
      c.input.bytes,
      c.input.values,
      c.output_bytes,
      c.steps,
    ] {
      capacity.extend_from_slice(&(n as u64).to_le_bytes());
    }
    let mut registry = b"IxBy/Flock/scalar-primitives/v0\0".to_vec();
    let opcodes: Vec<_> = primitives.opcodes().collect();
    registry.extend_from_slice(&(opcodes.len() as u32).to_le_bytes());
    registry.extend_from_slice(&opcodes);
    Self {
      protocol: *blake3::hash(&protocol).as_bytes(),
      implementation: *blake3::hash(match backend {
        Blake3Backend::LegacyOptionF => IMPLEMENTATION,
        Blake3Backend::PackedWordsV0 => PACKED_IMPLEMENTATION,
      })
      .as_bytes(),
      profile: hash(0, &[], &profile.to_bytes()),
      capacity: *blake3::hash(&capacity).as_bytes(),
      primitives: *blake3::hash(&registry).as_bytes(),
      registry: [0; 32],
      circuit: [0; 32],
      public_template: [0; 32],
      input_layout: [0; 32],
    }
  }
}
