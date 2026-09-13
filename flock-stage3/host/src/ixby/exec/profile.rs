use super::super::{
  byte_value::ByteCapacity,
  decode::PrimitiveSet,
  machine::MachineCapacities,
  nat_value::NatCapacity,
  object_value::{ObjectCapacity, ObjectLayout},
};
use crate::blake3_backend::Blake3Backend;
use anyhow::{Result, ensure};
use flock_prover::{field::F128, pcs::PcsParams};

/// Exact experimental `Codec.encodeProfile` envelope, not backend parameters.
/// Its fields are private so invalid profiles cannot reach setup accidentally.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticProfile([u32; 14], u32);

impl SemanticProfile {
  pub fn new(parameters: [u32; 14]) -> Result<Self> {
    ensure!(
      parameters[7] == 0 && parameters[8] == 0,
      "excluded Nat/String families"
    );
    Ok(Self(parameters, 0))
  }
  pub fn new_nat(parameters: [u32; 14]) -> Result<Self> {
    ensure!(parameters[8] == 0, "excluded String family");
    Ok(Self(parameters, 1))
  }
  pub fn revision(self) -> u32 {
    self.1
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

  /// Existing semantic envelope with a nonzero per-array bound. Other
  /// unsupported aggregate/value families remain excluded by this setup.
  pub fn bytes(c: MachineCapacities, capacity: ByteCapacity) -> Result<Self> {
    let mut profile = Self::scalar(c)?;
    profile.0[9] = capacity.bytes() as u32;
    profile.admit_bytes(c, capacity)?;
    Ok(profile)
  }
  pub fn objects(
    c: MachineCapacities,
    bytes: ByteCapacity,
    objects: ObjectCapacity,
  ) -> Result<Self> {
    ObjectLayout::new(c, objects)?;
    let mut profile = Self::bytes(c, bytes)?;
    profile.0[1] = objects.constructors() as u32;
    profile.0[6] = objects.nodes() as u32;
    profile.0[12] = objects.depth() as u32;
    profile.admit_objects(c, bytes, objects)?;
    Ok(profile)
  }
  pub(super) fn admit_objects(
    self,
    c: MachineCapacities,
    bytes: ByteCapacity,
    objects: ObjectCapacity,
  ) -> Result<()> {
    ensure!(
      self.0[1] as usize == objects.constructors()
        && self.0[6] as usize == objects.nodes()
        && self.0[12] as usize == objects.depth(),
      "constructor semantic profile mismatch"
    );
    ObjectLayout::new(c, objects)?;
    let mut scalar = self;
    scalar.0[1] = 0;
    scalar.0[6] = c.input.values.max(1) as u32;
    scalar.0[12] = 1;
    scalar.admit_bytes(c, bytes)
  }

  pub fn nat(
    c: MachineCapacities,
    bytes: ByteCapacity,
    objects: Option<ObjectCapacity>,
    nats: NatCapacity,
  ) -> Result<Self> {
    let mut profile = match objects {
      None => Self::bytes(c, bytes)?,
      Some(objects) => Self::objects(c, bytes, objects)?,
    };
    profile.0[7] = nats.bits() as u32;
    profile.1 = 1;
    profile.admit_nat(c, bytes, objects, nats)?;
    Ok(profile)
  }
  pub(super) fn admit_nat(
    self,
    c: MachineCapacities,
    bytes: ByteCapacity,
    objects: Option<ObjectCapacity>,
    nats: NatCapacity,
  ) -> Result<()> {
    ensure!(
      self.1 == 1 && self.0[7] as usize == nats.bits(),
      "Nat revision/bit-bound mismatch"
    );
    ensure!(
      nats.bytes() <= bytes.bytes(),
      "Nat magnitude exceeds arena capacity"
    );
    let mut v0 = self;
    v0.1 = 0;
    v0.0[7] = 0;
    match objects {
      None => v0.admit_bytes(c, bytes),
      Some(objects) => v0.admit_objects(c, bytes, objects),
    }
  }

  pub(super) fn admit_bytes(
    self,
    c: MachineCapacities,
    capacity: ByteCapacity,
  ) -> Result<()> {
    ensure!(
      self.0[9] as usize == capacity.bytes(),
      "byte-array profile mismatch"
    );
    let mut scalar = self;
    scalar.0[9] = 0;
    scalar.admit_scalar(c)
  }

  pub fn to_bytes(self) -> [u8; 68] {
    let mut bytes = [0; 68];
    bytes[..4].copy_from_slice(b"IXBP");
    bytes[4..8].copy_from_slice(&self.1.to_le_bytes());
    bytes[8..12].copy_from_slice(&self.1.to_le_bytes());
    for (index, value) in self.0.iter().enumerate() {
      bytes[12 + 4 * index..16 + 4 * index]
        .copy_from_slice(&value.to_le_bytes());
    }
    bytes
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    ensure!(bytes.len() == 68, "profile envelope length");
    ensure!(
      &bytes[..4] == b"IXBP" && bytes[4..8] == bytes[8..12],
      "profile domain/revision"
    );
    let parameters = std::array::from_fn(|i| {
      u32::from_le_bytes(bytes[12 + 4 * i..16 + 4 * i].try_into().unwrap())
    });
    match u32::from_le_bytes(bytes[4..8].try_into().unwrap()) {
      0 => Self::new(parameters),
      1 => Self::new_nat(parameters),
      _ => anyhow::bail!("profile domain/revision"),
    }
  }

  pub(super) fn admit_scalar(self, c: MachineCapacities) -> Result<()> {
    let p = self.0.map(|n| n as usize);
    ensure!(
      self.1 == 0 && p[7] == 0 && p[8] == 0,
      "scalar semantic revision/families"
    );
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
pub(super) const BYTE_TRANSCRIPT_DOMAIN: &[u8] = b"ix:ixby:byte-exec:v0";
pub(super) const OBJECT_TRANSCRIPT_DOMAIN: &[u8] = b"ix:ixby:object-exec:v0";
pub(super) const NAT_TRANSCRIPT_DOMAIN: &[u8] = b"ix:ixby:nat-exec:v1";
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
  pub(super) fn with_nats(mut self, capacity: NatCapacity) -> Self {
    self.protocol = *blake3::hash(
      &[
        b"IxBy/Flock/nat-protocol/v1\0".as_slice(),
        &self.protocol,
        NAT_TRANSCRIPT_DOMAIN,
      ]
      .concat(),
    )
    .as_bytes();
    self.implementation = *blake3::hash(
      &[
        b"IxBy/Flock/exact-nat-immutable-magnitude/v1\0".as_slice(),
        &self.implementation,
      ]
      .concat(),
    )
    .as_bytes();
    self.capacity = *blake3::hash(
      &[
        b"IxBy/Flock/nat-capacity/v1\0".as_slice(),
        &self.capacity,
        &(capacity.bits() as u64).to_le_bytes(),
      ]
      .concat(),
    )
    .as_bytes();
    self.primitives = *blake3::hash(
      &[b"IxBy/Flock/nat-primitives/v1\0".as_slice(), &self.primitives]
        .concat(),
    )
    .as_bytes();
    self
  }
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
    Self::with_values(profile, c, primitives, nu, params, backend, None)
  }

  pub(super) fn new_byte(
    profile: SemanticProfile,
    c: MachineCapacities,
    primitives: PrimitiveSet,
    nu: usize,
    params: &PcsParams,
    backend: Blake3Backend,
    byte_capacity: ByteCapacity,
  ) -> Self {
    Self::with_values(
      profile,
      c,
      primitives,
      nu,
      params,
      backend,
      Some(byte_capacity),
    )
  }
  pub(super) fn new_objects(
    profile: SemanticProfile,
    c: MachineCapacities,
    primitives: PrimitiveSet,
    nu: usize,
    params: &PcsParams,
    backend: Blake3Backend,
    values: (ByteCapacity, ObjectCapacity),
  ) -> Self {
    let mut identity =
      Self::new_byte(profile, c, primitives, nu, params, backend, values.0);
    let layout = ObjectLayout::new(c, values.1).unwrap();
    identity.protocol = *blake3::hash(
      &[
        b"IxBy/Flock/object-protocol/v0\0".as_slice(),
        &identity.protocol,
        OBJECT_TRANSCRIPT_DOMAIN,
      ]
      .concat(),
    )
    .as_bytes();
    identity.implementation = *blake3::hash(
      &[
        b"IxBy/Flock/immutable-constructor-machine/v0\0".as_slice(),
        &identity.implementation,
      ]
      .concat(),
    )
    .as_bytes();
    let mut capacity =
      [b"IxBy/Flock/object-capacity/v0\0".as_slice(), &identity.capacity]
        .concat();
    for value in [
      values.1.constructors(),
      values.1.depth(),
      values.1.nodes(),
      layout.input_slots(),
      layout.entries(),
      layout.byte_entries(),
    ] {
      capacity.extend_from_slice(&(value as u64).to_le_bytes());
    }
    identity.capacity = *blake3::hash(&capacity).as_bytes();
    identity.primitives = *blake3::hash(
      &[b"IxBy/Flock/object-primitives/v0\0".as_slice(), &identity.primitives]
        .concat(),
    )
    .as_bytes();
    identity
  }

  fn with_values(
    profile: SemanticProfile,
    c: MachineCapacities,
    primitives: PrimitiveSet,
    nu: usize,
    params: &PcsParams,
    backend: Blake3Backend,
    byte_capacity: Option<ByteCapacity>,
  ) -> Self {
    let mut protocol = b"IxBy/Flock/protocol/v0\0".to_vec();
    protocol.extend_from_slice(UPSTREAM);
    protocol.extend_from_slice(if byte_capacity.is_some() {
      BYTE_TRANSCRIPT_DOMAIN
    } else {
      TRANSCRIPT_DOMAIN
    });
    // F128, Fast128, BLAKE3 Merkle, chained-BLAKE3 transcript.
    protocol.extend_from_slice(&[1, 1, 1, 1]);
    for n in [nu, params.m, params.log_batch_size, params.log_inv_rate] {
      protocol.extend_from_slice(&(n as u64).to_le_bytes());
    }
    protocol.push(u8::from(params.num_lanes.is_some()));
    protocol
      .extend_from_slice(&(params.num_lanes.unwrap_or(0) as u64).to_le_bytes());
    let mut capacity = if byte_capacity.is_some() {
      b"IxBy/Flock/byte-capacity/v0\0".to_vec()
    } else {
      b"IxBy/Flock/scalar-capacity/v0\0".to_vec()
    };
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
    if let Some(bytes) = byte_capacity {
      capacity.extend_from_slice(&(bytes.bytes() as u64).to_le_bytes());
      let entries = c.program.functions * c.program.blocks * c.program.operands
        + c.input.values
        + c.steps;
      capacity.extend_from_slice(&(entries as u64).to_le_bytes());
    }
    let mut registry = if byte_capacity.is_some() {
      b"IxBy/Flock/byte-primitives/v0\0".to_vec()
    } else {
      b"IxBy/Flock/scalar-primitives/v0\0".to_vec()
    };
    let opcodes: Vec<_> = primitives.opcodes().collect();
    registry.extend_from_slice(&(opcodes.len() as u32).to_le_bytes());
    registry.extend_from_slice(&opcodes);
    Self {
      protocol: *blake3::hash(&protocol).as_bytes(),
      implementation: *blake3::hash(match (byte_capacity, backend) {
        (None, Blake3Backend::LegacyOptionF) => IMPLEMENTATION,
        (None, Blake3Backend::PackedWordsV0) => PACKED_IMPLEMENTATION,
        (Some(_), Blake3Backend::LegacyOptionF) => {
          b"IxBy/Flock/fixed-byte-machine/v0"
        },
        (Some(_), Blake3Backend::PackedWordsV0) => {
          b"IxBy/Flock/fixed-byte-machine/packed-blake3/v0"
        },
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
