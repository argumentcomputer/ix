//! The `ix_aggr` shapes, shared by every backend (`Ix/Aggr/Protocol.lean`).

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChildKind {
  Ixvm,
  Aggr,
}

impl ChildKind {
  pub const fn code(self) -> u8 {
    match self {
      Self::Ixvm => 0,
      Self::Aggr => 1,
    }
  }
}

pub fn shape_code(left: ChildKind, right: Option<ChildKind>) -> u8 {
  match right {
    None => left.code(),
    Some(right) => 2 + 2 * left.code() + right.code(),
  }
}

pub fn structural_shape_code(left: ChildKind, right: ChildKind) -> u8 {
  6 + 2 * left.code() + right.code()
}

/// Shapes 13 and 14 (`Aggr.dischargeShapeCode`): a child that assumes its
/// role binding, and in slot 1 an IxVM proof of the `Binding` claim.
pub fn discharge_shape_code(child: ChildKind) -> u8 {
  13 + child.code()
}

/// Shape 15 (`Aggr.crossBindingShapeCode`): the structural fold of two
/// unconditional `CheckEnv` claims under their common literal class.
pub const CROSS_BINDING_SHAPE: u8 = 15;

/// Shape 16 (`Aggr.catalogShapeCode`): the join of two claims of different
/// literal classes, or of catalogs, into a `Catalog` claim.
pub const CATALOG_SHAPE: u8 = 16;

/// The packed Blake3 digest of `bytes`: eight little-endian `u32` words
/// (`MultiStark.digestGs`).
pub fn packed_digest(bytes: &[u8]) -> Vec<u64> {
  crate::streams::digest_key(bytes)
}

/// `MultiStark.serializeClaims`: the claim count, then each claim's
/// length and canonical words, all `u64` little-endian.
pub fn serialize_claims(claims: &[&[u64]]) -> Vec<u8> {
  let mut out = Vec::new();
  out.extend_from_slice(&(claims.len() as u64).to_le_bytes());
  for claim in claims {
    out.extend_from_slice(&(claim.len() as u64).to_le_bytes());
    for word in *claim {
      out.extend_from_slice(&word.to_le_bytes());
    }
  }
  out
}

/// `Aggr.allowedBlob`: both verifying-key digests with their entry indices.
pub fn allowed_blob(
  ixvm_key: &[u8],
  ixvm_index: u64,
  aggr_key: &[u8],
  aggr_index: u64,
) -> Vec<u8> {
  let mut out = Vec::with_capacity(80);
  out.extend_from_slice(blake3::hash(ixvm_key).as_bytes());
  out.extend_from_slice(&ixvm_index.to_le_bytes());
  out.extend_from_slice(blake3::hash(aggr_key).as_bytes());
  out.extend_from_slice(&aggr_index.to_le_bytes());
  out
}

/// The version of the aggregate cache-key layout.
pub const CACHE_VERSION: u64 = 2;

/// The claims and cache keys of a proof system whose claims are canonical
/// field words: the call channel, the entry index, then the packed digest
/// of the claim (IxVM) or of the identity blob and the claim (`ix_aggr`).
pub struct WordIdentity {
  /// The call namespace of both entries: 0 in legacy Aiur, 1 in formal.
  pub channel: u64,
  pub ixvm_index: u64,
  pub aggr_index: u64,
  pub allowed: Vec<u8>,
  aggr_key_digest: [u8; 32],
  /// The FRI parameters of `ix_aggr` proofs, which the verifying key does
  /// not bind, so a cache entry from other parameters is never reused.
  fri_bytes: Vec<u8>,
}

impl WordIdentity {
  pub fn new(
    channel: u64,
    ixvm_key: &[u8],
    ixvm_index: u64,
    aggr_key: &[u8],
    aggr_index: u64,
    fri_bytes: Vec<u8>,
  ) -> Self {
    Self {
      channel,
      ixvm_index,
      aggr_index,
      allowed: allowed_blob(ixvm_key, ixvm_index, aggr_key, aggr_index),
      aggr_key_digest: *blake3::hash(aggr_key).as_bytes(),
      fri_bytes,
    }
  }
}

impl crate::backend::Identity for WordIdentity {
  type Claim = Vec<u64>;

  fn outer_claim(&self, kind: ChildKind, claim_bytes: &[u8]) -> Vec<u64> {
    let mut claim = vec![self.channel];
    match kind {
      ChildKind::Ixvm => claim.push(self.ixvm_index),
      ChildKind::Aggr => {
        claim.push(self.aggr_index);
        claim.extend(packed_digest(&self.allowed));
      },
    }
    claim.extend(packed_digest(claim_bytes));
    claim
  }

  fn claims_bytes(&self, outer: &Vec<u64>) -> Vec<u8> {
    serialize_claims(&[outer])
  }

  fn cache_key(&self, outer: &Vec<u64>) -> ix_common::address::Address {
    let mut bytes = Vec::with_capacity(8 + 32 + self.fri_bytes.len() + 256);
    bytes.extend_from_slice(&CACHE_VERSION.to_le_bytes());
    bytes.extend_from_slice(&self.aggr_key_digest);
    bytes.extend_from_slice(&self.fri_bytes);
    bytes.extend(serialize_claims(&[outer]));
    ix_common::address::Address::hash(&bytes)
  }
}
