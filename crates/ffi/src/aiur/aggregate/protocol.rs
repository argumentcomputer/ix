//! Aggregation protocol.

use aiur::{G, function_channel};
use ix_common::address::Address;
use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};

pub(super) const CACHE_VERSION: u64 = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ChildKind {
  Ixvm,
  Aggr,
}

impl ChildKind {
  pub(super) const fn code(self) -> u8 {
    match self {
      Self::Ixvm => 0,
      Self::Aggr => 1,
    }
  }
}

pub(super) fn packed_digest(bytes: &[u8]) -> Vec<G> {
  let digest = blake3::hash(bytes);
  digest
    .as_bytes()
    .as_chunks::<4>()
    .0
    .iter()
    .map(|word| G::from_u32(u32::from_le_bytes(*word)))
    .collect()
}

pub(super) fn build_claim(fun_idx: usize, input: &[G], output: &[G]) -> Vec<G> {
  let mut claim = Vec::with_capacity(2 + input.len() + output.len());
  claim.push(function_channel());
  claim.push(G::from_usize(fun_idx));
  claim.extend_from_slice(input);
  claim.extend_from_slice(output);
  claim
}

pub(super) fn serialize_claims(claims: &[&[G]]) -> Vec<u8> {
  let mut out = Vec::new();
  out.extend_from_slice(&(claims.len() as u64).to_le_bytes());
  for claim in claims {
    out.extend_from_slice(&(claim.len() as u64).to_le_bytes());
    for value in *claim {
      out.extend_from_slice(&value.as_canonical_u64().to_le_bytes());
    }
  }
  out
}

pub(super) fn inner_claim(verify_idx: usize, claim_bytes: &[u8]) -> Vec<G> {
  build_claim(verify_idx, &packed_digest(claim_bytes), &[])
}

pub(super) fn aggregate_outer_claim(
  aggr_idx: usize,
  allowed: &[u8],
  claim_bytes: &[u8],
) -> Vec<G> {
  let mut input = packed_digest(allowed);
  input.extend(packed_digest(claim_bytes));
  build_claim(aggr_idx, &input, &[])
}

pub(super) fn allowed_blob(
  ixvm_vk: &[u8],
  verify_idx: usize,
  aggr_vk: &[u8],
  aggr_idx: usize,
) -> Vec<u8> {
  let mut out = Vec::with_capacity(80);
  out.extend_from_slice(blake3::hash(ixvm_vk).as_bytes());
  out.extend_from_slice(&(verify_idx as u64).to_le_bytes());
  out.extend_from_slice(blake3::hash(aggr_vk).as_bytes());
  out.extend_from_slice(&(aggr_idx as u64).to_le_bytes());
  out
}

pub(super) fn cache_key(
  aggr_vk: &[u8],
  cache_fri_bytes: &[u8],
  outer_claim: &[G],
) -> Address {
  let mut bytes = Vec::with_capacity(8 + 32 + cache_fri_bytes.len() + 256);
  bytes.extend_from_slice(&CACHE_VERSION.to_le_bytes());
  bytes.extend_from_slice(blake3::hash(aggr_vk).as_bytes());
  bytes.extend_from_slice(cache_fri_bytes);
  bytes.extend(serialize_claims(&[outer_claim]));
  Address::hash(&bytes)
}

pub(super) fn shape_code(left: ChildKind, right: Option<ChildKind>) -> u8 {
  match right {
    None => left.code(),
    Some(right) => 2 + 2 * left.code() + right.code(),
  }
}

pub(super) fn structural_shape_code(left: ChildKind, right: ChildKind) -> u8 {
  6 + 2 * left.code() + right.code()
}
