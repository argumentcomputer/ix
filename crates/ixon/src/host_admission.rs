//! Separate IXHC/version1 host admission statement codec.
//!
//! Decoding is transport only. It neither admits an artifact nor certifies a
//! source value. The Lean host verifier authenticates these bytes and replays
//! actual logical/tier admission before accepting the commitments.

use ix_common::address::Address;

use crate::env::Env;
use crate::serialize::get_u8;

pub const MAGIC: &[u8; 4] = b"IXHC";
pub const VERSION: u8 = 1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind {
  Logical,
  Tiered { logical_root: Option<Address>, tier_root: Option<Address> },
}

/// Tier axioms are typed over an opaque scope, with no logical model for
/// them. Neither kind permits external artifact assumptions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Policy {
  NoExternalArtifactAssumptions,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Statement {
  pub kind: Kind,
  pub host_spec_digest: Address,
  pub binding_hash: Address,
  pub content_root: Address,
  pub main: Option<Address>,
  pub policy: Policy,
}

fn put_option(value: &Option<Address>, out: &mut Vec<u8>) {
  match value {
    None => out.push(0),
    Some(address) => {
      out.push(1);
      out.extend_from_slice(address.as_bytes());
    },
  }
}

fn get_address(input: &mut &[u8]) -> Result<Address, String> {
  let (bytes, rest) =
    input.split_at_checked(32).ok_or("host statement: truncated address")?;
  *input = rest;
  Address::from_slice(bytes)
    .map_err(|error| format!("host statement: invalid address width: {error}"))
}

fn get_option(input: &mut &[u8]) -> Result<Option<Address>, String> {
  match get_u8(input)? {
    0 => Ok(None),
    1 => Ok(Some(get_address(input)?)),
    _ => Err("host statement: invalid optional-root tag".to_owned()),
  }
}

impl Statement {
  /// Fixed-width encoding, separate from shared Claim/Proof format4.
  pub fn to_bytes(&self) -> Vec<u8> {
    let mut out = Vec::with_capacity(203);
    out.extend_from_slice(MAGIC);
    out.extend_from_slice(&[
      VERSION,
      Env::OBJECT_FORMAT,
      match self.kind {
        Kind::Logical => 0,
        Kind::Tiered { .. } => 1,
      },
      match self.policy {
        Policy::NoExternalArtifactAssumptions => 0,
      },
    ]);
    out.extend_from_slice(self.host_spec_digest.as_bytes());
    out.extend_from_slice(self.binding_hash.as_bytes());
    out.extend_from_slice(self.content_root.as_bytes());
    put_option(&self.main, &mut out);
    if let Kind::Tiered { logical_root, tier_root } = &self.kind {
      put_option(logical_root, &mut out);
      put_option(tier_root, &mut out);
    }
    out
  }

  /// Parse exactly one canonical statement. No stored success marker exists.
  pub fn decode(bytes: &[u8]) -> Result<Self, String> {
    let (magic, mut input) =
      bytes.split_at_checked(4).ok_or("host statement: truncated magic")?;
    if magic != MAGIC {
      return Err("host statement: expected IXHC".to_owned());
    }
    if get_u8(&mut input)? != VERSION {
      return Err("host statement: unsupported version".to_owned());
    }
    if get_u8(&mut input)? != Env::OBJECT_FORMAT {
      return Err(
        "host statement: unsupported checked object format".to_owned(),
      );
    }
    let kind = get_u8(&mut input)?;
    if kind > 1 {
      return Err("host statement: unknown admission kind".to_owned());
    }
    if get_u8(&mut input)? != 0 {
      return Err(
        "host statement: unsupported external-assumption policy".to_owned(),
      );
    }
    let host_spec_digest = get_address(&mut input)?;
    let binding_hash = get_address(&mut input)?;
    let content_root = get_address(&mut input)?;
    let main = get_option(&mut input)?;
    let kind = if kind == 0 {
      Kind::Logical
    } else {
      Kind::Tiered {
        logical_root: get_option(&mut input)?,
        tier_root: get_option(&mut input)?,
      }
    };
    if !input.is_empty() {
      return Err("host statement: trailing bytes".to_owned());
    }
    Ok(Self {
      kind,
      host_spec_digest,
      binding_hash,
      content_root,
      main,
      policy: Policy::NoExternalArtifactAssumptions,
    })
  }

  pub fn address(&self) -> Address {
    Address::hash(&self.to_bytes())
  }
}
