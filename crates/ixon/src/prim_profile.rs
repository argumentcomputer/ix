//! The primitive profile: which declarations play the checker's pinned
//! roles, as a canonical Ixon object with an address.
//!
//! A role (string literal type, `Nat.add`, the `Quot` constants, ...) is
//! identified by its position in `ROLE_NAMES`; the profile is the list of
//! the addresses bound to those roles, in that order, without the
//! synthetic reduction marker, which is not a Lean declaration. Two
//! toolchains that bind the same declarations produce byte-identical
//! profiles and so the same address. The object format version is part of
//! the bytes because addresses are only meaningful within one format.
//!
//! Wire layout, under the claim flag like every other standalone object:
//!
//! ```text
//! [TagN(0xE, 10) = E8 02] [OBJECT_FORMAT : u8] [count : TagN] [addr : 32 bytes] * count
//! ```

use ix_common::address::Address;
use ix_common::env::Name;
use ix_common::prim_addrs::{MARKER_ROLE, PrimAddrs, ROLE_NAMES};

use crate::env::Env;
use crate::proof::{FLAG_CLAIM, VARIANT_PRIM_PROFILE};
use crate::tag::TagN;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimProfile {
  /// One address per role in `PrimProfile::role_names()` order.
  pub addrs: Vec<Address>,
}

/// A dotted Lean name as the compiler registers it in an `.ixe`.
fn dotted_name(s: &str) -> Name {
  s.split('.').fold(Name::anon(), |pre, part| Name::str(pre, part.to_string()))
}

impl PrimProfile {
  /// The roles a profile binds, in wire order.
  pub fn role_names() -> impl Iterator<Item = &'static str> {
    ROLE_NAMES.iter().copied().filter(|n| *n != MARKER_ROLE)
  }

  pub fn from_addrs(a: &PrimAddrs) -> Self {
    let addrs = a
      .roles()
      .into_iter()
      .filter(|(name, _)| *name != MARKER_ROLE)
      .map(|(_, addr)| addr)
      .collect();
    PrimProfile { addrs }
  }

  pub fn to_addrs(&self) -> Result<PrimAddrs, String> {
    let expected = Self::role_names().count();
    if self.addrs.len() != expected {
      return Err(format!(
        "primitive profile binds {} roles, this build knows {expected}",
        self.addrs.len()
      ));
    }
    PrimAddrs::from_roles(
      Self::role_names().map(str::to_string).zip(self.addrs.iter().cloned()),
    )
  }

  /// Bind every role through `lookup`, which resolves a Lean name to the
  /// address registered under it. Fails naming every role that did not
  /// resolve, so a partial environment is reported rather than guessed.
  pub fn from_lookup<F>(mut lookup: F) -> Result<Self, String>
  where
    F: FnMut(&Name) -> Option<Address>,
  {
    let mut addrs = Vec::new();
    let mut missing = Vec::new();
    for role in Self::role_names() {
      match lookup(&dotted_name(role)) {
        Some(addr) => addrs.push(addr),
        None => missing.push(role),
      }
    }
    if !missing.is_empty() {
      return Err(format!(
        "environment does not register the primitive roles: {}",
        missing.join(", ")
      ));
    }
    Ok(PrimProfile { addrs })
  }

  /// The profile of the toolchain that produced `env`, read from its
  /// named section.
  pub fn from_env(env: &Env) -> Result<Self, String> {
    Self::from_lookup(|name| env.lookup_name(name).map(|named| named.addr))
  }

  pub fn put(&self, buf: &mut Vec<u8>) {
    TagN::put(4, FLAG_CLAIM, VARIANT_PRIM_PROFILE, buf);
    buf.push(Env::OBJECT_FORMAT);
    TagN::put(0, 0, self.addrs.len() as u64, buf);
    for addr in &self.addrs {
      buf.extend_from_slice(addr.as_bytes());
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let tag = TagN::get(4, buf)?;
    if tag.flag != FLAG_CLAIM || tag.value != VARIANT_PRIM_PROFILE {
      return Err(format!(
        "PrimProfile::get: expected header {{0xE, {VARIANT_PRIM_PROFILE}}}, got {{{}, {}}}",
        tag.flag, tag.value
      ));
    }
    let (format, rest) =
      buf.split_first().ok_or("PrimProfile::get: EOF reading format")?;
    *buf = rest;
    if *format != Env::OBJECT_FORMAT {
      return Err(format!(
        "PrimProfile::get: object format {format}, expected {} — regenerate the profile",
        Env::OBJECT_FORMAT
      ));
    }
    let count = TagN::get(0, buf)?.value;
    let count = usize::try_from(count)
      .map_err(|e| format!("PrimProfile::get: count overflow: {e}"))?;
    if buf.len() < count.saturating_mul(32) {
      return Err(format!(
        "PrimProfile::get: {count} addresses need {} bytes, have {}",
        count * 32,
        buf.len()
      ));
    }
    let mut addrs = Vec::with_capacity(count);
    for _ in 0..count {
      let (head, rest) = buf.split_at(32);
      *buf = rest;
      let addr = Address::from_slice(head)
        .map_err(|e| format!("PrimProfile::get: invalid address: {e:?}"))?;
      addrs.push(addr);
    }
    Ok(PrimProfile { addrs })
  }

  pub fn ser(&self) -> Vec<u8> {
    let mut buf = Vec::new();
    self.put(&mut buf);
    buf
  }

  /// Serialize and content-address: the store key of this profile.
  pub fn commit(&self) -> (Address, Vec<u8>) {
    let bytes = self.ser();
    (Address::hash(&bytes), bytes)
  }

  pub fn address(&self) -> Address {
    self.commit().0
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::env::Named;

  #[test]
  fn builtin_round_trips_through_addrs() {
    let builtin = PrimAddrs::new();
    let profile = PrimProfile::from_addrs(&builtin);
    assert_eq!(profile.addrs.len(), PrimProfile::role_names().count());
    let back = profile.to_addrs().unwrap();
    assert_eq!(back.roles(), builtin.roles());
  }

  #[test]
  fn bytes_round_trip_and_address_is_stable() {
    let profile = PrimProfile::from_addrs(&PrimAddrs::new());
    let (addr, bytes) = profile.commit();
    assert_eq!(bytes[0], 0xE8, "claim-flag header, rung 2");
    assert_eq!(bytes[1], 0x02, "variant 10 in rung 2");
    assert_eq!(bytes[2], Env::OBJECT_FORMAT);
    let mut cursor = &bytes[..];
    let decoded = PrimProfile::get(&mut cursor).unwrap();
    assert!(cursor.is_empty());
    assert_eq!(decoded, profile);
    assert_eq!(decoded.address(), addr);
  }

  #[test]
  fn a_changed_binding_changes_the_address() {
    let builtin = PrimAddrs::new();
    let mut other = builtin.clone();
    other.string = builtin.nat.clone();
    assert_ne!(
      PrimProfile::from_addrs(&other).address(),
      PrimProfile::from_addrs(&builtin).address()
    );
  }

  #[test]
  fn rejects_other_formats_and_short_input() {
    let mut bytes = PrimProfile::from_addrs(&PrimAddrs::new()).ser();
    bytes[2] = bytes[2].wrapping_add(1);
    assert!(
      PrimProfile::get(&mut &bytes[..]).unwrap_err().contains("object format")
    );
    let bytes = PrimProfile::from_addrs(&PrimAddrs::new()).ser();
    assert!(PrimProfile::get(&mut &bytes[..bytes.len() - 1]).is_err());
    let wrong_count = PrimProfile { addrs: vec![PrimAddrs::new().nat] };
    assert!(wrong_count.to_addrs().unwrap_err().contains("roles"));
  }

  #[test]
  fn from_env_reads_the_named_section_and_reports_gaps() {
    let builtin = PrimAddrs::new();
    let env = Env::new();
    for (name, addr) in builtin.roles() {
      if name == MARKER_ROLE {
        continue;
      }
      env.register_name(dotted_name(name), Named::with_addr(addr));
    }
    let profile = PrimProfile::from_env(&env).unwrap();
    assert_eq!(profile, PrimProfile::from_addrs(&builtin));

    let partial = Env::new();
    partial.register_name(dotted_name("Nat"), Named::with_addr(builtin.nat));
    let err = PrimProfile::from_env(&partial).unwrap_err();
    assert!(err.contains("Nat.zero") && !err.contains("eagerReduce"));
  }
}
