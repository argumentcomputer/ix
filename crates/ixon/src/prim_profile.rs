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
//! [TagN(0xE, 10) = E8 02] [OBJECT_FORMAT : u8] [SCHEMA_VERSION : u8] [count : TagN]
//! ([present : u8] [addr : 32 bytes if present]) * count
//! ```

use ix_common::address::Address;
use ix_common::env::Name;
use ix_common::prim_addrs::{
  MARKER_ROLE, PrimAddrs, ROLE_NAMES, absent_role_address, reserved_marker_name,
};

use crate::env::Env;
use crate::proof::{FLAG_CLAIM, VARIANT_PRIM_PROFILE};
use crate::tag::TagN;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimProfile {
  /// Optional bindings in `PrimProfile::role_names()` order.
  pub addrs: Vec<Option<Address>>,
}

/// A dotted Lean name as the compiler registers it in an `.ixe`.
fn dotted_name(s: &str) -> Name {
  s.split('.').fold(Name::anon(), |pre, part| Name::str(pre, part.to_string()))
}

impl PrimProfile {
  pub const SCHEMA_VERSION: u8 = 1;
  /// The roles a profile binds, in wire order.
  pub fn role_names() -> impl Iterator<Item = &'static str> {
    ROLE_NAMES.iter().copied().filter(|n| *n != MARKER_ROLE)
  }

  pub fn from_addrs(a: &PrimAddrs) -> Self {
    let addrs = a
      .roles()
      .into_iter()
      .filter(|(name, _)| *name != MARKER_ROLE)
      .map(|(role, addr)| (addr != absent_role_address(role)).then_some(addr))
      .collect();
    PrimProfile { addrs }
  }

  pub fn to_addrs(&self) -> Result<PrimAddrs, String> {
    self.validate()?;
    PrimAddrs::from_roles(Self::role_names().zip(&self.addrs).map(
      |(role, addr)| {
        (
          role.to_string(),
          addr.clone().unwrap_or_else(|| absent_role_address(role)),
        )
      },
    ))
  }

  /// Resolve available declarations by name. Missing roles remain absent;
  /// the checker requires support only when a corresponding rule is used.
  pub fn from_lookup<F>(mut lookup: F) -> Result<Self, String>
  where
    F: FnMut(&Name) -> Option<Address>,
  {
    let profile = Self {
      addrs: Self::role_names()
        .map(|role| lookup(&dotted_name(role)))
        .collect(),
    };
    profile.validate()?;
    Ok(profile)
  }

  fn validate(&self) -> Result<(), String> {
    let expected = Self::role_names().count();
    if self.addrs.len() != expected {
      return Err(format!(
        "primitive profile binds {} roles, expected {expected}",
        self.addrs.len()
      ));
    }
    for (role, addr) in Self::role_names().zip(&self.addrs) {
      if addr.as_ref().is_some_and(|a| reserved_marker_name(a).is_some()) {
        return Err(format!("primitive role {role} binds a reserved marker"));
      }
    }
    Ok(())
  }

  /// Parse a complete canonical profile object, including schema and arity.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    let mut cursor = bytes;
    let profile = Self::get(&mut cursor)?;
    if !cursor.is_empty() {
      return Err("primitive profile: trailing bytes".into());
    }
    profile.validate()?;
    if profile.ser() != bytes {
      return Err("primitive profile: noncanonical encoding".into());
    }
    Ok(profile)
  }

  /// The profile of the toolchain that produced `env`, read from its
  /// named section.
  pub fn from_env(env: &Env) -> Result<Self, String> {
    Self::from_lookup(|name| env.lookup_name(name).map(|named| named.addr))
  }

  pub fn put(&self, buf: &mut Vec<u8>) {
    TagN::put(4, FLAG_CLAIM, VARIANT_PRIM_PROFILE, buf);
    buf.push(Env::OBJECT_FORMAT);
    buf.push(Self::SCHEMA_VERSION);
    TagN::put(0, 0, self.addrs.len() as u64, buf);
    for addr in &self.addrs {
      buf.push(u8::from(addr.is_some()));
      if let Some(addr) = addr {
        buf.extend_from_slice(addr.as_bytes());
      }
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
    let (schema, rest) =
      buf.split_first().ok_or("primitive profile: missing schema")?;
    *buf = rest;
    if *schema != Self::SCHEMA_VERSION {
      return Err(format!(
        "primitive profile schema {schema}, expected {} — regenerate the profile",
        Self::SCHEMA_VERSION
      ));
    }
    let count = TagN::get(0, buf)?.value;
    let expected = Self::role_names().count();
    if count != expected as u64 {
      return Err(format!(
        "primitive profile binds {count} roles, expected {expected}"
      ));
    }
    let mut addrs = Vec::with_capacity(expected);
    for _ in 0..expected {
      let (present, rest) =
        buf.split_first().ok_or("primitive profile: missing presence tag")?;
      *buf = rest;
      match present {
        0 => addrs.push(None),
        1 => {
          if buf.len() < 32 {
            return Err("primitive profile: truncated address".into());
          }
          let (head, rest) = buf.split_at(32);
          *buf = rest;
          addrs.push(Some(
            Address::from_slice(head)
              .map_err(|e| format!("invalid address: {e:?}"))?,
          ));
        },
        _ => {
          return Err(format!(
            "primitive profile: invalid presence tag {present}"
          ));
        },
      }
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
    assert_eq!(PrimProfile::from_bytes(&bytes).unwrap(), profile);
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
    let wrong_count = PrimProfile { addrs: vec![Some(PrimAddrs::new().nat)] };
    assert!(wrong_count.to_addrs().unwrap_err().contains("roles"));
  }

  #[test]
  fn from_env_reads_the_named_section_and_preserves_absence() {
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
    let partial = PrimProfile::from_env(&partial).unwrap();
    assert_eq!(partial.addrs.iter().filter(|a| a.is_some()).count(), 1);
    let resolved = partial.to_addrs().unwrap();
    assert_eq!(resolved.nat_zero, absent_role_address("Nat.zero"));
    assert_eq!(PrimProfile::from_addrs(&resolved), partial);
  }
  #[test]
  fn whole_object_loader_rejects_junk_wrong_schema_and_counts() {
    let profile = PrimProfile::from_addrs(&PrimAddrs::new());
    let mut bytes = profile.ser();
    bytes.extend_from_slice(b"junk");
    assert!(PrimProfile::from_bytes(&bytes).unwrap_err().contains("trailing"));
    let mut bytes = profile.ser();
    bytes[3] = 0;
    assert!(PrimProfile::from_bytes(&bytes).unwrap_err().contains("schema"));
    for count in [0, 1, u64::MAX] {
      let mut bytes = profile.ser()[..4].to_vec();
      TagN::put(0, 0, count, &mut bytes);
      assert!(PrimProfile::from_bytes(&bytes).unwrap_err().contains("roles"));
    }
    let mut bytes = profile.ser();
    bytes[5] = 2;
    assert!(PrimProfile::from_bytes(&bytes).unwrap_err().contains("presence"));
  }

  #[test]
  fn unavailable_operations_stay_absent_without_old_version_fallback() {
    let a = PrimAddrs::new();
    let retired = ["Lean.reduceBool", "Lean.reduceNat", "String.Legacy.back"];
    let profile = PrimProfile::from_lookup(|name| {
      a.roles()
        .into_iter()
        .find(|(role, _)| !retired.contains(role) && dotted_name(role) == *name)
        .map(|(_, a)| a)
    })
    .unwrap();
    assert_eq!(profile.addrs.iter().filter(|a| a.is_none()).count(), 3);
    let resolved = profile.to_addrs().unwrap();
    assert_ne!(resolved.reduce_nat, a.reduce_nat);
    assert_ne!(resolved.reduce_nat, resolved.reduce_bool);
    assert!(reserved_marker_name(&resolved.reduce_nat).is_some());
    assert_eq!(PrimProfile::from_bytes(&profile.ser()).unwrap(), profile);
  }

  #[test]
  fn explicit_reserved_addresses_are_not_bindings() {
    let mut a = PrimAddrs::new();
    a.nat_add = a.eager_reduce.clone();
    let profile = PrimProfile::from_addrs(&a);
    assert!(profile.to_addrs().is_err());
    assert!(PrimProfile::from_bytes(&profile.ser()).is_err());
  }
}
