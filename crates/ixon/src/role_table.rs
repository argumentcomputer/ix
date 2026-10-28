//! Canonical E8 03 role-binding sections, matching IxC's `RoleTable` codec.
//!
//! This is wire validation only (`RoleTable.wireWF` in
//! `IxC/Kernel/Ixon/RoleTable.lean`). It neither authenticates the section nor
//! admits its roles/evidence. In particular, any byte-sized version, repeated
//! bound addresses, missing dependencies and unbound evidence can be canonical.
//! Semantic admission is a separate check. Bound packing uses this codec only
//! to select the artifact's actual role/evidence support addresses.

use ix_common::address::Address;

macro_rules! roles {
  ($($role:ident => $name:literal),+ $(,)?) => {
    /// Indices are IxC's `Role.all` order, independent of native primitive pins.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(u8)]
    pub enum Role { $($role),+ }

    impl Role {
      pub const ALL: [Self; 103] = [$(Self::$role),+];
      pub const fn index(self) -> u8 { self as u8 }
      pub fn from_index(index: u8) -> Option<Self> {
        Self::ALL.get(usize::from(index)).copied()
      }
      /// Source spelling, also checked against independently generated vectors.
      pub const fn lean_name(self) -> &'static str {
        match self { $(Self::$role => $name),+ }
      }
    }
  };
}

roles! {
  Nat => "Nat",
  NatZero => "Nat.zero",
  NatSucc => "Nat.succ",
  NatRec => "Nat.rec",
  Bool => "Bool",
  BoolFalse => "Bool.false",
  BoolTrue => "Bool.true",
  BoolRec => "Bool.rec",
  Eq => "Eq",
  EqRefl => "Eq.refl",
  EqRec => "Eq.rec",
  PUnit => "PUnit",
  PUnitUnit => "PUnit.unit",
  PUnitRec => "PUnit.rec",
  Empty => "Empty",
  EmptyRec => "Empty.rec",
  False => "False",
  FalseRec => "False.rec",
  True => "True",
  TrueIntro => "True.intro",
  And => "And",
  AndIntro => "And.intro",
  AndRec => "And.rec",
  Iff => "Iff",
  IffIntro => "Iff.intro",
  IffRec => "Iff.rec",
  Nonempty => "Nonempty",
  NonemptyIntro => "Nonempty.intro",
  NonemptyRec => "Nonempty.rec",
  List => "List",
  ListNil => "List.nil",
  ListCons => "List.cons",
  Quot => "Quot",
  QuotMk => "Quot.mk",
  QuotLift => "Quot.lift",
  QuotInd => "Quot.ind",
  QuotSound => "Quot.sound",
  String => "String",
  StringOfList => "String.ofList",
  Char => "Char",
  CharOfNat => "Char.ofNat",
  NatPred => "Nat.pred",
  NatAdd => "Nat.add",
  NatSub => "Nat.sub",
  NatMul => "Nat.mul",
  NatPow => "Nat.pow",
  NatBeq => "Nat.beq",
  NatBle => "Nat.ble",
  NatDiv => "Nat.div",
  NatMod => "Nat.mod",
  NatGcd => "Nat.gcd",
  NatLand => "Nat.land",
  NatLor => "Nat.lor",
  NatXor => "Nat.xor",
  NatShiftLeft => "Nat.shiftLeft",
  NatShiftRight => "Nat.shiftRight",
  Propext => "propext",
  Choice => "Classical.choice",
  SorryAx => "sorryAx",
  Decidable => "Decidable",
  DecidableIsTrue => "Decidable.isTrue",
  DecidableIsFalse => "Decidable.isFalse",
  Not => "Not",
  OfDecideEqTrue => "of_decide_eq_true",
  OfDecideEqFalse => "of_decide_eq_false",
  DecidableDecide => "Decidable.decide",
  NatLe => "Nat.le",
  NatDecEq => "Nat.decEq",
  NatDecLe => "Nat.decLe",
  NatDecLt => "Nat.decLt",
  Int => "Int",
  IntOfNat => "Int.ofNat",
  IntNegSucc => "Int.negSucc",
  IntNegOfNat => "Int.negOfNat",
  IntSubNatNat => "Int.subNatNat",
  IntNeg => "Int.neg",
  IntAdd => "Int.add",
  IntSub => "Int.sub",
  IntMul => "Int.mul",
  IntNatAbs => "Int.natAbs",
  IntEdiv => "Int.ediv",
  IntEmod => "Int.emod",
  IntPow => "Int.pow",
  BitVec => "BitVec",
  BitVecOfNat => "BitVec.ofNat",
  BitVecToNat => "BitVec.toNat",
  BitVecUlt => "BitVec.ult",
  StringDecEq => "String.decEq",
  ByteArray => "ByteArray",
  ByteArrayEmpty => "ByteArray.empty",
  StringToByteArray => "String.toByteArray",
  ListAppend => "List.append",
  StringAppend => "String.append",
  IfThenElse => "ite",
  IntLe => "Int.le",
  IntDecEq => "Int.decEq",
  IntDecLe => "Int.decLe",
  IntDecLt => "Int.decLt",
  IntBmod => "Int.bmod",
  IntBdiv => "Int.bdiv",
  CharUtf8Size => "Char.utf8Size",
  StringUtf8ByteSize => "String.utf8ByteSize",
  StringBack => "String.back",
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Evidence {
  DefEq,
  Proof(Address),
}

/// A wire table; construction does not assert canonicality or admission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoleTable {
  pub version: u8,
  pub bound: Vec<(Role, Address)>,
  pub evidence: Vec<(Role, Vec<Evidence>)>,
}

fn byte_count(len: usize) -> Result<u8, String> {
  u8::try_from(len)
    .map_err(|error| format!("role table: count exceeds 255: {error}"))
}

fn ascending<T>(entries: &[(Role, T)]) -> Result<(), String> {
  if entries.windows(2).any(|p| p[0].0 >= p[1].0) {
    Err("role table: roles are not strictly ascending".into())
  } else {
    Ok(())
  }
}

fn byte(input: &mut &[u8]) -> Result<u8, String> {
  let (b, rest) = input.split_first().ok_or("role table: truncated byte")?;
  *input = rest;
  Ok(*b)
}

fn role(input: &mut &[u8]) -> Result<Role, String> {
  Role::from_index(byte(input)?)
    .ok_or_else(|| "role table: unknown role".into())
}

fn address(input: &mut &[u8]) -> Result<Address, String> {
  let (bytes, rest) =
    input.split_at_checked(32).ok_or("role table: truncated address")?;
  let address = Address::from_slice(bytes).map_err(|e| e.to_string())?;
  *input = rest;
  Ok(address)
}

impl RoleTable {
  /// Exact counterpart of IxC's wireWF; Address and version widths are typed.
  pub fn check_wire(&self) -> Result<(), String> {
    byte_count(self.bound.len())?;
    byte_count(self.evidence.len())?;
    ascending(&self.bound)?;
    ascending(&self.evidence)?;
    for (_, es) in &self.evidence {
      byte_count(es.len())?;
    }
    Ok(())
  }

  /// Serialize canonical data without sorting, dropping or truncating entries.
  pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
    self.check_wire()?;
    let mut out = vec![0xe8, 0x03, self.version, byte_count(self.bound.len())?];
    for (r, a) in &self.bound {
      out.push(r.index());
      out.extend_from_slice(a.as_bytes());
    }
    out.push(byte_count(self.evidence.len())?);
    for (r, es) in &self.evidence {
      out.extend_from_slice(&[r.index(), byte_count(es.len())?]);
      for e in es {
        match e {
          Evidence::DefEq => out.push(0),
          Evidence::Proof(a) => {
            out.push(1);
            out.extend_from_slice(a.as_bytes());
          },
        }
      }
    }
    Ok(out)
  }

  /// Decode exactly one canonical section, consuming all bytes.
  pub fn from_bytes(mut input: &[u8]) -> Result<Self, String> {
    if byte(&mut input)? != 0xe8 || byte(&mut input)? != 0x03 {
      return Err("role table: expected E8 03".into());
    }
    let version = byte(&mut input)?;
    let n = byte(&mut input)?;
    let mut bound = Vec::with_capacity(usize::from(n));
    for _ in 0..n {
      bound.push((role(&mut input)?, address(&mut input)?));
    }
    let m = byte(&mut input)?;
    let mut evidence = Vec::with_capacity(usize::from(m));
    for _ in 0..m {
      let r = role(&mut input)?;
      let k = byte(&mut input)?;
      let mut es = Vec::with_capacity(usize::from(k));
      for _ in 0..k {
        es.push(match byte(&mut input)? {
          0 => Evidence::DefEq,
          1 => Evidence::Proof(address(&mut input)?),
          _ => return Err("role table: unknown evidence tag".into()),
        });
      }
      evidence.push((r, es));
    }
    if !input.is_empty() {
      return Err("role table: trailing bytes".into());
    }
    let table = Self { version, bound, evidence };
    table.check_wire()?;
    Ok(table)
  }
}

#[cfg(test)]
mod tests;
