//! Proof and claim types for ZK verification.

use crate::ix::address::Address;
use crate::ix::env::{DefinitionSafety, QuotKind};

use super::constant::DefKind;
use super::tag::{Tag0, Tag4};

// ============================================================================
// Core claim/proof types
// ============================================================================

/// An evaluation claim: asserts that the constant at `input` evaluates to the
/// constant at `output`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct EvalClaim {
  /// Address of the input constant
  pub input: Address,
  /// Address of the output constant
  pub output: Address,
}

/// A type-checking claim: asserts that the constant at `value` is well-typed.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CheckClaim {
  /// Address of the value constant
  pub value: Address,
}

// ============================================================================
// RevealClaim types
// ============================================================================

/// Revealed fields of a Constructor within an Inductive.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RevealConstructorInfo {
  pub is_unsafe: Option<bool>,
  pub lvls: Option<u64>,
  pub cidx: Option<u64>,
  pub params: Option<u64>,
  pub fields: Option<u64>,
  /// blake3(serialized typ Expr)
  pub typ: Option<Address>,
}

/// Revealed fields of a RecursorRule.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RevealRecursorRule {
  pub rule_idx: u64,
  pub fields: u64,
  /// blake3(serialized rhs Expr)
  pub rhs: Address,
}

/// Revealed fields of a MutConst component.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RevealMutConstInfo {
  Defn {
    kind: Option<DefKind>,
    safety: Option<DefinitionSafety>,
    lvls: Option<u64>,
    typ: Option<Address>,
    value: Option<Address>,
  },
  Indc {
    recr: Option<bool>,
    refl: Option<bool>,
    is_unsafe: Option<bool>,
    lvls: Option<u64>,
    params: Option<u64>,
    indices: Option<u64>,
    nested: Option<u64>,
    typ: Option<Address>,
    ctors: Option<Vec<(u64, RevealConstructorInfo)>>,
  },
  Recr {
    k: Option<bool>,
    is_unsafe: Option<bool>,
    lvls: Option<u64>,
    params: Option<u64>,
    indices: Option<u64>,
    motives: Option<u64>,
    minors: Option<u64>,
    typ: Option<Address>,
    rules: Option<Vec<RevealRecursorRule>>,
  },
}

/// Revealed fields of a ConstantInfo behind a commitment.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RevealConstantInfo {
  Defn {
    kind: Option<DefKind>,
    safety: Option<DefinitionSafety>,
    lvls: Option<u64>,
    typ: Option<Address>,
    value: Option<Address>,
  },
  Recr {
    k: Option<bool>,
    is_unsafe: Option<bool>,
    lvls: Option<u64>,
    params: Option<u64>,
    indices: Option<u64>,
    motives: Option<u64>,
    minors: Option<u64>,
    typ: Option<Address>,
    rules: Option<Vec<RevealRecursorRule>>,
  },
  Axio {
    is_unsafe: Option<bool>,
    lvls: Option<u64>,
    typ: Option<Address>,
  },
  Quot {
    kind: Option<QuotKind>,
    lvls: Option<u64>,
    typ: Option<Address>,
  },
  CPrj {
    idx: Option<u64>,
    cidx: Option<u64>,
    block: Option<Address>,
  },
  RPrj {
    idx: Option<u64>,
    block: Option<Address>,
  },
  IPrj {
    idx: Option<u64>,
    block: Option<Address>,
  },
  DPrj {
    idx: Option<u64>,
    block: Option<Address>,
  },
  Muts {
    components: Vec<(u64, RevealMutConstInfo)>,
  },
}

/// A reveal claim: selective revelation of fields of a committed constant.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RevealClaim {
  /// Address of the commitment
  pub comm: Address,
  /// Revealed field information
  pub info: RevealConstantInfo,
}

// ============================================================================
// Claim and Proof enums
// ============================================================================

/// A claim that can be proven.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Claim {
  /// Evaluation claim
  Evals(EvalClaim),
  /// Type-checking claim
  Checks(CheckClaim),
  /// Reveal claim (selective field revelation)
  Reveals(RevealClaim),
}

/// A proof of a claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
  /// The claim being proven
  pub claim: Claim,
  /// The proof data (opaque bytes, e.g., ZK proof)
  pub proof: Vec<u8>,
}

// ============================================================================
// Tag4 variant layout for flag 0xE
// ============================================================================

/// Tag4 flag for claims, proofs, commitments, and environment (0xE).
/// Size field encodes variant:
/// - 0: Environment (Env)
/// - 1: CheckProof (proof of CheckClaim)
/// - 2: EvalProof (proof of EvalClaim)
/// - 3: CheckClaim (no proof)
/// - 4: EvalClaim (no proof)
/// - 5: Commitment
/// - 6: RevealClaim
/// - 7: RevealProof
pub const FLAG: u8 = 0xE;

const VARIANT_CHECK_PROOF: u64 = 1;
const VARIANT_EVAL_PROOF: u64 = 2;
const VARIANT_CHECK_CLAIM: u64 = 3;
const VARIANT_EVAL_CLAIM: u64 = 4;
// VARIANT 5 = Comm (handled in comm.rs)
const VARIANT_REVEAL_CLAIM: u64 = 6;
const VARIANT_REVEAL_PROOF: u64 = 7;

// ============================================================================
// Serialization helpers
// ============================================================================

fn get_address(buf: &mut &[u8]) -> Result<Address, String> {
  if buf.len() < 32 {
    return Err(format!("get_address: need 32 bytes, have {}", buf.len()));
  }
  let (bytes, rest) = buf.split_at(32);
  *buf = rest;
  Address::from_slice(bytes).map_err(|_e| "get_address: invalid".to_string())
}

fn get_u8(buf: &mut &[u8]) -> Result<u8, String> {
  match buf.split_first() {
    Some((&x, rest)) => {
      *buf = rest;
      Ok(x)
    },
    None => Err("get_u8: EOF".to_string()),
  }
}

fn compute_mask(flags: &[bool]) -> u64 {
  let mut mask: u64 = 0;
  for (i, &f) in flags.iter().enumerate() {
    if f {
      mask |= 1 << i;
    }
  }
  mask
}

fn put_def_kind(k: DefKind, buf: &mut Vec<u8>) {
  buf.push(match k {
    DefKind::Definition => 0,
    DefKind::Opaque => 1,
    DefKind::Theorem => 2,
  });
}

fn get_def_kind(buf: &mut &[u8]) -> Result<DefKind, String> {
  match get_u8(buf)? {
    0 => Ok(DefKind::Definition),
    1 => Ok(DefKind::Opaque),
    2 => Ok(DefKind::Theorem),
    x => Err(format!("get_def_kind: invalid {x}")),
  }
}

fn put_def_safety(s: DefinitionSafety, buf: &mut Vec<u8>) {
  buf.push(match s {
    DefinitionSafety::Unsafe => 0,
    DefinitionSafety::Safe => 1,
    DefinitionSafety::Partial => 2,
  });
}

fn get_def_safety(buf: &mut &[u8]) -> Result<DefinitionSafety, String> {
  match get_u8(buf)? {
    0 => Ok(DefinitionSafety::Unsafe),
    1 => Ok(DefinitionSafety::Safe),
    2 => Ok(DefinitionSafety::Partial),
    x => Err(format!("get_def_safety: invalid {x}")),
  }
}

fn put_quot_kind(k: QuotKind, buf: &mut Vec<u8>) {
  buf.push(match k {
    QuotKind::Type => 0,
    QuotKind::Ctor => 1,
    QuotKind::Lift => 2,
    QuotKind::Ind => 3,
  });
}

fn get_quot_kind(buf: &mut &[u8]) -> Result<QuotKind, String> {
  match get_u8(buf)? {
    0 => Ok(QuotKind::Type),
    1 => Ok(QuotKind::Ctor),
    2 => Ok(QuotKind::Lift),
    3 => Ok(QuotKind::Ind),
    x => Err(format!("get_quot_kind: invalid {x}")),
  }
}

fn put_bool_field(b: bool, buf: &mut Vec<u8>) {
  buf.push(u8::from(b));
}

fn get_bool_field(buf: &mut &[u8]) -> Result<bool, String> {
  match get_u8(buf)? {
    0 => Ok(false),
    1 => Ok(true),
    x => Err(format!("get_bool_field: invalid {x}")),
  }
}

// ============================================================================
// RevealConstructorInfo serialization
// ============================================================================

impl RevealConstructorInfo {
  /// Serialize: mask (Tag0) + field values in mask order.
  pub fn put(&self, buf: &mut Vec<u8>) {
    let mask = compute_mask(&[
      self.is_unsafe.is_some(),
      self.lvls.is_some(),
      self.cidx.is_some(),
      self.params.is_some(),
      self.fields.is_some(),
      self.typ.is_some(),
    ]);
    Tag0::new(mask).put(buf);
    if let Some(u) = self.is_unsafe {
      put_bool_field(u, buf);
    }
    if let Some(l) = self.lvls {
      Tag0::new(l).put(buf);
    }
    if let Some(c) = self.cidx {
      Tag0::new(c).put(buf);
    }
    if let Some(p) = self.params {
      Tag0::new(p).put(buf);
    }
    if let Some(f) = self.fields {
      Tag0::new(f).put(buf);
    }
    if let Some(t) = &self.typ {
      buf.extend_from_slice(t.as_bytes());
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let mask = Tag0::get(buf)?.size;
    let is_unsafe =
      if mask & 1 != 0 { Some(get_bool_field(buf)?) } else { None };
    let lvls =
      if mask & 2 != 0 { Some(Tag0::get(buf)?.size) } else { None };
    let cidx =
      if mask & 4 != 0 { Some(Tag0::get(buf)?.size) } else { None };
    let params =
      if mask & 8 != 0 { Some(Tag0::get(buf)?.size) } else { None };
    let fields =
      if mask & 16 != 0 { Some(Tag0::get(buf)?.size) } else { None };
    let typ =
      if mask & 32 != 0 { Some(get_address(buf)?) } else { None };
    Ok(RevealConstructorInfo { is_unsafe, lvls, cidx, params, fields, typ })
  }
}

// ============================================================================
// RevealRecursorRule serialization
// ============================================================================

impl RevealRecursorRule {
  pub fn put(&self, buf: &mut Vec<u8>) {
    Tag0::new(self.rule_idx).put(buf);
    Tag0::new(self.fields).put(buf);
    buf.extend_from_slice(self.rhs.as_bytes());
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let rule_idx = Tag0::get(buf)?.size;
    let fields = Tag0::get(buf)?.size;
    let rhs = get_address(buf)?;
    Ok(RevealRecursorRule { rule_idx, fields, rhs })
  }
}

// ============================================================================
// Helper: put/get rules and ctors arrays
// ============================================================================

fn put_rules(rules: &[RevealRecursorRule], buf: &mut Vec<u8>) {
  Tag0::new(rules.len() as u64).put(buf);
  for rule in rules {
    rule.put(buf);
  }
}

fn get_rules(buf: &mut &[u8]) -> Result<Vec<RevealRecursorRule>, String> {
  let count = Tag0::get(buf)?.size;
  let mut rules = Vec::with_capacity(count as usize);
  for _ in 0..count {
    rules.push(RevealRecursorRule::get(buf)?);
  }
  Ok(rules)
}

fn put_ctors(ctors: &[(u64, RevealConstructorInfo)], buf: &mut Vec<u8>) {
  Tag0::new(ctors.len() as u64).put(buf);
  for (idx, info) in ctors {
    Tag0::new(*idx).put(buf);
    info.put(buf);
  }
}

fn get_ctors(
  buf: &mut &[u8],
) -> Result<Vec<(u64, RevealConstructorInfo)>, String> {
  let count = Tag0::get(buf)?.size;
  let mut ctors = Vec::with_capacity(count as usize);
  for _ in 0..count {
    let idx = Tag0::get(buf)?.size;
    let info = RevealConstructorInfo::get(buf)?;
    ctors.push((idx, info));
  }
  Ok(ctors)
}

// ============================================================================
// RevealMutConstInfo serialization
// ============================================================================

impl RevealMutConstInfo {
  pub fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Defn { kind, safety, lvls, typ, value } => {
        buf.push(0);
        let mask = compute_mask(&[
          kind.is_some(),
          safety.is_some(),
          lvls.is_some(),
          typ.is_some(),
          value.is_some(),
        ]);
        Tag0::new(mask).put(buf);
        if let Some(k) = kind {
          put_def_kind(*k, buf);
        }
        if let Some(s) = safety {
          put_def_safety(*s, buf);
        }
        if let Some(l) = lvls {
          Tag0::new(*l).put(buf);
        }
        if let Some(t) = typ {
          buf.extend_from_slice(t.as_bytes());
        }
        if let Some(v) = value {
          buf.extend_from_slice(v.as_bytes());
        }
      },
      Self::Indc {
        recr,
        refl,
        is_unsafe,
        lvls,
        params,
        indices,
        nested,
        typ,
        ctors,
      } => {
        buf.push(1);
        let mask = compute_mask(&[
          recr.is_some(),
          refl.is_some(),
          is_unsafe.is_some(),
          lvls.is_some(),
          params.is_some(),
          indices.is_some(),
          nested.is_some(),
          typ.is_some(),
          ctors.is_some(),
        ]);
        Tag0::new(mask).put(buf);
        if let Some(r) = recr {
          put_bool_field(*r, buf);
        }
        if let Some(r) = refl {
          put_bool_field(*r, buf);
        }
        if let Some(u) = is_unsafe {
          put_bool_field(*u, buf);
        }
        if let Some(l) = lvls {
          Tag0::new(*l).put(buf);
        }
        if let Some(p) = params {
          Tag0::new(*p).put(buf);
        }
        if let Some(i) = indices {
          Tag0::new(*i).put(buf);
        }
        if let Some(n) = nested {
          Tag0::new(*n).put(buf);
        }
        if let Some(t) = typ {
          buf.extend_from_slice(t.as_bytes());
        }
        if let Some(c) = ctors {
          put_ctors(c, buf);
        }
      },
      Self::Recr {
        k,
        is_unsafe,
        lvls,
        params,
        indices,
        motives,
        minors,
        typ,
        rules,
      } => {
        buf.push(2);
        let mask = compute_mask(&[
          k.is_some(),
          is_unsafe.is_some(),
          lvls.is_some(),
          params.is_some(),
          indices.is_some(),
          motives.is_some(),
          minors.is_some(),
          typ.is_some(),
          rules.is_some(),
        ]);
        Tag0::new(mask).put(buf);
        if let Some(k) = k {
          put_bool_field(*k, buf);
        }
        if let Some(u) = is_unsafe {
          put_bool_field(*u, buf);
        }
        if let Some(l) = lvls {
          Tag0::new(*l).put(buf);
        }
        if let Some(p) = params {
          Tag0::new(*p).put(buf);
        }
        if let Some(i) = indices {
          Tag0::new(*i).put(buf);
        }
        if let Some(m) = motives {
          Tag0::new(*m).put(buf);
        }
        if let Some(m) = minors {
          Tag0::new(*m).put(buf);
        }
        if let Some(t) = typ {
          buf.extend_from_slice(t.as_bytes());
        }
        if let Some(r) = rules {
          put_rules(r, buf);
        }
      },
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let variant = get_u8(buf)?;
    let mask = Tag0::get(buf)?.size;
    match variant {
      0 => {
        let kind =
          if mask & 1 != 0 { Some(get_def_kind(buf)?) } else { None };
        let safety =
          if mask & 2 != 0 { Some(get_def_safety(buf)?) } else { None };
        let lvls =
          if mask & 4 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let typ =
          if mask & 8 != 0 { Some(get_address(buf)?) } else { None };
        let value =
          if mask & 16 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::Defn { kind, safety, lvls, typ, value })
      },
      1 => {
        let recr =
          if mask & 1 != 0 { Some(get_bool_field(buf)?) } else { None };
        let refl =
          if mask & 2 != 0 { Some(get_bool_field(buf)?) } else { None };
        let is_unsafe =
          if mask & 4 != 0 { Some(get_bool_field(buf)?) } else { None };
        let lvls =
          if mask & 8 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let params =
          if mask & 16 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let indices =
          if mask & 32 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let nested =
          if mask & 64 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let typ =
          if mask & 128 != 0 { Some(get_address(buf)?) } else { None };
        let ctors =
          if mask & 256 != 0 { Some(get_ctors(buf)?) } else { None };
        Ok(Self::Indc {
          recr,
          refl,
          is_unsafe,
          lvls,
          params,
          indices,
          nested,
          typ,
          ctors,
        })
      },
      2 => {
        let k =
          if mask & 1 != 0 { Some(get_bool_field(buf)?) } else { None };
        let is_unsafe =
          if mask & 2 != 0 { Some(get_bool_field(buf)?) } else { None };
        let lvls =
          if mask & 4 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let params =
          if mask & 8 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let indices =
          if mask & 16 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let motives =
          if mask & 32 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let minors =
          if mask & 64 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let typ =
          if mask & 128 != 0 { Some(get_address(buf)?) } else { None };
        let rules =
          if mask & 256 != 0 { Some(get_rules(buf)?) } else { None };
        Ok(Self::Recr {
          k,
          is_unsafe,
          lvls,
          params,
          indices,
          motives,
          minors,
          typ,
          rules,
        })
      },
      x => Err(format!("RevealMutConstInfo::get: invalid variant {x}")),
    }
  }
}

// ============================================================================
// RevealConstantInfo serialization
// ============================================================================

impl RevealConstantInfo {
  /// Serialize: variant byte + mask (Tag0) + field values in mask order.
  pub fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Defn { kind, safety, lvls, typ, value } => {
        buf.push(0);
        let mask = compute_mask(&[
          kind.is_some(),
          safety.is_some(),
          lvls.is_some(),
          typ.is_some(),
          value.is_some(),
        ]);
        Tag0::new(mask).put(buf);
        if let Some(k) = kind {
          put_def_kind(*k, buf);
        }
        if let Some(s) = safety {
          put_def_safety(*s, buf);
        }
        if let Some(l) = lvls {
          Tag0::new(*l).put(buf);
        }
        if let Some(t) = typ {
          buf.extend_from_slice(t.as_bytes());
        }
        if let Some(v) = value {
          buf.extend_from_slice(v.as_bytes());
        }
      },
      Self::Recr {
        k,
        is_unsafe,
        lvls,
        params,
        indices,
        motives,
        minors,
        typ,
        rules,
      } => {
        buf.push(1);
        let mask = compute_mask(&[
          k.is_some(),
          is_unsafe.is_some(),
          lvls.is_some(),
          params.is_some(),
          indices.is_some(),
          motives.is_some(),
          minors.is_some(),
          typ.is_some(),
          rules.is_some(),
        ]);
        Tag0::new(mask).put(buf);
        if let Some(k) = k {
          put_bool_field(*k, buf);
        }
        if let Some(u) = is_unsafe {
          put_bool_field(*u, buf);
        }
        if let Some(l) = lvls {
          Tag0::new(*l).put(buf);
        }
        if let Some(p) = params {
          Tag0::new(*p).put(buf);
        }
        if let Some(i) = indices {
          Tag0::new(*i).put(buf);
        }
        if let Some(m) = motives {
          Tag0::new(*m).put(buf);
        }
        if let Some(m) = minors {
          Tag0::new(*m).put(buf);
        }
        if let Some(t) = typ {
          buf.extend_from_slice(t.as_bytes());
        }
        if let Some(r) = rules {
          put_rules(r, buf);
        }
      },
      Self::Axio { is_unsafe, lvls, typ } => {
        buf.push(2);
        let mask = compute_mask(&[
          is_unsafe.is_some(),
          lvls.is_some(),
          typ.is_some(),
        ]);
        Tag0::new(mask).put(buf);
        if let Some(u) = is_unsafe {
          put_bool_field(*u, buf);
        }
        if let Some(l) = lvls {
          Tag0::new(*l).put(buf);
        }
        if let Some(t) = typ {
          buf.extend_from_slice(t.as_bytes());
        }
      },
      Self::Quot { kind, lvls, typ } => {
        buf.push(3);
        let mask = compute_mask(&[
          kind.is_some(),
          lvls.is_some(),
          typ.is_some(),
        ]);
        Tag0::new(mask).put(buf);
        if let Some(k) = kind {
          put_quot_kind(*k, buf);
        }
        if let Some(l) = lvls {
          Tag0::new(*l).put(buf);
        }
        if let Some(t) = typ {
          buf.extend_from_slice(t.as_bytes());
        }
      },
      Self::CPrj { idx, cidx, block } => {
        buf.push(4);
        let mask = compute_mask(&[
          idx.is_some(),
          cidx.is_some(),
          block.is_some(),
        ]);
        Tag0::new(mask).put(buf);
        if let Some(i) = idx {
          Tag0::new(*i).put(buf);
        }
        if let Some(c) = cidx {
          Tag0::new(*c).put(buf);
        }
        if let Some(b) = block {
          buf.extend_from_slice(b.as_bytes());
        }
      },
      Self::RPrj { idx, block } => {
        buf.push(5);
        let mask =
          compute_mask(&[idx.is_some(), block.is_some()]);
        Tag0::new(mask).put(buf);
        if let Some(i) = idx {
          Tag0::new(*i).put(buf);
        }
        if let Some(b) = block {
          buf.extend_from_slice(b.as_bytes());
        }
      },
      Self::IPrj { idx, block } => {
        buf.push(6);
        let mask =
          compute_mask(&[idx.is_some(), block.is_some()]);
        Tag0::new(mask).put(buf);
        if let Some(i) = idx {
          Tag0::new(*i).put(buf);
        }
        if let Some(b) = block {
          buf.extend_from_slice(b.as_bytes());
        }
      },
      Self::DPrj { idx, block } => {
        buf.push(7);
        let mask =
          compute_mask(&[idx.is_some(), block.is_some()]);
        Tag0::new(mask).put(buf);
        if let Some(i) = idx {
          Tag0::new(*i).put(buf);
        }
        if let Some(b) = block {
          buf.extend_from_slice(b.as_bytes());
        }
      },
      Self::Muts { components } => {
        buf.push(8);
        let mask: u64 = if components.is_empty() { 0 } else { 1 };
        Tag0::new(mask).put(buf);
        if !components.is_empty() {
          Tag0::new(components.len() as u64).put(buf);
          for (idx, info) in components {
            Tag0::new(*idx).put(buf);
            info.put(buf);
          }
        }
      },
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let variant = get_u8(buf)?;
    let mask = Tag0::get(buf)?.size;
    match variant {
      0 => {
        // Defn
        let kind =
          if mask & 1 != 0 { Some(get_def_kind(buf)?) } else { None };
        let safety =
          if mask & 2 != 0 { Some(get_def_safety(buf)?) } else { None };
        let lvls =
          if mask & 4 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let typ =
          if mask & 8 != 0 { Some(get_address(buf)?) } else { None };
        let value =
          if mask & 16 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::Defn { kind, safety, lvls, typ, value })
      },
      1 => {
        // Recr
        let k =
          if mask & 1 != 0 { Some(get_bool_field(buf)?) } else { None };
        let is_unsafe =
          if mask & 2 != 0 { Some(get_bool_field(buf)?) } else { None };
        let lvls =
          if mask & 4 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let params =
          if mask & 8 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let indices =
          if mask & 16 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let motives =
          if mask & 32 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let minors =
          if mask & 64 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let typ =
          if mask & 128 != 0 { Some(get_address(buf)?) } else { None };
        let rules =
          if mask & 256 != 0 { Some(get_rules(buf)?) } else { None };
        Ok(Self::Recr {
          k,
          is_unsafe,
          lvls,
          params,
          indices,
          motives,
          minors,
          typ,
          rules,
        })
      },
      2 => {
        // Axio
        let is_unsafe =
          if mask & 1 != 0 { Some(get_bool_field(buf)?) } else { None };
        let lvls =
          if mask & 2 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let typ =
          if mask & 4 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::Axio { is_unsafe, lvls, typ })
      },
      3 => {
        // Quot
        let kind =
          if mask & 1 != 0 { Some(get_quot_kind(buf)?) } else { None };
        let lvls =
          if mask & 2 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let typ =
          if mask & 4 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::Quot { kind, lvls, typ })
      },
      4 => {
        // CPrj
        let idx =
          if mask & 1 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let cidx =
          if mask & 2 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let block =
          if mask & 4 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::CPrj { idx, cidx, block })
      },
      5 => {
        // RPrj
        let idx =
          if mask & 1 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let block =
          if mask & 2 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::RPrj { idx, block })
      },
      6 => {
        // IPrj
        let idx =
          if mask & 1 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let block =
          if mask & 2 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::IPrj { idx, block })
      },
      7 => {
        // DPrj
        let idx =
          if mask & 1 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let block =
          if mask & 2 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::DPrj { idx, block })
      },
      8 => {
        // Muts
        let components = if mask & 1 != 0 {
          let count = Tag0::get(buf)?.size;
          let mut comps = Vec::with_capacity(count as usize);
          for _ in 0..count {
            let idx = Tag0::get(buf)?.size;
            let info = RevealMutConstInfo::get(buf)?;
            comps.push((idx, info));
          }
          comps
        } else {
          Vec::new()
        };
        Ok(Self::Muts { components })
      },
      x => Err(format!("RevealConstantInfo::get: invalid variant {x}")),
    }
  }
}

// ============================================================================
// Claim serialization
// ============================================================================

impl Claim {
  pub fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Claim::Evals(eval) => {
        Tag4::new(FLAG, VARIANT_EVAL_CLAIM).put(buf);
        buf.extend_from_slice(eval.input.as_bytes());
        buf.extend_from_slice(eval.output.as_bytes());
      },
      Claim::Checks(check) => {
        Tag4::new(FLAG, VARIANT_CHECK_CLAIM).put(buf);
        buf.extend_from_slice(check.value.as_bytes());
      },
      Claim::Reveals(reveal) => {
        Tag4::new(FLAG, VARIANT_REVEAL_CLAIM).put(buf);
        buf.extend_from_slice(reveal.comm.as_bytes());
        reveal.info.put(buf);
      },
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let tag = Tag4::get(buf)?;
    if tag.flag != FLAG {
      return Err(format!(
        "Claim::get: expected flag 0x{:X}, got 0x{:X}",
        FLAG, tag.flag
      ));
    }

    match tag.size {
      VARIANT_EVAL_CLAIM => {
        let input = get_address(buf)?;
        let output = get_address(buf)?;
        Ok(Claim::Evals(EvalClaim { input, output }))
      },
      VARIANT_CHECK_CLAIM => {
        let value = get_address(buf)?;
        Ok(Claim::Checks(CheckClaim { value }))
      },
      VARIANT_REVEAL_CLAIM => {
        let comm = get_address(buf)?;
        let info = RevealConstantInfo::get(buf)?;
        Ok(Claim::Reveals(RevealClaim { comm, info }))
      },
      VARIANT_EVAL_PROOF | VARIANT_CHECK_PROOF | VARIANT_REVEAL_PROOF => {
        Err(format!(
          "Claim::get: got Proof variant {}, use Proof::get",
          tag.size
        ))
      },
      x => Err(format!("Claim::get: invalid variant {x}")),
    }
  }

  /// Serialize a claim and compute its content address.
  pub fn commit(&self) -> (Address, Vec<u8>) {
    let mut buf = Vec::new();
    self.put(&mut buf);
    let addr = Address::hash(&buf);
    (addr, buf)
  }
}

// ============================================================================
// Proof serialization
// ============================================================================

impl Proof {
  pub fn new(claim: Claim, proof: Vec<u8>) -> Self {
    Proof { claim, proof }
  }

  pub fn put(&self, buf: &mut Vec<u8>) {
    match &self.claim {
      Claim::Evals(eval) => {
        Tag4::new(FLAG, VARIANT_EVAL_PROOF).put(buf);
        buf.extend_from_slice(eval.input.as_bytes());
        buf.extend_from_slice(eval.output.as_bytes());
      },
      Claim::Checks(check) => {
        Tag4::new(FLAG, VARIANT_CHECK_PROOF).put(buf);
        buf.extend_from_slice(check.value.as_bytes());
      },
      Claim::Reveals(reveal) => {
        Tag4::new(FLAG, VARIANT_REVEAL_PROOF).put(buf);
        buf.extend_from_slice(reveal.comm.as_bytes());
        reveal.info.put(buf);
      },
    }
    // Proof bytes: length prefix + data
    Tag0::new(self.proof.len() as u64).put(buf);
    buf.extend_from_slice(&self.proof);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let tag = Tag4::get(buf)?;
    if tag.flag != FLAG {
      return Err(format!(
        "Proof::get: expected flag 0x{:X}, got 0x{:X}",
        FLAG, tag.flag
      ));
    }

    let claim = match tag.size {
      VARIANT_EVAL_PROOF => {
        let input = get_address(buf)?;
        let output = get_address(buf)?;
        Claim::Evals(EvalClaim { input, output })
      },
      VARIANT_CHECK_PROOF => {
        let value = get_address(buf)?;
        Claim::Checks(CheckClaim { value })
      },
      VARIANT_REVEAL_PROOF => {
        let comm = get_address(buf)?;
        let info = RevealConstantInfo::get(buf)?;
        Claim::Reveals(RevealClaim { comm, info })
      },
      VARIANT_EVAL_CLAIM | VARIANT_CHECK_CLAIM | VARIANT_REVEAL_CLAIM => {
        return Err(format!(
          "Proof::get: got Claim variant {}, use Claim::get",
          tag.size
        ));
      },
      x => return Err(format!("Proof::get: invalid variant {x}")),
    };

    // Proof bytes
    let len = usize::try_from(Tag0::get(buf)?.size)
      .expect("Tag0 size overflows usize");
    if buf.len() < len {
      return Err(format!(
        "Proof::get: need {} bytes for proof data, have {}",
        len,
        buf.len()
      ));
    }
    let (proof_bytes, rest) = buf.split_at(len);
    *buf = rest;

    Ok(Proof { claim, proof: proof_bytes.to_vec() })
  }

  /// Serialize a proof and compute its content address.
  pub fn commit(&self) -> (Address, Vec<u8>) {
    let mut buf = Vec::new();
    self.put(&mut buf);
    let addr = Address::hash(&buf);
    (addr, buf)
  }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
  use super::*;
  use quickcheck::{Arbitrary, Gen};

  // ========== Arbitrary impls ==========

  impl Arbitrary for EvalClaim {
    fn arbitrary(g: &mut Gen) -> Self {
      EvalClaim {
        input: Address::arbitrary(g),
        output: Address::arbitrary(g),
      }
    }
  }

  impl Arbitrary for CheckClaim {
    fn arbitrary(g: &mut Gen) -> Self {
      CheckClaim { value: Address::arbitrary(g) }
    }
  }

  impl Arbitrary for RevealConstructorInfo {
    fn arbitrary(g: &mut Gen) -> Self {
      RevealConstructorInfo {
        is_unsafe: if bool::arbitrary(g) {
          Some(bool::arbitrary(g))
        } else {
          None
        },
        lvls: if bool::arbitrary(g) {
          Some(u64::arbitrary(g) % 10)
        } else {
          None
        },
        cidx: if bool::arbitrary(g) {
          Some(u64::arbitrary(g) % 10)
        } else {
          None
        },
        params: if bool::arbitrary(g) {
          Some(u64::arbitrary(g) % 10)
        } else {
          None
        },
        fields: if bool::arbitrary(g) {
          Some(u64::arbitrary(g) % 10)
        } else {
          None
        },
        typ: if bool::arbitrary(g) {
          Some(Address::arbitrary(g))
        } else {
          None
        },
      }
    }
  }

  impl Arbitrary for RevealRecursorRule {
    fn arbitrary(g: &mut Gen) -> Self {
      RevealRecursorRule {
        rule_idx: u64::arbitrary(g) % 10,
        fields: u64::arbitrary(g) % 10,
        rhs: Address::arbitrary(g),
      }
    }
  }

  fn gen_opt_rules(g: &mut Gen) -> Option<Vec<RevealRecursorRule>> {
    if bool::arbitrary(g) {
      let n = (u8::arbitrary(g) % 4) as usize;
      Some((0..n).map(|_| RevealRecursorRule::arbitrary(g)).collect())
    } else {
      None
    }
  }

  fn gen_opt_ctors(
    g: &mut Gen,
  ) -> Option<Vec<(u64, RevealConstructorInfo)>> {
    if bool::arbitrary(g) {
      let n = (u8::arbitrary(g) % 4) as usize;
      Some(
        (0..n)
          .map(|_| {
            (u64::arbitrary(g) % 10, RevealConstructorInfo::arbitrary(g))
          })
          .collect(),
      )
    } else {
      None
    }
  }

  fn gen_opt_bool(g: &mut Gen) -> Option<bool> {
    if bool::arbitrary(g) { Some(bool::arbitrary(g)) } else { None }
  }

  fn gen_opt_u64(g: &mut Gen) -> Option<u64> {
    if bool::arbitrary(g) {
      Some(u64::arbitrary(g) % 100)
    } else {
      None
    }
  }

  fn gen_opt_addr(g: &mut Gen) -> Option<Address> {
    if bool::arbitrary(g) {
      Some(Address::arbitrary(g))
    } else {
      None
    }
  }

  impl Arbitrary for RevealMutConstInfo {
    fn arbitrary(g: &mut Gen) -> Self {
      match u8::arbitrary(g) % 3 {
        0 => Self::Defn {
          kind: if bool::arbitrary(g) {
            Some(DefKind::arbitrary(g))
          } else {
            None
          },
          safety: if bool::arbitrary(g) {
            Some(DefinitionSafety::arbitrary(g))
          } else {
            None
          },
          lvls: gen_opt_u64(g),
          typ: gen_opt_addr(g),
          value: gen_opt_addr(g),
        },
        1 => Self::Indc {
          recr: gen_opt_bool(g),
          refl: gen_opt_bool(g),
          is_unsafe: gen_opt_bool(g),
          lvls: gen_opt_u64(g),
          params: gen_opt_u64(g),
          indices: gen_opt_u64(g),
          nested: gen_opt_u64(g),
          typ: gen_opt_addr(g),
          ctors: gen_opt_ctors(g),
        },
        _ => Self::Recr {
          k: gen_opt_bool(g),
          is_unsafe: gen_opt_bool(g),
          lvls: gen_opt_u64(g),
          params: gen_opt_u64(g),
          indices: gen_opt_u64(g),
          motives: gen_opt_u64(g),
          minors: gen_opt_u64(g),
          typ: gen_opt_addr(g),
          rules: gen_opt_rules(g),
        },
      }
    }
  }

  impl Arbitrary for RevealConstantInfo {
    fn arbitrary(g: &mut Gen) -> Self {
      match u8::arbitrary(g) % 9 {
        0 => Self::Defn {
          kind: if bool::arbitrary(g) {
            Some(DefKind::arbitrary(g))
          } else {
            None
          },
          safety: if bool::arbitrary(g) {
            Some(DefinitionSafety::arbitrary(g))
          } else {
            None
          },
          lvls: gen_opt_u64(g),
          typ: gen_opt_addr(g),
          value: gen_opt_addr(g),
        },
        1 => Self::Recr {
          k: gen_opt_bool(g),
          is_unsafe: gen_opt_bool(g),
          lvls: gen_opt_u64(g),
          params: gen_opt_u64(g),
          indices: gen_opt_u64(g),
          motives: gen_opt_u64(g),
          minors: gen_opt_u64(g),
          typ: gen_opt_addr(g),
          rules: gen_opt_rules(g),
        },
        2 => Self::Axio {
          is_unsafe: gen_opt_bool(g),
          lvls: gen_opt_u64(g),
          typ: gen_opt_addr(g),
        },
        3 => Self::Quot {
          kind: if bool::arbitrary(g) {
            Some(QuotKind::arbitrary(g))
          } else {
            None
          },
          lvls: gen_opt_u64(g),
          typ: gen_opt_addr(g),
        },
        4 => Self::CPrj {
          idx: gen_opt_u64(g),
          cidx: gen_opt_u64(g),
          block: gen_opt_addr(g),
        },
        5 => Self::RPrj {
          idx: gen_opt_u64(g),
          block: gen_opt_addr(g),
        },
        6 => Self::IPrj {
          idx: gen_opt_u64(g),
          block: gen_opt_addr(g),
        },
        7 => Self::DPrj {
          idx: gen_opt_u64(g),
          block: gen_opt_addr(g),
        },
        _ => {
          let n = (u8::arbitrary(g) % 4) as usize;
          Self::Muts {
            components: (0..n)
              .map(|_| {
                (
                  u64::arbitrary(g) % 10,
                  RevealMutConstInfo::arbitrary(g),
                )
              })
              .collect(),
          }
        },
      }
    }
  }

  impl Arbitrary for RevealClaim {
    fn arbitrary(g: &mut Gen) -> Self {
      RevealClaim {
        comm: Address::arbitrary(g),
        info: RevealConstantInfo::arbitrary(g),
      }
    }
  }

  impl Arbitrary for Claim {
    fn arbitrary(g: &mut Gen) -> Self {
      match u8::arbitrary(g) % 3 {
        0 => Claim::Evals(EvalClaim::arbitrary(g)),
        1 => Claim::Checks(CheckClaim::arbitrary(g)),
        _ => Claim::Reveals(RevealClaim::arbitrary(g)),
      }
    }
  }

  impl Arbitrary for Proof {
    fn arbitrary(g: &mut Gen) -> Self {
      let len = u8::arbitrary(g) as usize % 64;
      let proof: Vec<u8> = (0..len).map(|_| u8::arbitrary(g)).collect();
      Proof { claim: Claim::arbitrary(g), proof }
    }
  }

  // ========== Roundtrip helpers ==========

  fn claim_roundtrip(c: &Claim) -> bool {
    let mut buf = Vec::new();
    c.put(&mut buf);
    match Claim::get(&mut buf.as_slice()) {
      Ok(c2) => c == &c2,
      Err(e) => {
        eprintln!("claim_roundtrip error: {e}");
        false
      },
    }
  }

  fn proof_roundtrip(p: &Proof) -> bool {
    let mut buf = Vec::new();
    p.put(&mut buf);
    match Proof::get(&mut buf.as_slice()) {
      Ok(p2) => p == &p2,
      Err(e) => {
        eprintln!("proof_roundtrip error: {e}");
        false
      },
    }
  }

  fn reveal_info_roundtrip(info: &RevealConstantInfo) -> bool {
    let mut buf = Vec::new();
    info.put(&mut buf);
    match RevealConstantInfo::get(&mut buf.as_slice()) {
      Ok(info2) => info == &info2,
      Err(e) => {
        eprintln!("reveal_info_roundtrip error: {e}");
        false
      },
    }
  }

  // ========== Quickcheck properties ==========

  #[allow(clippy::needless_pass_by_value)]
  #[quickcheck]
  fn prop_claim_roundtrip(c: Claim) -> bool {
    claim_roundtrip(&c)
  }

  #[allow(clippy::needless_pass_by_value)]
  #[quickcheck]
  fn prop_proof_roundtrip(p: Proof) -> bool {
    proof_roundtrip(&p)
  }

  #[allow(clippy::needless_pass_by_value)]
  #[quickcheck]
  fn prop_reveal_info_roundtrip(info: RevealConstantInfo) -> bool {
    reveal_info_roundtrip(&info)
  }

  // ========== Manual roundtrip tests ==========

  #[test]
  fn test_eval_claim_roundtrip() {
    let claim = Claim::Evals(EvalClaim {
      input: Address::hash(b"input"),
      output: Address::hash(b"output"),
    });
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_check_claim_roundtrip() {
    let claim =
      Claim::Checks(CheckClaim { value: Address::hash(b"value") });
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_eval_proof_roundtrip() {
    let proof = Proof::new(
      Claim::Evals(EvalClaim {
        input: Address::hash(b"input"),
        output: Address::hash(b"output"),
      }),
      vec![1, 2, 3, 4],
    );
    assert!(proof_roundtrip(&proof));
  }

  #[test]
  fn test_check_proof_roundtrip() {
    let proof = Proof::new(
      Claim::Checks(CheckClaim { value: Address::hash(b"value") }),
      vec![5, 6, 7, 8, 9],
    );
    assert!(proof_roundtrip(&proof));
  }

  #[test]
  fn test_empty_proof_data() {
    let proof = Proof::new(
      Claim::Evals(EvalClaim {
        input: Address::hash(b"c"),
        output: Address::hash(b"d"),
      }),
      vec![],
    );
    assert!(proof_roundtrip(&proof));
  }

  #[test]
  fn test_reveal_claim_roundtrip() {
    let claim = Claim::Reveals(RevealClaim {
      comm: Address::hash(b"comm"),
      info: RevealConstantInfo::Defn {
        kind: Some(DefKind::Definition),
        safety: Some(DefinitionSafety::Safe),
        lvls: Some(0),
        typ: None,
        value: None,
      },
    });
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_reveal_proof_roundtrip() {
    let proof = Proof::new(
      Claim::Reveals(RevealClaim {
        comm: Address::hash(b"comm"),
        info: RevealConstantInfo::Axio {
          is_unsafe: Some(false),
          lvls: None,
          typ: Some(Address::hash(b"typ")),
        },
      }),
      vec![0xAB, 0xCD],
    );
    assert!(proof_roundtrip(&proof));
  }

  // ========== Tag byte tests ==========

  #[test]
  fn test_claim_tags() {
    // EvalClaim should be 0xE4
    let eval_claim = Claim::Evals(EvalClaim {
      input: Address::hash(b"a"),
      output: Address::hash(b"b"),
    });
    let mut buf = Vec::new();
    eval_claim.put(&mut buf);
    assert_eq!(buf[0], 0xE4);

    // CheckClaim should be 0xE3
    let check_claim =
      Claim::Checks(CheckClaim { value: Address::hash(b"a") });
    let mut buf = Vec::new();
    check_claim.put(&mut buf);
    assert_eq!(buf[0], 0xE3);

    // RevealClaim should be 0xE6
    let reveal_claim = Claim::Reveals(RevealClaim {
      comm: Address::hash(b"a"),
      info: RevealConstantInfo::Defn {
        kind: None,
        safety: None,
        lvls: None,
        typ: None,
        value: None,
      },
    });
    let mut buf = Vec::new();
    reveal_claim.put(&mut buf);
    assert_eq!(buf[0], 0xE6);
  }

  #[test]
  fn test_proof_tags() {
    // EvalProof should be 0xE2
    let eval_proof = Proof::new(
      Claim::Evals(EvalClaim {
        input: Address::hash(b"a"),
        output: Address::hash(b"b"),
      }),
      vec![1, 2, 3],
    );
    let mut buf = Vec::new();
    eval_proof.put(&mut buf);
    assert_eq!(buf[0], 0xE2);

    // CheckProof should be 0xE1
    let check_proof = Proof::new(
      Claim::Checks(CheckClaim { value: Address::hash(b"a") }),
      vec![4, 5, 6],
    );
    let mut buf = Vec::new();
    check_proof.put(&mut buf);
    assert_eq!(buf[0], 0xE1);

    // RevealProof should be 0xE7
    let reveal_proof = Proof::new(
      Claim::Reveals(RevealClaim {
        comm: Address::hash(b"a"),
        info: RevealConstantInfo::Defn {
          kind: None,
          safety: None,
          lvls: None,
          typ: None,
          value: None,
        },
      }),
      vec![7, 8],
    );
    let mut buf = Vec::new();
    reveal_proof.put(&mut buf);
    assert_eq!(buf[0], 0xE7);
  }

  // ========== Bitmask encoding tests from plan examples ==========

  #[test]
  fn test_reveal_defn_safety() {
    // Plan example: Reveal that a committed Definition has safety = Safe
    // 0xE6 <32 bytes comm> 0x00 0x02 0x01
    let claim = Claim::Reveals(RevealClaim {
      comm: Address::hash(b"test_comm"),
      info: RevealConstantInfo::Defn {
        kind: None,
        safety: Some(DefinitionSafety::Safe),
        lvls: None,
        typ: None,
        value: None,
      },
    });
    let mut buf = Vec::new();
    claim.put(&mut buf);
    assert_eq!(buf[0], 0xE6); // Tag4: RevealClaim
    // buf[1..33] = comm_addr (32 bytes)
    assert_eq!(buf[33], 0x00); // variant: Definition
    assert_eq!(buf[34], 0x02); // mask: bit 1 (safety)
    assert_eq!(buf[35], 0x01); // DefinitionSafety::Safe
    assert_eq!(buf.len(), 36); // Total: 1 + 32 + 1 + 1 + 1 = 36 bytes
  }

  #[test]
  fn test_reveal_defn_typ() {
    // Plan example: Reveal a committed Definition's type expression
    // 0xE6 <32 bytes comm> 0x00 0x08 <32 bytes typ>
    let typ_addr = Address::hash(b"serialized typ expr");
    let claim = Claim::Reveals(RevealClaim {
      comm: Address::hash(b"test_comm"),
      info: RevealConstantInfo::Defn {
        kind: None,
        safety: None,
        lvls: None,
        typ: Some(typ_addr),
        value: None,
      },
    });
    let mut buf = Vec::new();
    claim.put(&mut buf);
    assert_eq!(buf[0], 0xE6); // Tag4: RevealClaim
    assert_eq!(buf[33], 0x00); // variant: Definition
    assert_eq!(buf[34], 0x08); // mask: bit 3 (typ)
    // buf[35..67] = typ address (32 bytes)
    assert_eq!(buf.len(), 67); // Total: 1 + 32 + 1 + 1 + 32 = 67 bytes
  }

  #[test]
  fn test_reveal_muts_component_safety() {
    // Plan example: Reveal a Muts component's safety
    // 0xE6 <32 comm> 0x08 0x01 0x01 0x02 0x00 0x02 0x01
    let claim = Claim::Reveals(RevealClaim {
      comm: Address::hash(b"test_comm"),
      info: RevealConstantInfo::Muts {
        components: vec![(
          2,
          RevealMutConstInfo::Defn {
            kind: None,
            safety: Some(DefinitionSafety::Safe),
            lvls: None,
            typ: None,
            value: None,
          },
        )],
      },
    });
    let mut buf = Vec::new();
    claim.put(&mut buf);
    assert_eq!(buf[0], 0xE6); // Tag4: RevealClaim
    assert_eq!(buf[33], 0x08); // variant: Muts
    assert_eq!(buf[34], 0x01); // mask: bit 0 (components)
    assert_eq!(buf[35], 0x01); // Tag0: 1 component revealed
    assert_eq!(buf[36], 0x02); // Tag0: component index 2
    assert_eq!(buf[37], 0x00); // RevealMutConstInfo variant: Definition
    assert_eq!(buf[38], 0x02); // mask: bit 1 (safety)
    assert_eq!(buf[39], 0x01); // DefinitionSafety::Safe
    assert_eq!(buf.len(), 40); // Total: 1 + 32 + 7 = 40 bytes
  }

  // ========== All RevealConstantInfo variant roundtrips ==========

  #[test]
  fn test_reveal_all_variants() {
    let cases: Vec<RevealConstantInfo> = vec![
      // Defn with all fields
      RevealConstantInfo::Defn {
        kind: Some(DefKind::Theorem),
        safety: Some(DefinitionSafety::Partial),
        lvls: Some(3),
        typ: Some(Address::hash(b"typ")),
        value: Some(Address::hash(b"val")),
      },
      // Defn with no fields
      RevealConstantInfo::Defn {
        kind: None,
        safety: None,
        lvls: None,
        typ: None,
        value: None,
      },
      // Recr with rules
      RevealConstantInfo::Recr {
        k: Some(true),
        is_unsafe: None,
        lvls: Some(1),
        params: None,
        indices: None,
        motives: None,
        minors: None,
        typ: None,
        rules: Some(vec![RevealRecursorRule {
          rule_idx: 0,
          fields: 2,
          rhs: Address::hash(b"rhs"),
        }]),
      },
      // Axio
      RevealConstantInfo::Axio {
        is_unsafe: Some(false),
        lvls: Some(0),
        typ: Some(Address::hash(b"axtyp")),
      },
      // Quot
      RevealConstantInfo::Quot {
        kind: Some(QuotKind::Lift),
        lvls: None,
        typ: None,
      },
      // CPrj
      RevealConstantInfo::CPrj {
        idx: Some(0),
        cidx: Some(1),
        block: Some(Address::hash(b"block")),
      },
      // RPrj
      RevealConstantInfo::RPrj {
        idx: Some(2),
        block: None,
      },
      // IPrj
      RevealConstantInfo::IPrj {
        idx: None,
        block: Some(Address::hash(b"blk")),
      },
      // DPrj
      RevealConstantInfo::DPrj {
        idx: Some(5),
        block: Some(Address::hash(b"dblk")),
      },
      // Muts with components
      RevealConstantInfo::Muts {
        components: vec![
          (
            0,
            RevealMutConstInfo::Indc {
              recr: Some(true),
              refl: None,
              is_unsafe: Some(false),
              lvls: None,
              params: Some(2),
              indices: None,
              nested: None,
              typ: None,
              ctors: Some(vec![(
                0,
                RevealConstructorInfo {
                  is_unsafe: Some(false),
                  lvls: None,
                  cidx: Some(0),
                  params: None,
                  fields: Some(3),
                  typ: None,
                },
              )]),
            },
          ),
          (
            1,
            RevealMutConstInfo::Recr {
              k: None,
              is_unsafe: None,
              lvls: Some(1),
              params: None,
              indices: None,
              motives: None,
              minors: None,
              typ: None,
              rules: None,
            },
          ),
        ],
      },
      // Muts with empty components
      RevealConstantInfo::Muts { components: vec![] },
    ];

    for (i, info) in cases.iter().enumerate() {
      assert!(
        reveal_info_roundtrip(info),
        "RevealConstantInfo roundtrip failed for case {i}"
      );
    }
  }
}
