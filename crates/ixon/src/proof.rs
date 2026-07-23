//! Proof, claim, and selective-revelation types for ZK verification.
//!
//! Claims assert properties about committed constants (type-checking, evaluation,
//! or selective field revelation). Proofs pair a claim with opaque proof bytes.
//!
//! `RevealConstantInfo` uses bitmask-based serialization: a mask (Tag0) encodes
//! which fields are present, followed by only the present field values in bit
//! order. This enables revealing specific fields of a committed constant without
//! exposing the full structure.

use ix_common::address::Address;
use ix_common::env::{DefinitionSafety, QuotKind};

use super::constant::DefKind;
use super::tag::{Tag0, Tag4};

// ============================================================================
// Reveal info types (per-variant selective-field structures)
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
    is_unsafe: Option<bool>,
    lvls: Option<u64>,
    params: Option<u64>,
    indices: Option<u64>,
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

// ============================================================================
// Claim and Proof types
// ============================================================================

/// A claim that can be proven.
///
/// Four families:
///
/// - **Typechecking claims** (`Eval`, `Check`, `CheckEnv`): assert that a
///   constant evaluates, a constant is well-typed, or every constant in
///   an env is well-typed. Each carries `assumptions: Option<Address>`:
///   - `None` → unconditional (constructive proof, no axioms).
///   - `Some(root)` → conditional on every leaf in the merkle tree
///     rooted at `root` being a well-typed constant.
/// - **Reveal**: selective field revelation of a committed constant.
///   Orthogonal to typechecking; carries no assumptions.
/// - **Contains**: structural membership claim — `const_addr` is a leaf
///   in the merkle tree rooted at `tree`. Used by the aggregation
///   circuit to resolve a leaf from a conditional claim's assumption
///   set. Carries no assumptions itself.
///
/// The `assumptions` root may be any merkle tree (canonical sorted+
/// padded via `merkle_root_canonical`, or free-form via `merkle_join`)
/// with `Address` leaves. Verifiers recover the leaf set via the
/// `AssumptionTree` serialization when free-form.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Claim {
  /// `input` evaluates to `output`, optionally modulo `assumptions`.
  Eval { input: Address, output: Address, assumptions: Option<Address> },
  /// The constant at `const_addr` is well-typed, optionally modulo
  /// `assumptions`.
  Check { const_addr: Address, assumptions: Option<Address> },
  /// Every constant in the tree at `root` is well-typed, assuming AT
  /// MOST the constants in the tree at `assumptions`.
  ///
  /// `assumptions` is mandatory: the trust surface is part of the
  /// statement, never elided. "Assumes nothing" is the canonical empty
  /// (padding) tree, whose root is the zero address. The kernel enforces
  /// the declaration — every constant it dereferences must be in
  /// `root union assumptions` — so the stated trust surface is the real
  /// one.
  CheckEnv { root: Address, assumptions: Address },
  /// Selective field revelation of a committed constant.
  Reveal { comm: Address, info: RevealConstantInfo },
  /// `const_addr` is a leaf in the merkle tree rooted at `tree`.
  Contains { tree: Address, const_addr: Address },
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
// Tag4 variant layout for flags 0xE (data + claims) and 0xF (proofs)
// ============================================================================

/// Tag4 flag for envs, commitments, AssumptionTree, and claims (0xE).
///
/// All variants under 0xE fit in single-byte tags (`0xE0`–`0xE7`).
/// Matches the `Variant (0-7)` constraint documented in `docs/Ixon.md`.
///
/// - 0: Env (on-disk env serialization)
/// - 1: Comm (commitment, handled in `comm.rs`)
/// - 2: AssumptionTree (recursive merkle-tree data, see `assumption_tree.rs`)
/// - 3: Eval claim
/// - 4: Check claim
/// - 5: CheckEnv claim
/// - 6: Reveal claim
/// - 7: Contains claim
pub const FLAG_CLAIM: u8 = 0xE;

pub const VARIANT_ENV: u64 = 0;
// VARIANT 1 = Comm (handled in comm.rs)
pub const VARIANT_ASSUMPTION_TREE: u64 = 2;
pub const VARIANT_EVAL_CLAIM: u64 = 3;
pub const VARIANT_CHECK_CLAIM: u64 = 4;
pub const VARIANT_CHECK_ENV_CLAIM: u64 = 5;
pub const VARIANT_REVEAL_CLAIM: u64 = 6;
pub const VARIANT_CONTAINS_CLAIM: u64 = 7;

/// Tag4 flag for ZK proofs (0xF). All variants in single-byte tags
/// (`0xF0`–`0xF4`). Slots 5-7 reserved for future proof variants.
///
/// Proof bytes are uniform opaque ZK proofs — witness data (e.g.,
/// merkle paths for Contains) is prover-side scratch consumed by the
/// ZK circuit and NOT transmitted on the wire.
///
/// - 0: Eval proof
/// - 1: Check proof
/// - 2: CheckEnv proof
/// - 3: Reveal proof
/// - 4: Contains proof
pub const FLAG_PROOF: u8 = 0xF;

pub const VARIANT_EVAL_PROOF: u64 = 0;
pub const VARIANT_CHECK_PROOF: u64 = 1;
pub const VARIANT_CHECK_ENV_PROOF: u64 = 2;
pub const VARIANT_REVEAL_PROOF: u64 = 3;
pub const VARIANT_CONTAINS_PROOF: u64 = 4;

// Backwards-compatibility re-export: many call sites refer to FLAG.
pub const FLAG: u8 = FLAG_CLAIM;

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
    let lvls = if mask & 2 != 0 { Some(Tag0::get(buf)?.size) } else { None };
    let cidx = if mask & 4 != 0 { Some(Tag0::get(buf)?.size) } else { None };
    let params = if mask & 8 != 0 { Some(Tag0::get(buf)?.size) } else { None };
    let fields = if mask & 16 != 0 { Some(Tag0::get(buf)?.size) } else { None };
    let typ = if mask & 32 != 0 { Some(get_address(buf)?) } else { None };
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
  let count =
    usize::try_from(Tag0::get(buf)?.size).map_err(|e| e.to_string())?;
  let mut rules = Vec::with_capacity(count);
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
  let count =
    usize::try_from(Tag0::get(buf)?.size).map_err(|e| e.to_string())?;
  let mut ctors = Vec::with_capacity(count);
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
      Self::Indc { is_unsafe, lvls, params, indices, typ, ctors } => {
        buf.push(1);
        let mask = compute_mask(&[
          is_unsafe.is_some(),
          lvls.is_some(),
          params.is_some(),
          indices.is_some(),
          typ.is_some(),
          ctors.is_some(),
        ]);
        Tag0::new(mask).put(buf);
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
        let kind = if mask & 1 != 0 { Some(get_def_kind(buf)?) } else { None };
        let safety =
          if mask & 2 != 0 { Some(get_def_safety(buf)?) } else { None };
        let lvls =
          if mask & 4 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let typ = if mask & 8 != 0 { Some(get_address(buf)?) } else { None };
        let value = if mask & 16 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::Defn { kind, safety, lvls, typ, value })
      },
      1 => {
        let is_unsafe =
          if mask & 1 != 0 { Some(get_bool_field(buf)?) } else { None };
        let lvls =
          if mask & 2 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let params =
          if mask & 4 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let indices =
          if mask & 8 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let typ = if mask & 16 != 0 { Some(get_address(buf)?) } else { None };
        let ctors = if mask & 32 != 0 { Some(get_ctors(buf)?) } else { None };
        Ok(Self::Indc { is_unsafe, lvls, params, indices, typ, ctors })
      },
      2 => {
        let k = if mask & 1 != 0 { Some(get_bool_field(buf)?) } else { None };
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
        let typ = if mask & 128 != 0 { Some(get_address(buf)?) } else { None };
        let rules = if mask & 256 != 0 { Some(get_rules(buf)?) } else { None };
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
        let mask =
          compute_mask(&[is_unsafe.is_some(), lvls.is_some(), typ.is_some()]);
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
        let mask =
          compute_mask(&[kind.is_some(), lvls.is_some(), typ.is_some()]);
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
        let mask =
          compute_mask(&[idx.is_some(), cidx.is_some(), block.is_some()]);
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
        let mask = compute_mask(&[idx.is_some(), block.is_some()]);
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
        let mask = compute_mask(&[idx.is_some(), block.is_some()]);
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
        let mask = compute_mask(&[idx.is_some(), block.is_some()]);
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
        let kind = if mask & 1 != 0 { Some(get_def_kind(buf)?) } else { None };
        let safety =
          if mask & 2 != 0 { Some(get_def_safety(buf)?) } else { None };
        let lvls =
          if mask & 4 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let typ = if mask & 8 != 0 { Some(get_address(buf)?) } else { None };
        let value = if mask & 16 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::Defn { kind, safety, lvls, typ, value })
      },
      1 => {
        // Recr
        let k = if mask & 1 != 0 { Some(get_bool_field(buf)?) } else { None };
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
        let typ = if mask & 128 != 0 { Some(get_address(buf)?) } else { None };
        let rules = if mask & 256 != 0 { Some(get_rules(buf)?) } else { None };
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
        let typ = if mask & 4 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::Axio { is_unsafe, lvls, typ })
      },
      3 => {
        // Quot
        let kind = if mask & 1 != 0 { Some(get_quot_kind(buf)?) } else { None };
        let lvls =
          if mask & 2 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let typ = if mask & 4 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::Quot { kind, lvls, typ })
      },
      4 => {
        // CPrj
        let idx = if mask & 1 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let cidx =
          if mask & 2 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let block = if mask & 4 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::CPrj { idx, cidx, block })
      },
      5 => {
        // RPrj
        let idx = if mask & 1 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let block = if mask & 2 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::RPrj { idx, block })
      },
      6 => {
        // IPrj
        let idx = if mask & 1 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let block = if mask & 2 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::IPrj { idx, block })
      },
      7 => {
        // DPrj
        let idx = if mask & 1 != 0 { Some(Tag0::get(buf)?.size) } else { None };
        let block = if mask & 2 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::DPrj { idx, block })
      },
      8 => {
        // Muts
        let components = if mask & 1 != 0 {
          let count =
            usize::try_from(Tag0::get(buf)?.size).map_err(|e| e.to_string())?;
          let mut comps = Vec::with_capacity(count);
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

/// Helper: write an `Option<Address>` as `[0x00]` (None) or
/// `[0x01][addr:32]` (Some). Single byte for absence avoids a 33-byte
/// gap when assumptions are absent.
fn put_opt_addr(opt: &Option<Address>, buf: &mut Vec<u8>) {
  match opt {
    None => buf.push(0x00),
    Some(addr) => {
      buf.push(0x01);
      buf.extend_from_slice(addr.as_bytes());
    },
  }
}

fn get_opt_addr(buf: &mut &[u8]) -> Result<Option<Address>, String> {
  match get_u8(buf)? {
    0x00 => Ok(None),
    0x01 => Ok(Some(get_address(buf)?)),
    b => Err(format!("get_opt_addr: invalid tag 0x{:02X}", b)),
  }
}

impl Claim {
  pub fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Claim::Eval { input, output, assumptions } => {
        Tag4::new(FLAG_CLAIM, VARIANT_EVAL_CLAIM).put(buf);
        buf.extend_from_slice(input.as_bytes());
        buf.extend_from_slice(output.as_bytes());
        put_opt_addr(assumptions, buf);
      },
      Claim::Check { const_addr, assumptions } => {
        Tag4::new(FLAG_CLAIM, VARIANT_CHECK_CLAIM).put(buf);
        buf.extend_from_slice(const_addr.as_bytes());
        put_opt_addr(assumptions, buf);
      },
      Claim::CheckEnv { root, assumptions } => {
        Tag4::new(FLAG_CLAIM, VARIANT_CHECK_ENV_CLAIM).put(buf);
        buf.extend_from_slice(root.as_bytes());
        buf.extend_from_slice(assumptions.as_bytes());
      },
      Claim::Reveal { comm, info } => {
        Tag4::new(FLAG_CLAIM, VARIANT_REVEAL_CLAIM).put(buf);
        buf.extend_from_slice(comm.as_bytes());
        info.put(buf);
      },
      Claim::Contains { tree, const_addr } => {
        Tag4::new(FLAG_CLAIM, VARIANT_CONTAINS_CLAIM).put(buf);
        buf.extend_from_slice(tree.as_bytes());
        buf.extend_from_slice(const_addr.as_bytes());
      },
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let tag = Tag4::get(buf)?;
    if tag.flag != FLAG_CLAIM {
      return Err(format!(
        "Claim::get: expected flag 0x{:X}, got 0x{:X}",
        FLAG_CLAIM, tag.flag
      ));
    }
    match tag.size {
      VARIANT_EVAL_CLAIM => {
        let input = get_address(buf)?;
        let output = get_address(buf)?;
        let assumptions = get_opt_addr(buf)?;
        Ok(Claim::Eval { input, output, assumptions })
      },
      VARIANT_CHECK_CLAIM => {
        let const_addr = get_address(buf)?;
        let assumptions = get_opt_addr(buf)?;
        Ok(Claim::Check { const_addr, assumptions })
      },
      VARIANT_CHECK_ENV_CLAIM => {
        let root = get_address(buf)?;
        let assumptions = get_address(buf)?;
        Ok(Claim::CheckEnv { root, assumptions })
      },
      VARIANT_REVEAL_CLAIM => {
        let comm = get_address(buf)?;
        let info = RevealConstantInfo::get(buf)?;
        Ok(Claim::Reveal { comm, info })
      },
      VARIANT_CONTAINS_CLAIM => {
        let tree = get_address(buf)?;
        let const_addr = get_address(buf)?;
        Ok(Claim::Contains { tree, const_addr })
      },
      x => {
        Err(format!("Claim::get: invalid claim variant {x} under flag 0xE",))
      },
    }
  }

  /// Serialize a claim and compute its content address.
  pub fn commit(&self) -> (Address, Vec<u8>) {
    let mut buf = Vec::new();
    self.put(&mut buf);
    let addr = Address::hash(&buf);
    (addr, buf)
  }

  /// Map a claim to its corresponding proof variant size (under flag 0xF).
  pub fn proof_variant_size(&self) -> u64 {
    match self {
      Claim::Eval { .. } => VARIANT_EVAL_PROOF,
      Claim::Check { .. } => VARIANT_CHECK_PROOF,
      Claim::CheckEnv { .. } => VARIANT_CHECK_ENV_PROOF,
      Claim::Reveal { .. } => VARIANT_REVEAL_PROOF,
      Claim::Contains { .. } => VARIANT_CONTAINS_PROOF,
    }
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
    let proof_size = self.claim.proof_variant_size();
    // Proofs live under flag 0xF; claim payload is the same body as the
    // matching Claim variant.
    Tag4::new(FLAG_PROOF, proof_size).put(buf);
    match &self.claim {
      Claim::Eval { input, output, assumptions } => {
        buf.extend_from_slice(input.as_bytes());
        buf.extend_from_slice(output.as_bytes());
        put_opt_addr(assumptions, buf);
      },
      Claim::Check { const_addr, assumptions } => {
        buf.extend_from_slice(const_addr.as_bytes());
        put_opt_addr(assumptions, buf);
      },
      Claim::CheckEnv { root, assumptions } => {
        buf.extend_from_slice(root.as_bytes());
        buf.extend_from_slice(assumptions.as_bytes());
      },
      Claim::Reveal { comm, info } => {
        buf.extend_from_slice(comm.as_bytes());
        info.put(buf);
      },
      Claim::Contains { tree, const_addr } => {
        buf.extend_from_slice(tree.as_bytes());
        buf.extend_from_slice(const_addr.as_bytes());
      },
    }
    // Opaque ZK proof bytes: length prefix + data
    Tag0::new(self.proof.len() as u64).put(buf);
    buf.extend_from_slice(&self.proof);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let tag = Tag4::get(buf)?;
    if tag.flag != FLAG_PROOF {
      return Err(format!(
        "Proof::get: expected flag 0x{:X}, got 0x{:X}",
        FLAG_PROOF, tag.flag
      ));
    }
    let claim = match tag.size {
      VARIANT_EVAL_PROOF => {
        let input = get_address(buf)?;
        let output = get_address(buf)?;
        let assumptions = get_opt_addr(buf)?;
        Claim::Eval { input, output, assumptions }
      },
      VARIANT_CHECK_PROOF => {
        let const_addr = get_address(buf)?;
        let assumptions = get_opt_addr(buf)?;
        Claim::Check { const_addr, assumptions }
      },
      VARIANT_CHECK_ENV_PROOF => {
        let root = get_address(buf)?;
        let assumptions = get_address(buf)?;
        Claim::CheckEnv { root, assumptions }
      },
      VARIANT_REVEAL_PROOF => {
        let comm = get_address(buf)?;
        let info = RevealConstantInfo::get(buf)?;
        Claim::Reveal { comm, info }
      },
      VARIANT_CONTAINS_PROOF => {
        let tree = get_address(buf)?;
        let const_addr = get_address(buf)?;
        Claim::Contains { tree, const_addr }
      },
      x => {
        return Err(format!(
          "Proof::get: invalid proof variant {x} under flag 0xF"
        ));
      },
    };

    // Opaque ZK proof bytes
    let len = usize::try_from(Tag0::get(buf)?.size)
      .map_err(|_e| "Proof::get: Tag0 size overflows usize".to_string())?;
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
  use quickcheck_macros::quickcheck;

  // ========== Arbitrary impls ==========

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

  fn gen_opt_ctors(g: &mut Gen) -> Option<Vec<(u64, RevealConstructorInfo)>> {
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
    if bool::arbitrary(g) { Some(u64::arbitrary(g) % 100) } else { None }
  }

  fn gen_opt_addr(g: &mut Gen) -> Option<Address> {
    if bool::arbitrary(g) { Some(Address::arbitrary(g)) } else { None }
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
          is_unsafe: gen_opt_bool(g),
          lvls: gen_opt_u64(g),
          params: gen_opt_u64(g),
          indices: gen_opt_u64(g),
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
        5 => Self::RPrj { idx: gen_opt_u64(g), block: gen_opt_addr(g) },
        6 => Self::IPrj { idx: gen_opt_u64(g), block: gen_opt_addr(g) },
        7 => Self::DPrj { idx: gen_opt_u64(g), block: gen_opt_addr(g) },
        _ => {
          let n = (u8::arbitrary(g) % 4) as usize;
          Self::Muts {
            components: (0..n)
              .map(|_| {
                (u64::arbitrary(g) % 10, RevealMutConstInfo::arbitrary(g))
              })
              .collect(),
          }
        },
      }
    }
  }

  impl Arbitrary for Claim {
    fn arbitrary(g: &mut Gen) -> Self {
      match u8::arbitrary(g) % 5 {
        0 => Claim::Eval {
          input: Address::arbitrary(g),
          output: Address::arbitrary(g),
          assumptions: gen_opt_addr(g),
        },
        1 => Claim::Check {
          const_addr: Address::arbitrary(g),
          assumptions: gen_opt_addr(g),
        },
        2 => Claim::CheckEnv {
          root: Address::arbitrary(g),
          assumptions: gen_opt_addr(g),
        },
        3 => Claim::Reveal {
          comm: Address::arbitrary(g),
          info: RevealConstantInfo::arbitrary(g),
        },
        _ => Claim::Contains {
          tree: Address::arbitrary(g),
          const_addr: Address::arbitrary(g),
        },
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

  // ---------- Per-variant claim roundtrips ----------

  #[test]
  fn test_eval_claim_no_asm_roundtrip() {
    let claim = Claim::Eval {
      input: Address::hash(b"input"),
      output: Address::hash(b"output"),
      assumptions: None,
    };
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_eval_claim_with_asm_roundtrip() {
    let claim = Claim::Eval {
      input: Address::hash(b"input"),
      output: Address::hash(b"output"),
      assumptions: Some(Address::hash(b"asm")),
    };
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_check_claim_no_asm_roundtrip() {
    let claim =
      Claim::Check { const_addr: Address::hash(b"value"), assumptions: None };
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_check_claim_with_asm_roundtrip() {
    let claim = Claim::Check {
      const_addr: Address::hash(b"value"),
      assumptions: Some(Address::hash(b"asm")),
    };
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_check_env_claim_no_asm_roundtrip() {
    let claim =
      Claim::CheckEnv { root: Address::hash(b"env-root"), assumptions: None };
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_check_env_claim_with_asm_roundtrip() {
    let claim = Claim::CheckEnv {
      root: Address::hash(b"env-root"),
      assumptions: Some(Address::hash(b"asm")),
    };
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_contains_claim_roundtrip() {
    let claim = Claim::Contains {
      tree: Address::hash(b"tree-root"),
      const_addr: Address::hash(b"member"),
    };
    assert!(claim_roundtrip(&claim));
  }

  // ---------- Per-variant proof roundtrips ----------

  #[test]
  fn test_eval_proof_roundtrip() {
    let proof = Proof::new(
      Claim::Eval {
        input: Address::hash(b"input"),
        output: Address::hash(b"output"),
        assumptions: None,
      },
      vec![1, 2, 3, 4],
    );
    assert!(proof_roundtrip(&proof));
  }

  #[test]
  fn test_check_proof_roundtrip() {
    let proof = Proof::new(
      Claim::Check { const_addr: Address::hash(b"value"), assumptions: None },
      vec![5, 6, 7, 8, 9],
    );
    assert!(proof_roundtrip(&proof));
  }

  #[test]
  fn test_check_env_proof_roundtrip() {
    let proof = Proof::new(
      Claim::CheckEnv { root: Address::hash(b"env-root"), assumptions: None },
      vec![0x11, 0x22],
    );
    assert!(proof_roundtrip(&proof));
  }

  #[test]
  fn test_check_proof_with_asm_roundtrip() {
    let proof = Proof::new(
      Claim::Check {
        const_addr: Address::hash(b"const"),
        assumptions: Some(Address::hash(b"asm")),
      },
      vec![0xAA, 0xBB, 0xCC],
    );
    assert!(proof_roundtrip(&proof));
  }

  #[test]
  fn test_contains_proof_roundtrip() {
    let proof = Proof::new(
      Claim::Contains {
        tree: Address::hash(b"tree-root"),
        const_addr: Address::hash(b"member"),
      },
      vec![0xDE, 0xAD, 0xBE, 0xEF],
    );
    assert!(proof_roundtrip(&proof));
  }

  #[test]
  fn test_empty_proof_data() {
    let proof = Proof::new(
      Claim::Eval {
        input: Address::hash(b"c"),
        output: Address::hash(b"d"),
        assumptions: None,
      },
      vec![],
    );
    assert!(proof_roundtrip(&proof));
  }

  #[test]
  fn test_reveal_claim_roundtrip() {
    let claim = Claim::Reveal {
      comm: Address::hash(b"comm"),
      info: RevealConstantInfo::Defn {
        kind: Some(DefKind::Definition),
        safety: Some(DefinitionSafety::Safe),
        lvls: Some(0),
        typ: None,
        value: None,
      },
    };
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_reveal_proof_roundtrip() {
    let proof = Proof::new(
      Claim::Reveal {
        comm: Address::hash(b"comm"),
        info: RevealConstantInfo::Axio {
          is_unsafe: Some(false),
          lvls: None,
          typ: Some(Address::hash(b"typ")),
        },
      },
      vec![0xAB, 0xCD],
    );
    assert!(proof_roundtrip(&proof));
  }

  // ---------- Tag4 flag/size dispatch ----------

  fn parse_tag(bytes: &[u8]) -> Tag4 {
    Tag4::get(&mut &bytes[..]).unwrap()
  }

  fn claim_tag(claim: &Claim) -> Tag4 {
    let mut buf = Vec::new();
    claim.put(&mut buf);
    parse_tag(&buf)
  }

  fn proof_tag(proof: &Proof) -> Tag4 {
    let mut buf = Vec::new();
    proof.put(&mut buf);
    parse_tag(&buf)
  }

  #[test]
  fn test_claim_tag_flag_and_size() {
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let reveal_info = RevealConstantInfo::Defn {
      kind: None,
      safety: None,
      lvls: None,
      typ: None,
      value: None,
    };

    let cases: Vec<(Claim, u64)> = vec![
      (
        Claim::Eval { input: a.clone(), output: b.clone(), assumptions: None },
        VARIANT_EVAL_CLAIM,
      ),
      (
        Claim::Check { const_addr: a.clone(), assumptions: None },
        VARIANT_CHECK_CLAIM,
      ),
      (
        Claim::CheckEnv { root: a.clone(), assumptions: None },
        VARIANT_CHECK_ENV_CLAIM,
      ),
      (
        Claim::Reveal { comm: a.clone(), info: reveal_info },
        VARIANT_REVEAL_CLAIM,
      ),
      (Claim::Contains { tree: a, const_addr: b }, VARIANT_CONTAINS_CLAIM),
    ];

    for (claim, expected_size) in cases {
      let tag = claim_tag(&claim);
      assert_eq!(tag.flag, FLAG_CLAIM, "claim must use flag 0xE");
      assert_eq!(tag.size, expected_size);
    }
  }

  #[test]
  fn test_proof_tag_flag_and_size() {
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let reveal_info = RevealConstantInfo::Defn {
      kind: None,
      safety: None,
      lvls: None,
      typ: None,
      value: None,
    };

    let cases: Vec<(Claim, u64)> = vec![
      (
        Claim::Eval { input: a.clone(), output: b.clone(), assumptions: None },
        VARIANT_EVAL_PROOF,
      ),
      (
        Claim::Check { const_addr: a.clone(), assumptions: None },
        VARIANT_CHECK_PROOF,
      ),
      (
        Claim::CheckEnv { root: a.clone(), assumptions: None },
        VARIANT_CHECK_ENV_PROOF,
      ),
      (
        Claim::Reveal { comm: a.clone(), info: reveal_info },
        VARIANT_REVEAL_PROOF,
      ),
      (Claim::Contains { tree: a, const_addr: b }, VARIANT_CONTAINS_PROOF),
    ];

    for (claim, expected_size) in cases {
      let proof = Proof::new(claim, vec![0]);
      let tag = proof_tag(&proof);
      assert_eq!(tag.flag, FLAG_PROOF, "proof must use flag 0xF");
      assert_eq!(tag.size, expected_size);
    }
  }

  // ---------- Per-variant payload byte lengths ----------

  fn claim_bytes(claim: &Claim) -> Vec<u8> {
    let mut buf = Vec::new();
    claim.put(&mut buf);
    buf
  }

  #[test]
  fn test_claim_byte_lengths() {
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let asm = Address::hash(b"asm");

    // Single-byte Tag4 + payload + 1 opt byte (+ 32 if Some).
    assert_eq!(
      claim_bytes(&Claim::Eval {
        input: a.clone(),
        output: b.clone(),
        assumptions: None
      })
      .len(),
      1 + 64 + 1,
      "Eval no-asm = 66 bytes"
    );
    assert_eq!(
      claim_bytes(&Claim::Eval {
        input: a.clone(),
        output: b.clone(),
        assumptions: Some(asm.clone())
      })
      .len(),
      1 + 64 + 1 + 32,
      "Eval with-asm = 98 bytes"
    );
    assert_eq!(
      claim_bytes(&Claim::Check { const_addr: a.clone(), assumptions: None })
        .len(),
      1 + 32 + 1,
      "Check no-asm = 34 bytes"
    );
    assert_eq!(
      claim_bytes(&Claim::Check {
        const_addr: a.clone(),
        assumptions: Some(asm.clone())
      })
      .len(),
      1 + 32 + 1 + 32,
      "Check with-asm = 66 bytes"
    );
    assert_eq!(
      claim_bytes(&Claim::CheckEnv { root: a.clone(), assumptions: None })
        .len(),
      1 + 32 + 1,
      "CheckEnv no-asm = 34 bytes"
    );
    assert_eq!(
      claim_bytes(&Claim::Contains { tree: a, const_addr: b }).len(),
      1 + 64,
      "Contains = 65 bytes"
    );
  }

  #[test]
  fn test_claim_first_byte() {
    // Single-byte Tag4 encoding: size 0-7 fits in one byte (0xE0..0xE7).
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let reveal_info = RevealConstantInfo::Defn {
      kind: None,
      safety: None,
      lvls: None,
      typ: None,
      value: None,
    };

    let cases: Vec<(Claim, u8)> = vec![
      (
        Claim::Eval { input: a.clone(), output: b.clone(), assumptions: None },
        0xE3,
      ),
      (Claim::Check { const_addr: a.clone(), assumptions: None }, 0xE4),
      (Claim::CheckEnv { root: a.clone(), assumptions: None }, 0xE5),
      (Claim::Reveal { comm: a.clone(), info: reveal_info }, 0xE6),
      (Claim::Contains { tree: a, const_addr: b }, 0xE7),
    ];
    for (claim, expected_byte) in cases {
      let bytes = claim_bytes(&claim);
      assert_eq!(bytes[0], expected_byte);
    }
  }

  #[test]
  fn test_proof_first_byte() {
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let reveal_info = RevealConstantInfo::Defn {
      kind: None,
      safety: None,
      lvls: None,
      typ: None,
      value: None,
    };
    let cases: Vec<(Claim, u8)> = vec![
      (
        Claim::Eval { input: a.clone(), output: b.clone(), assumptions: None },
        0xF0,
      ),
      (Claim::Check { const_addr: a.clone(), assumptions: None }, 0xF1),
      (Claim::CheckEnv { root: a.clone(), assumptions: None }, 0xF2),
      (Claim::Reveal { comm: a.clone(), info: reveal_info }, 0xF3),
      (Claim::Contains { tree: a, const_addr: b }, 0xF4),
    ];
    for (claim, expected_byte) in cases {
      let mut buf = Vec::new();
      Proof::new(claim, vec![]).put(&mut buf);
      assert_eq!(buf[0], expected_byte);
    }
  }

  // ========== Bitmask encoding tests from plan examples ==========

  // Reveal claim is variant 6 (single-byte tag 0xE6).

  #[test]
  fn test_reveal_defn_safety() {
    // 0xE6 <32 bytes comm> 0x00 0x02 0x01
    let claim = Claim::Reveal {
      comm: Address::hash(b"test_comm"),
      info: RevealConstantInfo::Defn {
        kind: None,
        safety: Some(DefinitionSafety::Safe),
        lvls: None,
        typ: None,
        value: None,
      },
    };
    let mut buf = Vec::new();
    claim.put(&mut buf);
    assert_eq!(buf[0], 0xE6); // Tag4: flag=0xE, size=6 (Reveal claim)
    // buf[1..33] = comm_addr (32 bytes)
    assert_eq!(buf[33], 0x00); // RevealConstantInfo variant: Definition
    assert_eq!(buf[34], 0x02); // mask: bit 1 (safety)
    assert_eq!(buf[35], 0x01); // DefinitionSafety::Safe
    assert_eq!(buf.len(), 36); // Total: 1 + 32 + 1 + 1 + 1 = 36 bytes
  }

  #[test]
  fn test_reveal_defn_typ() {
    // 0xE6 <32 bytes comm> 0x00 0x08 <32 bytes typ>
    let typ_addr = Address::hash(b"serialized typ expr");
    let claim = Claim::Reveal {
      comm: Address::hash(b"test_comm"),
      info: RevealConstantInfo::Defn {
        kind: None,
        safety: None,
        lvls: None,
        typ: Some(typ_addr),
        value: None,
      },
    };
    let mut buf = Vec::new();
    claim.put(&mut buf);
    assert_eq!(buf[0], 0xE6);
    assert_eq!(buf[33], 0x00); // RevealConstantInfo variant: Definition
    assert_eq!(buf[34], 0x08); // mask: bit 3 (typ)
    // buf[35..67] = typ address (32 bytes)
    assert_eq!(buf.len(), 67); // Total: 1 + 32 + 1 + 1 + 32 = 67 bytes
  }

  #[test]
  fn test_reveal_muts_component_safety() {
    // 0xE6 <32 comm> 0x08 0x01 0x01 0x02 0x00 0x02 0x01
    let claim = Claim::Reveal {
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
    };
    let mut buf = Vec::new();
    claim.put(&mut buf);
    assert_eq!(buf[0], 0xE6);
    assert_eq!(buf[33], 0x08); // RevealConstantInfo variant: Muts
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
      RevealConstantInfo::RPrj { idx: Some(2), block: None },
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
              is_unsafe: Some(false),
              lvls: None,
              params: Some(2),
              indices: None,
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
