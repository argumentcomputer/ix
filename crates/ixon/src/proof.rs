//! Proof, claim, and selective-revelation types for ZK verification.
//!
//! Claims assert properties about committed constants (type-checking, evaluation,
//! or selective field revelation). Proofs pair a claim with opaque proof bytes.
//!
//! `RevealConstantInfo` uses bitmask-based serialization: a mask (TagN) encodes
//! which fields are present, followed by only the present field values in bit
//! order. This enables revealing specific fields of a committed constant without
//! exposing the full structure.

use ix_common::address::Address;
use ix_common::env::{DefinitionSafety, QuotKind};

use super::constant::DefKind;
use super::env::Env;
use super::tag::TagN;

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

/// What a typing claim is relative to. The typing claims (`Eval`, `Check`,
/// `CheckEnv`, `Catalog`) state that constants are well-typed in Lean's
/// theory with its primitives read through a role binding, and these three
/// fields say which:
///
/// - `spec`: the specification digest ([`SPEC_DIGEST_HEX`]), naming the
///   specifications every bound role is validated against;
/// - `binding`: the binding hash, the BLAKE3 hash of the role table's section
///   bytes ([`crate::env::RoleBinding`]'s address), naming which constant
///   plays each role;
/// - `axioms`: the axioms the claim depends on beyond the standard three
///   (`propext`, `Classical.choice`, `Quot.sound`), as the canonical merkle
///   root of their sorted addresses. `None` means the standard three only. No
///   checker admits another axiom yet, so every claim made today carries
///   `None`; the field is reserved so that admitting declared axioms later
///   needs no second format change.
///
/// Typing assumptions (each claim's `assumptions`) are a different thing:
/// constants assumed well-typed and discharged by other claims. An axiom is
/// never discharged by typing, so axioms are never listed there.
///
/// `binding_assumed` says whether the claim validates the binding itself or
/// assumes it. A claim that validates it ([`VALIDATOR_ERASED_LEAN`]) checks,
/// in its own proof, every role it uses against its specification. A
/// `Check` or `CheckEnv` claim may instead assume it
/// ([`VALIDATOR_ERASED_LEAN_ASSUMED`]). It then states its typing only *if*
/// the role table with hash `binding` meets the specifications `spec`, which
/// a [`Claim::Binding`] states and aggregation discharges once. The flag is
/// the claim's validator byte, not a context field on the wire, and only
/// `Check` and `CheckEnv` carry it: the other typing claims always validate.
///
/// `literal_class` says that `binding` is not a binding hash but a literal
/// class digest ([`crate::role_table::RoleTable::literal_class`]): the hash of
/// the addresses a binding binds to the roles the checker uses without a
/// reference to them (the literal support and the standard axioms). A
/// `CheckEnv` claim under a literal class ([`VALIDATOR_ERASED_LEAN_CLASS`])
/// states its typing under every binding with that literal class that meets
/// the specifications. Only aggregation produces such claims (`ix_aggr` shape
/// 15); IxVM never reads one. Like `binding_assumed`, the flag is the
/// validator byte.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClaimContext {
  pub spec: Address,
  pub binding: Address,
  pub axioms: Option<Address>,
  pub binding_assumed: bool,
  pub literal_class: bool,
}

/// A claim that can be proven.
///
/// Four families:
///
/// - **Typechecking claims** (`Eval`, `Check`, `CheckEnv`, `Catalog`):
///   assert that a constant evaluates, a constant is well-typed, or every
///   constant in an env or catalog is well-typed, relative to their
///   [`ClaimContext`]. Each carries `assumptions: Option<Address>`:
///   - `None` → unconditional.
///   - `Some(root)` → conditional on every leaf in the merkle tree
///     rooted at `root` being a well-typed constant.
/// - **Reveal**: selective field revelation of a committed constant.
///   Orthogonal to typechecking; carries no assumptions.
/// - **Contains**: structural membership claim — `const_addr` is a leaf
///   in the merkle tree rooted at `tree`. Used by the aggregation
///   circuit to resolve a leaf from a conditional claim's assumption
///   set. Carries no assumptions itself.
///
/// Merkle commitments carried by claims — both `CheckEnv.root` and every
/// `assumptions` root — may be canonical sorted+padded trees from
/// `merkle_root_canonical` or free-form trees from `merkle_join`. Verifiers
/// recover leaves or membership evidence according to the proof protocol.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Claim {
  /// `input` evaluates to `output`, optionally modulo `assumptions`.
  /// Check the input, then normalize its body to the output definition's body.
  /// The output is a safe standalone definition with the same universe parameter
  /// count and structurally equal erased type. Assumptions cover input dependencies.
  Eval {
    ctx: ClaimContext,
    input: Address,
    output: Address,
    assumptions: Option<Address>,
  },
  /// The constant at `const_addr` is well-typed, optionally modulo
  /// `assumptions`.
  Check { ctx: ClaimContext, const_addr: Address, assumptions: Option<Address> },
  /// Every constant in the env merkle-rooted at `root` is well-typed,
  /// optionally modulo `assumptions` (typically the env's axiom
  /// leaves).
  CheckEnv { ctx: ClaimContext, root: Address, assumptions: Option<Address> },
  /// Selective field revelation of a committed constant.
  Reveal { comm: Address, info: RevealConstantInfo },
  /// `const_addr` is a leaf in the merkle tree rooted at `tree`.
  Contains { tree: Address, const_addr: Address },
  /// A conjunction of unconditional `CheckEnv` claims, each under its own
  /// context, so members compiled under different role bindings (different
  /// Lean toolchains) meet in one statement: every claim whose digest
  /// ([`Claim::commit`]) is a leaf of the canonical merkle tree `members`
  /// holds. Formed only by aggregation (`ix_aggr` shape 16), from
  /// unconditional `CheckEnv` claims (validator 3 or 5) and other catalogs;
  /// there is no whole-catalog interpreter arm.
  Catalog { members: Address },
  /// Combined erased typing and resource admission of a complete addressed closure.
  Resource { root: Address, profile: Address },
  /// The role table with hash `binding` binds every role, and each bound
  /// constant meets its specification in the set with digest `spec`. It
  /// discharges the condition of the typing claims that assume their binding
  /// ([`ClaimContext::binding_assumed`]), once per aggregate.
  Binding { spec: Address, binding: Address },
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
// TagN variant layout for flags 0xE (data + claims) and 0xF (proofs)
// ============================================================================

/// TagN flag for commitments, AssumptionTree, and claims (0xE).
///
/// The header is `TagN(4, 0xE, variant)`. Variants 0–7 are in rung 1, the
/// single bytes `0xE0`–`0xE7`; from 8 on the header is two bytes (rung 2),
/// so Catalog is `E8 00`, Resource `E8 01` and Binding `E8 02`.
///
/// - 1: Comm (commitment, handled in `comm.rs`)
/// - 2: AssumptionTree (recursive merkle-tree data, see `assumption_tree.rs`)
/// - 3: Eval claim
/// - 4: Check claim
/// - 5: CheckEnv claim
/// - 6: Reveal claim
/// - 7: Contains claim
/// - 8: Catalog claim (`E8 00`)
/// - 9: Resource claim (`E8 01`)
/// - 10: Binding claim (`E8 02`)
///
/// The `.ixe` header also uses flag 0xE, with its storage envelope version:
/// legacy 4 is `0xE4` and the role-bound 5 is `0xE5`. Checked claims still bind
/// object format 4. Readers know which object they read; nothing dispatches
/// on the first byte alone.
pub const FLAG_CLAIM: u8 = 0xE;

// VARIANT 1 = Comm (handled in comm.rs)
pub const VARIANT_ASSUMPTION_TREE: u64 = 2;
pub const VARIANT_EVAL_CLAIM: u64 = 3;
pub const VARIANT_CHECK_CLAIM: u64 = 4;
pub const VARIANT_CHECK_ENV_CLAIM: u64 = 5;
pub const VARIANT_REVEAL_CLAIM: u64 = 6;
pub const VARIANT_CONTAINS_CLAIM: u64 = 7;
pub const VARIANT_CATALOG_CLAIM: u64 = 8;
pub const VARIANT_RESOURCE_CLAIM: u64 = 9;
pub const VARIANT_BINDING_CLAIM: u64 = 10;

/// TagN flag for ZK proofs (0xF). Every variant is in rung 1, a single-byte
/// tag (`0xF0`–`0xF7`), which uses every single byte; a later proof variant
/// takes a two-byte tag.
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
/// - 5: Catalog proof
/// - 6: Resource proof
/// - 7: Binding proof
pub const FLAG_PROOF: u8 = 0xF;

pub const VARIANT_EVAL_PROOF: u64 = 0;
pub const VARIANT_CHECK_PROOF: u64 = 1;
pub const VARIANT_CHECK_ENV_PROOF: u64 = 2;
pub const VARIANT_REVEAL_PROOF: u64 = 3;
pub const VARIANT_CONTAINS_PROOF: u64 = 4;
pub const VARIANT_CATALOG_PROOF: u64 = 5;
pub const VARIANT_RESOURCE_PROOF: u64 = 6;
pub const VARIANT_BINDING_PROOF: u64 = 7;

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

/// Refuse a reveal mask with a bit at or above `width`: the variant has `width`
/// fields, and a mask bit naming none of them would give one claim two
/// encodings.
fn require_mask(mask: u64, width: u32) -> Result<(), String> {
  if width < 64 && mask >> width != 0 {
    return Err(format!(
      "claim: reveal mask {mask} sets bits beyond its {width} fields"
    ));
  }
  Ok(())
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
  /// Serialize: mask (TagN) + field values in mask order.
  pub fn put(&self, buf: &mut Vec<u8>) {
    let mask = compute_mask(&[
      self.is_unsafe.is_some(),
      self.lvls.is_some(),
      self.cidx.is_some(),
      self.params.is_some(),
      self.fields.is_some(),
      self.typ.is_some(),
    ]);
    TagN::put(0, 0, mask, buf);
    if let Some(u) = self.is_unsafe {
      put_bool_field(u, buf);
    }
    if let Some(l) = self.lvls {
      TagN::put(0, 0, l, buf);
    }
    if let Some(c) = self.cidx {
      TagN::put(0, 0, c, buf);
    }
    if let Some(p) = self.params {
      TagN::put(0, 0, p, buf);
    }
    if let Some(f) = self.fields {
      TagN::put(0, 0, f, buf);
    }
    if let Some(t) = &self.typ {
      buf.extend_from_slice(t.as_bytes());
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let mask = TagN::get(0, buf)?.value;
    require_mask(mask, 6)?;
    let is_unsafe =
      if mask & 1 != 0 { Some(get_bool_field(buf)?) } else { None };
    let lvls =
      if mask & 2 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
    let cidx =
      if mask & 4 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
    let params =
      if mask & 8 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
    let fields =
      if mask & 16 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
    let typ = if mask & 32 != 0 { Some(get_address(buf)?) } else { None };
    Ok(RevealConstructorInfo { is_unsafe, lvls, cidx, params, fields, typ })
  }
}

// ============================================================================
// RevealRecursorRule serialization
// ============================================================================

impl RevealRecursorRule {
  pub fn put(&self, buf: &mut Vec<u8>) {
    TagN::put(0, 0, self.rule_idx, buf);
    TagN::put(0, 0, self.fields, buf);
    buf.extend_from_slice(self.rhs.as_bytes());
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let rule_idx = TagN::get(0, buf)?.value;
    let fields = TagN::get(0, buf)?.value;
    let rhs = get_address(buf)?;
    Ok(RevealRecursorRule { rule_idx, fields, rhs })
  }
}

// ============================================================================
// Helper: put/get rules and ctors arrays
// ============================================================================

fn put_rules(rules: &[RevealRecursorRule], buf: &mut Vec<u8>) {
  TagN::put(0, 0, rules.len() as u64, buf);
  for rule in rules {
    rule.put(buf);
  }
}

fn get_rules(buf: &mut &[u8]) -> Result<Vec<RevealRecursorRule>, String> {
  let count =
    usize::try_from(TagN::get(0, buf)?.value).map_err(|e| e.to_string())?;
  let mut rules = Vec::with_capacity(count);
  for _ in 0..count {
    rules.push(RevealRecursorRule::get(buf)?);
  }
  Ok(rules)
}

fn put_ctors(ctors: &[(u64, RevealConstructorInfo)], buf: &mut Vec<u8>) {
  TagN::put(0, 0, ctors.len() as u64, buf);
  for (idx, info) in ctors {
    TagN::put(0, 0, *idx, buf);
    info.put(buf);
  }
}

fn get_ctors(
  buf: &mut &[u8],
) -> Result<Vec<(u64, RevealConstructorInfo)>, String> {
  let count =
    usize::try_from(TagN::get(0, buf)?.value).map_err(|e| e.to_string())?;
  let mut ctors = Vec::with_capacity(count);
  for _ in 0..count {
    let idx = TagN::get(0, buf)?.value;
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
        TagN::put(0, 0, mask, buf);
        if let Some(k) = kind {
          put_def_kind(*k, buf);
        }
        if let Some(s) = safety {
          put_def_safety(*s, buf);
        }
        if let Some(l) = lvls {
          TagN::put(0, 0, *l, buf);
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
        TagN::put(0, 0, mask, buf);
        if let Some(u) = is_unsafe {
          put_bool_field(*u, buf);
        }
        if let Some(l) = lvls {
          TagN::put(0, 0, *l, buf);
        }
        if let Some(p) = params {
          TagN::put(0, 0, *p, buf);
        }
        if let Some(i) = indices {
          TagN::put(0, 0, *i, buf);
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
        TagN::put(0, 0, mask, buf);
        if let Some(k) = k {
          put_bool_field(*k, buf);
        }
        if let Some(u) = is_unsafe {
          put_bool_field(*u, buf);
        }
        if let Some(l) = lvls {
          TagN::put(0, 0, *l, buf);
        }
        if let Some(p) = params {
          TagN::put(0, 0, *p, buf);
        }
        if let Some(i) = indices {
          TagN::put(0, 0, *i, buf);
        }
        if let Some(m) = motives {
          TagN::put(0, 0, *m, buf);
        }
        if let Some(m) = minors {
          TagN::put(0, 0, *m, buf);
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
    let mask = TagN::get(0, buf)?.value;
    require_mask(
      mask,
      match variant {
        0 => 5,
        1 => 6,
        2 => 9,
        _ => 64,
      },
    )?;
    match variant {
      0 => {
        let kind = if mask & 1 != 0 { Some(get_def_kind(buf)?) } else { None };
        let safety =
          if mask & 2 != 0 { Some(get_def_safety(buf)?) } else { None };
        let lvls =
          if mask & 4 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let typ = if mask & 8 != 0 { Some(get_address(buf)?) } else { None };
        let value = if mask & 16 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::Defn { kind, safety, lvls, typ, value })
      },
      1 => {
        let is_unsafe =
          if mask & 1 != 0 { Some(get_bool_field(buf)?) } else { None };
        let lvls =
          if mask & 2 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let params =
          if mask & 4 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let indices =
          if mask & 8 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let typ = if mask & 16 != 0 { Some(get_address(buf)?) } else { None };
        let ctors = if mask & 32 != 0 { Some(get_ctors(buf)?) } else { None };
        Ok(Self::Indc { is_unsafe, lvls, params, indices, typ, ctors })
      },
      2 => {
        let k = if mask & 1 != 0 { Some(get_bool_field(buf)?) } else { None };
        let is_unsafe =
          if mask & 2 != 0 { Some(get_bool_field(buf)?) } else { None };
        let lvls =
          if mask & 4 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let params =
          if mask & 8 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let indices =
          if mask & 16 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let motives =
          if mask & 32 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let minors =
          if mask & 64 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
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
  /// Serialize: variant byte + mask (TagN) + field values in mask order.
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
        TagN::put(0, 0, mask, buf);
        if let Some(k) = kind {
          put_def_kind(*k, buf);
        }
        if let Some(s) = safety {
          put_def_safety(*s, buf);
        }
        if let Some(l) = lvls {
          TagN::put(0, 0, *l, buf);
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
        TagN::put(0, 0, mask, buf);
        if let Some(k) = k {
          put_bool_field(*k, buf);
        }
        if let Some(u) = is_unsafe {
          put_bool_field(*u, buf);
        }
        if let Some(l) = lvls {
          TagN::put(0, 0, *l, buf);
        }
        if let Some(p) = params {
          TagN::put(0, 0, *p, buf);
        }
        if let Some(i) = indices {
          TagN::put(0, 0, *i, buf);
        }
        if let Some(m) = motives {
          TagN::put(0, 0, *m, buf);
        }
        if let Some(m) = minors {
          TagN::put(0, 0, *m, buf);
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
        TagN::put(0, 0, mask, buf);
        if let Some(u) = is_unsafe {
          put_bool_field(*u, buf);
        }
        if let Some(l) = lvls {
          TagN::put(0, 0, *l, buf);
        }
        if let Some(t) = typ {
          buf.extend_from_slice(t.as_bytes());
        }
      },
      Self::Quot { kind, lvls, typ } => {
        buf.push(3);
        let mask =
          compute_mask(&[kind.is_some(), lvls.is_some(), typ.is_some()]);
        TagN::put(0, 0, mask, buf);
        if let Some(k) = kind {
          put_quot_kind(*k, buf);
        }
        if let Some(l) = lvls {
          TagN::put(0, 0, *l, buf);
        }
        if let Some(t) = typ {
          buf.extend_from_slice(t.as_bytes());
        }
      },
      Self::CPrj { idx, cidx, block } => {
        buf.push(4);
        let mask =
          compute_mask(&[idx.is_some(), cidx.is_some(), block.is_some()]);
        TagN::put(0, 0, mask, buf);
        if let Some(i) = idx {
          TagN::put(0, 0, *i, buf);
        }
        if let Some(c) = cidx {
          TagN::put(0, 0, *c, buf);
        }
        if let Some(b) = block {
          buf.extend_from_slice(b.as_bytes());
        }
      },
      Self::RPrj { idx, block } => {
        buf.push(5);
        let mask = compute_mask(&[idx.is_some(), block.is_some()]);
        TagN::put(0, 0, mask, buf);
        if let Some(i) = idx {
          TagN::put(0, 0, *i, buf);
        }
        if let Some(b) = block {
          buf.extend_from_slice(b.as_bytes());
        }
      },
      Self::IPrj { idx, block } => {
        buf.push(6);
        let mask = compute_mask(&[idx.is_some(), block.is_some()]);
        TagN::put(0, 0, mask, buf);
        if let Some(i) = idx {
          TagN::put(0, 0, *i, buf);
        }
        if let Some(b) = block {
          buf.extend_from_slice(b.as_bytes());
        }
      },
      Self::DPrj { idx, block } => {
        buf.push(7);
        let mask = compute_mask(&[idx.is_some(), block.is_some()]);
        TagN::put(0, 0, mask, buf);
        if let Some(i) = idx {
          TagN::put(0, 0, *i, buf);
        }
        if let Some(b) = block {
          buf.extend_from_slice(b.as_bytes());
        }
      },
      Self::Muts { components } => {
        buf.push(8);
        let mask: u64 = if components.is_empty() { 0 } else { 1 };
        TagN::put(0, 0, mask, buf);
        if !components.is_empty() {
          TagN::put(0, 0, components.len() as u64, buf);
          for (idx, info) in components {
            TagN::put(0, 0, *idx, buf);
            info.put(buf);
          }
        }
      },
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let variant = get_u8(buf)?;
    let mask = TagN::get(0, buf)?.value;
    require_mask(
      mask,
      match variant {
        0 => 5,
        1 => 9,
        2..=4 => 3,
        5..=7 => 2,
        8 => 1,
        _ => 64,
      },
    )?;
    match variant {
      0 => {
        // Defn
        let kind = if mask & 1 != 0 { Some(get_def_kind(buf)?) } else { None };
        let safety =
          if mask & 2 != 0 { Some(get_def_safety(buf)?) } else { None };
        let lvls =
          if mask & 4 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
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
          if mask & 4 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let params =
          if mask & 8 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let indices =
          if mask & 16 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let motives =
          if mask & 32 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let minors =
          if mask & 64 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
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
          if mask & 2 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let typ = if mask & 4 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::Axio { is_unsafe, lvls, typ })
      },
      3 => {
        // Quot
        let kind = if mask & 1 != 0 { Some(get_quot_kind(buf)?) } else { None };
        let lvls =
          if mask & 2 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let typ = if mask & 4 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::Quot { kind, lvls, typ })
      },
      4 => {
        // CPrj
        let idx =
          if mask & 1 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let cidx =
          if mask & 2 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let block = if mask & 4 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::CPrj { idx, cidx, block })
      },
      5 => {
        // RPrj
        let idx =
          if mask & 1 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let block = if mask & 2 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::RPrj { idx, block })
      },
      6 => {
        // IPrj
        let idx =
          if mask & 1 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let block = if mask & 2 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::IPrj { idx, block })
      },
      7 => {
        // DPrj
        let idx =
          if mask & 1 != 0 { Some(TagN::get(0, buf)?.value) } else { None };
        let block = if mask & 2 != 0 { Some(get_address(buf)?) } else { None };
        Ok(Self::DPrj { idx, block })
      },
      8 => {
        // Muts
        let components = if mask & 1 != 0 {
          let count = usize::try_from(TagN::get(0, buf)?.value)
            .map_err(|e| e.to_string())?;
          let mut comps = Vec::with_capacity(count);
          for _ in 0..count {
            let idx = TagN::get(0, buf)?.value;
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

/// The validator a claim's scope names, after the object format.
///
/// - `0`, structural-v1: `Reveal` and `Contains`, which read bytes only.
/// - `1`, erased-lean-v1: retired. It named typing claims whose primitives
///   were recognized by fixed addresses and which admitted any axiom; readers
///   refuse it rather than read such a claim as a newer one.
/// - `2`, resource-v1: `Resource`.
/// - `3`, erased-lean-v2: the typing claims, relative to their
///   [`ClaimContext`], and `Binding`.
/// - `4`, erased-lean-v2-assumed: a `Check` or `CheckEnv` claim that assumes
///   its binding meets the specifications instead of validating it
///   ([`ClaimContext::binding_assumed`]); its typing holds if the `Binding`
///   claim for its context does.
/// - `5`, erased-lean-v2-class: a `CheckEnv` claim relative to a literal
///   class instead of one binding ([`ClaimContext::literal_class`]); its
///   typing holds under every binding of that class that meets the
///   specifications.
pub const VALIDATOR_STRUCTURAL: u8 = 0;
pub const VALIDATOR_ERASED_LEAN_RETIRED: u8 = 1;
pub const VALIDATOR_RESOURCE: u8 = 2;
pub const VALIDATOR_ERASED_LEAN: u8 = 3;
pub const VALIDATOR_ERASED_LEAN_ASSUMED: u8 = 4;
pub const VALIDATOR_ERASED_LEAN_CLASS: u8 = 5;

fn validator_for_variant(variant: u64) -> u8 {
  match variant {
    VARIANT_REVEAL_CLAIM | VARIANT_CONTAINS_CLAIM => VALIDATOR_STRUCTURAL,
    VARIANT_RESOURCE_CLAIM => VALIDATOR_RESOURCE,
    _ => VALIDATOR_ERASED_LEAN,
  }
}
/// Whether claims of variant `variant` may assume their binding: `Check`
/// and `CheckEnv`.
fn variant_may_assume(variant: u64) -> bool {
  variant == VARIANT_CHECK_CLAIM || variant == VARIANT_CHECK_ENV_CLAIM
}
fn put_scope(validator: u8, buf: &mut Vec<u8>) {
  buf.extend_from_slice(&[Env::OBJECT_FORMAT, validator]);
}
/// Read the scope of a claim of variant `variant`; returns its validator:
/// the variant's, [`VALIDATOR_ERASED_LEAN_ASSUMED`] for `Check` and
/// `CheckEnv`, or [`VALIDATOR_ERASED_LEAN_CLASS`] for `CheckEnv`. Any other
/// byte is refused.
fn get_scope(variant: u64, buf: &mut &[u8]) -> Result<u8, String> {
  let validator = validator_for_variant(variant);
  let format = get_u8(buf)?;
  if format != Env::OBJECT_FORMAT {
    return Err(format!(
      "claim: unsupported object format {format}, expected {} — regenerate \
       the claim",
      Env::OBJECT_FORMAT
    ));
  }
  let found = get_u8(buf)?;
  if found == validator
    || (found == VALIDATOR_ERASED_LEAN_ASSUMED && variant_may_assume(variant))
    || (found == VALIDATOR_ERASED_LEAN_CLASS
      && variant == VARIANT_CHECK_ENV_CLAIM)
  {
    return Ok(found);
  }
  if validator == VALIDATOR_ERASED_LEAN
    && found == VALIDATOR_ERASED_LEAN_RETIRED
  {
    return Err(
      "claim: validator erased-lean-v1 is retired — regenerate the claim"
        .into(),
    );
  }
  Err("claim: wrong validator identity".into())
}

impl ClaimContext {
  pub fn put(&self, buf: &mut Vec<u8>) {
    buf.extend_from_slice(self.spec.as_bytes());
    buf.extend_from_slice(self.binding.as_bytes());
    put_opt_addr(&self.axioms, buf);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let spec = get_address(buf)?;
    let binding = get_address(buf)?;
    let axioms = get_opt_addr(buf)?;
    Ok(ClaimContext {
      spec,
      binding,
      axioms,
      binding_assumed: false,
      literal_class: false,
    })
  }

  /// The context of a claim made today over `env`'s own role binding: this
  /// specification set ([`SPEC_DIGEST`]) and no axiom beyond the standard
  /// three, validating the binding. Fails when the environment carries no
  /// binding.
  pub fn for_env(env: &Env) -> Result<Self, String> {
    let binding = env.role_binding.as_ref().ok_or_else(|| {
      "claim context: the environment carries no role binding".to_string()
    })?;
    Ok(ClaimContext {
      spec: spec_digest(),
      binding: binding.address.clone(),
      axioms: None,
      binding_assumed: false,
      literal_class: false,
    })
  }

  /// The context of a `CheckEnv` claim under the literal class `class`:
  /// this specification set and no axiom beyond the standard three.
  pub fn for_literal_class(class: Address) -> Self {
    ClaimContext {
      spec: spec_digest(),
      binding: class,
      axioms: None,
      binding_assumed: false,
      literal_class: true,
    }
  }

  /// This context, assuming its binding meets the specifications.
  pub fn assuming_binding(mut self) -> Self {
    self.binding_assumed = true;
    self
  }
}

/// The specification digest (`Ix.SpecDigest.specDigest`): BLAKE3 of the
/// canonical encoding of the role specifications. Pinned here and checked
/// against the Lean value by the `claim` test suite.
pub const SPEC_DIGEST_HEX: &str =
  "f09825902503729718c7ab437405b9f87efb97024085f8f2ea10e1e3ca378ba3";

/// [`SPEC_DIGEST_HEX`] as an address.
pub fn spec_digest() -> Address {
  Address::from_hex(SPEC_DIGEST_HEX).expect("SPEC_DIGEST_HEX is 32 hex bytes")
}

impl Claim {
  /// The bytes after the scope, shared by claims and proofs.
  fn put_payload(&self, buf: &mut Vec<u8>) {
    match self {
      Claim::Eval { ctx, input, output, assumptions } => {
        ctx.put(buf);
        buf.extend_from_slice(input.as_bytes());
        buf.extend_from_slice(output.as_bytes());
        put_opt_addr(assumptions, buf);
      },
      Claim::Check { ctx, const_addr, assumptions } => {
        ctx.put(buf);
        buf.extend_from_slice(const_addr.as_bytes());
        put_opt_addr(assumptions, buf);
      },
      Claim::CheckEnv { ctx, root, assumptions } => {
        ctx.put(buf);
        buf.extend_from_slice(root.as_bytes());
        put_opt_addr(assumptions, buf);
      },
      Claim::Reveal { comm, info } => {
        buf.extend_from_slice(comm.as_bytes());
        info.put(buf);
      },
      Claim::Contains { tree, const_addr } => {
        buf.extend_from_slice(tree.as_bytes());
        buf.extend_from_slice(const_addr.as_bytes());
      },
      Claim::Catalog { members } => {
        // A two-byte claim tag: `E8 00` on the wire.
        buf.extend_from_slice(members.as_bytes());
      },
      Claim::Resource { root, profile } => {
        buf.extend_from_slice(root.as_bytes());
        buf.extend_from_slice(profile.as_bytes());
      },
      Claim::Binding { spec, binding } => {
        // A two-byte claim tag: `E8 02` on the wire.
        buf.extend_from_slice(spec.as_bytes());
        buf.extend_from_slice(binding.as_bytes());
      },
    }
  }

  /// Read the bytes after the scope of claim variant `variant`; `validator`
  /// is what the scope said ([`get_scope`]).
  fn get_payload(
    variant: u64,
    validator: u8,
    buf: &mut &[u8],
  ) -> Result<Self, String> {
    let assumed = validator == VALIDATOR_ERASED_LEAN_ASSUMED;
    match variant {
      VARIANT_EVAL_CLAIM => {
        let ctx = ClaimContext::get(buf)?;
        let input = get_address(buf)?;
        let output = get_address(buf)?;
        let assumptions = get_opt_addr(buf)?;
        Ok(Claim::Eval { ctx, input, output, assumptions })
      },
      VARIANT_CHECK_CLAIM => {
        let mut ctx = ClaimContext::get(buf)?;
        ctx.binding_assumed = assumed;
        let const_addr = get_address(buf)?;
        let assumptions = get_opt_addr(buf)?;
        Ok(Claim::Check { ctx, const_addr, assumptions })
      },
      VARIANT_CHECK_ENV_CLAIM => {
        let mut ctx = ClaimContext::get(buf)?;
        ctx.binding_assumed = assumed;
        ctx.literal_class = validator == VALIDATOR_ERASED_LEAN_CLASS;
        let root = get_address(buf)?;
        let assumptions = get_opt_addr(buf)?;
        Ok(Claim::CheckEnv { ctx, root, assumptions })
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
      VARIANT_CATALOG_CLAIM => {
        Ok(Claim::Catalog { members: get_address(buf)? })
      },
      VARIANT_RESOURCE_CLAIM => Ok(Claim::Resource {
        root: get_address(buf)?,
        profile: get_address(buf)?,
      }),
      VARIANT_BINDING_CLAIM => Ok(Claim::Binding {
        spec: get_address(buf)?,
        binding: get_address(buf)?,
      }),
      x => {
        Err(format!("Claim::get: invalid claim variant {x} under flag 0xE",))
      },
    }
  }

  /// The validator the claim's scope names: its variant's,
  /// [`VALIDATOR_ERASED_LEAN_ASSUMED`] for a `Check` or `CheckEnv` claim
  /// that assumes its binding, or [`VALIDATOR_ERASED_LEAN_CLASS`] for a
  /// `CheckEnv` claim under a literal class. Only those carry the flags on
  /// the wire; the other typing claims always validate one binding.
  pub fn validator(&self) -> u8 {
    match self {
      Claim::CheckEnv { ctx, .. } if ctx.literal_class => {
        VALIDATOR_ERASED_LEAN_CLASS
      },
      Claim::Check { ctx, .. } | Claim::CheckEnv { ctx, .. }
        if ctx.binding_assumed =>
      {
        VALIDATOR_ERASED_LEAN_ASSUMED
      },
      _ => validator_for_variant(self.proof_variant_size() + 3),
    }
  }

  pub fn put(&self, buf: &mut Vec<u8>) {
    TagN::put(4, FLAG_CLAIM, self.proof_variant_size() + 3, buf);
    put_scope(self.validator(), buf);
    self.put_payload(buf);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let tag = TagN::get(4, buf)?;
    if tag.flag != FLAG_CLAIM {
      return Err(format!(
        "Claim::get: expected flag 0x{:X}, got 0x{:X}",
        FLAG_CLAIM, tag.flag
      ));
    }
    let validator = get_scope(tag.value, buf)?;
    Self::get_payload(tag.value, validator, buf)
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    let mut rest = bytes;
    let claim = Self::get(&mut rest)?;
    if !rest.is_empty() {
      return Err("claim: trailing bytes".into());
    }
    Ok(claim)
  }

  /// Serialize a claim and compute its content address.
  pub fn commit(&self) -> (Address, Vec<u8>) {
    let mut buf = Vec::new();
    self.put(&mut buf);
    let addr = Address::hash(&buf);
    (addr, buf)
  }

  /// The claim's context, for the typing claims.
  pub fn context(&self) -> Option<&ClaimContext> {
    match self {
      Claim::Eval { ctx, .. }
      | Claim::Check { ctx, .. }
      | Claim::CheckEnv { ctx, .. } => Some(ctx),
      Claim::Reveal { .. }
      | Claim::Contains { .. }
      | Claim::Catalog { .. }
      | Claim::Resource { .. }
      | Claim::Binding { .. } => None,
    }
  }

  /// Map a claim to its corresponding proof variant size (under flag 0xF).
  pub fn proof_variant_size(&self) -> u64 {
    match self {
      Claim::Eval { .. } => VARIANT_EVAL_PROOF,
      Claim::Check { .. } => VARIANT_CHECK_PROOF,
      Claim::CheckEnv { .. } => VARIANT_CHECK_ENV_PROOF,
      Claim::Reveal { .. } => VARIANT_REVEAL_PROOF,
      Claim::Contains { .. } => VARIANT_CONTAINS_PROOF,
      Claim::Catalog { .. } => VARIANT_CATALOG_PROOF,
      Claim::Resource { .. } => VARIANT_RESOURCE_PROOF,
      Claim::Binding { .. } => VARIANT_BINDING_PROOF,
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
    TagN::put(4, FLAG_PROOF, proof_size, buf);
    put_scope(self.claim.validator(), buf);
    self.claim.put_payload(buf);
    // Opaque ZK proof bytes: length prefix + data
    TagN::put(0, 0, self.proof.len() as u64, buf);
    buf.extend_from_slice(&self.proof);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let tag = TagN::get(4, buf)?;
    if tag.flag != FLAG_PROOF {
      return Err(format!(
        "Proof::get: expected flag 0x{:X}, got 0x{:X}",
        FLAG_PROOF, tag.flag
      ));
    }
    if tag.value > VARIANT_BINDING_PROOF {
      return Err(format!(
        "Proof::get: invalid proof variant {} under flag 0xF",
        tag.value
      ));
    }
    let validator = get_scope(tag.value + 3, buf)?;
    let claim = Claim::get_payload(tag.value + 3, validator, buf)?;

    // Opaque ZK proof bytes
    let len = usize::try_from(TagN::get(0, buf)?.value)
      .map_err(|_e| "Proof::get: TagN size overflows usize".to_string())?;
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
  use crate::merkle::{merkle_join, merkle_root_canonical};
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

  /// A context that validates its binding. Only `Check` and `CheckEnv` may
  /// assume it (`gen_assumable_ctx`).
  impl Arbitrary for ClaimContext {
    fn arbitrary(g: &mut Gen) -> Self {
      ClaimContext {
        spec: Address::arbitrary(g),
        binding: Address::arbitrary(g),
        axioms: gen_opt_addr(g),
        binding_assumed: false,
        literal_class: false,
      }
    }
  }

  /// A context for `Check` or `CheckEnv`, which may assume its binding.
  fn gen_assumable_ctx(g: &mut Gen) -> ClaimContext {
    ClaimContext {
      binding_assumed: bool::arbitrary(g),
      ..ClaimContext::arbitrary(g)
    }
  }

  /// A context for `CheckEnv`, which may also be under a literal class.
  fn gen_check_env_ctx(g: &mut Gen) -> ClaimContext {
    match u8::arbitrary(g) % 3 {
      0 => ClaimContext::arbitrary(g),
      1 => ClaimContext { binding_assumed: true, ..ClaimContext::arbitrary(g) },
      _ => ClaimContext { literal_class: true, ..ClaimContext::arbitrary(g) },
    }
  }

  /// A fixed context: this specification set, a stand-in binding hash, the
  /// standard axioms only.
  fn test_ctx() -> ClaimContext {
    ClaimContext {
      spec: spec_digest(),
      binding: Address::hash(b"binding"),
      axioms: None,
      binding_assumed: false,
      literal_class: false,
    }
  }

  impl Arbitrary for Claim {
    fn arbitrary(g: &mut Gen) -> Self {
      match u8::arbitrary(g) % 8 {
        0 => Claim::Eval {
          ctx: ClaimContext::arbitrary(g),
          input: Address::arbitrary(g),
          output: Address::arbitrary(g),
          assumptions: gen_opt_addr(g),
        },
        1 => Claim::Check {
          ctx: gen_assumable_ctx(g),
          const_addr: Address::arbitrary(g),
          assumptions: gen_opt_addr(g),
        },
        2 => Claim::CheckEnv {
          ctx: gen_check_env_ctx(g),
          root: Address::arbitrary(g),
          assumptions: gen_opt_addr(g),
        },
        6 => Claim::Binding {
          spec: Address::arbitrary(g),
          binding: Address::arbitrary(g),
        },
        3 => Claim::Reveal {
          comm: Address::arbitrary(g),
          info: RevealConstantInfo::arbitrary(g),
        },
        4 => Claim::Catalog { members: Address::arbitrary(g) },
        5 => Claim::Resource {
          root: Address::arbitrary(g),
          profile: Address::arbitrary(g),
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

  /// A reveal mask bit beyond the variant's fields is refused, so one claim
  /// has one encoding. The Lean reader refuses the same bytes
  /// (`Tests/Ix/Claim.lean`, `revealMaskTests`): a Reveal claim over the zero
  /// commitment, its variant byte, then the one-byte mask.
  #[test]
  fn reveal_mask_refuses_unknown_bits() {
    let mut header = vec![0xE6, 0x04, 0x00];
    header.extend_from_slice(&[0u8; 32]);
    for (variant, unknown) in [(0u8, 0x20u8), (2, 0x08), (7, 0x04)] {
      let mut bytes = header.clone();
      bytes.extend_from_slice(&[variant, 0x00]);
      assert!(Claim::from_bytes(&bytes).is_ok(), "variant {variant}");
      let last = bytes.len() - 1;
      bytes[last] = unknown;
      let err = Claim::from_bytes(&bytes).unwrap_err();
      assert!(err.contains("reveal mask"), "{err}");
    }
  }

  /// The catalog claim's exact wire form is a cross-serializer
  /// commitment (the Rust↔Lean digest-parity gate pins the same bytes
  /// from the Lean side): the first multi-byte claim tag, TagN `0xE8 0x00`,
  /// the scope (object format, validator erased-lean-v2), then the members
  /// root: a catalog has no context of its own (each member claim carries
  /// one) and is unconditional. A drift here changes every catalog digest.
  #[test]
  fn catalog_claim_wire_bytes_pinned() {
    let members = Address::hash(b"members");
    let claim = Claim::Catalog { members: members.clone() };
    let (addr, bytes) = claim.commit();
    let mut expected = vec![0xE8, 0x00, 4, VALIDATOR_ERASED_LEAN];
    expected.extend_from_slice(members.as_bytes());
    assert_eq!(bytes, expected, "catalog claim wire bytes drifted");
    assert_eq!(addr, Address::hash(&expected));
    // Cross-language digest pin: `Tests/Ix/Claim.lean` asserts the
    // SAME hex from the Lean serializer over the same fixture — the
    // two serializers cannot drift on the large-tag path unnoticed.
    assert_eq!(
      addr.hex(),
      "4f5686bd1a8386231370703d58223aca769c82c835964d4914ca41305a8030f3",
      "catalog claim digest drifted"
    );
    assert_eq!(bytes.len(), 2 + 2 + 32);
    // The proof wrapper stays a single-byte tag: 0xF5.
    let proof = Proof::new(claim, Vec::new());
    let mut pbuf = Vec::new();
    proof.put(&mut pbuf);
    assert_eq!(pbuf[0], 0xF5, "catalog proof wrapper tag drifted");
    let back = Proof::get(&mut pbuf.as_slice()).expect("proof roundtrip");
    assert_eq!(back, proof);
  }

  /// A typing claim made for the retired erased-lean-v1 validator is refused,
  /// never read as an erased-lean-v2 claim.
  #[test]
  fn retired_validator_refused() {
    let claim = Claim::Check {
      ctx: test_ctx(),
      const_addr: Address::hash(b"value"),
      assumptions: None,
    };
    let mut bytes = Vec::new();
    claim.put(&mut bytes);
    assert_eq!(bytes[2], VALIDATOR_ERASED_LEAN);
    bytes[2] = VALIDATOR_ERASED_LEAN_RETIRED;
    let err = Claim::from_bytes(&bytes).unwrap_err();
    assert!(err.contains("erased-lean-v1 is retired"), "{err}");
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
      ctx: test_ctx(),
      input: Address::hash(b"input"),
      output: Address::hash(b"output"),
      assumptions: None,
    };
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_eval_claim_with_asm_roundtrip() {
    let claim = Claim::Eval {
      ctx: test_ctx(),
      input: Address::hash(b"input"),
      output: Address::hash(b"output"),
      assumptions: Some(Address::hash(b"asm")),
    };
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_check_claim_no_asm_roundtrip() {
    let claim = Claim::Check {
      ctx: test_ctx(),
      const_addr: Address::hash(b"value"),
      assumptions: None,
    };
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_check_claim_with_asm_roundtrip() {
    let claim = Claim::Check {
      ctx: test_ctx(),
      const_addr: Address::hash(b"value"),
      assumptions: Some(Address::hash(b"asm")),
    };
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_check_env_claim_no_asm_roundtrip() {
    let claim = Claim::CheckEnv {
      ctx: test_ctx(),
      root: Address::hash(b"env-root"),
      assumptions: None,
    };
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_check_env_claim_with_asm_roundtrip() {
    let claim = Claim::CheckEnv {
      ctx: test_ctx(),
      root: Address::hash(b"env-root"),
      assumptions: Some(Address::hash(b"asm")),
    };
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_check_env_claim_accepts_structural_root() {
    let a = Address::hash(b"structural-a");
    let b = Address::hash(b"structural-b");
    let c = Address::hash(b"structural-c");
    let left = merkle_root_canonical(&[a.clone(), b.clone()]).unwrap();
    let right = merkle_root_canonical(std::slice::from_ref(&c)).unwrap();
    let root = merkle_join(&left, &right);
    assert_ne!(root, merkle_root_canonical(&[a, b, c]).unwrap());
    assert!(claim_roundtrip(&Claim::CheckEnv {
      ctx: test_ctx(),
      root,
      assumptions: None
    }));
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
        ctx: test_ctx(),
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
      Claim::Check {
        ctx: test_ctx(),
        const_addr: Address::hash(b"value"),
        assumptions: None,
      },
      vec![5, 6, 7, 8, 9],
    );
    assert!(proof_roundtrip(&proof));
  }

  #[test]
  fn test_check_env_proof_roundtrip() {
    let proof = Proof::new(
      Claim::CheckEnv {
        ctx: test_ctx(),
        root: Address::hash(b"env-root"),
        assumptions: None,
      },
      vec![0x11, 0x22],
    );
    assert!(proof_roundtrip(&proof));
  }

  #[test]
  fn test_check_proof_with_asm_roundtrip() {
    let proof = Proof::new(
      Claim::Check {
        ctx: test_ctx(),
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
        ctx: test_ctx(),
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

  // ---------- TagN flag/size dispatch ----------

  fn parse_tag(bytes: &[u8]) -> TagN {
    TagN::get(4, &mut &bytes[..]).unwrap()
  }

  fn claim_tag(claim: &Claim) -> TagN {
    let mut buf = Vec::new();
    claim.put(&mut buf);
    parse_tag(&buf)
  }

  fn proof_tag(proof: &Proof) -> TagN {
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
        Claim::Eval {
          ctx: test_ctx(),
          input: a.clone(),
          output: b.clone(),
          assumptions: None,
        },
        VARIANT_EVAL_CLAIM,
      ),
      (
        Claim::Check {
          ctx: test_ctx(),
          const_addr: a.clone(),
          assumptions: None,
        },
        VARIANT_CHECK_CLAIM,
      ),
      (
        Claim::CheckEnv { ctx: test_ctx(), root: a.clone(), assumptions: None },
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
      assert_eq!(tag.value, expected_size);
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
        Claim::Eval {
          ctx: test_ctx(),
          input: a.clone(),
          output: b.clone(),
          assumptions: None,
        },
        VARIANT_EVAL_PROOF,
      ),
      (
        Claim::Check {
          ctx: test_ctx(),
          const_addr: a.clone(),
          assumptions: None,
        },
        VARIANT_CHECK_PROOF,
      ),
      (
        Claim::CheckEnv { ctx: test_ctx(), root: a.clone(), assumptions: None },
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
      assert_eq!(tag.value, expected_size);
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

    // Single-byte TagN + scope + context (spec, binding, no axioms) +
    // payload + 1 opt byte (+ 32 if Some).
    assert_eq!(
      claim_bytes(&Claim::Eval {
        ctx: test_ctx(),
        input: a.clone(),
        output: b.clone(),
        assumptions: None
      })
      .len(),
      1 + 2 + 65 + 64 + 1,
      "Eval no-asm = 133 bytes"
    );
    assert_eq!(
      claim_bytes(&Claim::Eval {
        ctx: test_ctx(),
        input: a.clone(),
        output: b.clone(),
        assumptions: Some(asm.clone())
      })
      .len(),
      1 + 2 + 65 + 64 + 1 + 32,
      "Eval with-asm = 165 bytes"
    );
    assert_eq!(
      claim_bytes(&Claim::Check {
        ctx: test_ctx(),
        const_addr: a.clone(),
        assumptions: None
      })
      .len(),
      1 + 2 + 65 + 32 + 1,
      "Check no-asm = 101 bytes"
    );
    assert_eq!(
      claim_bytes(&Claim::Check {
        ctx: test_ctx(),
        const_addr: a.clone(),
        assumptions: Some(asm.clone())
      })
      .len(),
      1 + 2 + 65 + 32 + 1 + 32,
      "Check with-asm = 133 bytes"
    );
    assert_eq!(
      claim_bytes(&Claim::CheckEnv {
        ctx: test_ctx(),
        root: a.clone(),
        assumptions: None
      })
      .len(),
      1 + 2 + 65 + 32 + 1,
      "CheckEnv no-asm = 101 bytes"
    );
    assert_eq!(
      claim_bytes(&Claim::Contains { tree: a, const_addr: b }).len(),
      1 + 2 + 64,
      "Contains = 67 bytes"
    );
  }

  #[test]
  fn test_claim_first_byte() {
    // Single-byte TagN encoding: size 0-7 fits in one byte (0xE0..0xE7).
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
        Claim::Eval {
          ctx: test_ctx(),
          input: a.clone(),
          output: b.clone(),
          assumptions: None,
        },
        0xE3,
      ),
      (
        Claim::Check {
          ctx: test_ctx(),
          const_addr: a.clone(),
          assumptions: None,
        },
        0xE4,
      ),
      (
        Claim::CheckEnv { ctx: test_ctx(), root: a.clone(), assumptions: None },
        0xE5,
      ),
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
        Claim::Eval {
          ctx: test_ctx(),
          input: a.clone(),
          output: b.clone(),
          assumptions: None,
        },
        0xF0,
      ),
      (
        Claim::Check {
          ctx: test_ctx(),
          const_addr: a.clone(),
          assumptions: None,
        },
        0xF1,
      ),
      (
        Claim::CheckEnv { ctx: test_ctx(), root: a.clone(), assumptions: None },
        0xF2,
      ),
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
    assert_eq!(buf[0], 0xE6); // TagN f=4: flag=0xE, value=6 (Reveal claim)
    // buf[3..35] = comm_addr (32 bytes)
    assert_eq!(buf[35], 0x00); // RevealConstantInfo variant: Definition
    assert_eq!(buf[36], 0x02); // mask: bit 1 (safety)
    assert_eq!(buf[37], 0x01); // DefinitionSafety::Safe
    assert_eq!(buf.len(), 38); // Total: 1 + 2 + 32 + 1 + 1 + 1 = 38 bytes
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
    assert_eq!(buf[35], 0x00); // RevealConstantInfo variant: Definition
    assert_eq!(buf[36], 0x08); // mask: bit 3 (typ)
    // buf[35..67] = typ address (32 bytes)
    assert_eq!(buf.len(), 69); // Total: 1 + 2 + 32 + 1 + 1 + 32 = 69 bytes
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
    assert_eq!(buf[35], 0x08); // RevealConstantInfo variant: Muts
    assert_eq!(buf[36], 0x01); // mask: bit 0 (components)
    assert_eq!(buf[37], 0x01); // TagN f=0: 1 component revealed
    assert_eq!(buf[38], 0x02); // TagN f=0: component index 2
    assert_eq!(buf[39], 0x00); // RevealMutConstInfo variant: Definition
    assert_eq!(buf[40], 0x02); // mask: bit 1 (safety)
    assert_eq!(buf[41], 0x01); // DefinitionSafety::Safe
    assert_eq!(buf.len(), 42); // Total: 1 + 32 + 7 = 40 bytes
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
  #[test]
  fn v4_claim_fixtures_and_strict_scope() {
    for line in
      include_str!("../../../Tests/Fixtures/ixon-v4/claims.tsv").lines()
    {
      if line.starts_with('#') || line.is_empty() {
        continue;
      }
      let fields: Vec<_> = line.split('\t').collect();
      let bytes: Vec<_> = fields[2]
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
          u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap()
        })
        .collect();
      let claim = Claim::from_bytes(&bytes).unwrap();
      let (address, encoded) = claim.commit();
      assert_eq!(encoded, bytes, "{}", fields[0]);
      assert_eq!(address.hex(), fields[1]);
      for len in 0..bytes.len() {
        assert!(Claim::from_bytes(&bytes[..len]).is_err());
      }
      let mut trailing = bytes.clone();
      trailing.push(0);
      assert!(Claim::from_bytes(&trailing).is_err());
      let header = if claim.proof_variant_size() + 3 >= 8 { 2 } else { 1 };
      let mut old_format = bytes.clone();
      old_format[header] = 3;
      let err = Claim::from_bytes(&old_format).unwrap_err();
      assert!(
        err.starts_with("claim: unsupported object format 3, expected 4"),
        "{err}"
      );
      let mut wrong_validator = bytes.clone();
      wrong_validator[header + 1] = 255;
      assert!(Claim::from_bytes(&wrong_validator).is_err());
      // A proof carries the same scope after its one-byte header (every
      // proof variant is below 8): object format 3 is rejected there too.
      let mut proof_bytes = Vec::new();
      Proof::new(claim.clone(), vec![1, 2, 3]).put(&mut proof_bytes);
      assert_eq!(proof_bytes[1], Env::OBJECT_FORMAT);
      proof_bytes[1] = 3;
      let err = Proof::get(&mut proof_bytes.as_slice()).unwrap_err();
      assert!(err.contains("unsupported object format 3"), "{err}");
      assert!(proof_roundtrip(&Proof::new(claim, vec![1, 2, 3])));
    }
  }

  /// Validator 4 (the binding assumed) is read only for `Check` and
  /// `CheckEnv`, as their context assuming the binding, and refused for
  /// every other variant.
  #[test]
  fn assumed_validator_only_for_check_and_check_env() {
    let ctx = test_ctx();
    let a = Address::hash(b"a");
    let claims = [
      Claim::Eval {
        ctx: ctx.clone(),
        input: a.clone(),
        output: a.clone(),
        assumptions: None,
      },
      Claim::Check {
        ctx: ctx.clone(),
        const_addr: a.clone(),
        assumptions: None,
      },
      Claim::CheckEnv { ctx: ctx.clone(), root: a.clone(), assumptions: None },
      Claim::Catalog { members: a.clone() },
      Claim::Binding { spec: ctx.spec.clone(), binding: ctx.binding.clone() },
    ];
    for claim in claims.clone() {
      let (_, mut bytes) = claim.commit();
      let header = if claim.proof_variant_size() + 3 >= 8 { 2 } else { 1 };
      bytes[header + 1] = VALIDATOR_ERASED_LEAN_ASSUMED;
      match (Claim::from_bytes(&bytes), &claim) {
        (Ok(Claim::Check { ctx: c, .. }), Claim::Check { .. })
        | (Ok(Claim::CheckEnv { ctx: c, .. }), Claim::CheckEnv { .. }) => {
          assert_eq!(c, ctx.clone().assuming_binding());
        },
        (Ok(read), _) => panic!("validator 4 read as {read:?}"),
        (Err(_), Claim::Check { .. } | Claim::CheckEnv { .. }) => {
          panic!("validator 4 refused for {claim:?}")
        },
        (Err(_), _) => {},
      }
    }
    // Validator 5 (a literal class) is read only for `CheckEnv`.
    for claim in claims {
      let (_, mut bytes) = claim.commit();
      let header = if claim.proof_variant_size() + 3 >= 8 { 2 } else { 1 };
      bytes[header + 1] = VALIDATOR_ERASED_LEAN_CLASS;
      match (Claim::from_bytes(&bytes), &claim) {
        (Ok(Claim::CheckEnv { ctx: c, .. }), Claim::CheckEnv { .. }) => {
          assert!(c.literal_class && !c.binding_assumed);
          assert_eq!(c.binding, ctx.binding);
        },
        (Ok(read), _) => panic!("validator 5 read as {read:?}"),
        (Err(_), Claim::CheckEnv { .. }) => {
          panic!("validator 5 refused for {claim:?}")
        },
        (Err(_), _) => {},
      }
    }
  }

  /// The literal class depends on exactly the class roles: rebinding
  /// another role keeps it, rebinding a class role moves it, and an
  /// incomplete table has none.
  #[test]
  fn literal_class_reads_only_the_class_roles() {
    use crate::role_table::{CLASS_ROLES, Role, RoleTable};
    let table = RoleTable {
      version: 2,
      bound: Role::ALL
        .iter()
        .map(|r| (*r, Address::hash(r.lean_name().as_bytes())))
        .collect(),
      evidence: vec![],
    };
    let class = table.literal_class().unwrap();
    let rebind = |role: Role| {
      let mut t = table.clone();
      for entry in &mut t.bound {
        if entry.0 == role {
          entry.1 = Address::hash(b"other");
        }
      }
      t.literal_class().unwrap()
    };
    assert_eq!(rebind(Role::NatLand), class);
    for role in CLASS_ROLES {
      assert_ne!(rebind(role), class, "{}", role.lean_name());
    }
    let mut incomplete = table.clone();
    incomplete.bound.pop();
    assert!(incomplete.literal_class().is_err());
    let indices: Vec<u8> = CLASS_ROLES.iter().map(|r| r.index()).collect();
    assert_eq!(indices, [0, 1, 2, 29, 30, 31, 37, 38, 39, 40, 56, 57]);
  }
}
