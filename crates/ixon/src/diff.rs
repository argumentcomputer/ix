//! Structured diff of two environments.
//!
//! [`diff_envs`] compares two [`Env`]s and produces an [`EnvDiff`] report.
//! Content-addressing frames the comparison: a name "changed" iff its
//! `Named.addr` differs, and constant value-equality coincides with
//! address-equality. Because addresses hash the *representation*
//! (sharing/refs/univs tables included), a changed address may carry no
//! semantic field difference — table reordering or different sharing
//! decisions — which the classifier reports honestly as `"encoding"`.
//!
//! Two modes:
//! - anon (`meta = false`, the default): only anonymous structure is
//!   compared — name→addr changes (with per-field classification of the
//!   two constants), consts/blobs set differences, comms, `main`,
//!   `assumptions`, and reducibility hints (which live in the anon §3
//!   section and drive kernel unfolding). Names serve as join/display
//!   keys only.
//! - meta (`meta = true`): additionally compares `Named.meta` /
//!   `Named.original` content, populating [`EnvDiff::named_meta_only`]
//!   and [`NamedChange::meta_fields`].
//!
//! Expression comparison ([`exprs_equal`]) is a lockstep structural walk
//! that resolves table indices through each side's own `Constant` tables:
//! identical expr bytes over different tables compare *different*, and
//! different indices resolving to the same addresses with the same
//! structure compare *equal*.
//!
//! Out of scope: `Env.names` (hash-consed name components — derived data;
//! the named join subsumes user-visible changes) and explanations for
//! orphan consts (mutual blocks and aux originals appear in the consts
//! set difference as raw truth). Synthetic Muts names (`Ix.<blockhex>`
//! prefixed) churn as one removed+added pair per changed block; display
//! layers may group them.

use rustc_hash::FxHashSet;

use ix_common::address::Address;
use ix_common::env::{Name, ReducibilityHints};

use super::constant::{
  Constant, ConstantInfo, Constructor, Definition, Inductive, MutConst,
  Recursor,
};
use super::env::{Env, Named};
use super::expr::Expr;
use super::univ::Univ;

/// Per-env entity counts, reported for both inputs so display layers can
/// print a header without re-walking the envs.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct EnvStats {
  pub consts: usize,
  pub named: usize,
  pub blobs: usize,
  pub comms: usize,
}

/// One name present in both envs whose constant address changed.
#[derive(Clone, Debug)]
pub struct NamedChange {
  /// `Name::pretty()` of the joined name.
  pub name: String,
  pub old_addr: Address,
  pub new_addr: Address,
  /// [`kind_label`] of each side's `ConstantInfo` variant.
  pub old_kind: &'static str,
  pub new_kind: &'static str,
  /// Changed-field labels, e.g. `"value"`, `"block.ctors[0].type"`.
  /// Never empty: `"kind"` when the variants differ, `"encoding"` when
  /// no semantic field difference explains the address change.
  pub fields: Vec<String>,
  /// Metadata component labels when the metadata ALSO changed. Only
  /// populated in meta mode; may be empty.
  pub meta_fields: Vec<String>,
}

/// Report produced by [`diff_envs`]. All name-keyed vectors are sorted
/// by (pretty name, name hash); address vectors are sorted ascending.
/// Set-difference lists are complete — display layers cap as needed.
#[derive(Clone, Debug, Default)]
pub struct EnvDiff {
  /// `None` = unchanged, otherwise `(a.main, b.main)`.
  pub main_changed: Option<(Option<Address>, Option<Address>)>,
  pub assumptions_added: Vec<Address>,
  pub assumptions_removed: Vec<Address>,
  /// Names only in the second env, with their constant address.
  pub named_added: Vec<(String, Address)>,
  /// Names only in the first env, with their constant address.
  pub named_removed: Vec<(String, Address)>,
  pub named_changed: Vec<NamedChange>,
  /// Same constant address, different metadata (meta mode only).
  pub named_meta_only: Vec<(String, Vec<String>)>,
  pub comms_added: Vec<Address>,
  pub comms_removed: Vec<Address>,
  /// Same commitment address, different `Comm` payload (possible
  /// because the comms section is not hash-verified on load).
  pub comms_changed: Vec<Address>,
  pub consts_only_a: Vec<Address>,
  pub consts_only_b: Vec<Address>,
  pub blobs_only_a: Vec<Address>,
  pub blobs_only_b: Vec<Address>,
  /// Hint deltas for constants present in BOTH envs (hint deltas of
  /// added/removed constants are implied by the other sections).
  /// Rendered as `"opaque" | "abbrev" | "regular(N)" | "none"`.
  pub hints_changed: Vec<(Address, String, String)>,
  pub stats_a: EnvStats,
  pub stats_b: EnvStats,
}

impl EnvDiff {
  /// True when no difference was found. Ignores `stats_*` (always
  /// populated).
  pub fn is_empty(&self) -> bool {
    self.main_changed.is_none()
      && self.assumptions_added.is_empty()
      && self.assumptions_removed.is_empty()
      && self.named_added.is_empty()
      && self.named_removed.is_empty()
      && self.named_changed.is_empty()
      && self.named_meta_only.is_empty()
      && self.comms_added.is_empty()
      && self.comms_removed.is_empty()
      && self.comms_changed.is_empty()
      && self.consts_only_a.is_empty()
      && self.consts_only_b.is_empty()
      && self.blobs_only_a.is_empty()
      && self.blobs_only_b.is_empty()
      && self.hints_changed.is_empty()
  }
}

/// Short label for a `ConstantInfo` variant.
pub fn kind_label(info: &ConstantInfo) -> &'static str {
  match info {
    ConstantInfo::Defn(_) => "defn",
    ConstantInfo::Recr(_) => "recr",
    ConstantInfo::Axio(_) => "axio",
    ConstantInfo::Quot(_) => "quot",
    ConstantInfo::CPrj(_) => "cprj",
    ConstantInfo::RPrj(_) => "rprj",
    ConstantInfo::IPrj(_) => "iprj",
    ConstantInfo::DPrj(_) => "dprj",
    ConstantInfo::Muts(_) => "muts",
  }
}

// ============================================================================
// Expression comparison
// ============================================================================

/// Follow a `Share` chain through `c.sharing` until a non-`Share` node.
/// Hop budget guards corrupt cycles (honest constants only reference
/// strictly earlier sharing entries, so chains are finite).
fn resolve_share<'c>(
  mut e: &'c Expr,
  c: &'c Constant,
  side: &str,
) -> Result<&'c Expr, String> {
  let mut hops: usize = 0;
  while let Expr::Share(i) = e {
    hops += 1;
    if hops > c.sharing.len() + 1 {
      return Err(format!("diff: Share cycle detected on the {side} side"));
    }
    let idx = usize::try_from(*i).map_err(|_e| {
      format!("diff: Share index {i} overflows usize on the {side} side")
    })?;
    e = c.sharing.get(idx).map(|a| a.as_ref()).ok_or_else(|| {
      format!(
        "diff: Share index {i} out of bounds ({} sharing entries) on the {side} side",
        c.sharing.len()
      )
    })?;
  }
  Ok(e)
}

fn univ_at<'c>(
  c: &'c Constant,
  idx: u64,
  side: &str,
) -> Result<&'c Univ, String> {
  usize::try_from(idx)
    .ok()
    .and_then(|i| c.univs.get(i))
    .map(|u| u.as_ref())
    .ok_or_else(|| {
      format!(
        "diff: univ index {idx} out of bounds ({} entries) on the {side} side",
        c.univs.len()
      )
    })
}

fn ref_at<'c>(
  c: &'c Constant,
  idx: u64,
  side: &str,
) -> Result<&'c Address, String> {
  usize::try_from(idx).ok().and_then(|i| c.refs.get(i)).ok_or_else(|| {
    format!(
      "diff: ref index {idx} out of bounds ({} entries) on the {side} side",
      c.refs.len()
    )
  })
}

/// Lockstep expression comparator over one pair of table contexts.
///
/// The pointer-pair memo persists across `eq` calls for the same
/// constant pair (tables are constant-level, so shared subterms recur
/// across type/value/rules). Entries record "heads matched, children
/// enqueued" — an unequal result returns early and leaves enqueued
/// children unverified, so [`Self::eq`] clears the memo on `false`.
struct ExprCmp<'a> {
  ca: &'a Constant,
  cb: &'a Constant,
  memo: FxHashSet<(usize, usize)>,
}

impl<'a> ExprCmp<'a> {
  fn new(ca: &'a Constant, cb: &'a Constant) -> Self {
    ExprCmp { ca, cb, memo: FxHashSet::default() }
  }

  fn eq(&mut self, a: &'a Expr, b: &'a Expr) -> Result<bool, String> {
    let r = self.eq_inner(a, b)?;
    if !r {
      self.memo.clear();
    }
    Ok(r)
  }

  fn eq_inner(&mut self, a: &'a Expr, b: &'a Expr) -> Result<bool, String> {
    // Iterative walk: kernel terms nest thousands deep, never recurse.
    let mut stack: Vec<(&'a Expr, &'a Expr)> = vec![(a, b)];
    while let Some((ea, eb)) = stack.pop() {
      let ea = resolve_share(ea, self.ca, "left")?;
      let eb = resolve_share(eb, self.cb, "right")?;
      let key =
        (std::ptr::from_ref(ea) as usize, std::ptr::from_ref(eb) as usize);
      if !self.memo.insert(key) {
        continue;
      }
      match (ea, eb) {
        (Expr::Var(x), Expr::Var(y)) => {
          if x != y {
            return Ok(false);
          }
        },
        (Expr::Sort(i), Expr::Sort(j)) => {
          if univ_at(self.ca, *i, "left")? != univ_at(self.cb, *j, "right")? {
            return Ok(false);
          }
        },
        (Expr::Ref(i, us), Expr::Ref(j, vs)) => {
          if ref_at(self.ca, *i, "left")? != ref_at(self.cb, *j, "right")?
            || !self.univ_lists_equal(us, vs)?
          {
            return Ok(false);
          }
        },
        (Expr::Rec(i, us), Expr::Rec(j, vs)) => {
          // Intra-block member index: positional, compare raw.
          if i != j || !self.univ_lists_equal(us, vs)? {
            return Ok(false);
          }
        },
        (Expr::Str(i), Expr::Str(j)) | (Expr::Nat(i), Expr::Nat(j)) => {
          // Blob content behind equal addresses is identical by
          // content-addressing (blob sections are hash-verified on load).
          if ref_at(self.ca, *i, "left")? != ref_at(self.cb, *j, "right")? {
            return Ok(false);
          }
        },
        (Expr::Prj(ti, fi, va), Expr::Prj(tj, fj, vb)) => {
          if fi != fj
            || ref_at(self.ca, *ti, "left")? != ref_at(self.cb, *tj, "right")?
          {
            return Ok(false);
          }
          stack.push((va, vb));
        },
        (Expr::App(f1, x1), Expr::App(f2, x2))
        | (Expr::Lam(f1, x1), Expr::Lam(f2, x2))
        | (Expr::All(f1, x1), Expr::All(f2, x2)) => {
          stack.push((f1, f2));
          stack.push((x1, x2));
        },
        (Expr::Let(n1, t1, v1, b1), Expr::Let(n2, t2, v2, b2)) => {
          if n1 != n2 {
            return Ok(false);
          }
          stack.push((t1, t2));
          stack.push((v1, v2));
          stack.push((b1, b2));
        },
        _ => return Ok(false),
      }
    }
    Ok(true)
  }

  fn univ_lists_equal(&self, us: &[u64], vs: &[u64]) -> Result<bool, String> {
    if us.len() != vs.len() {
      return Ok(false);
    }
    for (i, j) in us.iter().zip(vs.iter()) {
      // Univ trees are self-contained (Univ::Var is a universe-parameter
      // de Bruijn index, not a table index), so deep PartialEq is right.
      if univ_at(self.ca, *i, "left")? != univ_at(self.cb, *j, "right")? {
        return Ok(false);
      }
    }
    Ok(true)
  }
}

/// Structural equality of two expressions, resolving `Share`/`Sort`/
/// `Ref`/`Rec`-univ/`Str`/`Nat`/`Prj` indices through each side's own
/// `Constant` tables. Errors on out-of-bounds indices or `Share` cycles
/// (corrupt constants).
pub fn exprs_equal(
  a: &Expr,
  ca: &Constant,
  b: &Expr,
  cb: &Constant,
) -> Result<bool, String> {
  ExprCmp::new(ca, cb).eq(a, b)
}

// ============================================================================
// Per-kind field classification
// ============================================================================

fn classify_defn<'x>(
  a: &'x Definition,
  b: &'x Definition,
  cmp: &mut ExprCmp<'x>,
  prefix: &str,
  out: &mut Vec<String>,
) -> Result<(), String> {
  if a.kind != b.kind {
    out.push(format!("{prefix}def-kind"));
  }
  if a.safety != b.safety {
    out.push(format!("{prefix}safety"));
  }
  if a.lvls != b.lvls {
    out.push(format!("{prefix}lvls"));
  }
  if !cmp.eq(&a.typ, &b.typ)? {
    out.push(format!("{prefix}type"));
  }
  if !cmp.eq(&a.value, &b.value)? {
    out.push(format!("{prefix}value"));
  }
  Ok(())
}

fn classify_recr<'x>(
  a: &'x Recursor,
  b: &'x Recursor,
  cmp: &mut ExprCmp<'x>,
  prefix: &str,
  out: &mut Vec<String>,
) -> Result<(), String> {
  if a.k != b.k {
    out.push(format!("{prefix}k"));
  }
  if a.is_unsafe != b.is_unsafe {
    out.push(format!("{prefix}unsafe"));
  }
  if a.lvls != b.lvls {
    out.push(format!("{prefix}lvls"));
  }
  if a.params != b.params {
    out.push(format!("{prefix}params"));
  }
  if a.indices != b.indices {
    out.push(format!("{prefix}indices"));
  }
  if a.motives != b.motives {
    out.push(format!("{prefix}motives"));
  }
  if a.minors != b.minors {
    out.push(format!("{prefix}minors"));
  }
  if !cmp.eq(&a.typ, &b.typ)? {
    out.push(format!("{prefix}type"));
  }
  if a.rules.len() != b.rules.len() {
    out.push(format!("{prefix}rules.len"));
  }
  for (i, (ra, rb)) in a.rules.iter().zip(b.rules.iter()).enumerate() {
    if ra.fields != rb.fields {
      out.push(format!("{prefix}rules[{i}].fields"));
    }
    if !cmp.eq(&ra.rhs, &rb.rhs)? {
      out.push(format!("{prefix}rules[{i}].rhs"));
    }
  }
  Ok(())
}

fn classify_ctor<'x>(
  a: &'x Constructor,
  b: &'x Constructor,
  cmp: &mut ExprCmp<'x>,
  prefix: &str,
  out: &mut Vec<String>,
) -> Result<(), String> {
  if a.is_unsafe != b.is_unsafe {
    out.push(format!("{prefix}unsafe"));
  }
  if a.lvls != b.lvls {
    out.push(format!("{prefix}lvls"));
  }
  if a.cidx != b.cidx {
    out.push(format!("{prefix}cidx"));
  }
  if a.params != b.params {
    out.push(format!("{prefix}params"));
  }
  if a.fields != b.fields {
    out.push(format!("{prefix}fields"));
  }
  if !cmp.eq(&a.typ, &b.typ)? {
    out.push(format!("{prefix}type"));
  }
  Ok(())
}

fn classify_indc<'x>(
  a: &'x Inductive,
  b: &'x Inductive,
  cmp: &mut ExprCmp<'x>,
  prefix: &str,
  out: &mut Vec<String>,
) -> Result<(), String> {
  if a.is_unsafe != b.is_unsafe {
    out.push(format!("{prefix}unsafe"));
  }
  if a.lvls != b.lvls {
    out.push(format!("{prefix}lvls"));
  }
  if a.params != b.params {
    out.push(format!("{prefix}params"));
  }
  if a.indices != b.indices {
    out.push(format!("{prefix}indices"));
  }
  if !cmp.eq(&a.typ, &b.typ)? {
    out.push(format!("{prefix}type"));
  }
  if a.ctors.len() != b.ctors.len() {
    out.push(format!("{prefix}ctors.len"));
  }
  for (j, (ca, cb)) in a.ctors.iter().zip(b.ctors.iter()).enumerate() {
    classify_ctor(ca, cb, cmp, &format!("{prefix}ctors[{j}]."), out)?;
  }
  Ok(())
}

fn classify_mut_member<'x>(
  a: &'x MutConst,
  b: &'x MutConst,
  cmp: &mut ExprCmp<'x>,
  prefix: &str,
  out: &mut Vec<String>,
) -> Result<(), String> {
  match (a, b) {
    (MutConst::Defn(x), MutConst::Defn(y)) => {
      classify_defn(x, y, cmp, prefix, out)
    },
    (MutConst::Indc(x), MutConst::Indc(y)) => {
      classify_indc(x, y, cmp, prefix, out)
    },
    (MutConst::Recr(x), MutConst::Recr(y)) => {
      classify_recr(x, y, cmp, prefix, out)
    },
    _ => {
      out.push(format!("{prefix}kind"));
      Ok(())
    },
  }
}

fn classify_muts<'x>(
  ma: &'x [MutConst],
  mb: &'x [MutConst],
  cmp: &mut ExprCmp<'x>,
  prefix: &str,
  out: &mut Vec<String>,
) -> Result<(), String> {
  if ma.len() != mb.len() {
    out.push(format!("{prefix}members.len"));
  }
  for (i, (a, b)) in ma.iter().zip(mb.iter()).enumerate() {
    classify_mut_member(a, b, cmp, &format!("{prefix}members[{i}]."), out)?;
  }
  Ok(())
}

/// Same-kind projection pair whose `block` differs: descend one level
/// into the two Muts blocks and classify the projected member, with
/// labels prefixed `block.`. A member identical under resolved
/// comparison means the block hash moved because a *sibling* changed —
/// reported as `"block-siblings"`. Any structural surprise (block
/// missing — e.g. behind a bundle's assumption cut —, unparseable, not
/// Muts, index out of range) falls back to the honest `"block"` label.
/// No deeper recursion: blocks do not nest.
fn classify_prj(
  env_a: &Env,
  env_b: &Env,
  idx_a: u64,
  idx_b: u64,
  cidx: Option<(u64, u64)>,
  block_a: &Address,
  block_b: &Address,
  out: &mut Vec<String>,
) -> Result<(), String> {
  if idx_a != idx_b {
    out.push("idx".to_string());
  }
  if let Some((ca, cb)) = cidx
    && ca != cb
  {
    out.push("cidx".to_string());
  }
  if block_a == block_b {
    return Ok(());
  }
  // With differing member coordinates the two projections target
  // different members; per-member block detail would be meaningless.
  if idx_a != idx_b || cidx.is_some_and(|(x, y)| x != y) {
    out.push("block".to_string());
    return Ok(());
  }
  let (Some(Ok(ba)), Some(Ok(bb))) =
    (env_a.try_get_const(block_a), env_b.try_get_const(block_b))
  else {
    out.push("block".to_string());
    return Ok(());
  };
  let (ConstantInfo::Muts(ma), ConstantInfo::Muts(mb)) = (&ba.info, &bb.info)
  else {
    out.push("block".to_string());
    return Ok(());
  };
  let Some(idx) = usize::try_from(idx_a).ok() else {
    out.push("block".to_string());
    return Ok(());
  };
  let (Some(mem_a), Some(mem_b)) = (ma.get(idx), mb.get(idx)) else {
    out.push("block".to_string());
    return Ok(());
  };
  // Expression tables are constant-level: members resolve through the
  // enclosing block constants' tables.
  let mut cmp = ExprCmp::new(&ba, &bb);
  let before = out.len();
  match cidx {
    None => classify_mut_member(mem_a, mem_b, &mut cmp, "block.", out)?,
    Some((cx, _)) => {
      let (MutConst::Indc(ia), MutConst::Indc(ib)) = (mem_a, mem_b) else {
        out.push("block".to_string());
        return Ok(());
      };
      let Some(ci) = usize::try_from(cx).ok() else {
        out.push("block".to_string());
        return Ok(());
      };
      let (Some(ctor_a), Some(ctor_b)) = (ia.ctors.get(ci), ib.ctors.get(ci))
      else {
        out.push("block".to_string());
        return Ok(());
      };
      classify_ctor(ctor_a, ctor_b, &mut cmp, "block.ctor.", out)?;
    },
  }
  if out.len() == before {
    out.push("block-siblings".to_string());
  }
  Ok(())
}

/// Compare two same-name constants field by field; returns changed-field
/// labels. Never returns an empty list: kind mismatches yield `"kind"`,
/// and an address change with no detected semantic difference yields
/// `"encoding"` (table reorder / sharing-decision churn).
fn classify_constants(
  env_a: &Env,
  ca: &Constant,
  env_b: &Env,
  cb: &Constant,
) -> Result<Vec<String>, String> {
  let mut out = Vec::new();
  let mut cmp = ExprCmp::new(ca, cb);
  match (&ca.info, &cb.info) {
    (ConstantInfo::Defn(a), ConstantInfo::Defn(b)) => {
      classify_defn(a, b, &mut cmp, "", &mut out)?;
    },
    (ConstantInfo::Recr(a), ConstantInfo::Recr(b)) => {
      classify_recr(a, b, &mut cmp, "", &mut out)?;
    },
    (ConstantInfo::Axio(a), ConstantInfo::Axio(b)) => {
      if a.is_unsafe != b.is_unsafe {
        out.push("unsafe".to_string());
      }
      if a.lvls != b.lvls {
        out.push("lvls".to_string());
      }
      if !cmp.eq(&a.typ, &b.typ)? {
        out.push("type".to_string());
      }
    },
    (ConstantInfo::Quot(a), ConstantInfo::Quot(b)) => {
      if a.kind != b.kind {
        out.push("quot-kind".to_string());
      }
      if a.lvls != b.lvls {
        out.push("lvls".to_string());
      }
      if !cmp.eq(&a.typ, &b.typ)? {
        out.push("type".to_string());
      }
    },
    (ConstantInfo::DPrj(a), ConstantInfo::DPrj(b)) => {
      classify_prj(
        env_a, env_b, a.idx, b.idx, None, &a.block, &b.block, &mut out,
      )?;
    },
    (ConstantInfo::IPrj(a), ConstantInfo::IPrj(b)) => {
      classify_prj(
        env_a, env_b, a.idx, b.idx, None, &a.block, &b.block, &mut out,
      )?;
    },
    (ConstantInfo::RPrj(a), ConstantInfo::RPrj(b)) => {
      classify_prj(
        env_a, env_b, a.idx, b.idx, None, &a.block, &b.block, &mut out,
      )?;
    },
    (ConstantInfo::CPrj(a), ConstantInfo::CPrj(b)) => {
      classify_prj(
        env_a,
        env_b,
        a.idx,
        b.idx,
        Some((a.cidx, b.cidx)),
        &a.block,
        &b.block,
        &mut out,
      )?;
    },
    (ConstantInfo::Muts(ma), ConstantInfo::Muts(mb)) => {
      classify_muts(ma, mb, &mut cmp, "", &mut out)?;
    },
    _ => out.push("kind".to_string()),
  }
  if out.is_empty() {
    out.push("encoding".to_string());
  }
  Ok(out)
}

// ============================================================================
// Metadata comparison (meta mode)
// ============================================================================

/// Component labels for a same-addr metadata difference.
fn meta_component_labels(a: &Named, b: &Named) -> Vec<String> {
  let mut out = Vec::new();
  let (am, bm) = (a.meta(), b.meta());
  if am.info != bm.info {
    let (ka, kb) = (am.info.kind_name(), bm.info.kind_name());
    if ka == kb {
      out.push("meta.info".to_string());
    } else {
      out.push(format!("meta.info({ka}→{kb})"));
    }
  }
  if am.meta_sharing != bm.meta_sharing {
    out.push("meta.sharing".to_string());
  }
  if am.meta_refs != bm.meta_refs {
    out.push("meta.refs".to_string());
  }
  if am.meta_univs != bm.meta_univs {
    out.push("meta.univs".to_string());
  }
  match (a.original(), b.original()) {
    (None, None) => {},
    (None, Some(_)) => out.push("original.added".to_string()),
    (Some(_), None) => out.push("original.removed".to_string()),
    (Some((aa, ma)), Some((ab, mb))) => {
      if aa != ab {
        out.push("original.addr".to_string());
      }
      if ma != mb {
        out.push("original.meta".to_string());
      }
    },
  }
  out
}

// ============================================================================
// Env diff
// ============================================================================

fn hint_label(h: Option<&ReducibilityHints>) -> String {
  match h {
    None => "none".to_string(),
    Some(ReducibilityHints::Opaque) => "opaque".to_string(),
    Some(ReducibilityHints::Abbrev) => "abbrev".to_string(),
    Some(ReducibilityHints::Regular(n)) => format!("regular({n})"),
  }
}

fn env_stats(e: &Env) -> EnvStats {
  EnvStats {
    consts: e.consts.len(),
    named: e.named.len(),
    blobs: e.blobs.len(),
    comms: e.comms.len(),
  }
}

fn classify_named_change(
  env_a: &Env,
  env_b: &Env,
  name: &Name,
  na: &Named,
  nb: &Named,
  meta: bool,
) -> Result<NamedChange, String> {
  let materialize = |env: &Env, addr: &Address, which: &str| {
    env
      .try_get_const(addr)
      .ok_or_else(|| {
        format!(
          "diff: named '{}' addr {} not present in consts of the {which} env",
          name.pretty(),
          addr.hex()
        )
      })?
      .map_err(|e| {
        format!("diff: named '{}' ({}): {e}", name.pretty(), addr.hex())
      })
  };
  let ca = materialize(env_a, &na.addr, "first")?;
  let cb = materialize(env_b, &nb.addr, "second")?;
  let fields = classify_constants(env_a, &ca, env_b, &cb)?;
  let meta_fields =
    if meta { meta_component_labels(na, nb) } else { Vec::new() };
  Ok(NamedChange {
    name: name.pretty(),
    old_addr: na.addr.clone(),
    new_addr: nb.addr.clone(),
    old_kind: kind_label(&ca.info),
    new_kind: kind_label(&cb.info),
    fields,
    meta_fields,
  })
}

/// Sort by (pretty name, name hash) — the hash tiebreak keeps distinct
/// names with equal pretty forms deterministic.
fn sort_by_name<T>(v: &mut [(String, Name, T)]) {
  v.sort_by(|x, y| x.0.cmp(&y.0).then_with(|| x.1.cmp(&y.1)));
}

/// Diff two environments. `meta = false` (anon mode, the default)
/// compares only anonymous structure; `meta = true` additionally
/// compares `Named` metadata content. See the module docs.
pub fn diff_envs(a: &Env, b: &Env, meta: bool) -> Result<EnvDiff, String> {
  let mut d = EnvDiff {
    stats_a: env_stats(a),
    stats_b: env_stats(b),
    ..EnvDiff::default()
  };

  // Named join on Name. Alpha-equivalent multi-names (several names
  // sharing one constant address) need no special care: each name is
  // its own row.
  let mut added: Vec<(String, Name, Address)> = Vec::new();
  let mut removed: Vec<(String, Name, Address)> = Vec::new();
  let mut changed: Vec<(String, Name, NamedChange)> = Vec::new();
  let mut meta_only: Vec<(String, Name, Vec<String>)> = Vec::new();
  for entry in a.named.iter() {
    let (name, na) = (entry.key(), entry.value());
    match b.named.get(name) {
      None => removed.push((name.pretty(), name.clone(), na.addr.clone())),
      Some(nb_ref) => {
        let nb = nb_ref.value();
        if na.addr == nb.addr {
          if meta {
            let labels = meta_component_labels(na, nb);
            if !labels.is_empty() {
              meta_only.push((name.pretty(), name.clone(), labels));
            }
          }
        } else {
          let change = classify_named_change(a, b, name, na, nb, meta)?;
          changed.push((name.pretty(), name.clone(), change));
        }
      },
    }
  }
  for entry in b.named.iter() {
    let name = entry.key();
    if a.named.get(name).is_none() {
      added.push((name.pretty(), name.clone(), entry.value().addr.clone()));
    }
  }
  sort_by_name(&mut added);
  sort_by_name(&mut removed);
  sort_by_name(&mut changed);
  sort_by_name(&mut meta_only);
  d.named_added = added.into_iter().map(|(s, _, addr)| (s, addr)).collect();
  d.named_removed = removed.into_iter().map(|(s, _, addr)| (s, addr)).collect();
  d.named_changed = changed.into_iter().map(|(_, _, c)| c).collect();
  d.named_meta_only = meta_only.into_iter().map(|(s, _, l)| (s, l)).collect();

  // Consts / blobs set differences.
  for entry in a.consts.iter() {
    if !b.consts.contains_key(entry.key()) {
      d.consts_only_a.push(entry.key().clone());
    }
  }
  for entry in b.consts.iter() {
    if !a.consts.contains_key(entry.key()) {
      d.consts_only_b.push(entry.key().clone());
    }
  }
  for entry in a.blobs.iter() {
    if !b.blobs.contains_key(entry.key()) {
      d.blobs_only_a.push(entry.key().clone());
    }
  }
  for entry in b.blobs.iter() {
    if !a.blobs.contains_key(entry.key()) {
      d.blobs_only_b.push(entry.key().clone());
    }
  }

  // Comms join.
  for entry in a.comms.iter() {
    match b.comms.get(entry.key()) {
      None => d.comms_removed.push(entry.key().clone()),
      Some(other) => {
        if other.value() != entry.value() {
          d.comms_changed.push(entry.key().clone());
        }
      },
    }
  }
  for entry in b.comms.iter() {
    if a.comms.get(entry.key()).is_none() {
      d.comms_added.push(entry.key().clone());
    }
  }

  // Header: main + assumptions.
  if a.main != b.main {
    d.main_changed = Some((a.main.clone(), b.main.clone()));
  }
  for addr in &a.assumptions {
    if !b.assumptions.contains(addr) {
      d.assumptions_removed.push(addr.clone());
    }
  }
  for addr in &b.assumptions {
    if !a.assumptions.contains(addr) {
      d.assumptions_added.push(addr.clone());
    }
  }

  // Hints, joined on constants present in both envs.
  let shared =
    |addr: &Address| a.consts.contains_key(addr) && b.consts.contains_key(addr);
  for (addr, ha) in &a.anon_hints {
    if !shared(addr) {
      continue;
    }
    let hb = b.anon_hints.get(addr);
    if hb != Some(ha) {
      d.hints_changed.push((
        addr.clone(),
        hint_label(Some(ha)),
        hint_label(hb),
      ));
    }
  }
  for (addr, hb) in &b.anon_hints {
    if shared(addr) && !a.anon_hints.contains_key(addr) {
      d.hints_changed.push((
        addr.clone(),
        hint_label(None),
        hint_label(Some(hb)),
      ));
    }
  }

  d.consts_only_a.sort_unstable();
  d.consts_only_b.sort_unstable();
  d.blobs_only_a.sort_unstable();
  d.blobs_only_b.sort_unstable();
  d.comms_added.sort_unstable();
  d.comms_removed.sort_unstable();
  d.comms_changed.sort_unstable();
  d.assumptions_added.sort_unstable();
  d.assumptions_removed.sort_unstable();
  d.hints_changed.sort_unstable_by(|x, y| x.0.cmp(&y.0));

  Ok(d)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::comm::Comm;
  use crate::constant::{DefKind, defn_proj_constant};
  use crate::metadata::{ConstantMeta, ConstantMetaInfo, ExprMeta};
  use ix_common::env::DefinitionSafety;
  use std::sync::Arc;

  fn n(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  /// Store `c` at its true content address; returns the address.
  fn store_canonical(env: &Env, c: &Constant) -> Address {
    let (addr, _) = c.commit();
    env.store_const(addr.clone(), c.clone());
    addr
  }

  fn mk_defn(lvls: u64, typ: Arc<Expr>, value: Arc<Expr>) -> Definition {
    Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls,
      typ,
      value,
    }
  }

  fn defn_c(typ: Arc<Expr>, value: Arc<Expr>) -> Constant {
    Constant::new(ConstantInfo::Defn(mk_defn(0, typ, value)))
  }

  fn defn_ct(
    typ: Arc<Expr>,
    value: Arc<Expr>,
    sharing: Vec<Arc<Expr>>,
    refs: Vec<Address>,
    univs: Vec<Arc<Univ>>,
  ) -> Constant {
    Constant::with_tables(
      ConstantInfo::Defn(mk_defn(0, typ, value)),
      sharing,
      refs,
      univs,
    )
  }

  /// Single-constant env: store `c` canonically and name it `name`.
  fn env1(name: &str, c: &Constant) -> (Env, Address) {
    let env = Env::new();
    let addr = store_canonical(&env, c);
    env.register_name(n(name), Named::with_addr(addr.clone()));
    (env, addr)
  }

  fn labels(v: &[String]) -> Vec<&str> {
    v.iter().map(String::as_str).collect()
  }

  fn diff(a: &Env, b: &Env) -> EnvDiff {
    diff_envs(a, b, false).expect("diff_envs failed")
  }

  fn diff_meta(a: &Env, b: &Env) -> EnvDiff {
    diff_envs(a, b, true).expect("diff_envs failed")
  }

  #[test]
  fn identical_envs_empty_diff() {
    let mut env = Env::new();
    let c = defn_c(Expr::var(3), Expr::var(0));
    let addr = store_canonical(&env, &c);
    env.register_name(n("Foo"), Named::with_addr(addr.clone()));
    let blob = env.store_blob(vec![1, 2, 3]);
    env.store_comm(
      Address::hash(b"comm"),
      Comm::new(Address::hash(b"s"), Address::hash(b"p")),
    );
    env.main = Some(addr.clone());
    env.assumptions.insert(blob);
    env.anon_hints.insert(addr, ReducibilityHints::Regular(2));
    let copy = env.clone();
    let d = diff(&env, &copy);
    assert!(d.is_empty(), "anon self-diff should be empty: {d:?}");
    assert_eq!(d.stats_a, d.stats_b);
    assert_eq!(d.stats_a.consts, 1);
    assert!(diff_meta(&env, &copy).is_empty(), "meta self-diff not empty");
  }

  #[test]
  fn added_and_removed_name() {
    let (a, _) = env1("Base", &defn_c(Expr::var(3), Expr::var(0)));
    let b = a.clone();
    let extra = defn_c(Expr::var(4), Expr::var(1));
    let extra_addr = store_canonical(&b, &extra);
    b.register_name(n("Extra"), Named::with_addr(extra_addr.clone()));

    let d = diff(&a, &b);
    assert_eq!(d.named_added, vec![("Extra".to_string(), extra_addr.clone())]);
    assert!(d.named_removed.is_empty() && d.named_changed.is_empty());
    assert_eq!(d.consts_only_b, vec![extra_addr.clone()]);
    assert!(d.consts_only_a.is_empty());

    let d = diff(&b, &a);
    assert_eq!(
      d.named_removed,
      vec![("Extra".to_string(), extra_addr.clone())]
    );
    assert_eq!(d.consts_only_a, vec![extra_addr]);
  }

  #[test]
  fn defn_value_only_changed() {
    let (a, _) = env1("Foo", &defn_c(Expr::var(3), Expr::var(0)));
    let (b, _) = env1("Foo", &defn_c(Expr::var(3), Expr::var(1)));
    let d = diff(&a, &b);
    assert_eq!(d.named_changed.len(), 1);
    let c = &d.named_changed[0];
    assert_eq!(c.name, "Foo");
    assert_eq!((c.old_kind, c.new_kind), ("defn", "defn"));
    assert_eq!(labels(&c.fields), ["value"]);
    assert!(c.meta_fields.is_empty());
  }

  #[test]
  fn defn_type_only_changed() {
    let (a, _) = env1("Foo", &defn_c(Expr::var(3), Expr::var(0)));
    let (b, _) = env1("Foo", &defn_c(Expr::var(4), Expr::var(0)));
    let d = diff(&a, &b);
    assert_eq!(labels(&d.named_changed[0].fields), ["type"]);
  }

  #[test]
  fn defn_scalars_changed() {
    let ca = Constant::new(ConstantInfo::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: Expr::var(3),
      value: Expr::var(0),
    }));
    let cb = Constant::new(ConstantInfo::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Partial,
      lvls: 1,
      typ: Expr::var(3),
      value: Expr::var(0),
    }));
    let (a, _) = env1("Foo", &ca);
    let (b, _) = env1("Foo", &cb);
    let d = diff(&a, &b);
    assert_eq!(labels(&d.named_changed[0].fields), ["safety", "lvls"]);
  }

  /// Identical expr bytes over different refs tables are DIFFERENT.
  #[test]
  fn refs_shift_same_bytes_is_different() {
    let x = Address::hash(b"X");
    let y = Address::hash(b"Y");
    let mk = |r: Address| {
      defn_ct(Expr::var(9), Expr::reference(0, vec![]), vec![], vec![r], vec![])
    };
    let (a, _) = env1("Foo", &mk(x));
    let (b, _) = env1("Foo", &mk(y));
    let d = diff(&a, &b);
    assert_eq!(labels(&d.named_changed[0].fields), ["value"]);
  }

  /// Different indices resolving to the same addresses with the same
  /// structure are EQUAL — a real type change is the only field.
  #[test]
  fn refs_permuted_same_resolution_is_equal() {
    let x = Address::hash(b"X");
    let y = Address::hash(b"Y");
    let ca = defn_ct(
      Expr::var(1),
      Expr::app(Expr::reference(0, vec![]), Expr::reference(1, vec![])),
      vec![],
      vec![x.clone(), y.clone()],
      vec![],
    );
    let cb = defn_ct(
      Expr::var(2),
      Expr::app(Expr::reference(1, vec![]), Expr::reference(0, vec![])),
      vec![],
      vec![y.clone(), x.clone()],
      vec![],
    );
    let (a, _) = env1("Foo", &ca);
    let (b, _) = env1("Foo", &cb);
    let d = diff(&a, &b);
    assert_eq!(labels(&d.named_changed[0].fields), ["type"]);

    // Pure permutation: no semantic field difference at all.
    let ca = defn_ct(
      Expr::var(1),
      Expr::app(Expr::reference(0, vec![]), Expr::reference(1, vec![])),
      vec![],
      vec![x.clone(), y.clone()],
      vec![],
    );
    let cb = defn_ct(
      Expr::var(1),
      Expr::app(Expr::reference(1, vec![]), Expr::reference(0, vec![])),
      vec![],
      vec![y, x],
      vec![],
    );
    let (a, addr_a) = env1("Foo", &ca);
    let (b, addr_b) = env1("Foo", &cb);
    assert_ne!(addr_a, addr_b, "permuted tables must change the address");
    let d = diff(&a, &b);
    assert_eq!(labels(&d.named_changed[0].fields), ["encoding"]);
  }

  /// Sharing-table indirection vs inlined subterms: resolved-equal.
  #[test]
  fn share_vs_inline_equal() {
    let t = Expr::all(Expr::var(7), Expr::var(0));
    let ca = defn_ct(
      Expr::var(1),
      Expr::app(Arc::new(Expr::Share(0)), Arc::new(Expr::Share(0))),
      vec![t.clone()],
      vec![],
      vec![],
    );
    let cb =
      defn_ct(Expr::var(1), Expr::app(t.clone(), t), vec![], vec![], vec![]);
    let (a, addr_a) = env1("Foo", &ca);
    let (b, addr_b) = env1("Foo", &cb);
    assert_ne!(addr_a, addr_b);
    let d = diff(&a, &b);
    assert_eq!(labels(&d.named_changed[0].fields), ["encoding"]);
  }

  /// Univ-table shifts with identical resolution are not a type change;
  /// changed univ content behind the same index is.
  #[test]
  fn univ_table_shift_equal_content_change_not() {
    let ca =
      defn_ct(Expr::sort(0), Expr::var(0), vec![], vec![], vec![Univ::zero()]);
    let cb = defn_ct(
      Expr::sort(1),
      Expr::var(0),
      vec![],
      vec![],
      vec![Univ::succ(Univ::zero()), Univ::zero()],
    );
    let (a, _) = env1("Foo", &ca);
    let (b, _) = env1("Foo", &cb);
    let d = diff(&a, &b);
    assert_eq!(labels(&d.named_changed[0].fields), ["encoding"]);

    let ca =
      defn_ct(Expr::sort(0), Expr::var(0), vec![], vec![], vec![Univ::zero()]);
    let cb = defn_ct(
      Expr::sort(0),
      Expr::var(0),
      vec![],
      vec![],
      vec![Univ::succ(Univ::zero())],
    );
    let (a, _) = env1("Foo", &ca);
    let (b, _) = env1("Foo", &cb);
    let d = diff(&a, &b);
    assert_eq!(labels(&d.named_changed[0].fields), ["type"]);
  }

  /// A field-compare failure must not leave stale memo entries that
  /// mask a later field's difference (type and value share Arcs here).
  #[test]
  fn memo_cleared_after_unequal_field() {
    let e_a = Expr::app(Expr::var(1), Expr::var(5));
    let e_b = Expr::app(Expr::var(1), Expr::var(6));
    let ca = defn_c(e_a.clone(), e_a);
    let cb = defn_c(e_b.clone(), e_b);
    let (a, _) = env1("Foo", &ca);
    let (b, _) = env1("Foo", &cb);
    let d = diff(&a, &b);
    assert_eq!(labels(&d.named_changed[0].fields), ["type", "value"]);
  }

  #[test]
  fn metadata_only_change() {
    let c = defn_c(Expr::var(3), Expr::var(0));
    let (a, addr) = env1("Foo", &c);
    let b = Env::new();
    store_canonical(&b, &c);
    let meta = ConstantMeta {
      meta_refs: vec![Address::hash(b"extra-ref")],
      ..ConstantMeta::default()
    };
    b.register_name(n("Foo"), Named::new(addr.clone(), meta));

    let d = diff(&a, &b);
    assert!(d.is_empty(), "anon mode must ignore metadata: {d:?}");
    let d = diff_meta(&a, &b);
    assert_eq!(d.named_meta_only.len(), 1);
    assert_eq!(d.named_meta_only[0].0, "Foo");
    assert_eq!(labels(&d.named_meta_only[0].1), ["meta.refs"]);
    assert!(d.named_changed.is_empty());

    // original added + info kind change carry their own labels.
    let b2 = Env::new();
    store_canonical(&b2, &c);
    let info = ConstantMetaInfo::Def {
      name: Address::hash(b"nm"),
      lvls: vec![],
      hints: ReducibilityHints::Regular(1),
      all: vec![],
      ctx: vec![],
      arena: ExprMeta::default(),
      type_root: 0,
      value_root: 0,
    };
    let mut named2 = Named::new(addr.clone(), ConstantMeta::new(info));
    named2.set_original(addr.clone(), ConstantMeta::default());
    b2.register_name(n("Foo"), named2);
    let d = diff_meta(&a, &b2);
    assert_eq!(
      labels(&d.named_meta_only[0].1),
      ["meta.info(empty→def)", "original.added"]
    );
  }

  #[test]
  fn kind_change() {
    let ca = Constant::new(ConstantInfo::Axio(crate::constant::Axiom {
      is_unsafe: false,
      lvls: 0,
      typ: Expr::var(3),
    }));
    let cb = defn_c(Expr::var(3), Expr::var(0));
    let (a, _) = env1("Foo", &ca);
    let (b, _) = env1("Foo", &cb);
    let d = diff(&a, &b);
    let c = &d.named_changed[0];
    assert_eq!((c.old_kind, c.new_kind), ("axio", "defn"));
    assert_eq!(labels(&c.fields), ["kind"]);
  }

  #[test]
  fn main_assumptions_comms_hints() {
    let shared = defn_c(Expr::var(3), Expr::var(0));
    let p = Address::hash(b"p");
    let q = Address::hash(b"q");
    let r = Address::hash(b"r");
    let c1 = Address::hash(b"comm1");
    let c2 = Address::hash(b"comm2");

    let mut a = Env::new();
    let addr = store_canonical(&a, &shared);
    a.main = Some(addr.clone());
    a.assumptions.insert(p.clone());
    a.assumptions.insert(q.clone());
    a.store_comm(
      c1.clone(),
      Comm::new(Address::hash(b"s"), Address::hash(b"pay1")),
    );
    a.anon_hints.insert(addr.clone(), ReducibilityHints::Regular(1));

    let mut b = Env::new();
    store_canonical(&b, &shared);
    b.main = Some(p.clone());
    b.assumptions.insert(q);
    b.assumptions.insert(r.clone());
    b.store_comm(
      c1.clone(),
      Comm::new(Address::hash(b"s"), Address::hash(b"pay2")),
    );
    b.store_comm(
      c2.clone(),
      Comm::new(Address::hash(b"s"), Address::hash(b"pay3")),
    );
    b.anon_hints.insert(addr.clone(), ReducibilityHints::Regular(2));

    let d = diff(&a, &b);
    assert_eq!(d.main_changed, Some((Some(addr.clone()), Some(p.clone()))));
    assert_eq!(d.assumptions_added, vec![r]);
    assert_eq!(d.assumptions_removed, vec![p]);
    assert_eq!(d.comms_changed, vec![c1]);
    assert_eq!(d.comms_added, vec![c2]);
    assert!(d.comms_removed.is_empty());
    assert_eq!(
      d.hints_changed,
      vec![(addr, "regular(1)".to_string(), "regular(2)".to_string())]
    );
  }

  /// One-level block descent: the changed member gets `block.*` detail,
  /// the untouched sibling gets `block-siblings`.
  #[test]
  fn projection_block_descent() {
    let f = MutConst::Defn(mk_defn(0, Expr::var(3), Expr::var(0)));
    let g_old = MutConst::Defn(mk_defn(0, Expr::var(3), Expr::var(1)));
    let g_new = MutConst::Defn(mk_defn(0, Expr::var(3), Expr::var(2)));
    let block_a = Constant::new(ConstantInfo::Muts(vec![f.clone(), g_old]));
    let block_b = Constant::new(ConstantInfo::Muts(vec![f, g_new]));

    let a = Env::new();
    let block_a_addr = store_canonical(&a, &block_a);
    let fa = store_canonical(&a, &defn_proj_constant(0, block_a_addr.clone()));
    let ga = store_canonical(&a, &defn_proj_constant(1, block_a_addr));
    a.register_name(n("M.f"), Named::with_addr(fa));
    a.register_name(n("M.g"), Named::with_addr(ga));

    let b = Env::new();
    let block_b_addr = store_canonical(&b, &block_b);
    let fb = store_canonical(&b, &defn_proj_constant(0, block_b_addr.clone()));
    let gb = store_canonical(&b, &defn_proj_constant(1, block_b_addr));
    b.register_name(n("M.f"), Named::with_addr(fb));
    b.register_name(n("M.g"), Named::with_addr(gb));

    let d = diff(&a, &b);
    assert_eq!(d.named_changed.len(), 2);
    let mf = &d.named_changed[0];
    let mg = &d.named_changed[1];
    assert_eq!((mf.name.as_str(), mg.name.as_str()), ("M.f", "M.g"));
    assert_eq!((mf.old_kind, mf.new_kind), ("dprj", "dprj"));
    assert_eq!(labels(&mf.fields), ["block-siblings"]);
    assert_eq!(labels(&mg.fields), ["block.value"]);
  }

  #[test]
  fn recursor_rules_changed() {
    let mk = |rhs: Arc<Expr>, rules_extra: bool| {
      let mut rules = vec![crate::constant::RecursorRule { fields: 2, rhs }];
      if rules_extra {
        rules
          .push(crate::constant::RecursorRule { fields: 0, rhs: Expr::var(0) });
      }
      Constant::new(ConstantInfo::Recr(Recursor {
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 1,
        indices: 0,
        motives: 1,
        minors: 1,
        typ: Expr::var(9),
        rules,
      }))
    };
    let (a, _) = env1("R", &mk(Expr::var(4), false));
    let (b, _) = env1("R", &mk(Expr::var(5), false));
    let d = diff(&a, &b);
    assert_eq!(labels(&d.named_changed[0].fields), ["rules[0].rhs"]);

    let (a, _) = env1("R", &mk(Expr::var(4), false));
    let (b, _) = env1("R", &mk(Expr::var(4), true));
    let d = diff(&a, &b);
    assert_eq!(labels(&d.named_changed[0].fields), ["rules.len"]);
  }
}
