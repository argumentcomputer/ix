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
//! Every changed row additionally carries a ripple verdict
//! ([`NamedChange::rippled`]): after the join, changed pairs are
//! re-classified under a quotient where an (old, new) address pair
//! compares equal when some changed name maps old→new. Rows whose
//! residual labels are all `"encoding"`/`"block-siblings"` are
//! *rippled* — fully explained by dependency re-addressing (the
//! content-address ripple: one edited constant re-addresses its whole
//! reverse-dependency cone); the rest are *roots* (intrinsic edits). A
//! single-level mapping is complete because expression comparison only
//! ever consults immediate-dependency addresses — composition across
//! the DAG happens through the per-row verdicts, never through the map.
//! Accepted semantic edges:
//! - Induced re-elaboration verdicts root: a dependency's
//!   universe/arity signature change alters dependents' terms beyond
//!   addresses (e.g. `Ref` univ-argument arity), so "roots"
//!   over-approximates "human edits" when signatures change.
//! - An intrinsic edit of a block member with no named projection has
//!   no root row of its own (blocks are unnamed; in practice ix names
//!   every projection, so the member's projection row is the root).
//! - The `"block"` fallback (block bytes missing, e.g. behind a
//!   bundle's assumption cut) verdicts root — fail-safe over-report.
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

use std::cmp::Ordering;
use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::address::Address;
use ix_common::env::{Name, ReducibilityHints};

use super::constant::{
  Constant, ConstantInfo, Constructor, Definition, Inductive, MutConst,
  Recursor,
};
use super::env::{Env, LazyIndex, Named};
use super::expr::Expr;
use super::serialize::NamedMetaCursor;
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
  /// True iff the address change is fully explained by dependency
  /// re-addressing: re-classified under the old→new quotient of all
  /// changed rows, the residual labels are all `"encoding"` /
  /// `"block-siblings"`. `fields` stays the strict (unquotiented)
  /// classification; this is the orthogonal root-vs-ripple verdict.
  pub rippled: bool,
}

/// Report produced by [`diff_envs`]. All name-keyed vectors are sorted
/// by (pretty name, name hash); address vectors are sorted ascending.
/// Set-difference lists are complete — display layers cap as needed.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
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

/// Old→new address pairs harvested from every changed named row in
/// pass 1 (kind-change and encoding rows included). Set-valued to
/// tolerate name splits: two names sharing an old address, diverging in
/// the new env. Directional — keys are A-side (old) addresses.
type AddrMap = FxHashMap<Address, Vec<Address>>;

/// Lockstep expression comparator over one pair of table contexts.
///
/// The pointer-pair memo persists across `eq` calls for the same
/// constant pair (tables are constant-level, so shared subterms recur
/// across type/value/rules). Entries record "heads matched, children
/// enqueued" — an unequal result returns early and leaves enqueued
/// children unverified, so [`Self::eq`] clears the memo on `false`.
///
/// `map` selects the address equality: `None` = strict (pass 1),
/// `Some` = the ripple quotient (pass 2).
struct ExprCmp<'a> {
  ca: &'a Constant,
  cb: &'a Constant,
  memo: FxHashSet<(usize, usize)>,
  map: Option<&'a AddrMap>,
}

impl<'a> ExprCmp<'a> {
  fn new(ca: &'a Constant, cb: &'a Constant, map: Option<&'a AddrMap>) -> Self {
    ExprCmp { ca, cb, memo: FxHashSet::default(), map }
  }

  /// Address equality under the selected mode. `l` MUST be the A-side
  /// (old) address and `r` the B-side (new) — the quotient map is
  /// directional. Every comparison site preserves that order (the walk
  /// always pairs (A-expr, B-expr)).
  fn addrs_eq(&self, l: &Address, r: &Address) -> bool {
    l == r || self.map.is_some_and(|m| m.get(l).is_some_and(|v| v.contains(r)))
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
          if !self.addrs_eq(
            ref_at(self.ca, *i, "left")?,
            ref_at(self.cb, *j, "right")?,
          ) || !self.univ_lists_equal(us, vs)?
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
          // Blob addresses never enter the quotient map (it holds
          // constant addresses from named rows), so literal changes stay
          // intrinsic under pass 2 — `addrs_eq` degenerates to `==`.
          if !self.addrs_eq(
            ref_at(self.ca, *i, "left")?,
            ref_at(self.cb, *j, "right")?,
          ) {
            return Ok(false);
          }
        },
        (Expr::Prj(ti, fi, va), Expr::Prj(tj, fj, vb)) => {
          if fi != fj
            || !self.addrs_eq(
              ref_at(self.ca, *ti, "left")?,
              ref_at(self.cb, *tj, "right")?,
            )
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
  ExprCmp::new(ca, cb, None).eq(a, b)
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
  map: Option<&AddrMap>,
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
  // Strict `==` deliberately, even under the quotient: blocks are
  // unnamed (their synthetic names embed the hash, so they never join
  // as changed rows and never enter the map), and descent is mandatory
  // — a block-internal intrinsic edit has no named row of its own, so
  // short-circuiting a "mapped" block pair would hide the root.
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
  let mut cmp = ExprCmp::new(&ba, &bb, map);
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
///
/// `map = None` is the strict pass-1 classification; `Some` re-runs it
/// under the ripple quotient (pass 2), where the labels are consumed
/// only by the [`rippled_labels`] verdict and then discarded.
fn classify_constants(
  env_a: &Env,
  ca: &Constant,
  env_b: &Env,
  cb: &Constant,
  map: Option<&AddrMap>,
) -> Result<Vec<String>, String> {
  let mut out = Vec::new();
  let mut cmp = ExprCmp::new(ca, cb, map);
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
        env_a, env_b, a.idx, b.idx, None, &a.block, &b.block, map, &mut out,
      )?;
    },
    (ConstantInfo::IPrj(a), ConstantInfo::IPrj(b)) => {
      classify_prj(
        env_a, env_b, a.idx, b.idx, None, &a.block, &b.block, map, &mut out,
      )?;
    },
    (ConstantInfo::RPrj(a), ConstantInfo::RPrj(b)) => {
      classify_prj(
        env_a, env_b, a.idx, b.idx, None, &a.block, &b.block, map, &mut out,
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
        map,
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

/// Materialize the constant behind a named row's address, with
/// name-and-side error context. Shared by the pass-1 classification and
/// the pass-2 ripple verdict (constants are re-parsed on every call —
/// `LazyConstant` deliberately keeps no parse cache, which is what
/// bounds resident memory at mathlib scale).
fn materialize_const(
  env: &Env,
  addr: &Address,
  name: &Name,
  which: &str,
) -> Result<Arc<Constant>, String> {
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
}

fn classify_named_change(
  env_a: &Env,
  env_b: &Env,
  name: &Name,
  na: &Named,
  nb: &Named,
  meta_fields: Vec<String>,
) -> Result<NamedChange, String> {
  let ca = materialize_const(env_a, &na.addr, name, "first")?;
  let cb = materialize_const(env_b, &nb.addr, name, "second")?;
  let fields = classify_constants(env_a, &ca, env_b, &cb, None)?;
  Ok(NamedChange {
    name: name.pretty(),
    old_addr: na.addr.clone(),
    new_addr: nb.addr.clone(),
    old_kind: kind_label(&ca.info),
    new_kind: kind_label(&cb.info),
    fields,
    meta_fields,
    // Verdict assigned by pass 2 (a row is a root until explained).
    rippled: false,
  })
}

/// Pass-2 verdict over quotient labels: rippled iff every residual
/// label is explained by re-addressing — `"encoding"` (quotient-equal
/// everywhere; the fallback when no field label fired) or
/// `"block-siblings"` (the projected member is quotient-equal; the
/// block hash moved for reasons surfaced by other rows). Scalar labels,
/// `"kind"`, coordinate labels (`"idx"`/`"cidx"`), `"block"`, and all
/// `block.*` detail labels mean intrinsic change → root. Labels are
/// never empty (the `"encoding"` fallback), so `all` cannot pass
/// vacuously.
fn rippled_labels(labels: &[String]) -> bool {
  labels.iter().all(|l| l == "encoding" || l == "block-siblings")
}

/// Sort by (pretty name, name hash) — the hash tiebreak keeps distinct
/// names with equal pretty forms deterministic.
fn sort_by_name<T>(v: &mut [(String, Name, T)]) {
  v.sort_by(|x, y| x.0.cmp(&y.0).then_with(|| x.1.cmp(&y.1)));
}

/// Which diff pass a [`JoinProgress`] event reports.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DiffPhase {
  /// Meta mode only, before the join: the streaming §5 metadata sweep
  /// (lockstep merge-join of both files' named sections).
  MetaSweep,
  /// Pass 1: the named join (change detection + strict classification).
  NamedJoin,
  /// Pass 2: re-classification of changed rows under the ripple
  /// quotient (root vs rippled verdicts).
  RippleClassify,
}

/// Coarse progress for the passes whose cost scales with entry counts.
/// Parses happen before [`diff_envs`] and are the caller's to report.
#[derive(Clone, Copy, Debug)]
pub struct JoinProgress {
  /// The pass this event reports. `done` counts reset between phases.
  pub phase: DiffPhase,
  /// [`DiffPhase::MetaSweep`]: §5 entries merged (max of both sides).
  /// [`DiffPhase::NamedJoin`]: first-env named entries processed.
  /// [`DiffPhase::RippleClassify`]: changed rows verdicted.
  pub done: usize,
  /// Total entries of the reporting phase.
  pub total: usize,
  /// [`DiffPhase::MetaSweep`]: names with differing metadata so far.
  /// [`DiffPhase::NamedJoin`]: changed names classified so far.
  /// [`DiffPhase::RippleClassify`]: roots found so far.
  pub changed: usize,
}

/// Named-join / meta-sweep entries between progress callbacks.
const JOIN_PROGRESS_STRIDE: usize = 100_000;

/// Changed rows between pass-2 progress callbacks — one event every
/// ~1-2 s at mathlib scale (each row re-materializes and re-walks a
/// constant pair, so rows are ~10× slower than join probes).
const RIPPLE_PROGRESS_STRIDE: usize = 10_000;

/// Where metadata comparisons come from.
///
/// The full-reader path holds complete `Named` values in the envs
/// (`InEnv`); the memory-lean bytes/mmap path never materializes them
/// in bulk, so the streaming §5 sweep precomputes labels per name
/// (`Sweep`); anon mode compares no metadata at all (`None`).
enum MetaSource<'m> {
  None,
  InEnv,
  Sweep(&'m FxHashMap<Name, Vec<String>>),
}

impl MetaSource<'_> {
  fn labels(&self, name: &Name, na: &Named, nb: &Named) -> Vec<String> {
    match self {
      MetaSource::None => Vec::new(),
      MetaSource::InEnv => meta_component_labels(na, nb),
      MetaSource::Sweep(m) => m.get(name).cloned().unwrap_or_default(),
    }
  }
}

/// Diff two environments. `meta = false` (anon mode, the default)
/// compares only anonymous structure; `meta = true` additionally
/// compares `Named` metadata content held in the envs (full-reader
/// path — for the memory-lean bytes path see [`diff_env_bytes`]). See
/// the module docs.
pub fn diff_envs(a: &Env, b: &Env, meta: bool) -> Result<EnvDiff, String> {
  diff_envs_with(a, b, meta, &mut |_| {})
}

/// [`diff_envs`] with a progress callback: `on_progress` fires every
/// `JOIN_PROGRESS_STRIDE` named-join entries and once when each phase
/// completes (final events always carry `done == total`).
pub fn diff_envs_with(
  a: &Env,
  b: &Env,
  meta: bool,
  on_progress: &mut dyn FnMut(JoinProgress),
) -> Result<EnvDiff, String> {
  let source = if meta { MetaSource::InEnv } else { MetaSource::None };
  diff_envs_impl(a, b, &source, on_progress)
}

/// One side of a lazy-path diff: the env built from `index` over `data`
/// (via [`Env::from_lazy_index`] or [`Env::from_lazy_index_mmap`]).
#[derive(Clone, Copy)]
pub struct LazySide<'a> {
  pub env: &'a Env,
  pub index: &'a LazyIndex,
  pub data: &'a [u8],
}

/// Memory-lean bytes-level diff (the `ix diff` path): lazy-index
/// structural load plus, in meta mode, the streaming §5 metadata sweep
/// — `ConstantMeta` is never bulk-materialized on either side.
pub fn diff_env_bytes(
  a: &[u8],
  b: &[u8],
  meta: bool,
  on_progress: &mut dyn FnMut(JoinProgress),
) -> Result<EnvDiff, String> {
  let ia = Env::parse_lazy_index(a)?;
  let ib = Env::parse_lazy_index(b)?;
  let ea = Env::from_lazy_index(&ia, a)?;
  let eb = Env::from_lazy_index(&ib, b)?;
  diff_envs_lazy(
    LazySide { env: &ea, index: &ia, data: a },
    LazySide { env: &eb, index: &ib, data: b },
    meta,
    on_progress,
  )
}

/// Core of the bytes/mmap paths: both sides already lazily loaded. In
/// meta mode, runs the streaming §5 sweep first (metadata labels per
/// name, parse-compare-drop), then the structural join consuming them.
pub fn diff_envs_lazy(
  a: LazySide<'_>,
  b: LazySide<'_>,
  meta: bool,
  on_progress: &mut dyn FnMut(JoinProgress),
) -> Result<EnvDiff, String> {
  if meta {
    let map = sweep_meta(&a, &b, on_progress)?;
    diff_envs_impl(a.env, b.env, &MetaSource::Sweep(&map), on_progress)
  } else {
    diff_envs_impl(a.env, b.env, &MetaSource::None, on_progress)
  }
}

/// Streaming §5 metadata sweep: lockstep merge-join of both files'
/// named sections (canonical ascending name-hash order — exactly
/// `Name`'s `Ord`), parsing each side's entry against its own §4
/// reverse index, comparing, and dropping. Returns component labels
/// for every joined name whose metadata differs — the addr-equal ones
/// become `named_meta_only` rows, the addr-changed ones `meta_fields`.
fn sweep_meta(
  a: &LazySide<'_>,
  b: &LazySide<'_>,
  on_progress: &mut dyn FnMut(JoinProgress),
) -> Result<FxHashMap<Name, Vec<String>>, String> {
  let mut cur_a = NamedMetaCursor::open(a.data, a.index)?;
  let mut cur_b = NamedMetaCursor::open(b.data, b.index)?;
  let an = &a.index.named;
  let bn = &b.index.named;
  let total = an.len().max(bn.len());
  let mut out: FxHashMap<Name, Vec<String>> = FxHashMap::default();
  let (mut i, mut j) = (0usize, 0usize);
  let mut fired = 0usize;
  while i < an.len() && j < bn.len() {
    match an[i].name.cmp(&bn[j].name) {
      Ordering::Less => {
        cur_a.next_entry()?;
        i += 1;
      },
      Ordering::Greater => {
        cur_b.next_entry()?;
        j += 1;
      },
      Ordering::Equal => {
        let (_, na) = cur_a
          .next_entry()?
          .ok_or("sweep_meta: first cursor exhausted early")?;
        let (_, nb) = cur_b
          .next_entry()?
          .ok_or("sweep_meta: second cursor exhausted early")?;
        // Cursor and index walked the same section — desync means a bug.
        if na.addr != an[i].addr || nb.addr != bn[j].addr {
          return Err("sweep_meta: cursor desynced from index".to_string());
        }
        let labels = meta_component_labels(&na, &nb);
        if !labels.is_empty() {
          out.insert(an[i].name.clone(), labels);
        }
        i += 1;
        j += 1;
      },
    }
    let done = i.max(j);
    if done / JOIN_PROGRESS_STRIDE > fired && done < total {
      fired = done / JOIN_PROGRESS_STRIDE;
      on_progress(JoinProgress {
        phase: DiffPhase::MetaSweep,
        done,
        total,
        changed: out.len(),
      });
    }
  }
  // Unjoined tails carry no comparison work — cursors just drop.
  on_progress(JoinProgress {
    phase: DiffPhase::MetaSweep,
    done: total,
    total,
    changed: out.len(),
  });
  Ok(out)
}

fn diff_envs_impl(
  a: &Env,
  b: &Env,
  source: &MetaSource<'_>,
  on_progress: &mut dyn FnMut(JoinProgress),
) -> Result<EnvDiff, String> {
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
  // Old→new mapping over every changed row, consumed by pass 2.
  let mut addr_map: AddrMap = FxHashMap::default();
  let join_total = a.named.len();
  let mut join_done: usize = 0;
  for entry in a.named.iter() {
    let (name, na) = (entry.key(), entry.value());
    match b.named.get(name) {
      None => removed.push((name.pretty(), name.clone(), na.addr.clone())),
      Some(nb_ref) => {
        let nb = nb_ref.value();
        if na.addr == nb.addr {
          let labels = source.labels(name, na, nb);
          if !labels.is_empty() {
            meta_only.push((name.pretty(), name.clone(), labels));
          }
        } else {
          let meta_fields = source.labels(name, na, nb);
          let change = classify_named_change(a, b, name, na, nb, meta_fields)?;
          let slot = addr_map.entry(na.addr.clone()).or_default();
          if !slot.contains(&nb.addr) {
            slot.push(nb.addr.clone());
          }
          changed.push((name.pretty(), name.clone(), change));
        }
      },
    }
    join_done += 1;
    if join_done.is_multiple_of(JOIN_PROGRESS_STRIDE) && join_done < join_total
    {
      on_progress(JoinProgress {
        phase: DiffPhase::NamedJoin,
        done: join_done,
        total: join_total,
        changed: changed.len(),
      });
    }
  }
  on_progress(JoinProgress {
    phase: DiffPhase::NamedJoin,
    done: join_total,
    total: join_total,
    changed: changed.len(),
  });

  // Pass 2 (ripple): re-classify each changed pair under the quotient
  // of the just-completed old→new mapping. A pair whose residual labels
  // are all explained by re-addressing is rippled (induced by its
  // dependencies' address changes); the rest are roots. Alias rows —
  // several names spanning one (old, new) pair — share one cached
  // verdict and one computation. Materialization failure here is a hard
  // error: pass 1 already materialized both sides of every changed row.
  if !changed.is_empty() {
    let mut verdicts: FxHashMap<(Address, Address), bool> =
      FxHashMap::default();
    let ripple_total = changed.len();
    let mut roots: usize = 0;
    for (i, (_, name, ch)) in changed.iter_mut().enumerate() {
      let key = (ch.old_addr.clone(), ch.new_addr.clone());
      let rippled = match verdicts.get(&key) {
        Some(v) => *v,
        None => {
          let ca = materialize_const(a, &ch.old_addr, name, "first")?;
          let cb = materialize_const(b, &ch.new_addr, name, "second")?;
          let labels = classify_constants(a, &ca, b, &cb, Some(&addr_map))?;
          let v = rippled_labels(&labels);
          verdicts.insert(key, v);
          v
        },
      };
      ch.rippled = rippled;
      if !rippled {
        roots += 1;
      }
      let done = i + 1;
      if done.is_multiple_of(RIPPLE_PROGRESS_STRIDE) && done < ripple_total {
        on_progress(JoinProgress {
          phase: DiffPhase::RippleClassify,
          done,
          total: ripple_total,
          changed: roots,
        });
      }
    }
    on_progress(JoinProgress {
      phase: DiffPhase::RippleClassify,
      done: ripple_total,
      total: ripple_total,
      changed: roots,
    });
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
  for entry in a.anon_hints.iter() {
    let (addr, ha) = (entry.key(), entry.value());
    if !shared(addr) {
      continue;
    }
    let hb = b.anon_hints.get(addr).map(|r| *r);
    if hb != Some(*ha) {
      d.hints_changed.push((
        addr.clone(),
        hint_label(Some(ha)),
        hint_label(hb.as_ref()),
      ));
    }
  }
  for entry in b.anon_hints.iter() {
    let (addr, hb) = (entry.key(), entry.value());
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
  use crate::constant::{
    DefKind, ctor_proj_constant, defn_proj_constant, indc_proj_constant,
  };
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

  /// Anon-mode diffs must be identical whether the envs came from the
  /// full reader or the lazy-index path (`ix diff`'s memory-lean route).
  #[test]
  fn lazy_index_env_matches_full_reader_in_anon_mode() {
    let build = |value: Arc<Expr>, hint: u32, with_extra: bool| {
      let mut env = Env::new();
      let register = |env: &Env, label: &str, addr: Address| {
        let name = n(label);
        env
          .names
          .insert(Address::from_blake3_hash(*name.get_hash()), name.clone());
        env.register_name(name, Named::with_addr(addr));
      };
      let c = defn_c(Expr::var(3), value);
      let addr = store_canonical(&env, &c);
      register(&env, "Foo", addr.clone());
      // Hint lives on a constant PRESENT IN BOTH envs — the hints diff
      // joins on shared consts only.
      let stable = defn_c(Expr::var(7), Expr::var(0));
      let stable_addr = store_canonical(&env, &stable);
      register(&env, "Stable", stable_addr.clone());
      env.anon_hints.insert(stable_addr, ReducibilityHints::Regular(hint));
      env.store_blob(vec![1, 2, 3]);
      env.store_comm(
        Address::hash(b"comm"),
        Comm::new(Address::hash(b"s"), Address::hash(b"p")),
      );
      env.main = Some(addr);
      env.assumptions.insert(Address::hash(b"assumed"));
      if with_extra {
        let extra = defn_c(Expr::var(5), Expr::var(2));
        let extra_addr = store_canonical(&env, &extra);
        register(&env, "Extra", extra_addr);
      }
      let mut bytes = Vec::new();
      env.put(&mut bytes).expect("put failed");
      bytes
    };
    let bytes_a = build(Expr::var(0), 1, false);
    let bytes_b = build(Expr::var(1), 2, true);

    let full = |bytes: &[u8]| {
      let mut cursor = bytes;
      Env::get(&mut cursor).expect("full read failed")
    };
    let lazy = |bytes: &[u8]| {
      let index = Env::parse_lazy_index(bytes).expect("lazy index failed");
      Env::from_lazy_index(&index, bytes).expect("from_lazy_index failed")
    };

    let via_full = diff(&full(&bytes_a), &full(&bytes_b));
    let via_lazy = diff(&lazy(&bytes_a), &lazy(&bytes_b));
    assert_eq!(via_full, via_lazy);
    // Sanity: the pair genuinely exercises every section.
    assert_eq!(via_full.named_changed.len(), 1);
    assert_eq!(via_full.named_added.len(), 1);
    assert_eq!(via_full.hints_changed.len(), 1);
    // Lazy self-diff is empty.
    assert!(diff(&lazy(&bytes_a), &lazy(&bytes_a)).is_empty());
  }

  #[test]
  fn join_progress_final_event_totals() {
    let (a, _) = env1("Base", &defn_c(Expr::var(3), Expr::var(0)));
    let b = a.clone();
    let extra = defn_c(Expr::var(4), Expr::var(1));
    let extra_addr = store_canonical(&b, &extra);
    b.register_name(n("Extra"), Named::with_addr(extra_addr));
    // Change Base's constant so exactly one join entry classifies.
    let changed = defn_c(Expr::var(3), Expr::var(9));
    let changed_addr = store_canonical(&b, &changed);
    b.register_name(n("Base"), Named::with_addr(changed_addr));

    let mut events: Vec<JoinProgress> = Vec::new();
    let d = diff_envs_with(&a, &b, false, &mut |p| events.push(p))
      .expect("diff_envs_with failed");
    // `done` resets between phases — assert each phase separately.
    let join: Vec<_> =
      events.iter().filter(|p| p.phase == DiffPhase::NamedJoin).collect();
    let ripple: Vec<_> =
      events.iter().filter(|p| p.phase == DiffPhase::RippleClassify).collect();
    let last_join = join.last().expect("no join events");
    assert_eq!(last_join.done, last_join.total);
    assert_eq!(last_join.total, a.named.len());
    assert_eq!(last_join.changed, d.named_changed.len());
    assert_eq!(d.named_changed.len(), 1);
    let last_ripple = ripple.last().expect("no ripple events");
    assert_eq!(last_ripple.done, last_ripple.total);
    assert_eq!(last_ripple.total, d.named_changed.len());
    assert_eq!(
      last_ripple.changed,
      d.named_changed.iter().filter(|c| !c.rippled).count()
    );
    for phase_events in [&join, &ripple] {
      assert!(
        phase_events.windows(2).all(|w| w[0].done <= w[1].done),
        "per-phase progress must be monotone"
      );
    }
    // All ripple events come after the join completes.
    let first_ripple = events
      .iter()
      .position(|p| p.phase == DiffPhase::RippleClassify)
      .expect("no ripple events");
    let last_join_pos = events
      .iter()
      .rposition(|p| p.phase == DiffPhase::NamedJoin)
      .expect("no join events");
    assert!(last_join_pos < first_ripple, "phases must not interleave");
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

  // ==========================================================================
  // Ripple root-causing (pass 2)
  // ==========================================================================

  /// A defn whose value is a bare `Ref` into `refs[0] = r`.
  fn defn_ref(typ_var: u64, r: Address) -> Constant {
    defn_ct(
      Expr::var(typ_var),
      Expr::reference(0, vec![]),
      vec![],
      vec![r],
      vec![],
    )
  }

  fn changed_by_name<'d>(d: &'d EnvDiff, name: &str) -> &'d NamedChange {
    d.named_changed
      .iter()
      .find(|c| c.name == name)
      .unwrap_or_else(|| panic!("no changed row named {name}: {d:?}"))
  }

  /// Editing a leaf re-addresses the chain above it; only the leaf is a
  /// root. Proves the single-level map composes across the DAG through
  /// per-row verdicts.
  #[test]
  fn ripple_two_hop_chain() {
    let build = |leaf_value: Arc<Expr>| {
      let env = Env::new();
      let leaf = defn_c(Expr::var(3), leaf_value);
      let leaf_addr = store_canonical(&env, &leaf);
      let mid = defn_ref(4, leaf_addr.clone());
      let mid_addr = store_canonical(&env, &mid);
      let top = defn_ref(5, mid_addr.clone());
      let top_addr = store_canonical(&env, &top);
      env.register_name(n("Leaf"), Named::with_addr(leaf_addr));
      env.register_name(n("Mid"), Named::with_addr(mid_addr));
      env.register_name(n("Top"), Named::with_addr(top_addr));
      env
    };
    let a = build(Expr::var(0));
    let b = build(Expr::var(1));
    let d = diff(&a, &b);
    assert_eq!(d.named_changed.len(), 3);
    let leaf = changed_by_name(&d, "Leaf");
    assert!(!leaf.rippled, "the edited leaf is the root");
    assert_eq!(labels(&leaf.fields), ["value"]);
    for name in ["Mid", "Top"] {
      let c = changed_by_name(&d, name);
      assert!(c.rippled, "{name} must be rippled: {c:?}");
      // Strict fields are untouched by the verdict.
      assert_eq!(labels(&c.fields), ["value"]);
    }
  }

  /// Blob addresses never enter the quotient map: a literal edit is the
  /// intrinsic change site.
  #[test]
  fn ripple_literal_change_is_root() {
    let build = |blob: Vec<u8>| {
      let env = Env::new();
      let blob_addr = env.store_blob(blob);
      let c =
        defn_ct(Expr::var(3), Expr::nat(0), vec![], vec![blob_addr], vec![]);
      let addr = store_canonical(&env, &c);
      env.register_name(n("Lit"), Named::with_addr(addr));
      env
    };
    let a = build(vec![42]);
    let b = build(vec![43]);
    let d = diff(&a, &b);
    let c = changed_by_name(&d, "Lit");
    assert!(!c.rippled);
    assert_eq!(labels(&c.fields), ["value"]);
  }

  /// Block-internal ctor edit: the edited ctor's projection is the root
  /// (block descent runs under the quotient too); the untouched sibling
  /// ctor and any external dependent are rippled.
  #[test]
  fn ripple_block_ctor_edit_projections() {
    let build = |c1_typ: Arc<Expr>| {
      let env = Env::new();
      let indc = Inductive {
        is_unsafe: false,
        lvls: 0,
        params: 0,
        indices: 0,
        typ: Expr::var(3),
        ctors: vec![
          Constructor {
            is_unsafe: false,
            lvls: 0,
            cidx: 0,
            params: 0,
            fields: 0,
            typ: Expr::var(1),
          },
          Constructor {
            is_unsafe: false,
            lvls: 0,
            cidx: 1,
            params: 0,
            fields: 0,
            typ: c1_typ,
          },
        ],
      };
      let block = Constant::new(ConstantInfo::Muts(vec![MutConst::Indc(indc)]));
      let block_addr = store_canonical(&env, &block);
      let iprj =
        store_canonical(&env, &indc_proj_constant(0, block_addr.clone()));
      let c0 =
        store_canonical(&env, &ctor_proj_constant(0, 0, block_addr.clone()));
      let c1 = store_canonical(&env, &ctor_proj_constant(0, 1, block_addr));
      env.register_name(n("I"), Named::with_addr(iprj.clone()));
      env.register_name(n("I.c0"), Named::with_addr(c0));
      env.register_name(n("I.c1"), Named::with_addr(c1));
      // External dependent referencing the inductive's projection.
      let dep = defn_ref(9, iprj);
      let dep_addr = store_canonical(&env, &dep);
      env.register_name(n("UsesI"), Named::with_addr(dep_addr));
      env
    };
    let a = build(Expr::var(2));
    let b = build(Expr::var(9));
    let d = diff(&a, &b);
    assert_eq!(d.named_changed.len(), 4);

    let edited = changed_by_name(&d, "I.c1");
    assert!(!edited.rippled, "edited ctor's projection is the root");
    assert_eq!(labels(&edited.fields), ["block.ctor.type"]);

    let indc_row = changed_by_name(&d, "I");
    assert!(!indc_row.rippled, "the inductive sees its ctor's edit");
    assert_eq!(labels(&indc_row.fields), ["block.ctors[1].type"]);

    let sibling = changed_by_name(&d, "I.c0");
    assert!(sibling.rippled, "untouched sibling ctor is rippled");
    assert_eq!(labels(&sibling.fields), ["block-siblings"]);

    let dep = changed_by_name(&d, "UsesI");
    assert!(dep.rippled, "external dependent of the block is rippled");
    assert_eq!(labels(&dep.fields), ["value"]);
  }

  /// The existing block-descent fixture, now with verdicts: the member
  /// whose value changed is the root; its sibling projection rides.
  #[test]
  fn ripple_defn_block_sibling() {
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
    assert!(changed_by_name(&d, "M.f").rippled);
    assert!(!changed_by_name(&d, "M.g").rippled);
  }

  /// Scalar changes are quotient-invariant → always roots.
  #[test]
  fn ripple_lvls_change_is_root() {
    let (a, _) = env1(
      "Foo",
      &Constant::new(ConstantInfo::Defn(mk_defn(
        0,
        Expr::var(3),
        Expr::var(0),
      ))),
    );
    let (b, _) = env1(
      "Foo",
      &Constant::new(ConstantInfo::Defn(mk_defn(
        1,
        Expr::var(3),
        Expr::var(0),
      ))),
    );
    let d = diff(&a, &b);
    let c = changed_by_name(&d, "Foo");
    assert!(!c.rippled);
    assert_eq!(labels(&c.fields), ["lvls"]);
  }

  /// Pure representation churn (strict `["encoding"]`) has no intrinsic
  /// difference under the quotient either → rippled.
  #[test]
  fn ripple_pure_encoding_is_rippled() {
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
      Expr::var(1),
      Expr::app(Expr::reference(1, vec![]), Expr::reference(0, vec![])),
      vec![],
      vec![y, x],
      vec![],
    );
    let (a, _) = env1("Foo", &ca);
    let (b, _) = env1("Foo", &cb);
    let d = diff(&a, &b);
    let c = changed_by_name(&d, "Foo");
    assert_eq!(labels(&c.fields), ["encoding"]);
    assert!(c.rippled);
  }

  /// Kind-change rows enter the map too: their dependents are rippled.
  #[test]
  fn ripple_kind_change_root_and_maps() {
    let build = |axio: bool| {
      let env = Env::new();
      let dc: Constant = if axio {
        Constant::new(ConstantInfo::Axio(crate::constant::Axiom {
          is_unsafe: false,
          lvls: 0,
          typ: Expr::var(3),
        }))
      } else {
        defn_c(Expr::var(3), Expr::var(0))
      };
      let d_addr = store_canonical(&env, &dc);
      let dep = defn_ref(9, d_addr.clone());
      let dep_addr = store_canonical(&env, &dep);
      env.register_name(n("D"), Named::with_addr(d_addr));
      env.register_name(n("UsesD"), Named::with_addr(dep_addr));
      env
    };
    let a = build(true);
    let b = build(false);
    let d = diff(&a, &b);
    let kd = changed_by_name(&d, "D");
    assert!(!kd.rippled);
    assert_eq!(labels(&kd.fields), ["kind"]);
    let dep = changed_by_name(&d, "UsesD");
    assert!(dep.rippled, "kind rows must still enter the quotient map");
  }

  /// Two names sharing one old address, diverging in the new env: the
  /// set-valued map explains both dependents.
  #[test]
  fn ripple_name_split_conflict() {
    let a = Env::new();
    let x = defn_c(Expr::var(3), Expr::var(0));
    let x_addr = store_canonical(&a, &x);
    a.register_name(n("P"), Named::with_addr(x_addr.clone()));
    a.register_name(n("Q"), Named::with_addr(x_addr.clone()));
    let dp = defn_ref(7, x_addr.clone());
    let dp_addr = store_canonical(&a, &dp);
    a.register_name(n("DP"), Named::with_addr(dp_addr));
    let dq = defn_ref(8, x_addr);
    let dq_addr = store_canonical(&a, &dq);
    a.register_name(n("DQ"), Named::with_addr(dq_addr));

    let b = Env::new();
    let y1 = defn_c(Expr::var(3), Expr::var(1));
    let y1_addr = store_canonical(&b, &y1);
    let y2 = defn_c(Expr::var(3), Expr::var(2));
    let y2_addr = store_canonical(&b, &y2);
    b.register_name(n("P"), Named::with_addr(y1_addr.clone()));
    b.register_name(n("Q"), Named::with_addr(y2_addr.clone()));
    let dp2 = defn_ref(7, y1_addr);
    let dp2_addr = store_canonical(&b, &dp2);
    b.register_name(n("DP"), Named::with_addr(dp2_addr));
    let dq2 = defn_ref(8, y2_addr);
    let dq2_addr = store_canonical(&b, &dq2);
    b.register_name(n("DQ"), Named::with_addr(dq2_addr));

    let d = diff(&a, &b);
    assert!(!changed_by_name(&d, "P").rippled);
    assert!(!changed_by_name(&d, "Q").rippled);
    assert!(changed_by_name(&d, "DP").rippled);
    assert!(changed_by_name(&d, "DQ").rippled);
  }

  /// Ref univ arguments: same args over a mapped target → rippled;
  /// changed arg arity (induced re-elaboration) → root.
  #[test]
  fn ripple_ref_univ_args() {
    let build = |leaf_value: Arc<Expr>, dep_univs: bool| {
      let env = Env::new();
      let leaf =
        Constant::new(ConstantInfo::Defn(mk_defn(1, Expr::var(3), leaf_value)));
      let leaf_addr = store_canonical(&env, &leaf);
      let dep = if dep_univs {
        defn_ct(
          Expr::var(9),
          Expr::reference(0, vec![0, 1]),
          vec![],
          vec![leaf_addr.clone()],
          vec![Univ::zero(), Univ::succ(Univ::zero())],
        )
      } else {
        defn_ct(
          Expr::var(9),
          Expr::reference(0, vec![0]),
          vec![],
          vec![leaf_addr.clone()],
          vec![Univ::zero()],
        )
      };
      let dep_addr = store_canonical(&env, &dep);
      env.register_name(n("Leaf"), Named::with_addr(leaf_addr));
      env.register_name(n("Dep"), Named::with_addr(dep_addr));
      env
    };
    // Same univ args over a mapped target: rippled.
    let a = build(Expr::var(0), false);
    let b = build(Expr::var(1), false);
    let d = diff(&a, &b);
    assert!(!changed_by_name(&d, "Leaf").rippled);
    assert!(changed_by_name(&d, "Dep").rippled);

    // Univ-argument arity changed at the use site: intrinsic (induced
    // re-elaboration) → root, even though the target maps.
    let a = build(Expr::var(0), false);
    let b = build(Expr::var(1), true);
    let d = diff(&a, &b);
    assert!(!changed_by_name(&d, "Leaf").rippled);
    let dep = changed_by_name(&d, "Dep");
    assert!(!dep.rippled);
    assert_eq!(labels(&dep.fields), ["value"]);
  }

  /// A dependency renamed (removed+added) never enters the map: its
  /// dependents verdict root — fail-safe over-report.
  #[test]
  fn ripple_renamed_dep_is_root() {
    let a = Env::new();
    let old = defn_c(Expr::var(3), Expr::var(0));
    let old_addr = store_canonical(&a, &old);
    a.register_name(n("OldDep"), Named::with_addr(old_addr.clone()));
    let dep = defn_ref(9, old_addr);
    let dep_addr = store_canonical(&a, &dep);
    a.register_name(n("User"), Named::with_addr(dep_addr));

    let b = Env::new();
    let new = defn_c(Expr::var(3), Expr::var(1));
    let new_addr = store_canonical(&b, &new);
    b.register_name(n("NewDep"), Named::with_addr(new_addr.clone()));
    let dep2 = defn_ref(9, new_addr);
    let dep2_addr = store_canonical(&b, &dep2);
    b.register_name(n("User"), Named::with_addr(dep2_addr));

    let d = diff(&a, &b);
    assert_eq!(d.named_removed.len(), 1);
    assert_eq!(d.named_added.len(), 1);
    let user = changed_by_name(&d, "User");
    assert!(!user.rippled, "renamed dep is not in the map → root");
  }

  /// The third address site: `Expr::Prj` type targets quotient too.
  #[test]
  fn ripple_expr_prj_type_mapped() {
    let build = |t_value: Arc<Expr>| {
      let env = Env::new();
      let t = defn_c(Expr::var(3), t_value);
      let t_addr = store_canonical(&env, &t);
      let dep = defn_ct(
        Expr::var(9),
        Expr::prj(0, 0, Expr::var(0)),
        vec![],
        vec![t_addr.clone()],
        vec![],
      );
      let dep_addr = store_canonical(&env, &dep);
      env.register_name(n("T"), Named::with_addr(t_addr));
      env.register_name(n("UsesT"), Named::with_addr(dep_addr));
      env
    };
    let a = build(Expr::var(0));
    let b = build(Expr::var(1));
    let d = diff(&a, &b);
    assert!(!changed_by_name(&d, "T").rippled);
    assert!(changed_by_name(&d, "UsesT").rippled);
  }

  /// Changed projection coordinates target a different member: root.
  #[test]
  fn ripple_cprj_cidx_change_is_root() {
    let block_a = Constant::new(ConstantInfo::Muts(vec![MutConst::Defn(
      mk_defn(0, Expr::var(3), Expr::var(0)),
    )]));
    let block_b = Constant::new(ConstantInfo::Muts(vec![MutConst::Defn(
      mk_defn(0, Expr::var(3), Expr::var(1)),
    )]));
    let a = Env::new();
    let ba = store_canonical(&a, &block_a);
    let pa = store_canonical(&a, &ctor_proj_constant(0, 0, ba));
    a.register_name(n("C"), Named::with_addr(pa));
    let b = Env::new();
    let bb = store_canonical(&b, &block_b);
    let pb = store_canonical(&b, &ctor_proj_constant(0, 1, bb));
    b.register_name(n("C"), Named::with_addr(pb));
    let d = diff(&a, &b);
    let c = changed_by_name(&d, "C");
    assert_eq!(labels(&c.fields), ["cidx", "block"]);
    assert!(!c.rippled);
  }

  /// Alias rows spanning one (old, new) pair share one cached verdict.
  #[test]
  fn ripple_alias_rows_consistent() {
    let build = |value: Arc<Expr>| {
      let env = Env::new();
      let c = defn_c(Expr::var(3), value);
      let addr = store_canonical(&env, &c);
      env.register_name(n("P"), Named::with_addr(addr.clone()));
      env.register_name(n("Q"), Named::with_addr(addr));
      env
    };
    let a = build(Expr::var(0));
    let b = build(Expr::var(1));
    let d = diff(&a, &b);
    assert_eq!(d.named_changed.len(), 2);
    let p = changed_by_name(&d, "P");
    let q = changed_by_name(&d, "Q");
    assert_eq!(p.rippled, q.rippled);
    assert!(!p.rippled);
    assert_eq!(
      (p.old_addr.clone(), p.new_addr.clone()),
      (q.old_addr.clone(), q.new_addr.clone())
    );
  }

  /// A lone changed leaf with no dependents: verdict root, and strict
  /// fields identical to the pre-ripple behavior.
  #[test]
  fn ripple_single_root_no_map_hits() {
    let (a, _) = env1("Foo", &defn_c(Expr::var(3), Expr::var(0)));
    let (b, _) = env1("Foo", &defn_c(Expr::var(3), Expr::var(1)));
    let d = diff(&a, &b);
    let c = changed_by_name(&d, "Foo");
    assert!(!c.rippled);
    assert_eq!(labels(&c.fields), ["value"]);
  }

  // ==========================================================================
  // Streaming §5 meta sweep (diff_env_bytes)
  // ==========================================================================

  /// Register `name`'s component in `env.names`; returns its address.
  fn register_component(env: &Env, name: &Name) -> Address {
    let addr = Address::from_blake3_hash(*name.get_hash());
    env.names.insert(addr.clone(), name.clone());
    addr
  }

  /// `variant` lands in `type_root`, so two calls with different
  /// variants produce metas that differ while the constant (and its
  /// address) stays identical — a metadata-only difference.
  fn def_meta(name_addr: Address, variant: u32) -> ConstantMeta {
    ConstantMeta::new(ConstantMetaInfo::Def {
      name: name_addr,
      lvls: vec![],
      all: vec![],
      ctx: vec![],
      arena: ExprMeta::default(),
      type_root: u64::from(variant),
      value_root: 0,
    })
  }

  fn full_read(bytes: &[u8]) -> Env {
    let mut cur = bytes;
    Env::get(&mut cur).expect("full read failed")
  }

  /// The streaming §5 sweep must reproduce the full reader's meta-mode
  /// report exactly: `named_meta_only`, `meta_fields` on changed rows,
  /// and everything structural.
  #[test]
  fn meta_sweep_matches_full_reader() {
    let build = |foo_value: Arc<Expr>,
                 foo_variant: u32,
                 monly_variant: u32,
                 foo_original: bool|
     -> Vec<u8> {
      let env = Env::new();
      let foo = n("Foo");
      let foo_comp = register_component(&env, &foo);
      let c = defn_c(Expr::var(3), foo_value);
      let addr = store_canonical(&env, &c);
      let mut foo_named =
        Named::new(addr.clone(), def_meta(foo_comp, foo_variant));
      if foo_original {
        foo_named.set_original(addr, ConstantMeta::default());
      }
      env.register_name(foo.clone(), foo_named);
      // Same const both sides; only metadata differs → named_meta_only.
      let monly = n("MetaOnly");
      let monly_comp = register_component(&env, &monly);
      let stable = defn_c(Expr::var(7), Expr::var(0));
      let stable_addr = store_canonical(&env, &stable);
      env.register_name(
        monly.clone(),
        Named::new(stable_addr, def_meta(monly_comp, monly_variant)),
      );
      let mut bytes = Vec::new();
      env.put(&mut bytes).expect("put failed");
      bytes
    };
    let ba = build(Expr::var(0), 1, 3, false);
    let bb = build(Expr::var(1), 2, 4, true);

    let via_full =
      diff_envs(&full_read(&ba), &full_read(&bb), true).expect("full diff");
    let mut events: Vec<JoinProgress> = Vec::new();
    let via_sweep = diff_env_bytes(&ba, &bb, true, &mut |p| events.push(p))
      .expect("sweep diff");
    assert_eq!(via_full, via_sweep);
    // The pair genuinely exercises both meta categories.
    assert_eq!(via_full.named_meta_only.len(), 1);
    assert_eq!(via_full.named_meta_only[0].0, "MetaOnly");
    let foo_row =
      via_full.named_changed.iter().find(|c| c.name == "Foo").unwrap();
    assert!(!foo_row.meta_fields.is_empty());
    // The sweep phase fired and completed before the join started.
    assert_eq!(events.first().map(|p| p.phase), Some(DiffPhase::MetaSweep));
    let last_sweep =
      events.iter().rfind(|p| p.phase == DiffPhase::MetaSweep).unwrap();
    assert_eq!(last_sweep.done, last_sweep.total);

    // Anon parity through the bytes path too.
    let anon_full =
      diff_envs(&full_read(&ba), &full_read(&bb), false).expect("anon full");
    let anon_sweep =
      diff_env_bytes(&ba, &bb, false, &mut |_| {}).expect("anon sweep");
    assert_eq!(anon_full, anon_sweep);
    // Self-diff via the bytes path is empty in both modes.
    assert!(diff_env_bytes(&ba, &ba, true, &mut |_| {}).unwrap().is_empty());
    assert!(diff_env_bytes(&ba, &ba, false, &mut |_| {}).unwrap().is_empty());
  }

  /// Metadata name references are file-relative §4 indices, so raw §5
  /// windows differ across files whose name tables differ — the sweep
  /// must still see logically identical metadata as equal (it compares
  /// parsed, Address-valued values, never bytes).
  #[test]
  fn meta_sweep_ignores_name_index_shift() {
    let foo = n("Foo");
    let foo_comp = Address::from_blake3_hash(*foo.get_hash());
    // A name whose component address sorts BEFORE Foo's: its presence
    // in env B shifts Foo's §4 index, re-encoding Foo's (identical)
    // metadata over different indices.
    let extra = (0..)
      .map(|i| n(&format!("X{i}")))
      .find(|nm| Address::from_blake3_hash(*nm.get_hash()) < foo_comp)
      .expect("some candidate component sorts before Foo");
    let build = |with_extra: bool| -> Vec<u8> {
      let env = Env::new();
      register_component(&env, &foo);
      let c = defn_c(Expr::var(3), Expr::var(0));
      let addr = store_canonical(&env, &c);
      env.register_name(
        foo.clone(),
        Named::new(addr, def_meta(foo_comp.clone(), 1)),
      );
      if with_extra {
        register_component(&env, &extra);
        let c2 = defn_c(Expr::var(8), Expr::var(2));
        let a2 = store_canonical(&env, &c2);
        env.register_name(extra.clone(), Named::with_addr(a2));
      }
      let mut bytes = Vec::new();
      env.put(&mut bytes).expect("put failed");
      bytes
    };
    let ba = build(false);
    let bb = build(true);
    let d = diff_env_bytes(&ba, &bb, true, &mut |_| {}).expect("sweep diff");
    assert_eq!(d.named_added.len(), 1);
    assert!(
      d.named_meta_only.is_empty(),
      "index shift misread as a metadata diff: {d:?}"
    );
    assert!(d.named_changed.is_empty());
    // And the full reader agrees.
    assert_eq!(
      d,
      diff_envs(&full_read(&ba), &full_read(&bb), true).expect("full diff")
    );
  }

  /// Mmap-backed lazy sides produce the same report as heap-backed
  /// ones (the `rs_diff_env_files` path).
  #[test]
  fn mmap_lazy_side_matches_heap() {
    let build = |value: Arc<Expr>| -> Vec<u8> {
      let env = Env::new();
      let foo = n("Foo");
      register_component(&env, &foo);
      let c = defn_c(Expr::var(3), value);
      let addr = store_canonical(&env, &c);
      env.register_name(foo, Named::with_addr(addr));
      let mut bytes = Vec::new();
      env.put(&mut bytes).expect("put failed");
      bytes
    };
    let (ba, bb) = (build(Expr::var(0)), build(Expr::var(1)));

    let path = std::env::temp_dir()
      .join(format!("ixon-diff-mmap-test-{}.ixe", std::process::id()));
    std::fs::write(&path, &ba).expect("write temp");
    let file = std::fs::File::open(&path).expect("open temp");
    let mmap =
      Arc::new(unsafe { memmap2::Mmap::map(&file) }.expect("mmap temp"));
    let ia = Env::parse_lazy_index(&mmap[..]).expect("lazy index (mmap)");
    let ea = Env::from_lazy_index_mmap(&ia, &mmap).expect("from mmap");

    let ib = Env::parse_lazy_index(&bb).expect("lazy index (heap)");
    let eb = Env::from_lazy_index(&ib, &bb).expect("from heap");

    let via_mmap = diff_envs_lazy(
      LazySide { env: &ea, index: &ia, data: &mmap[..] },
      LazySide { env: &eb, index: &ib, data: &bb },
      true,
      &mut |_| {},
    )
    .expect("mmap-side diff");
    let via_heap =
      diff_env_bytes(&ba, &bb, true, &mut |_| {}).expect("heap diff");
    assert_eq!(via_mmap, via_heap);
    assert_eq!(via_heap.named_changed.len(), 1);
    std::fs::remove_file(&path).ok();
  }
}
