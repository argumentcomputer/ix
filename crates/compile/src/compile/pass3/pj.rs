//! The proof-justified passes (M6R slice 4): O7, O8, O9, O10 and O12 at an
//! occurrence, and the unit pass O11b, in the D1 form. A port of
//! `Ix/Compile/Pass/Opt/{Packed,O7,O8,O9,CollapseRec,O10,O12,O11b}.lean`; the
//! Lean module docstrings are the specification (contract, the lemma each
//! pass's proof term is built from, side condition and fallback, causes), and
//! each function names its Lean original. The sections below follow the Lean
//! modules one by one.
//!
//! Decision 5 (D1): every pass here produces a term that is provably equal to
//! the baseline but not convertible to it. The passes fire only at a site, in
//! the value of a definition (`Packed.pjAllowed`); the Lean name keeps its
//! faithful form, and the rewrite goes to the definition's canonical constant
//! `c._ix` (`Translate.RwState.inPlace`, `Driver.compileCanon`, see
//! [`super::translate`] and [`super::driver`]). No pass reads a dependent or
//! renames a reference; O10 and O12 compare handlers through the canonical
//! forms of their references (`OptEnv.canonAddrOf`).

use rustc_hash::{FxHashMap, FxHashSet};

use bignat::Nat;
use ix_common::address::Address;
use ix_common::env::{
  BinderInfo, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, Expr,
  ExprData, InductiveVal, Level, LevelData, Literal, Name, NameData,
  RecursorVal, ReducibilityHints,
};

use super::develop::instantiate;
use super::expr::{
  alpha_eq, bvar, get_app_fn, get_app_fn_args, is_always_zero, mk_app_n,
  mk_str, nat, nat_usize, replace_const_names, root_name, strip_mdata,
  subst_level,
};
use super::names::{IX_COMPONENT, n_pprod, n_pprod_mk, retyped_name};
use super::opt::{
  AuxKind, Occ, OptBlock, OptEnv, RecShape, as_str, below_name_of, cat,
  classify, forall_arity, ix_aux_of, mk_const, o5_levels, pick, rec_name_of,
  standard_telescope, strip_lams,
};

// ---------------------------------------------------------------------------
// Shared term helpers (`Canon.Expr`)
// ---------------------------------------------------------------------------

/// Some constant or projection structure name of `e` is in `names`
/// (`Canon.mentionsAnyName`).
fn mentions_any_name(names: &FxHashSet<Name>, e: &Expr) -> bool {
  fn go(names: &FxHashSet<Name>, e: &Expr) -> bool {
    match e.as_data() {
      ExprData::Const(nm, _, _) => names.contains(nm),
      ExprData::App(f, a, _) => go(names, f) || go(names, a),
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        go(names, t) || go(names, b)
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        go(names, t) || go(names, v) || go(names, b)
      },
      ExprData::Proj(nm, _, s, _) => names.contains(nm) || go(names, s),
      ExprData::Mdata(_, s, _) => go(names, s),
      _ => false,
    }
  }
  !names.is_empty() && go(names, e)
}

/// Every loose variable of `e` is at least `d` past its binders
/// (`Canon.looseAtLeast`).
fn loose_at_least(e: &Expr, d: usize) -> bool {
  fn go(e: &Expr, k: usize, d: usize) -> bool {
    match e.as_data() {
      ExprData::Bvar(i, _) => {
        let i = nat_usize(i);
        i < k || i - k >= d
      },
      ExprData::App(f, a, _) => go(f, k, d) && go(a, k, d),
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        go(t, k, d) && go(b, k + 1, d)
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        go(t, k, d) && go(v, k, d) && go(b, k + 1, d)
      },
      ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => go(s, k, d),
      _ => true,
    }
  }
  go(e, 0, d)
}

/// The entry of a de Bruijn context at index `k` when the variable is typed
/// as a below value at a constructor (Lean's `ctx[k]? = some (some _)`;
/// innermost binder last in the vector).
fn ctx_get<T: Copy>(ctx: &[Option<T>], k: usize) -> Option<T> {
  if k < ctx.len() { ctx[ctx.len() - 1 - k] } else { None }
}

/// The value of the first canonical constant, when it is a definition
/// (`cs[0]?.bind (·.value)` of O10 and O12).
fn defn_value(cs: &[ConstantInfo]) -> Option<Expr> {
  match cs.first() {
    Some(ConstantInfo::DefnInfo(d)) => Some(d.value.clone()),
    _ => None,
  }
}

// ---------------------------------------------------------------------------
// Packed (`Opt/Packed.lean`): packed images, the collapse renaming, the site
// guard
// ---------------------------------------------------------------------------

/// Strip the projections (and metadata) around a packed image's application
/// (`Packed.stripProjs`).
fn strip_projs(e: &Expr) -> Expr {
  let mut cur = e.clone();
  loop {
    let next = match cur.as_data() {
      ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => s.clone(),
      _ => return cur,
    };
    cur = next;
  }
}

/// The telescope positions of the loose variables of `e` (variables of a
/// lambda telescope of `arity` binders whose body is `e`), in first-occurrence
/// order (`Packed.telescopeVars`).
fn telescope_vars(arity: usize, e: &Expr) -> Vec<usize> {
  fn go(e: &Expr, d: usize, arity: usize, acc: &mut Vec<usize>) {
    match e.as_data() {
      ExprData::Bvar(i, _) => {
        let i = nat_usize(i);
        if i >= d && i - d < arity {
          let p = arity - 1 - (i - d);
          if !acc.contains(&p) {
            acc.push(p);
          }
        }
      },
      ExprData::App(f, a, _) => {
        go(f, d, arity, acc);
        go(a, d, arity, acc);
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        go(t, d, arity, acc);
        go(b, d + 1, arity, acc);
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        go(t, d, arity, acc);
        go(v, d, arity, acc);
        go(b, d + 1, arity, acc);
      },
      ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => {
        go(s, d, arity, acc)
      },
      _ => {},
    }
  }
  let mut acc = Vec::new();
  go(e, 0, arity, &mut acc);
  acc
}

/// The packed shape of an image (`Packed.PackedShape`).
pub(super) struct PackedShape {
  lean_rec: Name,
  level_params: Vec<Name>,
  np: usize,
  nm: usize,
  nmin: usize,
  ni: usize,
  /// The Ix recursor of the major's slot.
  ix_rec: Name,
  /// Its universe arguments in the image, over `level_params`.
  ix_levels: Vec<Level>,
  /// Ix slot `k` packs Lean motives `slots[k]` (Lean order).
  slots: Vec<Vec<usize>>,
  /// The Ix recursor's minor count.
  ix_minors: usize,
}

impl PackedShape {
  fn arity(&self) -> usize {
    self.np + self.nm + self.nmin + self.ni + 1
  }

  /// The slot classes partition Lean's motives (O7, `readCollapseRec`).
  fn partitions(&self) -> bool {
    let flat: Vec<usize> = self.slots.iter().flatten().copied().collect();
    flat.len() == self.nm && (0..self.nm).all(|i| flat.contains(&i))
  }
}

/// Read a packed image: `rho` under the projections, the parameters, indices
/// and major in place, and the Lean motives each Ix motive packs
/// (`Packed.readPacked`).
#[allow(clippy::too_many_arguments)]
fn read_packed(
  lean_rec: &Name,
  level_params: &[Name],
  np: usize,
  nm: usize,
  nmin: usize,
  ni: usize,
  value: &Expr,
  ix_rec_info: &dyn Fn(&Name) -> Option<RecursorVal>,
) -> Option<PackedShape> {
  let arity = np + nm + nmin + ni + 1;
  let body = strip_lams(arity, value)?;
  let (h, args) = get_app_fn_args(&strip_projs(&body));
  let ExprData::Const(rho, ls, _) = h.as_data() else { return None };
  let iv = ix_rec_info(rho)?;
  let (inm, inmin) = (nat_usize(&iv.num_motives), nat_usize(&iv.num_minors));
  if nat_usize(&iv.num_params) != np || nat_usize(&iv.num_indices) != ni {
    return None;
  }
  if args.len() != np + inm + inmin + ni + 1 {
    return None;
  }
  let pos = |e: &Expr| match e.as_data() {
    ExprData::Bvar(k, _) => {
      let k = nat_usize(k);
      if k < arity { Some(arity - 1 - k) } else { None }
    },
    _ => None,
  };
  for (i, a) in args.iter().enumerate().take(np) {
    if pos(a) != Some(i) {
      return None;
    }
  }
  for i in 0..ni + 1 {
    if pos(&args[np + inm + inmin + i]) != Some(np + nm + nmin + i) {
      return None;
    }
  }
  let mut slots = Vec::new();
  for k in 0..inm {
    let vs: Vec<usize> = telescope_vars(arity, &args[np + k])
      .into_iter()
      .filter_map(|p| if np <= p && p < np + nm { Some(p - np) } else { None })
      .collect();
    if vs.is_empty() {
      return None;
    }
    slots.push(vs);
  }
  Some(PackedShape {
    lean_rec: lean_rec.clone(),
    level_params: level_params.to_vec(),
    np,
    nm,
    nmin,
    ni,
    ix_rec: rho.clone(),
    ix_levels: ls.clone(),
    slots,
    ix_minors: inmin,
  })
}

/// The packed shape of the image of Lean recursor `r` of block `b`
/// (`OptBlock.packed?`).
fn packed(env: &OptEnv<'_>, b: &OptBlock, r: &Name) -> Option<PackedShape> {
  let (lps, img) = b.images.get(r)?;
  let Some(ConstantInfo::RecInfo(rv)) = env.const_of(r) else { return None };
  read_packed(
    r,
    lps,
    nat_usize(&rv.num_params),
    nat_usize(&rv.num_motives),
    nat_usize(&rv.num_minors),
    nat_usize(&rv.num_indices),
    img,
    &|n| b.ix_recs.get(n).cloned(),
  )
}

/// The collapse renaming of block `b`: every member to its class's first
/// member, its constructors to that member's by position
/// (`Packed.collapseRenaming`).
fn collapse_renaming(env: &OptEnv<'_>, b: &OptBlock) -> FxHashMap<Name, Name> {
  let mut m = FxHashMap::default();
  for x in &b.all {
    let Some(cls) = b.class_of.get(x) else { continue };
    let Some(rep) = cls.first() else { continue };
    if rep == x {
      continue;
    }
    m.insert(x.clone(), rep.clone());
    if let (
      Some(ConstantInfo::InductInfo(ix)),
      Some(ConstantInfo::InductInfo(ir)),
    ) = (env.const_of(x), env.const_of(rep))
    {
      for (c, c2) in ix.ctors.iter().zip(ir.ctors.iter()) {
        m.insert(c.clone(), c2.clone());
      }
    }
  }
  m
}

/// Two arguments agree after compilation: alpha-equal once the collapse
/// renaming is applied (`Packed.agreeAfterCompile`).
fn agree_after_compile(
  ren: &FxHashMap<Name, Name>,
  a: &Expr,
  b: &Expr,
) -> bool {
  alpha_eq(&replace_const_names(ren, a), &replace_const_names(ren, b))
}

/// The universe arguments of `rho` (and of its `casesOn`, `recOn`) at the
/// occurrence's levels, with Lean's motive universe in place of the
/// packing's `max 1 u` (`Packed.singleLevels`).
fn single_levels(
  env: &OptEnv<'_>,
  s: &PackedShape,
  us: &[Level],
) -> Option<Vec<Level>> {
  let Some(ConstantInfo::RecInfo(rv)) = env.const_of(&s.lean_rec) else {
    return None;
  };
  let x = rv.all.first()?;
  let Some(ConstantInfo::InductInfo(iv)) = env.const_of(x) else {
    return None;
  };
  let lean_elim = rv.cnst.level_params.len() > iv.cnst.level_params.len();
  let ls: Vec<Level> = if s.ix_levels.len() == s.level_params.len() {
    if lean_elim {
      let u = s.level_params.first()?;
      let mut ls = s.ix_levels.clone();
      if let Some(l0) = ls.first_mut() {
        *l0 = Level::param(u.clone());
      }
      ls
    } else {
      s.ix_levels.clone()
    }
  } else if s.ix_levels.len() == s.level_params.len() + 1 {
    match s.ix_levels.first().map(Level::as_data) {
      Some(LevelData::Zero(_)) => s.ix_levels.clone(),
      _ => return None,
    }
  } else {
    return None;
  };
  Some(ls.iter().map(|l| subst_level(&s.level_params, us, l)).collect())
}

/// The site guard of every proof-justified pass, applied last: the
/// occurrence is in the value of a definition (`Packed.pjAllowed`).
fn pj_allowed(o: &Occ<'_>) -> bool {
  o.site.is_some()
}

// ---------------------------------------------------------------------------
// O7 (`Opt/O7.lean`): `rec`/`recOn` over a collapsed block with identical
// motives and minors per class
// ---------------------------------------------------------------------------

/// `O7.apply`.
pub(super) fn o7(env: &OptEnv<'_>, o: &Occ<'_>) -> Option<Expr> {
  let (k, r) = classify(o.head)?;
  if k != AuxKind::Rec && k != AuxKind::RecOn {
    return None;
  }
  let b = (env.block_of)(o.head)?;
  let ch = &b.change;
  if !ch.collapse || ch.split || ch.evaporation {
    return None;
  }
  let Some(ConstantInfo::RecInfo(rv)) = env.const_of(&r) else { return None };
  if nat_usize(&rv.num_motives) != b.all.len() {
    return None;
  }
  let s = packed(env, b, &r)?;
  // the slot classes partition Lean's motives
  if !s.partitions() {
    return None;
  }
  let ci = env.const_of(o.head)?;
  if *ci.get_level_params() != s.level_params {
    return None;
  }
  let n = s.arity();
  if forall_arity(ci.get_type()) != n {
    return None;
  }
  if o.args.len() < n {
    return None;
  }
  // Lean's minors, member by member
  let mut counts: Vec<usize> = Vec::with_capacity(b.all.len());
  for m in &b.all {
    match env.const_of(m) {
      Some(ConstantInfo::InductInfo(iv)) => counts.push(iv.ctors.len()),
      _ => return None,
    }
  }
  if counts.iter().sum::<usize>() != s.nmin {
    return None;
  }
  let mut offsets: Vec<usize> = vec![0];
  for c in &counts {
    offsets.push(offsets.last().copied().unwrap_or(0) + c);
  }
  let a = o.args;
  let (np, nm, nmin, ni) = (s.np, s.nm, s.nmin, s.ni);
  let ps = &a[..np];
  let ms = &a[np..np + nm];
  let (mins, tail) = if k == AuxKind::Rec {
    (&a[np + nm..np + nm + nmin], &a[np + nm + nmin..n])
  } else {
    (&a[np + nm + ni + 1..n], &a[np + nm..np + nm + ni + 1])
  };
  let extra = &a[n..];
  let ren = collapse_renaming(env, b);
  let mut ms2: Vec<Expr> = Vec::new();
  let mut mins2: Vec<Expr> = Vec::new();
  for cls in &s.slots {
    let rep = *cls.first()?;
    let mr = ms.get(rep)?;
    let nc = *counts.get(rep)?;
    for &i in cls {
      let mi = ms.get(i)?;
      if !agree_after_compile(&ren, mi, mr) {
        return None;
      }
      if counts.get(i) != Some(&nc) {
        return None;
      }
    }
    for q in 0..nc {
      let vr = mins.get(offsets[rep] + q)?;
      for &i in cls {
        let vi = mins.get(offsets[i] + q)?;
        if !agree_after_compile(&ren, vi, vr) {
          return None;
        }
      }
      mins2.push(vr.clone());
    }
    ms2.push(mr.clone());
  }
  if mins2.len() != s.ix_minors {
    return None;
  }
  let ls = single_levels(env, &s, o.us)?;
  if !pj_allowed(o) {
    return None;
  }
  if k == AuxKind::Rec {
    Some(mk_app_n(
      mk_const(&s.ix_rec, ls),
      &cat(&[ps, &ms2, &mins2, tail, extra]),
    ))
  } else {
    let ix_rec_on = ix_aux_of(&s.ix_rec, AuxKind::RecOn)?;
    if !(env.resolves)(&ix_rec_on) {
      return None;
    }
    Some(mk_app_n(
      mk_const(&ix_rec_on, ls),
      &cat(&[ps, &ms2, tail, &mins2, extra]),
    ))
  }
}

// ---------------------------------------------------------------------------
// O8 (`Opt/O8.lean`): `casesOn` over a collapsed or lifted member
// ---------------------------------------------------------------------------

/// `O3.casesOnMember`.
fn cases_on_member(n: &Name) -> Option<Name> {
  match as_str(n)? {
    (x, "casesOn") => Some(x.clone()),
    _ => None,
  }
}

/// `O8.apply`.
pub(super) fn o8(env: &OptEnv<'_>, o: &Occ<'_>) -> Option<Expr> {
  let (k, r) = classify(o.head)?;
  if k != AuxKind::CasesOn {
    return None;
  }
  let x = cases_on_member(o.head)?;
  let b = (env.block_of)(o.head)?;
  if !b.change.collapse {
    return None;
  }
  let s = packed(env, b, &r)?;
  let Some(ConstantInfo::InductInfo(iv)) = env.const_of(&x) else {
    return None;
  };
  let ci = env.const_of(o.head)?;
  if *ci.get_level_params() != s.level_params {
    return None;
  }
  let n = s.np + 1 + s.ni + 1 + iv.ctors.len();
  if forall_arity(ci.get_type()) != n {
    return None;
  }
  if o.args.len() < n {
    return None;
  }
  let ix_cases = ix_aux_of(&s.ix_rec, AuxKind::CasesOn)?;
  if !(env.resolves)(&ix_cases) {
    return None;
  }
  let ls = single_levels(env, &s, o.us)?;
  if !pj_allowed(o) {
    return None;
  }
  Some(mk_app_n(mk_const(&ix_cases, ls), o.args))
}

// ---------------------------------------------------------------------------
// O9 (`Opt/O9.lean`): structural recursion over a split block with a cross
// field (the Ix `brecOn` with re-pathed handlers)
// ---------------------------------------------------------------------------

/// For one constructor: Lean's below leaves (one per field whose type is a
/// member of the block, in field order), each mapped to its Ix leaf or `None`
/// (a cross field); and the Ix leaf count (`O9.LeafMap`).
pub(super) struct LeafMap {
  map: Vec<Option<usize>>,
  ix_leaves: usize,
}

/// Peel `n` leading `forall`s, looking through metadata.
fn peel_n(ty: &Expr, n: usize) -> Option<Expr> {
  let mut ty = ty.clone();
  for _ in 0..n {
    let s = strip_mdata(&ty);
    let ExprData::ForallE(_, _, b, _, _) = s.as_data() else { return None };
    let b = b.clone();
    ty = b;
  }
  Some(ty)
}

/// The leaf map of constructor `k` of `x` (component `{x}`), or `None` when a
/// field mentions the block other than as a member applied
/// (`O9.leafMapOf`).
fn leaf_map_of(
  env: &OptEnv<'_>,
  all: &[Name],
  x: &Name,
  np: usize,
  k: &Name,
) -> Option<LeafMap> {
  let Some(ConstantInfo::CtorInfo(cv)) = env.const_of(k) else { return None };
  let blk: FxHashSet<Name> = all.iter().cloned().collect();
  let mut ty = peel_n(&cv.cnst.typ, np)?;
  let mut map = Vec::new();
  let mut n = 0;
  for _ in 0..nat_usize(&cv.num_fields) {
    let s = strip_mdata(&ty);
    let ExprData::ForallE(_, d, b, _, _) = s.as_data() else { return None };
    match get_app_fn(&strip_mdata(d)).as_data() {
      ExprData::Const(h, _, _) => {
        if blk.contains(h) {
          if h == x {
            map.push(Some(n));
            n += 1;
          } else {
            map.push(None);
          }
        } else if mentions_any_name(&blk, d) {
          return None;
        }
      },
      _ => {
        if mentions_any_name(&blk, d) {
          return None;
        }
      },
    }
    let b = b.clone();
    ty = b;
  }
  Some(LeafMap { map, ix_leaves: n })
}

/// The data of one re-typing (`O9.Retype`).
struct Retype<'s> {
  /// Lean's `x.below`.
  below_n: Name,
  /// Its argument count (`np + nm + ni + 1`).
  n_args: usize,
  np: usize,
  nm: usize,
  /// The Ix `rho.below`.
  ix_below: Name,
  /// The recursor shape (selection and O5's level rule).
  shape: &'s RecShape,
  /// The constructors of `x` and their leaf maps.
  leaves: FxHashMap<Name, LeafMap>,
  /// The block's Lean `below`/`brecOn` family: must not remain.
  forbidden: FxHashSet<Name>,
}

/// A chain of projections ending in a variable: the variable and the
/// projections (index, structure), innermost first (`O9.projChain`).
fn proj_chain(e: &Expr) -> Option<(Nat, Vec<(Nat, Name)>)> {
  let mut acc: Vec<(Nat, Name)> = Vec::new();
  let mut cur = e.clone();
  loop {
    let ExprData::Proj(s, i, inner, _) = cur.as_data() else { return None };
    acc.push((i.clone(), s.clone()));
    if let ExprData::Bvar(k, _) = inner.as_data() {
      acc.reverse();
      return Some((k.clone(), acc));
    }
    let next = inner.clone();
    cur = next;
  }
}

/// Re-path Lean's path (innermost first) to a field's recursive value
/// (`.2^j.1.1 ...`, `.2^j.1 ...` at the last leaf) to the Ix path to the same
/// value (`.1` included), with the length of the copied remainder
/// (`O9.repath`).
fn repath(lm: &LeafMap, path: &[usize]) -> Option<(Vec<usize>, usize)> {
  let k = lm.map.len();
  if k == 0 {
    return None;
  }
  // leading `.2`s select the leaf
  let mut j = 0;
  let mut p = path;
  while j + 1 < k {
    match p.split_first() {
      Some((1, rest)) => {
        j += 1;
        p = rest;
      },
      _ => break,
    }
  }
  if j + 1 < k {
    match p.split_first() {
      Some((0, rest)) => p = rest,
      _ => return None,
    }
  }
  // the leaf's `.1`: the recursive value
  let rest = match p.split_first() {
    Some((0, rest)) => rest,
    _ => return None,
  };
  let j2 = (*lm.map.get(j)?)?;
  let mut sel = vec![1; j2];
  if j2 + 1 < lm.ix_leaves {
    sel.push(0);
  }
  sel.push(0);
  Some((sel, rest.len()))
}

/// Rebuild a re-pathed projection chain: `sel` over the variable with the
/// innermost structure, then the copied remainder `rest` (innermost first).
fn rebuild_chain(
  k: &Nat,
  pprod: &Name,
  sel: &[usize],
  rest: &[(Nat, Name)],
) -> Expr {
  let mut inner = Expr::bvar(k.clone());
  for j in sel {
    inner = Expr::proj(pprod.clone(), nat(*j), inner);
  }
  for (j, sn) in rest {
    inner = Expr::proj(sn.clone(), j.clone(), inner);
  }
  inner
}

impl Retype<'_> {
  /// The leaf map of a below type at a constructor
  /// (`x.below ps ms is (k fs)`, `Retype.atCtor`).
  fn at_ctor(&self, ty: &Expr) -> Option<&LeafMap> {
    let (h, args) = get_app_fn_args(&strip_mdata(ty));
    let ExprData::Const(n, _, _) = h.as_data() else { return None };
    if *n != self.below_n || args.len() != self.n_args {
      return None;
    }
    let hd = get_app_fn(&strip_mdata(args.last()?));
    let ExprData::Const(k, _, _) = hd.as_data() else { return None };
    self.leaves.get(k)
  }

  fn go_all<'r>(
    &'r self,
    fuel: usize,
    ctx: &mut Vec<Option<&'r LeafMap>>,
    es: &[Expr],
  ) -> Option<Vec<Expr>> {
    es.iter().map(|a| self.go(fuel, ctx, a)).collect()
  }

  /// Re-type a term; `ctx` gives the leaf map of each bound variable typed
  /// as a below value at a constructor (`Retype.go`).
  fn go<'r>(
    &'r self,
    fuel: usize,
    ctx: &mut Vec<Option<&'r LeafMap>>,
    e: &Expr,
  ) -> Option<Expr> {
    if fuel == 0 {
      return None;
    }
    let fuel = fuel - 1;
    match e.as_data() {
      ExprData::Bvar(k, _) => {
        if ctx_get(ctx, nat_usize(k)).is_some() {
          None
        } else {
          Some(e.clone())
        }
      },
      ExprData::Const(n, _, _) => {
        if self.forbidden.contains(n) {
          None
        } else {
          Some(e.clone())
        }
      },
      ExprData::App(..) => {
        let (h, args) = get_app_fn_args(e);
        match h.as_data() {
          ExprData::Const(n, us, _) => {
            if *n == self.below_n && args.len() == self.n_args {
              let args2 = self.go_all(fuel, ctx, &args)?;
              let ls = o5_levels(self.shape, us)?;
              let ms = pick(
                &args2[self.np..self.np + self.nm],
                &self.shape.motive_src,
              )?;
              return Some(mk_app_n(
                mk_const(&self.ix_below, ls),
                &cat(&[&args2[..self.np], &ms, &args2[self.np + self.nm..]]),
              ));
            }
            if self.forbidden.contains(n) {
              return None;
            }
            let args2 = self.go_all(fuel, ctx, &args)?;
            Some(mk_app_n(h.clone(), &args2))
          },
          _ => {
            let h2 = self.go(fuel, ctx, &h)?;
            let args2 = self.go_all(fuel, ctx, &args)?;
            Some(mk_app_n(h2, &args2))
          },
        }
      },
      ExprData::Proj(s, i, x, _) => {
        if let Some((k, chain)) = proj_chain(e)
          && let (Some(lm), Some((_, pprod))) =
            (ctx_get(ctx, nat_usize(&k)), chain.first())
        {
          // `chain` is innermost first; the leaf part is `PProd`, the rest is
          // copied
          let path: Vec<usize> =
            chain.iter().map(|(j, _)| nat_usize(j)).collect();
          let (sel, rest_len) = repath(lm, &path)?;
          let rest = &chain[chain.len() - rest_len..];
          return Some(rebuild_chain(&k, pprod, &sel, rest));
        }
        let x2 = self.go(fuel, ctx, x)?;
        Some(Expr::proj(s.clone(), i.clone(), x2))
      },
      ExprData::Lam(n, t, b, bi, _) => {
        let t2 = self.go(fuel, ctx, t)?;
        ctx.push(self.at_ctor(t));
        let b2 = self.go(fuel, ctx, b);
        ctx.pop();
        Some(Expr::lam(n.clone(), t2, b2?, bi.clone()))
      },
      ExprData::ForallE(n, t, b, bi, _) => {
        let t2 = self.go(fuel, ctx, t)?;
        ctx.push(self.at_ctor(t));
        let b2 = self.go(fuel, ctx, b);
        ctx.pop();
        Some(Expr::all(n.clone(), t2, b2?, bi.clone()))
      },
      ExprData::LetE(n, t, v, b, nd, _) => {
        let t2 = self.go(fuel, ctx, t)?;
        let v2 = self.go(fuel, ctx, v)?;
        ctx.push(None);
        let b2 = self.go(fuel, ctx, b);
        ctx.pop();
        Some(Expr::letE(n.clone(), t2, v2, b2?, *nd))
      },
      ExprData::Mdata(md, x, _) => {
        let x2 = self.go(fuel, ctx, x)?;
        Some(Expr::mdata(md.clone(), x2))
      },
      _ => Some(e.clone()),
    }
  }
}

/// The recursion bound of a re-typing (`O9.retypeFuel`).
const RETYPE_FUEL: usize = 1 << 16;

/// A re-typed handler constant: `g` with name `g2`, re-typed type and value,
/// `g`'s universe parameters, hints and safety.
fn retyped_def(
  gv: &DefinitionVal,
  g2: &Name,
  ty: Expr,
  v: Expr,
) -> DefinitionVal {
  DefinitionVal {
    cnst: ConstantVal {
      name: g2.clone(),
      level_params: gv.cnst.level_params.clone(),
      typ: ty,
    },
    value: v,
    hints: gv.hints,
    safety: gv.safety,
    all: vec![g2.clone()],
  }
}

/// `O9.apply`.
pub(super) fn o9(
  env: &OptEnv<'_>,
  o: &Occ<'_>,
) -> Option<(Expr, Vec<ConstantInfo>)> {
  let (k, r) = classify(o.head)?;
  if k != AuxKind::BRecOn {
    return None;
  }
  let b = (env.block_of)(o.head)?;
  if !b.change.split || b.change.collapse {
    return None;
  }
  let s = b.shapes.get(&r)?;
  if s.is_selection() {
    return None;
  }
  let Some(ConstantInfo::RecInfo(rv)) = env.const_of(&r) else { return None };
  if nat_usize(&rv.num_motives) != b.all.len() {
    return None;
  }
  if s.motive_src.len() != 1 {
    return None;
  }
  let mi = *s.motive_src.first()?;
  let x = b.all.get(mi)?.clone();
  if r != rec_name_of(&x, None) {
    return None;
  }
  let n = standard_telescope(env, s, AuxKind::BRecOn, o.head, 0)?;
  if o.args.len() < n {
    return None;
  }
  let ls = o5_levels(s, o.us)?;
  let ix_brec_on = ix_aux_of(&s.ix_rec, AuxKind::BRecOn)?;
  let ix_below = ix_aux_of(&s.ix_rec, AuxKind::Below)?;
  if !(env.resolves)(&ix_brec_on) || !(env.resolves)(&ix_below) {
    return None;
  }
  let Some(ConstantInfo::InductInfo(iv)) = env.const_of(&x) else {
    return None;
  };
  let mut leaves: FxHashMap<Name, LeafMap> = FxHashMap::default();
  for c in &iv.ctors {
    leaves.insert(c.clone(), leaf_map_of(env, &b.all, &x, s.np, c)?);
  }
  let mut forbidden: FxHashSet<Name> = FxHashSet::default();
  for m in &b.all {
    forbidden.insert(mk_str(m, "below"));
    forbidden.insert(mk_str(m, "brecOn"));
  }
  let rt = Retype {
    below_n: below_name_of(&r),
    n_args: s.np + s.nm + s.ni + 1,
    np: s.np,
    nm: s.nm,
    ix_below,
    shape: s,
    leaves,
    forbidden,
  };
  let a = o.args;
  let ps = &a[..s.np];
  let ms = pick(&a[s.np..s.np + s.nm], &s.motive_src)?;
  let tail = &a[s.np + s.nm..s.np + s.nm + s.ni + 1];
  let hs = &a[s.np + s.nm + s.ni + 1..n];
  let rest = &a[n..];
  let h = hs.get(mi)?;
  let (h2, canon) = match h.as_data() {
    ExprData::Const(g, gus, _) => {
      let Some(ConstantInfo::DefnInfo(gv)) = env.const_of(g) else {
        return None;
      };
      let ty2 = rt.go(RETYPE_FUEL, &mut Vec::new(), &gv.cnst.typ)?;
      let v2 = rt.go(RETYPE_FUEL, &mut Vec::new(), &gv.value)?;
      let g2 = retyped_name(g)?;
      let dv = retyped_def(&gv, &g2, ty2, v2);
      (Expr::cnst(g2, gus.clone()), vec![ConstantInfo::DefnInfo(dv)])
    },
    _ => (rt.go(RETYPE_FUEL, &mut Vec::new(), h)?, Vec::new()),
  };
  if !pj_allowed(o) {
    return None;
  }
  Some((
    mk_app_n(
      mk_const(&ix_brec_on, ls),
      &cat(&[ps, &ms, tail, std::slice::from_ref(&h2), rest]),
    ),
    canon,
  ))
}

// ---------------------------------------------------------------------------
// CollapseRec (`Opt/CollapseRec.lean`): structural recursion over a collapsed
// block, shared by O10 and O12
// ---------------------------------------------------------------------------

/// Equality after compilation: alpha-equality where constants agree under
/// the renaming or by their compiled addresses (`CollapseRec.agreeAddr`).
fn agree_addr(
  ren: &FxHashMap<Name, Name>,
  addr: &dyn Fn(&Name) -> Option<Address>,
  a: &Expr,
  b: &Expr,
) -> bool {
  let rn = |n: &Name| ren.get(n).cloned().unwrap_or_else(|| n.clone());
  match (a.as_data(), b.as_data()) {
    (ExprData::Bvar(i, _), ExprData::Bvar(j, _)) => i == j,
    (ExprData::Sort(u, _), ExprData::Sort(v, _)) => u == v,
    (ExprData::Const(x, us, _), ExprData::Const(y, vs, _)) => {
      us == vs
        && (x == y
          || rn(x) == rn(y)
          || matches!((addr(x), addr(y)), (Some(p), Some(q)) if p == q))
    },
    (ExprData::App(f, x, _), ExprData::App(g, y, _)) => {
      agree_addr(ren, addr, f, g) && agree_addr(ren, addr, x, y)
    },
    (ExprData::Lam(_, t, b1, _, _), ExprData::Lam(_, t2, b2, _, _))
    | (ExprData::ForallE(_, t, b1, _, _), ExprData::ForallE(_, t2, b2, _, _)) => {
      agree_addr(ren, addr, t, t2) && agree_addr(ren, addr, b1, b2)
    },
    (
      ExprData::LetE(_, t, v, b1, _, _),
      ExprData::LetE(_, t2, v2, b2, _, _),
    ) => {
      agree_addr(ren, addr, t, t2)
        && agree_addr(ren, addr, v, v2)
        && agree_addr(ren, addr, b1, b2)
    },
    (ExprData::Lit(x, _), ExprData::Lit(y, _)) => x == y,
    (ExprData::Mdata(_, x, _), _) => agree_addr(ren, addr, x, b),
    (_, ExprData::Mdata(_, y, _)) => agree_addr(ren, addr, a, y),
    (ExprData::Proj(s, i, x, _), ExprData::Proj(s2, i2, y, _)) => {
      rn(s) == rn(s2) && i == i2 && agree_addr(ren, addr, x, y)
    },
    _ => false,
  }
}

/// The reading of a collapsed block's `brecOn` occurrence
/// (`CollapseRec.CollapseRec`).
struct CollapseRec<'b> {
  b: &'b OptBlock,
  /// The packed shape of the major's recursor.
  s: PackedShape,
  /// The major's member.
  x: Name,
  /// The slot of each Lean motive (member, by `all` index).
  slot_of: Vec<usize>,
  /// The Ix recursor of each slot.
  slot_rec: Vec<Name>,
  ps: Vec<Expr>,
  ms: Vec<Expr>,
  tail: Vec<Expr>,
  hs: Vec<Expr>,
  rest: Vec<Expr>,
}

/// Read a `brecOn` occurrence over a collapsed, unsplit block
/// (`CollapseRec.readCollapseRec`).
fn read_collapse_rec<'b>(
  env: &OptEnv<'b>,
  o: &Occ<'_>,
) -> Option<CollapseRec<'b>> {
  let (k, r) = classify(o.head)?;
  if k != AuxKind::BRecOn {
    return None;
  }
  let b = (env.block_of)(o.head)?;
  let ch = &b.change;
  if !ch.collapse || ch.split || ch.evaporation {
    return None;
  }
  let Some(ConstantInfo::RecInfo(rv)) = env.const_of(&r) else { return None };
  if nat_usize(&rv.num_motives) != b.all.len() {
    return None;
  }
  let s = packed(env, b, &r)?;
  if !s.partitions() {
    return None;
  }
  let x = b.all.iter().find(|m| rec_name_of(m, None) == r)?.clone();
  let ci = env.const_of(o.head)?;
  if *ci.get_level_params() != s.level_params {
    return None;
  }
  let n = s.np + s.nm + s.ni + 1 + s.nm;
  if forall_arity(ci.get_type()) != n {
    return None;
  }
  if o.args.len() < n {
    return None;
  }
  let mut slot_of = vec![0; s.nm];
  for (kk, cls) in s.slots.iter().enumerate() {
    for &i in cls {
      if let Some(x) = slot_of.get_mut(i) {
        *x = kk;
      }
    }
  }
  // the Ix recursor of each slot, from its members' images
  let mut slot_rec = Vec::new();
  for cls in &s.slots {
    let i = *cls.first()?;
    let m = b.all.get(i)?;
    let sm = packed(env, b, &rec_name_of(m, None))?;
    slot_rec.push(sm.ix_rec);
  }
  let a = o.args;
  let (np, nm, ni) = (s.np, s.nm, s.ni);
  Some(CollapseRec {
    b,
    x,
    slot_of,
    slot_rec,
    ps: a[..np].to_vec(),
    ms: a[np..np + nm].to_vec(),
    tail: a[np + nm..np + nm + ni + 1].to_vec(),
    hs: a[np + nm + ni + 1..n].to_vec(),
    rest: a[n..].to_vec(),
    s,
  })
}

/// For one constructor of a member: the Lean motive (member index) of each
/// below leaf, or `None` when a field mentions the block other than as a
/// member applied (`CollapseRec.leafMembers`).
fn leaf_members(
  env: &OptEnv<'_>,
  all: &[Name],
  np: usize,
  k: &Name,
) -> Option<Vec<usize>> {
  let Some(ConstantInfo::CtorInfo(cv)) = env.const_of(k) else { return None };
  let blk: FxHashSet<Name> = all.iter().cloned().collect();
  let mut ty = peel_n(&cv.cnst.typ, np)?;
  let mut out = Vec::new();
  for _ in 0..nat_usize(&cv.num_fields) {
    let s = strip_mdata(&ty);
    let ExprData::ForallE(_, d, b, _, _) = s.as_data() else { return None };
    match get_app_fn(&strip_mdata(d)).as_data() {
      ExprData::Const(h, _, _) => match all.iter().position(|m| m == h) {
        Some(i) => out.push(i),
        None => {
          if mentions_any_name(&blk, d) {
            return None;
          }
        },
      },
      _ => {
        if mentions_any_name(&blk, d) {
          return None;
        }
      },
    }
    let b = b.clone();
    ty = b;
  }
  Some(out)
}

type LevelsFn<'l> = Box<dyn Fn(&[Level]) -> Option<Vec<Level>> + 'l>;
type ExtraFn<'l> = Box<dyn Fn(usize) -> Vec<usize> + 'l>;

/// How a re-typing maps a below value at a constructor (`CollapseRec.CRetype`):
/// `extra = None` keeps every path (and allows bare uses), `Some f` re-paths
/// the leaf-value path of a leaf of Lean motive `i` by appending `f i` after
/// its `.1`, and forbids bare uses.
struct CRetype<'l> {
  /// Lean's `M.below` of every member to the member index.
  belows: FxHashMap<Name, usize>,
  n_args: usize,
  np: usize,
  nm: usize,
  /// The Ix `below` of each slot.
  ix_below: Vec<Name>,
  slot_of: Vec<usize>,
  /// The new motives, one per slot.
  motives: Vec<Expr>,
  /// The Ix `below`'s universe arguments at an occurrence's levels.
  levels: LevelsFn<'l>,
  /// Each constructor of the block to its leaves' Lean motives.
  leaves: FxHashMap<Name, Vec<usize>>,
  /// The re-path of a leaf value (`None`: identity).
  extra: Option<ExtraFn<'l>>,
  /// The block's other Lean `below`/`brecOn` names: must not remain.
  forbidden: FxHashSet<Name>,
}

/// Re-path a leaf-value path (innermost first, Lean's right-nested leaves)
/// for `extra`; the selection is unchanged (same leaves)
/// (`CollapseRec.crepath`).
fn crepath(
  lvs: &[usize],
  extra: &dyn Fn(usize) -> Vec<usize>,
  path: &[usize],
) -> Option<(Vec<usize>, usize)> {
  let k = lvs.len();
  if k == 0 {
    return None;
  }
  let mut j = 0;
  let mut p = path;
  while j + 1 < k {
    match p.split_first() {
      Some((1, rest)) => {
        j += 1;
        p = rest;
      },
      _ => break,
    }
  }
  let mut sel: Vec<usize> = vec![1; j];
  if j + 1 < k {
    match p.split_first() {
      Some((0, rest)) => {
        p = rest;
        sel.push(0);
      },
      _ => return None,
    }
  }
  let rest = match p.split_first() {
    Some((0, rest)) => rest,
    _ => return None,
  };
  let i = *lvs.get(j)?;
  sel.push(0);
  sel.extend(extra(i));
  Some((sel, rest.len()))
}

impl CRetype<'_> {
  /// `CRetype.atCtor`.
  fn at_ctor(&self, ty: &Expr) -> Option<&Vec<usize>> {
    let (h, args) = get_app_fn_args(&strip_mdata(ty));
    let ExprData::Const(n, _, _) = h.as_data() else { return None };
    if !self.belows.contains_key(n) || args.len() != self.n_args {
      return None;
    }
    let hd = get_app_fn(&strip_mdata(args.last()?));
    let ExprData::Const(k, _, _) = hd.as_data() else { return None };
    self.leaves.get(k)
  }

  fn go_all<'r>(
    &'r self,
    fuel: usize,
    ctx: &mut Vec<Option<&'r Vec<usize>>>,
    es: &[Expr],
  ) -> Option<Vec<Expr>> {
    es.iter().map(|a| self.go(fuel, ctx, a)).collect()
  }

  /// `CRetype.go`.
  fn go<'r>(
    &'r self,
    fuel: usize,
    ctx: &mut Vec<Option<&'r Vec<usize>>>,
    e: &Expr,
  ) -> Option<Expr> {
    if fuel == 0 {
      return None;
    }
    let fuel = fuel - 1;
    match e.as_data() {
      ExprData::Bvar(k, _) => {
        if ctx_get(ctx, nat_usize(k)).is_some() && self.extra.is_some() {
          None
        } else {
          Some(e.clone())
        }
      },
      ExprData::Const(n, _, _) => {
        if self.forbidden.contains(n) || self.belows.contains_key(n) {
          None
        } else {
          Some(e.clone())
        }
      },
      ExprData::App(..) => {
        let (h, args) = get_app_fn_args(e);
        match h.as_data() {
          ExprData::Const(n, us, _) => {
            if let Some(&mi) = self.belows.get(n) {
              if args.len() != self.n_args {
                return None;
              }
              let args2 = self.go_all(fuel, ctx, &args)?;
              let ls = (self.levels)(us)?;
              let sl = *self.slot_of.get(mi)?;
              let ix_b = self.ix_below.get(sl)?;
              return Some(mk_app_n(
                mk_const(ix_b, ls),
                &cat(&[
                  &args2[..self.np],
                  &self.motives,
                  &args2[self.np + self.nm..],
                ]),
              ));
            }
            if self.forbidden.contains(n) {
              return None;
            }
            let args2 = self.go_all(fuel, ctx, &args)?;
            Some(mk_app_n(h.clone(), &args2))
          },
          _ => {
            let h2 = self.go(fuel, ctx, &h)?;
            let args2 = self.go_all(fuel, ctx, &args)?;
            Some(mk_app_n(h2, &args2))
          },
        }
      },
      ExprData::Proj(s, i, x, _) => {
        if let Some(ex) = &self.extra
          && let Some((k, chain)) = proj_chain(e)
          && let (Some(lvs), Some((_, pprod))) =
            (ctx_get(ctx, nat_usize(&k)), chain.first())
        {
          let path: Vec<usize> =
            chain.iter().map(|(j, _)| nat_usize(j)).collect();
          let (sel, rest_len) = crepath(lvs, ex.as_ref(), &path)?;
          let rest = &chain[chain.len() - rest_len..];
          return Some(rebuild_chain(&k, pprod, &sel, rest));
        }
        let x2 = self.go(fuel, ctx, x)?;
        Some(Expr::proj(s.clone(), i.clone(), x2))
      },
      ExprData::Lam(n, t, b, bi, _) => {
        let t2 = self.go(fuel, ctx, t)?;
        ctx.push(self.at_ctor(t));
        let b2 = self.go(fuel, ctx, b);
        ctx.pop();
        Some(Expr::lam(n.clone(), t2, b2?, bi.clone()))
      },
      ExprData::ForallE(n, t, b, bi, _) => {
        let t2 = self.go(fuel, ctx, t)?;
        ctx.push(self.at_ctor(t));
        let b2 = self.go(fuel, ctx, b);
        ctx.pop();
        Some(Expr::all(n.clone(), t2, b2?, bi.clone()))
      },
      ExprData::LetE(n, t, v, b, nd, _) => {
        let t2 = self.go(fuel, ctx, t)?;
        let v2 = self.go(fuel, ctx, v)?;
        ctx.push(None);
        let b2 = self.go(fuel, ctx, b);
        ctx.pop();
        Some(Expr::letE(n.clone(), t2, v2, b2?, *nd))
      },
      ExprData::Mdata(md, x, _) => {
        let x2 = self.go(fuel, ctx, x)?;
        Some(Expr::mdata(md.clone(), x2))
      },
      _ => Some(e.clone()),
    }
  }
}

impl CollapseRec<'_> {
  /// The re-typing data of a collapsed-block occurrence, for new motives
  /// (one per slot), levels and leaf re-path (`CollapseRec.retype`).
  fn retype<'l>(
    &self,
    env: &OptEnv<'_>,
    motives: Vec<Expr>,
    levels: LevelsFn<'l>,
    extra: Option<ExtraFn<'l>>,
  ) -> Option<CRetype<'l>> {
    let mut belows: FxHashMap<Name, usize> = FxHashMap::default();
    let mut leaves: FxHashMap<Name, Vec<usize>> = FxHashMap::default();
    let mut forbidden: FxHashSet<Name> = FxHashSet::default();
    for (i, m) in self.b.all.iter().enumerate() {
      belows.insert(mk_str(m, "below"), i);
      forbidden.insert(mk_str(m, "brecOn"));
      let Some(ConstantInfo::InductInfo(iv)) = env.const_of(m) else {
        return None;
      };
      for c in &iv.ctors {
        leaves.insert(c.clone(), leaf_members(env, &self.b.all, self.s.np, c)?);
      }
    }
    let ix_below: Vec<Name> = self
      .slot_rec
      .iter()
      .map(|r| ix_aux_of(r, AuxKind::Below))
      .collect::<Option<Vec<_>>>()?;
    if ix_below.iter().any(|n| !(env.resolves)(n)) {
      return None;
    }
    Some(CRetype {
      belows,
      n_args: self.s.np + self.s.nm + self.s.ni + 1,
      np: self.s.np,
      nm: self.s.nm,
      ix_below,
      slot_of: self.slot_of.clone(),
      motives,
      levels,
      leaves,
      extra,
      forbidden,
    })
  }
}

/// Re-type a handler: a constant `g` (Lean's `f._f`) becomes the canonical
/// constant `p._ix_retyped.s` (`g = p.s`) with re-typed type and value;
/// another term is re-typed in place (`CollapseRec.retypeHandler`).
fn retype_handler(
  env: &OptEnv<'_>,
  rt: &CRetype<'_>,
  h: &Expr,
) -> Option<(Expr, Vec<ConstantInfo>)> {
  let (hd, args) = get_app_fn_args(h);
  match hd.as_data() {
    ExprData::Const(g, gus, _) => {
      let Some(ConstantInfo::DefnInfo(gv)) = env.const_of(g) else {
        return None;
      };
      let ty2 = rt.go(RETYPE_FUEL, &mut Vec::new(), &gv.cnst.typ)?;
      let v2 = rt.go(RETYPE_FUEL, &mut Vec::new(), &gv.value)?;
      let g2 = retyped_name(g)?;
      let args2 = rt.go_all(RETYPE_FUEL, &mut Vec::new(), &args)?;
      let dv = retyped_def(&gv, &g2, ty2, v2);
      Some((
        mk_app_n(Expr::cnst(g2, gus.clone()), &args2),
        vec![ConstantInfo::DefnInfo(dv)],
      ))
    },
    _ => Some((rt.go(RETYPE_FUEL, &mut Vec::new(), h)?, Vec::new())),
  }
}

// ---------------------------------------------------------------------------
// O10 (`Opt/O10.lean`): structural recursion over a collapsed block with
// equal arms (the twin's single function)
// ---------------------------------------------------------------------------

/// `O10.apply`.
pub(super) fn o10(
  env: &OptEnv<'_>,
  o: &Occ<'_>,
) -> Option<(Expr, Vec<ConstantInfo>)> {
  let cr = read_collapse_rec(env, o)?;
  let s = &cr.s;
  let ren = collapse_renaming(env, cr.b);
  let addr = |n: &Name| env.canon_addr_of(n);
  // the motives agree per slot
  let mut ps2: Vec<Expr> = Vec::new();
  for cls in &s.slots {
    let rep = *cls.first()?;
    let mr = cr.ms.get(rep)?;
    for &i in cls {
      if !agree_after_compile(&ren, cr.ms.get(i)?, mr) {
        return None;
      }
    }
    ps2.push(mr.clone());
  }
  let ls = single_levels(env, s, o.us)?;
  let rt = cr.retype(
    env,
    ps2.clone(),
    Box::new(|us: &[Level]| single_levels(env, s, us)),
    None,
  )?;
  // the re-typed handlers agree per slot
  let mut hs2: Vec<Expr> = Vec::new();
  let mut canon: Vec<ConstantInfo> = Vec::new();
  for cls in &s.slots {
    let rep = *cls.first()?;
    let (hr, cr2) = retype_handler(env, &rt, cr.hs.get(rep)?)?;
    let vr = defn_value(&cr2).unwrap_or_else(|| hr.clone());
    for &i in cls {
      if i == rep {
        continue;
      }
      let (hi, ci) = retype_handler(env, &rt, cr.hs.get(i)?)?;
      let vi = defn_value(&ci).unwrap_or(hi);
      if !agree_addr(&ren, &addr, &vi, &vr) {
        return None;
      }
    }
    hs2.push(hr);
    canon.extend(cr2);
  }
  let ix_brec_on = ix_aux_of(&s.ix_rec, AuxKind::BRecOn)?;
  if !(env.resolves)(&ix_brec_on) {
    return None;
  }
  if !pj_allowed(o) {
    return None;
  }
  Some((
    mk_app_n(
      mk_const(&ix_brec_on, ls),
      &cat(&[&cr.ps, &ps2, &cr.tail, &hs2, &cr.rest]),
    ),
    canon,
  ))
}

// ---------------------------------------------------------------------------
// O12 (`Opt/O12.lean`): structural recursion over a collapsed pair with
// different arms (the shared pair-valued helper `fg`)
// ---------------------------------------------------------------------------

/// `O12.levelKey`.
fn level_key(l: &Level) -> String {
  match l.as_data() {
    LevelData::Zero(_) => "0".to_string(),
    LevelData::Succ(x, _) => format!("s({})", level_key(x)),
    LevelData::Max(a, b, _) => format!("m({},{})", level_key(a), level_key(b)),
    LevelData::Imax(a, b, _) => {
      format!("i({},{})", level_key(a), level_key(b))
    },
    LevelData::Param(n, _) => format!("p({})", n.pretty()),
    LevelData::Mvar(n, _) => format!("v({})", n.pretty()),
  }
}

/// `O12.levelHasParam`.
fn level_has_param(l: &Level) -> bool {
  match l.as_data() {
    LevelData::Succ(x, _) => level_has_param(x),
    LevelData::Max(a, b, _) | LevelData::Imax(a, b, _) => {
      level_has_param(a) || level_has_param(b)
    },
    LevelData::Param(..) | LevelData::Mvar(..) => true,
    LevelData::Zero(_) => false,
  }
}

/// A content key of a term: binder names and metadata dropped, constants by
/// compiled address (by name when not compiled) (`O12.canonKey`).
fn canon_key(addr: &dyn Fn(&Name) -> Option<Address>, e: &Expr) -> String {
  match e.as_data() {
    ExprData::Bvar(i, _) => format!("#{i}"),
    ExprData::Sort(l, _) => format!("S{}", level_key(l)),
    ExprData::Const(n, ls, _) => {
      let c = match addr(n) {
        Some(a) => a.hex(),
        None => n.pretty(),
      };
      let mut out = format!("C{c}");
      for l in ls {
        out.push('.');
        out.push_str(&level_key(l));
      }
      out
    },
    ExprData::App(f, a, _) => {
      format!("({} {})", canon_key(addr, f), canon_key(addr, a))
    },
    ExprData::Lam(_, t, b, _, _) => {
      format!("(L {} {})", canon_key(addr, t), canon_key(addr, b))
    },
    ExprData::ForallE(_, t, b, _, _) => {
      format!("(P {} {})", canon_key(addr, t), canon_key(addr, b))
    },
    ExprData::LetE(_, t, v, b, _, _) => format!(
      "(Z {} {} {})",
      canon_key(addr, t),
      canon_key(addr, v),
      canon_key(addr, b)
    ),
    ExprData::Lit(l, _) => match l {
      Literal::NatVal(n) => format!("N{n}"),
      Literal::StrVal(s) => format!("T{}:{}", s.chars().count(), s),
    },
    ExprData::Mdata(_, x, _) => canon_key(addr, x),
    ExprData::Proj(s, i, x, _) => {
      let c = match addr(s) {
        Some(a) => a.hex(),
        None => s.pretty(),
      };
      format!("(J{c}.{i} {})", canon_key(addr, x))
    },
    _ => format!("?{}", e.get_hash().to_hex()),
  }
}

/// `m t` with a lambda motive developed (`O12.applyMotive`).
fn apply_motive(m: &Expr, t: &Expr) -> Option<Expr> {
  instantiate(m, std::slice::from_ref(t)).ok()
}

/// `λ (t : T). PProd.{u,u} (m_a t) (m_b t)` for the pair order `ord`
/// (`O12`'s `pairOf`).
fn o12_pair(
  cr: &CollapseRec<'_>,
  tt: &Expr,
  u: &Level,
  ord: [usize; 2],
) -> Option<Expr> {
  let a = apply_motive(cr.ms.get(ord[0])?, &bvar(0))?;
  let b = apply_motive(cr.ms.get(ord[1])?, &bvar(0))?;
  Some(Expr::lam(
    root_name("t"),
    tt.clone(),
    mk_app_n(Expr::cnst(n_pprod(), vec![u.clone(), u.clone()]), &[a, b]),
    BinderInfo::Default,
  ))
}

/// The re-typing of `O12` for the pair order `ord` (`retypeFor`): the one
/// motive is the pair, a leaf value of member `j` is read as `.1` then the
/// pair's component of `j`.
fn o12_retype<'l>(
  env: &OptEnv<'_>,
  cr: &CollapseRec<'_>,
  tt: &Expr,
  u: &Level,
  ls: &[Level],
  ord: [usize; 2],
) -> Option<CRetype<'l>> {
  let pair = o12_pair(cr, tt, u, ord)?;
  let ls2 = ls.to_vec();
  let first = ord[0];
  cr.retype(
    env,
    vec![pair],
    Box::new(move |_| Some(ls2.clone())),
    Some(Box::new(move |j| if j == first { vec![0] } else { vec![1] })),
  )
}

/// `O12.apply`.
pub(super) fn o12(
  env: &OptEnv<'_>,
  o: &Occ<'_>,
) -> Option<(Expr, Vec<ConstantInfo>)> {
  let cr = read_collapse_rec(env, o)?;
  let s = &cr.s;
  if s.slots.len() != 1 || s.np != 0 || s.ni != 0 {
    return None;
  }
  let cls = s.slots.first()?;
  if cls.len() != 2 {
    return None;
  }
  if o.us.iter().any(level_has_param) {
    return None;
  }
  // closed motives and handlers (no variable of the site)
  let closed = |e: &Expr| loose_at_least(e, 1 << 62);
  if !(cr.ms.iter().all(closed) && cr.hs.iter().all(closed)) {
    return None;
  }
  let u = o.us.first()?.clone();
  if is_always_zero(&u) {
    return None;
  }
  let i0 = *cls.first()?;
  let i1 = *cls.get(1)?;
  // the major's type (the motives' binder)
  let ExprData::Lam(_, tt, _, _, _) = cr.ms.get(i0)?.as_data() else {
    return None;
  };
  let tt = tt.clone();
  let ls: Vec<Level> =
    s.ix_levels.iter().map(|l| subst_level(&s.level_params, o.us, l)).collect();
  let ix_brec_on = ix_aux_of(&s.ix_rec, AuxKind::BRecOn)?;
  if !(env.resolves)(&ix_brec_on) {
    return None;
  }
  let addr = |n: &Name| env.canon_addr_of(n);
  // the content order: each handler re-typed with its own component first
  let key_of = |i: usize, other: usize| -> Option<String> {
    let rt = o12_retype(env, &cr, &tt, &u, &ls, [i, other])?;
    let (h, cs) = retype_handler(env, &rt, cr.hs.get(i)?)?;
    let v = defn_value(&cs).unwrap_or(h);
    Some(canon_key(&addr, &v))
  };
  let k0 = key_of(i0, i1)?;
  let k1 = key_of(i1, i0)?;
  let ord: [usize; 2] = if k1 < k0 { [i1, i0] } else { [i0, i1] };
  let pair = o12_pair(&cr, &tt, &u, ord)?;
  let rt = o12_retype(env, &cr, &tt, &u, &ls, ord)?;
  let (f0, c0) = retype_handler(env, &rt, cr.hs.get(ord[0])?)?;
  let (f1, c1) = retype_handler(env, &rt, cr.hs.get(ord[1])?)?;
  let ExprData::Const(g0, _, _) = cr.hs.get(ord[0])?.as_data() else {
    return None;
  };
  let NameData::Str(gp, _, _) = g0.as_data() else { return None };
  let fg_name = mk_str(&mk_str(gp, IX_COMPONENT), "fg");
  // G := λ (t : X) (f : ρ.below Pair t). ⟨F′₀ t f, F′₁ t f⟩
  let ix_below = ix_aux_of(&s.ix_rec, AuxKind::Below)?;
  let below_t =
    mk_app_n(Expr::cnst(ix_below, ls.clone()), &[pair.clone(), bvar(0)]);
  let m0t = apply_motive(cr.ms.get(ord[0])?, &bvar(1))?;
  let m1t = apply_motive(cr.ms.get(ord[1])?, &bvar(1))?;
  let uu = vec![u.clone(), u.clone()];
  let g_body = mk_app_n(
    Expr::cnst(n_pprod_mk(), uu.clone()),
    &[
      m0t,
      m1t,
      mk_app_n(f0, &[bvar(1), bvar(0)]),
      mk_app_n(f1, &[bvar(1), bvar(0)]),
    ],
  );
  let g = Expr::lam(
    root_name("t"),
    tt.clone(),
    Expr::lam(root_name("f"), below_t, g_body, BinderInfo::Default),
    BinderInfo::Default,
  );
  let fg_value = Expr::lam(
    root_name("t"),
    tt.clone(),
    mk_app_n(Expr::cnst(ix_brec_on, ls.clone()), &[pair, bvar(0), g]),
    BinderInfo::Default,
  );
  let a0 = apply_motive(cr.ms.get(ord[0])?, &bvar(0))?;
  let a1 = apply_motive(cr.ms.get(ord[1])?, &bvar(0))?;
  let fg_type = Expr::all(
    root_name("t"),
    tt.clone(),
    mk_app_n(Expr::cnst(n_pprod(), uu), &[a0, a1]),
    BinderInfo::Default,
  );
  let fg = DefinitionVal {
    cnst: ConstantVal {
      name: fg_name.clone(),
      level_params: Vec::new(),
      typ: fg_type,
    },
    value: fg_value,
    hints: ReducibilityHints::Abbrev,
    safety: DefinitionSafety::Safe,
    all: vec![fg_name.clone()],
  };
  let xi = cr.b.all.iter().position(|m| *m == cr.x)?;
  let pos = if xi == ord[0] { 0 } else { 1 };
  if !pj_allowed(o) {
    return None;
  }
  let out = mk_app_n(
    Expr::proj(
      n_pprod(),
      nat(pos),
      Expr::app(Expr::cnst(fg_name, Vec::new()), cr.tail.first()?.clone()),
    ),
    &cr.rest,
  );
  let mut cs = c0;
  cs.extend(c1);
  cs.push(ConstantInfo::DefnInfo(fg));
  Some((out, cs))
}

// ---------------------------------------------------------------------------
// O11b (`Opt/O11b.lean`): `noConfusion` of a split-off member in
// enumeration form (a unit pass, `Driver.unitPasses`)
// ---------------------------------------------------------------------------

/// The sort level of an inductive's type (`O11b.sortOfType`).
fn sort_of_type(e: &Expr) -> Option<Level> {
  match e.as_data() {
    ExprData::ForallE(_, _, b, _, _) | ExprData::Mdata(_, b, _) => {
      sort_of_type(b)
    },
    ExprData::Sort(l, _) => Some(l.clone()),
    _ => None,
  }
}

/// `T.noConfusionType` or `T.noConfusion`: `(T, isType)`
/// (`O11b.noConfusionOf`).
pub fn no_confusion_of(n: &Name) -> Option<(Name, bool)> {
  match as_str(n)? {
    (t, "noConfusionType") => Some((t.clone(), true)),
    (t, "noConfusion") => Some((t.clone(), false)),
    _ => None,
  }
}

/// `T` is an enumeration in Lean's sense, with its constructor count
/// (`O11b.enumCtors`).
fn enum_ctors(
  const_of: &dyn Fn(&Name) -> Option<ConstantInfo>,
  t: &Name,
) -> Option<(InductiveVal, usize)> {
  let Some(ConstantInfo::InductInfo(iv)) = const_of(t) else { return None };
  if nat_usize(&iv.num_params) != 0
    || nat_usize(&iv.num_indices) != 0
    || iv.ctors.is_empty()
    || iv.is_unsafe
  {
    return None;
  }
  let l = sort_of_type(&iv.cnst.typ)?;
  if l == Level::zero() {
    return None;
  }
  for c in &iv.ctors {
    let Some(ConstantInfo::CtorInfo(cv)) = const_of(c) else { return None };
    if nat_usize(&cv.num_fields) != 0 {
      return None;
    }
  }
  let n = iv.ctors.len();
  Some((iv, n))
}

/// The enumeration form of `T`'s two constants (one constructor), at the
/// motive universe `v` and `T`'s universe arguments `us`
/// (`O11b.enumForm`).
fn enum_form(
  iv: &InductiveVal,
  v: &Level,
  us: &[Level],
  is_type: bool,
) -> Option<Expr> {
  let l = sort_of_type(&iv.cnst.typ)?;
  let l = subst_level(&iv.cnst.level_params, us, &l);
  let t_c = Expr::cnst(iv.cnst.name.clone(), us.to_vec());
  let nm = root_name;
  let sort_v = Expr::sort(v.clone());
  use BinderInfo::{Default as D, Implicit as I};
  if is_type {
    // λ (P : Sort v) (x y : T). P → P
    Some(Expr::lam(
      nm("P"),
      sort_v,
      Expr::lam(
        nm("x"),
        t_c.clone(),
        Expr::lam(nm("y"), t_c, Expr::all(nm("a"), bvar(2), bvar(3), D), D),
        D,
      ),
      D,
    ))
  } else {
    // λ {P : Sort v} {x y : T} (h : @Eq.{l} T x y) (p : P). p
    let eq_ty = mk_app_n(
      Expr::cnst(root_name("Eq"), vec![l]),
      &[t_c.clone(), bvar(1), bvar(0)],
    );
    Some(Expr::lam(
      nm("P"),
      sort_v,
      Expr::lam(
        nm("x"),
        t_c.clone(),
        Expr::lam(
          nm("y"),
          t_c,
          Expr::lam(nm("h"), eq_ty, Expr::lam(nm("p"), bvar(3), bvar(0), D), D),
          I,
        ),
        I,
      ),
      I,
    ))
  }
}

/// Whether O11b rewrites the pair of `T` (the same decision at both
/// constants, `O11b.pairApplies`).
fn o11b_pair_applies(
  const_of: &dyn Fn(&Name) -> Option<ConstantInfo>,
  classes_of: &dyn Fn(&Name) -> Option<Vec<Vec<Name>>>,
  t: &Name,
) -> bool {
  (|| -> Option<()> {
    let Some(ConstantInfo::InductInfo(iv0)) = const_of(t) else { return None };
    if iv0.all.len() < 2 {
      return None;
    }
    let classes = classes_of(t)?;
    if classes.len() != 1 {
      return None;
    }
    let (_, n) = enum_ctors(const_of, t)?;
    if n != 1 {
      return None;
    }
    Some(())
  })()
  .is_some()
}

/// The rewritten value of one of the pair, when O11b applies to it
/// (`O11b.rewrite`).
pub fn o11b_rewrite(
  const_of: &dyn Fn(&Name) -> Option<ConstantInfo>,
  classes_of: &dyn Fn(&Name) -> Option<Vec<Vec<Name>>>,
  n: &Name,
  ci: &ConstantInfo,
) -> Option<DefinitionVal> {
  let (t, is_type) = no_confusion_of(n)?;
  let ConstantInfo::DefnInfo(dv) = ci else { return None };
  if !o11b_pair_applies(const_of, classes_of, &t) {
    return None;
  }
  let v = dv.cnst.level_params.first()?;
  if forall_arity(&dv.cnst.typ) != if is_type { 3 } else { 4 } {
    return None;
  }
  let (iv, _) = enum_ctors(const_of, &t)?;
  if dv.cnst.level_params.len() != iv.cnst.level_params.len() + 1 {
    return None;
  }
  let us: Vec<Level> =
    dv.cnst.level_params[1..].iter().map(|p| Level::param(p.clone())).collect();
  let value = enum_form(&iv, &Level::param(v.clone()), &us, is_type)?;
  Some(DefinitionVal { value, ..dv.clone() })
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::compile::pass3::expr::dotted;

  fn leaf_map(map: Vec<Option<usize>>) -> LeafMap {
    let ix_leaves = map.iter().filter(|x| x.is_some()).count();
    LeafMap { map, ix_leaves }
  }

  #[test]
  fn repath_selects_the_component_leaf() {
    // Lean's leaves [own, cross, own]; Ix leaves [own, own]
    let lm = leaf_map(vec![Some(0), None, Some(1)]);
    // leaf 0: `.1.1` (innermost first: [0, 0])
    assert_eq!(repath(&lm, &[0, 0]), Some((vec![0, 0], 0)));
    // the last leaf: `.2.2.1` then a copied `.1`
    assert_eq!(repath(&lm, &[1, 1, 0, 0]), Some((vec![1, 0], 1)));
    // the cross leaf has no Ix leaf: declined
    assert_eq!(repath(&lm, &[1, 0, 0]), None);
    // the whole below value of a leaf (no `.1`): declined
    assert_eq!(repath(&lm, &[1]), None);
  }

  #[test]
  fn crepath_appends_the_pair_component() {
    let extra = |i: usize| if i == 0 { vec![0] } else { vec![1] };
    // leaves of members [0, 1]: the second leaf's value, `.2.1` (last leaf),
    // then the pair's second component
    assert_eq!(crepath(&[0, 1], &extra, &[1, 0]), Some((vec![1, 0, 1], 0)));
    assert_eq!(crepath(&[0, 1], &extra, &[0, 0]), Some((vec![0, 0, 0], 0)));
    assert_eq!(crepath(&[], &extra, &[0]), None);
  }

  #[test]
  fn canon_key_drops_binder_names() {
    let a = dotted("A");
    let ty = Expr::cnst(a.clone(), vec![]);
    let l1 =
      Expr::lam(root_name("x"), ty.clone(), bvar(0), BinderInfo::Default);
    let l2 = Expr::lam(root_name("y"), ty, bvar(0), BinderInfo::Implicit);
    let none = |_: &Name| None;
    assert_eq!(canon_key(&none, &l1), canon_key(&none, &l2));
    assert_eq!(canon_key(&none, &l1), "(L CA #0)");
  }

  #[test]
  fn noconfusion_names() {
    assert_eq!(
      no_confusion_of(&dotted("T.noConfusionType")),
      Some((dotted("T"), true))
    );
    assert_eq!(
      no_confusion_of(&dotted("T.noConfusion")),
      Some((dotted("T"), false))
    );
    assert_eq!(no_confusion_of(&dotted("T.casesOn")), None);
  }
}
