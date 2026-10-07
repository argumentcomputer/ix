//! The definitional passes O1-O6 and O11a (M6R slice 2), at every full
//! application of an image-kind head, before the call-site rewrite inlines
//! the image (`Translate.RwState.opt?`). A port of
//! `Ix/Compile/Pass/Opt/{Core,Engine,O1,O2,O3,O4,O5,O6,O11a}.lean`; the
//! Lean modules are the specification of each pass (contract, faithfulness,
//! side condition), cited per function. The engine runs the proof-justified
//! passes after them (`pjPasses`: O8, O7; `emitPasses`: O9, O10, O12; slice
//! 4, [`super::pj`]), whose output goes to the canonical `_ix` form of the
//! site only (D1, `Translate.RwState.inPlace`).
//!
//! The scheduling edges O11a's output needs (`O11a.sizeOfEdges`) are
//! [`size_of_edges`]; the recorded declines (`O11a.declineCause?`) are
//! [`o11a_decline_cause`].

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::address::Address;
use ix_common::env::{
  ConstantInfo, Env as LeanEnv, Expr, ExprData, Level, LevelData, Name,
  NameData, RecursorVal,
};

use crate::compile::aux_gen::expr_utils::{
  LocalDecl, fresh_fvar, instantiate1, mk_lambda,
};
use crate::compile::surgery::{
  SourceRecTarget, aux_motive_sigs, find_source_rec_target, peel_binders,
  source_ctor_for_minor, source_minor_type,
};

use super::expr::{
  alpha_eq, dotted, get_app_fn_args, mk_app_n, mk_str, nat_usize, subst_level,
  used_constants,
};
use super::spec::BlockChange;

// ---------------------------------------------------------------------------
// Core (`Opt/Core.lean`)
// ---------------------------------------------------------------------------

/// An occurrence of an image-kind auxiliary: `head.{us} args`, the arguments
/// already in normal form (`Opt.Occ`).
pub struct Occ<'a> {
  pub head: &'a Name,
  pub us: &'a [Level],
  pub args: &'a [Expr],
  /// The definition whose value contains the occurrence, when the
  /// proof-justified passes (O7-O12) may fire there
  /// (`Translate.RwState.site`); their output goes to the definition's
  /// canonical `_ix` form only (D1).
  pub site: Option<&'a Name>,
}

/// The kinds of image-kind auxiliaries (`Opt.AuxKind`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AuxKind {
  Rec,
  RecOn,
  CasesOn,
  Below,
  BRecOn,
  Go,
  Eq,
}

/// `s` is `kind` or `kind_j` (`j >= 1`) (`Opt.suffixIdx?`).
// the Lean original's `Option (Option Nat)`: not a suffix, the bare kind, `_j`
#[allow(clippy::option_option)]
pub(super) fn suffix_idx(kind: &str, s: &str) -> Option<Option<usize>> {
  if s == kind {
    return Some(None);
  }
  let rest = s.strip_prefix(kind)?.strip_prefix('_')?;
  if rest.is_empty() || !rest.chars().all(|c| c.is_ascii_digit()) {
    return None;
  }
  let j: usize = rest.parse().ok()?;
  if j >= 1 { Some(Some(j)) } else { None }
}

/// `x.rec` or `x.rec_j` (`Opt.recNameOf`).
pub(super) fn rec_name_of(x: &Name, j: Option<usize>) -> Name {
  match j {
    None => mk_str(x, "rec"),
    Some(j) => mk_str(x, &format!("rec_{j}")),
  }
}

pub(super) fn as_str(n: &Name) -> Option<(&Name, &str)> {
  match n.as_data() {
    NameData::Str(p, s, _) => Some((p, s.as_str())),
    _ => None,
  }
}

/// Classify a Lean auxiliary name: its kind and the Lean recursor it is
/// built from (`Opt.classify`).
pub fn classify(n: &Name) -> Option<(AuxKind, Name)> {
  let (p, s) = as_str(n)?;
  if let Some(j) = suffix_idx("rec", s) {
    return Some((AuxKind::Rec, rec_name_of(p, j)));
  }
  if s == "recOn" {
    return Some((AuxKind::RecOn, rec_name_of(p, None)));
  }
  if s == "casesOn" {
    return Some((AuxKind::CasesOn, rec_name_of(p, None)));
  }
  if let Some(j) = suffix_idx("below", s) {
    return Some((AuxKind::Below, rec_name_of(p, j)));
  }
  if let Some(j) = suffix_idx("brecOn", s) {
    return Some((AuxKind::BRecOn, rec_name_of(p, j)));
  }
  if s == "go" || s == "eq" {
    let (x, t) = as_str(p)?;
    let j = suffix_idx("brecOn", t)?;
    let k = if s == "go" { AuxKind::Go } else { AuxKind::Eq };
    return Some((k, rec_name_of(x, j)));
  }
  None
}

/// The Ix auxiliary of kind `k` next to the Ix recursor `rho`, by the
/// reserved display names (`Opt.ixAuxOf`).
pub fn ix_aux_of(rho: &Name, k: AuxKind) -> Option<Name> {
  let (p, s) = as_str(rho)?;
  let j = suffix_idx("rec", s)?;
  let sfx = |base: &str| match j {
    None => base.to_string(),
    Some(j) => format!("{base}_{j}"),
  };
  match (k, j) {
    (AuxKind::Rec, _) => Some(rho.clone()),
    (AuxKind::RecOn, None) => Some(mk_str(p, "recOn")),
    (AuxKind::CasesOn, None) => Some(mk_str(p, "casesOn")),
    (AuxKind::RecOn | AuxKind::CasesOn, Some(_)) => None,
    (AuxKind::Below, _) => Some(mk_str(p, &sfx("below"))),
    (AuxKind::BRecOn, _) => Some(mk_str(p, &sfx("brecOn"))),
    (AuxKind::Go, _) => Some(mk_str(&mk_str(p, &sfx("brecOn")), "go")),
    (AuxKind::Eq, _) => Some(mk_str(&mk_str(p, &sfx("brecOn")), "eq")),
  }
}

/// The shape of a generated image (`Opt.RecShape`).
#[derive(Clone, Debug)]
pub struct RecShape {
  pub level_params: Vec<Name>,
  pub np: usize,
  pub nm: usize,
  pub nmin: usize,
  pub ni: usize,
  pub ix_rec: Name,
  pub ix_levels: Vec<Level>,
  /// Ix motive `k` is Lean motive `motive_src[k]`.
  pub motive_src: Vec<usize>,
  /// Ix minor `k` is Lean minor `j` (`Some j`), or another term (`None`).
  pub minor_src: Vec<Option<usize>>,
  pub minor_terms: Vec<Expr>,
}

impl RecShape {
  pub(super) fn arity(&self) -> usize {
    self.np + self.nm + self.nmin + self.ni + 1
  }

  /// `RecShape.isPerm`.
  fn is_perm(&self) -> bool {
    self.motive_src.len() == self.nm
      && self.minor_src.len() == self.nmin
      && self.minor_src.iter().all(Option::is_some)
      && (0..self.nm).all(|i| self.motive_src.contains(&i))
      && (0..self.nmin).all(|j| self.minor_src.contains(&Some(j)))
  }

  /// `RecShape.isSelection`.
  pub(super) fn is_selection(&self) -> bool {
    self.minor_src.iter().all(Option::is_some)
  }

  /// `RecShape.levelsAt`.
  fn levels_at(&self, us: &[Level]) -> Vec<Level> {
    self
      .ix_levels
      .iter()
      .map(|l| subst_level(&self.level_params, us, l))
      .collect()
  }

  fn minor_src_ids(&self) -> Vec<usize> {
    self.minor_src.iter().filter_map(|x| *x).collect()
  }
}

/// Strip `n` leading lambdas (`Opt.stripLams`).
pub(super) fn strip_lams(n: usize, e: &Expr) -> Option<Expr> {
  let mut cur = e.clone();
  for _ in 0..n {
    let next = match cur.as_data() {
      ExprData::Lam(_, _, b, _, _) => b.clone(),
      _ => return None,
    };
    cur = next;
  }
  Some(cur)
}

/// Read the shape off an image (`Opt.readShape`).
#[allow(clippy::too_many_arguments)]
pub fn read_shape(
  level_params: &[Name],
  np: usize,
  nm: usize,
  nmin: usize,
  ni: usize,
  value: &Expr,
  ix_rec_info: &dyn Fn(&Name) -> Option<RecursorVal>,
) -> Option<RecShape> {
  let arity = np + nm + nmin + ni + 1;
  let body = strip_lams(arity, value)?;
  let (h, args) = get_app_fn_args(&body);
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
  let mut motive_src = Vec::new();
  for k in 0..inm {
    let p = pos(&args[np + k])?;
    if p < np || p >= np + nm || motive_src.contains(&(p - np)) {
      return None;
    }
    motive_src.push(p - np);
  }
  let mut minor_src = Vec::new();
  let mut minor_terms = Vec::new();
  for k in 0..inmin {
    let a = &args[np + inm + k];
    minor_terms.push(a.clone());
    match pos(a) {
      Some(p) => {
        if p < np + nm
          || p >= np + nm + nmin
          || minor_src.contains(&Some(p - np - nm))
        {
          return None;
        }
        minor_src.push(Some(p - np - nm));
      },
      None => minor_src.push(None),
    }
  }
  Some(RecShape {
    level_params: level_params.to_vec(),
    np,
    nm,
    nmin,
    ni,
    ix_rec: rho.clone(),
    ix_levels: ls.clone(),
    motive_src,
    minor_src,
    minor_terms,
  })
}

/// The data of one changed Lean block the passes read (`Opt.OptBlock`).
pub struct OptBlock {
  pub all: Vec<Name>,
  pub change: BlockChange,
  pub class_of: FxHashMap<Name, Vec<Name>>,
  pub shapes: FxHashMap<Name, RecShape>,
  /// The generated images of the block's Lean recursors (those that built):
  /// their universe parameters and values, read by the proof-justified
  /// passes over collapsed blocks, whose images are packed (`Opt.Packed`).
  pub images: FxHashMap<Name, (Vec<Name>, Expr)>,
  /// The Ix recursors of the block's canonical components (view names, as
  /// the images name them).
  pub ix_recs: FxHashMap<Name, RecursorVal>,
}

/// What the passes read of the compiler (`Opt.OptEnv`).
pub struct OptEnv<'a> {
  /// The input environment.
  pub ienv: &'a LeanEnv,
  /// A name of `E` resolves to an address.
  pub resolves: &'a dyn Fn(&Name) -> bool,
  /// The block of a Lean image-kind head, when it is a changed block's.
  pub block_of: &'a dyn Fn(&Name) -> Option<&'a OptBlock>,
  /// The address of a name of `E`, when it resolves (the proof-justified
  /// passes compare compiled references, `Opt.CollapseRec.agreeAddr`);
  /// `None` gives Lean's default (`fun _ => none`).
  pub addr_of: Option<&'a dyn Fn(&Name) -> Option<Address>>,
  /// The canonical `_ix` form of a compiled dependency, when it has one
  /// (`OptEnv.ixForm?`, `Driver.ixFormOf`); `None` gives Lean's default.
  pub ix_form: Option<&'a dyn Fn(&Name) -> Option<Name>>,
}

impl OptEnv<'_> {
  pub(super) fn const_of(&self, n: &Name) -> Option<ConstantInfo> {
    self.ienv.get(n).map(|e| e.cloned())
  }

  /// `OptEnv.addrOf`.
  pub(super) fn addr_of(&self, n: &Name) -> Option<Address> {
    self.addr_of.and_then(|f| f(n))
  }

  /// The compiled address of a name's canonical form: its `_ix` form when
  /// it has one (D1), the name itself otherwise (`OptEnv.canonAddrOf`).
  pub(super) fn canon_addr_of(&self, n: &Name) -> Option<Address> {
    let m = self.ix_form.and_then(|f| f(n)).unwrap_or_else(|| n.clone());
    self.addr_of(&m)
  }
}

/// `Opt.pick`.
pub(super) fn pick(xs: &[Expr], src: &[usize]) -> Option<Vec<Expr>> {
  src.iter().map(|i| xs.get(*i).cloned()).collect()
}

/// `Opt.forallArity`.
pub(super) fn forall_arity(e: &Expr) -> usize {
  match e.as_data() {
    ExprData::ForallE(_, _, b, _, _) => forall_arity(b) + 1,
    ExprData::Mdata(_, b, _) => forall_arity(b),
    _ => 0,
  }
}

/// `Opt.standardTelescope`.
pub(super) fn standard_telescope(
  env: &OptEnv<'_>,
  s: &RecShape,
  k: AuxKind,
  a: &Name,
  nctors: usize,
) -> Option<usize> {
  let ci = env.const_of(a)?;
  if *ci.get_level_params() != s.level_params {
    return None;
  }
  let n = match k {
    AuxKind::Rec | AuxKind::RecOn => s.np + s.nm + s.nmin + s.ni + 1,
    AuxKind::CasesOn => s.np + 1 + s.ni + 1 + nctors,
    AuxKind::Below => s.np + s.nm + s.ni + 1,
    AuxKind::BRecOn | AuxKind::Go | AuxKind::Eq => {
      s.np + s.nm + s.ni + 1 + s.nm
    },
  };
  if forall_arity(ci.get_type()) != n {
    return None;
  }
  Some(n)
}

pub(super) fn mk_const(n: &Name, ls: Vec<Level>) -> Expr {
  Expr::cnst(n.clone(), ls)
}

pub(super) fn cat(parts: &[&[Expr]]) -> Vec<Expr> {
  parts.iter().flat_map(|p| p.iter().cloned()).collect()
}

// ---------------------------------------------------------------------------
// O5 (`Opt/O5.lean`): the level rule
// ---------------------------------------------------------------------------

/// `O5.levels`.
pub(super) fn o5_levels(s: &RecShape, us: &[Level]) -> Option<Vec<Level>> {
  if s.ix_levels.len() == s.level_params.len() {
    Some(s.levels_at(us))
  } else if s.ix_levels.len() == s.level_params.len() + 1 {
    match s.ix_levels.first().map(|l| l.as_data()) {
      Some(LevelData::Zero(_)) => Some(s.levels_at(us)),
      _ => None,
    }
  } else {
    None
  }
}

// ---------------------------------------------------------------------------
// O1 (`Opt/O1.lean`)
// ---------------------------------------------------------------------------

/// `Opt.permutationOnly`.
fn permutation_only(c: &BlockChange) -> bool {
  !c.split && !c.collapse && !c.evaporation
}

/// `O1.apply`.
fn o1(env: &OptEnv<'_>, o: &Occ<'_>) -> Option<Expr> {
  let (k, r) = classify(o.head)?;
  if k != AuxKind::Rec && k != AuxKind::RecOn {
    return None;
  }
  let b = (env.block_of)(o.head)?;
  if !permutation_only(&b.change) {
    return None;
  }
  let s = b.shapes.get(&r)?;
  if !s.is_perm() {
    return None;
  }
  let n = standard_telescope(env, s, k, o.head, 0)?;
  if o.args.len() < n {
    return None;
  }
  let ls = o5_levels(s, o.us)?;
  let a = o.args;
  let ps = &a[..s.np];
  let extra = &a[n..];
  if k == AuxKind::Rec {
    let ms = &a[s.np..s.np + s.nm];
    let mins = &a[s.np + s.nm..s.np + s.nm + s.nmin];
    let tail = &a[s.np + s.nm + s.nmin..n];
    let ms2 = pick(ms, &s.motive_src)?;
    let mins2 = pick(mins, &s.minor_src_ids())?;
    Some(mk_app_n(
      mk_const(&s.ix_rec, ls),
      &cat(&[ps, &ms2, &mins2, tail, extra]),
    ))
  } else {
    let ix_rec_on = ix_aux_of(&s.ix_rec, AuxKind::RecOn)?;
    if !(env.resolves)(&ix_rec_on) {
      return None;
    }
    let ms = &a[s.np..s.np + s.nm];
    let tail = &a[s.np + s.nm..s.np + s.nm + s.ni + 1];
    let mins = &a[s.np + s.nm + s.ni + 1..n];
    let ms2 = pick(ms, &s.motive_src)?;
    let mins2 = pick(mins, &s.minor_src_ids())?;
    Some(mk_app_n(
      mk_const(&ix_rec_on, ls),
      &cat(&[ps, &ms2, tail, &mins2, extra]),
    ))
  }
}

// ---------------------------------------------------------------------------
// O2 (`Opt/O2.lean`)
// ---------------------------------------------------------------------------

/// Strip leading lambdas, counting them (`Opt.stripLamsCount`).
fn strip_lams_count(e: &Expr) -> (Expr, usize) {
  let mut cur = e.clone();
  let mut d = 0;
  while let ExprData::Lam(_, _, b, _, _) = cur.as_data() {
    let b = b.clone();
    cur = b;
    d += 1;
  }
  (cur, d)
}

/// The Lean minor a wrapped Ix minor is built from (`Opt.wrappedMinorSrc`).
fn wrapped_minor_src(
  arity: usize,
  np: usize,
  nm: usize,
  nmin: usize,
  t: &Expr,
) -> Option<usize> {
  let (body, d) = strip_lams_count(t);
  let (h, _) = get_app_fn_args(&body);
  let ExprData::Bvar(k, _) = h.as_data() else { return None };
  let k = nat_usize(k);
  if k < d {
    return None;
  }
  let j = k - d;
  if j >= arity {
    return None;
  }
  let p = arity - 1 - j;
  if p < np + nm || p >= np + nm + nmin {
    return None;
  }
  Some(p - np - nm)
}

/// The occurrence passes' recursion (`engineN`'s `recur`).
type Recur<'r> = &'r dyn Fn(&Occ<'_>) -> Option<Expr>;

/// `Opt.relocatedIh`.
#[allow(clippy::too_many_arguments)]
fn relocated_ih(
  recur: Recur<'_>,
  target: &SourceRecTarget,
  field: &Expr,
  all: &[Name],
  us: &[Level],
  ps: &[Expr],
  ms: &[Expr],
  mins: &[Expr],
) -> Option<Expr> {
  let all0 = all.first()?;
  let target_rec = match all.get(target.source_pos) {
    Some(x) => mk_str(x, "rec"),
    None => mk_str(all0, &format!("rec_{}", target.source_pos - all.len() + 1)),
  };
  let field_app =
    target.xs_fvars.iter().fold(field.clone(), |f, x| Expr::app(f, x.clone()));
  let mut args = cat(&[ps, ms, mins, &target.idx_args]);
  args.push(field_app);
  let inner = recur(&Occ { head: &target_rec, us, args: &args, site: None })?;
  Some(mk_lambda(inner, &target.xs_decls))
}

/// The recursive fields of a minor's constructor: `(field index, target)`.
fn rec_fields_of(
  env: &LeanEnv,
  rv: &RecursorVal,
  field_decls: &[LocalDecl],
  ps: &[Expr],
  aux_sigs: &[crate::compile::surgery::AuxMotiveSig],
) -> Vec<(usize, SourceRecTarget)> {
  let mut out = Vec::new();
  for (field_idx, decl) in field_decls.iter().enumerate() {
    if let Some(t) = find_source_rec_target(
      &decl.domain,
      &rv.all,
      ps,
      env,
      "split_xs",
      field_idx,
      aux_sigs,
    ) {
      out.push((field_idx, t));
    }
  }
  out
}

/// `Opt.adaptMinor`: `Some(Some w)` the wrapper, `Some(None)` no field into
/// another component, `None` failure.
#[allow(clippy::too_many_arguments, clippy::option_option)]
fn adapt_minor(
  recur: Recur<'_>,
  env: &LeanEnv,
  rv: &RecursorVal,
  in_block: &[bool],
  us: &[Level],
  ps: &[Expr],
  ms: &[Expr],
  mins: &[Expr],
  j: usize,
) -> Option<Option<Expr>> {
  let aux_sigs = aux_motive_sigs(rv, us, ps, ms, env);
  let (_, ctor) = source_ctor_for_minor(j, rv, env, &aux_sigs)?;
  let minor_ty = source_minor_type(rv, us, ps, ms, mins, j)?;
  let (field_decls, field_fvars, after_fields) =
    peel_binders(minor_ty, nat_usize(&ctor.num_fields), "split_field", 0)?;
  let rec_fields = rec_fields_of(env, rv, &field_decls, ps, &aux_sigs);
  let inb = |p: usize| in_block.get(p).copied().unwrap_or(false);
  if !rec_fields.iter().any(|(_, t)| !inb(t.source_pos)) {
    return Some(None);
  }
  let (ih_decls, ih_fvars, _) =
    peel_binders(after_fields, rec_fields.len(), "split_ih", 0)?;
  if ih_decls.len() != rec_fields.len() {
    return None;
  }
  let mut decls = field_decls;
  let m = mins.get(j)?;
  let mut body =
    field_fvars.iter().fold(m.clone(), |f, x| Expr::app(f, x.clone()));
  for (ih_idx, (field_idx, target)) in rec_fields.iter().enumerate() {
    if inb(target.source_pos) {
      decls.push(ih_decls[ih_idx].clone());
      body = Expr::app(body, ih_fvars[ih_idx].clone());
    } else {
      let ih = relocated_ih(
        recur,
        target,
        &field_fvars[*field_idx],
        &rv.all,
        us,
        ps,
        ms,
        mins,
      )?;
      body = Expr::app(body, ih);
    }
  }
  Some(Some(mk_lambda(body, &decls)))
}

/// `O2.apply`.
fn o2(recur: Recur<'_>, env: &OptEnv<'_>, o: &Occ<'_>) -> Option<Expr> {
  let (k, r) = classify(o.head)?;
  if k != AuxKind::Rec {
    return None;
  }
  let b = (env.block_of)(o.head)?;
  if !b.change.split || b.change.collapse {
    return None;
  }
  let s = b.shapes.get(&r)?;
  let Some(ConstantInfo::RecInfo(rv)) = env.const_of(&r) else { return None };
  let n = standard_telescope(env, s, AuxKind::Rec, o.head, 0)?;
  if o.args.len() < n {
    return None;
  }
  let ls = o5_levels(s, o.us)?;
  let a = o.args;
  let ps = &a[..s.np];
  let ms = &a[s.np..s.np + s.nm];
  let mins = &a[s.np + s.nm..s.np + s.nm + s.nmin];
  let tail = &a[s.np + s.nm + s.nmin..n];
  let in_block: Vec<bool> =
    (0..s.nm).map(|i| s.motive_src.contains(&i)).collect();
  let ms2 = pick(ms, &s.motive_src)?;
  let mut mins2 = Vec::new();
  for (src, t) in s.minor_src.iter().zip(s.minor_terms.iter()) {
    let j = match src {
      Some(j) => *j,
      None => wrapped_minor_src(s.arity(), s.np, s.nm, s.nmin, t)?,
    };
    match adapt_minor(recur, env.ienv, &rv, &in_block, o.us, ps, ms, mins, j)? {
      Some(w) => {
        if src.is_some() {
          return None;
        }
        mins2.push(w);
      },
      None => mins2.push(mins.get(j)?.clone()),
    }
  }
  Some(mk_app_n(
    mk_const(&s.ix_rec, ls),
    &cat(&[ps, &ms2, &mins2, tail, &a[n..]]),
  ))
}

// ---------------------------------------------------------------------------
// O3 (`Opt/O3.lean`)
// ---------------------------------------------------------------------------

/// `O3.apply`.
fn o3(env: &OptEnv<'_>, o: &Occ<'_>) -> Option<Expr> {
  let (k, r) = classify(o.head)?;
  if k != AuxKind::CasesOn {
    return None;
  }
  let (x, s0) = as_str(o.head)?;
  if s0 != "casesOn" {
    return None;
  }
  let b = (env.block_of)(o.head)?;
  if b.change.collapse {
    return None;
  }
  let cls = b.class_of.get(x)?;
  if cls.len() != 1 {
    return None;
  }
  let s = b.shapes.get(&r)?;
  let Some(ConstantInfo::InductInfo(iv)) = env.const_of(x) else {
    return None;
  };
  let n = standard_telescope(env, s, AuxKind::CasesOn, o.head, iv.ctors.len())?;
  if o.args.len() < n {
    return None;
  }
  let ls = o5_levels(s, o.us)?;
  let ix_cases = ix_aux_of(&s.ix_rec, AuxKind::CasesOn)?;
  if !(env.resolves)(&ix_cases) {
    return None;
  }
  Some(mk_app_n(mk_const(&ix_cases, ls), o.args))
}

// ---------------------------------------------------------------------------
// O4 (`Opt/O4.lean`)
// ---------------------------------------------------------------------------

/// `x.rec ↦ x.below`, `all0.rec_j ↦ all0.below_j` (`Opt.belowNameOf`).
pub(super) fn below_name_of(n: &Name) -> Name {
  match as_str(n) {
    Some((p, s)) => {
      mk_str(p, &format!("below{}", s.get(3..).unwrap_or_default()))
    },
    None => n.clone(),
  }
}

/// `O4.apply`.
fn o4(env: &OptEnv<'_>, o: &Occ<'_>) -> Option<Expr> {
  let (k, r) = classify(o.head)?;
  if !matches!(k, AuxKind::Below | AuxKind::BRecOn | AuxKind::Go | AuxKind::Eq)
  {
    return None;
  }
  let b = (env.block_of)(o.head)?;
  if b.change.collapse {
    return None;
  }
  let s = b.shapes.get(&r)?;
  if !s.is_selection() {
    return None;
  }
  let n = standard_telescope(env, s, k, o.head, 0)?;
  if o.args.len() < n {
    return None;
  }
  let ls = o5_levels(s, o.us)?;
  let ix_a = ix_aux_of(&s.ix_rec, k)?;
  if !(env.resolves)(&ix_a) {
    return None;
  }
  if k != AuxKind::Below
    && !matches!(
      env.const_of(&below_name_of(&r)),
      Some(ConstantInfo::DefnInfo(_))
    )
  {
    return None;
  }
  let a = o.args;
  let ps = &a[..s.np];
  let ms = pick(&a[s.np..s.np + s.nm], &s.motive_src)?;
  let tail = &a[s.np + s.nm..s.np + s.nm + s.ni + 1];
  let rest = &a[n..];
  let hs = if k == AuxKind::Below {
    Vec::new()
  } else {
    pick(&a[s.np + s.nm + s.ni + 1..n], &s.motive_src)?
  };
  Some(mk_app_n(mk_const(&ix_a, ls), &cat(&[ps, &ms, tail, &hs, rest])))
}

// ---------------------------------------------------------------------------
// O6 (`Opt/O6.lean`)
// ---------------------------------------------------------------------------

/// `O6.apply`.
fn o6(env: &OptEnv<'_>, o: &Occ<'_>) -> Option<Expr> {
  let (k, r) = classify(o.head)?;
  if k != AuxKind::Rec && k != AuxKind::RecOn {
    return None;
  }
  let b = (env.block_of)(o.head)?;
  let s = b.shapes.get(&r)?;
  if !s.is_selection() {
    return None;
  }
  let n = standard_telescope(env, s, k, o.head, 0)?;
  if o.args.len() < n {
    return None;
  }
  let ls = o5_levels(s, o.us)?;
  let a = o.args;
  let ps = &a[..s.np];
  let ms = pick(&a[s.np..s.np + s.nm], &s.motive_src)?;
  let min_src = s.minor_src_ids();
  let extra = &a[n..];
  if k == AuxKind::Rec {
    let mins = pick(&a[s.np + s.nm..s.np + s.nm + s.nmin], &min_src)?;
    let tail = &a[s.np + s.nm + s.nmin..n];
    Some(mk_app_n(
      mk_const(&s.ix_rec, ls),
      &cat(&[ps, &ms, &mins, tail, extra]),
    ))
  } else {
    let ix_rec_on = ix_aux_of(&s.ix_rec, AuxKind::RecOn)?;
    if !(env.resolves)(&ix_rec_on) {
      return None;
    }
    let tail = &a[s.np + s.nm..s.np + s.nm + s.ni + 1];
    let mins = pick(&a[s.np + s.nm + s.ni + 1..n], &min_src)?;
    Some(mk_app_n(
      mk_const(&ix_rec_on, ls),
      &cat(&[ps, &ms, tail, &mins, extra]),
    ))
  }
}

// ---------------------------------------------------------------------------
// O11a (`Opt/O11a.lean`)
// ---------------------------------------------------------------------------

/// O11a's verdict while it reads an occurrence (`O11aM`): `Err(None)` not its
/// pattern, `Err(Some c)` a failing side condition `c`.
type O11aRes<T> = Result<T, Option<String>>;

fn pattern<T>(x: Option<T>) -> O11aRes<T> {
  x.ok_or(None)
}

fn side<T>(x: Option<T>, cause: impl FnOnce() -> String) -> O11aRes<T> {
  x.ok_or_else(|| Some(cause()))
}

fn need(b: bool, cause: impl FnOnce() -> String) -> O11aRes<()> {
  if b { Ok(()) } else { Err(Some(cause())) }
}

fn n_size_of_mk() -> Name {
  dotted("SizeOf.mk")
}

fn n_size_of() -> Name {
  dotted("SizeOf.sizeOf")
}

/// The body under at most `k` leading lambdas (`O11a.lamBody`).
fn lam_body(e: &Expr, k: usize) -> Expr {
  let mut cur = e.clone();
  for _ in 0..k {
    let next = match cur.as_data() {
      ExprData::Lam(_, _, b, _, _) => b.clone(),
      _ => break,
    };
    cur = next;
  }
  cur
}

/// `sizeOfTargetE`.
fn size_of_target(env: &OptEnv<'_>, t: &Name) -> O11aRes<()> {
  let tv = side(
    match env.const_of(t) {
      Some(ConstantInfo::InductInfo(tv)) => Some(tv),
      _ => None,
    },
    || {
      format!(
        "the cross target {} is not an inductive type of the input",
        t.pretty()
      )
    },
  )?;
  let np = nat_usize(&tv.num_params);
  need(np == 0, || {
    format!("the cross target {} has {np} parameter(s)", t.pretty())
  })?;
  let ni = nat_usize(&tv.num_indices);
  need(ni == 0, || {
    format!("the cross target {} has {ni} index(es)", t.pretty())
  })?;
  need(tv.cnst.level_params.is_empty(), || {
    format!("the cross target {} has universe parameters", t.pretty())
  })
}

/// An instance lookup (`sizeOfInstanceE` or `sizeOfInstanceAssumingAbsent`).
type InstLookup<'r> = &'r dyn Fn(&Name, &[Expr]) -> O11aRes<(Name, Level)>;

/// `sizeOfInstanceE`.
fn size_of_instance(
  env: &OptEnv<'_>,
  t: &Name,
  telescope: &[Expr],
) -> O11aRes<(Name, Level)> {
  size_of_target(env, t)?;
  let inst = mk_str(t, "_sizeOf_inst");
  let ip = inst.pretty();
  let ici = side(env.const_of(&inst), || {
    format!(
      "the size instance {ip} of a lower component is absent from the input"
    )
  })?;
  let iv = side(
    match ici {
      ConstantInfo::DefnInfo(iv) => Some(iv),
      _ => None,
    },
    || format!("the size instance {ip} is not a definition"),
  )?;
  need(iv.cnst.level_params.is_empty(), || {
    format!("the size instance {ip} has universe parameters")
  })?;
  let shape =
    || format!("the size instance {ip} is not `@SizeOf.mk {} k`", t.pretty());
  let (h, args) = get_app_fn_args(&iv.value);
  let (mk, ls) = side(
    match h.as_data() {
      ExprData::Const(mk, ls, _) => Some((mk.clone(), ls.clone())),
      _ => None,
    },
    shape,
  )?;
  need(mk == n_size_of_mk() && args.len() == 2, shape)?;
  let l = side(ls.first().cloned(), shape)?;
  need(
    matches!(args[0].as_data(), ExprData::Const(ty, _, _) if ty == t),
    shape,
  )?;
  let k = side(
    match args[1].as_data() {
      ExprData::Const(k, _, _) => Some(k.clone()),
      ExprData::Lam(_, _, b, _, _) => match b.as_data() {
        ExprData::App(f, x, _) => match (f.as_data(), x.as_data()) {
          (ExprData::Const(k, _, _), ExprData::Bvar(z, _))
            if nat_usize(z) == 0 =>
          {
            Some(k.clone())
          },
          _ => None,
        },
        _ => None,
      },
      _ => None,
    },
    shape,
  )?;
  let kshape = || {
    format!(
      "the size function {} of {ip} is not `λ t. {}.rec … t`",
      k.pretty(),
      t.pretty()
    )
  };
  let kv = side(
    match env.const_of(&k) {
      Some(ConstantInfo::DefnInfo(kv)) => Some(kv),
      _ => None,
    },
    kshape,
  )?;
  let body = side(
    match kv.value.as_data() {
      ExprData::Lam(_, _, b, _, _) => Some(b.clone()),
      _ => None,
    },
    kshape,
  )?;
  let (rh, rargs) = get_app_fn_args(&body);
  need(
    matches!(rh.as_data(), ExprData::Const(rn, _, _) if *rn == mk_str(t, "rec")),
    kshape,
  )?;
  need(
    matches!(rargs.last().map(|e| e.as_data()), Some(ExprData::Bvar(z, _)) if nat_usize(z) == 0),
    kshape,
  )?;
  let tel = || {
    format!(
      "the recursor telescope of {} is not the occurrence's (one mutual size family)",
      k.pretty()
    )
  };
  need(rargs.len() == telescope.len() + 1, tel)?;
  for (x, y) in rargs.iter().zip(telescope.iter()) {
    need(alpha_eq(x, y), tel)?;
  }
  Ok((inst, l))
}

/// `sizeOfInstanceAssumingAbsent`.
fn size_of_instance_assuming_absent(
  env: &OptEnv<'_>,
  t: &Name,
  telescope: &[Expr],
) -> O11aRes<(Name, Level)> {
  size_of_target(env, t)?;
  let inst = mk_str(t, "_sizeOf_inst");
  match env.const_of(&inst) {
    None => Ok((inst, Level::zero())),
    Some(_) => size_of_instance(env, t, telescope),
  }
}

/// `sizeOfMinorWith`.
#[allow(clippy::too_many_arguments)]
fn size_of_minor_with(
  env: &OptEnv<'_>,
  inst: InstLookup<'_>,
  rv: &RecursorVal,
  in_block: &[bool],
  us: &[Level],
  ps: &[Expr],
  ms: &[Expr],
  mins: &[Expr],
  j: usize,
) -> O11aRes<Option<Expr>> {
  let ienv = env.ienv;
  let aux_sigs = aux_motive_sigs(rv, us, ps, ms, ienv);
  let unread =
    || format!("the constructor and minor type of minor {j} cannot be read");
  let (_, ctor) = side(source_ctor_for_minor(j, rv, ienv, &aux_sigs), unread)?;
  let minor_ty = side(source_minor_type(rv, us, ps, ms, mins, j), unread)?;
  let num_fields = nat_usize(&ctor.num_fields);
  let (field_decls, _, _) =
    side(peel_binders(minor_ty, num_fields, "split_field", 0), unread)?;
  let rec_fields = rec_fields_of(ienv, rv, &field_decls, ps, &aux_sigs);
  let inb = |p: usize| in_block.get(p).copied().unwrap_or(false);
  if !rec_fields.iter().any(|(_, t)| !inb(t.source_pos)) {
    return Ok(None);
  }
  let m = side(mins.get(j).cloned(), unread)?;
  let nb = num_fields + rec_fields.len();
  let telescope = cat(&[ps, ms, mins]);
  let mut cur = m;
  let mut decls: Vec<LocalDecl> = Vec::new();
  let mut fvars: Vec<Expr> = Vec::new();
  for i in 0..nb {
    let (bn, dom, b, bi) = side(
      match cur.as_data() {
        ExprData::Lam(bn, dom, b, bi, _) => {
          Some((bn.clone(), dom.clone(), b.clone(), bi.clone()))
        },
        _ => None,
      },
      || {
        format!(
          "minor {j} is not a λ over its {num_fields} field(s) and {} induction hypothesis(es)",
          rec_fields.len()
        )
      },
    )?;
    let (fv_name, fv) = fresh_fvar("o11a", i);
    if i < num_fields {
      decls.push(LocalDecl {
        fvar_name: fv_name,
        binder_name: bn,
        domain: dom,
        info: bi,
      });
      fvars.push(fv.clone());
      cur = instantiate1(&b, &fv);
    } else {
      let (field_idx, target) = &rec_fields[i - num_fields];
      if inb(target.source_pos) {
        decls.push(LocalDecl {
          fvar_name: fv_name,
          binder_name: bn,
          domain: dom,
          info: bi,
        });
        cur = instantiate1(&b, &fv);
      } else {
        let t = side(rv.all.get(target.source_pos).cloned(), unread)?;
        need(target.xs_fvars.is_empty(), || {
          format!(
            "field {field_idx} of minor {j} is reflexive (a function into the cross target {})",
            t.pretty()
          )
        })?;
        need(target.idx_args.is_empty(), || {
          format!(
            "field {field_idx} of minor {j} has index arguments (its cross target {} is indexed)",
            t.pretty()
          )
        })?;
        let (inst_n, l) = inst(&t, &telescope)?;
        let field = side(fvars.get(*field_idx).cloned(), unread)?;
        let sz = mk_app_n(
          mk_const(&n_size_of(), vec![l]),
          &[mk_const(&t, vec![]), mk_const(&inst_n, vec![]), field],
        );
        cur = instantiate1(&b, &sz);
      }
    }
  }
  Ok(Some(mk_lambda(cur, &decls)))
}

/// `O11a.applyWithE`.
fn o11a_with(
  env: &OptEnv<'_>,
  inst: InstLookup<'_>,
  o: &Occ<'_>,
) -> O11aRes<Expr> {
  let (k, r) = pattern(classify(o.head))?;
  if k != AuxKind::Rec {
    return Err(None);
  }
  let b = pattern((env.block_of)(o.head))?;
  if !b.change.split || b.change.collapse {
    return Err(None);
  }
  let s = pattern(b.shapes.get(&r))?;
  let rv = pattern(match env.const_of(&r) {
    Some(ConstantInfo::RecInfo(rv)) => Some(rv),
    _ => None,
  })?;
  let n = pattern(standard_telescope(env, s, AuxKind::Rec, o.head, 0))?;
  if o.args.len() < n {
    return Err(None);
  }
  let ls = pattern(o5_levels(s, o.us))?;
  let a = o.args;
  let ps = &a[..s.np];
  let ms = &a[s.np..s.np + s.nm];
  let mins = &a[s.np + s.nm..s.np + s.nm + s.nmin];
  let tail = &a[s.np + s.nm + s.nmin..n];
  let in_block: Vec<bool> =
    (0..s.nm).map(|i| s.motive_src.contains(&i)).collect();
  let ms2 = pattern(pick(ms, &s.motive_src))?;
  let mut mins2 = Vec::new();
  let mut any = false;
  for (src, t) in s.minor_src.iter().zip(s.minor_terms.iter()) {
    let j = match src {
      Some(j) => *j,
      None => pattern(wrapped_minor_src(s.arity(), s.np, s.nm, s.nmin, t))?,
    };
    match size_of_minor_with(env, inst, &rv, &in_block, o.us, ps, ms, mins, j)?
    {
      Some(w) => {
        need(src.is_none(), || {
          format!("minor {j} has a cross field but O2 passes it unadapted")
        })?;
        any = true;
        mins2.push(w);
      },
      None => mins2.push(pattern(mins.get(j).cloned())?),
    }
  }
  if !any {
    return Err(None);
  }
  Ok(mk_app_n(
    mk_const(&s.ix_rec, ls),
    &cat(&[ps, &ms2, &mins2, tail, &a[n..]]),
  ))
}

/// `O11a.apply`.
fn o11a(env: &OptEnv<'_>, o: &Occ<'_>) -> Option<Expr> {
  o11a_with(env, &|t, tel| size_of_instance(env, t, tel), o).ok()
}

/// `O11a.isSizeOfOccurrence`.
fn is_size_of_occurrence(
  env: &OptEnv<'_>,
  rv: &RecursorVal,
  o: &Occ<'_>,
  k: usize,
) -> bool {
  let Some(all0) = rv.all.first() else { return false };
  let Some(ConstantInfo::InductInfo(v)) = env.const_of(all0) else {
    return false;
  };
  if o.args.len() < k {
    return false;
  }
  for i in 1..v.all.len() + nat_usize(&v.num_nested) + 1 {
    let Some(ConstantInfo::DefnInfo(dv)) =
      env.const_of(&mk_str(all0, &format!("_sizeOf_{i}")))
    else {
      continue;
    };
    let (h, args) = get_app_fn_args(&lam_body(&dv.value, 64));
    if !matches!(h.as_data(), ExprData::Const(..)) {
      continue;
    }
    if args.len() < k {
      continue;
    }
    if (0..k).all(|j| alpha_eq(&args[j], &o.args[j])) {
      return true;
    }
  }
  false
}

/// `O11a.declineCause?`: the recorded decline at an occurrence that is the
/// recursion of Lean's `sizeOf` family of a split block.
pub fn o11a_decline_cause(env: &OptEnv<'_>, o: &Occ<'_>) -> Option<String> {
  let cause = match o11a_with(env, &|t, tel| size_of_instance(env, t, tel), o) {
    Ok(_) | Err(None) => return None,
    Err(Some(c)) => c,
  };
  let (_, r) = classify(o.head)?;
  let b = (env.block_of)(o.head)?;
  let s = b.shapes.get(&r)?;
  let Some(ConstantInfo::RecInfo(rv)) = env.const_of(&r) else { return None };
  if !is_size_of_occurrence(env, &rv, o, s.np + s.nm + s.nmin) {
    return None;
  }
  let tail = format!(
    "the occurrence of {} keeps O2's relocated-recursor form",
    o.head.pretty()
  );
  match o11a_with(
    env,
    &|t, tel| size_of_instance_assuming_absent(env, t, tel),
    o,
  ) {
    Ok(e) => {
      let missing: Vec<Name> = used_constants(&e)
        .into_iter()
        .filter(|n| {
          matches!(n.as_data(), NameData::Str(_, s, _) if s == "_sizeOf_inst")
            && env.const_of(n).is_none()
        })
        .collect();
      if missing.is_empty() {
        return Some(format!("O11a declined: {cause}; {tail}"));
      }
      let names: Vec<String> = missing.iter().map(|n| n.pretty()).collect();
      Some(format!(
        "O11a declined: the size instance {} of a lower component is absent from the input; {tail}",
        names.join(", ")
      ))
    },
    Err(Some(c)) => Some(format!("O11a declined: {c}; {tail}")),
    Err(None) => Some(format!("O11a declined: {cause}; {tail}")),
  }
}

// ---------------------------------------------------------------------------
// The engine (`Opt/Engine.lean`)
// ---------------------------------------------------------------------------

/// `Engine.engineN`: the first pass that applies, with its name, over the
/// definitional passes in their fixed order (`passes`: O1, O11a, O2, O3,
/// O4, O6), then the proof-justified occurrence passes (`pjPasses`: O8,
/// O7), which fire only at a site (`Packed.pjAllowed`). The bound is on the
/// nesting of O2's relocated calls.
fn engine_n(
  fuel: usize,
  env: &OptEnv<'_>,
  o: &Occ<'_>,
) -> Option<(&'static str, Expr)> {
  if fuel == 0 {
    return None;
  }
  let recur = |o2: &Occ<'_>| engine_n(fuel - 1, env, o2).map(|(_, e)| e);
  o1(env, o)
    .map(|e| ("O1", e))
    .or_else(|| o11a(env, o).map(|e| ("O11a", e)))
    .or_else(|| o2(&recur, env, o).map(|e| ("O2", e)))
    .or_else(|| o3(env, o).map(|e| ("O3", e)))
    .or_else(|| o4(env, o).map(|e| ("O4", e)))
    .or_else(|| o6(env, o).map(|e| ("O6", e)))
    .or_else(|| super::pj::o8(env, o).map(|e| ("O8", e)))
    .or_else(|| super::pj::o7(env, o).map(|e| ("O7", e)))
}

/// The engine at one occurrence (`Engine.engine`, bound 64).
pub fn engine(env: &OptEnv<'_>, o: &Occ<'_>) -> Option<(&'static str, Expr)> {
  engine_n(64, env, o)
}

/// The engine at one occurrence, with the canonical constants the rewrite
/// references (`Engine.engineFull`): the occurrence passes, then the
/// emitting ones (`emitPasses`: O9, O10, O12; O10 before O12).
pub fn engine_full(
  env: &OptEnv<'_>,
  o: &Occ<'_>,
) -> Option<(&'static str, Expr, Vec<ConstantInfo>)> {
  if let Some((nm, e)) = engine(env, o) {
    return Some((nm, e, Vec::new()));
  }
  super::pj::o9(env, o)
    .map(|(e, cs)| ("O9", e, cs))
    .or_else(|| super::pj::o10(env, o).map(|(e, cs)| ("O10", e, cs)))
    .or_else(|| super::pj::o12(env, o).map(|(e, cs)| ("O12", e, cs)))
}

/// A pass whose output is not a conversion of the baseline (O7-O12): its
/// result goes to the canonical `_ix` form of the site only (D1,
/// `Engine.isProofJustified`).
pub fn is_proof_justified(nm: &str) -> bool {
  matches!(nm, "O8" | "O7" | "O9" | "O10" | "O12")
}

/// The data of a changed block for the passes, from its view
/// (`Engine.optBlockOf`): the change kind and classes of Pass 1, and the
/// shape of every Lean recursor's image (an image that fails has none).
pub fn opt_block_of(
  view: &super::view::BlockView,
  inp: &super::view::ViewInput<'_>,
) -> OptBlock {
  let mut class_of = FxHashMap::default();
  for c in &view.canon.components {
    for cls in &c.classes {
      for m in cls {
        class_of.insert(m.clone(), cls.clone());
      }
    }
  }
  let ix_rec_info = |n: &Name| match view.canon_consts.get(n) {
    Some(ConstantInfo::RecInfo(rv)) => Some(rv.clone()),
    _ => None,
  };
  let mut shapes = FxHashMap::default();
  let mut images = FxHashMap::default();
  for r in super::names::image_kinds(inp.const_of, &view.all) {
    let Some(ConstantInfo::RecInfo(rv)) = (inp.const_of)(&r) else { continue };
    let Ok((x, _)) = view.expansion(inp, &r) else { continue };
    images.insert(r.clone(), (x.level_params.clone(), x.value.clone()));
    if let Some(s) = read_shape(
      &x.level_params,
      nat_usize(&rv.num_params),
      nat_usize(&rv.num_motives),
      nat_usize(&rv.num_minors),
      nat_usize(&rv.num_indices),
      &x.value,
      &ix_rec_info,
    ) {
      shapes.insert(r, s);
    }
  }
  let ix_recs: FxHashMap<Name, RecursorVal> = view
    .canon_consts
    .iter()
    .filter_map(|(n, c)| match c {
      ConstantInfo::RecInfo(rv) => Some((n.clone(), rv.clone())),
      _ => None,
    })
    .collect();
  OptBlock {
    all: view.all.clone(),
    change: view.canon.change(),
    class_of,
    shapes,
    images,
    ix_recs,
  }
}

// ---------------------------------------------------------------------------
// O11a's scheduling edges (`O11a.sizeOfEdges`)
// ---------------------------------------------------------------------------

/// The scheduling edges `(source, target)` of O11a: for every split Lean
/// inductive block, `all0._sizeOf_N -> T._sizeOf_inst` for the cross targets
/// `T` of the component its recursion is over (every component's for a
/// nested auxiliary's), and `all0._sizeOf_N -> SizeOf.sizeOf`, when present
/// in `refs` and not inside one component (`O11a.sizeOfEdges`).
pub fn size_of_edges<'n>(
  candidates: impl Iterator<Item = &'n Name>,
  const_of: &dyn Fn(&Name) -> Option<ConstantInfo>,
  refs: &crate::graph::RefMap,
  low_links: &FxHashMap<Name, Name>,
) -> Vec<(Name, Name)> {
  let n_size_of = n_size_of();
  let comp = |m: &Name| low_links.get(m).cloned();
  let mut out = Vec::new();
  for n in candidates {
    if !refs.contains_key(n) {
      continue;
    }
    let Some(ConstantInfo::InductInfo(v)) = const_of(n) else { continue };
    if v.all.first() != Some(n) || v.all.len() < 2 {
      continue;
    }
    if v.all.iter().all(|m| comp(m) == comp(n)) {
      continue;
    }
    let members: FxHashSet<&Name> = v.all.iter().collect();
    let mut cross: FxHashMap<Option<Name>, Vec<Name>> = FxHashMap::default();
    let mut all_targets: Vec<Name> = Vec::new();
    for y in &v.all {
      let Some(ConstantInfo::InductInfo(yv)) = const_of(y) else { continue };
      for c in std::iter::once(y).chain(yv.ctors.iter()) {
        let Some(rs) = refs.get(c) else { continue };
        // the reference sets are hash sets: iterate in a fixed order so the
        // edge list is deterministic (only its set matters to the scheduler)
        let mut rs: Vec<&Name> = rs.iter().collect();
        rs.sort_by_key(|x| x.pretty());
        for r in rs {
          if members.contains(r) && comp(r) != comp(y) {
            let ts = cross.entry(comp(y)).or_default();
            if !ts.contains(r) {
              ts.push(r.clone());
            }
            if !all_targets.contains(r) {
              all_targets.push(r.clone());
            }
          }
        }
      }
    }
    if all_targets.is_empty() {
      continue;
    }
    for i in 1..v.all.len() + nat_usize(&v.num_nested) + 1 {
      let d = mk_str(n, &format!("_sizeOf_{i}"));
      if !refs.contains_key(&d) {
        continue;
      }
      let Some(ConstantInfo::DefnInfo(dv)) = const_of(&d) else { continue };
      let (h, _) = get_app_fn_args(&lam_body(&dv.value, 64));
      let ExprData::Const(r, _, _) = h.as_data() else { continue };
      let targets: Vec<Name> = match as_str(r) {
        Some((x, "rec")) => {
          if members.contains(x) {
            cross.get(&comp(x)).cloned().unwrap_or_default()
          } else {
            continue;
          }
        },
        Some((_, s)) if s.starts_with("rec_") => all_targets.clone(),
        _ => continue,
      };
      if refs.contains_key(&n_size_of) && comp(&d) != comp(&n_size_of) {
        out.push((d.clone(), n_size_of.clone()));
      }
      for t in targets {
        let inst = mk_str(&t, "_sizeOf_inst");
        if refs.contains_key(&inst) && comp(&d) != comp(&inst) {
          out.push((d.clone(), inst));
        }
      }
    }
  }
  out
}

/// Add O11a's scheduling edges to the condensation's block dependencies
/// (`O11a.addSizeOfEdges`): the components and representatives do not
/// change, only the ready order of the scheduler.
pub fn add_size_of_edges<'n>(
  candidates: impl Iterator<Item = &'n Name>,
  const_of: &dyn Fn(&Name) -> Option<ConstantInfo>,
  refs: &crate::graph::RefMap,
  blocks: &mut crate::condense::CondensedBlocks,
) -> usize {
  let edges = size_of_edges(candidates, const_of, refs, &blocks.low_links);
  let mut added = 0;
  for (d, t) in edges {
    let Some(lo) = blocks.low_links.get(&d).cloned() else { continue };
    if blocks.block_refs.entry(lo).or_default().insert(t) {
      added += 1;
    }
  }
  added
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn classify_names() {
    let x = dotted("T");
    assert_eq!(
      classify(&dotted("T.rec")),
      Some((AuxKind::Rec, dotted("T.rec")))
    );
    assert_eq!(
      classify(&dotted("T.rec_2")),
      Some((AuxKind::Rec, mk_str(&x, "rec_2")))
    );
    assert_eq!(
      classify(&dotted("T.casesOn")),
      Some((AuxKind::CasesOn, dotted("T.rec")))
    );
    assert_eq!(
      classify(&dotted("T.brecOn_3.go")),
      Some((AuxKind::Go, mk_str(&x, "rec_3")))
    );
    assert_eq!(
      classify(&dotted("T.below_1")),
      Some((AuxKind::Below, mk_str(&x, "rec_1")))
    );
    // `_0`, a non-digit suffix and a bare `go` are not auxiliaries
    assert_eq!(classify(&dotted("T.rec_0")), None);
    assert_eq!(classify(&dotted("T.rec_x")), None);
    assert_eq!(classify(&dotted("T.go")), None);
  }

  #[test]
  fn ix_aux_names() {
    let rho = dotted("A._ix.rec");
    assert_eq!(
      ix_aux_of(&rho, AuxKind::CasesOn),
      Some(dotted("A._ix.casesOn"))
    );
    assert_eq!(ix_aux_of(&rho, AuxKind::Eq), Some(dotted("A._ix.brecOn.eq")));
    let nested = dotted("A._ix.rec_2");
    assert_eq!(
      ix_aux_of(&nested, AuxKind::Below),
      Some(dotted("A._ix.below_2"))
    );
    // a nested position has no `casesOn`/`recOn`
    assert_eq!(ix_aux_of(&nested, AuxKind::CasesOn), None);
    assert_eq!(ix_aux_of(&dotted("A.notrec"), AuxKind::Rec), None);
  }
}
