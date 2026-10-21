//! The definitional passes O2-O6 (CQ5.1), at every full application of an
//! image-kind head, before the call-site rewrite inlines the image (Lean
//! `RwConfig.opt?`). A port of `Ix/Compile/Pass/Opt/{Core,Engine,O2,O3,O4,
//! O5,O6}.lean`; the Lean modules are the specification of each pass
//! (contract, faithfulness, side condition), cited per function. O1 is never
//! ported (O6 builds the identical term); O11a and the proof-justified
//! passes come with CQ5.3. Donor: `jcb/ix-certify-compile` `a9cf3607`,
//! `crates/compile/src/compile/pass3/opt.rs`.

use rustc_hash::FxHashMap;

use ix_common::env::{
  ConstantInfo, Env as LeanEnv, Expr, ExprData, Level, LevelData, Name,
  NameData, RecursorVal,
};

use super::expr::{get_app_fn_args, mk_app_n, nat_usize, subst_level};
use super::names::mk_str;
use super::spec::BlockChange;

// ---------------------------------------------------------------------------
// Core (`Opt/Core.lean`)
// ---------------------------------------------------------------------------

/// An occurrence of an image-kind auxiliary: `head.{us} args`, the arguments
/// already in normal form (`Opt.Occ`; the definitional passes do not read
/// its site).
pub struct Occ<'a> {
  pub head: &'a Name,
  pub us: &'a [Level],
  pub args: &'a [Expr],
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
  #[allow(dead_code)] // read by O2 (the next CQ5.1 commit)
  pub(super) fn arity(&self) -> usize {
    self.np + self.nm + self.nmin + self.ni + 1
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
}

/// What the passes read of the compiler (`Opt.OptEnv`).
pub struct OptEnv<'a> {
  /// The input environment.
  pub ienv: &'a LeanEnv,
  /// A name of `E` resolves to an address.
  pub resolves: &'a dyn Fn(&Name) -> bool,
  /// The block of a Lean image-kind head, when it is a changed block's.
  pub block_of: &'a dyn Fn(&Name) -> Option<&'a OptBlock>,
}

impl OptEnv<'_> {
  pub(super) fn const_of(&self, n: &Name) -> Option<ConstantInfo> {
    self.ienv.get(n).map(|e| e.cloned())
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
// The engine (`Opt/Engine.lean`)
// ---------------------------------------------------------------------------

/// The first pass that applies, with its name (`Engine.engineN`): O2, O3,
/// O4, O6 in this order. Fuel bounds the recursive optimization of O2's
/// relocated calls; zero returns `None`.
fn engine_n(
  fuel: usize,
  env: &OptEnv<'_>,
  o: &Occ<'_>,
) -> Option<(&'static str, Expr)> {
  if fuel == 0 {
    return None;
  }
  o3(env, o)
    .map(|e| ("O3", e))
    .or_else(|| o4(env, o).map(|e| ("O4", e)))
    .or_else(|| o6(env, o).map(|e| ("O6", e)))
}

/// The engine at one occurrence (`Engine.engine`, bound 64).
pub fn engine(env: &OptEnv<'_>, o: &Occ<'_>) -> Option<(&'static str, Expr)> {
  engine_n(64, env, o)
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
  for r in super::names::image_kinds(inp.const_of, &view.all) {
    let Some(ConstantInfo::RecInfo(rv)) = (inp.const_of)(&r) else { continue };
    let Ok((x, _)) = view.expansion(inp, &r) else { continue };
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
  OptBlock {
    all: view.all.clone(),
    change: view.canon.change(),
    class_of,
    shapes,
  }
}
