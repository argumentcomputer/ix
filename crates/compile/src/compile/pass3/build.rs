//! Pass 3a: the image of a Lean recursor over the canonical recursors
//! (design document §4.1-§4.4, Def 3.3-3.4). A port of
//! `Ix/Compile/Image/Build.lean` (`imageOf`, `buildRecApp`, `findElim`).
//!
//! The computation-rule statements the Lean generator also returns
//! (`RuleStmt`) are test data and are not built here; the image's value,
//! type and arity are.

use ix_common::env::{
  ConstantInfo, ConstructorVal, Expr, ExprData, InductiveVal, Level, LevelData,
  Name, RecursorVal,
};

use super::develop::subst_fvars;
use super::expr::{
  Gen, GenResult, Local, app_arg, eta_reduce, exprs, find_sub, forall_arity,
  fvar_idx, get_app_args, get_app_fn, head_const, idx, inst_forall,
  inst_locals, is_always_zero, lvl_one, lvl_zero, mk_app_n, mk_lambda, mk_str,
  motive_eq, motive_level, normalize_level, strip_mdata, strip_sort,
  subst_levels, telescope, used_constants,
};
use super::names::{
  n_and, n_and_intro, n_pprod, n_pprod_mk, n_true, n_true_intro,
};
use super::spec::{ImageSpec, ind_of};

pub type ConstOf<'a> = &'a dyn Fn(&Name) -> Option<ConstantInfo>;

fn rec_of(const_of: ConstOf<'_>, n: &Name) -> Result<RecursorVal, String> {
  match const_of(n) {
    Some(ConstantInfo::RecInfo(v)) => Ok(v),
    Some(c) => Err(format!(
      "image: {} is not a recursor ({})",
      n.pretty(),
      c.get_name().pretty()
    )),
    None => Err(format!("image: no recursor {}", n.pretty())),
  }
}

fn ctor_of(const_of: ConstOf<'_>, n: &Name) -> Result<ConstructorVal, String> {
  match const_of(n) {
    Some(ConstantInfo::CtorInfo(v)) => Ok(v),
    _ => Err(format!("image: {} is not a constructor", n.pretty())),
  }
}

fn usz(n: &bignat::Nat) -> usize {
  n.to_u64().unwrap_or(0) as usize
}

fn mk_rec_name(n: &Name) -> Name {
  mk_str(n, "rec")
}

/// The recursor of motive slot `k` of the block `all`.
fn rec_name_for(all: &[Name], k: usize) -> Name {
  if k < all.len() {
    mk_rec_name(&all[k])
  } else {
    match all.first() {
      Some(a) => mk_str(a, &format!("rec_{}", k - all.len() + 1)),
      None => Name::anon(),
    }
  }
}

/// A Lean minor: its motive and its constructor (renamed).
struct LeanMinor {
  motive: usize,
  ctor: Name,
}

struct LCtx<'a> {
  const_of: ConstOf<'a>,
  spec: &'a ImageSpec,
  ps: Vec<Local>,
  ms: Vec<Local>,
  mins: Vec<Local>,
  motive_tys: Vec<Expr>,
  minors: Vec<LeanMinor>,
  lu: Level,
  ind_levels: Vec<Level>,
}

impl LCtx<'_> {
  fn motive_params(&self) -> Vec<Name> {
    self
      .ind_levels
      .iter()
      .filter_map(|level| match level.as_data() {
        LevelData::Param(name, _) => Some(name.clone()),
        _ => None,
      })
      .collect()
  }
}

fn analyze_lean_minor(
  g: &mut Gen,
  ms: &[Local],
  ty: &Expr,
) -> GenResult<LeanMinor> {
  let (_, concl) = telescope(g, ty, None);
  let m = fvar_idx(ms, &get_app_fn(&concl))
    .ok_or("image: Lean minor's conclusion is not a motive")?;
  let a =
    app_arg(&concl).ok_or("image: Lean minor's conclusion has no major")?;
  let (c, _) = head_const(&a)
    .ok_or("image: Lean minor's conclusion is not a constructor")?;
  Ok(LeanMinor { motive: m, ctor: c })
}

struct Elim {
  rec_name: Name,
  ind: InductiveVal,
  ind_levels: Vec<Level>,
  params: Vec<Expr>,
  k: usize,
  has_elim_level: bool,
}

/// The motive types (up to sort) of the block of `ind` at `lvls`, `ps`.
fn elim_motive_types(
  g: &mut Gen,
  const_of: ConstOf<'_>,
  ind: &InductiveVal,
  lvls: &[Level],
  ps: &[Expr],
) -> GenResult<Vec<Expr>> {
  let a = ind.all.first().ok_or("image: empty block")?;
  let rv = rec_of(const_of, &mk_rec_name(a))?;
  let has_u = rv.cnst.level_params.len() > ind.cnst.level_params.len();
  let mut us: Vec<Level> = if has_u { vec![lvl_zero()] } else { vec![] };
  us.extend_from_slice(lvls);
  let ty =
    inst_forall(&subst_levels(&rv.cnst.level_params, &us, &rv.cnst.typ), ps)?;
  let (ms_c, _) = telescope(g, &ty, Some(usz(&rv.num_motives)));
  Ok(ms_c.iter().map(|m| strip_sort(&m.typ)).collect())
}

fn is_inductive(const_of: ConstOf<'_>, n: &Name) -> bool {
  matches!(const_of(n), Some(ConstantInfo::InductInfo(_)))
}

/// `elim(t)` (§4.1, Def 3.3).
fn find_elim(g: &mut Gen, c: &LCtx<'_>, t: usize) -> GenResult<Elim> {
  let motive_params = c.motive_params();
  let m = c.ms.get(t).ok_or("image: motive index")?;
  let target = idx(&c.motive_tys, t, "findElim: motive type")?.clone();
  let (xs, _) = telescope(g, &m.typ, None);
  let x = xs.last().ok_or("image: motive without a major")?;
  let big_t = x.typ.clone();
  let (h, h_lvls) =
    head_const(&big_t).ok_or("image: major type's head is not a constant")?;
  let used: Vec<Name> = used_constants(&big_t)
    .into_iter()
    .filter(|n| is_inductive(c.const_of, n))
    .collect();
  let occ = |i: &Name, np: usize| -> Option<(Vec<Expr>, Vec<Level>)> {
    let p = |e: &Expr| match head_const(e) {
      Some((hh, _)) => hh == *i && get_app_args(e).len() >= np,
      None => false,
    };
    find_sub(&p, &big_t).map(|e| {
      let args = get_app_args(&e);
      (args[..np].to_vec(), head_const(&e).map(|(_, l)| l).unwrap_or_default())
    })
  };
  let mut cands: Vec<(Name, Vec<Expr>, Vec<Level>)> = Vec::new();
  for i in &used {
    if c.spec.canon_inds.contains(i) {
      cands.push((i.clone(), exprs(&c.ps), c.ind_levels.clone()));
    }
  }
  for i in &used {
    if !c.spec.canon_inds.contains(i) && *i != h {
      let iv = ind_of(c.const_of, i)?;
      if let Some((ps, lv)) = occ(i, usz(&iv.num_params)) {
        cands.push((i.clone(), ps, lv));
      }
    }
  }
  let h_info = ind_of(c.const_of, &h)?;
  let targs = get_app_args(&big_t);
  let hnp = usz(&h_info.num_params).min(targs.len());
  cands.push((h.clone(), targs[..hnp].to_vec(), h_lvls));
  for (i, ps, lv) in cands {
    let ind = ind_of(c.const_of, &i)?;
    if ps.len() != usz(&ind.num_params) {
      continue;
    }
    let mts = elim_motive_types(g, c.const_of, &ind, &lv, &ps)?;
    if let Some(k) =
      mts.iter().position(|mt| motive_eq(&motive_params, mt, &target))
    {
      let rn = rec_name_for(&ind.all, k);
      let rv = rec_of(c.const_of, &rn)?;
      let has_elim_level =
        rv.cnst.level_params.len() > ind.cnst.level_params.len();
      return Ok(Elim {
        rec_name: rn,
        ind,
        ind_levels: lv,
        params: ps,
        k,
        has_elim_level,
      });
    }
  }
  Err(format!("image: no eliminator for Lean motive {t}"))
}

/// How a slot packs its class.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Pack {
  Single,
  Lift,
  Tuple(usize),
}

impl std::fmt::Display for Pack {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Pack::Single => write!(f, "Ix.Compile.Image.Pack.single"),
      Pack::Lift => write!(f, "Ix.Compile.Image.Pack.lift"),
      Pack::Tuple(n) => write!(f, "Ix.Compile.Image.Pack.tuple {n}"),
    }
  }
}

/// `a ×' b` or `a ∧ b`, with the levels; the pair and its level.
fn mk_pprod_ty(a: (Expr, Level), b: (Expr, Level)) -> (Expr, Level) {
  if is_always_zero(&a.1) && is_always_zero(&b.1) {
    (mk_app_n(Expr::cnst(n_and(), vec![]), &[a.0, b.0]), lvl_zero())
  } else {
    let l = normalize_level(&Level::max(
      Level::max(lvl_one(), a.1.clone()),
      b.1.clone(),
    ));
    (mk_app_n(Expr::cnst(n_pprod(), vec![a.1, b.1]), &[a.0, b.0]), l)
  }
}

/// `⟨a, b⟩`: value, type, level of each side.
fn mk_pprod_val(
  a: (Expr, Expr, Level),
  b: (Expr, Expr, Level),
) -> (Expr, Expr, Level) {
  let (ty, l) =
    mk_pprod_ty((a.1.clone(), a.2.clone()), (b.1.clone(), b.2.clone()));
  if is_always_zero(&a.2) && is_always_zero(&b.2) {
    (mk_app_n(Expr::cnst(n_and_intro(), vec![]), &[a.1, b.1, a.0, b.0]), ty, l)
  } else {
    (
      mk_app_n(Expr::cnst(n_pprod_mk(), vec![a.2, b.2]), &[a.1, b.1, a.0, b.0]),
      ty,
      l,
    )
  }
}

/// Right-nested fold of a non-empty array (`foldr1`).
fn foldr1<T: Clone>(f: &dyn Fn(T, T) -> T, xs: &[T], d: T) -> T {
  match xs.split_last() {
    None => d,
    Some((last, init)) => {
      init.iter().rev().fold(last.clone(), |acc, x| f(x.clone(), acc))
    },
  }
}

fn wrap_ty(p: Pack, lu: &Level, tys: &[Expr]) -> GenResult<Expr> {
  match (p, tys.first()) {
    (Pack::Single, Some(t)) => Ok(t.clone()),
    (Pack::Lift, Some(t)) => Ok(mk_app_n(
      Expr::cnst(n_pprod(), vec![lu.clone(), lvl_zero()]),
      &[t.clone(), Expr::cnst(n_true(), vec![])],
    )),
    (Pack::Tuple(_), Some(t)) => {
      let items: Vec<(Expr, Level)> =
        tys.iter().map(|x| (x.clone(), lu.clone())).collect();
      Ok(foldr1(&mk_pprod_ty, &items, (t.clone(), lu.clone())).0)
    },
    (_, None) => Err("image: wrapTy: empty slot class".into()),
  }
}

fn wrap_val(p: Pack, lu: &Level, vs: &[(Expr, Expr)]) -> GenResult<Expr> {
  match (p, vs.first()) {
    (Pack::Single, Some(v)) => Ok(v.0.clone()),
    (Pack::Lift, Some(v)) => Ok(mk_app_n(
      Expr::cnst(n_pprod_mk(), vec![lu.clone(), lvl_zero()]),
      &[
        v.1.clone(),
        Expr::cnst(n_true(), vec![]),
        v.0.clone(),
        Expr::cnst(n_true_intro(), vec![]),
      ],
    )),
    (Pack::Tuple(_), Some((v, t))) => {
      let items: Vec<(Expr, Expr, Level)> =
        vs.iter().map(|(v, t)| (v.clone(), t.clone(), lu.clone())).collect();
      Ok(foldr1(&mk_pprod_val, &items, (v.clone(), t.clone(), lu.clone())).0)
    },
    (_, None) => Err("image: wrapVal: empty slot class".into()),
  }
}

/// Component `pos` of a packed slot.
fn unwrap(p: Pack, lu_zero: bool, pos: usize, v: Expr) -> Expr {
  match p {
    Pack::Single => v,
    Pack::Lift => Expr::proj(n_pprod(), 0u64.into(), v),
    Pack::Tuple(n) => {
      let s = if lu_zero { n_and() } else { n_pprod() };
      let mut v = v;
      for _ in 0..pos {
        v = Expr::proj(s.clone(), 1u64.into(), v);
      }
      if pos + 1 < n { Expr::proj(s, 0u64.into(), v) } else { v }
    },
  }
}

/// A canonical minor's shape.
fn analyze_canon_minor(
  g: &mut Gen,
  const_of: ConstOf<'_>,
  ms_c: &[Local],
  ty: &Expr,
) -> GenResult<(usize, Name, usize, Vec<(usize, usize)>)> {
  let (bs, concl) = telescope(g, ty, None);
  let mi = fvar_idx(ms_c, &get_app_fn(&concl))
    .ok_or("image: canonical minor's conclusion")?;
  let a = app_arg(&concl).ok_or("image: canonical minor's major")?;
  let (ctor, _) =
    head_const(&a).ok_or("image: canonical minor's constructor")?;
  let nf = usz(&ctor_of(const_of, &ctor)?.num_fields);
  let flds: Vec<Local> = bs[..nf.min(bs.len())].to_vec();
  let mut ih_fields: Vec<(usize, usize)> = Vec::new();
  for ih in bs.iter().skip(nf) {
    let (_, cc) = telescope(g, &ih.typ, None);
    let m = fvar_idx(ms_c, &get_app_fn(&cc))
      .ok_or("image: canonical hypothesis head")?;
    let fa = app_arg(&cc).ok_or("image: canonical hypothesis major")?;
    let f = fvar_idx(&flds, &get_app_fn(&fa))
      .ok_or("image: canonical hypothesis field")?;
    ih_fields.push((f, m));
  }
  Ok((mi, ctor, nf, ih_fields))
}

/// `ρ.{ℓ} params motives′ minors′ idx major`, unwrapped at Lean motive `t`.
fn build_rec_app(
  g: &mut Gen,
  fuel: usize,
  c: &LCtx<'_>,
  t: usize,
  idx_args: &[Expr],
  major: &Expr,
) -> GenResult<Expr> {
  if fuel == 0 {
    return Err(format!(
      "image: relocation bound exhausted at Lean motive {t}"
    ));
  }
  let fuel = fuel - 1;
  let e = find_elim(g, c, t)?;
  let rv = rec_of(c.const_of, &e.rec_name)?;
  let mts = elim_motive_types(g, c.const_of, &e.ind, &e.ind_levels, &e.params)?;
  // step 1: slot classes
  let motive_params = c.motive_params();
  let classes: Vec<Vec<usize>> = mts
    .iter()
    .map(|mt| {
      c.motive_tys
        .iter()
        .enumerate()
        .filter(|(_, ty)| motive_eq(&motive_params, ty, mt))
        .map(|(j, _)| j)
        .collect()
    })
    .collect();
  for (i, cl) in classes.iter().enumerate() {
    if cl.is_empty() {
      return Err(format!(
        "image: eliminator {}: slot {i} has no Lean motive",
        e.rec_name.pretty()
      ));
    }
  }
  // step 2: the level
  let any_tuple = classes.iter().any(|cl| cl.len() > 1);
  let lu_zero = is_always_zero(&c.lu);
  let big_l = if any_tuple && !lu_zero {
    normalize_level(&Level::max(lvl_one(), c.lu.clone()))
  } else {
    c.lu.clone()
  };
  let packs: Vec<Pack> = classes
    .iter()
    .map(|cl| {
      if cl.len() > 1 {
        Pack::Tuple(cl.len())
      } else if any_tuple && !lu_zero {
        Pack::Lift
      } else {
        Pack::Single
      }
    })
    .collect();
  if !e.has_elim_level && !is_always_zero(&big_l) {
    return Err(format!(
      "image: eliminator {} is small but the Lean motives are not",
      e.rec_name.pretty()
    ));
  }
  let mut us: Vec<Level> =
    if e.has_elim_level { vec![big_l.clone()] } else { vec![] };
  us.extend(e.ind_levels.iter().cloned());
  let rec_c = Expr::cnst(e.rec_name.clone(), us.clone());
  let rty = inst_forall(
    &subst_levels(&rv.cnst.level_params, &us, &rv.cnst.typ),
    &e.params,
  )?;
  let classes_s: Vec<String> = classes
    .iter()
    .map(|cl| {
      format!(
        "#[{}]",
        cl.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ")
      )
    })
    .collect();
  let packs_s: Vec<String> = packs.iter().map(ToString::to_string).collect();
  g.trace(format!(
    "elim for Lean motive {t}: {} classes=#[{}] packs=#[{}]",
    e.rec_name.pretty(),
    classes_s.join(", "),
    packs_s.join(", ")
  ));
  let nmot = usz(&rv.num_motives);
  let (xs, _) = telescope(g, &rty, Some(nmot + usz(&rv.num_minors)));
  let ms_c: Vec<Local> = xs[..nmot.min(xs.len())].to_vec();
  let mins_c: Vec<Local> = xs[nmot.min(xs.len())..].to_vec();
  // step 3: motives
  let mut motives: Vec<Expr> = Vec::new();
  for (i, mc) in ms_c.iter().enumerate() {
    let (isy, _) = telescope(g, &mc.typ, None);
    let mut apps: Vec<Expr> = Vec::new();
    for j in idx(&classes, i, "buildRecApp: slot class")? {
      let m = idx(&c.ms, *j, "buildRecApp: Lean motive")?;
      apps.push(mk_app_n(m.expr(), &exprs(&isy)));
    }
    let p = *idx(&packs, i, "buildRecApp: slot pack")?;
    motives.push(eta_reduce(&mk_lambda(&isy, &wrap_ty(p, &c.lu, &apps)?)));
  }
  // step 4: minors
  let ms_c_names: Vec<Name> = ms_c.iter().map(|l| l.fvar.clone()).collect();
  let mut minors: Vec<Expr> = Vec::new();
  for min_c in &mins_c {
    let (mi, ctor, nf, ih_fields) =
      analyze_canon_minor(g, c.const_of, &ms_c, &min_c.typ)?;
    let mty = subst_fvars(&ms_c_names, &motives, &min_c.typ)?;
    let (bs, _) = telescope(g, &mty, None);
    let flds: Vec<Local> = bs[..nf.min(bs.len())].to_vec();
    let ihs_c: Vec<Local> = bs[nf.min(bs.len())..].to_vec();
    let mut comps: Vec<(Expr, Expr)> = Vec::new();
    for j in idx(&classes, mi, "buildRecApp: minor slot class")?.clone() {
      let lmi = c
        .minors
        .iter()
        .position(|lm| lm.motive == j && lm.ctor == ctor)
        .ok_or_else(|| {
          format!(
            "image: no Lean minor for motive {j} and constructor {}",
            ctor.pretty()
          )
        })?;
      let lm = idx(&c.mins, lmi, "buildRecApp: Lean minor")?.clone();
      let mut lty = inst_forall(&lm.typ, &exprs(&flds))?;
      let mut ih_vals: Vec<Expr> = Vec::new();
      for _ in 0..forall_arity(&lty) {
        let s = strip_mdata(&lty);
        let ExprData::ForallE(_, bt, body, _, _) = s.as_data() else {
          return Err("image: Lean minor arity".into());
        };
        let (ys, cc) = telescope(g, bt, None);
        let t2 = fvar_idx(&c.ms, &get_app_fn(&cc))
          .ok_or("image: Lean hypothesis head")?;
        let arg = app_arg(&cc).ok_or("image: Lean hypothesis major")?;
        let mut idx2 = get_app_args(&cc);
        idx2.pop();
        let f = fvar_idx(&flds, &get_app_fn(&arg))
          .ok_or("image: Lean hypothesis field")?;
        let v = match ih_fields.iter().position(|(ff, _)| *ff == f) {
          Some(q) => {
            let mq = idx(&ih_fields, q, "buildRecApp: hypothesis field")?.1;
            let pos = idx(&classes, mq, "buildRecApp: hypothesis slot class")?
              .iter()
              .position(|x| *x == t2)
              .ok_or_else(|| {
                format!("image: hypothesis motive {t2} not in its slot's class")
              })?;
            let p = *idx(&packs, mq, "buildRecApp: hypothesis slot pack")?;
            let ih = idx(&ihs_c, q, "buildRecApp: canonical hypothesis")?;
            mk_lambda(
              &ys,
              &unwrap(p, lu_zero, pos, mk_app_n(ih.expr(), &exprs(&ys))),
            )
          },
          None => {
            let v = build_rec_app(g, fuel, c, t2, &idx2, &arg)?;
            mk_lambda(&ys, &v)
          },
        };
        ih_vals.push(v.clone());
        lty = inst_locals(body, &[v]);
      }
      let mut args = exprs(&flds);
      args.extend(ih_vals);
      comps.push((mk_app_n(lm.expr(), &args), lty));
    }
    let p = *idx(&packs, mi, "buildRecApp: minor slot pack")?;
    minors.push(eta_reduce(&mk_lambda(&bs, &wrap_val(p, &c.lu, &comps)?)));
  }
  // step 5
  let mut args = e.params.clone();
  args.extend(motives);
  args.extend(minors);
  args.extend(idx_args.iter().cloned());
  args.push(major.clone());
  let app = mk_app_n(rec_c, &args);
  let pos = idx(&classes, e.k, "buildRecApp: eliminated slot class")?
    .iter()
    .position(|x| *x == t)
    .ok_or("image: eliminated motive not in its class")?;
  let p = *idx(&packs, e.k, "buildRecApp: eliminated slot pack")?;
  Ok(unwrap(p, lu_zero, pos, app))
}

/// The image of a Lean recursor.
#[derive(Clone, Debug)]
pub struct Image {
  pub level_params: Vec<Name>,
  /// `tr_N(type r)`.
  pub typ: Expr,
  /// A lambda over Lean's telescope.
  pub value: Expr,
  pub arity: usize,
}

/// The image of Lean recursor `r` of the block of `spec`.
pub fn image_of(
  const_of: ConstOf<'_>,
  spec: &ImageSpec,
  r: &Name,
) -> Result<Image, String> {
  let mut g = Gen::default();
  let rv = rec_of(const_of, r)?;
  let ty = spec.tr(&rv.cnst.typ);
  let (xs, body) = telescope(&mut g, &ty, None);
  let np = usz(&rv.num_params);
  let nm = usz(&rv.num_motives);
  let nmin = usz(&rv.num_minors);
  let sl = |a: usize, b: usize| -> Vec<Local> {
    xs[a.min(xs.len())..b.min(xs.len())].to_vec()
  };
  let ps = sl(0, np);
  let ms = sl(np, np + nm);
  let mins = sl(np + nm, np + nm + nmin);
  let is_ = sl(np + nm + nmin, xs.len().saturating_sub(1));
  let x = xs.last().ok_or("image: recursor without a major")?.clone();
  let m0 = ms.first().ok_or("image: recursor without motives")?.clone();
  let mut minors = Vec::with_capacity(mins.len());
  for m in &mins {
    minors.push(analyze_lean_minor(&mut g, &ms, &m.typ)?);
  }
  let a0 = rv.all.first().ok_or("image: empty block")?;
  let ind = ind_of(const_of, a0)?;
  let c = LCtx {
    const_of,
    spec,
    ps,
    motive_tys: ms.iter().map(|m| strip_sort(&m.typ)).collect(),
    ms: ms.clone(),
    mins,
    minors,
    lu: motive_level(&m0.typ),
    ind_levels: ind
      .cnst
      .level_params
      .iter()
      .map(|p| Level::param(p.clone()))
      .collect(),
  };
  let t =
    fvar_idx(&ms, &get_app_fn(&body)).ok_or("image: recursor's conclusion")?;
  let v = build_rec_app(&mut g, nm + 1, &c, t, &exprs(&is_), &x.expr())?;
  let value = mk_lambda(&xs, &v);
  // the rule statements' constructor lookups fail the image on the Lean side
  // when a rule's constructor is absent; keep that failure
  for rule in &rv.rules {
    ctor_of(const_of, &rule.ctor)?;
  }
  Ok(Image {
    level_params: rv.cnst.level_params.clone(),
    typ: ty,
    value,
    arity: np + nm + nmin + usz(&rv.num_indices) + 1,
  })
}
