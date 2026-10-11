//! The `partial_fixpoint` transport (a port of
//! `Ix/Compile/Clique/PartialFixpoint.lean` and `PFConjugation.lean`).

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::env::{BinderInfo, Expr, ExprData, Level, Name};

use super::basic::*;
use super::packing::*;
use super::structural::{path_prefix, proj_chain, steps_fit};
use super::telescope::*;
use super::wf::{Transported, WfOutput, finish_renames, scan_proofs};
use crate::compile::pass3::expr::{get_app_fn_args, strip_mdata, subst_levels};

pub fn n_order_fix() -> Name {
  ln("Lean.Order.fix")
}
fn n_inst_ccpo_pprod() -> Name {
  ln("Lean.Order.instCCPOPProd")
}
fn n_inst_lattice_pprod() -> Name {
  ln("Lean.Order.instCompleteLatticePProd")
}
fn n_inst_po_pprod() -> Name {
  ln("Lean.Order.instPartialOrderPProd")
}
fn n_ccpo_to_po() -> Name {
  ln("Lean.Order.CCPO.toPartialOrder")
}
fn n_lattice_to_po() -> Name {
  ln("Lean.Order.CompleteLattice.toPartialOrder")
}
fn n_mono_mk() -> Name {
  ln("Lean.Order.PProd.monotone_mk")
}
fn n_mono_fst() -> Name {
  ln("Lean.Order.PProd.monotone_fst")
}
fn n_mono_snd() -> Name {
  ln("Lean.Order.PProd.monotone_snd")
}
fn n_mono_id() -> Name {
  ln("Lean.Order.monotone_id")
}
pub fn n_mono_compose() -> Name {
  ln("Lean.Order.monotone_compose")
}
fn n_monotone() -> Name {
  ln("Lean.Order.monotone")
}

/// `mkInstTree`.
pub fn mk_inst_tree(h: &Name, s: &Spine, insts: &[Expr]) -> Expr {
  let n = s.size();
  let suf = s.suffixes();
  let mut acc = insts[n - 1].clone();
  for k in (0..n - 1).rev() {
    let (r, lr) = &suf[k + 1];
    acc = mk_app_n(
      cnst(h, &[s.lvls[k].clone(), lr.clone()]),
      &[s.leaves[k].clone(), r.clone(), insts[k].clone(), acc],
    );
  }
  acc
}

/// `decodeInstTree`.
pub fn decode_inst_tree(
  n: usize,
  e: &Expr,
) -> Option<(Name, Spine, Vec<Expr>)> {
  let (h, us, args) = const_app(e)?;
  if !((h == n_inst_ccpo_pprod()
    || h == n_inst_lattice_pprod()
    || h == n_inst_po_pprod())
    && us.len() == 2
    && args.len() == 4)
  {
    return None;
  }
  let s = decode_spine(
    PackKind::Pprod,
    n,
    &mk_app_n(cnst(&n_pprod(), &us), &[args[0].clone(), args[1].clone()]),
  )?;
  let mut insts = Vec::new();
  let mut cur = e.clone();
  for _ in 0..n - 1 {
    match const_app(&cur) {
      Some((h2, _, a)) if a.len() == 4 => {
        if h2 == h {
          insts.push(a[2].clone());
          cur = a[3].clone();
        } else {
          return None;
        }
      },
      _ => return None,
    }
  }
  insts.push(cur);
  if alpha_eq(&mk_inst_tree(&h, &s, &insts), e) {
    Some((h, s, insts))
  } else {
    None
  }
}

/// `mkPathApp`.
pub fn mk_path_app(s: &Spine, j: usize, x: &Expr) -> Expr {
  let n = s.size();
  let suf = s.suffixes();
  let mut acc = x.clone();
  for k in 0..j {
    let (r, lr) = &suf[k + 1];
    acc = mk_app_n(
      cnst(&n_pprod_snd(), &[s.lvls[k].clone(), lr.clone()]),
      &[s.leaves[k].clone(), r.clone(), acc],
    );
  }
  if j + 1 < n {
    let (r, lr) = &suf[j + 1];
    acc = mk_app_n(
      cnst(&n_pprod_fst(), &[s.lvls[j].clone(), lr.clone()]),
      &[s.leaves[j].clone(), r.clone(), acc],
    );
  }
  acc
}

/// `decodePathApp`.
pub fn decode_path_app(n: usize, e: &Expr) -> Option<(Spine, usize, Expr)> {
  let mut cur = e.clone();
  let mut steps: Vec<(Name, Vec<Level>, Expr, Expr)> = Vec::new();
  for _ in 0..n {
    match const_app(&cur) {
      Some((h, us, a)) if a.len() == 3 => {
        if h == n_pprod_fst() || h == n_pprod_snd() {
          steps.push((h, us, a[0].clone(), a[1].clone()));
          cur = a[2].clone();
        } else {
          break;
        }
      },
      _ => break,
    }
  }
  if steps.is_empty() {
    return None;
  }
  let (_, us, a, b) = steps.last().unwrap().clone();
  let s = decode_spine(
    PackKind::Pprod,
    n,
    &mk_app_n(cnst(&n_pprod(), &us), &[a, b]),
  )?;
  let ones = steps.iter().rev().take_while(|s| s.0 == n_pprod_snd()).count();
  let j = if ones + 1 < n { ones } else { n - 1 };
  if alpha_eq(&mk_path_app(&s, j, &cur), e) { Some((s, j, cur)) } else { None }
}

#[derive(Clone, Debug)]
pub struct PfLayout {
  pub n: usize,
  pub sigma: Vec<usize>,
  pub packed_name: Name,
  pub new_packed_name: Name,
  pub num_fixed: usize,
  pub fixed_perm: Vec<usize>,
  pub leaves: Vec<Expr>,
  pub spine: Spine,
  pub proof_perm: FxHashMap<Name, Vec<usize>>,
  pub compose_levels: Vec<Name>,
  pub member_fixed: Vec<Vec<usize>>,
}

/// `normOrderAlias`.
pub fn norm_order_alias(e: &Expr) -> Expr {
  match e.as_data() {
    ExprData::Const(c, _, _) => {
      if *c == ln("Lean.Order.ImplicationOrder")
        || *c == ln("Lean.Order.ReverseImplicationOrder")
      {
        sort0()
      } else {
        e.clone()
      }
    },
    ExprData::App(f, a, _) => {
      Expr::app(norm_order_alias(f), norm_order_alias(a))
    },
    ExprData::Lam(n, t, b, bi, _) => {
      Expr::lam(n.clone(), norm_order_alias(t), norm_order_alias(b), bi.clone())
    },
    ExprData::ForallE(n, t, b, bi, _) => {
      Expr::all(n.clone(), norm_order_alias(t), norm_order_alias(b), bi.clone())
    },
    ExprData::Mdata(_, x, _) => norm_order_alias(x),
    _ => e.clone(),
  }
}

impl PfLayout {
  pub fn is_clique(&self, s: &Spine) -> bool {
    s.size() == self.n
      && match_packing_leaves(
        &s.leaves.iter().map(norm_order_alias).collect::<Vec<_>>(),
        &self.leaves.iter().map(norm_order_alias).collect::<Vec<_>>(),
      )
      .is_some()
  }
}

/// `toPO`.
pub fn to_po(lattice: bool, lvl: &Level, ty: &Expr, inst: &Expr) -> Expr {
  mk_app_n(
    cnst(
      &if lattice { n_lattice_to_po() } else { n_ccpo_to_po() },
      std::slice::from_ref(lvl),
    ),
    &[ty.clone(), inst.clone()],
  )
}

#[derive(Clone, Debug)]
pub struct OrderData {
  pub spine: Spine,
  pub insts: Vec<Expr>,
  pub lattice: bool,
  pub tspine: Spine,
}

pub fn decode_order_data(l: &PfLayout, po: &Expr) -> Option<OrderData> {
  let (h, _, args) = const_app(po)?;
  if !((h == n_ccpo_to_po() || h == n_lattice_to_po()) && args.len() == 2) {
    return None;
  }
  let (ih, s, insts) = decode_inst_tree(l.n, &args[1])?;
  if !l.is_clique(&s) {
    return None;
  }
  Some(OrderData {
    spine: s.clone(),
    insts,
    lattice: ih == n_inst_lattice_pprod(),
    tspine: s,
  })
}

impl OrderData {
  fn inst_head(&self) -> Name {
    if self.lattice { n_inst_lattice_pprod() } else { n_inst_ccpo_pprod() }
  }

  pub fn packed_po(&self) -> Expr {
    let suf = self.spine.suffixes();
    to_po(
      self.lattice,
      &suf[0].1,
      &self.spine.typ(),
      &mk_inst_tree(&self.inst_head(), &self.spine, &self.insts),
    )
  }

  pub fn suffix_po(&self, k: usize) -> Expr {
    let suf = self.spine.suffixes();
    let n = self.spine.size();
    let inst = if k + 1 == n {
      self.insts[n - 1].clone()
    } else {
      mk_inst_tree(
        &self.inst_head(),
        &Spine {
          kind: self.spine.kind,
          leaves: extract(&self.spine.leaves, k, n),
          lvls: extract(&self.spine.lvls, k, n),
        },
        &extract(&self.insts, k, n),
      )
    };
    to_po(self.lattice, &suf[k].1, &suf[k].0, &inst)
  }

  pub fn po_tree(&self, k: usize) -> Expr {
    let t = &self.tspine;
    let n = t.size();
    let leaf_po =
      |j: usize| to_po(self.lattice, &t.lvls[j], &t.leaves[j], &self.insts[j]);
    if k + 1 == n {
      return leaf_po(n - 1);
    }
    mk_inst_tree(
      &n_inst_po_pprod(),
      &Spine {
        kind: t.kind,
        leaves: extract(&t.leaves, k, n),
        lvls: extract(&t.lvls, k, n),
      },
      &(0..n - k).map(|j| leaf_po(k + j)).collect::<Vec<_>>(),
    )
  }

  pub fn permute(&self, s: &[usize]) -> OrderData {
    OrderData {
      spine: self.spine.permute(s),
      insts: permute(s, &self.insts),
      lattice: self.lattice,
      tspine: self.tspine.permute(s),
    }
  }
}

/// `mkPathProof`.
pub fn mk_path_proof(d: &OrderData, j: usize) -> (Expr, Expr) {
  let s = &d.spine;
  let n = s.size();
  let suf = s.suffixes();
  let gamma = d.tspine.typ();
  let lgamma = suf[0].1.clone();
  let po_gamma = d.packed_po();
  let x_name = root("x");
  let mut f =
    Expr::lam(x_name.clone(), gamma.clone(), mk_bvar(0), BinderInfo::Default);
  let mut h = mk_app_n(
    cnst(&n_mono_id(), std::slice::from_ref(&lgamma)),
    &[gamma.clone(), po_gamma.clone()],
  );
  let mut body = mk_bvar(0);
  let mut steps: Vec<(usize, bool)> = (0..j).map(|k| (k, false)).collect();
  if j + 1 < n {
    steps.push((j, true));
  }
  for (k, is_fst) in steps {
    let (r, lr) = &suf[k + 1];
    let leaf_po = to_po(d.lattice, &s.lvls[k], &s.leaves[k], &d.insts[k]);
    let rest_po = d.suffix_po(k + 1);
    let lem = if is_fst { n_mono_fst() } else { n_mono_snd() };
    h = mk_app_n(
      cnst(&lem, &[s.lvls[k].clone(), lr.clone(), lgamma.clone()]),
      &[
        s.leaves[k].clone(),
        r.clone(),
        gamma.clone(),
        leaf_po,
        rest_po,
        po_gamma.clone(),
        f.clone(),
        h,
      ],
    );
    let pr = if is_fst { n_pprod_fst() } else { n_pprod_snd() };
    body = mk_app_n(
      cnst(&pr, &[s.lvls[k].clone(), lr.clone()]),
      &[s.leaves[k].clone(), r.clone(), body],
    );
    f = Expr::lam(
      x_name.clone(),
      gamma.clone(),
      body.clone(),
      BinderInfo::Default,
    );
  }
  (h, f)
}

/// `decodePathProof`.
pub fn decode_path_proof(l: &PfLayout, e: &Expr) -> Option<(OrderData, usize)> {
  let (h, _, args) = const_app(e)?;
  if !(h == n_mono_fst() || h == n_mono_snd() || h == n_mono_id()) {
    return None;
  }
  let po = if h == n_mono_id() {
    if args.len() == 2 { args.get(1)? } else { return None }
  } else if args.len() == 8 {
    args.get(5)?
  } else {
    return None;
  };
  let d = decode_order_data(l, po)?;
  let dom = if h == n_mono_id() { args.first()? } else { args.get(2)? };
  let ts = decode_spine(PackKind::Pprod, l.n, dom)?;
  if !l.is_clique(&ts) {
    return None;
  }
  let d = OrderData { tspine: ts, ..d };
  let mut cur = e.clone();
  let mut snds = 0;
  let mut fst = false;
  for _ in 0..l.n {
    match const_app(&cur) {
      Some((h2, _, a2)) => {
        if h2 == n_mono_snd() && a2.len() == 8 {
          snds += 1;
          cur = a2[7].clone();
        } else if h2 == n_mono_fst() && a2.len() == 8 {
          if fst || snds > 0 {
            return None;
          }
          fst = true;
          cur = a2[7].clone();
        } else {
          break;
        }
      },
      None => break,
    }
  }
  let j = snds;
  if !((fst && j + 1 < l.n) || (!fst && j + 1 == l.n)) {
    return None;
  }
  if alpha_eq(&mk_path_proof(&d, j).0, e) { Some((d, j)) } else { None }
}

/// `mkMonoTreeOver`.
pub fn mk_mono_tree_over(
  gamma: &Expr,
  lgamma: &Level,
  po_gamma: &Expr,
  d: &OrderData,
  fs: &[Expr],
  hs: &[Expr],
) -> Expr {
  let s = &d.tspine;
  let n = s.size();
  let suf = s.suffixes();
  let x_name = root("x");
  let inst_body = |f: &Expr| -> Expr {
    match strip_mdata(f).as_data() {
      ExprData::Lam(_, _, b, _, _) => b.clone(),
      _ => Expr::app(lift(f, 1), mk_bvar(0)),
    }
  };
  let mut g = fs[n - 1].clone();
  let mut h = hs[n - 1].clone();
  for k in (0..n - 1).rev() {
    let (r, lr) = &suf[k + 1];
    let leaf_po = to_po(d.lattice, &s.lvls[k], &s.leaves[k], &d.insts[k]);
    h = mk_app_n(
      cnst(&n_mono_mk(), &[s.lvls[k].clone(), lr.clone(), lgamma.clone()]),
      &[
        s.leaves[k].clone(),
        r.clone(),
        gamma.clone(),
        leaf_po,
        d.po_tree(k + 1),
        po_gamma.clone(),
        fs[k].clone(),
        g.clone(),
        hs[k].clone(),
        h,
      ],
    );
    if k > 0 {
      let tup = mk_app_n(
        cnst(&n_pprod_mk(), &[s.lvls[k].clone(), lr.clone()]),
        &[lift(&s.leaves[k], 1), lift(r, 1), inst_body(&fs[k]), inst_body(&g)],
      );
      g = Expr::lam(x_name.clone(), gamma.clone(), tup, BinderInfo::Default);
    }
  }
  h
}

pub fn mk_mono_tree(d: &OrderData, fs: &[Expr], hs: &[Expr]) -> Expr {
  mk_mono_tree_over(
    &d.spine.typ(),
    &d.spine.suffixes()[0].1,
    &d.packed_po(),
    d,
    fs,
    hs,
  )
}

/// `mkComposeFallback`.
pub fn mk_compose_fallback(
  sigma: &[usize],
  d: &OrderData,
  d2: &OrderData,
  k: usize,
  f: &Expr,
  h: &Expr,
  compose_levels: &[Name],
) -> R<Expr> {
  let s = &d.spine;
  let n = s.size();
  let gamma2 = d2.spine.typ();
  let lgamma2 = d2.spine.suffixes()[0].1.clone();
  let gamma = s.typ();
  let lgamma = s.suffixes()[0].1.clone();
  let y_name = root("y");
  let lifted = s.map_leaves(&|x| lift(x, 1));
  let lifted2 = d2.spine.map_leaves(&|x| lift(x, 1));
  let comps: Vec<Expr> =
    (0..n).map(|i| mk_path_app(&lifted2, sigma[i], &mk_bvar(0))).collect();
  let phi = Expr::lam(
    y_name,
    gamma2.clone(),
    mk_tuple(&lifted, &comps),
    BinderInfo::Default,
  );
  let paths: Vec<(Expr, Expr)> =
    (0..n).map(|i| mk_path_proof(d2, sigma[i])).collect();
  let mono_phi = mk_mono_tree_over(
    &gamma2,
    &lgamma2,
    &d2.packed_po(),
    d,
    &paths.iter().map(|p| p.1.clone()).collect::<Vec<_>>(),
    &paths.iter().map(|p| p.0.clone()).collect::<Vec<_>>(),
  );
  let po_d = to_po(d.lattice, &s.lvls[k], &s.leaves[k], &d.insts[k]);
  let mut us = Vec::new();
  for nm in compose_levels {
    if *nm == root("u") {
      us.push(lgamma2.clone());
    } else if *nm == root("v") {
      us.push(lgamma.clone());
    } else if *nm == root("w") {
      us.push(s.lvls[k].clone());
    } else {
      return Err("monotone_compose: unexpected universe parameter".into());
    }
  }
  Ok(mk_app_n(
    cnst(&n_mono_compose(), &us),
    &[
      gamma2,
      d2.packed_po(),
      gamma,
      d.packed_po(),
      s.leaves[k].clone(),
      po_d,
      phi,
      f.clone(),
      mono_phi,
      h.clone(),
    ],
  ))
}

/// `decodeMonoTree`.
pub fn decode_mono_tree(
  l: &PfLayout,
  e: &Expr,
) -> Option<(OrderData, Vec<Expr>, Vec<Expr>)> {
  let (h, us, args) = const_app(e)?;
  if !(h == n_mono_mk() && args.len() == 10) {
    return None;
  }
  let d = decode_order_data(l, &args[5])?;
  let ts = decode_spine(
    PackKind::Pprod,
    l.n,
    &mk_node(
      PackKind::Pprod,
      &us.first().cloned().unwrap_or_else(Level::zero),
      &us.get(1).cloned().unwrap_or_else(Level::zero),
      &args[0],
      &args[1],
    ),
  )?;
  if !l.is_clique(&ts) {
    return None;
  }
  let d = OrderData { tspine: ts, ..d };
  let mut fs = Vec::new();
  let mut hs = Vec::new();
  let mut cur = e.clone();
  for _ in 0..l.n - 1 {
    let (h2, _, a2) = const_app(&cur)?;
    if !(h2 == n_mono_mk() && a2.len() == 10) {
      return None;
    }
    fs.push(a2[6].clone());
    hs.push(a2[8].clone());
    if fs.len() + 1 == l.n {
      fs.push(a2[7].clone());
      hs.push(a2[9].clone());
    }
    cur = a2[9].clone();
  }
  if fs.len() != l.n {
    return None;
  }
  if alpha_eq(&mk_mono_tree(&d, &fs, &hs), e) {
    Some((d, fs, hs))
  } else {
    None
  }
}

/// `pfLayout`.
pub fn pf_layout(
  members: &[Decl],
  packed: &Decl,
  sigma: &[usize],
  new_packed_name: &Name,
) -> R<PfLayout> {
  let n = members.len();
  if !(n >= 2 && sigma.len() == n && is_perm(sigma)) {
    return Err("pfLayout: bad permutation".into());
  }
  let m = forall_arity(&packed.typ);
  let (_, gamma) = peel_foralls(m, &packed.typ);
  let Some(s) = decode_spine(PackKind::Pprod, n, &gamma) else {
    return Err("pfLayout: the packed type is not Lean's PProd packing".into());
  };
  let mut qss = Vec::new();
  for (i, d) in members.iter().enumerate() {
    let (ps, body) = peel_lams(lam_arity(&d.value), &d.value);
    let (h, _) = get_app_fn_args(&strip_mdata(&body));
    let (steps, base) = proj_chain(&h);
    let Some((c, _, args)) = const_app(&base) else {
      return Err(format!(
        "pfLayout: member {i} is not a projection of the fixpoint"
      ));
    };
    if !(c == packed.name && args.len() == m) {
      return Err(format!(
        "pfLayout: member {i} is not a projection of the fixpoint"
      ));
    }
    match path_prefix(n, &steps) {
      Some((j, len)) => {
        if !(j == i && len == steps.len()) {
          return Err(format!("pfLayout: member {i} projects component {j}"));
        }
      },
      None => return Err(format!("pfLayout: member {i}: not a path")),
    }
    let mut qs = Vec::new();
    for a in &args {
      match bvar_idx(&strip_mdata(a)) {
        Some(b) => {
          if b < ps.len() {
            qs.push(ps.len() - 1 - b)
          } else {
            return Err("pfLayout: fixed argument".into());
          }
        },
        None => {
          return Err("pfLayout: a fixed argument is not a parameter".into());
        },
      }
    }
    if !no_dups(&qs) {
      return Err(
        "pfLayout: distinct fixed parameters alias the same member binder"
          .into(),
      );
    }
    qss.push(qs);
  }
  if !eq_sorted(&qss[0]) {
    return Err(
      "pfLayout: the fixed parameters are not in the first member's order"
        .into(),
    );
  }
  let qg = qss[inv_perm(sigma)[0]].clone();
  let fixed_perm = sort_idx_by_key(m, &|a| qg[a]);
  Ok(PfLayout {
    n,
    sigma: sigma.to_vec(),
    packed_name: packed.name.clone(),
    new_packed_name: new_packed_name.clone(),
    num_fixed: m,
    fixed_perm,
    leaves: s.leaves.clone(),
    spine: s,
    proof_perm: FxHashMap::default(),
    compose_levels: Vec::new(),
    member_fixed: qss,
  })
}

// ---------------------------------------------------------------------------
// PFConjugation
// ---------------------------------------------------------------------------

fn project(s: &Name, i: usize, base: &Expr) -> Option<Expr> {
  let (c, _, args) = const_app(&strip_mdata(base))?;
  if !(((*s == n_pprod() && c == n_pprod_mk())
    || (*s == n_and() && c == n_and_intro()))
    && args.len() == 4
    && i < 2)
  {
    return None;
  }
  args.get(2 + i).cloned()
}

/// `reduceConjugation.reduceHead`.
pub fn reduce_head(e: &Expr) -> Expr {
  match e.as_data() {
    ExprData::Proj(s, i, x, _) => {
      project(s, crate::compile::pass3::expr::nat_usize(i), x)
        .unwrap_or_else(|| e.clone())
    },
    _ => {
      let (h, args) = get_app_fn_args(e);
      if let ExprData::Const(c, _, _) = h.as_data()
        && (*c == n_pprod_fst() || *c == n_pprod_snd())
        && args.len() >= 3
        && let Some(value) =
          project(&n_pprod(), if *c == n_pprod_fst() { 0 } else { 1 }, &args[2])
      {
        return mk_app_n(value, &args[3..]);
      }
      e.clone()
    },
  }
}

/// `substitutePFInput`.
pub fn substitute_pf_input(
  input: &Spine,
  sigma: &[usize],
  body: &Expr,
) -> R<Expr> {
  fn go(input: &Spine, sigma: &[usize], e: &Expr, depth: usize) -> R<Expr> {
    let source = input.map_leaves(&|x| lift(x, depth + 1));
    let target = source.permute(sigma);
    if let Some((spine, j, base)) = decode_path_app(input.size(), e)
      && alpha_eq(&base, &mk_bvar(depth))
    {
      if !alpha_eq(
        &norm_order_alias(&spine.typ()),
        &norm_order_alias(&source.typ()),
      ) {
        return Err("PF conjugation: recursive path has a foreign type".into());
      }
      return Ok(mk_path_app(&spine.permute(sigma), sigma[j], &base));
    }
    if let ExprData::Proj(..) = e.as_data() {
      let (steps, base) = proj_chain(e);
      if alpha_eq(&base, &mk_bvar(depth)) {
        let Some((j, used)) = path_prefix(input.size(), &steps) else {
          return Err(
            "PF conjugation: recursive projection is not a component path"
              .into(),
          );
        };
        if !steps_fit(&source, j, &extract(&steps, 0, used)) {
          return Err(
            "PF conjugation: recursive projection has a foreign structure"
              .into(),
          );
        }
        let mut st = target.proj_steps(sigma[j]);
        st.extend(extract(&steps, used, steps.len()));
        return Ok(apply_projs(&st, &base));
      }
    }
    Ok(match e.as_data() {
      ExprData::Bvar(..) => {
        if is_bvar(e, depth) {
          let cs: Vec<Expr> = sigma
            .iter()
            .map(|&j| apply_projs(&target.proj_steps(j), e))
            .collect();
          mk_tuple(&source, &cs)
        } else {
          e.clone()
        }
      },
      ExprData::App(f, a, _) => {
        Expr::app(go(input, sigma, f, depth)?, go(input, sigma, a, depth)?)
      },
      ExprData::Proj(s, i, x, _) => {
        Expr::proj(s.clone(), i.clone(), go(input, sigma, x, depth)?)
      },
      ExprData::Lam(n, t, b, bi, _) => Expr::lam(
        n.clone(),
        go(input, sigma, t, depth)?,
        go(input, sigma, b, depth + 1)?,
        bi.clone(),
      ),
      ExprData::ForallE(n, t, b, bi, _) => Expr::all(
        n.clone(),
        go(input, sigma, t, depth)?,
        go(input, sigma, b, depth + 1)?,
        bi.clone(),
      ),
      ExprData::LetE(n, t, v, b, nd, _) => Expr::letE(
        n.clone(),
        go(input, sigma, t, depth)?,
        go(input, sigma, v, depth)?,
        go(input, sigma, b, depth + 1)?,
        *nd,
      ),
      ExprData::Mdata(d, x, _) => {
        Expr::mdata(d.clone(), go(input, sigma, x, depth)?)
      },
      _ => e.clone(),
    })
  }
  go(input, sigma, body, 0)
}

/// `conjugatePF`.
pub fn conjugate_pf(n: usize, sigma: &[usize], functional: &Expr) -> R<Expr> {
  if !(n >= 2 && sigma.len() == n && is_perm(sigma)) {
    return Err("PF conjugation: invalid permutation".into());
  }
  let (name, domain, body, bi) = match strip_mdata(functional).as_data() {
    ExprData::Lam(nm, d, b, bi, _) => {
      (nm.clone(), d.clone(), b.clone(), bi.clone())
    },
    _ => return Err("PF conjugation: missing recursive binder".into()),
  };
  let Some(input) = decode_spine(PackKind::Pprod, n, &domain) else {
    return Err(
      "PF conjugation: recursive binder is not a packed product".into(),
    );
  };
  let Some((output, components)) = decode_tuple(n, &strip_mdata(&body)) else {
    return Err("PF conjugation: missing encoded result tuple".into());
  };
  if !alpha_eq(
    &norm_order_alias(&output.typ()),
    &norm_order_alias(&lift(&input.typ(), 1)),
  ) {
    return Err("PF conjugation: input and output packing differ".into());
  }
  let target = input.permute(sigma);
  let mut cs = Vec::new();
  for c in &components {
    cs.push(substitute_pf_input(&input, sigma, c)?);
  }
  Ok(Expr::lam(
    name,
    target.typ(),
    mk_tuple(&output.permute(sigma), &permute(sigma, &cs)),
    bi,
  ))
}

/// `conjugatePFInput`.
pub fn conjugate_pf_input(
  input: &Spine,
  sigma: &[usize],
  functional: &Expr,
) -> R<Expr> {
  if !(input.size() >= 2 && sigma.len() == input.size() && is_perm(sigma)) {
    return Err("PF input conjugation: invalid permutation".into());
  }
  let (name, domain, body, bi) = match strip_mdata(functional).as_data() {
    ExprData::Lam(nm, d, b, bi, _) => {
      (nm.clone(), d.clone(), b.clone(), bi.clone())
    },
    _ => return Err("PF input conjugation: missing recursive binder".into()),
  };
  if !alpha_eq(&norm_order_alias(&domain), &norm_order_alias(&input.typ())) {
    return Err("PF input conjugation: wrong binder domain".into());
  }
  let Some(actual_input) = decode_spine(PackKind::Pprod, input.size(), &domain)
  else {
    return Err("PF input conjugation: missing functional packing".into());
  };
  let target = actual_input.permute(sigma);
  Ok(Expr::lam(
    name,
    target.typ(),
    substitute_pf_input(&actual_input, sigma, &body)?,
    bi,
  ))
}

/// `ownedMonoPremise`.
fn owned_mono_premise(domain: &Name, order: &Name, e: &Expr) -> bool {
  match e.as_data() {
    ExprData::ForallE(_, t, b, _, _) => {
      !mentions_fvar(domain, t)
        && !mentions_fvar(order, t)
        && owned_mono_premise(domain, order, b)
    },
    _ => match const_app(&strip_mdata(e)) {
      Some((c, _, args)) => {
        c == n_monotone()
          && args.len() == 5
          && alpha_eq(&args[0], &fvar(domain))
          && alpha_eq(&args[1], &fvar(order))
      },
      None => false,
    },
  }
}

/// `transportOwnedMono`.
fn transport_owned_mono(
  tm: &mut Tm,
  l: &PfLayout,
  const_of: ConstOf<'_>,
  fuel: usize,
  e: &Expr,
) -> R<Expr> {
  if fuel == 0 {
    return Err("PF proof ownership: recursion bound exhausted".into());
  }
  let fuel = fuel - 1;
  if let Some((data, j)) = decode_path_proof(l, e) {
    return Ok(mk_path_proof(&data.permute(&l.sigma), l.sigma[j]).0);
  }
  match e.as_data() {
    ExprData::Lam(n, t, b, bi, _) => {
      return Ok(Expr::lam(
        n.clone(),
        t.clone(),
        transport_owned_mono(tm, l, const_of, fuel, b)?,
        bi.clone(),
      ));
    },
    ExprData::Mdata(d, x, _) => {
      return Ok(Expr::mdata(
        d.clone(),
        transport_owned_mono(tm, l, const_of, fuel, x)?,
      ));
    },
    _ => {},
  }
  let Some((name, levels, args)) = const_app(e) else {
    return Err(
      "PF proof ownership: expected an applied monotonicity theorem".into(),
    );
  };
  let Some(info) = const_of(&name) else {
    return Err(format!(
      "PF proof ownership: missing theorem {}",
      name_to_string(&name)
    ));
  };
  let typ = subst_levels(info.get_level_params(), &levels, info.get_type());
  let (parameters, conclusion) = open_binders(tm, false, args.len(), &typ)?;
  let Some((head, _, result_args)) = const_app(&conclusion) else {
    return Err(
      "PF proof ownership: theorem conclusion is not monotonicity".into(),
    );
  };
  if !(head == n_monotone() && result_args.len() == 5) {
    return Err(
      "PF proof ownership: theorem conclusion is not monotonicity".into(),
    );
  }
  let ExprData::Fvar(domain, _) = result_args[0].as_data() else {
    return Err("PF proof ownership: domain is not a theorem parameter".into());
  };
  let ExprData::Fvar(order, _) = result_args[1].as_data() else {
    return Err("PF proof ownership: order is not a theorem parameter".into());
  };
  if !(!mentions_fvar(domain, &result_args[2])
    && !mentions_fvar(order, &result_args[2])
    && !mentions_fvar(domain, &result_args[3])
    && !mentions_fvar(order, &result_args[3]))
  {
    return Err(
      "PF proof ownership: conclusion output depends on the recursive-domain parameter".into(),
    );
  }
  let Some(domain_index) = parameters.iter().position(|p| p.fvar == *domain)
  else {
    return Err("PF proof ownership: missing domain parameter".into());
  };
  let Some(order_index) = parameters.iter().position(|p| p.fvar == *order)
  else {
    return Err("PF proof ownership: missing order parameter".into());
  };
  let Some(spine) = decode_spine(PackKind::Pprod, l.n, &args[domain_index])
  else {
    return Err(
      "PF proof ownership: recursive domain is not the decoded packing".into(),
    );
  };
  let Some(data) = decode_order_data(l, &args[order_index]) else {
    return Err(
      "PF proof ownership: recursive order is not the decoded order".into(),
    );
  };
  if !(l.is_clique(&spine)
    && alpha_eq(
      &norm_order_alias(&spine.typ()),
      &norm_order_alias(&data.spine.typ()),
    ))
  {
    return Err("PF proof ownership: domain/order mismatch".into());
  }
  let target = OrderData { tspine: spine.clone(), ..data }.permute(&l.sigma);
  let mut args2 = args.clone();
  for i in 0..parameters.len() {
    let parameter = &parameters[i];
    if i == domain_index {
      args2[i] = target.tspine.typ();
    } else if i == order_index {
      args2[i] = target.packed_po();
    } else if mentions_fvar(domain, &parameter.typ)
      || mentions_fvar(order, &parameter.typ)
    {
      if owned_mono_premise(domain, order, &parameter.typ) {
        args2[i] = transport_owned_mono(tm, l, const_of, fuel, &args[i])?;
      } else {
        let (input, output) = match strip_mdata(&parameter.typ).as_data() {
          ExprData::ForallE(_, i2, o, _, _) => (i2.clone(), o.clone()),
          _ => {
            return Err(
              "PF proof ownership: unsupported dependent argument role".into(),
            );
          },
        };
        if !(alpha_eq(&input, &fvar(domain))
          && !mentions_fvar(domain, &output)
          && !mentions_fvar(order, &output)
          && loose_all_at_least(&output, 1))
        {
          return Err(
            "PF proof ownership: unsupported dependent functional role".into(),
          );
        }
        args2[i] = conjugate_pf_input(&spine, &l.sigma, &args[i])?;
      }
    }
  }
  Ok(mk_app_n(cnst(&name, &levels), &args2))
}

/// `conjugatePFMonoChecked`.
fn conjugate_pf_mono_checked(
  tm: &mut Tm,
  l: &PfLayout,
  const_of: ConstOf<'_>,
  proof: &Expr,
) -> R<Expr> {
  let Some((data, fs, hs)) = decode_mono_tree(l, proof) else {
    return Err(
      "PF conjugation: monotonicity proof is not a decoded tuple tree".into(),
    );
  };
  let target = data.permute(&l.sigma);
  let mut fs2 = Vec::new();
  for f in &fs {
    fs2.push(conjugate_pf_input(&data.tspine, &l.sigma, f)?);
  }
  let mut hs2 = Vec::new();
  for k in 0..l.n {
    let saved = tm.next;
    match transport_owned_mono(tm, l, const_of, DEFAULT_FUEL, &hs[k]) {
      Ok(h) => hs2.push(h),
      Err(reason) => {
        tm.next = saved;
        hs2.push(mk_compose_fallback(
          &l.sigma,
          &data,
          &target,
          k,
          &fs[k],
          &hs[k],
          &l.compose_levels,
        )?);
        tm.fallbacks.push(format!("monotonicity proof {k}: {reason}"));
      },
    }
  }
  Ok(mk_mono_tree(&target, &permute(&l.sigma, &fs2), &permute(&l.sigma, &hs2)))
}

/// `rewritePFPackedUses`.
pub fn rewrite_pf_packed_uses(l: &PfLayout, e: &Expr) -> R<Expr> {
  fn go(l: &PfLayout, fuel: usize, e: &Expr) -> R<Expr> {
    if fuel == 0 {
      return Err("PF ownership: packed-use recursion bound exhausted".into());
    }
    let fuel = fuel - 1;
    if let Some((name, levels, args)) = const_app(e)
      && name == l.packed_name
    {
      if args.len() != l.num_fixed {
        return Err(
          "PF ownership: partial/over-applied packed declaration".into(),
        );
      }
      let mut args2 = Vec::new();
      for a in &args {
        args2.push(go(l, fuel, a)?);
      }
      let rev: Vec<Expr> = args.iter().rev().cloned().collect();
      let source = l.spine.map_leaves(&|t| instantiate_rev(t, &rev));
      let target = source.permute(&l.sigma);
      let value = mk_app_n(
        cnst(&l.new_packed_name, &levels),
        &l.fixed_perm.iter().map(|&i| args2[i].clone()).collect::<Vec<_>>(),
      );
      let cs: Vec<Expr> = l
        .sigma
        .iter()
        .map(|&j| apply_projs(&target.proj_steps(j), &value))
        .collect();
      return Ok(mk_tuple(&source, &cs));
    }
    Ok(match e.as_data() {
      ExprData::App(f, a, _) => {
        let f2 = go(l, fuel, f)?;
        let a2 = go(l, fuel, a)?;
        if f2 == *f && a2 == *a {
          return Ok(e.clone());
        }
        reduce_head(&Expr::app(f2, a2))
      },
      ExprData::Proj(s, i, x, _) => {
        let x2 = go(l, fuel, x)?;
        if x2 == *x {
          return Ok(e.clone());
        }
        reduce_head(&Expr::proj(s.clone(), i.clone(), x2))
      },
      ExprData::Lam(n, t, b, bi, _) => {
        Expr::lam(n.clone(), go(l, fuel, t)?, go(l, fuel, b)?, bi.clone())
      },
      ExprData::ForallE(n, t, b, bi, _) => {
        Expr::all(n.clone(), go(l, fuel, t)?, go(l, fuel, b)?, bi.clone())
      },
      ExprData::LetE(n, t, v, b, nd, _) => Expr::letE(
        n.clone(),
        go(l, fuel, t)?,
        go(l, fuel, v)?,
        go(l, fuel, b)?,
        *nd,
      ),
      ExprData::Mdata(d, x, _) => Expr::mdata(d.clone(), go(l, fuel, x)?),
      _ => e.clone(),
    })
  }
  go(l, DEFAULT_FUEL, e)
}

/// `conjugatePFStatement`.
fn conjugate_pf_statement(l: &PfLayout, typ: &Expr) -> R<Expr> {
  let Some((head, levels, args)) = const_app(&strip_mdata(typ)) else {
    return Err("PF ownership: expected a monotonicity statement".into());
  };
  if !(head == n_monotone() && args.len() == 5) {
    return Err("PF ownership: expected a monotonicity statement".into());
  }
  let Some(input) = decode_spine(PackKind::Pprod, l.n, &args[0]) else {
    return Err("PF ownership: statement has no input packing".into());
  };
  let Some(output) = decode_spine(PackKind::Pprod, l.n, &args[2]) else {
    return Err("PF ownership: statement has no output packing".into());
  };
  let Some(data) = decode_order_data(l, &args[1]) else {
    return Err("PF ownership: statement has no packed input order".into());
  };
  let data = OrderData { tspine: output.clone(), ..data };
  if !(l.is_clique(&input)
    && alpha_eq(
      &norm_order_alias(&input.typ()),
      &norm_order_alias(&output.typ()),
    )
    && alpha_eq(&args[3], &data.po_tree(0)))
  {
    return Err("PF ownership: statement input/output orders differ".into());
  }
  let target = data.permute(&l.sigma);
  Ok(mk_app_n(
    cnst(&head, &levels),
    &[
      input.permute(&l.sigma).typ(),
      target.packed_po(),
      target.tspine.typ(),
      target.po_tree(0),
      conjugate_pf(l.n, &l.sigma, &args[4])?,
    ],
  ))
}

struct PfEquationStep {
  left: Expr,
  right: Expr,
  proof: Expr,
}

/// `conjugatePFEquationProof`.
fn conjugate_pf_equation_proof(
  l: &PfLayout,
  component: usize,
  source_fix: &Expr,
  target_fix: &Expr,
  fuel: usize,
  e: &Expr,
) -> R<PfEquationStep> {
  if fuel == 0 {
    return Err(
      "PF equation ownership: proof recursion bound exhausted".into(),
    );
  }
  let fuel = fuel - 1;
  let Some((head, levels, args)) = const_app(&strip_mdata(e)) else {
    return Err("PF equation ownership: unsupported proof constructor".into());
  };
  if head == ln("id") && args.len() == 2 {
    return conjugate_pf_equation_proof(
      l, component, source_fix, target_fix, fuel, &args[1],
    );
  }
  if head == ln("Eq.trans") && args.len() == 6 {
    match const_app(&args[5]) {
      Some((last, _, last_args))
        if last == ln("Eq.refl") && last_args.len() == 2 => {},
      _ => {
        return Err(
          "PF equation ownership: non-reflexive final equation step".into(),
        );
      },
    }
    return conjugate_pf_equation_proof(
      l, component, source_fix, target_fix, fuel, &args[4],
    );
  }
  if (head == ln("Lean.Order.fix_eq")
    || head == ln("Lean.Order.lfp_monotone_fix"))
    && args.len() == 4
  {
    let Some((source_head, _, source_args)) = const_app(source_fix) else {
      return Err("PF equation ownership: missing source fixpoint".into());
    };
    let Some((_, _, target_args)) = const_app(target_fix) else {
      return Err("PF equation ownership: missing target fixpoint".into());
    };
    let expected = if source_head == n_order_fix() {
      ln("Lean.Order.fix_eq")
    } else {
      ln("Lean.Order.lfp_monotone_fix")
    };
    if !(head == expected
      && args.len() == source_args.len()
      && target_args.len() == 4
      && args.iter().zip(source_args.iter()).all(|(a, b)| alpha_eq(a, b)))
    {
      return Err(
        "PF equation ownership: equation belongs to another fixpoint".into(),
      );
    }
    return Ok(PfEquationStep {
      left: target_fix.clone(),
      right: Expr::app(target_args[2].clone(), target_fix.clone()),
      proof: mk_app_n(cnst(&head, &levels), &target_args),
    });
  }
  if head == ln("congrArg") && args.len() == 6 {
    let (binder, domain, body, bi) = match strip_mdata(&args[4]).as_data() {
      ExprData::Lam(b, d, x, bi, _) => {
        (b.clone(), d.clone(), x.clone(), bi.clone())
      },
      _ => {
        return Err(
          "PF equation ownership: congruence is not a member projection".into(),
        );
      },
    };
    let Some(source) = decode_spine(PackKind::Pprod, l.n, &domain) else {
      return Err(
        "PF equation ownership: congruence has no packed binder".into(),
      );
    };
    let (steps, base) = proj_chain(&body);
    let Some((index, used)) = path_prefix(l.n, &steps) else {
      return Err(
        "PF equation ownership: congruence is not a complete member path"
          .into(),
      );
    };
    if !(index == component
      && used == steps.len()
      && alpha_eq(&base, &mk_bvar(0))
      && steps_fit(&source, index, &steps))
    {
      return Err(
        "PF equation ownership: congruence selects another binder/component"
          .into(),
      );
    }
    let previous = conjugate_pf_equation_proof(
      l, component, source_fix, target_fix, fuel, &args[5],
    )?;
    let target = source.permute(&l.sigma);
    let projection = Expr::lam(
      binder,
      target.typ(),
      apply_projs(&target.proj_steps(l.sigma[component]), &mk_bvar(0)),
      bi,
    );
    return Ok(PfEquationStep {
      left: Expr::app(projection.clone(), previous.left.clone()),
      right: Expr::app(projection.clone(), previous.right.clone()),
      proof: mk_app_n(
        cnst(&head, &levels),
        &[
          target.typ(),
          args[1].clone(),
          previous.left,
          previous.right,
          projection,
          previous.proof,
        ],
      ),
    });
  }
  if head == ln("congrFun") && args.len() == 6 {
    let previous = conjugate_pf_equation_proof(
      l, component, source_fix, target_fix, fuel, &args[4],
    )?;
    return Ok(PfEquationStep {
      left: Expr::app(previous.left.clone(), args[5].clone()),
      right: Expr::app(previous.right.clone(), args[5].clone()),
      proof: mk_app_n(
        cnst(&head, &levels),
        &[
          args[0].clone(),
          args[1].clone(),
          previous.left,
          previous.right,
          previous.proof,
          args[5].clone(),
        ],
      ),
    });
  }
  Err(format!(
    "PF equation ownership: unsupported proof constructor {}",
    name_to_string(&head)
  ))
}

/// `conjugatePFEquation`.
fn conjugate_pf_equation(
  tm: &mut Tm,
  l: &PfLayout,
  members: &[Decl],
  source_packed: &Decl,
  target_packed: &Decl,
  lemma: &Decl,
  new_name: &Name,
) -> R<Decl> {
  let arity = forall_arity(&lemma.typ);
  let (parameters, statement) = open_binders(tm, false, arity, &lemma.typ)?;
  let Some((eq, _, eq_args)) = const_app(&statement) else {
    return Err("PF equation ownership: statement is not an equality".into());
  };
  if !(eq == ln("Eq") && eq_args.len() == 3) {
    return Err("PF equation ownership: statement is not an equality".into());
  }
  let Some((member_name, _, member_args)) = const_app(&eq_args[1]) else {
    return Err(
      "PF equation ownership: equality does not start at a member application"
        .into(),
    );
  };
  let Some(component) = members.iter().position(|m| m.name == member_name)
  else {
    return Err(
      "PF equation ownership: equality concerns another declaration".into(),
    );
  };
  let applied_member = beta_app(&members[component].value, &member_args);
  let (projection, _) = get_app_fn_args(&applied_member);
  let (_, base) = proj_chain(&projection);
  let Some((packed_name, _, fixed_args)) = const_app(&base) else {
    return Err("PF equation ownership: member has no packed root".into());
  };
  if !(packed_name == source_packed.name && fixed_args.len() == l.num_fixed) {
    return Err(
      "PF equation ownership: member uses another packed root".into(),
    );
  }
  let source_fix = beta_app(&source_packed.value, &fixed_args);
  let target_fix = beta_app(
    &target_packed.value,
    &l.fixed_perm.iter().map(|&i| fixed_args[i].clone()).collect::<Vec<_>>(),
  );
  let (binders, proof_body) = peel_lams(arity, &lemma.value);
  if binders.len() != arity {
    return Err(
      "PF equation ownership: proof telescope differs from its statement"
        .into(),
    );
  }
  let proof_body = inst_locals(&proof_body, &exprs(&parameters));
  let proof = conjugate_pf_equation_proof(
    l,
    component,
    &source_fix,
    &target_fix,
    DEFAULT_FUEL,
    &proof_body,
  )?;
  let value = close_binders(true, &parameters, &proof.proof)?;
  Ok(Decl { name: new_name.clone(), value, ..lemma.clone() })
}

/// `transportPF`.
#[allow(clippy::too_many_arguments)]
pub fn transport_pf(
  tm: &mut Tm,
  members: &[Decl],
  packed: &Decl,
  proofs: &[Decl],
  sigma: &[usize],
  new_packed_name: &Name,
  const_of: ConstOf<'_>,
  lemmas: &[(Decl, Name)],
) -> R<WfOutput> {
  let initial = pf_layout(members, packed, sigma, new_packed_name)?;
  let compose_levels = match const_of(&n_mono_compose()) {
    Some(info) => info.get_level_params().clone(),
    None => Vec::new(),
  };
  let proof_names: FxHashSet<Name> =
    proofs.iter().map(|p| p.name.clone()).collect();
  let (fixed, body) = open_binders(tm, true, initial.num_fixed, &packed.value)?;
  let fixed_names: Vec<Name> = fixed.iter().map(|f| f.fvar.clone()).collect();
  let mut uses: FxHashMap<Name, Vec<usize>> = FxHashMap::default();
  scan_proofs(&proof_names, &fixed_names, &body, &mut uses);
  let inverse_fixed = inv_perm(&initial.fixed_perm);
  let mut proof_perm: FxHashMap<Name, Vec<usize>> = FxHashMap::default();
  for (name, indices) in &uses {
    proof_perm.insert(
      name.clone(),
      sort_idx_by_key(indices.len(), &|a| inverse_fixed[indices[a]]),
    );
  }
  let l =
    PfLayout { compose_levels, proof_perm: proof_perm.clone(), ..initial };
  let typ = with_reordered_binders2(
    tm,
    false,
    l.num_fixed,
    &l.fixed_perm,
    &packed.typ,
    &mut |_, x| Ok(x.clone()),
    &mut |_, e| {
      let Some(spine) = decode_spine(PackKind::Pprod, l.n, &strip_mdata(e))
      else {
        return Err("PF ownership: packed result type is not a product".into());
      };
      if !l.is_clique(&spine) {
        return Err(
          "PF ownership: packed result type differs from the layout".into(),
        );
      }
      Ok(spine.permute(sigma).typ())
    },
  )?;
  let value = with_reordered_binders2(
    tm,
    true,
    l.num_fixed,
    &l.fixed_perm,
    &packed.value,
    &mut |_, x| Ok(x.clone()),
    &mut |_, e| {
      let Some((head, levels, args)) = const_app(&strip_mdata(e)) else {
        return Err(
          "PF ownership: packed value is not a fixpoint application".into(),
        );
      };
      if !((head == n_order_fix() || head == ln("Lean.Order.lfp_monotone"))
        && args.len() == 4)
      {
        return Err("PF ownership: unsupported fixpoint root".into());
      }
      let Some(spine) = decode_spine(PackKind::Pprod, l.n, &args[0]) else {
        return Err("PF ownership: fixpoint has no packed domain".into());
      };
      let Some((instance_name, instance_spine, instances)) =
        decode_inst_tree(l.n, &args[1])
      else {
        return Err(
          "PF ownership: fixpoint has no decoded instance tree".into(),
        );
      };
      if !(l.is_clique(&spine)
        && alpha_eq(
          &norm_order_alias(&spine.typ()),
          &norm_order_alias(&instance_spine.typ()),
        ))
      {
        return Err("PF ownership: fixpoint type/instance mismatch".into());
      }
      let Some((proof_name, proof_levels, proof_args)) = const_app(&args[3])
      else {
        return Err(
          "PF ownership: fixpoint proof is not an owned abstracted declaration"
            .into(),
        );
      };
      if !proof_names.contains(&proof_name) {
        return Err(
          "PF ownership: fixpoint proof is not among the owned declarations"
            .into(),
        );
      }
      let permutation =
        proof_perm.get(&proof_name).cloned().unwrap_or_default();
      if proof_args.len() != permutation.len() {
        return Err("PF ownership: proof fixed-argument arity mismatch".into());
      }
      let proof = mk_app_n(
        cnst(&proof_name, &proof_levels),
        &permutation.iter().map(|&i| proof_args[i].clone()).collect::<Vec<_>>(),
      );
      Ok(mk_app_n(
        cnst(&head, &levels),
        &[
          spine.permute(sigma).typ(),
          mk_inst_tree(
            &instance_name,
            &instance_spine.permute(sigma),
            &permute(sigma, &instances),
          ),
          conjugate_pf(l.n, sigma, &args[2])?,
          proof,
        ],
      ))
    },
  )?;
  let mut out: Vec<Transported> = vec![Transported::ok(Decl {
    name: new_packed_name.clone(),
    typ: typ.clone(),
    value: value.clone(),
    ..packed.clone()
  })];
  for proof in proofs {
    let permutation = proof_perm.get(&proof.name).cloned().unwrap_or_default();
    let t = with_reordered_binders2(
      tm,
      false,
      permutation.len(),
      &permutation,
      &proof.typ,
      &mut |_, x| Ok(x.clone()),
      &mut |_, e| conjugate_pf_statement(&l, e),
    )?;
    let before = tm.fallbacks.len();
    let v = with_reordered_binders2(
      tm,
      true,
      permutation.len(),
      &permutation,
      &proof.value,
      &mut |_, x| Ok(x.clone()),
      &mut |tm, e| conjugate_pf_mono_checked(tm, &l, const_of, e),
    )?;
    let causes = tm.fallbacks[before..].to_vec();
    out.push(Transported {
      decl: Decl { typ: t, value: v, ..proof.clone() },
      fallback: if causes.is_empty() { None } else { Some(causes.join("; ")) },
    });
  }
  for member in members {
    out.push(Transported::ok(Decl {
      typ: rewrite_pf_packed_uses(&l, &member.typ)?,
      value: rewrite_pf_packed_uses(&l, &member.value)?,
      ..member.clone()
    }));
  }
  let target_packed = Decl {
    name: new_packed_name.clone(),
    typ: typ.clone(),
    value: value.clone(),
    ..packed.clone()
  };
  for (lemma, name) in lemmas {
    let d = conjugate_pf_equation(
      tm,
      &l,
      members,
      packed,
      &target_packed,
      lemma,
      name,
    )?;
    out.push(Transported::ok(d));
  }
  let order = const_occurrences(&|n| proof_names.contains(n), &value);
  let rest: Vec<Name> = proofs
    .iter()
    .map(|p| p.name.clone())
    .filter(|n| !order.contains(n))
    .collect();
  let numbered: Vec<(Name, Name)> = order
    .iter()
    .chain(rest.iter())
    .enumerate()
    .map(|(i, n)| {
      (n.clone(), mk_str(new_packed_name, &format!("_proof_{}", i + 1)))
    })
    .collect();
  let lemma_renames: Vec<(Name, Name)> = lemmas
    .iter()
    .filter(|(d, n)| d.name != *n)
    .map(|(d, n)| (d.name.clone(), n.clone()))
    .collect();
  Ok(finish_renames(out, packed, new_packed_name, numbered, lemma_renames))
}
