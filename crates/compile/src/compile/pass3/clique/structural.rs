//! The structural transport (a port of `Ix/Compile/Clique/Structural.lean`).

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::env::{ConstantInfo, Expr, ExprData, Name, NameData};

use super::basic::*;
use super::packing::*;
use super::telescope::*;
use super::wf::Transported;
use crate::compile::pass3::expr::{get_app_fn_args, nat_usize, strip_mdata};

#[derive(Clone, Copy, Debug)]
pub struct BlockAux {
  pub pos: usize,
  pub is_brec_on: bool,
}

#[derive(Clone, Debug)]
pub struct Group {
  pub members: Vec<usize>,
  pub arity: usize,
  pub spine: Spine,
  pub perm: Vec<usize>,
}

impl Group {
  pub fn size(&self) -> usize {
    self.members.len()
  }
  pub fn canon_spine(&self) -> Spine {
    self.spine.permute(&self.perm)
  }
}

fn empty_spine() -> Spine {
  Spine { kind: PackKind::Psum, leaves: Vec::new(), lvls: Vec::new() }
}

pub struct StructLayout<'a> {
  pub n: usize,
  pub sigma: Vec<usize>,
  pub const_of: ConstOf<'a>,
  pub num_params: usize,
  pub num_motives: usize,
  pub aux: FxHashMap<Name, BlockAux>,
  pub groups: Vec<Group>,
  pub f_names: FxHashSet<Name>,
  pub num_fixed: usize,
  pub fixed_perm: Vec<usize>,
  pub matchers: FxHashSet<Name>,
  pub num_fun_types: usize,
  pub member_fixed: Vec<Vec<usize>>,
  pub f_depth: FxHashMap<Name, (usize, usize)>,
  pub check_ownership: bool,
}

impl StructLayout<'_> {
  pub fn fun_perm(&self) -> Vec<usize> {
    inv_perm(&self.sigma)
  }

  /// `isBelowTy`.
  pub fn is_below_ty(&self, ty: &Expr) -> bool {
    match const_app(&strip_mdata(ty)) {
      Some((c, _, _)) => match self.aux.get(&c) {
        Some(a) => !a.is_brec_on,
        None => false,
      },
      None => false,
    }
  }

  /// `brecOnCount`.
  pub fn brec_on_count(&self, e: &Expr) -> usize {
    match e.as_data() {
      ExprData::Const(c, _, _) => match self.aux.get(c) {
        Some(a) => usize::from(a.is_brec_on),
        None => 0,
      },
      ExprData::App(f, a, _) => self.brec_on_count(f) + self.brec_on_count(a),
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        self.brec_on_count(t) + self.brec_on_count(b)
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        self.brec_on_count(t) + self.brec_on_count(v) + self.brec_on_count(b)
      },
      ExprData::Proj(_, _, x, _) | ExprData::Mdata(_, x, _) => {
        self.brec_on_count(x)
      },
      _ => 0,
    }
  }

  /// `elimShape?` (the motives with their arities).
  pub fn elim_motives(&self, c: &Name) -> Option<Vec<(usize, usize)>> {
    let ci = (self.const_of)(c)?;
    let ty = ci.get_type().clone();
    let ar = forall_arity(&ty);
    let (ps, _) = peel_foralls(ar, &ty);
    let mut motives: Vec<(usize, usize)> = Vec::new();
    for k in 0..ps.len() {
      let pt = &ps[k].1;
      let fc = forall_arity(pt);
      let (_, concl) = peel_foralls(fc, pt);
      if let Some(i) = bvar_idx(&get_app_fn_args(&strip_mdata(&concl)).0)
        && i >= fc
        && i - fc < k
      {
        let mk = k - 1 - (i - fc);
        if !motives.iter().any(|m| m.0 == mk) {
          motives.push((mk, forall_arity(&ps[mk].1)));
        }
      }
    }
    Some(motives)
  }
}

// ---------------------------------------------------------------------------
// Paths
// ---------------------------------------------------------------------------

/// `projChain`: steps innermost first, and the base.
pub fn proj_chain(e: &Expr) -> (Vec<(Name, usize)>, Expr) {
  match e.as_data() {
    ExprData::Proj(s, i, x, _) => {
      let (mut st, b) = proj_chain(x);
      st.push((s.clone(), nat_usize(i)));
      (st, b)
    },
    ExprData::Mdata(_, x, _) => proj_chain(x),
    _ => (Vec::new(), e.clone()),
  }
}

/// `pathPrefix`.
pub fn path_prefix(
  n: usize,
  steps: &[(Name, usize)],
) -> Option<(usize, usize)> {
  if n < 2 {
    return Some((0, 0));
  }
  let k = steps.iter().take_while(|s| s.1 == 1).count();
  if k + 1 < n {
    if k < steps.len() {
      if steps[k].1 == 0 { Some((k, k + 1)) } else { None }
    } else {
      None
    }
  } else {
    Some((n - 1, n - 1))
  }
}

/// `stepsFit`.
pub fn steps_fit(s: &Spine, idx: usize, steps: &[(Name, usize)]) -> bool {
  let a: Vec<Name> = s.proj_steps(idx).into_iter().map(|x| x.0).collect();
  let b: Vec<Name> = steps.iter().map(|x| x.0.clone()).collect();
  a == b
}

/// `transportPath`.
pub fn transport_path(
  g: &Group,
  steps: &[(Name, usize)],
) -> R<Vec<(Name, usize)>> {
  if g.size() < 2 {
    return Ok(steps.to_vec());
  }
  let Some((idx, len)) = path_prefix(g.size(), steps) else {
    return Err(
      "grammar: a projection of a packed value that is not a path".into(),
    );
  };
  let part = extract(steps, 0, len);
  if !steps_fit(&g.spine, idx, &part) {
    return Err(
      "grammar: a path whose projections are not the packing's".into(),
    );
  }
  let mut out = g.canon_spine().proj_steps(g.perm[idx]);
  out.extend(extract(steps, len, steps.len()));
  Ok(out)
}

#[derive(Clone, Debug)]
pub enum PStep {
  Proj(Name, usize),
  App(Expr),
}

/// `pathChain`.
pub fn path_chain(e: &Expr) -> (Vec<PStep>, Expr) {
  match e.as_data() {
    ExprData::Proj(s, i, x, _) => {
      let (mut st, b) = path_chain(x);
      st.push(PStep::Proj(s.clone(), nat_usize(i)));
      (st, b)
    },
    ExprData::App(f, a, _) => {
      let (mut st, b) = path_chain(f);
      st.push(PStep::App(a.clone()));
      (st, b)
    },
    ExprData::Mdata(_, x, _) => path_chain(x),
    _ => (Vec::new(), e.clone()),
  }
}

pub fn apply_steps(steps: &[PStep], e: &Expr) -> Expr {
  steps.iter().fold(e.clone(), |acc, st| match st {
    PStep::Proj(s, i) => proj(s, *i, acc),
    PStep::App(a) => Expr::app(acc, a.clone()),
  })
}

/// `projPrefix`.
pub fn proj_prefix(steps: &[PStep]) -> (Vec<(Name, usize)>, Vec<PStep>) {
  let mut acc = Vec::new();
  for i in 0..steps.len() {
    match &steps[i] {
      PStep::Proj(s, j) => acc.push((s.clone(), *j)),
      PStep::App(_) => return (acc, steps[i..].to_vec()),
    }
  }
  (acc, Vec::new())
}

/// `belowPath`.
pub fn below_path(
  tm: &mut Tm,
  l: &StructLayout<'_>,
  ty: &Expr,
  steps: &[PStep],
) -> R<Option<Vec<PStep>>> {
  let Some((c, us, args)) = const_app(ty) else { return Ok(None) };
  let Some(a) = l.aux.get(&c) else { return Ok(None) };
  if a.is_brec_on || args.len() < l.num_params + l.num_motives {
    return Ok(None);
  }
  let mut cans: Vec<Name> = Vec::new();
  let mut args2 = args.clone();
  for j in 0..l.num_motives {
    let f = tm.fresh();
    args2[l.num_params + j] = fvar(&f);
    cans.push(f);
  }
  let mut cur = mk_app_n(cnst(&c, &us), &args2);
  for t in 0..steps.len() {
    let w = whnf(l.const_of, WHNF_FUEL, &cur);
    match &steps[t] {
      PStep::Proj(s, i) => match decode_node(PackKind::Pprod, &w) {
        Some((_, _, a, b)) => {
          let is_and = match const_app(&w) {
            Some((h, _, _)) => h == n_and(),
            None => false,
          };
          if (*s == n_and()) != is_and {
            return Err(
              "grammar: a projection into a below dictionary whose structure is not the node's"
                .into(),
            );
          }
          cur = if *i == 0 { a } else { b };
        },
        None => {
          return Err(
            "grammar: a projection into a below dictionary that the walk cannot follow"
              .into(),
          );
        },
      },
      PStep::App(x) => match strip_mdata(&w).as_data() {
        ExprData::ForallE(_, _, b, _, _) => {
          cur = instantiate_rev(b, std::slice::from_ref(x))
        },
        _ => {
          return Err(
            "grammar: an application inside a below dictionary that the walk cannot follow"
              .into(),
          );
        },
      },
    }
    if let ExprData::Fvar(f, _) =
      get_app_fn_args(&strip_mdata(&cur)).0.as_data()
    {
      match cans.iter().position(|x| x == f) {
        Some(j) => {
          let g = &l.groups[j];
          let (projs, tail) = proj_prefix(&extract(steps, t + 1, steps.len()));
          let projs2 = transport_path(g, &projs)?;
          let mut out = extract(steps, 0, t + 1);
          out.extend(projs2.into_iter().map(|(s, i)| PStep::Proj(s, i)));
          out.extend(tail);
          return Ok(Some(out));
        },
        None => {
          return Err(
            "grammar: a path into a below dictionary that reaches a foreign variable"
              .into(),
          );
        },
      }
    }
  }
  Ok(None)
}

// ---------------------------------------------------------------------------
// Φ_σ
// ---------------------------------------------------------------------------

pub type Ctx = Vec<(Expr, bool)>;

fn ctx_hash(ctx: &Ctx) -> Hash {
  let mut h = blake3::Hasher::new();
  for (t, o) in ctx {
    h.update(t.get_hash().as_bytes());
    h.update(&[u8::from(*o)]);
  }
  h.finalize()
}

/// `phiS` (`phiSFix` with its memo).
pub fn phi_s(
  tm: &mut Tm,
  l: &StructLayout<'_>,
  ctx: &Ctx,
  e: &Expr,
) -> R<Expr> {
  phi_s_fix(tm, l, DEFAULT_FUEL, ctx, e)
}

fn phi_s_fix(
  tm: &mut Tm,
  l: &StructLayout<'_>,
  fuel: usize,
  ctx: &Ctx,
  e: &Expr,
) -> R<Expr> {
  if fuel == 0 {
    return Err("Φ: recursion bound exhausted".into());
  }
  let key = (*e.get_hash(), ctx_hash(ctx));
  if let Some(r) = tm.cache_own.get(&key) {
    return Ok(r.clone());
  }
  let r = phi_s_step(tm, l, fuel - 1, ctx, e)?;
  tm.cache_own.insert(key, r.clone());
  Ok(r)
}

/// `phiSMotive`.
fn phi_s_motive(
  tm: &mut Tm,
  l: &StructLayout<'_>,
  fuel: usize,
  ctx: &Ctx,
  j: usize,
  arg: &Expr,
) -> R<Expr> {
  let g = &l.groups[j];
  if g.size() < 2 {
    return phi_s_fix(tm, l, fuel, ctx, arg);
  }
  let (bs, body) = peel_lams(g.arity, arg);
  let mut ctx2 = ctx.clone();
  let mut bs2 = Vec::new();
  for (nm, t, bi) in bs {
    bs2.push((nm, phi_s_fix(tm, l, fuel, &ctx2, &t)?, bi));
    ctx2.push((t, false));
  }
  let Some(s) = decode_spine(PackKind::Pprod, g.size(), &body) else {
    return Err("grammar: a packed motive that is not Lean's".into());
  };
  let mut leaves = Vec::new();
  for x in &s.leaves {
    leaves.push(phi_s_fix(tm, l, fuel, &ctx2, x)?);
  }
  Ok(mk_lams(&bs2, s.with_leaves(leaves).permute(&g.perm).typ()))
}

/// `phiSDictType`.
fn phi_s_dict_type(
  tm: &mut Tm,
  l: &StructLayout<'_>,
  fuel: usize,
  ctx: &Ctx,
  t: &Expr,
) -> R<Expr> {
  let (h, args) = get_app_fn_args(t);
  if let ExprData::Const(c, _, _) = h.as_data()
    && let Some(a) = l.aux.get(c)
  {
    if a.is_brec_on {
      return phi_s_fix(tm, l, fuel, ctx, t);
    }
    let p = l.num_params;
    let k = l.num_motives;
    let mut args2 = Vec::new();
    for (i, x) in args.iter().enumerate() {
      if p <= i && i < p + k {
        args2.push(phi_s_motive(tm, l, fuel, ctx, i - p, x)?);
      } else {
        args2.push(phi_s_fix(tm, l, fuel, ctx, x)?);
      }
    }
    return Ok(mk_app_n(h, &args2));
  }
  phi_s_fix(tm, l, fuel, ctx, t)
}

/// The public entry used by `transportStructural` (`phiSDictType L (phiS L)`).
pub fn phi_s_dict(
  tm: &mut Tm,
  l: &StructLayout<'_>,
  ctx: &Ctx,
  t: &Expr,
) -> R<Expr> {
  phi_s_dict_type(tm, l, DEFAULT_FUEL, ctx, t)
}

#[allow(clippy::too_many_arguments)]
fn under_binders(
  tm: &mut Tm,
  l: &StructLayout<'_>,
  fuel: usize,
  ctx: &Ctx,
  n: usize,
  lam: bool,
  x: &Expr,
  owned: &dyn Fn(usize) -> bool,
  k: &mut dyn FnMut(&mut Tm, &Ctx, &Expr) -> R<Expr>,
) -> R<Expr> {
  let (bs, body) = if lam { peel_lams(n, x) } else { peel_foralls(n, x) };
  let mut ctx2 = ctx.clone();
  let mut bs2 = Vec::new();
  for (i, (nm, t, bi)) in bs.into_iter().enumerate() {
    let t2 = if owned(i) {
      phi_s_dict_type(tm, l, fuel, &ctx2, &t)?
    } else {
      phi_s_fix(tm, l, fuel, &ctx2, &t)?
    };
    bs2.push((nm, t2, bi));
    ctx2.push((t, owned(i)));
  }
  let body2 = k(tm, &ctx2, &body)?;
  Ok(if lam { mk_lams(&bs2, body2) } else { mk_foralls(&bs2, body2) })
}

/// `phiSStep`.
fn phi_s_step(
  tm: &mut Tm,
  l: &StructLayout<'_>,
  fuel: usize,
  ctx: &Ctx,
  e: &Expr,
) -> R<Expr> {
  let owned_arg = |x: &Expr| -> bool {
    match bvar_idx(&strip_mdata(x)) {
      Some(i) if i < ctx.len() => ctx[ctx.len() - 1 - i].1,
      _ => false,
    }
  };
  match e.as_data() {
    ExprData::Proj(..) => {
      let (gsteps, gbase) = path_chain(e);
      if let Some(i) = bvar_idx(&strip_mdata(&gbase))
        && i < ctx.len()
      {
        let (t, owned) = ctx[ctx.len() - 1 - i].clone();
        let ty = lift(&t, i + 1);
        if let Some(steps2) = below_path(tm, l, &ty, &gsteps)? {
          if l.check_ownership && !owned {
            return Err(
              "grammar: a path into a below dictionary that is not the recursion's own"
                .into(),
            );
          }
          let mut steps3 = Vec::new();
          for st in steps2 {
            match st {
              PStep::App(a) => {
                steps3.push(PStep::App(phi_s_fix(tm, l, fuel, ctx, &a)?))
              },
              s => steps3.push(s),
            }
          }
          return Ok(apply_steps(&steps3, &gbase));
        }
      }
      let (steps, base) = proj_chain(e);
      let base2 = strip_mdata(&base);
      if let ExprData::Bvar(..) = base2.as_data() {
        return Ok(apply_projs(&steps, &base));
      }
      let is_brec = match const_app(&base2) {
        Some((c, _, _)) => l.aux.get(&c).is_some_and(|a| a.is_brec_on),
        None => false,
      };
      let b = phi_s_fix(tm, l, fuel, ctx, &base2)?;
      if is_brec {
        let Some((c, _, _)) = const_app(&base2) else {
          return Ok(apply_projs(&steps, &b));
        };
        let Some(a) = l.aux.get(&c) else { return Ok(apply_projs(&steps, &b)) };
        let steps2 = transport_path(&l.groups[a.pos], &steps)?;
        return Ok(apply_projs(&steps2, &b));
      }
      Ok(apply_projs(&steps, &b))
    },
    ExprData::App(..) => {
      let (h, args) = get_app_fn_args(e);
      if let ExprData::Const(c, _, _) = h.as_data() {
        if let Some(a) = l.aux.get(c).copied() {
          if !a.is_brec_on && l.check_ownership {
            let mut a2 = Vec::new();
            for x in &args {
              a2.push(phi_s_fix(tm, l, fuel, ctx, x)?);
            }
            return Ok(mk_app_n(h, &a2));
          }
          let p = l.num_params;
          let k = l.num_motives;
          let g_arity = l.groups[a.pos].arity;
          let f_start = p + k + g_arity;
          let mut args2 = Vec::new();
          for (i, x) in args.iter().enumerate() {
            if p <= i && i < p + k {
              args2.push(phi_s_motive(tm, l, fuel, ctx, i - p, x)?);
            } else if a.is_brec_on && f_start <= i && i < f_start + k {
              args2.push(functional(tm, l, fuel, ctx, i - f_start, x)?);
            } else {
              args2.push(phi_s_fix(tm, l, fuel, ctx, x)?);
            }
          }
          return Ok(mk_app_n(h, &args2));
        }
        if l.f_names.contains(c) {
          if args.len() < l.num_fixed {
            return Err(
              "grammar: a partial application of a functional".into(),
            );
          }
          let mut a2 = Vec::new();
          for x in &args {
            a2.push(if owned_arg(x) {
              x.clone()
            } else {
              phi_s_fix(tm, l, fuel, ctx, x)?
            });
          }
          let mut out: Vec<Expr> =
            l.fixed_perm.iter().map(|&i| a2[i].clone()).collect();
          out.extend(a2[l.num_fixed..].iter().cloned());
          return Ok(mk_app_n(h, &out));
        }
        if l.matchers.contains(c) {
          let m = l.num_fun_types;
          if args.len() < m {
            return Err(
              "grammar: a partial application of a below matcher".into(),
            );
          }
          let mut a2 = Vec::new();
          for x in &args {
            a2.push(if owned_arg(x) {
              x.clone()
            } else {
              phi_s_fix(tm, l, fuel, ctx, x)?
            });
          }
          let mut out: Vec<Expr> =
            l.fun_perm().iter().map(|&i| a2[i].clone()).collect();
          out.extend(a2[m..].iter().cloned());
          return Ok(mk_app_n(h, &out));
        }
        if l.check_ownership && args.iter().any(owned_arg) {
          let cs = name_to_string(c);
          let Some(ci) = (l.const_of)(c) else {
            return Err(format!(
              "grammar: a below dictionary passed to {cs}, which is not in the input"
            ));
          };
          let ty = ci.get_type().clone();
          let ar = forall_arity(&ty);
          if ar > args.len() {
            return Err(format!(
              "grammar: a below dictionary passed to a partial application of {cs}"
            ));
          }
          for x in args.iter().take(ar) {
            if owned_arg(x) {
              return Err(format!(
                "grammar: a below dictionary passed whole to {cs}"
              ));
            }
          }
          let extras: Vec<bool> = args[ar..].iter().map(owned_arg).collect();
          let (ps, _) = peel_foralls(ar, &ty);
          let motives = l.elim_motives(c).unwrap_or_default();
          let mut args2 = Vec::new();
          for (k, x) in args.iter().enumerate() {
            if let Some(&(_, ma)) = motives.iter().find(|m| m.0 == k) {
              if lam_arity(x) < ma {
                return Err(format!(
                  "grammar: a motive of {cs} that is not a function of its discriminants"
                ));
              }
              let extras2 = extras.clone();
              let cs2 = cs.clone();
              args2.push(under_binders(
                tm,
                l,
                fuel,
                ctx,
                ma,
                true,
                x,
                &|_| false,
                &mut |tm, ctx2, body| {
                  let (fs, rest) = peel_foralls(extras2.len(), body);
                  if fs.len() != extras2.len() {
                    return Err(format!(
                      "grammar: a motive of {cs2} that does not bind the dictionary"
                    ));
                  }
                  let mut c2 = ctx2.clone();
                  let mut fs2 = Vec::new();
                  for (j, (nm, t, bi)) in fs.into_iter().enumerate() {
                    let t2 = if extras2[j] {
                      phi_s_dict_type(tm, l, fuel, &c2, &t)?
                    } else {
                      phi_s_fix(tm, l, fuel, &c2, &t)?
                    };
                    fs2.push((nm, t2, bi));
                    c2.push((t, false));
                  }
                  Ok(mk_foralls(&fs2, phi_s_fix(tm, l, fuel, &c2, &rest)?))
                },
              )?);
            } else if k < ps.len() {
              let pt = &ps[k].1;
              let fc = forall_arity(pt);
              let (_, concl) = peel_foralls(fc, pt);
              let is_alt =
                match bvar_idx(&get_app_fn_args(&strip_mdata(&concl)).0) {
                  Some(i) => i >= fc && i - fc < k,
                  None => false,
                };
              if is_alt {
                if lam_arity(x) < fc + extras.len() {
                  return Err(format!(
                    "grammar: an alternative of {cs} that does not bind the dictionary"
                  ));
                }
                let extras2 = extras.clone();
                args2.push(under_binders(
                  tm,
                  l,
                  fuel,
                  ctx,
                  fc + extras.len(),
                  true,
                  x,
                  &|i| i >= fc && extras2[i - fc],
                  &mut |tm, ctx2, body| phi_s_fix(tm, l, fuel, ctx2, body),
                )?);
              } else {
                args2.push(phi_s_fix(tm, l, fuel, ctx, x)?);
              }
            } else {
              args2.push(if owned_arg(x) {
                x.clone()
              } else {
                phi_s_fix(tm, l, fuel, ctx, x)?
              });
            }
          }
          return Ok(mk_app_n(h, &args2));
        }
        let mut a2 = Vec::new();
        for x in &args {
          a2.push(phi_s_fix(tm, l, fuel, ctx, x)?);
        }
        return Ok(mk_app_n(h, &a2));
      }
      if l.check_ownership && args.iter().any(owned_arg) {
        return Err(
          "grammar: a below dictionary passed to a term that is not an eliminator".into(),
        );
      }
      let h2 = phi_s_fix(tm, l, fuel, ctx, &h)?;
      let mut a2 = Vec::new();
      for x in &args {
        a2.push(phi_s_fix(tm, l, fuel, ctx, x)?);
      }
      Ok(mk_app_n(h2, &a2))
    },
    ExprData::Const(c, _, _) => {
      if l.f_names.contains(c) && l.num_fixed > 0 {
        return Err("grammar: a bare functional".into());
      }
      if l.matchers.contains(c) && l.num_fun_types > 0 {
        return Err("grammar: a bare below matcher".into());
      }
      Ok(e.clone())
    },
    ExprData::Lam(nm, t, b, bi, _) => {
      if l.check_ownership && l.is_below_ty(t) {
        return Err(format!(
          "grammar: a binder {} of a below type that is not the recursion's dictionary",
          nm.pretty()
        ));
      }
      let t2 = phi_s_fix(tm, l, fuel, ctx, t)?;
      let mut c2 = ctx.clone();
      c2.push((t.clone(), false));
      Ok(Expr::lam(nm.clone(), t2, phi_s_fix(tm, l, fuel, &c2, b)?, bi.clone()))
    },
    ExprData::ForallE(nm, t, b, bi, _) => {
      let t2 = phi_s_fix(tm, l, fuel, ctx, t)?;
      let mut c2 = ctx.clone();
      c2.push((t.clone(), false));
      Ok(Expr::all(nm.clone(), t2, phi_s_fix(tm, l, fuel, &c2, b)?, bi.clone()))
    },
    ExprData::LetE(nm, t, v, b, nd, _) => {
      if l.check_ownership && l.is_below_ty(t) {
        return Err(format!(
          "grammar: a let {} of a below type that is not the recursion's dictionary",
          nm.pretty()
        ));
      }
      let t2 = phi_s_fix(tm, l, fuel, ctx, t)?;
      let v2 = phi_s_fix(tm, l, fuel, ctx, v)?;
      let mut c2 = ctx.clone();
      c2.push((t.clone(), false));
      Ok(Expr::letE(nm.clone(), t2, v2, phi_s_fix(tm, l, fuel, &c2, b)?, *nd))
    },
    ExprData::Bvar(..) => {
      if l.check_ownership && owned_arg(e) {
        return Err(
          "grammar: a below dictionary used whole outside an eliminator".into(),
        );
      }
      Ok(e.clone())
    },
    ExprData::Mdata(d, x, _) => {
      Ok(Expr::mdata(d.clone(), phi_s_fix(tm, l, fuel, ctx, x)?))
    },
    _ => Ok(e.clone()),
  }
}

/// The packed functional at functional position `j` (`phiSStep.functional`).
fn functional(
  tm: &mut Tm,
  l: &StructLayout<'_>,
  fuel: usize,
  ctx: &Ctx,
  j: usize,
  arg: &Expr,
) -> R<Expr> {
  let g = l.groups[j].clone();
  let dict = move |i: usize| i == g.arity;
  if g.size() < 2 {
    return under_binders(
      tm,
      l,
      fuel,
      ctx,
      g.arity + 1,
      true,
      arg,
      &dict,
      &mut |tm, c2, body| phi_s_fix(tm, l, fuel, c2, body),
    );
  }
  let g2 = l.groups[j].clone();
  under_binders(
    tm,
    l,
    fuel,
    ctx,
    g.arity + 1,
    true,
    arg,
    &dict,
    &mut |tm, c2, body| {
      let Some((s, cs)) = decode_tuple(g2.size(), body) else {
        return Err("grammar: a packed functional that is not Lean's".into());
      };
      let mut leaves = Vec::new();
      for x in &s.leaves {
        leaves.push(phi_s_fix(tm, l, fuel, c2, x)?);
      }
      let mut cs2 = Vec::new();
      for x in &cs {
        cs2.push(phi_s_fix(tm, l, fuel, c2, x)?);
      }
      Ok(mk_tuple(
        &s.with_leaves(leaves).permute(&g2.perm),
        &permute(&g2.perm, &cs2),
      ))
    },
  )
}

// ---------------------------------------------------------------------------
// The layout
// ---------------------------------------------------------------------------

type BlockOf = (FxHashMap<Name, BlockAux>, usize, usize, Vec<usize>);

/// `blockOf`.
pub fn block_of(const_of: ConstOf<'_>, brec_on: &Name) -> R<BlockOf> {
  let ind = match brec_on.as_data() {
    NameData::Str(p, _, _) => p.clone(),
    _ => brec_on.clone(),
  };
  let Some(ConstantInfo::InductInfo(iv)) = const_of(&ind) else {
    return Err(format!(
      "{}: not the brecOn of an inductive",
      name_to_string(brec_on)
    ));
  };
  let all = iv.all.clone();
  let k_total = all.len() + nat_usize(&iv.num_nested);
  let mut aux: FxHashMap<Name, BlockAux> = FxHashMap::default();
  let mut arities = Vec::new();
  for j in 0..k_total {
    let (below, brec, rec_n) = if j < all.len() {
      (
        mk_str(&all[j], "below"),
        mk_str(&all[j], "brecOn"),
        mk_str(&all[j], "rec"),
      )
    } else {
      let k = j - all.len() + 1;
      (
        mk_str(&all[0], &format!("below_{k}")),
        mk_str(&all[0], &format!("brecOn_{k}")),
        mk_str(&all[0], &format!("rec_{k}")),
      )
    };
    aux.insert(below, BlockAux { pos: j, is_brec_on: false });
    aux.insert(brec, BlockAux { pos: j, is_brec_on: true });
    let Some(ConstantInfo::RecInfo(r)) = const_of(&rec_n) else {
      return Err(format!("{}: no recursor", name_to_string(&rec_n)));
    };
    arities.push(nat_usize(&r.num_indices) + 1);
  }
  Ok((aux, nat_usize(&iv.num_params), k_total, arities))
}

/// `peelLets`.
pub fn peel_lets(n: usize, e: &Expr) -> (Vec<(Name, Expr, Expr)>, Expr) {
  let mut acc = Vec::new();
  let mut cur = e.clone();
  for _ in 0..n {
    let s = strip_mdata(&cur);
    match s.as_data() {
      ExprData::LetE(nm, t, v, b, _, _) => {
        acc.push((nm.clone(), t.clone(), v.clone()));
        cur = b.clone();
      },
      _ => return (acc, s),
    }
  }
  (acc, cur)
}

pub fn let_arity(e: &Expr) -> usize {
  match e.as_data() {
    ExprData::LetE(_, _, _, b, _, _) => let_arity(b) + 1,
    ExprData::Mdata(_, x, _) => let_arity(x),
    _ => 0,
  }
}

#[derive(Clone, Debug)]
pub struct MemberShape {
  pub lams: usize,
  pub lets: usize,
  pub brec_on_name: Name,
  pub brec_args: Vec<Expr>,
  pub steps: Vec<(Name, usize)>,
}

/// `memberShape`.
pub fn member_shape(d: &Decl) -> R<MemberShape> {
  let (ps, b1) = peel_lams(lam_arity(&d.value), &d.value);
  let (ls, b2) = peel_lets(let_arity(&b1), &b1);
  let (h, _) = get_app_fn_args(&strip_mdata(&b2));
  let (steps, base) = match strip_mdata(&h).as_data() {
    ExprData::Proj(..) => proj_chain(&h),
    _ => (Vec::new(), strip_mdata(&b2)),
  };
  let Some((c, _, args)) = const_app(&base) else {
    return Err(format!(
      "member {}: not a brecOn application",
      name_to_string(&d.name)
    ));
  };
  Ok(MemberShape {
    lams: ps.len(),
    lets: ls.len(),
    brec_on_name: c,
    brec_args: args,
    steps,
  })
}

/// `remapLoose`.
pub fn remap_loose(n: usize, f: &dyn Fn(usize) -> usize, e: &Expr) -> Expr {
  fn go(e: &Expr, d: usize, n: usize, f: &dyn Fn(usize) -> usize) -> Expr {
    match e.as_data() {
      ExprData::Bvar(i, _) => {
        let i = nat_usize(i);
        if d <= i && i < d + n { mk_bvar(d + f(i - d)) } else { mk_bvar(i) }
      },
      ExprData::App(g, a, _) => Expr::app(go(g, d, n, f), go(a, d, n, f)),
      ExprData::Lam(nm, t, b, bi, _) => {
        Expr::lam(nm.clone(), go(t, d, n, f), go(b, d + 1, n, f), bi.clone())
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        Expr::all(nm.clone(), go(t, d, n, f), go(b, d + 1, n, f), bi.clone())
      },
      ExprData::LetE(nm, t, v, b, nd, _) => Expr::letE(
        nm.clone(),
        go(t, d, n, f),
        go(v, d, n, f),
        go(b, d + 1, n, f),
        *nd,
      ),
      ExprData::Proj(s, i, x, _) => {
        Expr::proj(s.clone(), i.clone(), go(x, d, n, f))
      },
      ExprData::Mdata(m, x, _) => Expr::mdata(m.clone(), go(x, d, n, f)),
      _ => e.clone(),
    }
  }
  go(e, 0, n, f)
}

type Lets = Vec<(Name, Expr, Expr)>;

/// `reorderLets`.
pub fn reorder_lets(perm: &[usize], ls: &Lets, body: &Expr) -> R<(Lets, Expr)> {
  let n = ls.len();
  let mut closed = Vec::new();
  for (i, (nm, t, v)) in ls.iter().enumerate() {
    let Some(t2) = lower_opt(t, i) else {
      return Err("a let type mentions an earlier let".into());
    };
    let Some(v2) = lower_opt(v, i) else {
      return Err("a let value mentions an earlier let".into());
    };
    closed.push((nm.clone(), t2, v2));
  }
  let inv = inv_perm(perm);
  let ls2: Lets = (0..n)
    .map(|p| {
      let (nm, t, v) = &closed[perm[p]];
      (nm.clone(), lift(t, p), lift(v, p))
    })
    .collect();
  let body2 = remap_loose(n, &|k| n - 1 - inv[n - 1 - k], body);
  Ok((ls2, body2))
}

pub fn mk_lets(ls: &Lets, body: Expr) -> Expr {
  ls.iter().rev().fold(body, |acc, (nm, t, v)| {
    Expr::letE(nm.clone(), t.clone(), v.clone(), acc, false)
  })
}

/// `structLayout`.
pub fn struct_layout<'a>(
  members: &[Decl],
  aux: &[Decl],
  sigma: &[usize],
  const_of: ConstOf<'a>,
) -> R<StructLayout<'a>> {
  let n = members.len();
  if !(n >= 2 && sigma.len() == n && is_perm(sigma)) {
    return Err("structLayout: bad permutation".into());
  }
  let mut shapes = Vec::new();
  for m in members {
    shapes.push(member_shape(m)?);
  }
  let (block_aux, p, k_total, arities) =
    block_of(const_of, &shapes[0].brec_on_name)?;
  let mut poss = Vec::new();
  for s in &shapes {
    match block_aux.get(&s.brec_on_name) {
      Some(a) => {
        if a.is_brec_on {
          poss.push(a.pos)
        } else {
          return Err("structLayout: not a brecOn".into());
        }
      },
      None => return Err("structLayout: members over different blocks".into()),
    }
  }
  let mut matchers: FxHashSet<Name> = FxHashSet::default();
  for d in aux {
    if let NameData::Str(_, s, _) = d.name.as_data()
      && s.starts_with("match_")
    {
      matchers.insert(d.name.clone());
    }
  }
  let mut groups: Vec<Group> = (0..k_total)
    .map(|j| Group {
      members: (0..n).filter(|&i| poss[i] == j).collect(),
      arity: arities[j],
      spine: empty_spine(),
      perm: Vec::new(),
    })
    .collect();
  for j in 0..k_total {
    let g = groups[j].clone();
    if g.size() >= 2 {
      let Some(motive) = shapes[0].brec_args.get(p + j) else {
        return Err("structLayout: missing motive".into());
      };
      let (_, body) = peel_lams(g.arity, motive);
      let Some(s) = decode_spine(PackKind::Pprod, g.size(), &body) else {
        return Err("structLayout: a packed motive that is not Lean's".into());
      };
      let ranks: Vec<usize> = g.members.iter().map(|&i| sigma[i]).collect();
      let perm: Vec<usize> = (0..g.size())
        .map(|a| ranks.iter().filter(|&&r| r < ranks[a]).count())
        .collect();
      groups[j] = Group { spine: s, perm, ..g };
    } else {
      groups[j] = Group { perm: id_perm(g.size()), ..g };
    }
  }
  for i in 0..n {
    let g = &groups[poss[i]];
    let a = g.members.iter().position(|&x| x == i).unwrap_or(0);
    if g.size() >= 2 {
      match path_prefix(g.size(), &shapes[i].steps) {
        Some((idx, len)) => {
          if !(idx == a
            && len == shapes[i].steps.len()
            && steps_fit(&g.spine, idx, &shapes[i].steps))
          {
            return Err(format!(
              "structLayout: member {i} does not project its clique position"
            ));
          }
        },
        None => {
          return Err(format!(
            "structLayout: member {i} does not project its clique position"
          ));
        },
      }
    }
  }
  let mut f_names: FxHashSet<Name> = FxHashSet::default();
  let mut f_depth: FxHashMap<Name, (usize, usize)> = FxHashMap::default();
  let mut qss: Vec<Vec<usize>> = Vec::new();
  for i in 0..n {
    let sh = &shapes[i];
    let f_start = p + k_total + arities[poss[i]];
    let mut q_opt: Option<Vec<usize>> = None;
    for j in 0..k_total {
      let g = &groups[j];
      if g.size() == 0 {
        continue;
      }
      let Some(f) = sh.brec_args.get(f_start + j) else {
        return Err("structLayout: missing functional".into());
      };
      let depth = lam_arity(f).min(g.arity + 1);
      let (_, body) = peel_lams(depth, f);
      let comps = if g.size() >= 2 {
        match decode_tuple(g.size(), &body) {
          Some((_, cs)) => cs,
          None => {
            return Err(
              "structLayout: a packed functional that is not Lean's".into(),
            );
          },
        }
      } else {
        vec![body]
      };
      for c in &comps {
        let Some((h, _, args)) = const_app(c) else {
          return Err(
            "structLayout: a functional that is not a constant".into(),
          );
        };
        if matchers.contains(&h) {
          continue;
        }
        f_names.insert(h.clone());
        f_depth.insert(h.clone(), (depth, g.arity));
        if args.len() < depth {
          return Err(
            "structLayout: a functional applied to too few arguments".into(),
          );
        }
        let m = args.len() - depth;
        let mut q = Vec::new();
        for x in &args[..m] {
          match bvar_idx(&strip_mdata(x)) {
            Some(b) => {
              if !(b >= depth + sh.lets && b - depth - sh.lets < sh.lams) {
                return Err(
                  "structLayout: a fixed argument is not a member parameter"
                    .into(),
                );
              }
              q.push(sh.lams - 1 - (b - depth - sh.lets));
            },
            None => {
              return Err(
                "structLayout: a fixed argument is not a member parameter"
                  .into(),
              );
            },
          }
        }
        if !no_dups(&q) {
          return Err(
            "structLayout: distinct fixed parameters alias the same binder"
              .into(),
          );
        }
        match &q_opt {
          None => q_opt = Some(q),
          Some(q2) => {
            if q != *q2 {
              return Err("structLayout: inconsistent fixed arguments".into());
            }
          },
        }
      }
    }
    qss.push(q_opt.unwrap_or_default());
  }
  let m = qss[0].len();
  if !qss.iter().all(|q| q.len() == m) {
    return Err("structLayout: inconsistent fixed parameters".into());
  }
  if !eq_sorted(&qss[0]) {
    return Err(
      "structLayout: the fixed parameters are not in the first member's order"
        .into(),
    );
  }
  let qg = qss[inv_perm(sigma)[0]].clone();
  let fixed_perm = sort_idx_by_key(m, &|a| qg[a]);
  let num_fun_types = shapes[0].lets;
  if !shapes.iter().all(|s| s.lets == num_fun_types) {
    return Err("structLayout: inconsistent funType lets".into());
  }
  if !(num_fun_types == 0 || num_fun_types == n) {
    return Err("structLayout: unexpected lets".into());
  }
  Ok(StructLayout {
    n,
    sigma: sigma.to_vec(),
    const_of,
    num_params: p,
    num_motives: k_total,
    aux: block_aux,
    groups,
    f_names,
    num_fixed: m,
    fixed_perm,
    matchers,
    num_fun_types,
    member_fixed: qss,
    f_depth,
    check_ownership: true,
  })
}

/// `transportStructural`.
pub fn transport_structural(
  tm: &mut Tm,
  members: &[Decl],
  aux: &[Decl],
  sigma: &[usize],
  const_of: ConstOf<'_>,
  lemmas: &[(Decl, Name)],
  force_ownership: bool,
) -> R<Vec<Transported>> {
  let mut l = struct_layout(members, aux, sigma, const_of)?;
  l.check_ownership = force_ownership || !members.iter().all(|d| d.is_thm);
  if l.check_ownership {
    for d in aux {
      if !(l.brec_on_count(&d.typ) == 0 && l.brec_on_count(&d.value) == 0) {
        return Err(format!(
          "grammar: a brecOn application of the block outside a member's root (in {})",
          name_to_string(&d.name)
        ));
      }
    }
    for d in members {
      if !(l.brec_on_count(&d.typ) == 0 && l.brec_on_count(&d.value) == 1) {
        return Err(format!(
          "grammar: a brecOn application of the block outside a member's root (in {})",
          name_to_string(&d.name)
        ));
      }
    }
  }
  let empty: Ctx = Vec::new();
  let phi_f = |tm: &mut Tm,
               l: &StructLayout<'_>,
               depth: usize,
               arity: usize,
               e: &Expr,
               lam: bool|
   -> R<Expr> {
    let (bs, body) =
      if lam { peel_lams(depth, e) } else { peel_foralls(depth, e) };
    let mut ctx: Ctx = Vec::new();
    let mut bs2 = Vec::new();
    for (i, (nm, t, bi)) in bs.into_iter().enumerate() {
      let dict = depth == arity + 1 && i == arity;
      let t2 = if dict {
        phi_s_dict(tm, l, &ctx, &t)?
      } else {
        phi_s(tm, l, &ctx, &t)?
      };
      bs2.push((nm, t2, bi));
      // the type's telescope records no ownership (`phiFTy`)
      ctx.push((t, dict && lam));
    }
    let b = phi_s(tm, l, &ctx, &body)?;
    Ok(if lam { mk_lams(&bs2, b) } else { mk_foralls(&bs2, b) })
  };
  let mut out: Vec<Transported> = Vec::new();
  for d in aux {
    if l.f_names.contains(&d.name) {
      let m = l.num_fixed;
      let (_, arity) = l.f_depth.get(&d.name).copied().unwrap_or((0, 0));
      let depth = arity + 1;
      let fp = l.fixed_perm.clone();
      let typ = with_reordered_binders2(
        tm,
        false,
        m,
        &fp,
        &d.typ,
        &mut |tm, x| phi_s(tm, &l, &empty, x),
        &mut |tm, x| phi_f(tm, &l, depth, arity, x, false),
      )?;
      let value = with_reordered_binders2(
        tm,
        true,
        m,
        &fp,
        &d.value,
        &mut |tm, x| phi_s(tm, &l, &empty, x),
        &mut |tm, x| phi_f(tm, &l, depth, arity, x, true),
      )?;
      out.push(Transported::ok(Decl { typ, value, ..d.clone() }));
    } else if l.matchers.contains(&d.name) {
      let m = l.num_fun_types;
      let fp = l.fun_perm();
      let typ =
        with_reordered_binders(tm, false, m, &fp, &d.typ, &mut |tm, x| {
          phi_s(tm, &l, &empty, x)
        })?;
      let value =
        with_reordered_binders(tm, true, m, &fp, &d.value, &mut |tm, x| {
          phi_s(tm, &l, &empty, x)
        })?;
      out.push(Transported::ok(Decl { typ, value, ..d.clone() }));
    } else {
      let typ = phi_s(tm, &l, &empty, &d.typ)?;
      let value = phi_s(tm, &l, &empty, &d.value)?;
      out.push(Transported::ok(Decl { typ, value, ..d.clone() }));
    }
  }
  for d in members {
    let (ps, b1) = peel_lams(lam_arity(&d.value), &d.value);
    let mut ctx: Ctx = Vec::new();
    let mut ps2 = Vec::new();
    for (nm, t, bi) in ps {
      if l.check_ownership && l.is_below_ty(&t) {
        return Err("grammar: a member parameter of a below type".into());
      }
      ps2.push((nm, phi_s(tm, &l, &ctx, &t)?, bi));
      ctx.push((t, false));
    }
    let (ls, b2) = peel_lets(l.num_fun_types, &b1);
    let (ls, b2) = reorder_lets(&l.fun_perm(), &ls, &b2)?;
    let mut ls2 = Vec::new();
    for (nm, t, v) in ls {
      let t2 = phi_s(tm, &l, &ctx, &t)?;
      let v2 = phi_s(tm, &l, &ctx, &v)?;
      ls2.push((nm, t2, v2));
      ctx.push((t, false));
    }
    let body = phi_s(tm, &l, &ctx, &b2)?;
    let typ = phi_s(tm, &l, &empty, &d.typ)?;
    out.push(Transported::ok(Decl {
      typ,
      value: mk_lams(&ps2, mk_lets(&ls2, body)),
      ..d.clone()
    }));
  }
  l.check_ownership = false;
  for (d, nn) in lemmas {
    let typ = phi_s(tm, &l, &empty, &d.typ)?;
    let value = phi_s(tm, &l, &empty, &d.value)?;
    out.push(Transported::ok(Decl {
      name: nn.clone(),
      typ,
      value,
      ..d.clone()
    }));
  }
  Ok(out)
}
