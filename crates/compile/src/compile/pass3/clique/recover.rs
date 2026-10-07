//! The recovered specification of a clique and the canonical order (a port
//! of `Ix/Compile/Clique/Recover.lean`: `normalisedSpecs`, `cliqueOrder`
//! and what they call).

use ix_common::address::Address;
use ix_common::env::{BinderInfo, Expr, ExprData, Level, Name};

use super::basic::*;
use super::order::{AddrOf, Member, clique_classes, statement_order};
use super::packing::*;
use super::pf::{PfLayout, n_order_fix, norm_order_alias, pf_layout};
use super::structural::*;
use super::telescope::*;
use super::transport::{Encoding, Input, OrderSource, find_packed};
use super::wf::{WfLayout, conjugate_wf_root, wf_layout};
use crate::compile::pass3::expr::{get_app_fn_args, strip_mdata};

pub fn ph_motive() -> Name {
  root("_ix_spec_motive")
}
pub fn ph_rel() -> Name {
  root("_ix_spec_rel")
}
pub fn ph_rec_var() -> Name {
  root("_ix_spec_recvar")
}

/// `placeholderAddr?`.
pub fn placeholder_addr(n: &Name) -> Option<Address> {
  let mk = |k: u8| {
    let mut b = [0u8; 32];
    b[31] = k;
    Address::from_slice(&b).ok()
  };
  if *n == ph_motive() {
    mk(1)
  } else if *n == ph_rel() {
    mk(2)
  } else if *n == ph_rec_var() {
    mk(3)
  } else {
    None
  }
}

#[derive(Clone, Debug)]
enum Hole {
  Expr(Expr),
  SCall(usize),
  WCall(usize, Spine, Expr),
}

#[derive(Default)]
struct Holes {
  hs: Vec<Hole>,
  i: usize,
}

impl Holes {
  fn push(&mut self, h: Hole) {
    self.hs.push(h);
  }
  fn pop(&mut self) -> R<Hole> {
    let Some(h) = self.hs.get(self.i).cloned() else {
      return Err("recovery: the holes ran out during re-encoding".into());
    };
    self.i += 1;
    Ok(h)
  }
  fn pop_expr(&mut self) -> R<Expr> {
    match self.pop()? {
      Hole::Expr(e) => Ok(e),
      _ => Err("recovery: an erased annotation was expected".into()),
    }
  }
}

fn ph(n: &Name) -> Expr {
  cnst(n, &[])
}

fn is_const_named(e: &Expr, n: &Name) -> bool {
  matches!(strip_mdata(e).as_data(), ExprData::Const(c, _, _) if c == n)
}

/// `belowWalk`.
fn below_walk(
  tm: &mut Tm,
  l: &StructLayout<'_>,
  ty: &Expr,
  steps: &[PStep],
) -> R<Option<(usize, usize, Expr)>> {
  let Some((c, us, args)) = const_app(ty) else { return Ok(None) };
  let Some(a) = l.aux.get(&c) else { return Ok(None) };
  if a.is_brec_on || args.len() < l.num_params + l.num_motives {
    return Ok(None);
  }
  let mut cans = Vec::new();
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
          let is_and = matches!(const_app(&w), Some((h, _, _)) if h == n_and());
          if (*s == n_and()) != is_and {
            return Err("recovery: a projection that is not the node's".into());
          }
          cur = if *i == 0 { a } else { b };
        },
        None => {
          return Err("recovery: a projection the walk cannot follow".into());
        },
      },
      PStep::App(x) => match strip_mdata(&w).as_data() {
        ExprData::ForallE(_, _, b, _, _) => {
          cur = instantiate_rev(b, std::slice::from_ref(x))
        },
        _ => {
          return Err("recovery: an application the walk cannot follow".into());
        },
      },
    }
    let sc = strip_mdata(&cur);
    if let ExprData::Fvar(f, _) = get_app_fn_args(&sc).0.as_data() {
      return match cans.iter().position(|x| x == f) {
        Some(j) => Ok(Some((t, j, sc))),
        None => Err("recovery: a path that reaches a foreign variable".into()),
      };
    }
  }
  Ok(None)
}

struct RecS<'a, 'b> {
  l: &'a StructLayout<'b>,
  names: &'a [Name],
  lvls: &'a [Level],
}

impl RecS<'_, '_> {
  fn dict_ty(
    &self,
    tm: &mut Tm,
    hs: &mut Holes,
    fuel: usize,
    ctx: &[Expr],
    t: &Expr,
  ) -> R<Expr> {
    let (h, args) = get_app_fn_args(t);
    if let ExprData::Const(c, _, _) = h.as_data()
      && let Some(a) = self.l.aux.get(c)
      && !a.is_brec_on
    {
      let p = self.l.num_params;
      let k = self.l.num_motives;
      let mut args2 = Vec::new();
      for (i, x) in args.iter().enumerate() {
        if p <= i && i < p + k {
          hs.push(Hole::Expr(x.clone()));
          args2.push(ph(&ph_motive()));
        } else {
          args2.push(self.go(tm, hs, fuel, ctx, x)?);
        }
      }
      return Ok(mk_app_n(h, &args2));
    }
    self.go(tm, hs, fuel, ctx, t)
  }

  fn owned_var(&self, ctx: &[Expr], x: &Expr) -> bool {
    match bvar_idx(&strip_mdata(x)) {
      Some(i) if i < ctx.len() => {
        self.l.is_below_ty(&lift(&ctx[ctx.len() - 1 - i], i + 1))
      },
      _ => false,
    }
  }

  /// `recS`.
  fn go(
    &self,
    tm: &mut Tm,
    hs: &mut Holes,
    fuel: usize,
    ctx: &[Expr],
    e: &Expr,
  ) -> R<Expr> {
    if fuel == 0 {
      return Err("recovery: recursion bound exhausted".into());
    }
    let fuel = fuel - 1;
    let l = self.l;
    if matches!(e.as_data(), ExprData::Proj(..) | ExprData::App(..)) {
      let (steps, base) = path_chain(e);
      if let Some(i) = bvar_idx(&strip_mdata(&base))
        && i < ctx.len()
      {
        let ty = lift(&ctx[ctx.len() - 1 - i], i + 1);
        if let Some((t, j, entry)) = below_walk(tm, l, &ty, &steps)? {
          let g = &l.groups[j];
          let (projs, tail) = proj_prefix(&extract(&steps, t + 1, steps.len()));
          let Some((idx, len)) = path_prefix(g.size(), &projs) else {
            return Err(
              "recovery: a path that does not select a function".into(),
            );
          };
          if !(steps_fit(&g.spine, idx, &extract(&projs, 0, len))
            || g.size() < 2)
          {
            return Err(
              "recovery: a path whose projections are not the packing's".into(),
            );
          }
          let Some(&m) = g.members.get(idx) else {
            return Err("recovery: no such member".into());
          };
          let (_, eargs) = get_app_fn_args(&entry);
          hs.push(Hole::SCall(i));
          let mut acc = mk_app_n(cnst(&self.names[m], self.lvls), &eargs);
          let mut rest: Vec<PStep> = extract(&projs, len, projs.len())
            .into_iter()
            .map(|(s, k)| PStep::Proj(s, k))
            .collect();
          rest.extend(tail);
          for st in rest {
            match st {
              PStep::Proj(s, k) => acc = proj(&s, k, acc),
              PStep::App(x) => {
                acc = Expr::app(acc, self.go(tm, hs, fuel, ctx, &x)?)
              },
            }
          }
          return Ok(acc);
        }
      }
    }
    Ok(match e.as_data() {
      ExprData::App(..) => {
        let (h, args) = get_app_fn_args(e);
        match h.as_data() {
          ExprData::Const(c, _, _) => {
            if let Some(a) = l.aux.get(c).copied() {
              if !a.is_brec_on {
                let mut a2 = Vec::new();
                for x in &args {
                  a2.push(self.go(tm, hs, fuel, ctx, x)?);
                }
                return Ok(mk_app_n(h, &a2));
              }
              let p = l.num_params;
              let k = l.num_motives;
              let mut args2 = Vec::new();
              for (i, x) in args.iter().enumerate() {
                if p <= i && i < p + k {
                  hs.push(Hole::Expr(x.clone()));
                  args2.push(ph(&ph_motive()));
                } else {
                  args2.push(self.go(tm, hs, fuel, ctx, x)?);
                }
              }
              return Ok(mk_app_n(h, &args2));
            }
            if let Some(motives) = l.elim_motives(c) {
              let arity =
                (l.const_of)(c).map_or(0, |ci| forall_arity(ci.get_type()));
              if arity < args.len()
                && args[arity..].iter().any(|x| self.owned_var(ctx, x))
              {
                let extras: Vec<bool> = args[arity..]
                  .iter()
                  .map(|x| self.owned_var(ctx, x))
                  .collect();
                let mut args2 = Vec::new();
                for (k, x) in args.iter().enumerate() {
                  match motives.iter().find(|m| m.0 == k) {
                    Some(&(_, ma)) => {
                      let (bs, body) = peel_lams(ma, x);
                      let mut c2: Vec<Expr> = ctx.to_vec();
                      let mut bs2 = Vec::new();
                      for (nm, t, bi) in bs {
                        bs2.push((nm, self.go(tm, hs, fuel, &c2, &t)?, bi));
                        c2.push(t);
                      }
                      let (fs, rest) = peel_foralls(extras.len(), &body);
                      let mut fs2 = Vec::new();
                      for (j, (nm, t, bi)) in fs.into_iter().enumerate() {
                        let t2 = if extras.get(j).copied().unwrap_or(false) {
                          self.dict_ty(tm, hs, fuel, &c2, &t)?
                        } else {
                          self.go(tm, hs, fuel, &c2, &t)?
                        };
                        fs2.push((nm, t2, bi));
                        c2.push(t);
                      }
                      let r = self.go(tm, hs, fuel, &c2, &rest)?;
                      args2.push(mk_lams(&bs2, mk_foralls(&fs2, r)));
                    },
                    None => args2.push(self.go(tm, hs, fuel, ctx, x)?),
                  }
                }
                return Ok(mk_app_n(h, &args2));
              }
            }
            let mut a2 = Vec::new();
            for x in &args {
              a2.push(self.go(tm, hs, fuel, ctx, x)?);
            }
            mk_app_n(h, &a2)
          },
          _ => {
            let h2 = self.go(tm, hs, fuel, ctx, &h)?;
            let mut a2 = Vec::new();
            for x in &args {
              a2.push(self.go(tm, hs, fuel, ctx, x)?);
            }
            mk_app_n(h2, &a2)
          },
        }
      },
      ExprData::Lam(nm, t, b, bi, _) => {
        let t2 = if l.is_below_ty(t) {
          self.dict_ty(tm, hs, fuel, ctx, t)?
        } else {
          self.go(tm, hs, fuel, ctx, t)?
        };
        let mut c2 = ctx.to_vec();
        c2.push(t.clone());
        Expr::lam(nm.clone(), t2, self.go(tm, hs, fuel, &c2, b)?, bi.clone())
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        let t2 = self.go(tm, hs, fuel, ctx, t)?;
        let mut c2 = ctx.to_vec();
        c2.push(t.clone());
        Expr::all(nm.clone(), t2, self.go(tm, hs, fuel, &c2, b)?, bi.clone())
      },
      ExprData::LetE(nm, t, v, b, nd, _) => {
        let t2 = self.go(tm, hs, fuel, ctx, t)?;
        let v2 = self.go(tm, hs, fuel, ctx, v)?;
        let mut c2 = ctx.to_vec();
        c2.push(t.clone());
        Expr::letE(nm.clone(), t2, v2, self.go(tm, hs, fuel, &c2, b)?, *nd)
      },
      ExprData::Proj(s, i, x, _) => {
        Expr::proj(s.clone(), i.clone(), self.go(tm, hs, fuel, ctx, x)?)
      },
      ExprData::Mdata(d, x, _) => {
        Expr::mdata(d.clone(), self.go(tm, hs, fuel, ctx, x)?)
      },
      _ => e.clone(),
    })
  }
}

/// `leanSearch`.
fn lean_search(
  tm: &mut Tm,
  l: &StructLayout<'_>,
  ty: &Expr,
  j: usize,
  major: &Expr,
) -> R<Option<Vec<PStep>>> {
  let Some((c, us, args)) = const_app(ty) else { return Ok(None) };
  if args.len() < l.num_params + l.num_motives {
    return Ok(None);
  }
  let mut cans = Vec::new();
  let mut args2 = args.clone();
  for k in 0..l.num_motives {
    let f = tm.fresh();
    args2[l.num_params + k] = fvar(&f);
    cans.push(f);
  }
  let Some(can) = cans.get(j).cloned() else { return Ok(None) };
  let start = mk_app_n(cnst(&c, &us), &args2);
  let major_args = get_app_fn_args(&strip_mdata(major)).1;
  let const_of = l.const_of;
  let is_terminal = |w: &Expr| match const_app(w) {
    Some((h, _, _)) => h == ln("PUnit") || h == ln("True"),
    None => false,
  };
  let node_struct = |w: &Expr| match const_app(w) {
    Some((h, _, _)) => {
      if h == n_and() {
        n_and()
      } else {
        n_pprod()
      }
    },
    None => n_pprod(),
  };
  fn search2(
    const_of: ConstOf<'_>,
    can: &Name,
    major: &Expr,
    is_terminal: &dyn Fn(&Expr) -> bool,
    node_struct: &dyn Fn(&Expr) -> Name,
    fuel: usize,
    cur: &Expr,
    acc: Vec<PStep>,
  ) -> Option<Vec<PStep>> {
    if fuel == 0 {
      return None;
    }
    let fuel = fuel - 1;
    let w = whnf(const_of, WHNF_FUEL, cur);
    match decode_node(PackKind::Pprod, &w) {
      Some((_, _, d1, d2)) => {
        let s = node_struct(&w);
        let mut a1 = acc.clone();
        a1.push(PStep::Proj(s.clone(), 0));
        search2(const_of, can, major, is_terminal, node_struct, fuel, &d1, a1)
          .or_else(|| {
            let mut a2 = acc;
            a2.push(PStep::Proj(s, 1));
            search2(
              const_of,
              can,
              major,
              is_terminal,
              node_struct,
              fuel,
              &d2,
              a2,
            )
          })
      },
      None => {
        if is_terminal(&w) {
          return None;
        }
        let (h, fargs) = get_app_fn_args(&w);
        match h.as_data() {
          ExprData::Fvar(f, _) => {
            if f == can
              && fargs.last().is_some_and(|a| {
                alpha_eq(&strip_all_mdata(a), &strip_all_mdata(major))
              })
            {
              Some(acc)
            } else {
              None
            }
          },
          _ => None,
        }
      },
    }
  }
  let inst_entry = |w: &Expr| -> Option<(Expr, Vec<PStep>)> {
    let mut k = 0;
    let mut cur = w.clone();
    for _ in 0..major_args.len() + 1 {
      match strip_mdata(&whnf(const_of, WHNF_FUEL, &cur)).as_data() {
        ExprData::ForallE(_, _, b, _, _) => {
          k += 1;
          cur = b.clone();
        },
        _ => break,
      }
    }
    if major_args.len() < k {
      return None;
    }
    let tail_args =
      extract(&major_args, major_args.len() - k, major_args.len());
    let mut ent = w.clone();
    for x in &tail_args {
      match strip_mdata(&whnf(const_of, WHNF_FUEL, &ent)).as_data() {
        ExprData::ForallE(_, _, b, _, _) => {
          ent = instantiate_rev(b, std::slice::from_ref(x))
        },
        _ => return None,
      }
    }
    Some((ent, tail_args.into_iter().map(PStep::App).collect()))
  };
  #[allow(clippy::too_many_arguments)]
  fn search1(
    const_of: ConstOf<'_>,
    can: &Name,
    major: &Expr,
    is_terminal: &dyn Fn(&Expr) -> bool,
    node_struct: &dyn Fn(&Expr) -> Name,
    inst_entry: &dyn Fn(&Expr) -> Option<(Expr, Vec<PStep>)>,
    fuel: usize,
    cur: &Expr,
    acc: Vec<PStep>,
  ) -> Option<Vec<PStep>> {
    if fuel == 0 {
      return None;
    }
    let fuel = fuel - 1;
    let w = whnf(const_of, WHNF_FUEL, cur);
    match decode_node(PackKind::Pprod, &w) {
      Some((_, _, d1, d2)) => {
        let s = node_struct(&w);
        let mut a1 = acc.clone();
        a1.push(PStep::Proj(s.clone(), 0));
        search1(
          const_of,
          can,
          major,
          is_terminal,
          node_struct,
          inst_entry,
          fuel,
          &d1,
          a1,
        )
        .or_else(|| {
          let mut a2 = acc;
          a2.push(PStep::Proj(s, 1));
          search1(
            const_of,
            can,
            major,
            is_terminal,
            node_struct,
            inst_entry,
            fuel,
            &d2,
            a2,
          )
        })
      },
      None => {
        if is_terminal(&w) {
          return None;
        }
        match inst_entry(&w) {
          Some((e2, apps)) => {
            let mut a = acc;
            a.extend(apps);
            search2(
              const_of,
              can,
              major,
              is_terminal,
              node_struct,
              fuel,
              &e2,
              a,
            )
          },
          None => None,
        }
      },
    }
  }
  Ok(search1(
    const_of,
    &can,
    major,
    &is_terminal,
    &node_struct,
    &inst_entry,
    64,
    &start,
    Vec::new(),
  ))
}

struct EncS<'a, 'b> {
  l: &'a StructLayout<'b>,
  names: &'a [Name],
  member_group: &'a [(usize, usize)],
}

impl EncS<'_, '_> {
  fn go(
    &self,
    tm: &mut Tm,
    hs: &mut Holes,
    fuel: usize,
    ctx: &[Expr],
    e: &Expr,
  ) -> R<Expr> {
    if fuel == 0 {
      return Err("recovery: recursion bound exhausted".into());
    }
    let fuel = fuel - 1;
    let l = self.l;
    match e.as_data() {
      ExprData::App(..) | ExprData::Const(..) | ExprData::Proj(..) => {
        let (h, args) = get_app_fn_args(e);
        if let ExprData::Const(c, _, _) = h.as_data() {
          if let Some(m) = self.names.iter().position(|n| n == c) {
            let (j, idx) = self.member_group[m];
            let g = &l.groups[j];
            if args.len() < g.arity {
              return Err("recovery: a call with too few arguments".into());
            }
            let eargs = extract(&args, 0, g.arity);
            let Some(major) = eargs.last().cloned() else {
              return Err("recovery: a call without its argument".into());
            };
            let Hole::SCall(i) = hs.pop()? else {
              return Err("recovery: a structural call was expected".into());
            };
            if i >= ctx.len() {
              return Err("recovery: the dictionary is out of scope".into());
            }
            let ty = lift(&ctx[ctx.len() - 1 - i], i + 1);
            let Some(steps) = lean_search(tm, l, &ty, j, &major)? else {
              return Err(
                "recovery: Lean's search does not find the call".into(),
              );
            };
            let mut all_steps = steps;
            if g.size() >= 2 {
              all_steps.extend(
                g.spine
                  .proj_steps(idx)
                  .into_iter()
                  .map(|(s, k)| PStep::Proj(s, k)),
              );
            }
            let mut acc = apply_steps(&all_steps, &mk_bvar(i));
            for x in &args[g.arity..] {
              acc = Expr::app(acc, self.go(tm, hs, fuel, ctx, x)?);
            }
            return Ok(acc);
          }
          if l.aux.contains_key(c) {
            let p = l.num_params;
            let k = l.num_motives;
            let mut args2 = Vec::new();
            for (kk, x) in args.iter().enumerate() {
              if p <= kk && kk < p + k && is_const_named(x, &ph_motive()) {
                args2.push(hs.pop_expr()?);
              } else {
                args2.push(self.go(tm, hs, fuel, ctx, x)?);
              }
            }
            return Ok(mk_app_n(h, &args2));
          }
        }
        Ok(match e.as_data() {
          ExprData::App(..) => {
            let h2 = self.go(tm, hs, fuel, ctx, &h)?;
            let mut a2 = Vec::new();
            for x in &args {
              a2.push(self.go(tm, hs, fuel, ctx, x)?);
            }
            mk_app_n(h2, &a2)
          },
          ExprData::Proj(s, i, x, _) => {
            Expr::proj(s.clone(), i.clone(), self.go(tm, hs, fuel, ctx, x)?)
          },
          _ => e.clone(),
        })
      },
      ExprData::Lam(nm, t, b, bi, _) => {
        let t2 = self.go(tm, hs, fuel, ctx, t)?;
        let mut c2 = ctx.to_vec();
        c2.push(t.clone());
        Ok(Expr::lam(
          nm.clone(),
          t2,
          self.go(tm, hs, fuel, &c2, b)?,
          bi.clone(),
        ))
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        let t2 = self.go(tm, hs, fuel, ctx, t)?;
        let mut c2 = ctx.to_vec();
        c2.push(t.clone());
        Ok(Expr::all(
          nm.clone(),
          t2,
          self.go(tm, hs, fuel, &c2, b)?,
          bi.clone(),
        ))
      },
      ExprData::LetE(nm, t, v, b, nd, _) => {
        let t2 = self.go(tm, hs, fuel, ctx, t)?;
        let v2 = self.go(tm, hs, fuel, ctx, v)?;
        let mut c2 = ctx.to_vec();
        c2.push(t.clone());
        Ok(Expr::letE(nm.clone(), t2, v2, self.go(tm, hs, fuel, &c2, b)?, *nd))
      },
      ExprData::Mdata(d, x, _) => {
        Ok(Expr::mdata(d.clone(), self.go(tm, hs, fuel, ctx, x)?))
      },
      _ => Ok(e.clone()),
    }
  }
}

/// `recoverStructural`.
fn recover_structural(
  tm: &mut Tm,
  members: &[Decl],
  aux: &[Decl],
  const_of: ConstOf<'_>,
) -> R<Vec<Expr>> {
  let n = members.len();
  let l = struct_layout(members, aux, &id_perm(n), const_of)?;
  if l.num_fun_types > 0 {
    return Err(
      "recovery: the inductive-predicate route is not recovered".into(),
    );
  }
  transport_structural(tm, members, aux, &id_perm(n), const_of, &[], true)?;
  let names: Vec<Name> = members.iter().map(|d| d.name.clone()).collect();
  let lvls: Vec<Level> =
    members[0].level_params.iter().map(|p| Level::param(p.clone())).collect();
  let mut member_group = vec![(0usize, 0usize); n];
  for (j, g) in l.groups.iter().enumerate() {
    for (k, &m) in g.members.iter().enumerate() {
      member_group[m] = (j, k);
    }
  }
  let mut out = Vec::new();
  let rs = RecS { l: &l, names: &names, lvls: &lvls };
  let es = EncS { l: &l, names: &names, member_group: &member_group };
  for d in members {
    let f_name = mk_str(&d.name, "_f");
    let Some(f) = aux.iter().find(|x| x.name == f_name) else {
      return Err(format!(
        "recovery: no functional for {}",
        name_to_string(&f_name)
      ));
    };
    let mut hs = Holes::default();
    let spec = rs.go(tm, &mut hs, DEFAULT_FUEL, &[], &f.value)?;
    let mut hs2 = Holes { hs: hs.hs.clone(), i: 0 };
    let back = es.go(tm, &mut hs2, DEFAULT_FUEL, &[], &spec)?;
    if !(hs2.i == hs.hs.len() && alpha_eq(&back, &f.value)) {
      return Err(format!(
        "recovery: re-encoding {} does not give Lean's term back",
        name_to_string(&f_name)
      ));
    }
    out.push(spec);
  }
  Ok(out)
}

/// `recW`.
fn rec_w(
  l: &WfLayout,
  names: &[Name],
  lvls: &[Level],
  hs: &mut Holes,
  fuel: usize,
  ctx: &[bool],
  e: &Expr,
) -> R<Expr> {
  if fuel == 0 {
    return Err("recovery: recursion bound exhausted".into());
  }
  let fuel = fuel - 1;
  let push = |c: &[bool], v: bool| {
    let mut c2 = c.to_vec();
    c2.push(v);
    c2
  };
  let is_rec = |i: usize| i < ctx.len() && ctx[ctx.len() - 1 - i];
  match e.as_data() {
    ExprData::App(..) => {
      let (h, args) = get_app_fn_args(e);
      if let ExprData::Const(name, levels, _) = h.as_data()
        && *name == ln("PSigma.casesOn")
        && args.len() == 6
        && let Some(identity) = bvar_idx(&strip_mdata(&args[5]))
        && is_rec(identity)
      {
        let (mn, mt, rn, rt, result, rbi, mbi) = match strip_mdata(&args[2])
          .as_data()
        {
          ExprData::Lam(mn, mt, b, mbi, _) => match b.as_data() {
            ExprData::ForallE(rn, rt, result, rbi, _) => (
              mn.clone(),
              mt.clone(),
              rn.clone(),
              rt.clone(),
              result.clone(),
              rbi.clone(),
              mbi.clone(),
            ),
            _ => {
              return Err(
                "recovery: threaded PSigma motive has no recursion binder"
                  .into(),
              );
            },
          },
          _ => {
            return Err(
              "recovery: threaded PSigma motive has no recursion binder".into(),
            );
          },
        };
        let minor = strip_mdata(&args[4]);
        let parts = (|| {
          let ExprData::Lam(an, aty, b1, abi, _) = minor.as_data() else {
            return None;
          };
          let ExprData::Lam(bn, bty, b2, bbi, _) = b1.as_data() else {
            return None;
          };
          let ExprData::Lam(cn, cty, body, cbi, _) = b2.as_data() else {
            return None;
          };
          Some((
            an.clone(),
            aty.clone(),
            abi.clone(),
            bn.clone(),
            bty.clone(),
            bbi.clone(),
            cn.clone(),
            cty.clone(),
            body.clone(),
            cbi.clone(),
          ))
        })();
        let Some((an, aty, abi, bn, bty, bbi, cn, cty, body, cbi)) = parts
        else {
          return Err(
            "recovery: threaded PSigma minor has no recursion binder".into(),
          );
        };
        let alpha = rec_w(l, names, lvls, hs, fuel, ctx, &args[0])?;
        let beta = rec_w(l, names, lvls, hs, fuel, ctx, &args[1])?;
        let mt = rec_w(l, names, lvls, hs, fuel, ctx, &mt)?;
        hs.push(Hole::Expr(rt));
        let result = rec_w(
          l,
          names,
          lvls,
          hs,
          fuel,
          &push(&push(ctx, false), false),
          &result,
        )?;
        let motive =
          Expr::lam(mn, mt, Expr::all(rn, ph(&ph_rec_var()), result, rbi), mbi);
        let major = rec_w(l, names, lvls, hs, fuel, ctx, &args[3])?;
        let aty = rec_w(l, names, lvls, hs, fuel, ctx, &aty)?;
        let bty = rec_w(l, names, lvls, hs, fuel, &push(ctx, false), &bty)?;
        hs.push(Hole::Expr(cty));
        let body = rec_w(
          l,
          names,
          lvls,
          hs,
          fuel,
          &push(&push(&push(ctx, false), false), true),
          &body,
        )?;
        let minor = Expr::lam(
          an,
          aty,
          Expr::lam(bn, bty, Expr::lam(cn, ph(&ph_rec_var()), body, cbi), bbi),
          abi,
        );
        hs.push(Hole::Expr(args[5].clone()));
        return Ok(mk_app_n(
          cnst(name, levels),
          &[alpha, beta, motive, major, minor, ph(&ph_rec_var())],
        ));
      }
      match h.as_data() {
        ExprData::Bvar(..) => {
          let i = bvar_idx(&h).unwrap();
          if is_rec(i) {
            let Some(y) = args.first() else {
              return Err("recovery: a bare recursion variable".into());
            };
            let Some(pf) = args.get(1) else {
              return Err(
                "recovery: a recursive call without its proof".into(),
              );
            };
            let Some((s, j, v)) = decode_inj(l.n, y) else {
              return Err(
                "recovery: a recursive call whose argument is not an injection"
                  .into(),
              );
            };
            if !l.is_clique(&s) {
              return Err(
                "recovery: a recursive call into another packing".into(),
              );
            }
            hs.push(Hole::WCall(i, s, pf.clone()));
            let mut acc = Expr::app(
              cnst(&names[j], lvls),
              rec_w(l, names, lvls, hs, fuel, ctx, &v)?,
            );
            for x in &args[2..] {
              acc = Expr::app(acc, rec_w(l, names, lvls, hs, fuel, ctx, x)?);
            }
            return Ok(acc);
          }
          let mut a2 = Vec::new();
          for x in &args {
            a2.push(rec_w(l, names, lvls, hs, fuel, ctx, x)?);
          }
          Ok(mk_app_n(h, &a2))
        },
        ExprData::Const(..) => {
          let mut a2 = Vec::new();
          for x in &args {
            a2.push(rec_w(l, names, lvls, hs, fuel, ctx, x)?);
          }
          Ok(mk_app_n(h, &a2))
        },
        _ => {
          let h2 = rec_w(l, names, lvls, hs, fuel, ctx, &h)?;
          let mut a2 = Vec::new();
          for x in &args {
            a2.push(rec_w(l, names, lvls, hs, fuel, ctx, x)?);
          }
          Ok(mk_app_n(h2, &a2))
        },
      }
    },
    ExprData::Lam(nm, t, b, bi, _) => Ok(Expr::lam(
      nm.clone(),
      rec_w(l, names, lvls, hs, fuel, ctx, t)?,
      rec_w(l, names, lvls, hs, fuel, &push(ctx, false), b)?,
      bi.clone(),
    )),
    ExprData::ForallE(nm, t, b, bi, _) => Ok(Expr::all(
      nm.clone(),
      rec_w(l, names, lvls, hs, fuel, ctx, t)?,
      rec_w(l, names, lvls, hs, fuel, &push(ctx, false), b)?,
      bi.clone(),
    )),
    ExprData::LetE(nm, t, v, b, nd, _) => {
      let t2 = rec_w(l, names, lvls, hs, fuel, ctx, t)?;
      let v2 = rec_w(l, names, lvls, hs, fuel, ctx, v)?;
      Ok(Expr::letE(
        nm.clone(),
        t2,
        v2,
        rec_w(l, names, lvls, hs, fuel, &push(ctx, false), b)?,
        *nd,
      ))
    },
    ExprData::Bvar(..) => {
      if is_rec(bvar_idx(e).unwrap()) {
        return Err(
          "recovery: exact recursive binder escapes the decoded call region"
            .into(),
        );
      }
      Ok(e.clone())
    },
    ExprData::Proj(s, i, x, _) => Ok(Expr::proj(
      s.clone(),
      i.clone(),
      rec_w(l, names, lvls, hs, fuel, ctx, x)?,
    )),
    ExprData::Mdata(d, x, _) => {
      Ok(Expr::mdata(d.clone(), rec_w(l, names, lvls, hs, fuel, ctx, x)?))
    },
    _ => Ok(e.clone()),
  }
}

/// `encW`.
fn enc_w(names: &[Name], hs: &mut Holes, fuel: usize, e: &Expr) -> R<Expr> {
  if fuel == 0 {
    return Err("recovery: recursion bound exhausted".into());
  }
  let fuel = fuel - 1;
  if is_const_named(e, &ph_rel()) || is_const_named(e, &ph_rec_var()) {
    return hs.pop_expr();
  }
  Ok(match e.as_data() {
    ExprData::App(..) => {
      let (h, args) = get_app_fn_args(e);
      if let ExprData::Const(c, _, _) = h.as_data()
        && let Some(j) = names.iter().position(|n| n == c)
      {
        let Some(v) = args.first() else {
          return Err("recovery: a call without its argument".into());
        };
        let Hole::WCall(i, s, pf) = hs.pop()? else {
          return Err("recovery: a well-founded call was expected".into());
        };
        let v2 = enc_w(names, hs, fuel, v)?;
        let mut acc = mk_app_n(mk_bvar(i), &[mk_inj(&s, j, &v2), pf]);
        for x in &args[1..] {
          acc = Expr::app(acc, enc_w(names, hs, fuel, x)?);
        }
        return Ok(acc);
      }
      let h2 = enc_w(names, hs, fuel, &h)?;
      let mut a2 = Vec::new();
      for x in &args {
        a2.push(enc_w(names, hs, fuel, x)?);
      }
      mk_app_n(h2, &a2)
    },
    ExprData::Lam(nm, t, b, bi, _) => Expr::lam(
      nm.clone(),
      enc_w(names, hs, fuel, t)?,
      enc_w(names, hs, fuel, b)?,
      bi.clone(),
    ),
    ExprData::ForallE(nm, t, b, bi, _) => Expr::all(
      nm.clone(),
      enc_w(names, hs, fuel, t)?,
      enc_w(names, hs, fuel, b)?,
      bi.clone(),
    ),
    ExprData::LetE(nm, t, v, b, nd, _) => Expr::letE(
      nm.clone(),
      enc_w(names, hs, fuel, t)?,
      enc_w(names, hs, fuel, v)?,
      enc_w(names, hs, fuel, b)?,
      *nd,
    ),
    ExprData::Proj(s, i, x, _) => {
      Expr::proj(s.clone(), i.clone(), enc_w(names, hs, fuel, x)?)
    },
    ExprData::Mdata(d, x, _) => {
      Expr::mdata(d.clone(), enc_w(names, hs, fuel, x)?)
    },
    _ => e.clone(),
  })
}

/// `recoverWF`.
fn recover_wf(
  tm: &mut Tm,
  members: &[Decl],
  mut_decl: &Decl,
  const_of: ConstOf<'_>,
) -> R<Vec<Expr>> {
  let n = members.len();
  let l = wf_layout(members, mut_decl, &id_perm(n), &mut_decl.name)?;
  let names: Vec<Name> = members.iter().map(|d| d.name.clone()).collect();
  let lvls: Vec<Level> =
    members[0].level_params.iter().map(|p| Level::param(p.clone())).collect();
  let (_, fix_app) = peel_lams(l.num_fixed, &mut_decl.value);
  conjugate_wf_root(tm, &l, &fix_app, const_of)?;
  let (_, fargs) = get_app_fn_args(&strip_mdata(&fix_app));
  let Some(f) = fargs.last() else {
    return Err("recovery: no functional in the packed function".into());
  };
  let (bs, body) = peel_lams(2, f);
  if bs.len() != 2 {
    return Err("recovery: the functional is not `λ x a. …`".into());
  }
  let Some(t) = decode_tree(n, &body) else {
    return Err("recovery: the functional is not Lean's case tree".into());
  };
  if !l.is_clique(&t.spine) {
    return Err("recovery: a case tree over another packing".into());
  }
  let mut out = Vec::new();
  for leaf in &t.leaves {
    let sl = strip_mdata(leaf);
    let parts = (|| {
      let ExprData::Lam(pn, pt, b, pbi, _) = sl.as_data() else { return None };
      let ExprData::Lam(rn, rt, body, rbi, _) = b.as_data() else {
        return None;
      };
      Some((
        pn.clone(),
        pt.clone(),
        pbi.clone(),
        rn.clone(),
        rt.clone(),
        body.clone(),
        rbi.clone(),
      ))
    })();
    let Some((pn, pt, pbi, rn, rt, body, rbi)) = parts else {
      return Err("recovery: missing decoded leaf entry binders".into());
    };
    let mut hs = Holes::default();
    hs.push(Hole::Expr(rt));
    let body2 =
      rec_w(&l, &names, &lvls, &mut hs, DEFAULT_FUEL, &[false, true], &body)?;
    let spec =
      Expr::lam(pn, pt, Expr::lam(rn, ph(&ph_rec_var()), body2, rbi), pbi);
    let mut hs2 = Holes { hs: hs.hs.clone(), i: 0 };
    let back = enc_w(&names, &mut hs2, DEFAULT_FUEL, &spec)?;
    if !(hs2.i == hs.hs.len() && alpha_eq(&back, leaf)) {
      return Err(
        "recovery: re-encoding a leaf does not give Lean's term back".into(),
      );
    }
    out.push(spec);
  }
  Ok(out)
}

/// `recP`.
fn rec_p(
  s: &Spine,
  names: &[Name],
  lvls: &[Level],
  fuel: usize,
  d: usize,
  e: &Expr,
) -> R<Expr> {
  if fuel == 0 {
    return Err("recovery: recursion bound exhausted".into());
  }
  let fuel = fuel - 1;
  Ok(match e.as_data() {
    ExprData::Proj(sn, i, x, _) => {
      let (steps, base) = proj_chain(e);
      match bvar_idx(&strip_mdata(&base)) {
        Some(b) => {
          if b == d {
            let Some((j, len)) = path_prefix(s.size(), &steps) else {
              return Err("recovery: a projection of the packed variable that is not a path".into());
            };
            if !steps_fit(s, j, &extract(&steps, 0, len)) {
              return Err(
                "recovery: a path whose projections are not the packing's"
                  .into(),
              );
            }
            let Some(m) = names.get(j) else {
              return Err("recovery: no such member".into());
            };
            apply_projs(&extract(&steps, len, steps.len()), &cnst(m, lvls))
          } else {
            e.clone()
          }
        },
        None => {
          Expr::proj(sn.clone(), i.clone(), rec_p(s, names, lvls, fuel, d, x)?)
        },
      }
    },
    ExprData::Bvar(..) => {
      if is_bvar(e, d) {
        return Err(
          "recovery: the packed variable outside a projection path".into(),
        );
      }
      e.clone()
    },
    ExprData::App(f, a, _) => Expr::app(
      rec_p(s, names, lvls, fuel, d, f)?,
      rec_p(s, names, lvls, fuel, d, a)?,
    ),
    ExprData::Lam(nm, t, b, bi, _) => Expr::lam(
      nm.clone(),
      rec_p(s, names, lvls, fuel, d, t)?,
      rec_p(s, names, lvls, fuel, d + 1, b)?,
      bi.clone(),
    ),
    ExprData::ForallE(nm, t, b, bi, _) => Expr::all(
      nm.clone(),
      rec_p(s, names, lvls, fuel, d, t)?,
      rec_p(s, names, lvls, fuel, d + 1, b)?,
      bi.clone(),
    ),
    ExprData::LetE(nm, t, v, b, nd, _) => Expr::letE(
      nm.clone(),
      rec_p(s, names, lvls, fuel, d, t)?,
      rec_p(s, names, lvls, fuel, d, v)?,
      rec_p(s, names, lvls, fuel, d + 1, b)?,
      *nd,
    ),
    ExprData::Mdata(md, x, _) => {
      Expr::mdata(md.clone(), rec_p(s, names, lvls, fuel, d, x)?)
    },
    _ => e.clone(),
  })
}

/// `encP`.
fn enc_p(s: &Spine, names: &[Name], d: usize, e: &Expr) -> Expr {
  match e.as_data() {
    ExprData::Const(c, _, _) => match names.iter().position(|n| n == c) {
      Some(j) => apply_projs(&s.proj_steps(j), &mk_bvar(d)),
      None => e.clone(),
    },
    ExprData::Proj(sn, i, x, _) => {
      Expr::proj(sn.clone(), i.clone(), enc_p(s, names, d, x))
    },
    ExprData::App(f, a, _) => {
      Expr::app(enc_p(s, names, d, f), enc_p(s, names, d, a))
    },
    ExprData::Lam(nm, t, b, bi, _) => Expr::lam(
      nm.clone(),
      enc_p(s, names, d, t),
      enc_p(s, names, d + 1, b),
      bi.clone(),
    ),
    ExprData::ForallE(nm, t, b, bi, _) => Expr::all(
      nm.clone(),
      enc_p(s, names, d, t),
      enc_p(s, names, d + 1, b),
      bi.clone(),
    ),
    ExprData::LetE(nm, t, v, b, nd, _) => Expr::letE(
      nm.clone(),
      enc_p(s, names, d, t),
      enc_p(s, names, d, v),
      enc_p(s, names, d + 1, b),
      *nd,
    ),
    ExprData::Mdata(md, x, _) => Expr::mdata(md.clone(), enc_p(s, names, d, x)),
    _ => e.clone(),
  }
}

/// `recoverPF`.
fn recover_pf(members: &[Decl], packed: &Decl) -> R<(Vec<Expr>, PfLayout)> {
  let n = members.len();
  let l = pf_layout(members, packed, &id_perm(n), &packed.name)?;
  let names: Vec<Name> = members.iter().map(|d| d.name.clone()).collect();
  let lvls: Vec<Level> =
    members[0].level_params.iter().map(|p| Level::param(p.clone())).collect();
  let (_, body) = peel_lams(l.num_fixed, &packed.value);
  let Some((head, _, args)) = const_app(&strip_mdata(&body)) else {
    return Err(
      "recovery: the packed value is not a fixpoint application".into(),
    );
  };
  if !((head == n_order_fix() || head == ln("Lean.Order.lfp_monotone"))
    && args.len() == 4)
  {
    return Err("recovery: unsupported partial-fixpoint root".into());
  }
  let (domain, functional) = match strip_mdata(&args[2]).as_data() {
    ExprData::Lam(_, d, f, _, _) => (d.clone(), f.clone()),
    _ => {
      return Err(
        "recovery: the fixpoint functional has no recursive binder".into(),
      );
    },
  };
  let Some(input) = decode_spine(PackKind::Pprod, n, &domain) else {
    return Err(
      "recovery: the recursive binder is not a packed product".into(),
    );
  };
  let Some((output, cs)) = decode_tuple(n, &strip_mdata(&functional)) else {
    return Err("recovery: the functional has no encoded output tuple".into());
  };
  if !(l.is_clique(&input)
    && alpha_eq(&norm_order_alias(&domain), &norm_order_alias(&args[0]))
    && alpha_eq(
      &norm_order_alias(&output.typ()),
      &norm_order_alias(&lift(&domain, 1)),
    ))
  {
    return Err(
      "recovery: the decoded functional disagrees with the fixpoint packing"
        .into(),
    );
  }
  let mut out = Vec::new();
  for c in &cs {
    let spec = rec_p(&l.spine, &names, &lvls, DEFAULT_FUEL, 0, c)?;
    if !alpha_eq(&enc_p(&l.spine, &names, 0, &spec), c) {
      return Err("recovery: re-encoding a functional component does not give Lean's term back".into());
    }
    out.push(spec);
  }
  Ok((out, l))
}

fn ph_enc() -> Expr {
  ph(&ph_rec_var())
}

fn fixed_args_of(num_params: usize, q: &[usize]) -> Vec<Expr> {
  q.iter().map(|&p| mk_bvar(num_params - 1 - p)).collect()
}

/// `normalisedSpecs`.
pub fn normalised_specs(inp: &Input<'_>) -> R<Vec<Expr>> {
  let n = inp.members.len();
  let params_of = |d: &Decl| peel_lams(lam_arity(&d.value), &d.value).0;
  match inp.encoding {
    Encoding::WellFounded => {
      let Some(packed) = find_packed(&inp.members, &inp.aux) else {
        return Err("recovery: no packed function".into());
      };
      let l = wf_layout(&inp.members, &packed, &id_perm(n), &packed.name)?;
      let leaves =
        recover_wf(&mut Tm::default(), &inp.members, &packed, inp.const_of)?;
      Ok(
        (0..n)
          .map(|i| {
            let d = &inp.members[i];
            let ps = params_of(d);
            let mut fixed = fixed_args_of(ps.len(), &l.member_fixed[i]);
            fixed.reverse();
            let mut a = vec![ph_enc(), ph_enc()];
            a.extend(fixed);
            mk_lams(&ps, instantiate_rev(&leaves[i], &a))
          })
          .collect(),
      )
    },
    Encoding::Structural => {
      let l = struct_layout(&inp.members, &inp.aux, &id_perm(n), inp.const_of)?;
      let member_fixed = l.member_fixed.clone();
      drop(l);
      let fs = recover_structural(
        &mut Tm::default(),
        &inp.members,
        &inp.aux,
        inp.const_of,
      )?;
      Ok(
        (0..n)
          .map(|i| {
            let d = &inp.members[i];
            let ps = params_of(d);
            mk_lams(
              &ps,
              mk_app_n(
                fs[i].clone(),
                &fixed_args_of(ps.len(), &member_fixed[i]),
              ),
            )
          })
          .collect(),
      )
    },
    Encoding::PartialFixpoint => {
      let Some(packed) = find_packed(&inp.members, &inp.aux) else {
        return Err("recovery: no packed fixpoint".into());
      };
      let (cs, l) = recover_pf(&inp.members, &packed)?;
      Ok(
        (0..n)
          .map(|i| {
            let d = &inp.members[i];
            let ps = params_of(d);
            let mut fixed = fixed_args_of(ps.len(), &l.member_fixed[i]);
            fixed.reverse();
            let mut a = vec![ph_enc()];
            a.extend(fixed);
            mk_lams(&ps, instantiate_rev(&cs[i], &a))
          })
          .collect(),
      )
    },
  }
}

/// `cliqueOrder`.
pub fn clique_order(
  addr: AddrOf<'_>,
  inp: &Input<'_>,
) -> R<(Vec<usize>, Vec<Vec<Name>>, OrderSource)> {
  let addr2 = |n: &Name| placeholder_addr(n).or_else(|| addr(n));
  match normalised_specs(inp) {
    Ok(specs) => {
      let members: Vec<Member> = inp
        .members
        .iter()
        .zip(specs)
        .map(|(d, v)| Member {
          name: d.name.clone(),
          level_params: d.level_params.clone(),
          typ: d.typ.clone(),
          value: v,
        })
        .collect();
      let cls = clique_classes(&addr2, &members)?;
      let order: Vec<Name> = cls.iter().flatten().cloned().collect();
      let sigma: Vec<usize> = members
        .iter()
        .map(|m| order.iter().position(|x| *x == m.name).unwrap_or(0))
        .collect();
      if !is_perm(&sigma) {
        return Err("order: the classes do not order every member".into());
      }
      Ok((sigma, cls, OrderSource::Specification))
    },
    Err(why) => {
      let members: Vec<Member> = inp
        .members
        .iter()
        .map(|d| Member {
          name: d.name.clone(),
          level_params: d.level_params.clone(),
          typ: d.typ.clone(),
          value: d.value.clone(),
        })
        .collect();
      match statement_order(&addr2, &members)? {
        Some(sigma) => {
          let cls = inv_perm(&sigma)
            .into_iter()
            .map(|i| vec![members[i].name.clone()])
            .collect();
          Ok((sigma, cls, OrderSource::Statements(why)))
        },
        None => Err(format!("NOSPEC: {why}; the statements tie")),
      }
    },
  }
}

#[allow(dead_code)]
fn _unused(_: BinderInfo) {}
