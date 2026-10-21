//! The recovered specification of a clique, and the canonical order it
//! gives (a port of `Ix/Compile/Pass/Clique/Recover.lean`).
//!
//! A theorem clique has no `EqnInfo`, so Pass 1 has no specification to
//! order it by. It is ordered by its **recovered specification**: the
//! inverse of Lean's encoding applied to Lean's own bodies, i.e. each
//! member's body with its recursion made explicit again; when that cannot be
//! recovered, by its statements alone ([`statement_order`]). The same
//! recovery orders a definition clique.
//!
//! **Recovery `R`.**
//! * Structural route (`brecOn`, theorems over data): the member's
//!   functional `f._f` (`λ fixed is x (below : T.below … x) rest. body`),
//!   one of the functionals the members' `brecOn` applications pass
//!   ([`StructLayout::f_names`]). Every path into a `below` dictionary that
//!   reaches an entry ([`below_walk`], the replay of Lean's
//!   `searchPProd`/`toBelowAux` with canaries) and then selects function `m`
//!   inside the group's packed motive becomes the call `f_m is x` (the
//!   entry's arguments), applied to whatever the path was applied to. The
//!   packed motives at the motive positions of `below`/`brecOn` applications
//!   are erased (a placeholder): they are the encoding's.
//! * Well-founded route: the leaf of `processSumCasesOn`'s tree for member
//!   `i` in the packed function (`λ v a. body`). Every application of the
//!   recursion variable `a (inj_j v) h` becomes `f_j v` (the decreasing
//!   proof `h` is dropped: it is the encoding's obligation); the recursion
//!   variable's type is erased only at the root-validated leaf entry and
//!   explicitly threaded `PSigma` eliminator positions. User relations and
//!   same-typed user binders remain intact.
//! * `partial_fixpoint` route: a component `F_i` of the fixpoint's
//!   functional, each full projection path into the packed variable to
//!   component `j` becoming the member `f_j`.
//! * The inductive-predicate route (no `_f`; below matchers) is not
//!   recovered.
//!
//! **The check: re-encoding.** `R` records what it erased and which
//! dictionary or recursion variable each call used ([`Hole`]). `E` rebuilds
//! the encoding from the specification: each structural call by Lean's own
//! search for the dictionary entry ([`lean_search`]: `searchPProd` and
//! `toBelowAux` of `Structural/BRecOn.lean`, first match in Lean's order,
//! then the path to the function inside the packed motive), each
//! well-founded call by `ArgsPacker`'s injection ([`mk_inj`]), each
//! `partial_fixpoint` call by Lean's projection path; the erased annotations
//! are restored verbatim. The recovery is accepted only if `E (R t)` is
//! Lean's term (up to binder names and `mdata`); otherwise the clique is
//! ordered by its statements, or keeps its baseline (`NOSPEC`).
//!
//! **The order** ([`clique_order`]). Pass 1's classes over the members with
//! the statement as the type and the normalised specification as the value
//! ([`clique_classes`], under the compiler's rules, [`Rules::default`],
//! Lean's `Rules.compiler`: the name-hash seed): the statements are compared
//! first, and recursive calls compare by class, as in every definition
//! clique. Members that are still in one class have bisimilar
//! specifications; their order is Pass 1's seed order within the class, and
//! the hook may alias them.
//!
//! The placeholders are reserved names (`_ix_spec_*`) with fixed addresses.
//! Total and pure, like the transport.
//!
//! The binder contexts are Lean's arrays, kept here as one vector per walk
//! with a push before and a pop after each binder's body: the context a
//! visit sees is the one Lean passes it.

use std::slice;

use rustc_hash::FxHashSet;

use ix_common::address::Address;
use ix_common::env::{Expr, ExprData, Level, Name};

use super::basic::{
  Binder, ConstOf, Decl, R, TState, alpha_eq_skip_mdata, bvar, bvar_idx, cnst,
  const_app, dotted, extract, fvar, instantiate_rev, inv_perm, is_perm,
  lam_arity, lift_loose, mk_app_n, mk_foralls, mk_lams, mk_str, n_and, n_pprod,
  name_to_string, peel_foralls, peel_lams, proj, root_name, strip_all_mdata,
};
use super::bounds::{SEARCH_DEPTH, TRANSPORT_FUEL, WHNF_FUEL};
use super::order::{
  AddrOf, Clique, CliqueKind, CliqueMember, Rules, clique_classes,
  statement_order,
};
use super::packing::{
  PackKind, Spine, apply_projs, decode_inj, decode_node, decode_spine,
  decode_tree, decode_tuple, mk_inj,
};
use super::pf::{PfLayout, n_order_fix, norm_order_alias, pf_layout};
use super::plan::{Encoding, OrderSource};
use super::structural::{
  PStep, StructLayout, apply_steps, path_chain, path_prefix, proj_chain,
  proj_prefix, steps_fit, struct_layout, transport_structural,
};
use super::telescope::{id_perm, whnf};
use super::transport::{Input, find_packed};
use super::wf::{WfLayout, conjugate_wf_root, wf_layout};
use crate::compile::pass3::expr::{get_app_fn_args, strip_mdata};

/// The error of an exhausted recovery walk.
pub const RECOVERY_EXHAUSTED: &str = "recovery: recursion bound exhausted";

// ---------------------------------------------------------------------------
// Placeholders
// ---------------------------------------------------------------------------

/// `phMotive`.
pub fn ph_motive() -> Name {
  root_name("_ix_spec_motive")
}

/// `phRel`.
pub fn ph_rel() -> Name {
  root_name("_ix_spec_rel")
}

/// `phRecVar`.
pub fn ph_rec_var() -> Name {
  root_name("_ix_spec_recvar")
}

/// `placeholderAddr?`: a fixed address per placeholder (no hashing needed):
/// 31 zero bytes, then the placeholder's number.
pub fn placeholder_addr(n: &Name) -> Option<Address> {
  let mk = |k: u8| {
    let bytes: Vec<u8> = std::iter::repeat_n(0u8, 31).chain([k]).collect();
    Address::from_slice(&bytes).ok()
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

/// What `R` erased or dropped, in traversal order (`Hole`).
#[derive(Clone, Debug)]
pub enum Hole {
  /// an erased annotation, restored verbatim
  Expr(Expr),
  /// a structural call through the dictionary variable `bvar i`
  SCall(usize),
  /// a well-founded call through the recursion variable `bvar i`, into the
  /// packing `s`, with the decreasing proof `h`
  WCall(usize, Spine, Expr),
}

/// The holes `R` and `E` run with (the state of Lean's `RM`): `R` appends,
/// `E` consumes from the cursor.
#[derive(Clone, Debug, Default)]
pub struct Holes {
  pub holes: Vec<Hole>,
  pub cursor: usize,
}

impl Holes {
  /// `pushHole`.
  pub fn push_hole(&mut self, h: Hole) {
    self.holes.push(h);
  }

  /// `popHole`.
  pub fn pop_hole(&mut self) -> R<Hole> {
    let Some(h) = self.holes.get(self.cursor).cloned() else {
      return Err("recovery: the holes ran out during re-encoding".into());
    };
    self.cursor += 1;
    Ok(h)
  }

  /// `popExpr`.
  pub fn pop_expr(&mut self) -> R<Expr> {
    match self.pop_hole()? {
      Hole::Expr(e) => Ok(e),
      _ => Err("recovery: an erased annotation was expected".into()),
    }
  }
}

/// `bvarType?`: the type of `bvar i` in the context `ctx` (Lean's binder
/// types, outermost first), lifted to the current depth; `None` out of
/// scope.
pub fn bvar_type(ctx: &[Expr], i: usize) -> Option<Expr> {
  if i < ctx.len() {
    ctx.get(ctx.len() - 1 - i).map(|t| lift_loose(t, i + 1, 0))
  } else {
    None
  }
}

/// `bvarMarked`: `bvar i` is marked in `ctx` (outermost first); `false` out
/// of scope.
pub fn bvar_marked(ctx: &[bool], i: usize) -> bool {
  i < ctx.len() && ctx.get(ctx.len() - 1 - i).copied().unwrap_or(false)
}

/// `isConstNamed`.
pub fn is_const_named(e: &Expr, n: &Name) -> bool {
  matches!(strip_mdata(e).as_data(), ExprData::Const(c, _, _) if c == n)
}

/// Run `k` with `xs` pushed on `ctx` (the binders of a body), and restore
/// `ctx` after, whatever `k` pushed.
fn under<X: Clone, A>(
  ctx: &mut Vec<X>,
  xs: &[X],
  k: impl FnOnce(&mut Vec<X>) -> R<A>,
) -> R<A> {
  let base = ctx.len();
  ctx.extend_from_slice(xs);
  let r = k(ctx);
  ctx.truncate(base);
  r
}

// ---------------------------------------------------------------------------
// The structural route
// ---------------------------------------------------------------------------

/// `belowWalk`: the walk of
/// [`below_path`](super::structural::below_path), returning where the path
/// reaches an entry: the step index, the group, and the entry `C_j args`. A
/// step the walk cannot follow, or an exhausted reducer, is a refusal.
pub fn below_walk(
  tm: &mut TState,
  l: &StructLayout<'_>,
  ty: &Expr,
  steps: &[PStep],
) -> R<Option<(usize, usize, Expr)>> {
  let Some((c, us, args)) = const_app(ty) else { return Ok(None) };
  let Some(a) = l.aux.get(&c) else { return Ok(None) };
  let p = l.num_params;
  let k = l.num_motives;
  if a.is_brec_on || args.len() < p.saturating_add(k) {
    return Ok(None);
  }
  // the canaries
  let cans: Vec<Name> = (0..k).map(|_| tm.fresh_fvar()).collect();
  let mut args2 = extract(&args, 0, p);
  args2.extend(cans.iter().map(fvar));
  args2.extend(extract(&args, p.saturating_add(k), args.len()));
  let mut cur = mk_app_n(cnst(&c, &us), &args2);
  for (t, step) in steps.iter().enumerate() {
    let w = whnf(l.const_of, WHNF_FUEL, &cur)?;
    match step {
      PStep::Proj(s, i) => match decode_node(PackKind::Pprod, &w) {
        Some((_, _, left, right)) => {
          let is_and = const_app(&w).is_some_and(|(h, _, _)| h == n_and());
          if (*s == n_and()) != is_and {
            return Err("recovery: a projection that is not the node's".into());
          }
          cur = if *i == 0 { left } else { right };
        },
        None => {
          return Err("recovery: a projection the walk cannot follow".into());
        },
      },
      PStep::App(x) => match strip_mdata(&w).as_data() {
        ExprData::ForallE(_, _, b, _, _) => {
          cur = instantiate_rev(b, slice::from_ref(x));
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

/// `eraseMotives`: the arguments of a `below`/`brecOn` application with the
/// motives (the positions `P ≤ k < P + K`) erased to the placeholder, each
/// erased motive recorded as a hole, and the others transformed by `go`, in
/// argument order.
pub fn erase_motives(
  l: &StructLayout<'_>,
  hs: &mut Holes,
  args: &[Expr],
  go: &mut dyn FnMut(&mut Holes, &Expr) -> R<Expr>,
) -> R<Vec<Expr>> {
  let p = l.num_params;
  let k = l.num_motives;
  let mut args2 = Vec::with_capacity(args.len());
  for (i, x) in args.iter().enumerate() {
    if p <= i && i < p.saturating_add(k) {
      hs.push_hole(Hole::Expr(x.clone()));
      args2.push(cnst(&ph_motive(), &[]));
    } else {
      args2.push(go(hs, x)?);
    }
  }
  Ok(args2)
}

/// `recS`: `R` on a structural functional, in a context of Lean's binder
/// types.
///
/// The motives of the block's `brecOn` applications (a member's root) and
/// of the `below` applications in the binder types of owned dictionaries (a
/// λ binder of a `below` type: after the ownership check every such binder
/// is the recursion's own; and the binders a matcher motive gets for an
/// owned dictionary, `MatcherApp.addArg`) are erased to a placeholder, since
/// they are the packing's; a `below` application anywhere else is the
/// user's and keeps its motive (two members that differ only there keep
/// different specifications).
pub struct StructRec<'c, 'a> {
  pub l: &'c StructLayout<'a>,
  /// the members' names, in Lean's order
  pub names: &'c [Name],
  /// the members' universe parameters, as levels
  pub lvls: &'c [Level],
}

impl StructRec<'_, '_> {
  /// An owned dictionary's binder type: its motives erased (`dictTy`).
  fn dict_ty(
    &self,
    tm: &mut TState,
    hs: &mut Holes,
    fuel: usize,
    ctx: &mut Vec<Expr>,
    t: &Expr,
  ) -> R<Expr> {
    let (h, args) = get_app_fn_args(t);
    if let ExprData::Const(c, _, _) = h.as_data()
      && let Some(a) = self.l.aux.get(c)
      && !a.is_brec_on
    {
      let mut go = |hs: &mut Holes, x: &Expr| self.rec_s(tm, hs, fuel, ctx, x);
      return Ok(mk_app_n(h, &erase_motives(self.l, hs, &args, &mut go)?));
    }
    self.rec_s(tm, hs, fuel, ctx, t)
  }

  /// `ownedVar`: `x` is a bound variable of a `below` type.
  fn owned_var(&self, ctx: &[Expr], x: &Expr) -> bool {
    match bvar_idx(&strip_mdata(x)) {
      Some(i) => bvar_type(ctx, i).is_some_and(|ty| self.l.is_below_ty(&ty)),
      None => false,
    }
  }

  /// `args.mapM (go ctx)`.
  fn map_rec(
    &self,
    tm: &mut TState,
    hs: &mut Holes,
    fuel: usize,
    ctx: &mut Vec<Expr>,
    args: &[Expr],
  ) -> R<Vec<Expr>> {
    args.iter().map(|x| self.rec_s(tm, hs, fuel, ctx, x)).collect()
  }

  /// A path into a dictionary that reaches an entry: the recovered call.
  fn dictionary_call(
    &self,
    tm: &mut TState,
    hs: &mut Holes,
    fuel: usize,
    ctx: &mut Vec<Expr>,
    e: &Expr,
  ) -> R<Option<Expr>> {
    let (steps, base) = path_chain(e);
    let Some(i) = bvar_idx(&strip_mdata(&base)) else { return Ok(None) };
    let Some(ty) = bvar_type(ctx, i) else { return Ok(None) };
    let Some((t, j, entry)) = below_walk(tm, self.l, &ty, &steps)? else {
      return Ok(None);
    };
    let Some(g) = self.l.groups.get(j) else {
      return Err("recovery: a dictionary entry of no group".into());
    };
    let (projs, tail) =
      proj_prefix(&extract(&steps, t.saturating_add(1), steps.len()));
    let Some((idx, len)) = path_prefix(g.size(), &projs) else {
      return Err("recovery: a path that does not select a function".into());
    };
    if !(steps_fit(&g.spine, idx, &extract(&projs, 0, len)) || g.size() < 2) {
      return Err(
        "recovery: a path whose projections are not the packing's".into(),
      );
    }
    let no_member = || "recovery: no such member".to_string();
    let Some(&m) = g.members.get(idx) else { return Err(no_member()) };
    let Some(name) = self.names.get(m) else { return Err(no_member()) };
    let (_, eargs) = get_app_fn_args(&entry);
    hs.push_hole(Hole::SCall(i));
    let mut acc = mk_app_n(cnst(name, self.lvls), &eargs);
    let rest = extract(&projs, len, projs.len())
      .into_iter()
      .map(|(s, k)| PStep::Proj(s, k))
      .chain(tail);
    for st in rest {
      match st {
        PStep::Proj(s, k) => acc = proj(&s, k, acc),
        PStep::App(x) => {
          acc = Expr::app(acc, self.rec_s(tm, hs, fuel, ctx, &x)?);
        },
      }
    }
    Ok(Some(acc))
  }

  /// An eliminator that receives an owned dictionary past its arity: its
  /// motive's binders for the extras are dictionary types.
  fn eliminator(
    &self,
    tm: &mut TState,
    hs: &mut Holes,
    fuel: usize,
    ctx: &mut Vec<Expr>,
    c: &Name,
    args: &[Expr],
  ) -> R<Option<Vec<Expr>>> {
    let Some(sh) = self.l.elim_shape(c) else { return Ok(None) };
    let extras: Vec<bool> =
      args.iter().skip(sh.arity).map(|x| self.owned_var(ctx, x)).collect();
    if !(sh.arity < args.len() && extras.iter().any(|&o| o)) {
      return Ok(None);
    }
    let mut args2 = Vec::with_capacity(args.len());
    for (k, x) in args.iter().enumerate() {
      match sh.motives.iter().find(|m| m.0 == k) {
        Some(&(_, ma)) => {
          let (bs, body) = peel_lams(ma, x);
          let r = under(ctx, &[], |ctx| {
            let mut bs2 = Vec::with_capacity(bs.len());
            for (nm, t, bi) in bs {
              bs2.push((nm, self.rec_s(tm, hs, fuel, ctx, &t)?, bi));
              ctx.push(t);
            }
            let (fs, rest) = peel_foralls(extras.len(), &body);
            let mut fs2 = Vec::with_capacity(fs.len());
            // `fs` has at most `extras.len()` binders
            for ((nm, t, bi), &is_dict) in fs.into_iter().zip(&extras) {
              let t2 = if is_dict {
                self.dict_ty(tm, hs, fuel, ctx, &t)?
              } else {
                self.rec_s(tm, hs, fuel, ctx, &t)?
              };
              fs2.push((nm, t2, bi));
              ctx.push(t);
            }
            let rest = self.rec_s(tm, hs, fuel, ctx, &rest)?;
            Ok(mk_lams(&bs2, mk_foralls(&fs2, rest)))
          });
          args2.push(r?);
        },
        None => args2.push(self.rec_s(tm, hs, fuel, ctx, x)?),
      }
    }
    Ok(Some(args2))
  }

  /// `recS`.
  pub fn rec_s(
    &self,
    tm: &mut TState,
    hs: &mut Holes,
    fuel: usize,
    ctx: &mut Vec<Expr>,
    e: &Expr,
  ) -> R<Expr> {
    let Some(fuel) = fuel.checked_sub(1) else {
      return Err(RECOVERY_EXHAUSTED.into());
    };
    // a path into a dictionary
    if matches!(e.as_data(), ExprData::Proj(..) | ExprData::App(..))
      && let Some(call) = self.dictionary_call(tm, hs, fuel, ctx, e)?
    {
      return Ok(call);
    }
    Ok(match e.as_data() {
      ExprData::App(..) => {
        let (h, args) = get_app_fn_args(e);
        match h.as_data() {
          ExprData::Const(c, _, _) => {
            if let Some(a) = self.l.aux.get(c) {
              // a `brecOn` application (a member's root): its motives
              // erased; a `below` application outside a dictionary's binder
              // type: the user's
              if !a.is_brec_on {
                return Ok(mk_app_n(
                  h,
                  &self.map_rec(tm, hs, fuel, ctx, &args)?,
                ));
              }
              let mut go =
                |hs: &mut Holes, x: &Expr| self.rec_s(tm, hs, fuel, ctx, x);
              return Ok(mk_app_n(
                h,
                &erase_motives(self.l, hs, &args, &mut go)?,
              ));
            }
            if let Some(args2) = self.eliminator(tm, hs, fuel, ctx, c, &args)? {
              return Ok(mk_app_n(h, &args2));
            }
            mk_app_n(h, &self.map_rec(tm, hs, fuel, ctx, &args)?)
          },
          _ => {
            let h2 = self.rec_s(tm, hs, fuel, ctx, &h)?;
            mk_app_n(h2, &self.map_rec(tm, hs, fuel, ctx, &args)?)
          },
        }
      },
      ExprData::Lam(nm, t, b, bi, _) => {
        let t2 = if self.l.is_below_ty(t) {
          self.dict_ty(tm, hs, fuel, ctx, t)?
        } else {
          self.rec_s(tm, hs, fuel, ctx, t)?
        };
        let b2 = under(ctx, slice::from_ref(t), |ctx| {
          self.rec_s(tm, hs, fuel, ctx, b)
        })?;
        Expr::lam(nm.clone(), t2, b2, bi.clone())
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        let t2 = self.rec_s(tm, hs, fuel, ctx, t)?;
        let b2 = under(ctx, slice::from_ref(t), |ctx| {
          self.rec_s(tm, hs, fuel, ctx, b)
        })?;
        Expr::all(nm.clone(), t2, b2, bi.clone())
      },
      ExprData::LetE(nm, t, v, b, nd, _) => {
        let t2 = self.rec_s(tm, hs, fuel, ctx, t)?;
        let v2 = self.rec_s(tm, hs, fuel, ctx, v)?;
        let b2 = under(ctx, slice::from_ref(t), |ctx| {
          self.rec_s(tm, hs, fuel, ctx, b)
        })?;
        Expr::letE(nm.clone(), t2, v2, b2, *nd)
      },
      ExprData::Proj(s, i, x, _) => {
        Expr::proj(s.clone(), i.clone(), self.rec_s(tm, hs, fuel, ctx, x)?)
      },
      ExprData::Mdata(d, x, _) => {
        Expr::mdata(d.clone(), self.rec_s(tm, hs, fuel, ctx, x)?)
      },
      _ => e.clone(),
    })
  }
}

/// `searchTerminal`: a dictionary's terminal node (`PUnit`, `True`): no
/// entry below it.
pub fn search_terminal(w: &Expr) -> bool {
  const_app(w)
    .is_some_and(|(h, _, _)| h == dotted("PUnit") || h == dotted("True"))
}

/// `searchNodeStruct`: the structure of a dictionary node (`And` or
/// `PProd`).
pub fn search_node_struct(w: &Expr) -> Name {
  match const_app(w) {
    Some((h, _, _)) if h == n_and() => n_and(),
    _ => n_pprod(),
  }
}

/// `searchEntry`: step 2 of [`lean_search`]: search the instantiated entry
/// for the canary `can` applied to the recursive argument `major`,
/// depth-first, first component first. The bound ends the search without a
/// result; an exhausted reducer is a refusal (the second component is not
/// tried).
pub fn search_entry(
  const_of: ConstOf<'_>,
  can: &Name,
  major: &Expr,
  fuel: usize,
  cur: &Expr,
  acc: Vec<PStep>,
) -> R<Option<Vec<PStep>>> {
  let Some(fuel) = fuel.checked_sub(1) else { return Ok(None) };
  let w = whnf(const_of, WHNF_FUEL, cur)?;
  match decode_node(PackKind::Pprod, &w) {
    Some((_, _, d1, d2)) => {
      let s = search_node_struct(&w);
      let mut a1 = acc.clone();
      a1.push(PStep::Proj(s.clone(), 0));
      if let Some(r) = search_entry(const_of, can, major, fuel, &d1, a1)? {
        return Ok(Some(r));
      }
      let mut a2 = acc;
      a2.push(PStep::Proj(s, 1));
      search_entry(const_of, can, major, fuel, &d2, a2)
    },
    None => {
      if search_terminal(&w) {
        return Ok(None);
      }
      let (h, fargs) = get_app_fn_args(&w);
      match h.as_data() {
        ExprData::Fvar(f, _) => {
          let applied = fargs.last().is_some_and(|a| {
            alpha_eq_skip_mdata(&strip_all_mdata(a), &strip_all_mdata(major))
          });
          Ok(if f == can && applied { Some(acc) } else { None })
        },
        _ => Ok(None),
      }
    },
  }
}

/// `searchInstEntry`: the `∀`s of a reflexive entry `w`, instantiated at the
/// last arguments of the recursive argument (`major_args`): the
/// instantiated entry and the application steps; `None` when the recursive
/// argument has too few arguments.
pub fn search_inst_entry(
  const_of: ConstOf<'_>,
  major_args: &[Expr],
  w: &Expr,
) -> R<Option<(Expr, Vec<PStep>)>> {
  let mut k: usize = 0;
  let mut cur = w.clone();
  for _ in 0..major_args.len().saturating_add(1) {
    match strip_mdata(&whnf(const_of, WHNF_FUEL, &cur)?).as_data() {
      ExprData::ForallE(_, _, b, _, _) => {
        k += 1;
        cur = b.clone();
      },
      _ => break,
    }
  }
  if major_args.len() < k {
    return Ok(None);
  }
  let tail_args = extract(major_args, major_args.len() - k, major_args.len());
  let mut ent = w.clone();
  for x in &tail_args {
    match strip_mdata(&whnf(const_of, WHNF_FUEL, &ent)?).as_data() {
      ExprData::ForallE(_, _, b, _, _) => {
        ent = instantiate_rev(b, slice::from_ref(x));
      },
      _ => return Ok(None),
    }
  }
  Ok(Some((ent, tail_args.into_iter().map(PStep::App).collect())))
}

/// `searchDict`: step 1 of [`lean_search`]: the dictionary's nodes,
/// depth-first, first component first; at the first other node, step 2 on
/// the instantiated entry with the remaining bound.
pub fn search_dict(
  const_of: ConstOf<'_>,
  can: &Name,
  major: &Expr,
  major_args: &[Expr],
  fuel: usize,
  cur: &Expr,
  acc: Vec<PStep>,
) -> R<Option<Vec<PStep>>> {
  let Some(fuel) = fuel.checked_sub(1) else { return Ok(None) };
  let w = whnf(const_of, WHNF_FUEL, cur)?;
  match decode_node(PackKind::Pprod, &w) {
    Some((_, _, d1, d2)) => {
      let s = search_node_struct(&w);
      let mut a1 = acc.clone();
      a1.push(PStep::Proj(s.clone(), 0));
      if let Some(r) =
        search_dict(const_of, can, major, major_args, fuel, &d1, a1)?
      {
        return Ok(Some(r));
      }
      let mut a2 = acc;
      a2.push(PStep::Proj(s, 1));
      search_dict(const_of, can, major, major_args, fuel, &d2, a2)
    },
    None => {
      if search_terminal(&w) {
        return Ok(None);
      }
      match search_inst_entry(const_of, major_args, &w)? {
        Some((e2, apps)) => {
          let mut a = acc;
          a.extend(apps);
          search_entry(const_of, can, major, fuel, &e2, a)
        },
        None => Ok(None),
      }
    },
  }
}

/// `leanSearch`: Lean's search for the dictionary entry of a recursive call
/// (`searchPProd` and `toBelowAux`, `Structural/BRecOn.lean`): depth-first
/// over the `PProd`/`And` nodes, first component first; at the first other
/// node, instantiate its `∀`s (a reflexive field's entry) at the last
/// arguments of the recursive argument, search again, and accept the canary
/// of group `j` applied to the recursive argument. Returns the steps; `None`
/// when the search (bounded by [`SEARCH_DEPTH`]) finds no entry. An
/// exhausted reducer is a refusal.
pub fn lean_search(
  tm: &mut TState,
  l: &StructLayout<'_>,
  ty: &Expr,
  j: usize,
  major: &Expr,
) -> R<Option<Vec<PStep>>> {
  let Some((c, us, args)) = const_app(ty) else { return Ok(None) };
  let p = l.num_params;
  let k = l.num_motives;
  if args.len() < p.saturating_add(k) {
    return Ok(None);
  }
  let cans: Vec<Name> = (0..k).map(|_| tm.fresh_fvar()).collect();
  let mut args2 = extract(&args, 0, p);
  args2.extend(cans.iter().map(fvar));
  args2.extend(extract(&args, p.saturating_add(k), args.len()));
  let Some(can) = cans.get(j) else { return Ok(None) };
  let start = mk_app_n(cnst(&c, &us), &args2);
  let major_args = get_app_fn_args(&strip_mdata(major)).1;
  search_dict(
    l.const_of,
    can,
    major,
    &major_args,
    SEARCH_DEPTH,
    &start,
    Vec::new(),
  )
}

/// `encS`: `E` on a structural functional: rebuild every call by Lean's
/// search, restore the erased motives.
pub struct StructEnc<'c, 'a> {
  pub l: &'c StructLayout<'a>,
  /// the members' names, in Lean's order
  pub names: &'c [Name],
  /// per member: its group and its position in it
  pub member_group: &'c [(usize, usize)],
}

impl StructEnc<'_, '_> {
  /// `args.mapM (go ctx)`.
  fn map_enc(
    &self,
    tm: &mut TState,
    hs: &mut Holes,
    fuel: usize,
    ctx: &mut Vec<Expr>,
    args: &[Expr],
  ) -> R<Vec<Expr>> {
    args.iter().map(|x| self.enc_s(tm, hs, fuel, ctx, x)).collect()
  }

  /// A recovered call of member `m`: Lean's path into the dictionary.
  fn call(
    &self,
    tm: &mut TState,
    hs: &mut Holes,
    fuel: usize,
    ctx: &mut Vec<Expr>,
    m: usize,
    args: &[Expr],
  ) -> R<Expr> {
    let no_group = || "recovery: a member of no group".to_string();
    let Some(&(j, idx)) = self.member_group.get(m) else {
      return Err(no_group());
    };
    let Some(g) = self.l.groups.get(j) else { return Err(no_group()) };
    if args.len() < g.arity {
      return Err("recovery: a call with too few arguments".into());
    }
    let eargs = extract(args, 0, g.arity);
    let Some(major) = eargs.last() else {
      return Err("recovery: a call without its argument".into());
    };
    let Hole::SCall(i) = hs.pop_hole()? else {
      return Err("recovery: a structural call was expected".into());
    };
    let Some(ty) = bvar_type(ctx, i) else {
      return Err("recovery: the dictionary is out of scope".into());
    };
    let Some(mut steps) = lean_search(tm, self.l, &ty, j, major)? else {
      return Err("recovery: Lean's search does not find the call".into());
    };
    if g.size() >= 2 {
      let Some(st) = g.spine.proj_steps(idx) else {
        return Err("recovery: a call past its group's packed motive".into());
      };
      steps.extend(st.into_iter().map(|(s, k)| PStep::Proj(s, k)));
    }
    let mut acc = apply_steps(&steps, &bvar(i));
    for x in args.iter().skip(g.arity) {
      acc = Expr::app(acc, self.enc_s(tm, hs, fuel, ctx, x)?);
    }
    Ok(acc)
  }

  /// `encS`.
  pub fn enc_s(
    &self,
    tm: &mut TState,
    hs: &mut Holes,
    fuel: usize,
    ctx: &mut Vec<Expr>,
    e: &Expr,
  ) -> R<Expr> {
    let Some(fuel) = fuel.checked_sub(1) else {
      return Err(RECOVERY_EXHAUSTED.into());
    };
    Ok(match e.as_data() {
      ExprData::App(..) | ExprData::Const(..) | ExprData::Proj(..) => {
        let (h, args) = get_app_fn_args(e);
        if let ExprData::Const(c, _, _) = h.as_data() {
          if let Some(m) = self.names.iter().position(|n| n == c) {
            return self.call(tm, hs, fuel, ctx, m, &args);
          }
          if self.l.aux.contains_key(c) {
            let p = self.l.num_params;
            let k = self.l.num_motives;
            let mut args2 = Vec::with_capacity(args.len());
            for (i, x) in args.iter().enumerate() {
              // a placeholder where `recS` erased the motive; a user's
              // `below` application keeps its own
              if p <= i
                && i < p.saturating_add(k)
                && is_const_named(x, &ph_motive())
              {
                args2.push(hs.pop_expr()?);
              } else {
                args2.push(self.enc_s(tm, hs, fuel, ctx, x)?);
              }
            }
            return Ok(mk_app_n(h, &args2));
          }
        }
        match e.as_data() {
          ExprData::App(..) => {
            let h2 = self.enc_s(tm, hs, fuel, ctx, &h)?;
            mk_app_n(h2, &self.map_enc(tm, hs, fuel, ctx, &args)?)
          },
          ExprData::Proj(s, i, x, _) => {
            Expr::proj(s.clone(), i.clone(), self.enc_s(tm, hs, fuel, ctx, x)?)
          },
          _ => e.clone(),
        }
      },
      ExprData::Lam(nm, t, b, bi, _) => {
        let t2 = self.enc_s(tm, hs, fuel, ctx, t)?;
        let b2 = under(ctx, slice::from_ref(t), |ctx| {
          self.enc_s(tm, hs, fuel, ctx, b)
        })?;
        Expr::lam(nm.clone(), t2, b2, bi.clone())
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        let t2 = self.enc_s(tm, hs, fuel, ctx, t)?;
        let b2 = under(ctx, slice::from_ref(t), |ctx| {
          self.enc_s(tm, hs, fuel, ctx, b)
        })?;
        Expr::all(nm.clone(), t2, b2, bi.clone())
      },
      ExprData::LetE(nm, t, v, b, nd, _) => {
        let t2 = self.enc_s(tm, hs, fuel, ctx, t)?;
        let v2 = self.enc_s(tm, hs, fuel, ctx, v)?;
        let b2 = under(ctx, slice::from_ref(t), |ctx| {
          self.enc_s(tm, hs, fuel, ctx, b)
        })?;
        Expr::letE(nm.clone(), t2, v2, b2, *nd)
      },
      ExprData::Mdata(d, x, _) => {
        Expr::mdata(d.clone(), self.enc_s(tm, hs, fuel, ctx, x)?)
      },
      _ => e.clone(),
    })
  }
}

/// The members' universe parameters, as levels; the first member's
/// (`m0.levelParams.map Level.mkParam`).
fn member_levels(members: &[Decl]) -> R<Vec<Level>> {
  let Some(m0) = members.first() else {
    return Err("recovery: a clique without members".into());
  };
  Ok(m0.level_params.iter().map(|p| Level::param(p.clone())).collect())
}

/// `recoverStructural`: the recovered specifications of a structural clique
/// (one functional body per member, in Lean's order), each checked by
/// re-encoding. `family` is the block's authenticated `below`/`brecOn`
/// family ([`family_candidates`](super::structural::family_candidates)). A
/// member's functional `f._f` must be one of the functionals the members'
/// `brecOn` applications pass ([`StructLayout::f_names`]).
pub fn recover_structural(
  tm: &mut TState,
  members: &[Decl],
  aux: &[Decl],
  const_of: ConstOf<'_>,
  family: &FxHashSet<Name>,
) -> R<Vec<Expr>> {
  let n = members.len();
  let l = struct_layout(members, aux, &id_perm(n), const_of, family.clone())?;
  if l.num_fun_types > 0 {
    return Err(
      "recovery: the inductive-predicate route is not recovered".into(),
    );
  }
  // Every dictionary path `R` reads as a recursive call must be the
  // recursion's own ("Ownership" in `structural`): a path out of a user's
  // `below` value would be read as an invented call, and two members that
  // differ only there would get one specification (and be aliased). The
  // identity transport with ownership enforced is that check.
  transport_structural(
    tm,
    members,
    aux,
    &id_perm(n),
    const_of,
    family.clone(),
    &[],
    true,
  )?;
  let names: Vec<Name> = members.iter().map(|d| d.name.clone()).collect();
  let lvls = member_levels(members)?;
  // each member's group and position in it (the layout puts every member in
  // exactly one group)
  let Some(member_group) = (0..n)
    .map(|m| {
      l.groups.iter().enumerate().find_map(|(j, g)| {
        g.members.iter().position(|&x| x == m).map(|k| (j, k))
      })
    })
    .collect::<Option<Vec<(usize, usize)>>>()
  else {
    return Err("recovery: a member of no group".into());
  };
  let rec = StructRec { l: &l, names: &names, lvls: &lvls };
  let enc = StructEnc { l: &l, names: &names, member_group: &member_group };
  let mut out = Vec::with_capacity(n);
  for d in members {
    let f_name = mk_str(&d.name, "_f");
    if !l.f_names.contains(&f_name) {
      return Err(format!(
        "recovery: {} is not a functional of the members' brecOn \
         applications",
        name_to_string(&f_name)
      ));
    }
    let Some(f) = aux.iter().find(|x| x.name == f_name) else {
      return Err(format!(
        "recovery: no functional for {}",
        name_to_string(&f_name)
      ));
    };
    let mut hs = Holes::default();
    let spec =
      rec.rec_s(tm, &mut hs, TRANSPORT_FUEL, &mut Vec::new(), &f.value)?;
    let mut back_hs = Holes { holes: hs.holes, cursor: 0 };
    let back =
      enc.enc_s(tm, &mut back_hs, TRANSPORT_FUEL, &mut Vec::new(), &spec)?;
    if !(back_hs.cursor == back_hs.holes.len()
      && alpha_eq_skip_mdata(&back, &f.value))
    {
      return Err(format!(
        "recovery: re-encoding {} does not give Lean's term back",
        name_to_string(&f_name)
      ));
    }
    out.push(spec);
  }
  Ok(out)
}

// ---------------------------------------------------------------------------
// The well-founded route
// ---------------------------------------------------------------------------

/// `recW`: `R` on a leaf of the packed function's case tree, in the user
/// region, under binders of which the context marks the recursion
/// variables.
pub struct WfRec<'c> {
  pub l: &'c WfLayout,
  /// the members' names, in Lean's order
  pub names: &'c [Name],
  /// the members' universe parameters, as levels
  pub lvls: &'c [Level],
}

impl WfRec<'_> {
  /// `args.mapM (go ctx)`.
  fn map_rec(
    &self,
    hs: &mut Holes,
    fuel: usize,
    ctx: &mut Vec<bool>,
    args: &[Expr],
  ) -> R<Vec<Expr>> {
    args.iter().map(|x| self.rec_w(hs, fuel, ctx, x)).collect()
  }

  /// `go` under the binders marked `marks`.
  fn rec_under(
    &self,
    hs: &mut Holes,
    fuel: usize,
    ctx: &mut Vec<bool>,
    marks: &[bool],
    e: &Expr,
  ) -> R<Expr> {
    under(ctx, marks, |ctx| self.rec_w(hs, fuel, ctx, e))
  }

  /// A `PSigma.casesOn` that passes the exact recursion argument `last` to
  /// its minor's third binder. Value flow, not a matching type, establishes
  /// the copied binder's role.
  fn threaded_psigma(
    &self,
    hs: &mut Holes,
    fuel: usize,
    ctx: &mut Vec<bool>,
    head: &Expr,
    args: &[Expr],
  ) -> R<Option<Expr>> {
    let [alpha0, beta0, motive0, major0, minor0, last] = args else {
      return Ok(None);
    };
    let Some(identity) = bvar_idx(&strip_mdata(last)) else { return Ok(None) };
    if !bvar_marked(ctx, identity) {
      return Ok(None);
    }
    let no_motive =
      || "recovery: threaded PSigma motive has no recursion binder".to_string();
    let motive0 = strip_mdata(motive0);
    let ExprData::Lam(mn, mt, mb, mbi, _) = motive0.as_data() else {
      return Err(no_motive());
    };
    let ExprData::ForallE(rn, rt, result, rbi, _) = mb.as_data() else {
      return Err(no_motive());
    };
    let no_minor =
      || "recovery: threaded PSigma minor has no recursion binder".to_string();
    let minor0 = strip_mdata(minor0);
    let ExprData::Lam(an, aty, ab, abi, _) = minor0.as_data() else {
      return Err(no_minor());
    };
    let ExprData::Lam(bn, bty, bb, bbi, _) = ab.as_data() else {
      return Err(no_minor());
    };
    let ExprData::Lam(cn, cty, body, cbi, _) = bb.as_data() else {
      return Err(no_minor());
    };
    let ph = cnst(&ph_rec_var(), &[]);
    let alpha = self.rec_w(hs, fuel, ctx, alpha0)?;
    let beta = self.rec_w(hs, fuel, ctx, beta0)?;
    let mt = self.rec_w(hs, fuel, ctx, mt)?;
    hs.push_hole(Hole::Expr(rt.clone()));
    let result = self.rec_under(hs, fuel, ctx, &[false, false], result)?;
    let motive = Expr::lam(
      mn.clone(),
      mt,
      Expr::all(rn.clone(), ph.clone(), result, rbi.clone()),
      mbi.clone(),
    );
    let major = self.rec_w(hs, fuel, ctx, major0)?;
    let aty = self.rec_w(hs, fuel, ctx, aty)?;
    let bty = self.rec_under(hs, fuel, ctx, &[false], bty)?;
    hs.push_hole(Hole::Expr(cty.clone()));
    let body = self.rec_under(hs, fuel, ctx, &[false, false, true], body)?;
    let minor = Expr::lam(
      an.clone(),
      aty,
      Expr::lam(
        bn.clone(),
        bty,
        Expr::lam(cn.clone(), ph.clone(), body, cbi.clone()),
        bbi.clone(),
      ),
      abi.clone(),
    );
    hs.push_hole(Hole::Expr(last.clone()));
    Ok(Some(mk_app_n(head.clone(), &[alpha, beta, motive, major, minor, ph])))
  }

  /// `recW`.
  pub fn rec_w(
    &self,
    hs: &mut Holes,
    fuel: usize,
    ctx: &mut Vec<bool>,
    e: &Expr,
  ) -> R<Expr> {
    let Some(fuel) = fuel.checked_sub(1) else {
      return Err(RECOVERY_EXHAUSTED.into());
    };
    Ok(match e.as_data() {
      ExprData::App(..) => {
        let (h, args) = get_app_fn_args(e);
        if let ExprData::Const(name, _, _) = h.as_data()
          && *name == dotted("PSigma.casesOn")
          && let Some(r) = self.threaded_psigma(hs, fuel, ctx, &h, &args)?
        {
          return Ok(r);
        }
        match bvar_idx(&h) {
          Some(i) if bvar_marked(ctx, i) => {
            let Some(y) = args.first() else {
              return Err("recovery: a bare recursion variable".into());
            };
            let Some(pf) = args.get(1) else {
              return Err(
                "recovery: a recursive call without its proof".into(),
              );
            };
            let Some((s, j, v)) = decode_inj(self.l.n, y) else {
              return Err(
                "recovery: a recursive call whose argument is not an \
                 injection"
                  .into(),
              );
            };
            if !self.l.is_clique(&s) {
              return Err(
                "recovery: a recursive call into another packing".into(),
              );
            }
            hs.push_hole(Hole::WCall(i, s, pf.clone()));
            let Some(name) = self.names.get(j) else {
              return Err("recovery: no such member".into());
            };
            let mut acc =
              Expr::app(cnst(name, self.lvls), self.rec_w(hs, fuel, ctx, &v)?);
            for x in args.iter().skip(2) {
              acc = Expr::app(acc, self.rec_w(hs, fuel, ctx, x)?);
            }
            acc
          },
          Some(_) => mk_app_n(h, &self.map_rec(hs, fuel, ctx, &args)?),
          None => {
            let h2 = self.rec_w(hs, fuel, ctx, &h)?;
            mk_app_n(h2, &self.map_rec(hs, fuel, ctx, &args)?)
          },
        }
      },
      ExprData::Lam(nm, t, b, bi, _) => {
        let t2 = self.rec_w(hs, fuel, ctx, t)?;
        let b2 = self.rec_under(hs, fuel, ctx, &[false], b)?;
        Expr::lam(nm.clone(), t2, b2, bi.clone())
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        let t2 = self.rec_w(hs, fuel, ctx, t)?;
        let b2 = self.rec_under(hs, fuel, ctx, &[false], b)?;
        Expr::all(nm.clone(), t2, b2, bi.clone())
      },
      ExprData::LetE(nm, t, v, b, nd, _) => {
        let t2 = self.rec_w(hs, fuel, ctx, t)?;
        let v2 = self.rec_w(hs, fuel, ctx, v)?;
        let b2 = self.rec_under(hs, fuel, ctx, &[false], b)?;
        Expr::letE(nm.clone(), t2, v2, b2, *nd)
      },
      ExprData::Bvar(..) => {
        if bvar_idx(e).is_some_and(|i| bvar_marked(ctx, i)) {
          return Err(
            "recovery: exact recursive binder escapes the decoded call region"
              .into(),
          );
        }
        e.clone()
      },
      ExprData::Proj(s, i, x, _) => {
        Expr::proj(s.clone(), i.clone(), self.rec_w(hs, fuel, ctx, x)?)
      },
      ExprData::Mdata(d, x, _) => {
        Expr::mdata(d.clone(), self.rec_w(hs, fuel, ctx, x)?)
      },
      _ => e.clone(),
    })
  }
}

/// `encW`: `E` on a recovered leaf: every call rebuilt by `ArgsPacker`'s
/// injection, the erased annotations restored.
pub fn enc_w(names: &[Name], hs: &mut Holes, fuel: usize, e: &Expr) -> R<Expr> {
  let Some(fuel) = fuel.checked_sub(1) else {
    return Err(RECOVERY_EXHAUSTED.into());
  };
  if let ExprData::Const(c, _, _) = strip_mdata(e).as_data()
    && (*c == ph_rel() || *c == ph_rec_var())
  {
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
        // `R` recorded the call before transforming its argument
        let Hole::WCall(i, s, pf) = hs.pop_hole()? else {
          return Err("recovery: a well-founded call was expected".into());
        };
        let v2 = enc_w(names, hs, fuel, v)?;
        let Some(inj) = mk_inj(&s, j, &v2) else {
          return Err("recovery: a call past its packing".into());
        };
        let mut acc = mk_app_n(bvar(i), &[inj, pf]);
        for x in args.iter().skip(1) {
          acc = Expr::app(acc, enc_w(names, hs, fuel, x)?);
        }
        return Ok(acc);
      }
      let h2 = enc_w(names, hs, fuel, &h)?;
      let args2 = args
        .iter()
        .map(|x| enc_w(names, hs, fuel, x))
        .collect::<R<Vec<Expr>>>()?;
      mk_app_n(h2, &args2)
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
    ExprData::LetE(nm, t, v, b, nd, _) => {
      let t2 = enc_w(names, hs, fuel, t)?;
      let v2 = enc_w(names, hs, fuel, v)?;
      Expr::letE(nm.clone(), t2, v2, enc_w(names, hs, fuel, b)?, *nd)
    },
    ExprData::Proj(s, i, x, _) => {
      Expr::proj(s.clone(), i.clone(), enc_w(names, hs, fuel, x)?)
    },
    ExprData::Mdata(d, x, _) => {
      Expr::mdata(d.clone(), enc_w(names, hs, fuel, x)?)
    },
    _ => e.clone(),
  })
}

/// `recoverWF`: the recovered specifications of a well-founded clique (one
/// leaf per member, in Lean's order), each checked by re-encoding.
pub fn recover_wf(
  tm: &mut TState,
  members: &[Decl],
  mut_decl: &Decl,
  const_of: ConstOf<'_>,
) -> R<Vec<Expr>> {
  let n = members.len();
  let l = wf_layout(members, mut_decl, &id_perm(n), &mut_decl.name)?;
  let names: Vec<Name> = members.iter().map(|d| d.name.clone()).collect();
  let lvls = member_levels(members)?;
  let (_, fix_app) = peel_lams(l.num_fixed, &mut_decl.value);
  // Validate the actual root, relationship, tree and entry identities before
  // assigning a recursion role to any leaf binder. This identity permutation
  // is a decoder check; recovery still reads the original source syntax.
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
  let rec = WfRec { l: &l, names: &names, lvls: &lvls };
  let mut out = Vec::with_capacity(t.leaves.len());
  for leaf in &t.leaves {
    let missing = || "recovery: missing decoded leaf entry binders".to_string();
    let entry = strip_mdata(leaf);
    let ExprData::Lam(pn, pt, pb, pbi, _) = entry.as_data() else {
      return Err(missing());
    };
    let ExprData::Lam(rn, rt, body, rbi, _) = pb.as_data() else {
      return Err(missing());
    };
    let mut hs = Holes::default();
    hs.push_hole(Hole::Expr(rt.clone()));
    let body =
      rec.rec_w(&mut hs, TRANSPORT_FUEL, &mut vec![false, true], body)?;
    let spec = Expr::lam(
      pn.clone(),
      pt.clone(),
      Expr::lam(rn.clone(), cnst(&ph_rec_var(), &[]), body, rbi.clone()),
      pbi.clone(),
    );
    let mut back_hs = Holes { holes: hs.holes, cursor: 0 };
    let back = enc_w(&names, &mut back_hs, TRANSPORT_FUEL, &spec)?;
    if !(back_hs.cursor == back_hs.holes.len()
      && alpha_eq_skip_mdata(&back, leaf))
    {
      return Err(
        "recovery: re-encoding a leaf does not give Lean's term back".into(),
      );
    }
    out.push(spec);
  }
  Ok(out)
}

// ---------------------------------------------------------------------------
// The `partial_fixpoint` route
// ---------------------------------------------------------------------------
//
// The packed fixpoint is `λ fixed. fix … (λ x. ⟨F₀, …, F_{n-1}⟩) h` (or a
// lattice fixpoint of the same shape); a recursive call in `F_i` is a full
// projection path `x.2.1` into the packed variable (`PProdN.proj`). `R`
// turns a path to component `j` into the member `f_j`; any other occurrence
// of the packed variable fails. `E` rebuilds each call as Lean's path
// (`Spine::proj_steps`) and the recovery is accepted only if it gives Lean's
// component back.

/// `recP`: `R` on a functional component; `d` is the packed variable's de
/// Bruijn index at the current depth.
pub fn rec_p(
  s: &Spine,
  names: &[Name],
  lvls: &[Level],
  fuel: usize,
  d: usize,
  e: &Expr,
) -> R<Expr> {
  let Some(fuel) = fuel.checked_sub(1) else {
    return Err(RECOVERY_EXHAUSTED.into());
  };
  let go = |d: usize, x: &Expr| rec_p(s, names, lvls, fuel, d, x);
  Ok(match e.as_data() {
    ExprData::Proj(sn, i, x, _) => {
      let (steps, base) = proj_chain(e);
      match bvar_idx(&strip_mdata(&base)) {
        Some(b) => {
          if b != d {
            return Ok(e.clone());
          }
          let Some((j, len)) = path_prefix(s.size(), &steps) else {
            return Err(
              "recovery: a projection of the packed variable that is not a \
               path"
                .into(),
            );
          };
          if !steps_fit(s, j, &extract(&steps, 0, len)) {
            return Err(
              "recovery: a path whose projections are not the packing's".into(),
            );
          }
          let Some(m) = names.get(j) else {
            return Err("recovery: no such member".into());
          };
          apply_projs(&extract(&steps, len, steps.len()), &cnst(m, lvls))
        },
        None => Expr::proj(sn.clone(), i.clone(), go(d, x)?),
      }
    },
    ExprData::Bvar(..) => {
      if bvar_idx(e) == Some(d) {
        return Err(
          "recovery: the packed variable outside a projection path".into(),
        );
      }
      e.clone()
    },
    ExprData::App(f, a, _) => Expr::app(go(d, f)?, go(d, a)?),
    ExprData::Lam(nm, t, b, bi, _) => {
      Expr::lam(nm.clone(), go(d, t)?, go(d + 1, b)?, bi.clone())
    },
    ExprData::ForallE(nm, t, b, bi, _) => {
      Expr::all(nm.clone(), go(d, t)?, go(d + 1, b)?, bi.clone())
    },
    ExprData::LetE(nm, t, v, b, nd, _) => {
      Expr::letE(nm.clone(), go(d, t)?, go(d, v)?, go(d + 1, b)?, *nd)
    },
    ExprData::Mdata(md, x, _) => Expr::mdata(md.clone(), go(d, x)?),
    _ => e.clone(),
  })
}

/// `encP`: `E` on a recovered component: every member constant becomes
/// Lean's path (a member past the packing is a refusal).
pub fn enc_p(s: &Spine, names: &[Name], d: usize, e: &Expr) -> R<Expr> {
  let go = |d: usize, x: &Expr| enc_p(s, names, d, x);
  Ok(match e.as_data() {
    ExprData::Const(c, _, _) => match names.iter().position(|n| n == c) {
      Some(j) => match s.proj_steps(j) {
        Some(st) => apply_projs(&st, &bvar(d)),
        None => {
          return Err("recovery: a member past the fixpoint's packing".into());
        },
      },
      None => e.clone(),
    },
    ExprData::Proj(sn, i, x, _) => Expr::proj(sn.clone(), i.clone(), go(d, x)?),
    ExprData::App(f, a, _) => Expr::app(go(d, f)?, go(d, a)?),
    ExprData::Lam(nm, t, b, bi, _) => {
      Expr::lam(nm.clone(), go(d, t)?, go(d + 1, b)?, bi.clone())
    },
    ExprData::ForallE(nm, t, b, bi, _) => {
      Expr::all(nm.clone(), go(d, t)?, go(d + 1, b)?, bi.clone())
    },
    ExprData::LetE(nm, t, v, b, nd, _) => {
      Expr::letE(nm.clone(), go(d, t)?, go(d, v)?, go(d + 1, b)?, *nd)
    },
    ExprData::Mdata(md, x, _) => Expr::mdata(md.clone(), go(d, x)?),
    _ => e.clone(),
  })
}

/// `recoverPF`: the recovered functional components of a `partial_fixpoint`
/// clique (in the context of the fixed parameters and the packed variable,
/// `bvar 0`), each checked by re-encoding, and the layout.
pub fn recover_pf(members: &[Decl], packed: &Decl) -> R<(Vec<Expr>, PfLayout)> {
  let n = members.len();
  let l = pf_layout(members, packed, &id_perm(n), &packed.name)?;
  let names: Vec<Name> = members.iter().map(|d| d.name.clone()).collect();
  let lvls = member_levels(members)?;
  let (_, body) = peel_lams(l.num_fixed, &packed.value);
  let Some((head, _, args)) = const_app(&strip_mdata(&body)) else {
    return Err(
      "recovery: the packed value is not a fixpoint application".into(),
    );
  };
  let unsupported =
    || "recovery: unsupported partial-fixpoint root".to_string();
  if !(head == n_order_fix() || head == dotted("Lean.Order.lfp_monotone")) {
    return Err(unsupported());
  }
  let [root_domain, _, root_functional, _] = args.as_slice() else {
    return Err(unsupported());
  };
  let root_functional = strip_mdata(root_functional);
  let ExprData::Lam(_, domain, functional, _, _) = root_functional.as_data()
  else {
    return Err(
      "recovery: the fixpoint functional has no recursive binder".into(),
    );
  };
  let Some(input) = decode_spine(PackKind::Pprod, n, domain) else {
    return Err(
      "recovery: the recursive binder is not a packed product".into(),
    );
  };
  let Some((output, cs)) = decode_tuple(n, &strip_mdata(functional)) else {
    return Err("recovery: the functional has no encoded output tuple".into());
  };
  let output_fits = output.typ().is_some_and(|output_type| {
    alpha_eq_skip_mdata(
      &norm_order_alias(&output_type),
      &norm_order_alias(&lift_loose(domain, 1, 0)),
    )
  });
  if !(l.is_clique(&input)
    && alpha_eq_skip_mdata(
      &norm_order_alias(domain),
      &norm_order_alias(root_domain),
    )
    && output_fits)
  {
    return Err(
      "recovery: the decoded functional disagrees with the fixpoint packing"
        .into(),
    );
  }
  let mut out = Vec::with_capacity(cs.len());
  for c in &cs {
    let spec = rec_p(&l.spine, &names, &lvls, TRANSPORT_FUEL, 0, c)?;
    if !alpha_eq_skip_mdata(&enc_p(&l.spine, &names, 0, &spec)?, c) {
      return Err(
        "recovery: re-encoding a functional component does not give Lean's \
         term back"
          .into(),
      );
    }
    out.push(spec);
  }
  Ok((out, l))
}

// ---------------------------------------------------------------------------
// Specifications in each member's own parameters
// ---------------------------------------------------------------------------
//
// The recovery reads each member's body back out of the encoding, but in
// the encoding's context: the fixed parameters follow Lean's *first*
// function's order, so the recovered bodies of two presentations differ by a
// permutation of those binders. A member's specification is stated in the
// member's own parameters instead: the recovered body is instantiated at the
// member's own arguments of the fixed positions (read off its call of the
// encoding, `member_fixed`) and abstracted over the member's own parameters.
// The result is a function of the member's specification alone, so two
// presentations give the same specifications, whatever Lean's first function
// was. The encoding's own variables that `R` left (none, when the encoding
// is Lean's) become the recursion-variable placeholder.

/// `phEnc`: the placeholder for an encoding variable in a specification.
pub fn ph_enc() -> Expr {
  cnst(&ph_rec_var(), &[])
}

/// `fixedArgsOf`: the member's own arguments of the fixed positions, under
/// its own parameters (`num_params` binders; Lean's truncated subtraction).
pub fn fixed_args_of(num_params: usize, q: &[usize]) -> Vec<Expr> {
  q.iter()
    .map(|&p| bvar(num_params.saturating_sub(1).saturating_sub(p)))
    .collect()
}

/// One member's recovered body and fixed positions.
pub type MemberFixed<'d> = (&'d Decl, &'d Expr, &'d [usize]);

/// `withMemberFixed`: per member (Lean's order), its recovered body and its
/// fixed positions (`member_fixed`); a member without either is a refusal
/// (neither happens: the recovery gives one body per member, the layout one
/// entry per member).
pub fn with_member_fixed<'d>(
  members: &'d [Decl],
  bodies: &'d [Expr],
  member_fixed: &'d [Vec<usize>],
) -> R<Vec<MemberFixed<'d>>> {
  members
    .iter()
    .enumerate()
    .map(|(i, d)| {
      let Some(body) = bodies.get(i) else {
        return Err(format!(
          "recovery: no recovered body for {}",
          name_to_string(&d.name)
        ));
      };
      let Some(q) = member_fixed.get(i) else {
        return Err(format!(
          "recovery: no fixed positions for {}",
          name_to_string(&d.name)
        ));
      };
      Ok((d, body, q.as_slice()))
    })
    .collect()
}

/// A member's parameters (`paramsOf`).
fn params_of(d: &Decl) -> Vec<Binder> {
  peel_lams(lam_arity(&d.value), &d.value).0
}

/// `λ ps. instantiateRev body (lead ++ (fixedArgsOf ps.size q).reverse)`.
fn instantiated(items: Vec<MemberFixed<'_>>, lead: usize) -> Vec<Expr> {
  items
    .into_iter()
    .map(|(d, body, q)| {
      let ps = params_of(d);
      let mut subst: Vec<Expr> = (0..lead).map(|_| ph_enc()).collect();
      subst.extend(fixed_args_of(ps.len(), q).into_iter().rev());
      mk_lams(&ps, instantiate_rev(body, &subst))
    })
    .collect()
}

/// `normalisedSpecs`: the normalised specifications of a clique
/// (`inp.members` in Lean's order; `inp.sigma` is ignored): one closed term
/// per member, a function of the member's specification alone. An error
/// means the recovery failed.
pub fn normalised_specs(inp: &Input<'_>) -> R<Vec<Expr>> {
  let n = inp.members.len();
  match inp.encoding {
    Encoding::WellFounded => {
      let Some(packed) = find_packed(&inp.members, &inp.aux) else {
        return Err("recovery: no packed function".into());
      };
      let l = wf_layout(&inp.members, &packed, &id_perm(n), &packed.name)?;
      let leaves = recover_wf(
        &mut TState::default(),
        &inp.members,
        &packed,
        inp.const_of,
      )?;
      // a leaf lives under the fixed parameters, then `F`'s `x` and `a`
      let items = with_member_fixed(&inp.members, &leaves, &l.member_fixed)?;
      Ok(instantiated(items, 2))
    },
    Encoding::Structural => {
      let l = struct_layout(
        &inp.members,
        &inp.aux,
        &id_perm(n),
        inp.const_of,
        inp.family.clone(),
      )?;
      let fs = recover_structural(
        &mut TState::default(),
        &inp.members,
        &inp.aux,
        inp.const_of,
        &inp.family,
      )?;
      // a functional `f._f` is closed: applied to the member's fixed
      // arguments
      let items = with_member_fixed(&inp.members, &fs, &l.member_fixed)?;
      Ok(
        items
          .into_iter()
          .map(|(d, f, q)| {
            let ps = params_of(d);
            mk_lams(&ps, mk_app_n(f.clone(), &fixed_args_of(ps.len(), q)))
          })
          .collect(),
      )
    },
    Encoding::PartialFixpoint => {
      let Some(packed) = find_packed(&inp.members, &inp.aux) else {
        return Err("recovery: no packed fixpoint".into());
      };
      let (cs, l) = recover_pf(&inp.members, &packed)?;
      // a component lives under the fixed parameters, then the packed
      // variable
      let items = with_member_fixed(&inp.members, &cs, &l.member_fixed)?;
      Ok(instantiated(items, 1))
    },
  }
}

/// A clique's canonical order: `σ` (Lean index ↦ canonical position), the
/// classes, and where the order came from.
pub type CliqueOrder = (Vec<usize>, Vec<Vec<Name>>, OrderSource);

/// `cliqueOrder`: the canonical order of a clique: Pass 1's classes over
/// each member's type and normalised specification, statements compared
/// first, under the compiler's rules ([`Rules::default`], Lean's
/// `Rules.compiler`: the name-hash seed); members still in one class follow
/// Pass 1's seed order. When the specification cannot be recovered, the
/// statements alone ([`statement_order`], same rules); when they tie too, an
/// error (`NOSPEC`: the clique keeps its baseline). `σ[i]` is the canonical
/// position of Lean's member `i`; the classes are returned for the plan (a
/// class of two or more members is ordered by the seed order). `addr` gives
/// the external constants' addresses; the placeholders have their own
/// ([`placeholder_addr`]).
pub fn clique_order(addr: AddrOf<'_>, inp: &Input<'_>) -> R<CliqueOrder> {
  let rules = Rules::default();
  let addr2 = |n: &Name| placeholder_addr(n).or_else(|| addr(n));
  let member = |d: &Decl, value: Expr| CliqueMember {
    name: d.name.clone(),
    level_params: d.level_params.clone(),
    typ: d.typ.clone(),
    value,
    rec_arg_pos: None,
  };
  match normalised_specs(inp) {
    Ok(specs) => {
      let members: Vec<CliqueMember> =
        inp.members.iter().zip(specs).map(|(d, v)| member(d, v)).collect();
      let names: Vec<Name> = members.iter().map(|m| m.name.clone()).collect();
      let (cls, _) = clique_classes(
        rules,
        &addr2,
        &Clique { kind: CliqueKind::NoSpec, members },
      )?;
      let order: Vec<&Name> = cls.iter().flatten().collect();
      let unordered = || "order: the classes do not order every member";
      let Some(sigma) = names
        .iter()
        .map(|m| order.iter().position(|x| *x == m))
        .collect::<Option<Vec<usize>>>()
      else {
        return Err(unordered().into());
      };
      if !is_perm(&sigma) {
        return Err(unordered().into());
      }
      Ok((sigma, cls, OrderSource::Specification))
    },
    Err(why) => {
      let members: Vec<CliqueMember> =
        inp.members.iter().map(|d| member(d, d.value.clone())).collect();
      match statement_order(rules, &addr2, &members)? {
        Some(sigma) => {
          let Some(cls) = inv_perm(&sigma).and_then(|inv| {
            inv
              .iter()
              .map(|&i| members.get(i).map(|m| vec![m.name.clone()]))
              .collect::<Option<Vec<Vec<Name>>>>()
          }) else {
            return Err(
              "order: the statements' order is not a permutation of the \
               members"
                .into(),
            );
          };
          Ok((sigma, cls, OrderSource::Statements(why)))
        },
        None => Err(format!("NOSPEC: {why}; the statements tie")),
      }
    },
  }
}

#[cfg(test)]
mod tests {
  use ix_common::address::Address;
  use ix_common::env::{
    ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, Expr, Name,
    ReducibilityHints,
  };

  use super::{
    CliqueOrder, Hole, Holes, RECOVERY_EXHAUSTED, clique_order, enc_p,
    normalised_specs, ph_motive, ph_rec_var, ph_rel, placeholder_addr, rec_p,
    search_dict, with_member_fixed,
  };
  use crate::compile::pass3::clique::basic::{
    Decl, alpha_eq_skip_mdata, bvar, cnst, dotted, fvar, inv_perm, is_perm,
    lvl_one, mk_app_n, n_pprod, name_to_string, proj, sort0,
  };
  use crate::compile::pass3::clique::bounds::SEARCH_DEPTH;
  use crate::compile::pass3::clique::pf::n_order_fix;
  use crate::compile::pass3::clique::plan::{Encoding, OrderSource};
  use crate::compile::pass3::clique::structural::PStep;
  use crate::compile::pass3::clique::telescope::WHNF_EXHAUSTED;
  use crate::compile::pass3::clique::transport::tests::{
    Fixture, c, def, lam, lookup, one, pf_clique, pf_env, pf_proj_clique,
    pf_spine, pi, struct_clique, struct_env, struct_family, wf_clique,
  };
  use crate::compile::pass3::clique::transport::{Input, transport};

  /// `addr? n = some n.getHash`.
  fn by_hash() -> impl Fn(&Name) -> Option<Address> {
    |n: &Name| Some(Address::from_blake3_hash(*n.get_hash()))
  }

  /// The members in canonical order.
  fn canonical(order: &CliqueOrder, members: &[Decl]) -> Vec<Name> {
    let inv = inv_perm(&order.0).expect("a permutation");
    inv.iter().map(|&i| members[i].name.clone()).collect()
  }

  /// The clique as an input (the permutation is not read).
  fn input(encoding: Encoding, k: &Fixture) -> Input<'static> {
    Input::new(
      encoding,
      k.members.clone(),
      k.aux.clone(),
      vec![0, 1],
      dotted("unused"),
    )
  }

  #[test]
  fn placeholders_have_fixed_addresses() {
    let addr = |k: u8| {
      let mut b = [0u8; 32];
      b[31] = k;
      Address::from_slice(&b).ok()
    };
    assert_eq!(placeholder_addr(&ph_motive()), addr(1));
    assert_eq!(placeholder_addr(&ph_rel()), addr(2));
    assert_eq!(placeholder_addr(&ph_rec_var()), addr(3));
    assert_eq!(placeholder_addr(&dotted("_ix_spec_motive.x")), None);
    assert_eq!(name_to_string(&ph_rec_var()), "_ix_spec_recvar");
  }

  #[test]
  fn structural_order_by_the_specification() {
    let env = struct_env();
    let env = lookup(&env);
    let run = |k: &Fixture| {
      let inp = Input {
        const_of: &env,
        family: struct_family(),
        ..input(Encoding::Structural, k)
      };
      (normalised_specs(&inp), clique_order(&by_hash(), &inp))
    };
    let k = struct_clique(false, "f._f");
    let (specs, order) = run(&k);
    // each member's functional under its own parameter, the packed motive of
    // the dictionary's type erased
    let below = mk_app_n(c("T.below"), &[cnst(&ph_motive(), &[]), bvar(0)]);
    let spec = |v: &str| {
      lam("x", c("T"), lam("x", c("T"), lam("f", below.clone(), c(v))))
    };
    assert_eq!(specs, Ok(vec![spec("a"), spec("b")]));
    let order = order.expect("ordered");
    assert_eq!(order.2, OrderSource::Specification);
    assert!(is_perm(&order.0) && order.1.iter().all(|c| c.len() == 1));
    // the other presentation (Lean's order `g, f`, packing `PProd B A`)
    // gives the same canonical order
    let mut k2 = struct_clique(true, "f._f");
    k2.members.reverse();
    let order2 = run(&k2).1.expect("ordered");
    assert_eq!(order2.2, OrderSource::Specification);
    assert_eq!(canonical(&order, &k.members), canonical(&order2, &k2.members));
    assert_eq!(order.1, order2.1);
  }

  #[test]
  fn structural_refusals() {
    let env = struct_env();
    let env = lookup(&env);
    // the empty family authenticates nothing: the statements decide
    let k = struct_clique(false, "f._f");
    let inp = Input { const_of: &env, ..input(Encoding::Structural, &k) };
    let why = "T.below: not in the block's authenticated below/brecOn family";
    assert_eq!(normalised_specs(&inp).err().as_deref(), Some(why));
    let order = clique_order(&by_hash(), &inp).expect("ordered");
    assert_eq!(order.2, OrderSource::Statements(why.into()));
    assert!(is_perm(&order.0) && order.1.iter().all(|c| c.len() == 1));
    // a decoy `f._f` beside the functional the members' `brecOn` passes
    let decoy = struct_clique(false, "f._g");
    let inp = Input {
      const_of: &env,
      family: struct_family(),
      ..input(Encoding::Structural, &decoy)
    };
    assert_eq!(
      normalised_specs(&inp).err().as_deref(),
      Some(
        "recovery: f._f is not a functional of the members' brecOn \
         applications"
      )
    );
  }

  #[test]
  fn well_founded_order_by_the_specification() {
    let k = wf_clique();
    let inp = input(Encoding::WellFounded, &k);
    // each leaf, its recursive call made explicit, under the member's own
    // parameter
    let ph = cnst(&ph_rec_var(), &[]);
    let spec = |domain: &str, callee: &str, arg: &str| {
      let call = Expr::app(c(callee), c(arg));
      lam("n", c(domain), lam("p", c(domain), lam("r", ph.clone(), call)))
    };
    let specs = normalised_specs(&inp).expect("recovered");
    assert_eq!(specs.len(), 2);
    assert!(alpha_eq_skip_mdata(&specs[0], &spec("Nat", "g", "i0")));
    assert!(alpha_eq_skip_mdata(&specs[1], &spec("Int", "f", "n0")));
    let order = clique_order(&by_hash(), &inp).expect("ordered");
    assert_eq!(order.2, OrderSource::Specification);
    assert!(is_perm(&order.0) && order.1.iter().all(|c| c.len() == 1));
    // the transported clique, in its canonical order `g, f`, gives the same
    // order
    let out = transport(&Input {
      sigma: vec![1, 0],
      new_enc_name: dotted("g._mutual"),
      ..input(Encoding::WellFounded, &k)
    });
    assert!(!out.baseline);
    let members2 = vec![out.decls[3].clone(), out.decls[2].clone()];
    let aux2 = vec![out.decls[0].clone(), out.decls[1].clone()];
    let k2 = Fixture { members: members2, aux: aux2 };
    let order2 = clique_order(&by_hash(), &input(Encoding::WellFounded, &k2))
      .expect("ordered");
    assert_eq!(order2.2, OrderSource::Specification);
    assert_eq!(canonical(&order, &k.members), canonical(&order2, &k2.members));
  }

  #[test]
  fn partial_fixpoint_order() {
    // calls in projection form: recovered
    let k = pf_proj_clique();
    let inp = input(Encoding::PartialFixpoint, &k);
    let spec = |x: &str, domain: &str, callee: &str, arg: &str| {
      let call = Expr::app(c(callee), c(arg));
      lam(x, c(domain), lam(x, c(domain), call))
    };
    assert_eq!(
      normalised_specs(&inp),
      Ok(vec![spec("n", "Nat", "g", "i0"), spec("i", "Int", "f", "n0")])
    );
    let order = clique_order(&by_hash(), &inp).expect("ordered");
    assert_eq!(order.2, OrderSource::Specification);
    // a call in application form is not a projection path: the statements
    // decide
    let k = pf_clique();
    let inp =
      Input { const_of: &pf_env, ..input(Encoding::PartialFixpoint, &k) };
    let why = "recovery: the packed variable outside a projection path";
    assert_eq!(normalised_specs(&inp).err().as_deref(), Some(why));
    let order = clique_order(&by_hash(), &inp).expect("ordered");
    assert_eq!(order.2, OrderSource::Statements(why.into()));
    assert!(is_perm(&order.0) && order.1.iter().all(|c| c.len() == 1));
    // roots the recovery does not read
    let with_root = |value: Expr| {
      let mut k = pf_proj_clique();
      k.aux[0].value = value;
      normalised_specs(&input(Encoding::PartialFixpoint, &k)).err()
    };
    assert_eq!(
      with_root(sort0()).as_deref(),
      Some("recovery: the packed value is not a fixpoint application")
    );
    let Some(gamma) = pf_spine().typ() else { panic!("a packing type") };
    let three = mk_app_n(
      cnst(&n_order_fix(), &[one()]),
      &[gamma.clone(), c("inst"), lam("x", gamma, c("t"))],
    );
    assert_eq!(
      with_root(three).as_deref(),
      Some("recovery: unsupported partial-fixpoint root")
    );
  }

  #[test]
  fn nospec_when_the_statements_tie() {
    let f = def("f", pi("n", c("Nat"), c("Nat")), lam("n", c("Nat"), c("z")));
    let g = Decl { name: dotted("g"), ..f.clone() };
    let inp = Input::new(
      Encoding::WellFounded,
      vec![f, g],
      vec![],
      vec![0, 1],
      dotted("unused"),
    );
    assert_eq!(
      clique_order(&by_hash(), &inp).err().as_deref(),
      Some("NOSPEC: recovery: no packed function; the statements tie")
    );
  }

  #[test]
  fn an_exhausted_reducer_ends_the_search() {
    // `loop := loop` has no weak head normal form
    let looping = ConstantInfo::DefnInfo(DefinitionVal {
      cnst: ConstantVal {
        name: dotted("loop"),
        level_params: vec![],
        typ: sort0(),
      },
      value: c("loop"),
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![dotted("loop")],
    });
    let env = vec![looping];
    let env = lookup(&env);
    let can = dotted("can");
    let major = c("t");
    let entry = Expr::app(fvar(&can), major.clone());
    let node = |a: Expr| {
      mk_app_n(cnst(&n_pprod(), &[lvl_one(), lvl_one()]), &[a, entry.clone()])
    };
    let search = |fuel: usize, a: Expr| {
      search_dict(&env, &can, &major, &[], fuel, &node(a), Vec::new())
    };
    // the first component is terminal: the entry is the second
    assert_eq!(
      search(SEARCH_DEPTH, c("PUnit")),
      Ok(Some(vec![PStep::Proj(n_pprod(), 1)]))
    );
    // the first component does not reduce: a refusal, the second component
    // is not tried
    assert_eq!(search(SEARCH_DEPTH, c("loop")), Err(WHNF_EXHAUSTED.into()));
    // the bound ends the search without a result
    assert_eq!(search(1, c("PUnit")), Ok(None));
  }

  #[test]
  fn refusals_carry_the_lean_texts() {
    let mut hs = Holes::default();
    assert_eq!(
      hs.pop_hole().err().as_deref(),
      Some("recovery: the holes ran out during re-encoding")
    );
    hs.push_hole(Hole::SCall(0));
    assert_eq!(
      hs.pop_expr().err().as_deref(),
      Some("recovery: an erased annotation was expected")
    );
    let names = ["f", "g", "h"].map(dotted);
    let s = pf_spine();
    assert_eq!(enc_p(&s, &names, 0, &c("g")), Ok(proj(&n_pprod(), 1, bvar(0))));
    assert_eq!(
      enc_p(&s, &names, 0, &c("h")).err().as_deref(),
      Some("recovery: a member past the fixpoint's packing")
    );
    assert_eq!(
      rec_p(&s, &names, &[], 0, 0, &c("x")).err().as_deref(),
      Some(RECOVERY_EXHAUSTED)
    );
    let k = wf_clique();
    assert_eq!(
      with_member_fixed(&k.members, &[c("x")], &[vec![], vec![]])
        .err()
        .as_deref(),
      Some("recovery: no recovered body for g")
    );
    assert_eq!(
      with_member_fixed(&k.members, &[c("x"), c("y")], &[vec![]])
        .err()
        .as_deref(),
      Some("recovery: no fixed positions for g")
    );
  }
}
