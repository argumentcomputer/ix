//! The equation rows of a transported well-founded clique and the faithful
//! copies of its encoding, as pure functions over terms (a port of
//! `Ix/Compile/Pass/Clique/Row.lean`, whose module note is the contract).
//!
//! A transported member `f` keeps Lean's name and type, and its value becomes
//! the transported one over the canonical constants (`g._ix._mutual`, its
//! `_proof_k`). Lean's own encoding constants get faithful copies under
//! reserved names, and each member a row relating Lean's value to `f`:
//!
//! * **the encoding set** ([`encoding_set`]) of a well-founded plan: the
//!   clique's Lean encoding constants ([`is_encoding_name`]) that the rows'
//!   left-hand sides (the transported members' Lean values) reference,
//!   closed under the references of the set itself, on
//!   [`EQ_LEMMA_BOUND`]. A referenced encoding constant missing from the
//!   input is an error. The rename to the copies ([`src_rename`]) is over
//!   this set only, and a row whose statement or proof would reference an
//!   encoding constant outside it is refused (never a dangling `_ix.src`
//!   name);
//! * **the copy** `n._ix.src` of each `n` of the set ([`src_copy`]): `n`'s
//!   record (kind, type, value, level parameters, hints, safety, `all`) with
//!   its name replaced and the references to the set (constants and `all`,
//!   constructor and recursor names) renamed to their copies;
//! * **the row** `f._ix.row : @Eq.{u} T lhs (f us)` ([`row_of`]), a theorem
//!   with `f`'s level parameters, `T` its type, `us` its parameters as levels
//!   and `lhs` Lean's value of `f` with the set renamed to its copies
//!   ([`row_lhs`]). `u` is `T`'s sort ([`sort_of`]).
//!
//! Names go through [`crate::compile::pass3::names`] (`n._ix.src`,
//! `f._ix.row` by [`append_comps`]).
//!
//! **The sort** ([`sort_of`]): light and fail-closed, over declared types. A
//! `Sort v` has sort `succ v`; a `∀` the [`mk_level_imax_prime`] (Lean's
//! simplifying `imax`) of its domain's and body's sorts, the body under a
//! free variable `_clq_sort.k`; an application of a constant or a free
//! variable its head's declared type (a constant's at its levels), the
//! arguments peeled one `∀` each (reduced by [`whnf`] when not one), reduced
//! to a `Sort v`: `v`. Anything else, or an exhausted bound ([`SORT_DEPTH`],
//! or [`WHNF_FUEL`] per reduction), is `None`, and then no row. The level is
//! not normalised.
//!
//! **The proof** ([`row_proof`]) is a fixed term recipe, every implicit
//! argument and level explicit (see `Row.lean`'s note for the term): over the
//! member's parameters, `WellFounded.induction` over Lean's packed domain of
//! the motive "Lean's packed function equals the canonical one at the
//! canonical summand", each step one unfolding of either fixpoint
//! (`fix_eq`), the recursive calls related through the induction hypothesis
//! (`funext`, `congrArg`) and the two functionals' applications identified
//! by conversion (`Eq.refl`); then `funext` over the parameters. The case
//! trees are [`Tree::build`] over Lean's spine. The proof is built over
//! Lean's constants and the set renamed to its copies at the end.
//!
//! **Refusals** (errors; the wiring keeps Lean's form): an alias member; a
//! value or root outside the recipe's shapes; a definition clique (motive
//! level not `0`) whose functional uses the recursion binder other than as
//! calls through `PSigma` layers ([`leaf_reduces`]); no sort; an encoding
//! constant missing from the input or not a definition or theorem; a row
//! mentioning an encoding constant outside the set. Plans of another encoding
//! get no row ([`row_of`] is `None`, [`rows_of`] empty).
//!
//! Total and pure: the walks are structural or on the named bounds, no
//! panicking access. The pretty-name sorts are stable here and Lean's `qsort`
//! is not (see [`super::plan_clique`] on ties).

use std::slice;

use rustc_hash::FxHashSet;

use ix_common::env::{
  BinderInfo, ConstantInfo, ConstantVal, DefinitionVal, Expr, ExprData,
  InductiveVal, Level, LevelData, Name, OpaqueVal, RecursorRule, RecursorVal,
  TheoremVal,
};

use super::basic::{
  ConstOf, Decl, Local, R, TState, abstract_fvars, cnst, const_app,
  const_occurrences, dotted, exprs, extract, inst_locals, instantiate_rev,
  lam_arity, level_is_zero, lvl_one, mk_app_n, mk_forall, mk_lambda,
  mk_level_max_prime, n_psum, n_psum_cases_on, n_psum_inl, n_psum_inr,
  peel_lams, rename_consts, root_name, sort0, tm_idx,
};
use super::bounds::{EQ_LEMMA_BOUND, SORT_DEPTH, WF_DEPTH, WHNF_FUEL};
use super::packing::{
  PackKind, Spine, Tree, decode_inj, decode_spine, decode_tree, mk_inj,
};
use super::plan::{CliquePlan, Encoding};
use super::plan_clique::{pop_unseen, push_stack, value_of};
use super::table::is_encoding_name;
use super::telescope::{beta_app, open_binders, whnf};
use super::wf::{apply_wf_case, leaf_reduces};
use crate::compile::pass3::expr::{
  get_app_fn_args, nat, strip_mdata, subst_levels,
};
use crate::compile::pass3::names::{Comp, IX_COMPONENT, append_comps};
use crate::compile::pass3::par_big_stack;

/// A constant lookup that threads may share: what [`rows_of`] reads, one
/// member's row on each of its threads.
pub type SyncConstOf<'a> = &'a (dyn Fn(&Name) -> Option<ConstantInfo> + Sync);

// ---------------------------------------------------------------------------
// Names
// ---------------------------------------------------------------------------

/// `srcName`: `n._ix.src`, the faithful copy of the encoding constant `n`.
pub fn src_name(n: &Name) -> Name {
  append_comps(
    n,
    &[Comp::S(IX_COMPONENT.to_string()), Comp::S("src".to_string())],
  )
}

/// `rowName`: `f._ix.row`, the equation row of the member `f`.
pub fn row_name(f: &Name) -> Name {
  append_comps(
    f,
    &[Comp::S(IX_COMPONENT.to_string()), Comp::S("row".to_string())],
  )
}

/// `LibraryNames.nEq`.
pub fn n_eq() -> Name {
  dotted("Eq")
}
/// `LibraryNames.nEqRefl`.
pub fn n_eq_refl() -> Name {
  dotted("Eq.refl")
}
pub fn n_eq_symm() -> Name {
  dotted("Eq.symm")
}
pub fn n_eq_trans() -> Name {
  dotted("Eq.trans")
}
pub fn n_congr_arg() -> Name {
  dotted("congrArg")
}
pub fn n_funext() -> Name {
  dotted("funext")
}
pub fn n_wf_induction() -> Name {
  dotted("WellFounded.induction")
}
pub fn n_wf_fix() -> Name {
  dotted("WellFounded.fix")
}
pub fn n_wf_fix_eq() -> Name {
  dotted("WellFounded.fix_eq")
}
pub fn n_nat_fix() -> Name {
  dotted("WellFounded.Nat.fix")
}
pub fn n_nat_fix_eq() -> Name {
  dotted("WellFounded.Nat.fix_eq")
}
pub fn n_inv_image_wf() -> Name {
  dotted("InvImage.wf")
}
pub fn n_wf_rel_rel() -> Name {
  dotted("WellFoundedRelation.rel")
}
pub fn n_wf_rel_wf() -> Name {
  dotted("WellFoundedRelation.wf")
}
pub fn n_nat() -> Name {
  dotted("Nat")
}
pub fn n_nat_lt_wf_rel() -> Name {
  dotted("Nat.lt_wfRel")
}

/// `rowPrereqs`: the library constants a row proof references (for the
/// scheduler): the row's statement `Eq`, the proof's equality steps, the
/// induction and the fixpoint equations, the sum packing's type, injections
/// and case split, and the `Nat.fix` well-foundedness witness.
pub fn row_prereqs() -> Vec<Name> {
  vec![
    n_eq(),
    n_eq_refl(),
    n_eq_symm(),
    n_eq_trans(),
    n_congr_arg(),
    n_funext(),
    n_wf_induction(),
    n_wf_fix_eq(),
    n_nat_fix_eq(),
    n_psum(),
    n_psum_cases_on(),
    n_psum_inl(),
    n_psum_inr(),
    n_inv_image_wf(),
    n_wf_rel_rel(),
    n_wf_rel_wf(),
    n_nat(),
    n_nat_lt_wf_rel(),
  ]
}

// ---------------------------------------------------------------------------
// The copies and the row's left-hand side
// ---------------------------------------------------------------------------

/// `srcRename`: the renaming of the encoding set `enc` to its copies.
pub fn src_rename(enc: &FxHashSet<Name>, c: &Name) -> Option<Name> {
  if enc.contains(c) { Some(src_name(c)) } else { None }
}

/// `srcCopy`: the copy `n._ix.src` of `n`'s record `ci`: the name replaced,
/// and the references to `enc` (in the type, the value, `all`, and the names
/// of a constructor's inductive or a recursor's rules) renamed to their
/// copies.
pub fn src_copy(enc: &FxHashSet<Name>, ci: &ConstantInfo) -> ConstantInfo {
  let e = |x: &Expr| rename_consts(&|c| src_rename(enc, c), x);
  let n = |c: &Name| src_rename(enc, c).unwrap_or_else(|| c.clone());
  let ns = |cs: &[Name]| cs.iter().map(n).collect::<Vec<_>>();
  let cv = |v: &ConstantVal| ConstantVal {
    name: src_name(&v.name),
    level_params: v.level_params.clone(),
    typ: e(&v.typ),
  };
  match ci {
    ConstantInfo::AxiomInfo(v) => {
      let mut v = v.clone();
      v.cnst = cv(&v.cnst);
      ConstantInfo::AxiomInfo(v)
    },
    ConstantInfo::DefnInfo(v) => ConstantInfo::DefnInfo(DefinitionVal {
      cnst: cv(&v.cnst),
      value: e(&v.value),
      all: ns(&v.all),
      ..v.clone()
    }),
    ConstantInfo::ThmInfo(v) => ConstantInfo::ThmInfo(TheoremVal {
      cnst: cv(&v.cnst),
      value: e(&v.value),
      all: ns(&v.all),
    }),
    ConstantInfo::OpaqueInfo(v) => ConstantInfo::OpaqueInfo(OpaqueVal {
      cnst: cv(&v.cnst),
      value: e(&v.value),
      all: ns(&v.all),
      ..v.clone()
    }),
    ConstantInfo::QuotInfo(v) => {
      let mut v = v.clone();
      v.cnst = cv(&v.cnst);
      ConstantInfo::QuotInfo(v)
    },
    ConstantInfo::InductInfo(v) => ConstantInfo::InductInfo(InductiveVal {
      cnst: cv(&v.cnst),
      all: ns(&v.all),
      ctors: ns(&v.ctors),
      ..v.clone()
    }),
    ConstantInfo::CtorInfo(v) => {
      let mut v = v.clone();
      v.cnst = cv(&v.cnst);
      v.induct = n(&v.induct);
      ConstantInfo::CtorInfo(v)
    },
    ConstantInfo::RecInfo(v) => {
      let rules = v
        .rules
        .iter()
        .map(|r| RecursorRule { ctor: n(&r.ctor), rhs: e(&r.rhs), ..r.clone() })
        .collect();
      ConstantInfo::RecInfo(RecursorVal {
        cnst: cv(&v.cnst),
        all: ns(&v.all),
        rules,
        ..v.clone()
      })
    },
  }
}

/// `rowLhs`: the row's left-hand side, Lean's value of the member with the
/// encoding set renamed to its copies.
pub fn row_lhs(enc: &FxHashSet<Name>, lean_value: &Expr) -> Expr {
  rename_consts(&|c| src_rename(enc, c), lean_value)
}

// ---------------------------------------------------------------------------
// The encoding set
// ---------------------------------------------------------------------------

/// `encodingClosure`: the names reached from `stack` through the references
/// satisfying `is_enc` of their types and values, added to `seen`. At most
/// `fuel` names are visited; an exhausted bound, or a name that is not in
/// the input, is an error.
pub fn encoding_closure(
  const_of: ConstOf<'_>,
  is_enc: &dyn Fn(&Name) -> bool,
  fuel: usize,
  mut stack: Vec<Name>,
  mut seen: FxHashSet<Name>,
) -> R<FxHashSet<Name>> {
  let mut fuel = fuel;
  loop {
    let Some(c) = pop_unseen(&seen, &mut stack) else { return Ok(seen) };
    let Some(rest) = fuel.checked_sub(1) else {
      return Err("row: the encoding set exceeds its bound".to_string());
    };
    fuel = rest;
    let Some(ci) = const_of(&c) else {
      return Err(format!(
        "row: the encoding constant {} is not in the input",
        c.pretty()
      ));
    };
    let mut refs = const_occurrences(is_enc, ci.get_type());
    if let Some(v) = value_of(&ci) {
      refs.extend(const_occurrences(is_enc, v));
    }
    push_stack(&mut stack, refs);
    seen.insert(c);
  }
}

/// `rowMembers`: the members of a plan that get rows, its transported
/// members, in Lean's order.
pub fn row_members(plan: &CliquePlan) -> Vec<Name> {
  plan.all.iter().filter(|m| plan.members.contains_key(*m)).cloned().collect()
}

/// `encodingSet`: the encoding set of a plan, the clique's Lean encoding
/// constants that the rows' left-hand sides (the Lean values of
/// [`row_members`]) reference, closed under those references. At most
/// [`EQ_LEMMA_BOUND`] names are visited.
pub fn encoding_set(
  const_of: ConstOf<'_>,
  plan: &CliquePlan,
) -> R<FxHashSet<Name>> {
  let is_enc = |n: &Name| is_encoding_name(&plan.all, n);
  let mut seeds = Vec::new();
  for m in row_members(plan) {
    if let Some(ci) = const_of(&m)
      && let Some(v) = value_of(&ci)
    {
      seeds.extend(const_occurrences(&is_enc, v));
    }
  }
  let mut stack = Vec::new();
  push_stack(&mut stack, seeds);
  encoding_closure(
    const_of,
    &is_enc,
    EQ_LEMMA_BOUND,
    stack,
    FxHashSet::default(),
  )
}

// ---------------------------------------------------------------------------
// The row's level
// ---------------------------------------------------------------------------

/// `levelNeverZero`: Lean's `Level.isNeverZero`.
pub fn level_never_zero(l: &Level) -> bool {
  match l.as_data() {
    LevelData::Succ(..) => true,
    LevelData::Max(a, b, _) => level_never_zero(a) || level_never_zero(b),
    LevelData::Imax(_, b, _) => level_never_zero(b),
    _ => false,
  }
}

/// `mkLevelIMax'`: Lean's `mkLevelIMax'` (`mkLevelIMaxCore`), the
/// simplifying `imax` of `inferType`'s `∀` rule.
pub fn mk_level_imax_prime(u: &Level, v: &Level) -> Level {
  if level_never_zero(v) {
    mk_level_max_prime(u, v)
  } else if level_is_zero(v) || level_is_zero(u) {
    v.clone()
  } else if u == v {
    u.clone()
  } else {
    Level::imax(u.clone(), v.clone())
  }
}

/// `sortVarRoot`: the root of the free variables [`sort_of`] opens binders
/// with.
pub fn sort_var_root() -> Name {
  root_name("_clq_sort")
}

/// `headType?`: the declared type of an application head, a constant at its
/// levels (as many as its parameters), or a free variable of `ctx`.
pub fn head_type(
  const_of: ConstOf<'_>,
  ctx: &[Local],
  h: &Expr,
) -> Option<Expr> {
  match h.as_data() {
    ExprData::Const(c, us, _) => {
      let ci = const_of(c)?;
      if ci.get_level_params().len() != us.len() {
        return None;
      }
      Some(subst_levels(ci.get_level_params(), us, ci.get_type()))
    },
    ExprData::Fvar(x, _) => {
      ctx.iter().find(|l| l.fvar == *x).map(|l| l.typ.clone())
    },
    _ => None,
  }
}

/// `instForallArgs`: `ty` at the arguments `args`, each one instantiating a
/// `∀`, `ty` reduced to weak head normal form first when it is not one.
pub fn inst_forall_args(
  const_of: ConstOf<'_>,
  ty: &Expr,
  args: &[Expr],
) -> Option<Expr> {
  let mut ty = ty.clone();
  for a in args {
    let t = strip_mdata(&ty);
    let t = if matches!(t.as_data(), ExprData::ForallE(..)) {
      t
    } else {
      strip_mdata(&whnf(const_of, WHNF_FUEL, &t).ok()?)
    };
    let ExprData::ForallE(_, _, b, _, _) = t.as_data() else { return None };
    ty = instantiate_rev(b, slice::from_ref(a));
  }
  Some(ty)
}

/// `sortOfAux`: [`sort_of`] on an explicit bound (`ctx` is restored on
/// return).
pub fn sort_of_aux(
  const_of: ConstOf<'_>,
  fuel: usize,
  ctx: &mut Vec<Local>,
  ty: &Expr,
) -> Option<Level> {
  let fuel = fuel.checked_sub(1)?;
  let ty = strip_mdata(ty);
  match ty.as_data() {
    ExprData::Sort(u, _) => Some(Level::succ(u.clone())),
    ExprData::ForallE(nm, dom, body, bi, _) => {
      let u = sort_of_aux(const_of, fuel, ctx, dom)?;
      let x = Local {
        fvar: Name::num(sort_var_root(), nat(ctx.len())),
        user_name: nm.clone(),
        typ: dom.clone(),
        bi: bi.clone(),
      };
      let body = instantiate_rev(body, &[x.expr()]);
      ctx.push(x);
      let v = sort_of_aux(const_of, fuel, ctx, &body);
      ctx.pop();
      Some(mk_level_imax_prime(&u, &v?))
    },
    _ => {
      let (h, args) = get_app_fn_args(&ty);
      let head = head_type(const_of, ctx, &strip_mdata(&h))?;
      let t = inst_forall_args(const_of, &head, &args)?;
      let r = whnf(const_of, WHNF_FUEL, &t).ok()?;
      match strip_mdata(&r).as_data() {
        ExprData::Sort(u, _) => Some(u.clone()),
        _ => None,
      }
    },
  }
}

/// `sortOf?`: the sort `u` of the type `ty` (`ty : Sort u`), over declared
/// types, with `ctx` the free variables' types (see the module note);
/// `None` outside the computation's shapes or past [`SORT_DEPTH`].
pub fn sort_of(
  const_of: ConstOf<'_>,
  ctx: &[Local],
  ty: &Expr,
) -> Option<Level> {
  let mut ctx = ctx.to_vec();
  sort_of_aux(const_of, SORT_DEPTH, &mut ctx, ty)
}

// ---------------------------------------------------------------------------
// The well-founded row proof
// ---------------------------------------------------------------------------

/// `RowFix`: a packed function's root at its fixed arguments.
#[derive(Clone, Debug)]
pub struct RowFix {
  /// `WellFounded.Nat.fix` (else `WellFounded.fix`)
  pub nat: bool,
  /// the root's levels `[u, v]`: the domain's and the motive's
  pub levels: Vec<Level>,
  /// the root's arguments (without the point)
  pub args: Vec<Expr>,
  pub domain: Expr,
  pub motive: Expr,
  pub functional: Expr,
  pub domain_level: Level,
  pub motive_level: Level,
}

/// `readRowFix`: `WellFounded.fix.{u,v} α C r hwf F` or
/// `WellFounded.Nat.fix.{u,v} α C h F`.
pub fn read_row_fix(root: &Expr) -> R<RowFix> {
  let not_fix = || {
    "row: the packed function's value is not a `WellFounded.fix` or \
     `WellFounded.Nat.fix` root"
      .to_string()
  };
  let Some((h, levels, args)) = const_app(root) else { return Err(not_fix()) };
  let [u, v] = levels.as_slice() else { return Err(not_fix()) };
  let (u, v) = (u.clone(), v.clone());
  let (nat, domain, motive, functional) = if h == n_wf_fix() {
    let [a, c, _, _, f] = args.as_slice() else { return Err(not_fix()) };
    (false, a.clone(), c.clone(), f.clone())
  } else if h == n_nat_fix() {
    let [a, c, _, f] = args.as_slice() else { return Err(not_fix()) };
    (true, a.clone(), c.clone(), f.clone())
  } else {
    return Err(not_fix());
  };
  Ok(RowFix {
    nat,
    levels,
    args,
    domain,
    motive,
    functional,
    domain_level: u,
    motive_level: v,
  })
}

impl RowFix {
  /// `RowFix.eqAt`: the fixpoint equation of a root (`fix_eq` /
  /// `Nat.fix_eq`, the root's arguments then the point).
  pub fn eq_at(&self, point: &Expr) -> Expr {
    let head = if self.nat { n_nat_fix_eq() } else { n_wf_fix_eq() };
    let mut args = self.args.clone();
    args.push(point.clone());
    mk_app_n(cnst(&head, &self.levels), &args)
  }
}

/// `RowSide`: one side of a row, a packed function at a member's fixed
/// arguments.
#[derive(Clone, Debug)]
pub struct RowSide {
  /// `P.{us} fixed`
  pub head: Expr,
  pub fix: RowFix,
  /// the domain's sum packing
  pub spine: Spine,
  /// the recursion relation `R y x`, over the free variables `rel_y`,
  /// `rel_x`
  pub rel_y: Name,
  pub rel_x: Name,
  pub rel: Expr,
}

impl RowSide {
  /// `RowSide.relAt`: `R y x` at the given terms.
  pub fn rel_at(&self, y: &Expr, x: &Expr) -> Expr {
    inst_locals(
      &abstract_fvars(&[self.rel_y.clone(), self.rel_x.clone()], &self.rel),
      &[y.clone(), x.clone()],
    )
  }
}

/// A packed function's declaration by name (Lean's `Name → Option Decl`).
pub type DeclOf<'a> = &'a dyn Fn(&Name) -> Option<Decl>;

/// `rowSide`: the side of the body `P.{us} fixed point` (a member's value
/// under its parameters), with `decl_of` the packed function's declaration:
/// its root at the fixed arguments, the domain's packing of `n` summands and
/// the relation of the functional's recursion binder; and the point.
pub fn row_side(
  tm: &mut TState,
  decl_of: DeclOf<'_>,
  n: usize,
  body: &Expr,
  what: &str,
) -> R<(RowSide, Expr)> {
  let not_packed =
    || format!("row: {what} is not an application of the packed function");
  let Some((p, us, args)) = const_app(body) else { return Err(not_packed()) };
  let Some((point, fixed)) = args.split_last() else {
    return Err(not_packed());
  };
  let Some(d) = decl_of(&p) else {
    return Err(format!(
      "row: {what}: {} is not the clique's packed function",
      p.pretty()
    ));
  };
  if d.level_params.len() != us.len() {
    return Err(format!(
      "row: {what}: the packed function's universe arguments"
    ));
  }
  let fx = read_row_fix(&beta_app(
    &subst_levels(&d.level_params, &us, &d.value),
    fixed,
  ))?;
  let Some(spine) = decode_spine(PackKind::Psum, n, &fx.domain) else {
    return Err(format!(
      "row: {what}: the fixpoint's domain is not the clique's sum packing"
    ));
  };
  let (xs, rest) = open_binders(tm, true, 1, &fx.functional)?;
  let Some(x) = xs.first() else {
    return Err(format!("row: {what}: the functional has no argument"));
  };
  let rest = strip_mdata(&rest);
  let ExprData::Lam(_, rec_type, _, _, _) = rest.as_data() else {
    return Err(format!("row: {what}: the functional has no recursion binder"));
  };
  let (ys, rec_body) = open_binders(tm, false, 1, rec_type)?;
  let Some(y) = ys.first() else {
    return Err(format!("row: {what}: the recursion binder is not a function"));
  };
  let rec_body = strip_mdata(&rec_body);
  let ExprData::ForallE(_, rel, _, _, _) = rec_body.as_data() else {
    return Err(format!(
      "row: {what}: the recursion binder has no decreasing hypothesis"
    ));
  };
  let side = RowSide {
    head: mk_app_n(cnst(&p, &us), fixed),
    fix: fx,
    spine,
    rel_y: y.fvar.clone(),
    rel_x: x.fvar.clone(),
    rel: rel.clone(),
  };
  Ok((side, point.clone()))
}

/// `rowLocal`: a local named `name` (default binder).
pub fn row_local(tm: &mut TState, name: &str, typ: Expr) -> Local {
  Local {
    fvar: tm.fresh_fvar(),
    user_name: root_name(name),
    typ,
    bi: BinderInfo::Default,
  }
}

/// `rowSome`: an optional result, or the named refusal.
pub fn row_some<T>(what: &str, x: Option<T>) -> R<T> {
  x.ok_or_else(|| format!("row: {what}"))
}

/// `rowTelescope`: the domains of `typ`'s leading `∀`s at the terms `xs`,
/// each with the rest of the type after it (instantiated through it).
pub fn row_telescope(typ: &Expr, xs: &[Expr]) -> R<Vec<(Expr, Expr)>> {
  let mut cur = typ.clone();
  let mut out = Vec::new();
  for x in xs {
    let s = strip_mdata(&cur);
    let ExprData::ForallE(_, dom, body, _, _) = s.as_data() else {
      return Err(
        "row: the member's type binds fewer parameters than its value"
          .to_string(),
      );
    };
    let rest = instantiate_rev(body, slice::from_ref(x));
    out.push((dom.clone(), rest.clone()));
    cur = rest;
  }
  Ok(out)
}

/// The two sides of a row proof and the clique's shape: the term builders of
/// [`row_proof`] (`M`, `Φ`, the case splits and the induction step). Every
/// case tree is over Lean's spine; the canonical injections are on the
/// canonical spine at `σ[j]`.
pub struct RowSides<'a> {
  /// Lean's side
  pub lean: RowSide,
  /// the canonical side
  pub ix: RowSide,
  /// the number of members
  pub n: usize,
  pub sigma: &'a [usize],
}

/// A motive of a case split, at the split variable.
pub type MotiveK<'a> = &'a dyn Fn(&mut TState, &Expr) -> R<Expr>;

/// A leaf of a case split, at the summand and its variable.
pub type LeafK<'a> = &'a dyn Fn(&mut TState, usize, &Local) -> R<Expr>;

impl RowSides<'_> {
  /// Lean's packed domain `α`.
  pub fn alpha(&self) -> &Expr {
    &self.lean.fix.domain
  }

  /// `C x` (`applyWFCase`).
  pub fn at_c(&self, x: &Expr) -> Expr {
    apply_wf_case(&self.lean.fix.motive, x)
  }

  /// `@Eq.{v} (C x) a b`.
  pub fn eq_at(&self, x: &Expr, a: Expr, b: Expr) -> Expr {
    mk_app_n(
      cnst(&n_eq(), slice::from_ref(&self.lean.fix.motive_level)),
      &[self.at_c(x), a, b],
    )
  }

  /// Lean's injection `inj_j w`.
  pub fn inj_l(&self, j: usize, w: &Expr) -> R<Expr> {
    row_some("Lean's injection", mk_inj(&self.lean.spine, j, w))
  }

  /// The canonical injection `inj'_{σ j} w`.
  pub fn inj_i(&self, j: usize, w: &Expr) -> R<Expr> {
    let k = *tm_idx(self.sigma, j, "row: σ")?;
    row_some("the canonical injection", mk_inj(&self.ix.spine, k, w))
  }

  /// A case split of `major : α` at the motive's level `w` (`Tree.build`):
  /// the motive at a fresh `x`, then each summand's leaf at a fresh `w`.
  pub fn cases(
    &self,
    tm: &mut TState,
    w: &Level,
    motive: MotiveK<'_>,
    major: &Expr,
    leaf: LeafK<'_>,
  ) -> R<Expr> {
    let x = row_local(tm, "x", self.alpha().clone());
    let m = motive(tm, &x.expr())?;
    let motive_body = abstract_fvars(slice::from_ref(&x.fvar), &m);
    let mut leaves = Vec::new();
    for j in 0..self.n {
      let summand = tm_idx(&self.lean.spine.leaves, j, "row: summand")?.clone();
      let wl = row_local(tm, "w", summand);
      let body = leaf(tm, j, &wl)?;
      leaves.push(mk_lambda(slice::from_ref(&wl), &body));
    }
    let tree = Tree {
      spine: self.lean.spine.clone(),
      w: w.clone(),
      motive_body,
      motive_name: x.user_name,
      major: major.clone(),
      leaves,
      extras: vec![],
      alt_names: vec![],
    };
    row_some("the case tree", tree.build())
  }

  /// `M x`: the members' equations at their summands.
  pub fn mot_m(&self, tm: &mut TState, major: &Expr) -> R<Expr> {
    self.cases(tm, &lvl_one(), &|_, _| Ok(sort0()), major, &|_, j, w| {
      let xl = self.inj_l(j, &w.expr())?;
      let xi = self.inj_i(j, &w.expr())?;
      Ok(self.eq_at(
        &xl,
        Expr::app(self.lean.head.clone(), xl.clone()),
        Expr::app(self.ix.head.clone(), xi),
      ))
    })
  }

  /// `Φ y`: the canonical fixpoint at the canonical summand of `y`'s.
  pub fn phi(&self, tm: &mut TState, major: &Expr) -> R<Expr> {
    self.cases(
      tm,
      &self.lean.fix.motive_level,
      &|_, x| Ok(self.at_c(x)),
      major,
      &|_, j, w| Ok(Expr::app(self.ix.head.clone(), self.inj_i(j, &w.expr())?)),
    )
  }

  /// `IH x := ∀ (y : α) (hy : R y x), M y`.
  pub fn ih_type(&self, tm: &mut TState, x: &Expr) -> R<Expr> {
    let y = row_local(tm, "y", self.alpha().clone());
    let hy = row_local(tm, "hy", self.lean.rel_at(&y.expr(), x));
    let m = self.mot_m(tm, &y.expr())?;
    Ok(mk_forall(&[y, hy], &m))
  }

  /// `λ (y : α) (hy : rel y). g y`.
  pub fn guarded(
    &self,
    tm: &mut TState,
    alpha: &Expr,
    rel: &dyn Fn(&Expr) -> Expr,
    g: MotiveK<'_>,
  ) -> R<Expr> {
    let y = row_local(tm, "y", alpha.clone());
    let hy = row_local(tm, "hy", rel(&y.expr()));
    let body = g(tm, &y.expr())?;
    Ok(mk_lambda(&[y, hy], &body))
  }

  /// The induction step at summand `j`: `λ (ih : IH xL). chain_j`.
  pub fn branch(&self, tm: &mut TState, j: usize, w: &Local) -> R<Expr> {
    let (sl, si) = (&self.lean, &self.ix);
    let v_l = &sl.fix.motive_level;
    let u_l = &sl.fix.domain_level;
    let xl = self.inj_l(j, &w.expr())?;
    let xi = self.inj_i(j, &w.expr())?;
    let ih_ty = self.ih_type(tm, &xl)?;
    let ih = row_local(tm, "ih", ih_ty);
    let g_a =
      self.guarded(tm, self.alpha(), &|y| sl.rel_at(y, &xl), &|_, y| {
        Ok(Expr::app(sl.head.clone(), y.clone()))
      })?;
    let g_b =
      self.guarded(tm, &si.fix.domain, &|y| si.rel_at(y, &xi), &|_, y| {
        Ok(Expr::app(si.head.clone(), y.clone()))
      })?;
    let g_phi =
      self.guarded(tm, self.alpha(), &|y| sl.rel_at(y, &xl), &|tm, y| {
        self.phi(tm, y)
      })?;
    let ty = self.at_c(&xl);
    let f_l = Expr::app(sl.fix.functional.clone(), xl.clone());
    let f_i = Expr::app(si.fix.functional.clone(), xi.clone());
    let lhs = Expr::app(sl.head.clone(), xl.clone());
    let rhs = Expr::app(si.head.clone(), xi.clone());
    // K : gA = gΦ, from the induction hypothesis
    let y = row_local(tm, "y", self.alpha().clone());
    let hy = row_local(tm, "hy", sl.rel_at(&y.expr(), &xl));
    let split_motive = |tm: &mut TState, t: &Expr| -> R<Expr> {
      let mt = self.mot_m(tm, t)?;
      let m = row_local(tm, "m", mt);
      let p = self.phi(tm, t)?;
      Ok(mk_forall(
        slice::from_ref(&m),
        &self.eq_at(t, Expr::app(sl.head.clone(), t.clone()), p),
      ))
    };
    let split_leaf = |tm: &mut TState, k: usize, w2: &Local| -> R<Expr> {
      let xk = self.inj_l(k, &w2.expr())?;
      let mt = self.mot_m(tm, &xk)?;
      let m = row_local(tm, "m", mt);
      Ok(mk_lambda(slice::from_ref(&m), &m.expr()))
    };
    let split =
      self.cases(tm, &Level::zero(), &split_motive, &y.expr(), &split_leaf)?;
    let at_y = Expr::app(split, mk_app_n(ih.expr(), &[y.expr(), hy.expr()]));
    let rec_level = mk_level_imax_prime(&Level::zero(), v_l);
    let inner = mk_app_n(
      cnst(&n_funext(), &[Level::zero(), v_l.clone()]),
      &[
        hy.typ.clone(),
        mk_lambda(slice::from_ref(&hy), &self.at_c(&y.expr())),
        Expr::app(g_a.clone(), y.expr()),
        Expr::app(g_phi.clone(), y.expr()),
        mk_lambda(slice::from_ref(&hy), &at_y),
      ],
    );
    let k_proof = mk_app_n(
      cnst(&n_funext(), &[u_l.clone(), rec_level.clone()]),
      &[
        self.alpha().clone(),
        mk_lambda(
          slice::from_ref(&y),
          &mk_forall(slice::from_ref(&hy), &self.at_c(&y.expr())),
        ),
        g_a.clone(),
        g_phi.clone(),
        mk_lambda(slice::from_ref(&y), &inner),
      ],
    );
    let congr = mk_app_n(
      cnst(
        &n_congr_arg(),
        &[mk_level_imax_prime(u_l, &rec_level), v_l.clone()],
      ),
      &[
        mk_forall(&[y.clone(), hy.clone()], &self.at_c(&y.expr())),
        ty.clone(),
        g_a.clone(),
        g_phi.clone(),
        f_l.clone(),
        k_proof,
      ],
    );
    let refl = mk_app_n(
      cnst(&n_eq_refl(), slice::from_ref(v_l)),
      &[ty.clone(), Expr::app(f_l.clone(), g_phi.clone())],
    );
    let symm = mk_app_n(
      cnst(&n_eq_symm(), slice::from_ref(v_l)),
      &[
        ty.clone(),
        rhs.clone(),
        Expr::app(f_i.clone(), g_b.clone()),
        si.fix.eq_at(&xi),
      ],
    );
    let trans = |a: Expr, b: Expr, p: Expr, q: Expr| {
      mk_app_n(
        cnst(&n_eq_trans(), slice::from_ref(v_l)),
        &[ty.clone(), a, b, rhs.clone(), p, q],
      )
    };
    let f_l_a = Expr::app(f_l.clone(), g_a);
    let f_l_phi = Expr::app(f_l, g_phi);
    let chain = trans(
      lhs,
      f_l_a.clone(),
      sl.fix.eq_at(&xl),
      trans(
        f_l_a,
        f_l_phi.clone(),
        congr,
        trans(f_l_phi, Expr::app(f_i, g_b), refl, symm),
      ),
    );
    Ok(mk_lambda(slice::from_ref(&ih), &chain))
  }
}

/// The inputs of [`row_proof`] (Lean's `rowProof` arguments).
pub struct RowProofInput<'a> {
  pub const_of: ConstOf<'a>,
  /// the declaration of Lean's packed function
  pub lean_decl: DeclOf<'a>,
  /// the declaration of the canonical packed function
  pub ix_decl: DeclOf<'a>,
  /// the number of members
  pub n: usize,
  pub sigma: &'a [usize],
  /// the member's Lean index
  pub index: usize,
  /// the member's type
  pub typ: &'a Expr,
  pub lean_value: &'a Expr,
  /// the member's transported value
  pub ix_value: &'a Expr,
  /// `f us`
  pub rhs: &'a Expr,
}

/// `rowProof`: the proof of `lean_value = rhs` for the member at Lean index
/// `index` (see `Row.lean`'s module note for the term). Over Lean's
/// constants: the caller renames the encoding set.
pub fn row_proof(tm: &mut TState, inp: &RowProofInput<'_>) -> R<Expr> {
  let n = inp.n;
  // the member's parameters, and both bodies under them
  let arity = lam_arity(inp.lean_value);
  let (ps, body_l) = open_binders(tm, true, arity, inp.lean_value)?;
  let pes = exprs(&ps);
  let (ix_binders, ix_body) = peel_lams(arity, inp.ix_value);
  if ix_binders.len() != arity {
    return Err(
      "row: the transported value does not bind the member's parameters"
        .to_string(),
    );
  }
  let body_i = inst_locals(&ix_body, &pes);
  let tele = row_telescope(inp.typ, &pes)?;
  let (s_l, x_l) = row_side(tm, inp.lean_decl, n, &body_l, "Lean's value")?;
  let (s_i, x_i) =
    row_side(tm, inp.ix_decl, n, &body_i, "the transported value")?;
  let Some((_, j_l, _)) = decode_inj(n, &x_l) else {
    return Err("row: Lean's packed argument is not an injection".to_string());
  };
  let Some((_, j_i, _)) = decode_inj(n, &x_i) else {
    return Err(
      "row: the transported packed argument is not an injection".to_string(),
    );
  };
  if !(j_l == inp.index && inp.sigma.get(inp.index) == Some(&j_i)) {
    return Err("row: the members' injections do not follow σ".to_string());
  }
  let alpha_l = s_l.fix.domain.clone();
  let u_l = s_l.fix.domain_level.clone();
  // the conjugated step is one unfolding of either side only when Lean's
  // bodies use the recursion binder as calls (through `PSigma` layers, as
  // `leaf_reduces` decides for the packed equation lemma): threaded into a
  // `match`, the transport passes an adapter instead. Proofs (motive level
  // `0`) are equal regardless.
  if !level_is_zero(&s_l.fix.motive_level) {
    let (_, functional_body) = peel_lams(2, &s_l.fix.functional);
    let Some(tree) = decode_tree(n, &functional_body) else {
      return Err(
        "row: Lean's functional is not a refinement case tree".to_string(),
      );
    };
    if !tree.leaves.iter().all(|l| leaf_reduces(WF_DEPTH, l)) {
      return Err(
        "row: a body threads the recursion binder (argument pushing): one \
         unfolding does not give the transported body"
          .to_string(),
      );
    }
  }
  let sides = RowSides { lean: s_l, ix: s_i, n, sigma: inp.sigma };
  let x = row_local(tm, "x", alpha_l.clone());
  let ih_ty = sides.ih_type(tm, &x.expr())?;
  let ih = row_local(tm, "ih", ih_ty);
  let step_motive = |tm: &mut TState, t: &Expr| -> R<Expr> {
    let ht = sides.ih_type(tm, t)?;
    let h = row_local(tm, "ih", ht);
    let m = sides.mot_m(tm, t)?;
    Ok(mk_forall(slice::from_ref(&h), &m))
  };
  let step_tree =
    sides.cases(tm, &Level::zero(), &step_motive, &x.expr(), &|tm, j, w| {
      sides.branch(tm, j, w)
    })?;
  let step = mk_lambda(&[x, ih.clone()], &Expr::app(step_tree, ih.expr()));
  let xm = row_local(tm, "x", alpha_l.clone());
  let motive_body = sides.mot_m(tm, &xm.expr())?;
  let motive = mk_lambda(slice::from_ref(&xm), &motive_body);
  let s_l = &sides.lean;
  let relation = mk_lambda(
    &[
      Local {
        fvar: s_l.rel_y.clone(),
        user_name: root_name("y"),
        typ: alpha_l.clone(),
        bi: BinderInfo::Default,
      },
      Local {
        fvar: s_l.rel_x.clone(),
        user_name: root_name("x"),
        typ: alpha_l.clone(),
        bi: BinderInfo::Default,
      },
    ],
    &s_l.rel,
  );
  let wf = if s_l.fix.nat {
    let measure =
      tm_idx(&s_l.fix.args, 2, "row: the measure of `Nat.fix`")?.clone();
    let nat_c = cnst(&n_nat(), &[]);
    let lt_rel = cnst(&n_nat_lt_wf_rel(), &[]);
    mk_app_n(
      cnst(&n_inv_image_wf(), &[u_l.clone(), lvl_one()]),
      &[
        alpha_l.clone(),
        nat_c.clone(),
        mk_app_n(
          cnst(&n_wf_rel_rel(), &[lvl_one()]),
          &[nat_c.clone(), lt_rel.clone()],
        ),
        measure,
        mk_app_n(cnst(&n_wf_rel_wf(), &[lvl_one()]), &[nat_c, lt_rel]),
      ],
    )
  } else {
    tm_idx(
      &s_l.fix.args,
      3,
      "row: the well-foundedness proof of `WellFounded.fix`",
    )?
    .clone()
  };
  // `M xL`, which is `A xL = B xI`: Lean's body is the transported one
  let mut proof = mk_app_n(
    cnst(&n_wf_induction(), slice::from_ref(&u_l)),
    &[alpha_l, relation, wf, motive, x_l, step],
  );
  // funext over the parameters, innermost first
  for j in (0..arity).rev() {
    let p = tm_idx(&ps, j, "row: parameter")?;
    let (dom, rest) = tm_idx(&tele, j, "row: parameter type")?;
    let u = row_some(
      "no sort for a parameter's type",
      sort_of(inp.const_of, &ps, dom),
    )?;
    let v = row_some(
      "no sort for a parameter's codomain",
      sort_of(inp.const_of, &ps, rest),
    )?;
    proof = mk_app_n(
      cnst(&n_funext(), &[u, v]),
      &[
        dom.clone(),
        mk_lambda(slice::from_ref(p), rest),
        mk_lambda(&extract(&ps, j, arity), &body_l),
        mk_app_n(inp.rhs.clone(), &extract(&pes, 0, j)),
        mk_lambda(slice::from_ref(p), &proof),
      ],
    );
  }
  Ok(proof)
}

// ---------------------------------------------------------------------------
// Rows
// ---------------------------------------------------------------------------

/// `rowOfWith`: the row of the member `f` of a well-founded `plan`, with the
/// encoding set `enc` ([`encoding_set`]).
pub fn row_of_with(
  const_of: ConstOf<'_>,
  plan: &CliquePlan,
  enc: &FxHashSet<Name>,
  f: &Name,
) -> R<ConstantInfo> {
  let Some(index) = plan.all.iter().position(|a| a == f) else {
    return Err(format!("row: {} is not a member of the clique", f.pretty()));
  };
  if plan.aliases.iter().any(|(m, _)| m == f) {
    return Err(format!(
      "row: {} is an alias (its value is its representative's, at another \
       summand)",
      f.pretty()
    ));
  }
  let Some(md) = plan.members.get(f) else {
    return Err(format!("row: {} is not a transported member", f.pretty()));
  };
  let Some(ci) = const_of(f) else {
    return Err(format!("row: {} is not in the input", f.pretty()));
  };
  let Some(lean_value) = value_of(&ci) else {
    return Err(format!("row: {} has no value", f.pretty()));
  };
  let level_params = ci.get_level_params().clone();
  let typ = ci.get_type();
  let us: Vec<Level> = level_params.iter().cloned().map(Level::param).collect();
  let rhs = cnst(f, &us);
  let Some(u) = sort_of(const_of, &[], typ) else {
    return Err(format!("row: no sort for the type of {}", f.pretty()));
  };
  let lean_decl = |p: &Name| {
    if enc.contains(p) {
      const_of(p).and_then(|c| Decl::of_constant_info(&c))
    } else {
      None
    }
  };
  let ix_decl = |p: &Name| {
    plan.canon.iter().find(|(d, _)| d.name == *p).map(|(d, _)| d.clone())
  };
  let inp = RowProofInput {
    const_of,
    lean_decl: &lean_decl,
    ix_decl: &ix_decl,
    n: plan.all.len(),
    sigma: &plan.sigma,
    index,
    typ,
    lean_value,
    ix_value: &md.value,
    rhs: &rhs,
  };
  let proof = row_proof(&mut TState::default(), &inp)?;
  // every Lean encoding constant the row mentions has a copy
  let outside = |c: &Name| is_encoding_name(&plan.all, c) && !enc.contains(c);
  let mut occ = const_occurrences(&outside, lean_value);
  occ.extend(const_occurrences(&outside, &proof));
  if let Some(c) = occ.first() {
    return Err(format!(
      "row: the row of {} references the encoding constant {}, which has \
       no copy",
      f.pretty(),
      c.pretty()
    ));
  }
  let name = row_name(f);
  let statement = mk_app_n(
    cnst(&n_eq(), &[u]),
    &[typ.clone(), row_lhs(enc, lean_value), rhs],
  );
  Ok(ConstantInfo::ThmInfo(TheoremVal {
    cnst: ConstantVal { name: name.clone(), level_params, typ: statement },
    value: rename_consts(&|c| src_rename(enc, c), &proof),
    all: vec![name],
  }))
}

/// `rowOf`: the row `f._ix.row` of the member `f` (see the module note):
/// `None` for a plan that is not well-founded, an error where the recipe
/// does not apply (the wiring keeps Lean's form then).
pub fn row_of(
  const_of: ConstOf<'_>,
  plan: &CliquePlan,
  f: &Name,
) -> R<Option<ConstantInfo>> {
  if plan.encoding != Encoding::WellFounded {
    return Ok(None);
  }
  let enc = encoding_set(const_of, plan)?;
  row_of_with(const_of, plan, &enc, f).map(Some)
}

/// `rowsOf`: every record a well-founded plan adds, the copies of its
/// encoding set, then the rows of its transported members, each in
/// pretty-name order of the names they get; both empty for another
/// encoding. An encoding constant that is not a definition or a theorem is
/// an error, and so is any member's refusal (the first in that order). The
/// members' rows are computed on threads with large stacks and read back in
/// order (`par_big_stack`; Lean's `rowsOf`, a task per member), so the value
/// is the sequential one.
pub fn rows_of(
  const_of: SyncConstOf<'_>,
  plan: &CliquePlan,
) -> R<(Vec<ConstantInfo>, Vec<ConstantInfo>)> {
  if plan.encoding != Encoding::WellFounded {
    return Ok((vec![], vec![]));
  }
  let enc = encoding_set(const_of, plan)?;
  let mut names: Vec<Name> = enc.iter().cloned().collect();
  names.sort_by_cached_key(|a| src_name(a).pretty());
  let mut copies = Vec::with_capacity(names.len());
  for c in &names {
    match const_of(c) {
      Some(ci @ (ConstantInfo::DefnInfo(_) | ConstantInfo::ThmInfo(_))) => {
        copies.push(src_copy(&enc, &ci));
      },
      Some(_) => {
        return Err(format!(
          "row: the encoding constant {} is not a definition or a theorem",
          c.pretty()
        ));
      },
      None => {
        return Err(format!(
          "row: the encoding constant {} is not in the input",
          c.pretty()
        ));
      },
    }
  }
  let mut members = row_members(plan);
  members.sort_by_cached_key(|a| row_name(a).pretty());
  let rows = par_big_stack(&members, |f| row_of_with(const_of, plan, &enc, f))
    .into_iter()
    .collect::<R<Vec<_>>>()?;
  Ok((copies, rows))
}

#[cfg(test)]
mod tests {
  use std::slice;

  use rustc_hash::FxHashSet;

  use ix_common::env::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, ConstructorVal,
    DefinitionSafety, DefinitionVal, Expr, ExprData, InductiveVal, Level, Name,
    RecursorRule, RecursorVal, ReducibilityHints, TheoremVal,
  };

  use super::{
    encoding_closure, encoding_set, mk_level_imax_prime, read_row_fix, row_lhs,
    row_members, row_name, row_of, row_prereqs, row_side, rows_of, sort_of,
    sort_of_aux, src_copy, src_name,
  };
  use crate::compile::pass3::clique::basic::{
    Decl, Local, TState, bvar, const_occurrences, dotted, is_bvar, mentions,
    mk_app_n, rename_consts, sort0,
  };
  use crate::compile::pass3::clique::plan::{CliquePlan, Encoding};
  use crate::compile::pass3::clique::plan_clique::tests::wf_transported;
  use crate::compile::pass3::clique::transport::tests::{c, lam, one, pi};
  use crate::compile::pass3::expr::nat;

  fn cval(n: &str, typ: Expr) -> ConstantVal {
    ConstantVal { name: dotted(n), level_params: vec![], typ }
  }

  fn axiom(n: &str, typ: Expr) -> ConstantInfo {
    ConstantInfo::AxiomInfo(AxiomVal { cnst: cval(n, typ), is_unsafe: false })
  }

  fn type0() -> Expr {
    Expr::sort(one())
  }

  /// The library types the hand-built clique's statements mention.
  fn types(n: &Name) -> Option<ConstantInfo> {
    ["Nat", "Int"]
      .into_iter()
      .find(|s| *n == dotted(s))
      .map(|s| axiom(s, type0()))
  }

  fn set(xs: &[&str]) -> FxHashSet<Name> {
    xs.iter().map(|x| dotted(x)).collect()
  }

  #[test]
  fn names_go_through_the_reserved_component() {
    let n = dotted("a.b");
    assert_eq!(src_name(&n).pretty(), "a.b._ix.src");
    assert_eq!(row_name(&n).pretty(), "a.b._ix.row");
    let ix = Name::str(n.clone(), "_ix".to_string());
    assert_eq!(src_name(&n), Name::str(ix.clone(), "src".to_string()));
    assert_eq!(row_name(&n), Name::str(ix, "row".to_string()));
    // a numeric component stays one
    let m = Name::num(dotted("f"), nat(1));
    assert_eq!(src_name(&m).pretty(), "f.1._ix.src");
    let pre = row_prereqs();
    assert_eq!(pre.len(), 18);
    assert_eq!(pre.first(), Some(&dotted("Eq")));
    assert_eq!(pre.last(), Some(&dotted("Nat.lt_wfRel")));
  }

  #[test]
  fn copies_rename_the_set_only() {
    let enc = set(&["P", "P.q"]);
    let ty = Expr::app(c("T"), c("P.q"));
    let value = Expr::app(c("P"), Expr::app(c("Q"), c("P.q")));
    let lp = vec![dotted("u")];
    let defn = ConstantInfo::DefnInfo(DefinitionVal {
      cnst: ConstantVal {
        name: dotted("P"),
        level_params: lp.clone(),
        typ: ty,
      },
      value,
      hints: ReducibilityHints::Regular(3),
      safety: DefinitionSafety::Partial,
      all: vec![dotted("P"), dotted("R")],
    });
    let ConstantInfo::DefnInfo(v) = src_copy(&enc, &defn) else {
      panic!("a definition")
    };
    assert_eq!(v.cnst.name.pretty(), "P._ix.src");
    assert_eq!(v.cnst.level_params, lp);
    assert_eq!(v.cnst.typ, Expr::app(c("T"), c("P.q._ix.src")));
    assert_eq!(
      v.value,
      Expr::app(c("P._ix.src"), Expr::app(c("Q"), c("P.q._ix.src")))
    );
    assert_eq!(v.all, vec![dotted("P._ix.src"), dotted("R")]);
    assert_eq!(v.hints, ReducibilityHints::Regular(3));
    assert_eq!(v.safety, DefinitionSafety::Partial);
    // a theorem; the left-hand side is the same renaming
    let thm = ConstantInfo::ThmInfo(TheoremVal {
      cnst: cval("P.q", sort0()),
      value: c("P"),
      all: vec![dotted("P.q")],
    });
    let ConstantInfo::ThmInfo(v) = src_copy(&enc, &thm) else {
      panic!("a theorem")
    };
    assert_eq!(
      (v.cnst.name.pretty(), v.value),
      ("P.q._ix.src".into(), c("P._ix.src"))
    );
    assert_eq!(v.all, vec![dotted("P.q._ix.src")]);
    assert_eq!(
      row_lhs(&enc, &Expr::app(c("P"), c("Z"))),
      Expr::app(c("P._ix.src"), c("Z"))
    );
    // an inductive's block and constructors, a constructor's inductive, a
    // recursor's rules
    let ind = ConstantInfo::InductInfo(InductiveVal {
      cnst: cval("P", sort0()),
      num_params: nat(0),
      num_indices: nat(0),
      all: vec![dotted("P")],
      ctors: vec![dotted("P.q"), dotted("P.r")],
      num_nested: nat(0),
      is_rec: false,
      is_unsafe: false,
      is_reflexive: false,
    });
    let ConstantInfo::InductInfo(v) = src_copy(&enc, &ind) else {
      panic!("an inductive")
    };
    assert_eq!(v.all, vec![dotted("P._ix.src")]);
    assert_eq!(v.ctors, vec![dotted("P.q._ix.src"), dotted("P.r")]);
    let ctor = ConstantInfo::CtorInfo(ConstructorVal {
      cnst: cval("P.q", c("P")),
      induct: dotted("P"),
      cidx: nat(0),
      num_params: nat(0),
      num_fields: nat(0),
      is_unsafe: false,
    });
    let ConstantInfo::CtorInfo(v) = src_copy(&enc, &ctor) else {
      panic!("a constructor")
    };
    assert_eq!((v.cnst.typ, v.induct), (c("P._ix.src"), dotted("P._ix.src")));
    let rec = ConstantInfo::RecInfo(RecursorVal {
      cnst: cval("P.rec", sort0()),
      all: vec![dotted("P")],
      num_params: nat(0),
      num_indices: nat(0),
      num_motives: nat(1),
      num_minors: nat(1),
      rules: vec![RecursorRule {
        ctor: dotted("P.q"),
        n_fields: nat(0),
        rhs: c("P.q"),
      }],
      k: false,
      is_unsafe: false,
    });
    let ConstantInfo::RecInfo(v) = src_copy(&enc, &rec) else {
      panic!("a recursor")
    };
    assert_eq!(v.cnst.name.pretty(), "P.rec._ix.src");
    assert_eq!(v.all, vec![dotted("P._ix.src")]);
    let Some(r) = v.rules.first() else { panic!("a rule") };
    assert_eq!(
      (r.ctor.clone(), r.rhs.clone()),
      (dotted("P.q._ix.src"), c("P.q._ix.src"))
    );
  }

  #[test]
  fn sorts_of_declared_types() {
    let u = Level::param(dotted("u"));
    let list_ty = pi(
      "α",
      Expr::sort(Level::succ(u.clone())),
      Expr::sort(Level::succ(u.clone())),
    );
    let fam = ConstantInfo::DefnInfo(DefinitionVal {
      cnst: cval("Fam", Expr::sort(Level::succ(one()))),
      value: pi("n", c("Nat"), type0()),
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![dotted("Fam")],
    });
    let list = ConstantInfo::AxiomInfo(AxiomVal {
      cnst: ConstantVal {
        name: dotted("List"),
        level_params: vec![dotted("u")],
        typ: list_ty,
      },
      is_unsafe: false,
    });
    let lookup = |n: &Name| {
      types(n)
        .or_else(|| (*n == dotted("Fam")).then(|| fam.clone()))
        .or_else(|| (*n == dotted("List")).then(|| list.clone()))
        .or_else(|| (*n == dotted("fam")).then(|| axiom("fam", c("Fam"))))
    };
    // `Sort u : Sort (succ u)`
    assert_eq!(
      sort_of(&lookup, &[], &Expr::sort(u.clone())),
      Some(Level::succ(u.clone()))
    );
    // `Nat → Nat : Type` (Lean's simplifying `imax`)
    assert_eq!(
      sort_of(&lookup, &[], &pi("n", c("Nat"), c("Nat"))),
      Some(one())
    );
    // `∀ (α : Sort u), α : Sort (imax (succ u) u)`, the body under a free
    // variable of `Sort u`
    let poly = pi("α", Expr::sort(u.clone()), bvar(0));
    assert_eq!(
      sort_of(&lookup, &[], &poly),
      Some(Level::imax(Level::succ(u.clone()), u.clone()))
    );
    assert_eq!(mk_level_imax_prime(&u, &Level::zero()), Level::zero());
    assert_eq!(mk_level_imax_prime(&Level::zero(), &u), u);
    assert_eq!(mk_level_imax_prime(&u, &u), u);
    // an application: the head's type at its levels, the arguments peeled
    let list_nat =
      Expr::app(Expr::cnst(dotted("List"), vec![Level::zero()]), c("Nat"));
    assert_eq!(sort_of(&lookup, &[], &list_nat), Some(one()));
    // a head type that is a `∀` only after δ
    assert_eq!(
      sort_of(&lookup, &[], &Expr::app(c("fam"), c("z"))),
      Some(one())
    );
    // a free variable of the context
    let t = Local {
      fvar: dotted("t"),
      user_name: dotted("t"),
      typ: Expr::sort(u.clone()),
      bi: BinderInfo::Default,
    };
    assert_eq!(
      sort_of(&lookup, slice::from_ref(&t), &t.expr()),
      Some(u.clone())
    );
    // fail-closed: a λ, an unknown head, a level mismatch, an exhausted bound
    assert_eq!(sort_of(&lookup, &[], &lam("x", c("Nat"), c("Nat"))), None);
    assert_eq!(sort_of(&lookup, &[], &c("Nope")), None);
    assert_eq!(sort_of(&lookup, &[], &Expr::app(c("List"), c("Nat"))), None);
    assert_eq!(sort_of_aux(&lookup, 0, &mut vec![], &sort0()), None);
    assert_eq!(
      sort_of_aux(&lookup, 1, &mut vec![], &pi("n", c("Nat"), c("Nat"))),
      None
    );
    assert_eq!(
      sort_of_aux(&lookup, 2, &mut vec![], &pi("n", c("Nat"), c("Nat"))),
      Some(one())
    );
  }

  /// The hand-built well-founded clique's transported presentation, its
  /// plan, and its input with the library types.
  fn wf_plan() -> (impl Fn(&Name) -> Option<ConstantInfo>, CliquePlan) {
    let ((env, _, _), plan, _) = wf_transported();
    let lookup =
      move |n: &Name| env.get(n).map(|e| e.cloned()).or_else(|| types(n));
    (lookup, plan)
  }

  #[test]
  fn rows_of_a_well_founded_plan() {
    let (lookup, plan) = wf_plan();
    let (Some(all0), Some(all1)) = (plan.all.first(), plan.all.get(1)) else {
      panic!("two members")
    };
    let packed = Name::str(all0.clone(), "_mutual".to_string());
    let proof = Name::str(packed.clone(), "_proof_1".to_string());
    let canon = dotted(&format!("{}._ix._mutual", all1.pretty()));
    let enc = encoding_set(&lookup, &plan);
    assert_eq!(enc, Ok([packed.clone(), proof.clone()].into_iter().collect()));
    assert_eq!(row_members(&plan), plan.all);
    let Ok((copies, rows)) = rows_of(&lookup, &plan) else { panic!("rows") };
    // the copies, in pretty-name order: each Lean record renamed
    let names: Vec<Name> =
      copies.iter().map(|ci| ci.get_name().clone()).collect();
    assert_eq!(names, vec![src_name(&packed), src_name(&proof)]);
    let Some(ConstantInfo::DefnInfo(p)) = lookup(&packed) else {
      panic!("Lean's packed function")
    };
    let Some(ConstantInfo::DefnInfo(cp)) = copies.first() else {
      panic!("a definition")
    };
    let Ok(enc) = enc else { panic!("the set") };
    let ren = |e: &Expr| rename_consts(&|n| super::src_rename(&enc, n), e);
    assert_eq!(
      (cp.value.clone(), cp.cnst.typ.clone()),
      (ren(&p.value), ren(&p.cnst.typ))
    );
    assert!(mentions(&src_name(&proof), &cp.value));
    // the rows: `f._ix.row : @Eq.{1} T lhs f`, by row name
    let mut members = plan.all.clone();
    members.sort_by_cached_key(Name::pretty);
    assert_eq!(rows.len(), 2);
    for (f, row) in members.iter().zip(&rows) {
      let ConstantInfo::ThmInfo(v) = row else { panic!("a theorem") };
      assert_eq!(v.cnst.name, row_name(f));
      assert!(v.cnst.level_params.is_empty());
      assert_eq!(v.all, vec![row_name(f)]);
      let Some(ci) = lookup(f) else { panic!("a member") };
      let Some(lean) = ci.get_value() else { panic!("a value") };
      let want = mk_app_n(
        Expr::cnst(dotted("Eq"), vec![one()]),
        &[ci.get_type().clone(), ren(lean), Expr::cnst(f.clone(), vec![])],
      );
      assert_eq!(v.cnst.typ, want);
      // a proof about the copies and the canonical constants: no Lean
      // encoding constant
      assert!(!mentions(&packed, &v.value) && !mentions(&proof, &v.value));
      assert!(
        mentions(&src_name(&packed), &v.value) && mentions(&canon, &v.value)
      );
      let heads = const_occurrences(&|_| true, &v.value);
      assert_eq!(heads.first(), Some(&dotted("funext")));
      for n in [
        "WellFounded.induction",
        "WellFounded.Nat.fix_eq",
        "InvImage.wf",
        "congrArg",
        "Eq.trans",
        "Eq.symm",
        "Eq.refl",
        "PSum.casesOn",
      ] {
        assert!(mentions(&dotted(n), &v.value), "{n}");
      }
      // one member's row alone is the same record
      let Ok(Some(ConstantInfo::ThmInfo(w))) = row_of(&lookup, &plan, f) else {
        panic!("a row")
      };
      assert_eq!((w.cnst, w.value), (v.cnst.clone(), v.value.clone()));
    }
  }

  #[test]
  fn refusals() {
    let (lookup, plan) = wf_plan();
    let (Some(all0), Some(all1)) =
      (plan.all.first().cloned(), plan.all.get(1).cloned())
    else {
      panic!("two members")
    };
    let packed = Name::str(all0.clone(), "_mutual".to_string());
    let proof = Name::str(packed.clone(), "_proof_1".to_string());
    let f = all0.pretty();
    let err = |p: &CliquePlan, m: &Name| {
      row_of(&lookup, p, m).map(|r| r.map(|ci| ci.get_name().clone()))
    };
    // another encoding: no row
    let other = CliquePlan { encoding: Encoding::Structural, ..plan.clone() };
    assert_eq!(err(&other, &all0), Ok(None));
    assert!(
      matches!(rows_of(&lookup, &other), Ok((c, r)) if c.is_empty() && r.is_empty())
    );
    // not a member, an alias, not transported
    assert_eq!(
      err(&plan, &dotted("h")),
      Err("row: h is not a member of the clique".to_string())
    );
    let alias = CliquePlan {
      aliases: vec![(all0.clone(), all1.clone())],
      ..plan.clone()
    };
    assert_eq!(
      err(&alias, &all0),
      Err(format!(
        "row: {f} is an alias (its value is its representative's, at another summand)"
      ))
    );
    let mut untransported = plan.clone();
    untransported.members.remove(&all0);
    assert_eq!(
      err(&untransported, &all0),
      Err(format!("row: {f} is not a transported member"))
    );
    // the injections against σ
    let id = CliquePlan { sigma: vec![0, 1], ..plan.clone() };
    assert_eq!(
      err(&id, &all0),
      Err("row: the members' injections do not follow σ".to_string())
    );
    // no sort: the library types missing
    let ((env, _, _), _, _) = wf_transported();
    let bare = |n: &Name| env.get(n).map(|e| e.cloned());
    assert_eq!(
      row_of(&bare, &plan, &all0).map(|_| ()),
      Err(format!("row: no sort for the type of {f}"))
    );
    // an encoding constant missing from the input, or not a definition
    let missing = |n: &Name| if *n == proof { None } else { lookup(n) };
    let want = format!(
      "row: the encoding constant {} is not in the input",
      proof.pretty()
    );
    assert_eq!(rows_of(&missing, &plan).map(|_| ()), Err(want));
    let ax = |n: &Name| {
      if *n == proof { Some(axiom("x", sort0())) } else { lookup(n) }
    };
    let want = format!(
      "row: the encoding constant {} is not a definition or a theorem",
      proof.pretty()
    );
    assert_eq!(rows_of(&ax, &plan).map(|_| ()), Err(want));
    // a row mentioning an encoding constant without a copy (the canonical
    // functional made to reference one)
    let stray = Name::str(packed.clone(), "_proof_7".to_string());
    let mut leaky = plan.clone();
    let Some((canon, _)) = leaky.canon.first_mut() else {
      panic!("a packed function")
    };
    let canon_proof = Name::str(canon.name.clone(), "_proof_1".to_string());
    canon.value = rename_consts(
      &|n| (*n == canon_proof).then(|| stray.clone()),
      &canon.value,
    );
    assert!(mentions(&stray, &canon.value));
    let want = format!(
      "row: the row of {f} references the encoding constant {}, which has no copy",
      stray.pretty()
    );
    assert_eq!(err(&leaky, &all0), Err(want));
    // the closure's bound
    let stack = vec![packed.clone()];
    assert_eq!(
      encoding_closure(
        &lookup,
        &|_| true,
        0,
        stack.clone(),
        FxHashSet::default()
      ),
      Err("row: the encoding set exceeds its bound".to_string())
    );
    assert_eq!(
      encoding_closure(&lookup, &|_| false, 1, stack, FxHashSet::default()),
      Ok([packed.clone()].into_iter().collect())
    );
    // the sides' shapes
    let none = |_: &Name| -> Option<Decl> { None };
    let mut tm = TState::default();
    assert_eq!(
      row_side(&mut tm, &none, 2, &c("x"), "Lean's value").map(|_| ()),
      Err(
        "row: Lean's value is not an application of the packed function"
          .to_string()
      )
    );
    assert_eq!(
      row_side(&mut tm, &none, 2, &Expr::app(c("P"), c("x")), "Lean's value")
        .map(|_| ()),
      Err(
        "row: Lean's value: P is not the clique's packed function".to_string()
      )
    );
    assert_eq!(
      read_row_fix(&c("x")).map(|_| ()),
      Err("row: the packed function's value is not a `WellFounded.fix` or `WellFounded.Nat.fix` root".to_string())
    );
  }

  /// Every recursive call `r a h` (the recursion binder `bvar 0` applied)
  /// replaced by `thread r`: the binder passed on whole.
  fn thread(e: &Expr) -> Expr {
    match e.as_data() {
      ExprData::App(f, a, _) => {
        if let ExprData::App(g, _, _) = f.as_data()
          && is_bvar(g, 0)
        {
          return Expr::app(c("thread"), bvar(0));
        }
        Expr::app(thread(f), thread(a))
      },
      ExprData::Lam(n, t, b, bi, _) => {
        Expr::lam(n.clone(), thread(t), thread(b), bi.clone())
      },
      ExprData::ForallE(n, t, b, bi, _) => {
        Expr::all(n.clone(), thread(t), thread(b), bi.clone())
      },
      _ => e.clone(),
    }
  }

  #[test]
  fn a_threaded_recursion_binder_is_refused() {
    let (lookup, plan) = wf_plan();
    let Some(all0) = plan.all.first().cloned() else { panic!("a member") };
    let packed = Name::str(all0.clone(), "_mutual".to_string());
    // Lean's packed function with its leaves passing the recursion binder
    // on (a definition clique: the guard applies)
    let threaded = |n: &Name| match lookup(n) {
      Some(ConstantInfo::DefnInfo(v)) if *n == packed => {
        Some(ConstantInfo::DefnInfo(DefinitionVal {
          value: thread(&v.value),
          ..v
        }))
      },
      ci => ci,
    };
    let Some(ConstantInfo::DefnInfo(v)) = threaded(&packed) else {
      panic!("a definition")
    };
    assert!(mentions(&dotted("thread"), &v.value));
    assert!(row_of(&lookup, &plan, &all0).is_ok());
    assert_eq!(
      row_of(&threaded, &plan, &all0).map(|_| ()),
      Err(
        "row: a body threads the recursion binder (argument pushing): one \
         unfolding does not give the transported body"
          .to_string()
      )
    );
  }
}
