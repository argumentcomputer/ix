//! The transport of a structural clique (a port of
//! `Ix/Compile/Pass/Clique/Structural.lean`). Structural recursion has no
//! packed function to rename and no measure: the transport re-associates the
//! packings and reorders telescopes.
//!
//! Lean's encoding (`Elab/PreDefinition/Structural`, Lean 4.34.1), as the
//! transport sees it:
//!
//! * the functions are grouped by the type former of their recursive
//!   argument (`Positions.groupAndSort`); the groups follow the inductive's
//!   `all` order (nested auxiliaries included), and **within a group the
//!   functions are in clique order**, the only place the clique order enters;
//! * per type former, the packed motive `λ is x. R₀ ×' (R₁ ×' …)` (`PProd`,
//!   or `And` for propositions; the motive itself for a singleton group) is
//!   passed to `T.brecOn`/`T.below` (`PProdN.packLambdas`);
//! * each function's functional `f._f : ∀ fixed is x (f : T.below … x) …`,
//!   whose body reaches a recursive call through a path into the `below`
//!   dictionary (`searchPProd`): a prefix that walks the inductive's `below`
//!   structure, then the position inside the packed motive;
//! * the members `f := λ ys. (T.brecOn ps motives is x F₁ … F_K).2.1 rest`,
//!   `F_k = λ is x f. ⟨g₀._f fixed is x f, …⟩` the packed functionals;
//! * for an inductive predicate (`IndPred`), `let funType_i := …` in clique
//!   order around the body, the functionals inline, and "below" matchers
//!   (`IndPredBelow.mkBelowMatcher`) closing over the `funType` lets in
//!   clique order (their first parameters when they close over nothing
//!   else);
//! * the fixed parameters in the first function's order (in every `_f`).
//!
//! `Φ_σ` re-associates, per group `k` (with `σ_k`, the restriction of `σ`):
//! the packed motives at the motive positions of every `below`/`brecOn`
//! application of the block, the packed functionals at `brecOn`'s functional
//! positions, the members' projections out of `brecOn`, and the motive-part
//! of every path into a `below` dictionary, found, as Lean finds it, by
//! reducing the dictionary's type with canaries in place of the packed
//! motives ([`whnf`]); a path through a reflexive field `f : A → T` applies
//! the field's entry to the argument in the middle of the path, and the walk
//! instantiates the entry's `∀` there, as `toBelowAux` does. The
//! `let funType` telescope is reordered, and with it the first `n`
//! parameters of every below matcher, in its declaration and at its
//! applications alike; the `_f` telescopes too. Nothing else moves: the
//! prefix of a path, the bodies, the matchers' alternatives, the recursive
//! argument's position.
//!
//! **The `below`/`brecOn` family is authenticated, never found by name.**
//! The block is the inductive of the members' `brecOn` head; it must be
//! recursive (`isRec`: Lean generates the family only then).
//! [`family_candidates`] lists every name the transport may treat as the
//! block's family: per motive position its `below` and `brecOn` (`T.below`,
//! `T.brecOn` for `T` in `all`, then `all₀.below_k`, `all₀.brecOn_k` for the
//! nested auxiliaries), and the `.go`/`.eq` the input has under the `brecOn`
//! names. The caller keeps the ones
//! `crate::compile::aux_gen::source_family::filter_heads` authenticates (each
//! equal to what Lean's generators build from the block's source recursors)
//! and passes that set to [`struct_layout`] (`family`); this module does not
//! call the authentication (it needs the compiler's environment).
//! [`block_of`] refuses a block one of whose `below`/`brecOn` names is not
//! in the set, and an encoding constant of the family
//! ([`StructLayout::is_encoding_const`]) is a name with a prefix in the set
//! (`T.brecOn.go`, the constructors and `casesOn` of an inductive predicate's
//! `T.below`).
//!
//! **A matcher is recognised by its declaration, not by its name.** A
//! `match_*` name is only a pre-filter: an auxiliary is a below matcher
//! ([`StructLayout::matchers`]) only when its declaration has the shape the
//! transport relies on ([`matcher_shape`]). Any other auxiliary, whatever
//! its name, is an ordinary constant (in particular, the ownership rules
//! apply to it as to any constant).
//!
//! Unsupported shapes are outside the grammar and leave the clique in Lean's
//! form (the fallback is the baseline): a dictionary passed whole to a
//! helper other than an eliminator, a path the walk cannot follow, a
//! projection of a `brecOn` result that is not a full path, an
//! unauthenticated family, or a carried equation lemma of a repacked group
//! that cannot be regenerated. [`super::structural_eq`] builds an unfolding
//! proof from the unchanged statement and the actual `casesOn`; it does not
//! transport Lean's old packed proof.
//!
//! # Ownership of the `below` dictionaries
//!
//! A path into a `below` dictionary is re-associated only when the
//! dictionary is the recursion's own, decided by where the variable is bound
//! and never by its type:
//!
//! * the dictionary binder of a functional `f._f` (the binder after the
//!   indices and the major, [`StructLayout::f_depth`]), and the dictionary
//!   binder of each packed functional handed to the members' `brecOn`;
//! * the binders that receive an owned dictionary through a matcher or a
//!   `casesOn` (`MatcherApp.addArg`): the arguments past the eliminator's
//!   declared arity are passed to the trailing binders of every alternative
//!   (a parameter whose type concludes in an earlier parameter, the motive),
//!   after that alternative's own fields.
//!
//! An owned dictionary passed to a below matcher must sit at one of its
//! discriminants whose declared type is a `below` of the block (the
//! dictionary the below matcher eliminates) or past its declared arity (an
//! extra argument, which the alternatives' trailing binders receive and the
//! binder rules check); anywhere else (a `funType` parameter, the motive, an
//! alternative) is a refusal.
//!
//! A user's binder whose type is a `below` of the block, a path into a
//! `below` value that is not owned, an owned dictionary passed whole
//! anywhere else, and a `brecOn` application of the block outside a
//! member's root are outside the grammar: the clique stays in Lean's form.
//! Lean's own encoding never produces them; user code can (a user
//! `Nat.brecOn` whose motive has the packing's shape, a user `below` binder
//! read through primitive projections). A theorem clique is exempt: its
//! terms are proofs, so a wrong path can make the kernel reject but cannot
//! change a value.
//!
//! Every refusal is an error with the Lean text; no index is unchecked.

use std::ops::ControlFlow;
use std::slice;

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::env::{
  ConstantInfo, Expr, ExprData, InductiveVal, Name, NameData,
};

use super::basic::{
  Binder, ConstOf, Decl, Hash, R, TState, bvar, bvar_idx, cnst, const_app,
  eq_sorted, extract, fold_consts, forall_arity, fvar, instantiate_rev,
  inv_perm, is_perm, lam_arity, lift_loose, lower_opt, mentions, mk_app_n,
  mk_foralls, mk_lams, mk_str, n_and, name_to_string, no_dups, peel_foralls,
  peel_lams, permute, proj, tm_idx,
};
use super::bounds::{TRANSPORT_FUEL, WHNF_FUEL};
use super::packing::{
  PackKind, Spine, apply_projs, decode_node, decode_spine, decode_tuple,
  mk_tuple,
};
use super::structural_eq::{eq_def_name_eq, regenerate_structural_eq};
use super::telescope::{
  id_perm, reorder, whnf, with_reordered_binders, with_reordered_binders2,
};
use super::wf::{Transported, sort_idx_by_key, spine_type_m};
use crate::compile::pass3::expr::{
  ExactMemo, get_app_fn_args, key, nat_usize, strip_mdata,
};

/// A `below` or `brecOn` constant of the block (`BlockAux`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct BlockAux {
  /// the motive position (type former, nested auxiliaries after `all`)
  pub pos: usize,
  pub is_brec_on: bool,
}

/// The functions recursing on one type former (`Group`).
#[derive(Clone, Debug)]
pub struct Group {
  /// Lean member indices, in Lean's group order
  pub members: Vec<usize>,
  /// the motive's binders (indices and major)
  pub arity: usize,
  /// Lean's packed motive (when the group has two or more members), its
  /// leaves under `arity` binders
  pub spine: Spine,
  /// Lean group position ↦ canonical group position
  pub perm: Vec<usize>,
}

impl Group {
  /// `Group.size`.
  pub fn size(&self) -> usize {
    self.members.len()
  }

  /// `Group.canonSpine`: the canonical packed-motive spine (for the
  /// projections' structure names); `None` when `perm` is not a permutation
  /// of the leaves.
  pub fn canon_spine(&self) -> Option<Spine> {
    self.spine.permute(&self.perm)
  }
}

/// The spine of a group without a packed motive (Lean's `default`).
fn empty_spine() -> Spine {
  Spine { kind: PackKind::Psum, leaves: Vec::new(), lvls: Vec::new() }
}

// ---------------------------------------------------------------------------
// Eliminators and matchers
// ---------------------------------------------------------------------------

/// The shape of an eliminator (a matcher or a `casesOn`) that receives an
/// owned dictionary past its declared arity (`MatcherApp.addArg`), read off
/// its declaration (`ElimShape`): the declared arity, for each declared
/// parameter its number of fields when it is an alternative (a parameter
/// whose type concludes in an earlier parameter), and the motives (the
/// parameters the alternatives conclude in) with their own arities.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ElimShape {
  pub arity: usize,
  pub alts: Vec<Option<usize>>,
  pub motives: Vec<(usize, usize)>,
}

/// `elimShapeOf?`: `None` when the constant is not in the input.
pub fn elim_shape_of(const_of: ConstOf<'_>, c: &Name) -> Option<ElimShape> {
  let ci = const_of(c)?;
  let ty = ci.get_type();
  let ar = forall_arity(ty);
  let (ps, _) = peel_foralls(ar, ty);
  let mut alts = Vec::with_capacity(ps.len());
  let mut motives: Vec<(usize, usize)> = Vec::new();
  for (k, (_, pt, _)) in ps.iter().enumerate() {
    let fc = forall_arity(pt);
    let (_, concl) = peel_foralls(fc, pt);
    match bvar_idx(&get_app_fn_args(&strip_mdata(&concl)).0) {
      Some(i) if i >= fc && i - fc < k => {
        alts.push(Some(fc));
        let mk = k - 1 - (i - fc);
        if !motives.iter().any(|m| m.0 == mk) {
          let (_, mt, _) = ps.get(mk)?;
          motives.push((mk, forall_arity(mt)));
        }
      },
      _ => alts.push(None),
    }
  }
  Some(ElimShape { arity: ar, alts, motives })
}

/// The shape of a below matcher, read off its declared type
/// ([`matcher_shape`]), in argument positions (a `let` of the telescope is
/// not an argument): the declared arity, the motive's position, the number
/// of discriminants, and each argument's declared domain (`MatcherShape`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MatcherShape {
  pub arity: usize,
  pub motive: usize,
  pub discrs: usize,
  pub domains: Vec<Expr>,
}

/// `isCasesOn`: `c` is `T.casesOn` for an inductive `T` of the input.
pub fn is_cases_on(const_of: ConstOf<'_>, c: &Name) -> bool {
  match c.as_data() {
    NameData::Str(p, s, _) if s == "casesOn" => {
      matches!(const_of(p), Some(ConstantInfo::InductInfo(_)))
    },
    _ => false,
  }
}

/// `isRecursorDef`: `c` is a definition of the input whose value, after its
/// leading `λ`s, applies a recursor of the input: Lean's sparse `casesOn`
/// (`mkSparseCasesOn`), which its match compiler names after the declaration
/// that needed it, not after the inductive.
pub fn is_recursor_def(const_of: ConstOf<'_>, c: &Name) -> bool {
  let Some(ConstantInfo::DefnInfo(v)) = const_of(c) else { return false };
  let (_, body) = peel_lams(lam_arity(&v.value), &v.value);
  const_app(&body).is_some_and(|(r, _, _)| {
    matches!(const_of(&r), Some(ConstantInfo::RecInfo(_)))
  })
}

/// `isMatcherName`: the pre-filter of the matchers, the last component
/// starts with `match_`. It decides nothing alone ([`matcher_shape`]).
pub fn is_matcher_name(n: &Name) -> bool {
  matches!(n.as_data(), NameData::Str(_, s, _) if s.starts_with("match_"))
}

/// One binder of [`binders_through_lets`]: its domain, with its value for a
/// `let`.
pub type LetBinder = (Expr, Option<Expr>);

/// `bindersThroughLets`: the binders of a declaration's type (`∀`,
/// `lam = false`) or value (`λ`, `lam = true`), through `let`s and `mdata`:
/// each binder's domain, with its value for a `let`; and the body.
pub fn binders_through_lets(lam: bool, e: &Expr) -> (Vec<LetBinder>, Expr) {
  let mut acc = Vec::new();
  let mut cur = e.clone();
  loop {
    let next = match cur.as_data() {
      ExprData::ForallE(_, t, b, _, _) if !lam => {
        acc.push((t.clone(), None));
        b.clone()
      },
      ExprData::Lam(_, t, b, _, _) if lam => {
        acc.push((t.clone(), None));
        b.clone()
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        acc.push((t.clone(), Some(v.clone())));
        b.clone()
      },
      ExprData::Mdata(_, x, _) => x.clone(),
      _ => return (acc, cur),
    };
    cur = next;
  }
}

/// Lean's `==` on two telescopes of [`binders_through_lets`]: the same
/// length, each domain and `let` value equal.
fn let_binders_eq(a: &[LetBinder], b: &[LetBinder]) -> bool {
  a.len() == b.len()
    && a.iter().zip(b).all(|((t, v), (u, w))| {
      t.same_raw(u)
        && match (v, w) {
          (None, None) => true,
          (Some(v), Some(w)) => v.same_raw(w),
          _ => false,
        }
    })
}

/// `matcherShape?`: the auxiliary `d` is a below matcher whose first
/// `num_permuted` arguments the transport may permute, recognised by its
/// declaration (the one in the input, `const_of(&d.name)`, which `d` must
/// be), never by its name. It checks exactly:
///
/// * the declaration is a definition, `d` is it (same type and value), and
///   its value does not mention its own name (not recursive);
/// * its type is a telescope `(p₁ … p_m) (motive) (d₁ … d_k) (h₁ … h_r)`
///   ending in `motive d₁ … d_k`, where the parameters `p` may be
///   interleaved with `let`s and every later binder is a `∀`: the conclusion
///   is a binder (the motive) applied to exactly the `k` binders that follow
///   it, in order (the discriminants); the motive's own type is a telescope
///   of `k` binders ending in a sort; every binder after the discriminants
///   is an alternative, whose type concludes in the motive;
/// * the arguments the transport permutes are parameters before the motive:
///   `1 ≤ num_permuted ≤ m` (`m` counts the `∀` parameters, not the
///   `let`s);
/// * its value is the same telescope (a `λ` with the same domain for each
///   `∀`, the same `let`s), whose body (up to `mdata`) is an eliminator
///   application: `T.casesOn` of an inductive `T` of the input, a
///   recursor-based definition of the input ([`is_recursor_def`]), or a
///   matcher already accepted (`accepted`), whose declaration
///   [`elim_shape_of`] reads, applied to at least its declared arity.
///
/// Lean's below matchers (`IndPredBelow.mkBelowMatcher`, through
/// `Match.mkMatcher`) have this shape. The transport permutes the first
/// `num_permuted` arguments, which are the `funType` parameters exactly when
/// the matcher closes over nothing else.
pub fn matcher_shape(
  const_of: ConstOf<'_>,
  accepted: &dyn Fn(&Name) -> bool,
  num_permuted: usize,
  d: &Decl,
) -> Option<MatcherShape> {
  let Some(ConstantInfo::DefnInfo(v)) = const_of(&d.name) else {
    return None;
  };
  if !(!d.is_thm && v.cnst.typ.same_raw(&d.typ) && v.value.same_raw(&d.value)) {
    return None;
  }
  if mentions(&d.name, &v.value) {
    return None;
  }
  let (ps, concl) = binders_through_lets(false, &v.cnst.typ);
  let n = ps.len();
  let (hd, ds) = get_app_fn_args(&strip_mdata(&concl));
  let mv = bvar_idx(&strip_mdata(&hd))?;
  if mv >= n {
    return None;
  }
  // the motive is binder `mt`, discriminant `j` binder `mt + 1 + j`
  let mt = n - 1 - mv;
  let k = ds.len();
  if !(mt + k < n && ps.iter().skip(mt).all(|x| x.1.is_none())) {
    return None;
  }
  let discriminants = ds.iter().enumerate().all(|(j, x)| {
    bvar_idx(&strip_mdata(x))
      == Some(n.saturating_sub(2).saturating_sub(mt).saturating_sub(j))
  });
  if !discriminants {
    return None;
  }
  let (mty, _) = ps.get(mt)?;
  let (mbs, mres) = peel_foralls(k, mty);
  if !(mbs.len() == k
    && matches!(strip_mdata(&mres).as_data(), ExprData::Sort(..)))
  {
    return None;
  }
  // every later binder `q` concludes in the motive (`bvar (q - 1 - mt)` in
  // its context, under its own `fc` binders)
  let alternatives =
    ps.iter().enumerate().skip(mt + k + 1).all(|(q, (pt, _))| {
      let fc = forall_arity(pt);
      let (_, c) = peel_foralls(fc, pt);
      bvar_idx(&get_app_fn_args(&strip_mdata(&c)).0)
        == Some(q.saturating_sub(1).saturating_sub(mt).saturating_add(fc))
    });
  if !alternatives {
    return None;
  }
  let num_lets = ps.iter().filter(|x| x.1.is_some()).count();
  let motive = mt.saturating_sub(num_lets);
  if !(1..=motive).contains(&num_permuted) {
    return None;
  }
  let (vs, body) = binders_through_lets(true, &v.value);
  if !let_binders_eq(&vs, &ps) {
    return None;
  }
  let (h, _, bargs) = const_app(&body)?;
  if !(accepted(&h)
    || is_cases_on(const_of, &h)
    || is_recursor_def(const_of, &h))
  {
    return None;
  }
  let sh = elim_shape_of(const_of, &h)?;
  if sh.arity > bargs.len() {
    return None;
  }
  Some(MatcherShape {
    arity: n - num_lets,
    motive,
    discrs: k,
    domains: ps
      .into_iter()
      .filter_map(|(t, x)| if x.is_none() { Some(t) } else { None })
      .collect(),
  })
}

// ---------------------------------------------------------------------------
// The layout
// ---------------------------------------------------------------------------

/// What `Φ_σ` needs to know about a structural clique (`StructLayout`).
pub struct StructLayout<'a> {
  pub n: usize,
  /// Lean index ↦ canonical position
  pub sigma: Vec<usize>,
  pub const_of: ConstOf<'a>,
  pub num_params: usize,
  pub num_motives: usize,
  /// the block's `below`/`brecOn` constants
  pub aux: FxHashMap<Name, BlockAux>,
  /// the block's authenticated `below`/`brecOn` family
  /// ([`family_candidates`])
  pub family: FxHashSet<Name>,
  pub groups: Vec<Group>,
  pub f_names: FxHashSet<Name>,
  /// the functionals in the order the members' `brecOn` applications pass
  /// them (the first occurrence of each)
  pub f_list: Vec<Name>,
  pub num_fixed: usize,
  /// new fixed position `p` ↦ Lean's fixed position
  pub fixed_perm: Vec<usize>,
  /// the below matchers, with their shapes ([`matcher_shape`])
  pub matchers: FxHashMap<Name, MatcherShape>,
  /// IndPred: the number of `funType` lets (`n`), else `0`
  pub num_fun_types: usize,
  /// new position `p` ↦ Lean position (`inv_perm(sigma)`), for the
  /// `funType` telescope and the matchers' `funType` binders
  pub fun_perm: Vec<usize>,
  /// per member (Lean's order): the member's parameter (outermost `0`) at
  /// each fixed position of its functionals' applications
  pub member_fixed: Vec<Vec<usize>>,
  /// per functional `f._f`: the number of its binders after the fixed
  /// parameters (indices, major, then the `below` dictionary when the number
  /// is the arity plus one) and its group's arity
  pub f_depth: FxHashMap<Name, (usize, usize)>,
  /// enforce the ownership of the `below` dictionaries (see "Ownership" in
  /// the module documentation); off for a theorem clique, whose terms are
  /// proofs
  pub check_ownership: bool,
}

/// `underFamily`: `n` or one of its prefixes is in `family`.
pub fn under_family(family: &FxHashSet<Name>, n: &Name) -> bool {
  let mut cur = n;
  loop {
    if family.contains(cur) {
      return true;
    }
    match cur.as_data() {
      NameData::Str(p, _, _) | NameData::Num(p, _, _) => cur = p,
      NameData::Anonymous(_) => return false,
    }
  }
}

impl StructLayout<'_> {
  /// `repacks`: some type former's group packs two or more functions in an
  /// order the transport changes (`perm` is not the identity): only then
  /// does the clique have packed motives, tuples and paths to re-associate.
  pub fn repacks(&self) -> bool {
    self.groups.iter().any(|g| g.size() >= 2 && g.perm != id_perm(g.size()))
  }

  /// `elimShape?`.
  pub fn elim_shape(&self, c: &Name) -> Option<ElimShape> {
    elim_shape_of(self.const_of, c)
  }

  /// `isEncodingConst`: `c` is a constant of the recursion's encoding: a
  /// functional `f._f`, a below matcher, or a name with a prefix in the
  /// authenticated family (a `below`/`brecOn` constant of the block or a
  /// constant under one: `T.brecOn.go`, `T.brecOn.eq`, the constructors of
  /// an inductive `T.below`).
  pub fn is_encoding_const(&self, c: &Name) -> bool {
    self.f_names.contains(c)
      || self.matchers.contains_key(c)
      || under_family(&self.family, c)
  }

  /// `isBelowTy`: `ty` is a `below` of the block (by its head constant).
  pub fn is_below_ty(&self, ty: &Expr) -> bool {
    const_app(&strip_mdata(ty))
      .is_some_and(|(c, _, _)| self.aux.get(&c).is_some_and(|a| !a.is_brec_on))
  }

  /// `isBrecOnConst`: `c` is a `brecOn` constant of the block.
  pub fn is_brec_on_const(&self, c: &Name) -> bool {
    self.aux.get(c).is_some_and(|a| a.is_brec_on)
  }

  /// `brecOnCount`: the number of occurrences of the block's `brecOn`
  /// constants in `e`, counted in the unshared tree (an occurrence in a
  /// shared subterm counts once per occurrence of the subterm), memoised by
  /// the subterm. The count saturates at `usize::MAX` (only its equality to
  /// `1` is read).
  pub fn brec_on_count(&self, e: &Expr) -> usize {
    fn go(
      l: &StructLayout<'_>,
      e: &Expr,
      memo: &mut ExactMemo<(), usize>,
    ) -> usize {
      if let ExprData::Const(c, _, _) = e.as_data() {
        return usize::from(l.is_brec_on_const(c));
      }
      if let Some(r) = memo.get(e, ()) {
        return r;
      }
      let r = match e.as_data() {
        ExprData::App(f, a, _) => go(l, f, memo).saturating_add(go(l, a, memo)),
        ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
          go(l, t, memo).saturating_add(go(l, b, memo))
        },
        ExprData::LetE(_, t, v, b, _, _) => go(l, t, memo)
          .saturating_add(go(l, v, memo))
          .saturating_add(go(l, b, memo)),
        ExprData::Proj(_, _, x, _) | ExprData::Mdata(_, x, _) => go(l, x, memo),
        _ => return 0,
      };
      memo.insert(e, (), r);
      r
    }
    go(self, e, &mut ExactMemo::default())
  }

  /// `checkMatcherOwnership`: with ownership enforced, the owned arguments
  /// (`owned`, by position) of an application of the below matcher `c` of
  /// shape `sh`: each must be one of its discriminants whose declared type
  /// is a `below` of the block, or past its declared arity.
  pub fn check_matcher_ownership(
    &self,
    c: &Name,
    sh: &MatcherShape,
    owned: &[bool],
  ) -> R<()> {
    for (i, &o) in owned.iter().enumerate() {
      if !o || i >= sh.arity {
        continue;
      }
      let declared_below =
        sh.domains.get(i).is_some_and(|t| self.is_below_ty(t));
      let is_below_discr =
        sh.motive < i && i <= sh.motive + sh.discrs && declared_below;
      if !is_below_discr {
        return Err(format!(
          "grammar: a below dictionary passed to the matcher {} outside its \
           below discriminants",
          name_to_string(c)
        ));
      }
    }
    Ok(())
  }
}

/// `mentionsWhere`: `e` mentions a constant satisfying `p`.
pub fn mentions_where(p: &dyn Fn(&Name) -> bool, e: &Expr) -> bool {
  fold_consts(e, false, |_, n| {
    if p(n) { ControlFlow::Break(true) } else { ControlFlow::Continue(false) }
  })
}

// ---------------------------------------------------------------------------
// Paths
// ---------------------------------------------------------------------------

/// `projChain`: the projection chain around `e`: steps innermost first, and
/// the base.
pub fn proj_chain(e: &Expr) -> (Vec<(Name, usize)>, Expr) {
  let mut steps = Vec::new();
  let mut cur = e.clone();
  loop {
    let next = match cur.as_data() {
      ExprData::Proj(s, i, x, _) => {
        steps.push((s.clone(), nat_usize(i)));
        x.clone()
      },
      ExprData::Mdata(_, x, _) => x.clone(),
      _ => break,
    };
    cur = next;
  }
  steps.reverse();
  (steps, cur)
}

/// `pathPrefix`: a path to a component of an `n`-component product at the
/// start of `steps`: the component and the number of steps it takes
/// (`PProdN.proj`).
pub fn path_prefix(
  n: usize,
  steps: &[(Name, usize)],
) -> Option<(usize, usize)> {
  if n < 2 {
    return Some((0, 0));
  }
  let k = steps.iter().take_while(|s| s.1 == 1).count();
  if k + 1 < n {
    match steps.get(k) {
      Some(st) if st.1 == 0 => Some((k, k + 1)),
      _ => None,
    }
  } else {
    Some((n - 1, n - 1))
  }
}

/// `stepsFit`: the structure names of `steps` must be those of the spine's
/// nodes.
pub fn steps_fit(s: &Spine, idx: usize, steps: &[(Name, usize)]) -> bool {
  match s.proj_steps(idx) {
    Some(st) => st.iter().map(|x| &x.0).eq(steps.iter().map(|x| &x.0)),
    None => false,
  }
}

/// `transportPath`: re-associate the start of `steps` (a path into group
/// `g`'s packed motive) and keep the rest.
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
  let past =
    || "grammar: a path into a packed motive past its group".to_string();
  let Some(&p) = g.perm.get(idx) else { return Err(past()) };
  let Some(canon) = g.canon_spine() else {
    return Err(
      "grammar: a packed motive whose group order is not a permutation".into(),
    );
  };
  let Some(mut st) = canon.proj_steps(p) else { return Err(past()) };
  st.extend(extract(steps, len, steps.len()));
  Ok(st)
}

/// One step of a path into a `below` dictionary (`PStep`): a projection, or
/// (through a reflexive field `f : A → T`, whose dictionary entry is a
/// function) an application to an argument.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum PStep {
  Proj(Name, usize),
  App(Expr),
}

/// `pathChain`: the chain of projections and applications around `e`: steps
/// innermost first, and the base.
pub fn path_chain(e: &Expr) -> (Vec<PStep>, Expr) {
  let mut steps = Vec::new();
  let mut cur = e.clone();
  loop {
    let next = match cur.as_data() {
      ExprData::Proj(s, i, x, _) => {
        steps.push(PStep::Proj(s.clone(), nat_usize(i)));
        x.clone()
      },
      ExprData::App(f, a, _) => {
        steps.push(PStep::App(a.clone()));
        f.clone()
      },
      ExprData::Mdata(_, x, _) => x.clone(),
      _ => break,
    };
    cur = next;
  }
  steps.reverse();
  (steps, cur)
}

/// `applySteps`.
pub fn apply_steps(steps: &[PStep], e: &Expr) -> Expr {
  steps.iter().fold(e.clone(), |acc, st| match st {
    PStep::Proj(s, i) => proj(s, *i, acc),
    PStep::App(a) => Expr::app(acc, a.clone()),
  })
}

/// `projPrefix`: the maximal prefix of projections, and the rest.
pub fn proj_prefix(steps: &[PStep]) -> (Vec<(Name, usize)>, Vec<PStep>) {
  let k = steps
    .iter()
    .position(|st| matches!(st, PStep::App(_)))
    .unwrap_or(steps.len());
  let projs = extract(steps, 0, k)
    .into_iter()
    .filter_map(|st| match st {
      PStep::Proj(s, j) => Some((s, j)),
      PStep::App(_) => None,
    })
    .collect();
  (projs, extract(steps, k, steps.len()))
}

/// `belowPath`: the motive-part of a path into a `below` dictionary of type
/// `ty`: replay Lean's `searchPProd` and `toBelowAux`
/// (`Structural/BRecOn.lean`) with canaries for the packed motives. The walk
/// follows the `PProd`/`And` nodes of the dictionary's weak head normal
/// form, and passes through a reflexive field's entry (a `∀`) by
/// instantiating it at the path's argument, until it reaches an entry
/// `C_j t`; the projections that follow select the function inside group
/// `j`'s packed motive and are re-associated. `None` when the steps end
/// inside the dictionary before any entry (a part of the dictionary,
/// independent of the clique). A step the walk cannot follow (a weak head
/// normal form that is neither a node nor a `∀`, or another structure than
/// the node's, or an exhausted reducer) is a grammar failure: such a path
/// might reach into the packed motives in a way the walk does not see, so it
/// is never left alone.
pub fn below_path(
  tm: &mut TState,
  l: &StructLayout<'_>,
  ty: &Expr,
  steps: &[PStep],
) -> R<Option<Vec<PStep>>> {
  let Some((c, us, args)) = const_app(ty) else { return Ok(None) };
  let Some(aux) = l.aux.get(&c) else { return Ok(None) };
  let p = l.num_params;
  let k = l.num_motives;
  if aux.is_brec_on || args.len() < p.saturating_add(k) {
    return Ok(None);
  }
  // the canaries
  let cans: Vec<Name> = (0..k).map(|_| tm.fresh_fvar()).collect();
  let mut args2 = extract(&args, 0, p);
  args2.extend(cans.iter().map(fvar));
  args2.extend(extract(&args, p + k, args.len()));
  let mut cur = mk_app_n(cnst(&c, &us), &args2);
  for (t, step) in steps.iter().enumerate() {
    let w = whnf(l.const_of, WHNF_FUEL, &cur)?;
    match step {
      PStep::Proj(s, i) => match decode_node(PackKind::Pprod, &w) {
        Some((_, _, left, right)) => {
          let is_and = const_app(&w).is_some_and(|(h, _, _)| h == n_and());
          if (*s == n_and()) != is_and {
            return Err(
              "grammar: a projection into a below dictionary whose structure \
               is not the node's"
                .into(),
            );
          }
          cur = if *i == 0 { left } else { right };
        },
        None => {
          return Err(
            "grammar: a projection into a below dictionary that the walk \
             cannot follow"
              .into(),
          );
        },
      },
      PStep::App(x) => match strip_mdata(&w).as_data() {
        ExprData::ForallE(_, _, b, _, _) => {
          cur = instantiate_rev(b, slice::from_ref(x));
        },
        _ => {
          return Err(
            "grammar: an application inside a below dictionary that the walk \
             cannot follow"
              .into(),
          );
        },
      },
    }
    // an entry of the dictionary: a canary applied
    let head = get_app_fn_args(&strip_mdata(&cur)).0;
    if let ExprData::Fvar(f, _) = head.as_data() {
      let Some(j) = cans.iter().position(|x| x == f) else {
        return Err(
          "grammar: a path into a below dictionary that reaches a foreign \
           variable"
            .into(),
        );
      };
      let g =
        tm_idx(&l.groups, j, "structural: the group of a dictionary entry")?;
      let (projs, tail) = proj_prefix(&extract(steps, t + 1, steps.len()));
      let projs2 = transport_path(g, &projs)?;
      let mut out = extract(steps, 0, t + 1);
      out.extend(projs2.into_iter().map(|(s, i)| PStep::Proj(s, i)));
      out.extend(tail);
      return Ok(Some(out));
    }
  }
  Ok(None)
}

// ---------------------------------------------------------------------------
// Φ_σ
// ---------------------------------------------------------------------------

/// The binder context of the structural `Φ` (`SCtx`): Lean's binder types,
/// outermost first, each with its ownership (the recursion's own `below`
/// dictionary), and the running hash of the entries, the context's part of
/// the memo key ([`phi_s_fix`]), so that a push costs O(1).
///
/// The running hash is Lean's fold (seed `7`, then per entry the type's hash
/// and the ownership tag `11`/`13`) over Blake3 digests: the memo key of
/// [`TState::cache_own`] is a pair of full digests where Lean mixes 64-bit
/// hashes and confirms a hit on the entries.
#[derive(Clone, Debug)]
pub struct SCtx {
  pub entries: Vec<(Expr, bool)>,
  pub hash: Hash,
}

impl Default for SCtx {
  fn default() -> Self {
    SCtx { entries: Vec::new(), hash: blake3::hash(&[7]) }
  }
}

impl SCtx {
  /// One step of the running hash.
  fn mix(h: &Hash, t: &Expr, owned: bool) -> Hash {
    let mut hasher = blake3::Hasher::new();
    hasher.update(h.as_bytes());
    hasher.update(key(t).as_bytes());
    hasher.update(&[if owned { 11 } else { 13 }]);
    hasher.finalize()
  }

  /// The running hash of `entries`, recomputed by the full fold (the value
  /// [`SCtx::push`] maintains).
  pub fn fold_hash(entries: &[(Expr, bool)]) -> Hash {
    entries.iter().fold(SCtx::default().hash, |h, (t, o)| SCtx::mix(&h, t, *o))
  }

  /// `SCtx.push`, in place.
  pub fn push(&mut self, t: &Expr, owned: bool) {
    self.hash = SCtx::mix(&self.hash, t, owned);
    self.entries.push((t.clone(), owned));
  }

  /// `SCtx.push`, as a new context.
  pub fn pushed(&self, t: &Expr, owned: bool) -> SCtx {
    let mut c = self.clone();
    c.push(t, owned);
    c
  }

  /// `SCtx.ofArray`.
  pub fn of_array(xs: &[(Expr, bool)]) -> SCtx {
    let mut c = SCtx::default();
    for (t, o) in xs {
      c.push(t, *o);
    }
    c
  }

  /// `SCtx.get?`: the binder `bvar i` refers to, its type (in its own
  /// context) and its ownership; `None` for a variable bound outside the
  /// context.
  pub fn get(&self, i: usize) -> Option<&(Expr, bool)> {
    let n = self.entries.len();
    if i < n { self.entries.get(n - 1 - i) } else { None }
  }
}

/// `go`, the transformation of subterms inside one step of `Φ_σ`:
/// [`phi_s_fix`] on the layout `l` with the remaining bound `fuel`
/// (`phiSFix L fuel`; `phiSC L` is the one with [`TRANSPORT_FUEL`]).
#[derive(Clone, Copy)]
pub struct Go<'l, 'a> {
  pub l: &'l StructLayout<'a>,
  pub fuel: usize,
}

impl Go<'_, '_> {
  /// Apply `go` to `e` in the context `ctx`.
  pub fn run(self, tm: &mut TState, ctx: &SCtx, e: &Expr) -> R<Expr> {
    phi_s_fix(tm, self.l, self.fuel, ctx, e)
  }

  /// `go` on each of `xs` (`xs.mapM (go ctx)`).
  pub fn run_all(
    self,
    tm: &mut TState,
    ctx: &SCtx,
    xs: &[Expr],
  ) -> R<Vec<Expr>> {
    xs.iter().map(|x| self.run(tm, ctx, x)).collect()
  }
}

/// `phiSMotive`: the packed motive at motive position `j` of a
/// `below`/`brecOn` application of the block, in canonical order (its
/// leaves transported by `go`).
pub fn phi_s_motive(
  tm: &mut TState,
  go: Go<'_, '_>,
  ctx: &SCtx,
  j: usize,
  arg: &Expr,
) -> R<Expr> {
  let g =
    tm_idx(&go.l.groups, j, "structural: the group of a motive position")?;
  if g.size() < 2 {
    return go.run(tm, ctx, arg);
  }
  let (bs, body) = peel_lams(g.arity, arg);
  let mut ctx2 = ctx.clone();
  let mut bs2: Vec<Binder> = Vec::with_capacity(bs.len());
  for (nm, t, bi) in bs {
    bs2.push((nm, go.run(tm, &ctx2, &t)?, bi));
    ctx2.push(&t, false);
  }
  let Some(s) = decode_spine(PackKind::Pprod, g.size(), &body) else {
    return Err("grammar: a packed motive that is not Lean's".into());
  };
  let leaves = go.run_all(tm, &ctx2, &s.leaves)?;
  let Some(s2) = s.with_leaves(leaves).permute(&g.perm) else {
    return Err(
      "grammar: a packed motive whose group order is not a permutation".into(),
    );
  };
  Ok(mk_lams(&bs2, spine_type_m(&s2, "grammar: a packed motive")?))
}

/// `phiSDictType`: the type of an owned dictionary binder (or of a matcher
/// motive's binder built from one, `MatcherApp.addArg`): a `below`
/// application of the block has its motives permuted. These are the only
/// places where Lean's encoding writes a `below` application in a definition
/// clique, so with ownership enforced no other `below` application is
/// touched (a user's `below` application keeps its motive). Anything else is
/// `go`.
pub fn phi_s_dict_type(
  tm: &mut TState,
  go: Go<'_, '_>,
  ctx: &SCtx,
  t: &Expr,
) -> R<Expr> {
  let (h, args) = get_app_fn_args(t);
  if let ExprData::Const(c, _, _) = h.as_data()
    && let Some(a) = go.l.aux.get(c)
  {
    if a.is_brec_on {
      return go.run(tm, ctx, t);
    }
    let p = go.l.num_params;
    let k = go.l.num_motives;
    let mut args2 = Vec::with_capacity(args.len());
    for (i, x) in args.iter().enumerate() {
      args2.push(if p <= i && i - p < k {
        phi_s_motive(tm, go, ctx, i - p, x)?
      } else {
        go.run(tm, ctx, x)?
      });
    }
    return Ok(mk_app_n(h.clone(), &args2));
  }
  go.run(tm, ctx, t)
}

/// The transformation of the binders' bodies in [`StepCx::under_binders`]
/// (`SCtx → Expr → TM Expr`).
pub type BodyK<'k> = &'k dyn Fn(&mut TState, &SCtx, &Expr) -> R<Expr>;

/// The local definitions of one [`phi_s_step`] (`underBinders`, `ownedArg`,
/// `functional`), which close over `go` and the step's context.
struct StepCx<'c, 'l, 'a> {
  go: Go<'l, 'a>,
  ctx: &'c SCtx,
}

impl StepCx<'_, '_, '_> {
  /// `underBinders`: transform `n` leading binders of `x` (`λ` when `lam`,
  /// else `∀`; a binder `i` with `owned(i)` as an owned dictionary) and the
  /// body with `k`.
  fn under_binders(
    &self,
    tm: &mut TState,
    n: usize,
    lam: bool,
    x: &Expr,
    owned: &dyn Fn(usize) -> bool,
    k: BodyK<'_>,
  ) -> R<Expr> {
    let (bs, body) = if lam { peel_lams(n, x) } else { peel_foralls(n, x) };
    let mut ctx2 = self.ctx.clone();
    let mut bs2: Vec<Binder> = Vec::with_capacity(bs.len());
    for (i, (nm, t, bi)) in bs.into_iter().enumerate() {
      let t2 = if owned(i) {
        phi_s_dict_type(tm, self.go, &ctx2, &t)?
      } else {
        self.go.run(tm, &ctx2, &t)?
      };
      bs2.push((nm, t2, bi));
      ctx2.push(&t, owned(i));
    }
    let body2 = k(tm, &ctx2, &body)?;
    Ok(if lam { mk_lams(&bs2, body2) } else { mk_foralls(&bs2, body2) })
  }

  /// `ownedArg`: `x` is a variable bound to an owned dictionary.
  fn owned_arg(&self, x: &Expr) -> bool {
    bvar_idx(&strip_mdata(x))
      .and_then(|i| self.ctx.get(i))
      .is_some_and(|(_, o)| *o)
  }

  /// `args.mapM fun x => if ownedArg x then pure x else go ctx x`.
  fn run_unowned(&self, tm: &mut TState, args: &[Expr]) -> R<Vec<Expr>> {
    args
      .iter()
      .map(|x| {
        if self.owned_arg(x) {
          Ok(x.clone())
        } else {
          self.go.run(tm, self.ctx, x)
        }
      })
      .collect()
  }

  /// `functional`: the packed functional at functional position `j`; its
  /// last binder is the dictionary `brecOn` builds.
  fn functional(&self, tm: &mut TState, j: usize, arg: &Expr) -> R<Expr> {
    let g = tm_idx(
      &self.go.l.groups,
      j,
      "structural: the group of a functional position",
    )?;
    let arity = g.arity;
    let dict = |i: usize| i == arity;
    let go = self.go;
    if g.size() < 2 {
      return self.under_binders(
        tm,
        arity.saturating_add(1),
        true,
        arg,
        &dict,
        &|tm, c, body| go.run(tm, c, body),
      );
    }
    self.under_binders(
      tm,
      arity.saturating_add(1),
      true,
      arg,
      &dict,
      &|tm, c, body| {
        let Some((s, cs)) = decode_tuple(g.size(), body) else {
          return Err("grammar: a packed functional that is not Lean's".into());
        };
        let leaves = go.run_all(tm, c, &s.leaves)?;
        let cs = go.run_all(tm, c, &cs)?;
        let not_perm = || {
          "grammar: a packed functional whose group order is not a \
           permutation"
            .to_string()
        };
        let Some(s2) = s.with_leaves(leaves).permute(&g.perm) else {
          return Err(not_perm());
        };
        let Some(cs2) = permute(&g.perm, &cs) else { return Err(not_perm()) };
        mk_tuple(&s2, &cs2).ok_or_else(|| {
          "grammar: a packed functional with fewer components than its \
           packing"
            .to_string()
        })
      },
    )
  }
}

/// `phiSStep`: one step of `Φ_σ` on a structural clique's term, in a context
/// of binder types (Lean's, outermost first) each with its ownership (the
/// recursion's own `below` dictionary); `go` is `Φ_σ` on subterms.
pub fn phi_s_step(
  tm: &mut TState,
  go: Go<'_, '_>,
  ctx: &SCtx,
  e: &Expr,
) -> R<Expr> {
  let l = go.l;
  let cx = StepCx { go, ctx };
  match e.as_data() {
    ExprData::Proj(..) => {
      // a path of projections and applications from a variable: a path into
      // a `below` dictionary when the variable is one (the applications are
      // a reflexive field's arguments, transported as terms)
      let (gsteps, gbase) = path_chain(e);
      if let Some(i) = bvar_idx(&strip_mdata(&gbase))
        && let Some((t, owned)) = ctx.get(i)
      {
        let ty = lift_loose(t, i.saturating_add(1), 0);
        if let Some(steps2) = below_path(tm, l, &ty, &gsteps)? {
          if l.check_ownership && !owned {
            return Err(
              "grammar: a path into a below dictionary that is not the \
               recursion's own"
                .into(),
            );
          }
          let mut steps3 = Vec::with_capacity(steps2.len());
          for st in steps2 {
            steps3.push(match st {
              PStep::App(a) => PStep::App(go.run(tm, ctx, &a)?),
              s @ PStep::Proj(..) => s,
            });
          }
          return Ok(apply_steps(&steps3, &gbase));
        }
      }
      let (steps, base) = proj_chain(e);
      let base2 = strip_mdata(&base);
      if let ExprData::Bvar(..) = base2.as_data() {
        return Ok(apply_projs(&steps, &base));
      }
      let brec_on = const_app(&base2)
        .and_then(|(c, _, _)| l.aux.get(&c).copied())
        .filter(|a| a.is_brec_on);
      let b = go.run(tm, ctx, &base2)?;
      match brec_on {
        Some(a) => {
          let g = tm_idx(
            &l.groups,
            a.pos,
            "structural: the group of a brecOn application",
          )?;
          let steps2 = transport_path(g, &steps)?;
          Ok(apply_projs(&steps2, &b))
        },
        None => Ok(apply_projs(&steps, &b)),
      }
    },
    ExprData::App(..) => {
      let (h, args) = get_app_fn_args(e);
      let ExprData::Const(c, _, _) = h.as_data() else {
        if l.check_ownership && args.iter().any(|x| cx.owned_arg(x)) {
          return Err(
            "grammar: a below dictionary passed to a term that is not an \
             eliminator"
              .into(),
          );
        }
        let h2 = go.run(tm, ctx, &h)?;
        return Ok(mk_app_n(h2, &go.run_all(tm, ctx, &args)?));
      };
      if let Some(a) = l.aux.get(c).copied() {
        // with ownership enforced, a `below` application here is not in an
        // owned dictionary's binder type (those go through
        // `phi_s_dict_type`): it is the user's, and keeps its motive
        if !a.is_brec_on && l.check_ownership {
          return Ok(mk_app_n(h.clone(), &go.run_all(tm, ctx, &args)?));
        }
        let p = l.num_params;
        let k = l.num_motives;
        let g = tm_idx(
          &l.groups,
          a.pos,
          "structural: the group of a below/brecOn application",
        )?;
        let f_start = p.saturating_add(k).saturating_add(g.arity);
        let mut args2 = Vec::with_capacity(args.len());
        for (i, x) in args.iter().enumerate() {
          args2.push(if p <= i && i - p < k {
            phi_s_motive(tm, go, ctx, i - p, x)?
          } else if a.is_brec_on && f_start <= i && i - f_start < k {
            cx.functional(tm, i - f_start, x)?
          } else {
            go.run(tm, ctx, x)?
          });
        }
        return Ok(mk_app_n(h.clone(), &args2));
      }
      if l.f_names.contains(c) {
        if args.len() < l.num_fixed {
          return Err("grammar: a partial application of a functional".into());
        }
        let args2 = cx.run_unowned(tm, &args)?;
        let Some(mut out) = reorder(&l.fixed_perm, &args2) else {
          return Err(
            "grammar: a functional's fixed arguments do not fit its telescope"
              .into(),
          );
        };
        out.extend(extract(&args2, l.num_fixed, args2.len()));
        return Ok(mk_app_n(h.clone(), &out));
      }
      if let Some(msh) = l.matchers.get(c) {
        let m = l.num_fun_types;
        if args.len() < m {
          return Err(
            "grammar: a partial application of a below matcher".into(),
          );
        }
        if l.check_ownership {
          let owned: Vec<bool> = args.iter().map(|x| cx.owned_arg(x)).collect();
          l.check_matcher_ownership(c, msh, &owned)?;
        }
        let args2 = cx.run_unowned(tm, &args)?;
        let Some(mut out) = reorder(&l.fun_perm, &args2) else {
          return Err(
            "grammar: a below matcher's funType arguments do not fit the \
             clique"
              .into(),
          );
        };
        out.extend(extract(&args2, m, args2.len()));
        return Ok(mk_app_n(h.clone(), &out));
      }
      if l.check_ownership && args.iter().any(|x| cx.owned_arg(x)) {
        let args2 = phi_s_eliminator(tm, &cx, c, &args)?;
        return Ok(mk_app_n(h.clone(), &args2));
      }
      Ok(mk_app_n(h.clone(), &go.run_all(tm, ctx, &args)?))
    },
    ExprData::Const(c, _, _) => {
      if l.f_names.contains(c) && l.num_fixed > 0 {
        return Err("grammar: a bare functional".into());
      }
      if l.matchers.contains_key(c) && l.num_fun_types > 0 {
        return Err("grammar: a bare below matcher".into());
      }
      Ok(e.clone())
    },
    ExprData::Lam(nm, t, b, bi, _) => {
      if l.check_ownership && l.is_below_ty(t) {
        return Err(format!(
          "grammar: a binder {} of a below type that is not the recursion's \
           dictionary",
          nm.pretty()
        ));
      }
      let t2 = go.run(tm, ctx, t)?;
      let b2 = go.run(tm, &ctx.pushed(t, false), b)?;
      Ok(Expr::lam(nm.clone(), t2, b2, bi.clone()))
    },
    ExprData::ForallE(nm, t, b, bi, _) => {
      let t2 = go.run(tm, ctx, t)?;
      let b2 = go.run(tm, &ctx.pushed(t, false), b)?;
      Ok(Expr::all(nm.clone(), t2, b2, bi.clone()))
    },
    ExprData::LetE(nm, t, v, b, nd, _) => {
      if l.check_ownership && l.is_below_ty(t) {
        return Err(format!(
          "grammar: a let {} of a below type that is not the recursion's \
           dictionary",
          nm.pretty()
        ));
      }
      let t2 = go.run(tm, ctx, t)?;
      let v2 = go.run(tm, ctx, v)?;
      let b2 = go.run(tm, &ctx.pushed(t, false), b)?;
      Ok(Expr::letE(nm.clone(), t2, v2, b2, *nd))
    },
    ExprData::Bvar(..) => {
      if l.check_ownership && cx.owned_arg(e) {
        return Err(
          "grammar: a below dictionary used whole outside an eliminator".into(),
        );
      }
      Ok(e.clone())
    },
    ExprData::Mdata(d, x, _) => Ok(Expr::mdata(d.clone(), go.run(tm, ctx, x)?)),
    _ => Ok(e.clone()),
  }
}

/// The arguments of an application of the eliminator `c` (neither a
/// `below`/`brecOn` constant, a functional nor a below matcher) that
/// receives an owned dictionary, with ownership enforced: the dictionary
/// must be past `c`'s declared arity, and it reaches the trailing binders of
/// the alternatives (`phiSStep`'s eliminator case).
fn phi_s_eliminator(
  tm: &mut TState,
  cx: &StepCx<'_, '_, '_>,
  c: &Name,
  args: &[Expr],
) -> R<Vec<Expr>> {
  let go = cx.go;
  let cs = name_to_string(c);
  let Some(ci) = (go.l.const_of)(c) else {
    return Err(format!(
      "grammar: a below dictionary passed to {cs}, which is not in the input"
    ));
  };
  let ty = ci.get_type();
  let ar = forall_arity(ty);
  if ar > args.len() {
    return Err(format!(
      "grammar: a below dictionary passed to a partial application of {cs}"
    ));
  }
  if extract(args, 0, ar).iter().any(|x| cx.owned_arg(x)) {
    return Err(format!("grammar: a below dictionary passed whole to {cs}"));
  }
  let extras: Vec<bool> =
    extract(args, ar, args.len()).iter().map(|x| cx.owned_arg(x)).collect();
  let (ps, _) = peel_foralls(ar, ty);
  let Some(shape) = go.l.elim_shape(c) else {
    return Err(format!(
      "grammar: a below dictionary passed to {cs}, whose declaration cannot \
       be read"
    ));
  };
  let mut args2 = Vec::with_capacity(args.len());
  for (k, x) in args.iter().enumerate() {
    if let Some(&(_, ma)) = shape.motives.iter().find(|m| m.0 == k) {
      // the motive: its leading binders after its own are the extras'
      // types, an owned dictionary's a `below` of the block
      if lam_arity(x) < ma {
        return Err(format!(
          "grammar: a motive of {cs} that is not a function of its \
           discriminants"
        ));
      }
      args2.push(cx.under_binders(
        tm,
        ma,
        true,
        x,
        &|_| false,
        &|tm, c2, body| {
          let (fs, rest) = peel_foralls(extras.len(), body);
          if fs.len() != extras.len() {
            return Err(format!(
              "grammar: a motive of {cs} that does not bind the dictionary"
            ));
          }
          let mut c3 = c2.clone();
          let mut fs2: Vec<Binder> = Vec::with_capacity(fs.len());
          for ((nm, t, bi), &is_owned) in fs.into_iter().zip(&extras) {
            let t2 = if is_owned {
              phi_s_dict_type(tm, go, &c3, &t)?
            } else {
              go.run(tm, &c3, &t)?
            };
            fs2.push((nm, t2, bi));
            c3.push(&t, false);
          }
          Ok(mk_foralls(&fs2, go.run(tm, &c3, &rest)?))
        },
      )?);
    } else if let Some((_, pt, _)) = ps.get(k) {
      let fc = forall_arity(pt);
      let (_, concl) = peel_foralls(fc, pt);
      let is_alt = bvar_idx(&get_app_fn_args(&strip_mdata(&concl)).0)
        .is_some_and(|i| i >= fc && i - fc < k);
      if is_alt {
        let n = fc.saturating_add(extras.len());
        if lam_arity(x) < n {
          return Err(format!(
            "grammar: an alternative of {cs} that does not bind the dictionary"
          ));
        }
        args2.push(cx.under_binders(
          tm,
          n,
          true,
          x,
          &|i| i >= fc && extras.get(i - fc) == Some(&true),
          &|tm, c2, body| go.run(tm, c2, body),
        )?);
      } else {
        args2.push(go.run(tm, cx.ctx, x)?);
      }
    } else if cx.owned_arg(x) {
      args2.push(x.clone());
    } else {
      args2.push(go.run(tm, cx.ctx, x)?);
    }
  }
  Ok(args2)
}

/// `phiSFix`: `Φ_σ` with a context, memoised by the term, the context and
/// the ownership mode (`l.check_ownership`). Within one transport the layout
/// differs only in that mode (the members and functionals of a definition
/// clique with ownership enforced, the carried lemmas without), and
/// [`phi_s_step`]'s result depends on it (a `below` application outside an
/// owned binder keeps its motive with ownership enforced and is
/// re-associated without), so a result is shared only within one mode. The
/// key is the term's digest, the context's running hash ([`SCtx::hash`])
/// and the mode; as in Lean, the bound is not part of it.
pub fn phi_s_fix(
  tm: &mut TState,
  l: &StructLayout<'_>,
  fuel: usize,
  ctx: &SCtx,
  e: &Expr,
) -> R<Expr> {
  let Some(fuel) = fuel.checked_sub(1) else {
    return Err("Φ: recursion bound exhausted".into());
  };
  let k = (key(e), ctx.hash, l.check_ownership);
  if let Some(r) = tm.cache_own.get(&k) {
    return Ok(r.clone());
  }
  let r = phi_s_step(tm, Go { l, fuel }, ctx, e)?;
  tm.cache_own.insert(k, r.clone());
  Ok(r)
}

/// `phiSC`: `Φ_σ` in the context `ctx`, with the transport's bound.
pub fn phi_sc(
  tm: &mut TState,
  l: &StructLayout<'_>,
  ctx: &SCtx,
  e: &Expr,
) -> R<Expr> {
  phi_s_fix(tm, l, TRANSPORT_FUEL, ctx, e)
}

/// `phiS`: `Φ_σ` in the context of the binder types `ctx` (outermost
/// first, each with its ownership).
pub fn phi_s(
  tm: &mut TState,
  l: &StructLayout<'_>,
  ctx: &[(Expr, bool)],
  e: &Expr,
) -> R<Expr> {
  phi_sc(tm, l, &SCtx::of_array(ctx), e)
}

// ---------------------------------------------------------------------------
// The block and its family
// ---------------------------------------------------------------------------

/// `brecOnOwner`: the inductive of a `brecOn` constant, `T` for `T.brecOn`,
/// `all₀` for `all₀.brecOn_k`.
pub fn brec_on_owner(n: &Name) -> Name {
  match n.as_data() {
    NameData::Str(p, _, _) => p.clone(),
    _ => n.clone(),
  }
}

/// `blockNames`: per motive position of the block of `iv` (the type formers
/// of `all`, then the nested auxiliaries), its `below`, `brecOn` and
/// recursor names; `None` for a block with nested auxiliaries and no type
/// former.
pub fn block_names(iv: &InductiveVal) -> Option<Vec<(Name, Name, Name)>> {
  let all = &iv.all;
  (0..all.len().saturating_add(nat_usize(&iv.num_nested)))
    .map(|j| match all.get(j) {
      Some(t) => {
        Some((mk_str(t, "below"), mk_str(t, "brecOn"), mk_str(t, "rec")))
      },
      None => {
        let t = all.first()?;
        let k = j - all.len() + 1;
        Some((
          mk_str(t, &format!("below_{k}")),
          mk_str(t, &format!("brecOn_{k}")),
          mk_str(t, &format!("rec_{k}")),
        ))
      },
    })
    .collect()
}

/// `familyCandidates`: the names the transport may treat as the
/// `below`/`brecOn` family of the block of the `brecOn` constant `brec_on`,
/// for the caller to authenticate: the block's `all`, and per motive
/// position its `below` and `brecOn`, then the `.go`/`.eq` the input has
/// under the `brecOn` names. The caller passes the names
/// `aux_gen::source_family::filter_heads` keeps as [`struct_layout`]'s
/// `family`. `None` when `brec_on` is not under a recursive inductive of the
/// input ([`block_of`] refuses those).
pub fn family_candidates(
  const_of: ConstOf<'_>,
  brec_on: &Name,
) -> Option<(Vec<Name>, Vec<Name>)> {
  let Some(ConstantInfo::InductInfo(iv)) = const_of(&brec_on_owner(brec_on))
  else {
    return None;
  };
  if !iv.is_rec {
    return None;
  }
  let names = block_names(&iv)?;
  let mut out: Vec<Name> = names
    .iter()
    .flat_map(|(below, brec, _)| [below.clone(), brec.clone()])
    .collect();
  out.extend(
    names
      .iter()
      .flat_map(|(_, brec, _)| [mk_str(brec, "go"), mk_str(brec, "eq")])
      .filter(|x| const_of(x).is_some()),
  );
  Some((iv.all, out))
}

/// The block of a `brecOn` constant ([`block_of`]): its `below`/`brecOn`
/// constants by motive position, the number of parameters and motives, each
/// position's motive arity.
pub type BlockOf = (FxHashMap<Name, BlockAux>, usize, usize, Vec<usize>);

/// `blockOf`: the block of a `brecOn` constant. The inductive must be
/// recursive, and every `below`/`brecOn` name the layout relies on must be
/// in the authenticated `family`.
pub fn block_of(
  const_of: ConstOf<'_>,
  family: &FxHashSet<Name>,
  brec_on: &Name,
) -> R<BlockOf> {
  let bs = name_to_string(brec_on);
  let Some(ConstantInfo::InductInfo(iv)) = const_of(&brec_on_owner(brec_on))
  else {
    return Err(format!("{bs}: not the brecOn of an inductive"));
  };
  if !iv.is_rec {
    return Err(format!(
      "{bs}: the inductive is not recursive (Lean generates no below/brecOn \
       family)"
    ));
  }
  let Some(names) = block_names(&iv) else {
    return Err(format!(
      "{bs}: a block with nested auxiliaries and no type former"
    ));
  };
  let mut aux: FxHashMap<Name, BlockAux> = FxHashMap::default();
  let mut arities = Vec::with_capacity(names.len());
  for (j, (below, brec, rec_n)) in names.iter().enumerate() {
    for x in [below, brec] {
      if !family.contains(x) {
        return Err(format!(
          "{}: not in the block's authenticated below/brecOn family",
          name_to_string(x)
        ));
      }
    }
    aux.insert(below.clone(), BlockAux { pos: j, is_brec_on: false });
    aux.insert(brec.clone(), BlockAux { pos: j, is_brec_on: true });
    let Some(ConstantInfo::RecInfo(r)) = const_of(rec_n) else {
      return Err(format!("{}: no recursor", name_to_string(rec_n)));
    };
    arities.push(nat_usize(&r.num_indices).saturating_add(1));
  }
  Ok((aux, nat_usize(&iv.num_params), names.len(), arities))
}

// ---------------------------------------------------------------------------
// The members
// ---------------------------------------------------------------------------

/// A telescope of `let`s: name, type, value, outermost first.
pub type Lets = Vec<(Name, Expr, Expr)>;

/// `peelLets`: peel up to `n` leading `let`s (through `mdata`); on fewer,
/// the rest with its `mdata` stripped.
pub fn peel_lets(n: usize, e: &Expr) -> (Lets, Expr) {
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

/// `letArity`: the number of leading `let`s (through `mdata`).
pub fn let_arity(e: &Expr) -> usize {
  let mut n = 0;
  let mut cur = e;
  loop {
    match cur.as_data() {
      ExprData::LetE(_, _, _, b, _, _) => {
        n += 1;
        cur = b;
      },
      ExprData::Mdata(_, x, _) => cur = x,
      _ => return n,
    }
  }
}

/// A member's shape, `λ ys. let … ; (projs (brecOn …)) rest`
/// (`MemberShape`).
#[derive(Clone, Debug)]
pub struct MemberShape {
  pub lams: usize,
  pub lets: usize,
  pub brec_on_name: Name,
  /// the `brecOn` application's arguments
  pub brec_args: Vec<Expr>,
  pub steps: Vec<(Name, usize)>,
}

/// `memberShape`.
pub fn member_shape(d: &Decl) -> R<MemberShape> {
  let (ps, b1) = peel_lams(lam_arity(&d.value), &d.value);
  let (ls, b2) = peel_lets(let_arity(&b1), &b1);
  let (h, _) = get_app_fn_args(&strip_mdata(&b2));
  // `(projs (brecOn …)) rest`, or the `brecOn` application itself
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

/// `remapLoose`: map the loose variables `bvar k`, `k < map.len()`, of `e`
/// to `bvar map[k]` (over distinct subterms).
pub fn remap_loose(map: &[usize], e: &Expr) -> Expr {
  fn go(
    map: &[usize],
    e: &Expr,
    d: usize,
    memo: &mut ExactMemo<usize, Expr>,
  ) -> Expr {
    if let ExprData::Bvar(i, _) = e.as_data() {
      let i = nat_usize(i);
      return match i.checked_sub(d).and_then(|k| map.get(k)) {
        Some(&m) => bvar(d.saturating_add(m)),
        None => e.clone(),
      };
    }
    if let Some(r) = memo.get(e, d) {
      return r;
    }
    let r = match e.as_data() {
      ExprData::App(f, a, _) => {
        let f2 = go(map, f, d, memo);
        Expr::app(f2, go(map, a, d, memo))
      },
      ExprData::Lam(nm, t, b, bi, _) => {
        let t2 = go(map, t, d, memo);
        Expr::lam(nm.clone(), t2, go(map, b, d + 1, memo), bi.clone())
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        let t2 = go(map, t, d, memo);
        Expr::all(nm.clone(), t2, go(map, b, d + 1, memo), bi.clone())
      },
      ExprData::LetE(nm, t, v, b, nd, _) => {
        let t2 = go(map, t, d, memo);
        let v2 = go(map, v, d, memo);
        Expr::letE(nm.clone(), t2, v2, go(map, b, d + 1, memo), *nd)
      },
      ExprData::Proj(s, i, x, _) => {
        Expr::proj(s.clone(), i.clone(), go(map, x, d, memo))
      },
      ExprData::Mdata(m, x, _) => Expr::mdata(m.clone(), go(map, x, d, memo)),
      _ => return e.clone(),
    };
    memo.insert(e, d, r.clone());
    r
  }
  if map.is_empty() {
    return e.clone();
  }
  go(map, e, 0, &mut ExactMemo::default())
}

/// `reorderLets`: reorder a telescope of independent `let`s (`perm[p]` =
/// old let at new position `p`) and re-index the body; the values must not
/// mention earlier lets (Lean's `funType_i`, `IndPred.lean`'s
/// `withFunTypes`).
pub fn reorder_lets(perm: &[usize], ls: &Lets, body: &Expr) -> R<(Lets, Expr)> {
  let n = ls.len();
  let mut closed = Vec::with_capacity(n);
  for (i, (nm, t, v)) in ls.iter().enumerate() {
    let Some(t2) = lower_opt(t, i) else {
      return Err("a let type mentions an earlier let".into());
    };
    let Some(v2) = lower_opt(v, i) else {
      return Err("a let value mentions an earlier let".into());
    };
    closed.push((nm.clone(), t2, v2));
  }
  let Some(inv) = inv_perm(perm) else {
    return Err("reorderLets: the order is not a permutation".into());
  };
  let not_index =
    || "reorderLets: the order does not index the lets".to_string();
  let ls2: Option<Lets> = (0..n)
    .map(|p| {
      let (nm, t, v) = closed.get(*perm.get(p)?)?;
      Some((nm.clone(), lift_loose(t, p, 0), lift_loose(v, p, 0)))
    })
    .collect();
  let Some(ls2) = ls2 else { return Err(not_index()) };
  // old let `i` is `bvar (n-1-i)`; it becomes `bvar (n-1-inv[i])`
  let map: Option<Vec<usize>> = (0..n)
    .map(|k| {
      let j = *inv.get(n - 1 - k)?;
      Some(n.saturating_sub(1).saturating_sub(j))
    })
    .collect();
  let Some(map) = map else { return Err(not_index()) };
  Ok((ls2, remap_loose(&map, body)))
}

/// `mkLets`: `let ls; body`, outermost first.
pub fn mk_lets(ls: &Lets, body: Expr) -> Expr {
  ls.iter().rev().fold(body, |acc, (nm, t, v)| {
    Expr::letE(nm.clone(), t.clone(), v.clone(), acc, false)
  })
}

/// `structLayout`: the structural layout of a clique from its members
/// (Lean's order), the other constants of its encoding (`aux`: the
/// functionals, the below matchers), `sigma`, the input, and the
/// authenticated `below`/`brecOn` family of its block
/// ([`family_candidates`]).
pub fn struct_layout<'a>(
  members: &[Decl],
  aux: &[Decl],
  sigma: &[usize],
  const_of: ConstOf<'a>,
  family: FxHashSet<Name>,
) -> R<StructLayout<'a>> {
  let bad = || "structLayout: bad permutation".to_string();
  let n = members.len();
  if !(n >= 2 && sigma.len() == n && is_perm(sigma)) {
    return Err(bad());
  }
  let shapes = members.iter().map(member_shape).collect::<R<Vec<_>>>()?;
  let Some(sh0) = shapes.first() else { return Err(bad()) };
  let (block_aux, p, k_total, arities) =
    block_of(const_of, &family, &sh0.brec_on_name)?;
  let poss = shapes
    .iter()
    .map(|s| match block_aux.get(&s.brec_on_name) {
      Some(a) if a.is_brec_on => Ok(a.pos),
      Some(_) => Err("structLayout: not a brecOn".to_string()),
      None => Err("structLayout: members over different blocks".to_string()),
    })
    .collect::<R<Vec<usize>>>()?;
  // the below matchers: the name is a pre-filter, the declaration decides
  let num_fun_types = sh0.lets;
  let mut matchers: FxHashMap<Name, MatcherShape> = FxHashMap::default();
  for d in aux {
    if !is_matcher_name(&d.name) {
      continue;
    }
    let shape =
      matcher_shape(const_of, &|c| matchers.contains_key(c), num_fun_types, d);
    if let Some(s) = shape {
      matchers.insert(d.name.clone(), s);
    }
  }
  // groups
  let missing_motive = || "structLayout: missing motive".to_string();
  let mut groups: Vec<Group> = Vec::with_capacity(k_total);
  for j in 0..k_total {
    let Some(&arity) = arities.get(j) else { return Err(missing_motive()) };
    let members: Vec<usize> =
      (0..n).filter(|&i| poss.get(i) == Some(&j)).collect();
    let size = members.len();
    if size >= 2 {
      let Some(motive) = sh0.brec_args.get(p.saturating_add(j)) else {
        return Err(missing_motive());
      };
      let (_, body) = peel_lams(arity, motive);
      let Some(spine) = decode_spine(PackKind::Pprod, size, &body) else {
        return Err("structLayout: a packed motive that is not Lean's".into());
      };
      let Some(ranks) = members
        .iter()
        .map(|&i| sigma.get(i).copied())
        .collect::<Option<Vec<usize>>>()
      else {
        return Err(bad());
      };
      let perm = ranks
        .iter()
        .map(|&r| ranks.iter().filter(|&&x| x < r).count())
        .collect();
      groups.push(Group { members, arity, spine, perm });
    } else {
      groups.push(Group {
        members,
        arity,
        spine: empty_spine(),
        perm: id_perm(size),
      });
    }
  }
  // each member projects its own position
  for (i, sh) in shapes.iter().enumerate() {
    let not_proj = || {
      format!("structLayout: member {i} does not project its clique position")
    };
    let Some(g) = poss.get(i).and_then(|&pos| groups.get(pos)) else {
      return Err(not_proj());
    };
    if g.size() >= 2 {
      let Some(a) = g.members.iter().position(|&x| x == i) else {
        return Err(not_proj());
      };
      match path_prefix(g.size(), &sh.steps) {
        Some((idx, len))
          if idx == a
            && len == sh.steps.len()
            && steps_fit(&g.spine, idx, &sh.steps) => {},
        _ => return Err(not_proj()),
      }
    }
  }
  // the functionals and the fixed parameters
  let mut f_names: FxHashSet<Name> = FxHashSet::default();
  let mut f_list: Vec<Name> = Vec::new();
  let mut f_depth: FxHashMap<Name, (usize, usize)> = FxHashMap::default();
  let mut qss: Vec<Vec<usize>> = Vec::with_capacity(n);
  for (i, sh) in shapes.iter().enumerate() {
    let missing = || "structLayout: missing functional".to_string();
    let Some(&arity) = poss.get(i).and_then(|&pos| arities.get(pos)) else {
      return Err(missing());
    };
    let f_start = p.saturating_add(k_total).saturating_add(arity);
    let mut q_opt: Option<Vec<usize>> = None;
    for (j, g) in groups.iter().enumerate() {
      if g.size() == 0 {
        continue;
      }
      let Some(f) = sh.brec_args.get(f_start.saturating_add(j)) else {
        return Err(missing());
      };
      let depth = lam_arity(f).min(g.arity.saturating_add(1));
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
        if matchers.contains_key(&h) {
          continue;
        }
        if !f_names.contains(&h) {
          f_list.push(h.clone());
        }
        f_names.insert(h.clone());
        f_depth.insert(h, (depth, g.arity));
        if args.len() < depth {
          return Err(
            "structLayout: a functional applied to too few arguments".into(),
          );
        }
        let m = args.len() - depth;
        let mut q = Vec::with_capacity(m);
        for x in args.iter().take(m) {
          match bvar_idx(&strip_mdata(x)) {
            Some(b)
              if b >= depth + sh.lets && b - depth - sh.lets < sh.lams =>
            {
              q.push(sh.lams - 1 - (b - depth - sh.lets));
            },
            _ => {
              return Err(
                "structLayout: a fixed argument is not a member parameter"
                  .into(),
              );
            },
          }
        }
        // A fixed slot is identified by its source binder, not by its type.
        // Repeated arguments do not establish an invertible telescope map.
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
    // a member none of whose functionals is a constant (the inductive-
    // predicate route, whose functionals are inline) has no fixed parameter
    qss.push(q_opt.unwrap_or_default());
  }
  let inconsistent =
    || "structLayout: inconsistent fixed parameters".to_string();
  let Some(q0) = qss.first() else { return Err(inconsistent()) };
  let m = q0.len();
  if !qss.iter().all(|q| q.len() == m) {
    return Err(inconsistent());
  }
  if !eq_sorted(q0) {
    return Err(
      "structLayout: the fixed parameters are not in the first member's order"
        .into(),
    );
  }
  let Some(fun_perm) = inv_perm(sigma) else { return Err(bad()) };
  let Some(qg) = fun_perm.first().and_then(|&g| qss.get(g)) else {
    return Err(inconsistent());
  };
  let fixed_perm = sort_idx_by_key(qg);
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
    family,
    groups,
    f_names,
    f_list,
    num_fixed: m,
    fixed_perm,
    matchers,
    num_fun_types,
    fun_perm,
    member_fixed: qss,
    f_depth,
    check_ownership: true,
  })
}

// ---------------------------------------------------------------------------
// The transport
// ---------------------------------------------------------------------------

/// A functional's telescope after its fixed parameters (`phiF`, `λ` when
/// `lam`; `phiFTy`, the same telescope in its type, `∀`): the indices, the
/// major and (at depth `arity + 1`) the recursion's own dictionary, whose
/// binder is owned in the value only.
fn phi_functional(
  tm: &mut TState,
  l: &StructLayout<'_>,
  lam: bool,
  depth: usize,
  arity: usize,
  e: &Expr,
) -> R<Expr> {
  let (bs, body) =
    if lam { peel_lams(depth, e) } else { peel_foralls(depth, e) };
  let go = Go { l, fuel: TRANSPORT_FUEL };
  let mut ctx = SCtx::default();
  let mut bs2: Vec<Binder> = Vec::with_capacity(bs.len());
  for (i, (nm, t, bi)) in bs.into_iter().enumerate() {
    let dict = depth == arity.saturating_add(1) && i == arity;
    let t2 = if dict {
      phi_s_dict_type(tm, go, &ctx, &t)?
    } else {
      go.run(tm, &ctx, &t)?
    };
    bs2.push((nm, t2, bi));
    ctx.push(&t, dict && lam);
  }
  let b = go.run(tm, &ctx, &body)?;
  Ok(if lam { mk_lams(&bs2, b) } else { mk_foralls(&bs2, b) })
}

/// The regeneration of a carried `member.eq_def` of a repacked group
/// ([`regenerate_structural_eq`] at the member's recursive binder), over the
/// transported declarations `const_of`.
fn regenerate_lemma(
  tm: &mut TState,
  l: &StructLayout<'_>,
  members: &[Decl],
  const_of: ConstOf<'_>,
  d: &Decl,
  new_name: &Name,
) -> R<Decl> {
  let Some(member) = members
    .iter()
    .find(|m| eq_def_name_eq(&d.name, &mk_str(&m.name, "eq_def")))
  else {
    return Err("structural eq_def: not a member unfolding theorem".into());
  };
  let sh = member_shape(member)?;
  let Some(a) = l.aux.get(&sh.brec_on_name) else {
    return Err("structural eq_def: no block layout".into());
  };
  let g = tm_idx(&l.groups, a.pos, "structural eq_def: the member's group")?;
  let pos = l
    .num_params
    .saturating_add(l.num_motives)
    .saturating_add(g.arity)
    .saturating_sub(1);
  let Some(major) = sh.brec_args.get(pos) else {
    return Err("structural eq_def: no recursive argument".into());
  };
  let Some(i) = bvar_idx(&strip_mdata(major)) else {
    return Err("structural eq_def: recursive argument is not a binder".into());
  };
  if !(sh.lets <= i && i - sh.lets < sh.lams) {
    return Err(
      "structural eq_def: recursive binder lies outside the member telescope"
        .into(),
    );
  }
  regenerate_structural_eq(
    tm,
    const_of,
    member,
    d,
    new_name,
    sh.lams - 1 - (i - sh.lets),
  )
}

/// `transportStructural`: transport a structural clique: the functionals
/// (`_f`), the below matchers, the members, and the carried equation lemmas
/// (`lemmas`, each with its output name). `family` is the block's
/// authenticated `below`/`brecOn` family ([`family_candidates`]). Fails (and
/// the caller keeps the baseline) on anything outside the grammar, including
/// a `below` dictionary or `brecOn` application the recursion does not own
/// (see "Ownership" in the module documentation).
pub fn transport_structural(
  tm: &mut TState,
  members: &[Decl],
  aux: &[Decl],
  sigma: &[usize],
  const_of: ConstOf<'_>,
  family: FxHashSet<Name>,
  lemmas: &[(Decl, Name)],
  force_ownership: bool,
) -> R<Vec<Transported>> {
  let mut l = struct_layout(members, aux, sigma, const_of, family)?;
  // the transport rewrites the encoding's constants (`aux`) and reorders the
  // calls to the functionals: a functional outside `aux` would keep Lean's
  // telescope while its calls are reordered
  if let Some(f) = l.f_list.iter().find(|f| !aux.iter().any(|d| d.name == **f))
  {
    return Err(format!(
      "transportStructural: the functional {} is not one of the encoding's constants",
      name_to_string(f)
    ));
  }
  l.check_ownership = force_ownership || !members.iter().all(|d| d.is_thm);
  // `brecOn` of the block: at the members' roots only
  if l.check_ownership {
    let brec_on = |c: &Name| l.is_brec_on_const(c);
    let outside = |d: &Decl| {
      format!(
        "grammar: a brecOn application of the block outside a member's root \
         (in {})",
        name_to_string(&d.name)
      )
    };
    for d in aux {
      if mentions_where(&brec_on, &d.typ) || mentions_where(&brec_on, &d.value)
      {
        return Err(outside(d));
      }
    }
    for d in members {
      if !(!mentions_where(&brec_on, &d.typ) && l.brec_on_count(&d.value) == 1)
      {
        return Err(outside(d));
      }
    }
  }
  let empty = SCtx::default();
  let phi = |tm: &mut TState, x: &Expr| phi_sc(tm, &l, &empty, x);
  let mut out: Vec<Transported> = Vec::new();
  for d in aux {
    if l.f_names.contains(&d.name) {
      let m = l.num_fixed;
      // the dictionary is the binder after the group's indices and major, in
      // the functional's own telescope (a member may pass it eta-reduced)
      let Some(&(_, arity)) = l.f_depth.get(&d.name) else {
        return Err(format!(
          "structLayout: the functional {} has no recorded telescope",
          name_to_string(&d.name)
        ));
      };
      let depth = arity.saturating_add(1);
      let typ = with_reordered_binders2(
        tm,
        false,
        m,
        &l.fixed_perm,
        &d.typ,
        &phi,
        &|tm, x| phi_functional(tm, &l, false, depth, arity, x),
      )?;
      let value = with_reordered_binders2(
        tm,
        true,
        m,
        &l.fixed_perm,
        &d.value,
        &phi,
        &|tm, x| phi_functional(tm, &l, true, depth, arity, x),
      )?;
      out.push(Transported::ok(Decl { typ, value, ..d.clone() }));
    } else if l.matchers.contains_key(&d.name) {
      let m = l.num_fun_types;
      let typ =
        with_reordered_binders(tm, false, m, &l.fun_perm, &d.typ, &phi)?;
      let value =
        with_reordered_binders(tm, true, m, &l.fun_perm, &d.value, &phi)?;
      out.push(Transported::ok(Decl { typ, value, ..d.clone() }));
    } else {
      let typ = phi(tm, &d.typ)?;
      let value = phi(tm, &d.value)?;
      out.push(Transported::ok(Decl { typ, value, ..d.clone() }));
    }
  }
  for d in members {
    let (ps, b1) = peel_lams(lam_arity(&d.value), &d.value);
    let mut ctx = SCtx::default();
    let mut ps2: Vec<Binder> = Vec::with_capacity(ps.len());
    for (nm, t, bi) in ps {
      if l.check_ownership && l.is_below_ty(&t) {
        return Err("grammar: a member parameter of a below type".into());
      }
      ps2.push((nm, phi_sc(tm, &l, &ctx, &t)?, bi));
      ctx.push(&t, false);
    }
    let (ls, b2) = peel_lets(l.num_fun_types, &b1);
    let (ls, b2) = reorder_lets(&l.fun_perm, &ls, &b2)?;
    let mut ls2: Lets = Vec::with_capacity(ls.len());
    for (nm, t, v) in ls {
      let t2 = phi_sc(tm, &l, &ctx, &t)?;
      let v2 = phi_sc(tm, &l, &ctx, &v)?;
      ls2.push((nm, t2, v2));
      ctx.push(&t, false);
    }
    let body = phi_sc(tm, &l, &ctx, &b2)?;
    let typ = phi(tm, &d.typ)?;
    out.push(Transported::ok(Decl {
      typ,
      value: mk_lams(&ps2, mk_lets(&ls2, body)),
      ..d.clone()
    }));
  }
  if lemmas.is_empty() {
    return Ok(out);
  }
  // Regeneration sees exactly the transported members/functionals, before
  // the encoding constants get canonical names. Source declarations retain
  // all metadata; the override changes only the produced type/value.
  let targets: Vec<Decl> = out.iter().map(|t| t.decl.clone()).collect();
  let target_const = |n: &Name| -> Option<ConstantInfo> {
    let ci = const_of(n)?;
    match (targets.iter().find(|d| eq_def_name_eq(&d.name, n)), ci) {
      (Some(d), ConstantInfo::DefnInfo(mut v)) => {
        v.cnst.typ = d.typ.clone();
        v.value = d.value.clone();
        Some(ConstantInfo::DefnInfo(v))
      },
      (Some(d), ConstantInfo::ThmInfo(mut v)) => {
        v.cnst.typ = d.typ.clone();
        v.value = d.value.clone();
        Some(ConstantInfo::ThmInfo(v))
      },
      (_, ci) => Some(ci),
    }
  };
  // the carried lemmas are transported without ownership (Lean's `Lp`); the
  // layout is otherwise the same
  let lp = StructLayout { check_ownership: false, ..l };
  for (d, nn) in lemmas {
    let enc = |c: &Name| lp.is_encoding_const(c);
    if lp.repacks()
      && (mentions_where(&enc, &d.typ) || mentions_where(&enc, &d.value))
    {
      // Keep the original refusal, including its text, unless every branch
      // of the replacement proof was constructed and checked by conversion.
      let Ok(regenerated) =
        regenerate_lemma(tm, &lp, members, &target_const, d, nn)
      else {
        return Err(format!(
          "grammar: the carried equation lemma {} unfolds a member through \
           the encoding of a repacked group (brecOn.go/brecOn.eq and packed \
           values the transport does not re-associate)",
          name_to_string(&d.name)
        ));
      };
      out.push(Transported::ok(regenerated));
    } else {
      let typ = phi_sc(tm, &lp, &empty, &d.typ)?;
      let value = phi_sc(tm, &lp, &empty, &d.value)?;
      out.push(Transported::ok(Decl {
        name: nn.clone(),
        typ,
        value,
        ..d.clone()
      }));
    }
  }
  Ok(out)
}

#[cfg(test)]
mod tests {
  use rustc_hash::FxHashSet;

  use ix_common::env::{
    BinderInfo, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal,
    Expr, InductiveVal, Name, RecursorVal, ReducibilityHints,
  };

  use super::{
    ElimShape, MatcherShape, SCtx, block_of, elim_shape_of, family_candidates,
    is_matcher_name, is_recursor_def, matcher_shape, reorder_lets,
    struct_layout, transport_structural, under_family,
  };
  use crate::compile::pass3::clique::basic::{
    Decl, TState, bvar, cnst, dotted, lvl_one, mk_app_n, mk_str, n_pprod,
    n_pprod_mk, proj, sort0,
  };
  use crate::compile::pass3::expr::nat;

  fn c(s: &str) -> Expr {
    cnst(&dotted(s), &[])
  }

  fn app(f: Expr, a: Expr) -> Expr {
    Expr::app(f, a)
  }

  fn lam(x: &str, t: Expr, b: Expr) -> Expr {
    Expr::lam(dotted(x), t, b, BinderInfo::Default)
  }

  fn pi(x: &str, t: Expr, b: Expr) -> Expr {
    Expr::all(dotted(x), t, b, BinderInfo::Default)
  }

  fn cval(n: &str, typ: Expr) -> ConstantVal {
    ConstantVal { name: dotted(n), level_params: vec![], typ }
  }

  fn defn(n: &str, typ: Expr, value: Expr) -> ConstantInfo {
    ConstantInfo::DefnInfo(DefinitionVal {
      cnst: cval(n, typ),
      value,
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![dotted(n)],
    })
  }

  fn induct(n: &str, is_rec: bool) -> ConstantInfo {
    ConstantInfo::InductInfo(InductiveVal {
      cnst: cval(n, sort0()),
      num_params: nat(0),
      num_indices: nat(0),
      all: vec![dotted(n)],
      ctors: vec![],
      num_nested: nat(0),
      is_rec,
      is_unsafe: false,
      is_reflexive: false,
    })
  }

  fn recursor(n: &str) -> ConstantInfo {
    ConstantInfo::RecInfo(RecursorVal {
      cnst: cval(n, sort0()),
      all: vec![],
      num_params: nat(0),
      num_indices: nat(0),
      num_motives: nat(1),
      num_minors: nat(0),
      rules: vec![],
      k: false,
      is_unsafe: false,
    })
  }

  fn decl(ci: &ConstantInfo) -> Decl {
    Decl::of_constant_info(ci).expect("a definition")
  }

  fn lookup(
    env: &[ConstantInfo],
  ) -> impl Fn(&Name) -> Option<ConstantInfo> + '_ {
    move |n| env.iter().find(|ci| ci.get_name() == n).cloned()
  }

  fn names(xs: &[&str]) -> FxHashSet<Name> {
    xs.iter().map(|x| dotted(x)).collect()
  }

  // ------------------------------------------------------------------
  // Matchers
  // ------------------------------------------------------------------

  /// `motive : D → Sort 0`
  fn motive_ty() -> Expr {
    pi("d", c("D"), sort0())
  }

  /// `h : ∀ y : E, motive (C y)`, under `motive` and the discriminant.
  fn alt_ty() -> Expr {
    pi("y", c("E"), app(bvar(2), app(c("C"), bvar(0))))
  }

  /// `binder (p : param) (motive) (d : D) (h), body`.
  fn tele(
    binder: fn(&str, Expr, Expr) -> Expr,
    param: Expr,
    body: Expr,
  ) -> Expr {
    binder(
      "p",
      param,
      binder(
        "motive",
        motive_ty(),
        binder("d", c("D"), binder("h", alt_ty(), body)),
      ),
    )
  }

  /// A matcher `p motive d h`, its value `λ (p : value_param) motive d h.
  /// body`.
  fn matcher(name: &str, value_param: Expr, body: Expr) -> ConstantInfo {
    defn(
      name,
      tele(pi, c("P"), app(bvar(2), bvar(1))),
      tele(lam, value_param, body),
    )
  }

  fn cases_body(head: &str) -> Expr {
    mk_app_n(c(head), &[bvar(2), bvar(1), bvar(0)])
  }

  fn matcher_env() -> Vec<ConstantInfo> {
    // `D.casesOn : ∀ (motive : D → Sort 0) (t : D) (mk : ∀ y, motive (C y)),
    // motive t`
    let cases_ty = pi(
      "motive",
      motive_ty(),
      pi("t", c("D"), pi("mk", alt_ty(), app(bvar(2), bvar(1)))),
    );
    let cases_value = lam(
      "motive",
      motive_ty(),
      lam(
        "t",
        c("D"),
        lam("mk", alt_ty(), mk_app_n(c("D.rec"), &[bvar(2), bvar(1), bvar(0)])),
      ),
    );
    vec![
      induct("D", false),
      recursor("D.rec"),
      defn("D.casesOn", cases_ty.clone(), c("opaque")),
      // a sparse `casesOn`: a definition applying a recursor
      defn("sparse", cases_ty, cases_value),
      matcher("f.match_1", c("P"), cases_body("D.casesOn")),
      matcher("f.match_2", c("P"), cases_body("Q")),
      matcher(
        "f.match_3",
        c("P"),
        app(cases_body("D.casesOn"), c("f.match_3")),
      ),
      matcher("f.match_4", c("P2"), cases_body("D.casesOn")),
      matcher(
        "f.match_5",
        c("P"),
        mk_app_n(c("f.match_1"), &[bvar(3), bvar(2), bvar(1), bvar(0)]),
      ),
      matcher("f.match_6", c("P"), cases_body("sparse")),
    ]
  }

  #[test]
  fn matcher_shape_reads_the_declaration() {
    let env = matcher_env();
    let env = lookup(&env);
    let get = |n: &str| decl(&env(&dotted(n)).expect("in the environment"));
    let none = |_: &Name| false;
    let shape = MatcherShape {
      arity: 4,
      motive: 1,
      discrs: 1,
      domains: vec![c("P"), motive_ty(), c("D"), alt_ty()],
    };
    assert_eq!(
      elim_shape_of(&env, &dotted("D.casesOn")),
      Some(ElimShape {
        arity: 3,
        alts: vec![None, None, Some(1)],
        motives: vec![(0, 1)]
      })
    );
    let m1 = get("f.match_1");
    assert_eq!(matcher_shape(&env, &none, 1, &m1), Some(shape.clone()));
    // the permuted arguments are parameters before the motive
    assert_eq!(matcher_shape(&env, &none, 0, &m1), None);
    assert_eq!(matcher_shape(&env, &none, 2, &m1), None);
    // look-alikes: a body that is not an eliminator, a recursive value, a
    // retyped binder, a declaration other than the input's
    assert_eq!(matcher_shape(&env, &none, 1, &get("f.match_2")), None);
    assert_eq!(matcher_shape(&env, &none, 1, &get("f.match_3")), None);
    assert_eq!(matcher_shape(&env, &none, 1, &get("f.match_4")), None);
    let other = Decl { typ: c("P"), ..m1.clone() };
    assert_eq!(matcher_shape(&env, &none, 1, &other), None);
    let thm = Decl { is_thm: true, ..m1 };
    assert_eq!(matcher_shape(&env, &none, 1, &thm), None);
    // an earlier accepted matcher counts as an eliminator
    let m5 = get("f.match_5");
    assert_eq!(matcher_shape(&env, &none, 1, &m5), None);
    let first = |n: &Name| *n == dotted("f.match_1");
    assert_eq!(matcher_shape(&env, &first, 1, &m5), Some(shape.clone()));
    // a recursor-based definition (a sparse `casesOn`)
    assert!(is_recursor_def(&env, &dotted("sparse")));
    assert!(!is_recursor_def(&env, &dotted("D.casesOn")));
    assert_eq!(matcher_shape(&env, &none, 1, &get("f.match_6")), Some(shape));
    // the name is only a pre-filter
    assert!(is_matcher_name(&dotted("f.match_1")));
    assert!(!is_matcher_name(&dotted("f.matcher")));
    assert!(!is_matcher_name(&Name::num(dotted("f.match_1"), nat(1))));
  }

  #[test]
  fn matcher_shape_lets_in_the_parameters() {
    // `∀ (p : P), let q : Q := v; ∀ motive d h, motive d`
    let tele_let = |binder: fn(&str, Expr, Expr) -> Expr, body: Expr| {
      binder(
        "p",
        c("P"),
        Expr::letE(
          dotted("q"),
          c("Q"),
          c("v"),
          binder(
            "motive",
            motive_ty(),
            binder("d", c("D"), binder("h", alt_ty(), body)),
          ),
          false,
        ),
      )
    };
    let mut env = matcher_env();
    env.push(defn(
      "g.match_1",
      tele_let(pi, app(bvar(2), bvar(1))),
      tele_let(lam, cases_body("D.casesOn")),
    ));
    let env = lookup(&env);
    let d = decl(&env(&dotted("g.match_1")).expect("in the environment"));
    let none = |_: &Name| false;
    assert_eq!(
      matcher_shape(&env, &none, 1, &d),
      Some(MatcherShape {
        arity: 4,
        motive: 1,
        discrs: 1,
        domains: vec![c("P"), motive_ty(), c("D"), alt_ty()],
      })
    );
    assert_eq!(matcher_shape(&env, &none, 2, &d), None);
  }

  // ------------------------------------------------------------------
  // The block and its family
  // ------------------------------------------------------------------

  #[test]
  fn family_membership_and_the_block() {
    let family = names(&["T.below", "T.brecOn", "T.brecOn.go"]);
    assert!(under_family(&family, &dotted("T.brecOn.go")));
    assert!(under_family(&family, &dotted("T.brecOn.eq")));
    assert!(under_family(&family, &dotted("T.below.casesOn")));
    assert!(under_family(&family, &Name::num(dotted("T.brecOn"), nat(3))));
    assert!(!under_family(&family, &dotted("T")));
    assert!(!under_family(&family, &dotted("T.below_1")));
    assert!(!under_family(&family, &Name::anon()));

    let env = vec![
      induct("T", true),
      recursor("T.rec"),
      defn("T.brecOn.go", sort0(), sort0()),
      induct("U", false),
      recursor("U.rec"),
      induct("V", true),
    ];
    let env = lookup(&env);
    let brec = dotted("T.brecOn");
    let (aux, p, k, arities) =
      block_of(&env, &names(&["T.below", "T.brecOn"]), &brec)
        .expect("an authenticated block");
    assert_eq!((p, k, arities), (0, 1, vec![1]));
    assert_eq!(aux.len(), 2);
    assert!(aux.get(&brec).is_some_and(|a| a.is_brec_on && a.pos == 0));
    assert_eq!(
      block_of(&env, &names(&["T.below"]), &brec).map(|_| ()),
      Err(
        "T.brecOn: not in the block's authenticated below/brecOn family"
          .to_string()
      )
    );
    assert_eq!(
      block_of(&env, &names(&["T.brecOn"]), &brec).map(|_| ()),
      Err(
        "T.below: not in the block's authenticated below/brecOn family".into()
      )
    );
    assert_eq!(
      block_of(&env, &names(&["U.below", "U.brecOn"]), &dotted("U.brecOn"))
        .map(|_| ()),
      Err(
        "U.brecOn: the inductive is not recursive (Lean generates no \
         below/brecOn family)"
          .to_string()
      )
    );
    assert_eq!(
      block_of(&env, &names(&["V.below", "V.brecOn"]), &dotted("V.brecOn"))
        .map(|_| ()),
      Err("V.rec: no recursor".into())
    );
    assert_eq!(
      block_of(&env, &family, &dotted("W.brecOn")).map(|_| ()),
      Err("W.brecOn: not the brecOn of an inductive".into())
    );
    // the candidates: the heads, then the helpers the input has
    assert_eq!(
      family_candidates(&env, &brec),
      Some((
        vec![dotted("T")],
        vec![dotted("T.below"), brec.clone(), dotted("T.brecOn.go")]
      ))
    );
    assert_eq!(family_candidates(&env, &dotted("U.brecOn")), None);
    assert_eq!(family_candidates(&env, &dotted("W.brecOn")), None);
  }

  // ------------------------------------------------------------------
  // Contexts and telescopes
  // ------------------------------------------------------------------

  #[test]
  fn context_hash_is_the_running_fold() {
    let entries = vec![(c("A"), false), (c("B"), true), (bvar(0), false)];
    let mut ctx = SCtx::default();
    assert_eq!(ctx.hash, SCtx::fold_hash(&[]));
    for (t, o) in &entries {
      ctx.push(t, *o);
      assert_eq!(ctx.hash, SCtx::fold_hash(&ctx.entries));
    }
    assert_eq!(ctx.hash, SCtx::of_array(&entries).hash);
    assert_eq!(
      ctx.hash,
      SCtx::default()
        .pushed(&c("A"), false)
        .pushed(&c("B"), true)
        .pushed(&bvar(0), false)
        .hash
    );
    // the ownership and the order are part of the hash
    let flipped = vec![(c("A"), false), (c("B"), false), (bvar(0), false)];
    assert_ne!(ctx.hash, SCtx::fold_hash(&flipped));
    let swapped = vec![(c("B"), true), (c("A"), false), (bvar(0), false)];
    assert_ne!(ctx.hash, SCtx::fold_hash(&swapped));
    // `bvar i` is the `i`-th entry from the end
    assert_eq!(ctx.get(0), Some(&(bvar(0), false)));
    assert_eq!(ctx.get(1), Some(&(c("B"), true)));
    assert_eq!(ctx.get(3), None);
  }

  #[test]
  fn reordered_lets() {
    // `let a : A := x; let b : B := y; F a b` ↦ `let b; let a; F a b`
    let ls = vec![(dotted("a"), c("A"), c("x")), (dotted("b"), c("B"), c("y"))];
    let body = mk_app_n(c("F"), &[bvar(1), bvar(0)]);
    let (ls2, body2) = reorder_lets(&[1, 0], &ls, &body).expect("independent");
    assert_eq!(ls2, vec![ls[1].clone(), ls[0].clone()]);
    assert_eq!(body2, mk_app_n(c("F"), &[bvar(0), bvar(1)]));
    let dep = vec![
      (dotted("a"), c("A"), c("x")),
      (dotted("b"), app(c("B"), bvar(0)), c("y")),
    ];
    assert_eq!(
      reorder_lets(&[1, 0], &dep, &body),
      Err("a let type mentions an earlier let".to_string())
    );
    assert_eq!(
      reorder_lets(&[0, 0], &ls, &body),
      Err("reorderLets: the order is not a permutation".to_string())
    );
  }

  // ------------------------------------------------------------------
  // A small structural transport
  // ------------------------------------------------------------------

  fn pprod(a: Expr, b: Expr) -> Expr {
    mk_app_n(cnst(&n_pprod(), &[lvl_one(), lvl_one()]), &[a, b])
  }

  /// `T.below motive x`, `x` the innermost binder.
  fn below(motive: &Expr) -> Expr {
    mk_app_n(c("T.below"), &[motive.clone(), bvar(0)])
  }

  /// The clique `f, g : T → A, B` of one group over `T`, Lean's packing
  /// `PProd l r` (the members' order `f, g` or `g, f`): the members, the
  /// functionals.
  fn clique(swapped: bool) -> (Vec<Decl>, Vec<Decl>) {
    let (l, r) = if swapped { ("B", "A") } else { ("A", "B") };
    let (fl, fr) = if swapped { ("g._f", "f._f") } else { ("f._f", "g._f") };
    let motive = lam("x", c("T"), pprod(c(l), c(r)));
    let call = |f: &str| mk_app_n(c(f), &[bvar(1), bvar(0)]);
    let tuple = mk_app_n(
      cnst(&n_pprod_mk(), &[lvl_one(), lvl_one()]),
      &[c(l), c(r), call(fl), call(fr)],
    );
    let functional = lam("x", c("T"), lam("f", below(&motive), tuple));
    let brec_on =
      mk_app_n(c("T.brecOn"), &[motive.clone(), bvar(0), functional]);
    let member = |n: &str, ty: &str, field: usize| Decl {
      name: dotted(n),
      level_params: vec![],
      typ: pi("x", c("T"), c(ty)),
      value: lam("x", c("T"), proj(&n_pprod(), field, brec_on.clone())),
      is_thm: false,
    };
    let fa = if swapped { 1 } else { 0 };
    let members = vec![member("f", "A", fa), member("g", "B", 1 - fa)];
    let func = |n: &str, ty: &str, v: &str| Decl {
      name: dotted(n),
      level_params: vec![],
      typ: pi("x", c("T"), pi("f", below(&motive), c(ty))),
      value: lam("x", c("T"), lam("f", below(&motive), c(v))),
      is_thm: false,
    };
    (members, vec![func("f._f", "A", "a"), func("g._f", "B", "b")])
  }

  #[test]
  fn structural_transport_repacks_a_group() {
    let env = vec![induct("T", true), recursor("T.rec")];
    let env = lookup(&env);
    let family = names(&["T.below", "T.brecOn"]);
    let (members, aux) = clique(false);
    let layout = struct_layout(&members, &aux, &[1, 0], &env, family.clone())
      .expect("a structural layout");
    assert!(layout.repacks());
    assert_eq!(layout.groups.len(), 1);
    assert!(layout.groups.first().is_some_and(|g| g.perm == vec![1, 0]));
    assert!(layout.is_encoding_const(&dotted("f._f")));
    assert!(layout.is_encoding_const(&mk_str(&dotted("T.brecOn"), "go")));
    assert!(!layout.is_encoding_const(&dotted("T")));
    assert!(!layout.is_encoding_const(&dotted("A")));

    // σ = [1, 0]: the packing becomes `PProd B A`, the members project the
    // other component
    let mut tm = TState::default();
    let out = transport_structural(
      &mut tm,
      &members,
      &aux,
      &[1, 0],
      &env,
      family.clone(),
      &[],
      false,
    )
    .expect("transported");
    let (want_members, want_aux) = clique(true);
    let got: Vec<Decl> = out.iter().map(|t| t.decl.clone()).collect();
    let want: Vec<Decl> = want_aux.into_iter().chain(want_members).collect();
    assert_eq!(got.len(), want.len());
    for (g, w) in got.iter().zip(&want) {
      assert_eq!((&g.name, &g.typ, &g.value), (&w.name, &w.typ, &w.value));
    }
    assert!(out.iter().all(|t| t.fallback.is_none()));

    // the identity moves nothing
    let mut tm = TState::default();
    let out = transport_structural(
      &mut tm,
      &members,
      &aux,
      &[0, 1],
      &env,
      family.clone(),
      &[],
      false,
    )
    .expect("transported");
    let same: Vec<Decl> = aux.iter().chain(&members).cloned().collect();
    for (g, w) in out.iter().zip(&same) {
      assert_eq!((&g.decl.typ, &g.decl.value), (&w.typ, &w.value));
    }

    // a `brecOn` of the block outside a member's root is refused
    let stray = Decl {
      name: dotted("h"),
      level_params: vec![],
      typ: sort0(),
      value: c("T.brecOn"),
      is_thm: false,
    };
    let aux2: Vec<Decl> = aux.iter().cloned().chain([stray]).collect();
    assert_eq!(
      transport_structural(
        &mut TState::default(),
        &members,
        &aux2,
        &[1, 0],
        &env,
        family,
        &[],
        false
      )
      .map(|_| ()),
      Err(
        "grammar: a brecOn application of the block outside a member's root \
         (in h)"
          .to_string()
      )
    );
    // an unauthenticated family
    assert_eq!(
      struct_layout(&members, &aux, &[1, 0], &env, names(&["T.below"]))
        .map(|_| ()),
      Err(
        "T.brecOn: not in the block's authenticated below/brecOn family"
          .to_string()
      )
    );
  }
}
