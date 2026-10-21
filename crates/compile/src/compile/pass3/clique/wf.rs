//! The well-founded transport (a port of `Ix/Compile/Pass/Clique/WF.lean`,
//! `WFSchema.lean`, `WFMatcher.lean` and `WFConjugation.lean`).
//!
//! Lean's encoding (`Elab/PreDefinition/WF`, Lean 4.34.1):
//!
//! * `f₀._mutual : ∀ fixed, (x : α) → C x` with `α = PSum D₀ (… D_{n-1})` in
//!   Lean's clique order and `C` a `mkCodomain` case tree; the fixed
//!   parameters in the first function's order;
//! * its value `λ fixed. WellFounded.fix α (λ x. C x) rel wf F` or
//!   `λ fixed. WellFounded.Nat.fix α (λ x. C x) measure F`, where `rel`
//!   (`(invImage m inst).1`) and `measure` carry the per-function measures in
//!   a case tree over `α`, and `F = λ x a. tree` is `processSumCasesOn`'s
//!   refinement tree whose leaves are the functions' bodies, recursive calls
//!   `a (inj_j ⟨args⟩) h`;
//! * the decreasing proofs `f₀._mutual._proof_k : ∀ ctx, rel (inj_j y) (inj_i
//!   x)` (definitions; for theorems they stay inline), whose bodies mention
//!   the packing in copies of their goal (`id`, motives);
//! * the members `f_i := λ ps. f₀._mutual fixed (inj_i ⟨varying⟩)`.
//!
//! The layout ([`wf_layout`]), the proofs' fixed-argument scan, the prologue
//! and epilogue the well-founded and `partial_fixpoint` transports share
//! ([`fixed_proof_perms`], [`number_proofs`]) and the pieces of the packed
//! equation lemma's regeneration are `WF.lean`'s. The transport finds the
//! encoding by ownership, from the exact root of `f₀._mutual`
//! ([`decode_wf_root`], `WFSchema.lean`), and moves only what that root owns:
//! its packing, codomain and measure, its refinement tree, the recursive
//! binder and the recursive calls through it, the complete root obligations,
//! and the decoded calls of the packed function and of its abstracted proofs
//! elsewhere (`WFConjugation.lean`; a `match` on a `Nat` is followed only
//! through a declaration-checked dispatcher, `WFMatcher.lean`). It never
//! recognises the packing by its shape elsewhere in a term, so user values of
//! the packing's type are left alone. [`transport_wf`] runs it over a whole
//! clique.
//!
//! Every refusal is an error with the Lean text; no index is unchecked.

use std::ops::ControlFlow;
use std::slice;

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::env::{BinderInfo, Expr, ExprData, Level, Name, NameData};

use super::basic::{
  ConstOf, Decl, Local, R, TState, TransportMemo, abstract_fvars,
  alpha_eq_skip_mdata, bvar, cnst, const_app, const_occurrences, dotted,
  eq_sorted, exprs, extract, fold_distinct, forall_arity, fvar, inst_locals,
  instantiate_rev, inv_perm, is_bvar, is_perm, lam_arity, lift_loose,
  memo_transport, mentions_fvar, mk_app_n, mk_forall, mk_lambda, mk_str,
  n_psigma, name_to_string, no_dups, peel_foralls, peel_lams, proj,
  rename_consts, root_name, tm_idx,
};
use super::bounds::{TRANSPORT_FUEL, WF_DEPTH};
use super::packing::{
  PackKind, Spine, Tree, decode_inj, decode_spine, decode_tree,
  match_packing_leaves, mk_inj,
};
use super::telescope::{
  close_binders, id_perm, n_nat_succ, open_binders, reorder,
  with_reordered_binders2,
};
use crate::compile::pass3::expr::{
  get_app_fn_args, nat_usize, strip_mdata, subst_levels,
};

// ---------------------------------------------------------------------------
// The layout (`WF.lean`)
// ---------------------------------------------------------------------------

/// What `Φ_σ` needs to know about a well-founded clique (`WFLayout`).
#[derive(Clone, Debug)]
pub struct WfLayout {
  pub n: usize,
  /// Lean index ↦ canonical position
  pub sigma: Vec<usize>,
  pub mutual_name: Name,
  pub new_mutual_name: Name,
  pub num_fixed: usize,
  /// new fixed position `p` ↦ Lean's fixed position
  pub fixed_perm: Vec<usize>,
  /// Lean's summands `D_i`, from `f₀._mutual`'s type (the fixed parameters
  /// as loose variables)
  pub leaves: Vec<Expr>,
  /// abstracted proof ↦ the permutation of its leading fixed-parameter
  /// binders (empty when it uses none)
  pub proof_perm: FxHashMap<Name, Vec<usize>>,
  /// the packed function's equation lemmas carried with the clique: in the
  /// user region, an application of one re-enters the encoding region at its
  /// packed argument, as an application of the packed function does
  pub packed_lemmas: FxHashSet<Name>,
  /// per member (Lean's order): the member's parameter (outermost `0`) at
  /// each fixed position of its call of the packed function
  pub member_fixed: Vec<Vec<usize>>,
}

impl WfLayout {
  /// `WFLayout.isClique`: `s` is this clique's packing (its leaves match
  /// Lean's summands under one correspondence).
  pub fn is_clique(&self, s: &Spine) -> bool {
    s.size() == self.n
      && match_packing_leaves(&s.leaves, &self.leaves).is_some()
  }
}

/// `nInvImage`.
pub fn n_inv_image() -> Name {
  dotted("InvImage")
}

/// `nWFRelation`.
pub fn n_wf_relation() -> Name {
  dotted("WellFoundedRelation")
}

/// `Spine.typeM`: the packing type of a spine inside the transport. A
/// decoded spine (and any permutation of one) always has it; a spine without
/// leaves, or whose leaves and levels differ in number, is a refusal named by
/// `what`.
pub fn spine_type_m(s: &Spine, what: &str) -> R<Expr> {
  s.typ().ok_or_else(|| {
    format!(
      "{what}: the packing has no type (no leaves, or leaves and levels \
       differ in number)"
    )
  })
}

/// `sortIdxByKey`: the indices of `keys` sorted by their key, equal keys in
/// index order. The order is total on `(key, index)`, so the result is the
/// one sorted arrangement, Lean's `qsort` included.
pub fn sort_idx_by_key(keys: &[usize]) -> Vec<usize> {
  let mut pairs: Vec<(usize, usize)> = keys.iter().copied().zip(0..).collect();
  pairs.sort_unstable();
  pairs.into_iter().map(|(_, i)| i).collect()
}

/// `memberFixedArgs`: the fixed-parameter positions of a member's call of
/// `f₀._mutual` (for each fixed argument, the member's parameter it is,
/// outermost `0`) and the packed argument.
pub fn member_fixed_args(
  mutual_name: &Name,
  m: usize,
  member: &Decl,
) -> R<(Vec<usize>, Expr)> {
  let (ps, body) = peel_lams(lam_arity(&member.value), &member.value);
  let mn = name_to_string(&member.name);
  let not_packed =
    || format!("member {mn}: not an application of the packed function");
  let Some((h, _, args)) = const_app(&body) else { return Err(not_packed()) };
  if !(h == *mutual_name && args.len() == m + 1) {
    return Err(not_packed());
  }
  let mut qs = Vec::new();
  for j in 0..m {
    let Some(arg) = args.get(j) else { return Err(not_packed()) };
    match strip_mdata(arg).as_data() {
      ExprData::Bvar(b, _) => {
        let b = nat_usize(b);
        if b < ps.len() {
          qs.push(ps.len() - 1 - b);
        } else {
          return Err(format!("member {mn}: fixed argument out of scope"));
        }
      },
      _ => {
        return Err(format!(
          "member {mn}: a fixed argument is not a parameter"
        ));
      },
    }
  }
  if !no_dups(&qs) {
    return Err(format!(
      "member {mn}: distinct fixed parameters alias the same binder"
    ));
  }
  let Some(packed_arg) = args.get(m) else { return Err(not_packed()) };
  Ok((qs, packed_arg.clone()))
}

/// `wfLayout`: the layout of the clique `members` (Lean's order) packed by
/// `mut_decl`, under the permutation `sigma` (Lean index ↦ canonical
/// position), with the packed function renamed `new_mutual_name`.
pub fn wf_layout(
  members: &[Decl],
  mut_decl: &Decl,
  sigma: &[usize],
  new_mutual_name: &Name,
) -> R<WfLayout> {
  let bad = || "wfLayout: bad permutation".to_string();
  let n = members.len();
  if !(n >= 2 && sigma.len() == n && is_perm(sigma)) {
    return Err(bad());
  }
  let ar = forall_arity(&mut_decl.typ);
  if ar < 1 {
    return Err("wfLayout: the packed function has no argument".into());
  }
  let m = ar - 1;
  let (bs, _) = peel_foralls(ar, &mut_decl.typ);
  let Some((_, alpha, _)) = bs.get(m) else {
    return Err("wfLayout: no packed argument".into());
  };
  let Some(s) = decode_spine(PackKind::Psum, n, alpha) else {
    return Err(
      "wfLayout: the packed domain is not Lean's PSum packing".into(),
    );
  };
  let mut qss: Vec<Vec<usize>> = Vec::new();
  for (i, member) in members.iter().enumerate() {
    let (qs, arg) = member_fixed_args(&mut_decl.name, m, member)?;
    match decode_inj(n, &arg) {
      Some((_, j, _)) => {
        if j != i {
          return Err(format!(
            "wfLayout: member {i} injects at summand {j} (not Lean's order)"
          ));
        }
      },
      None => {
        return Err(format!(
          "wfLayout: member {i}'s argument is not an injection"
        ));
      },
    }
    qss.push(qs);
  }
  // Lean's fixed order is its first member's order
  let Some(q0) = qss.first() else { return Err(bad()) };
  if !eq_sorted(q0) {
    return Err(
      "wfLayout: the fixed parameters are not in the first member's order"
        .into(),
    );
  }
  // the canonical first member's order
  let Some(inv) = inv_perm(sigma) else { return Err(bad()) };
  let Some(&g) = inv.first() else { return Err(bad()) };
  let Some(qg) = qss.get(g) else { return Err(bad()) };
  // `qg` has one entry per fixed position (`member_fixed_args`)
  let fixed_perm = sort_idx_by_key(qg);
  Ok(WfLayout {
    n,
    sigma: sigma.to_vec(),
    mutual_name: mut_decl.name.clone(),
    new_mutual_name: new_mutual_name.clone(),
    num_fixed: m,
    fixed_perm,
    leaves: s.leaves,
    proof_perm: FxHashMap::default(),
    packed_lemmas: FxHashSet::default(),
    member_fixed: qss,
  })
}

/// `scanProofs`: for every application of an abstracted proof in the
/// (opened) value of `f₀._mutual`, the fixed parameters (by Lean position)
/// among its leading arguments, recorded at the first application met. The
/// walk visits each distinct subterm once, in first-occurrence pre-order
/// ([`fold_distinct`]); an application node is visited before its function
/// part, so the full argument list is the one recorded.
pub fn scan_proofs(
  proofs: &FxHashSet<Name>,
  fixed: &[Name],
  e: &Expr,
  initial: FxHashMap<Name, Vec<usize>>,
) -> FxHashMap<Name, Vec<usize>> {
  fold_distinct(e, initial, |mut acc, x| {
    if let ExprData::App(..) = x.as_data() {
      let (h, args) = get_app_fn_args(x);
      if let ExprData::Const(c, _, _) = h.as_data()
        && proofs.contains(c)
        && !acc.contains_key(c)
      {
        let positions = args
          .iter()
          .map_while(|a| match strip_mdata(a).as_data() {
            ExprData::Fvar(y, _) => fixed.iter().position(|z| z == y),
            _ => None,
          })
          .collect();
        acc.insert(c.clone(), positions);
      }
    }
    ControlFlow::Continue(acc)
  })
}

// ---------------------------------------------------------------------------
// The transport's outcome, and the steps both packed transports share
// ---------------------------------------------------------------------------

/// One constant's outcome (`Transported`).
#[derive(Clone, Debug)]
pub struct Transported {
  pub decl: Decl,
  /// `None`: transported; `Some(why)`: Lean's term kept (the faithful
  /// fallback), with the reason
  pub fallback: Option<String>,
}

impl Transported {
  /// A transported declaration (no fallback).
  pub fn ok(decl: Decl) -> Self {
    Transported { decl, fallback: None }
  }
}

/// The outcome of a packed transport, well-founded or `partial_fixpoint`
/// (`TransportOutput`).
#[derive(Clone, Debug)]
pub struct TransportOutput {
  pub decls: Vec<Transported>,
  /// Lean's constant ↦ its canonical name (the packed function, the
  /// renumbered proofs, the renamed lemmas)
  pub renames: Vec<(Name, Name)>,
}

/// The abstracted proofs' fixed parameters, as both packed transports
/// compute them before transporting anything (`FixedProofs`, from
/// [`fixed_proof_perms`]).
#[derive(Clone, Debug)]
pub struct FixedProofs {
  /// the abstracted proofs' names
  pub proof_names: FxHashSet<Name>,
  /// the packed function's fixed parameters, opened with fresh free
  /// variables (Lean's order)
  pub fixed: Vec<Local>,
  /// the packed function's value under them
  pub body: Expr,
  /// proof ↦ the fixed parameters (Lean position) among the leading
  /// arguments of its first application in `body` ([`scan_proofs`])
  pub uses: FxHashMap<Name, Vec<usize>>,
  /// proof ↦ the permutation of its leading fixed-parameter binders: their
  /// indices sorted by the new position of the fixed parameter each one is
  pub proof_perm: FxHashMap<Name, Vec<usize>>,
}

/// `fixedProofPerms`, the prologue of the packed transports
/// ([`transport_wf`], and the `partial_fixpoint` transport): open the
/// `num_fixed` fixed parameters of the packed function's value
/// `packed_value` (allocating their free variables), scan the abstracted
/// `proofs`' applications for the fixed parameters they receive, and order
/// each proof's leading fixed binders by the new fixed order `fixed_perm`
/// (new position ↦ Lean's position). `fixed_perm` not being a permutation of
/// the fixed positions, or a recorded position outside it, is a refusal
/// (neither happens for a layout's own permutation).
pub fn fixed_proof_perms(
  tm: &mut TState,
  proofs: &[Decl],
  num_fixed: usize,
  fixed_perm: &[usize],
  packed_value: &Expr,
) -> R<FixedProofs> {
  let proof_names: FxHashSet<Name> =
    proofs.iter().map(|proof| proof.name.clone()).collect();
  let (fixed, body) = open_binders(tm, true, num_fixed, packed_value)?;
  let fixed_names: Vec<Name> = fixed.iter().map(|x| x.fvar.clone()).collect();
  let uses =
    scan_proofs(&proof_names, &fixed_names, &body, FxHashMap::default());
  let Some(inverse) = inv_perm(fixed_perm) else {
    return Err(
      "clique transport: the fixed-parameter order is not a permutation".into(),
    );
  };
  let mut proof_perm: FxHashMap<Name, Vec<usize>> = FxHashMap::default();
  for (name, positions) in &uses {
    let keys: Option<Vec<usize>> =
      positions.iter().map(|&p| inverse.get(p).copied()).collect();
    let Some(keys) = keys else {
      return Err(format!(
        "clique transport: proof {} receives a fixed parameter outside the \
         fixed order",
        name_to_string(name)
      ));
    };
    proof_perm.insert(name.clone(), sort_idx_by_key(&keys));
  }
  Ok(FixedProofs { proof_names, fixed, body, uses, proof_perm })
}

/// `numberProofs`, the epilogue of the packed transports: number the
/// abstracted `proofs` `new_name._proof_{i+1}`, first those the transported
/// packed value `value` mentions, in first-occurrence order
/// ([`const_occurrences`]), then the others in `proofs` order; rename each
/// carried lemma `(lemma, name)` whose name changes; apply both renamings to
/// the name, type and value of every declaration of `output`; and list the
/// renames, the packed function `packed_name ↦ new_name` first, then the
/// proofs, then the lemmas.
pub fn number_proofs(
  output: Vec<Transported>,
  packed_name: &Name,
  new_name: &Name,
  proofs: &[Decl],
  lemmas: &[(Decl, Name)],
  value: &Expr,
) -> TransportOutput {
  let proof_names: FxHashSet<Name> =
    proofs.iter().map(|proof| proof.name.clone()).collect();
  let used = const_occurrences(&|n| proof_names.contains(n), value);
  let rest: Vec<Name> = proofs
    .iter()
    .map(|proof| proof.name.clone())
    .filter(|name| !used.contains(name))
    .collect();
  let numbered: Vec<(Name, Name)> = used
    .iter()
    .chain(&rest)
    .enumerate()
    .map(|(index, name)| {
      (name.clone(), mk_str(new_name, &format!("_proof_{}", index + 1)))
    })
    .collect();
  let lemma_renames: Vec<(Name, Name)> = lemmas
    .iter()
    .filter(|(declaration, name)| declaration.name != *name)
    .map(|(declaration, name)| (declaration.name.clone(), name.clone()))
    .collect();
  // later entries win, as Lean's `foldl insert`
  let names: FxHashMap<Name, Name> =
    numbered.iter().chain(&lemma_renames).cloned().collect();
  let get = |n: &Name| names.get(n).cloned();
  let decls = output
    .into_iter()
    .map(|item| Transported {
      decl: Decl {
        name: get(&item.decl.name).unwrap_or_else(|| item.decl.name.clone()),
        typ: rename_consts(&get, &item.decl.typ),
        value: rename_consts(&get, &item.decl.value),
        ..item.decl
      },
      fallback: item.fallback,
    })
    .collect();
  let mut renames = vec![(packed_name.clone(), new_name.clone())];
  renames.extend(numbered);
  renames.extend(lemma_renames);
  TransportOutput { decls, renames }
}

// ---------------------------------------------------------------------------
// The packed function's equation lemma
// ---------------------------------------------------------------------------
//
// Lean proves `f₀._mutual.eq_def : ∀ fixed x, f₀._mutual fixed x = T x` (the
// case tree `T` of the bodies, recursive calls through `f₀._mutual`) by
// `WellFounded.fix_eq` (or `Nat.fix_eq`) followed by a `simp` chain that
// pushes the recursion argument through the case tree. That chain's shape
// follows the packing node by node and is not transported. The canonical
// lemma keeps the transported statement, keeps Lean's `fix_eq` step, and
// replaces the chain by the step it computes, made explicit: a case split on
// the packed argument (`PSum.casesOn` over the canonical packing, then
// `PSigma.casesOn` over each summand's arguments), each leaf the `fix_eq`
// step at the constructor, which proves its case by conversion (β and ι).
// The proof is regenerated by a fixed term recipe; no tactic runs.

/// `stripId`: `@id T p ↦ p`.
pub fn strip_id(e: &Expr) -> Expr {
  match const_app(e) {
    Some((h, _, args)) => match args.as_slice() {
      [_, p] if h == dotted("id") => p.clone(),
      _ => e.clone(),
    },
    None => e.clone(),
  }
}

/// `eqDefFixStep`: the `fix_eq` step of Lean's packed equation lemma (the
/// first argument of its `Eq.trans`), opened at `xs` (the fixed parameters
/// in Lean's order, then the packed argument).
pub fn eq_def_fix_step(eq_def: &Decl, m: usize, xs: &[Expr]) -> R<Expr> {
  let (bs, body) = peel_lams(m + 1, &eq_def.value);
  if bs.len() != m + 1 {
    return Err(
      "eq_def: the proof does not bind the fixed parameters and the argument"
        .into(),
    );
  }
  let body = inst_locals(&body, xs);
  let not_trans =
    || "eq_def: the proof is not `Eq.trans (fix_eq …) …`".to_string();
  match const_app(&strip_id(&body)) {
    Some((h, _, args)) => match args.as_slice() {
      [_, _, _, _, step, _] if h == dotted("Eq.trans") => Ok(step.clone()),
      _ => Err(not_trans()),
    },
    None => Err(not_trans()),
  }
}

/// A term builder of the transport that may refuse (Lean's
/// `Expr → TM Expr`).
pub type ExprK<'a> = &'a dyn Fn(&mut TState, Expr) -> R<Expr>;

/// `splitPSigma`: split `major : ty` into its `PSigma` components and prove
/// the motive at `mk ⟨a⃗⟩` by `leaf`: `PSigma.casesOn` with motive
/// `λ t. motive (mk t)` at each `PSigma` level, `leaf (mk ⟨a⃗⟩)` at the atoms.
/// `motive` and `leaf` may refuse (they build injections, which can fail);
/// more than `fuel` nested levels is a refusal.
pub fn split_psigma(
  tm: &mut TState,
  motive: ExprK<'_>,
  leaf: ExprK<'_>,
  fuel: usize,
  ty: &Expr,
  mk: &dyn Fn(Expr) -> Expr,
  major: &Expr,
) -> R<Expr> {
  let Some(fuel) = fuel.checked_sub(1) else {
    return Err("eq_def: PSigma nesting bound exhausted".into());
  };
  if let Some((h, us, args)) = const_app(ty)
    && let ([u0, u1], [alpha, beta]) = (us.as_slice(), args.as_slice())
    && h == n_psigma()
  {
    let a = tm.fresh_fvar();
    let b = tm.fresh_fvar();
    let la = Local {
      fvar: a.clone(),
      user_name: root_name("a"),
      typ: alpha.clone(),
      bi: BinderInfo::Default,
    };
    let bty = match strip_mdata(beta).as_data() {
      ExprData::Lam(_, _, body, _, _) => instantiate_rev(body, &[fvar(&a)]),
      _ => Expr::app(beta.clone(), fvar(&a)),
    };
    let lb = Local {
      fvar: b.clone(),
      user_name: root_name("b"),
      typ: bty.clone(),
      bi: BinderInfo::Default,
    };
    let pair = |t: Expr| {
      mk_app_n(
        cnst(&dotted("PSigma.mk"), &us),
        &[alpha.clone(), beta.clone(), fvar(&a), t],
      )
    };
    let inner =
      split_psigma(tm, motive, leaf, fuel, &bty, &|t| mk(pair(t)), &fvar(&b))?;
    let t = tm.fresh_fvar();
    let lt = Local {
      fvar: t.clone(),
      user_name: root_name("t"),
      typ: ty.clone(),
      bi: BinderInfo::Default,
    };
    let mot = mk_lambda(&[lt], &motive(tm, mk(fvar(&t)))?);
    return Ok(mk_app_n(
      cnst(&dotted("PSigma.casesOn"), &[Level::zero(), u0.clone(), u1.clone()]),
      &[
        alpha.clone(),
        beta.clone(),
        mot,
        major.clone(),
        mk_lambda(&[la, lb], &inner),
      ],
    ));
  }
  leaf(tm, mk(major.clone()))
}

/// `onlyCalls`: `bvar d` occurs in `e` only as the head of an application (a
/// recursive call `a y h`), never passed on whole; `false` when `fuel` runs
/// out.
pub fn only_calls(fuel: usize, d: usize, e: &Expr) -> bool {
  let Some(fuel) = fuel.checked_sub(1) else { return false };
  match e.as_data() {
    ExprData::App(..) => {
      let (h, args) = get_app_fn_args(e);
      let head_ok = match h.as_data() {
        ExprData::Bvar(..) => true,
        _ => only_calls(fuel, d, &h),
      };
      head_ok
        && args
          .iter()
          .all(|x| !is_bvar(&strip_mdata(x), d) && only_calls(fuel, d, x))
    },
    ExprData::Bvar(..) => !is_bvar(e, d),
    ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
      only_calls(fuel, d, t) && only_calls(fuel, d + 1, b)
    },
    ExprData::LetE(_, t, v, b, _, _) => {
      only_calls(fuel, d, t)
        && only_calls(fuel, d, v)
        && only_calls(fuel, d + 1, b)
    },
    ExprData::Proj(_, _, x, _) | ExprData::Mdata(_, x, _) => {
      only_calls(fuel, d, x)
    },
    _ => true,
  }
}

/// `leafReduces`: a leaf of the packed function's case tree (`λ v a. E`)
/// whose recursion variable reaches the bodies only through `PSigma.casesOn`
/// layers (which the regenerated proof splits) and is used there only as
/// recursive calls: the functional applied at a constructor then reduces to
/// the statement's leaf by β and ι. A body that threads the recursion
/// variable through a `match` needs Lean's argument pushing, which is not
/// regenerated.
pub fn leaf_reduces(fuel: usize, e: &Expr) -> bool {
  let Some(fuel) = fuel.checked_sub(1) else { return false };
  let (bs, body) = peel_lams(lam_arity(e), e);
  if bs.is_empty() {
    return false;
  }
  if let Some((h, _, args)) = const_app(&body)
    && let [_, _, _, _, minor, major] = args.as_slice()
    && h == dotted("PSigma.casesOn")
    && is_bvar(&strip_mdata(major), 0)
  {
    return leaf_reduces(fuel, minor);
  }
  only_calls(TRANSPORT_FUEL, 0, &body)
}

// ---------------------------------------------------------------------------
// The exact root and the positions it relates (`WFSchema.lean`)
// ---------------------------------------------------------------------------

/// `applyWFCase`: a case function at an argument (β at a `λ`).
pub fn apply_wf_case(function: &Expr, argument: &Expr) -> Expr {
  match strip_mdata(function).as_data() {
    ExprData::Lam(_, _, body, _, _) => {
      instantiate_rev(body, slice::from_ref(argument))
    },
    _ => Expr::app(function.clone(), argument.clone()),
  }
}

/// `decodeWFCase`: permute only the case tree fed by this function's exact
/// input binder. The case alternatives and constant codomains/measures are
/// user syntax; in particular a constant codomain equal to the packing is
/// not permuted.
pub fn decode_wf_case(
  tm: &mut TState,
  spine: &Spine,
  sigma: &[usize],
  function: &Expr,
) -> R<Expr> {
  let (locals, body) = open_binders(tm, true, 1, function)?;
  let Some(argument) = locals.first() else {
    return Err("WF schema: missing case function argument".into());
  };
  let spine_type = spine_type_m(spine, "WF schema")?;
  if !alpha_eq_skip_mdata(&argument.typ, &spine_type) {
    return Err("WF schema: case function has a foreign domain".into());
  }
  let body2 = if !mentions_fvar(&argument.fvar, &body) {
    body
  } else {
    let Some(tree) = decode_tree(spine.size(), &body) else {
      return Err(
        "WF schema: input-dependent function is not a case tree".into(),
      );
    };
    let tree_type = spine_type_m(&tree.spine, "WF schema")?;
    if !(alpha_eq_skip_mdata(&tree_type, &spine_type)
      && alpha_eq_skip_mdata(&tree.major, &argument.expr())
      && tree.extras.is_empty())
    {
      return Err(
        "WF schema: case function has foreign entry identities".into(),
      );
    }
    if tree.leaves.iter().any(|l| mentions_fvar(&argument.fvar, l))
      || mentions_fvar(&argument.fvar, &tree.motive_body)
    {
      return Err(
        "WF schema: case function captures its input outside the decoded \
         major"
          .into(),
      );
    }
    let Some(value) = tree.permute(sigma).and_then(|t| t.build()) else {
      return Err("WF schema: case function reconstruction failed".into());
    };
    value
  };
  let Some(target) = spine.permute(sigma) else {
    return Err(
      "WF schema: case function domain does not take the permutation".into(),
    );
  };
  let target_type = spine_type_m(&target, "WF schema")?;
  close_binders(true, &[Local { typ: target_type, ..argument.clone() }], &body2)
}

/// The decoded root of `f₀._mutual` (`WFRootSchema`): the source and target
/// packings, codomains and measures, the fixpoint head, the source arguments
/// and their transported counterparts, and (for `WellFounded.fix`) the
/// relation.
#[derive(Clone, Debug)]
pub struct WfRootSchema {
  pub source_spine: Spine,
  pub target_spine: Spine,
  pub source_codomain: Expr,
  pub target_codomain: Expr,
  pub source_measure: Expr,
  pub target_measure: Expr,
  pub head: Expr,
  pub source_arguments: Vec<Expr>,
  pub target_arguments: Vec<Expr>,
  pub source_relation: Option<Expr>,
  pub target_relation: Option<Expr>,
}

impl WfRootSchema {
  /// `WFRootSchema.mapExpressions`: `f` applied to every expression of the
  /// schema but its head (spine leaves, not their levels).
  pub fn map_expressions(&self, f: &dyn Fn(&Expr) -> Expr) -> WfRootSchema {
    WfRootSchema {
      source_spine: self.source_spine.map_leaves(f),
      target_spine: self.target_spine.map_leaves(f),
      source_codomain: f(&self.source_codomain),
      target_codomain: f(&self.target_codomain),
      source_measure: f(&self.source_measure),
      target_measure: f(&self.target_measure),
      head: self.head.clone(),
      source_arguments: self.source_arguments.iter().map(f).collect(),
      target_arguments: self.target_arguments.iter().map(f).collect(),
      source_relation: self.source_relation.as_ref().map(f),
      target_relation: self.target_relation.as_ref().map(f),
    }
  }
}

/// The fixed data of [`rewrite_wf_obligations`]'s walk (Lean's `visit`
/// parameters and the schema it closes over).
struct Obligations<'a> {
  schema: &'a WfRootSchema,
  sigma: &'a [usize],
  source_type: &'a Expr,
  target_type: &'a Expr,
}

/// `rewriteWFObligations`: rewrite the complete decreasing obligations of
/// the root (`rel (inj_j y) (inj_i x)` with the root's own relation, or
/// `InvImage` at the root's domain and measure) to the target relation at
/// the permuted injections. At corresponding decoded constructors, source
/// and target measures reduce to the same user leaf, so this rewrite is a
/// definitional equality, even inside a user proof; it never rewrites a
/// relation's underlying user instance or arbitrary inputs because their
/// types match.
pub fn rewrite_wf_obligations(
  tm: &mut TState,
  schema: &WfRootSchema,
  sigma: &[usize],
  fuel: usize,
  expression: &Expr,
) -> R<Expr> {
  let source_type = spine_type_m(&schema.source_spine, "WF obligation")?;
  let target_type = spine_type_m(&schema.target_spine, "WF obligation")?;
  let cx = Obligations {
    schema,
    sigma,
    source_type: &source_type,
    target_type: &target_type,
  };
  obligations_visit(tm, &mut TransportMemo::default(), &cx, fuel, expression)
}

fn obligations_visit(
  tm: &mut TState,
  memo: &mut TransportMemo,
  cx: &Obligations<'_>,
  fuel: usize,
  e: &Expr,
) -> R<Expr> {
  let Some(next) = fuel.checked_sub(1) else {
    return Err("WF obligation: recursion bound".into());
  };
  memo_transport(tm, memo, e, fuel, 0, |tm, memo| {
    let go = |tm: &mut TState, memo: &mut TransportMemo, x: &Expr| {
      obligations_visit(tm, memo, cx, next, x)
    };
    let (head, args) = get_app_fn_args(e);
    let relation: Option<(Expr, Expr, Expr)> = 'relation: {
      if let (Some(source), Some(target)) =
        (&cx.schema.source_relation, &cx.schema.target_relation)
        && let [first, second] = args.as_slice()
        && alpha_eq_skip_mdata(&head, source)
      {
        break 'relation Some((target.clone(), first.clone(), second.clone()));
      }
      if let Some((name, levels, a)) = const_app(e)
        && let [domain, a1, a2, measure, first, second] = a.as_slice()
        && name == n_inv_image()
        && alpha_eq_skip_mdata(domain, cx.source_type)
        && alpha_eq_skip_mdata(measure, &cx.schema.source_measure)
      {
        let relation = mk_app_n(
          cnst(&name, &levels),
          &[
            cx.target_type.clone(),
            a1.clone(),
            a2.clone(),
            cx.schema.target_measure.clone(),
          ],
        );
        break 'relation Some((relation, first.clone(), second.clone()));
      }
      None
    };
    if let Some((relation, first, second)) = relation {
      let n = cx.schema.source_spine.size();
      if let Some((first_spine, first_index, first_payload)) =
        decode_inj(n, &first)
        && let Some((second_spine, second_index, second_payload)) =
          decode_inj(n, &second)
      {
        let first_type = spine_type_m(&first_spine, "WF obligation")?;
        let second_type = spine_type_m(&second_spine, "WF obligation")?;
        if alpha_eq_skip_mdata(&first_type, cx.source_type)
          && alpha_eq_skip_mdata(&second_type, cx.source_type)
        {
          let first_payload = go(tm, memo, &first_payload)?;
          let second_payload = go(tm, memo, &second_payload)?;
          let first_position =
            *tm_idx(cx.sigma, first_index, "WF obligation: permutation")?;
          let second_position =
            *tm_idx(cx.sigma, second_index, "WF obligation: permutation")?;
          let failed = || "WF obligation: injection reconstruction failed";
          let Some(first_inj) =
            mk_inj(&cx.schema.target_spine, first_position, &first_payload)
          else {
            return Err(failed().into());
          };
          let Some(second_inj) =
            mk_inj(&cx.schema.target_spine, second_position, &second_payload)
          else {
            return Err(failed().into());
          };
          return Ok(mk_app_n(relation, &[first_inj, second_inj]));
        }
      }
    }
    Ok(match e.as_data() {
      ExprData::App(f, a, _) => Expr::app(go(tm, memo, f)?, go(tm, memo, a)?),
      ExprData::Lam(n, t, b, bi, _) => {
        Expr::lam(n.clone(), go(tm, memo, t)?, go(tm, memo, b)?, bi.clone())
      },
      ExprData::ForallE(n, t, b, bi, _) => {
        Expr::all(n.clone(), go(tm, memo, t)?, go(tm, memo, b)?, bi.clone())
      },
      ExprData::LetE(n, t, v, b, nd, _) => Expr::letE(
        n.clone(),
        go(tm, memo, t)?,
        go(tm, memo, v)?,
        go(tm, memo, b)?,
        *nd,
      ),
      ExprData::Proj(s, i, x, _) => {
        Expr::proj(s.clone(), i.clone(), go(tm, memo, x)?)
      },
      ExprData::Mdata(d, x, _) => Expr::mdata(d.clone(), go(tm, memo, x)?),
      _ => e.clone(),
    })
  })
}

/// `decodeWFRoot`: decode the actual `Nat.fix` or `fix (invImage …).rel`
/// root. The underlying measure codomain and relation instance are opaque
/// user objects; only `invImage`'s declared source domain and measure
/// argument may change.
pub fn decode_wf_root(
  tm: &mut TState,
  l: &WfLayout,
  value: &Expr,
) -> R<WfRootSchema> {
  let Some((name, levels, args)) = const_app(&strip_mdata(value)) else {
    return Err("WF schema: root is not a fixpoint application".into());
  };
  let is_nat = name == dotted("WellFounded.Nat.fix");
  let unsupported = || "WF schema: unsupported fixpoint root".to_string();
  if !((is_nat && args.len() == 4)
    || (name == dotted("WellFounded.fix") && args.len() == 5))
  {
    return Err(unsupported());
  }
  let Some(domain) = args.first() else { return Err(unsupported()) };
  let Some(source_codomain) = args.get(1) else { return Err(unsupported()) };
  let Some(third) = args.get(2) else { return Err(unsupported()) };
  let Some(spine) = decode_spine(PackKind::Psum, l.n, domain) else {
    return Err("WF schema: root has no sum packing".into());
  };
  if !l.is_clique(&spine) {
    return Err("WF schema: root has a foreign packing".into());
  }
  let Some(target_spine) = spine.permute(&l.sigma) else {
    return Err("WF schema: root packing does not take the permutation".into());
  };
  let source_type = spine_type_m(&spine, "WF schema")?;
  let target_type = spine_type_m(&target_spine, "WF schema")?;
  let codomain = decode_wf_case(tm, &spine, &l.sigma, source_codomain)?;
  let (measure, target_args, relations) = if is_nat {
    let measure = decode_wf_case(tm, &spine, &l.sigma, third)?;
    (third.clone(), vec![target_type.clone(), codomain.clone(), measure], None)
  } else {
    let stripped = strip_mdata(third);
    let ExprData::Proj(structure_name, field, relation, _) = stripped.as_data()
    else {
      return Err(
        "WF schema: general relation is not the owned projection".into(),
      );
    };
    if !(*structure_name == n_wf_relation() && nat_usize(field) == 0) {
      return Err(
        "WF schema: general relation projects another structure".into(),
      );
    }
    let Some((rel_name, rel_levels, rel_args)) = const_app(relation) else {
      return Err("WF schema: general relation is not invImage".into());
    };
    let foreign_domain =
      || "WF schema: general relation has foreign invImage domain".to_string();
    if rel_name != dotted("invImage") {
      return Err(foreign_domain());
    }
    let [rel_domain, rel_codomain, rel_measure, rel_instance] =
      rel_args.as_slice()
    else {
      return Err(foreign_domain());
    };
    if !alpha_eq_skip_mdata(rel_domain, &source_type) {
      return Err(foreign_domain());
    }
    let measure = decode_wf_case(tm, &spine, &l.sigma, rel_measure)?;
    let target_rel = mk_app_n(
      cnst(&rel_name, &rel_levels),
      &[
        target_type.clone(),
        rel_codomain.clone(),
        measure,
        rel_instance.clone(),
      ],
    );
    let target_relation = proj(&n_wf_relation(), 0, target_rel.clone());
    // Lean may abstract its opaqueId/projection into a separate proof
    // declaration. Regenerate the well-founded witness from the same decoded
    // relation record, instead of recognising arbitrary proof syntax.
    let mut proof = proj(&n_wf_relation(), 1, target_rel);
    // This wrapper belongs to the exact root witness, not a user proof
    // discovered by its type. Preserve Lean's inline opaqueId convention only
    // after checking its complete source proposition and projection.
    let Some(witness) = args.get(3) else { return Err(unsupported()) };
    if let Some((wrapper, wrapper_levels, wrapper_args)) = const_app(witness)
      && let [wrapped_goal, wrapped_proof] = wrapper_args.as_slice()
      && wrapper == dotted("Lean.opaqueId")
    {
      let Some(domain_level) = levels.first() else {
        return Err("WF schema: missing domain universe".into());
      };
      let well_founded =
        cnst(&dotted("WellFounded"), slice::from_ref(domain_level));
      let source_goal =
        mk_app_n(well_founded.clone(), &[source_type.clone(), third.clone()]);
      if !(alpha_eq_skip_mdata(wrapped_goal, &source_goal)
        && alpha_eq_skip_mdata(
          wrapped_proof,
          &proj(&n_wf_relation(), 1, relation.clone()),
        ))
      {
        return Err(
          "WF schema: inline well-founded witness differs from the exact root \
           relation"
            .into(),
        );
      }
      let target_goal =
        mk_app_n(well_founded, &[target_type.clone(), target_relation.clone()]);
      proof = mk_app_n(cnst(&wrapper, &wrapper_levels), &[target_goal, proof]);
    }
    (
      rel_measure.clone(),
      vec![
        target_type.clone(),
        codomain.clone(),
        target_relation.clone(),
        proof,
      ],
      Some((third.clone(), target_relation)),
    )
  };
  let target_measure = decode_wf_case(tm, &spine, &l.sigma, &measure)?;
  let (source_relation, target_relation) = relations.unzip();
  Ok(WfRootSchema {
    source_spine: spine,
    target_spine,
    source_codomain: source_codomain.clone(),
    target_codomain: codomain,
    source_measure: measure,
    target_measure,
    head: cnst(&name, &levels),
    source_arguments: args,
    target_arguments: target_args,
    source_relation,
    target_relation,
  })
}

/// `ownedWFRecType`: rebuild only the two declared binders of a recursive
/// telescope `∀ (y : α) (h : rel y source_point), C y`. Exact source measure
/// and point identities establish the decreasing relation; the underlying
/// relation and all its parameters stay unchanged.
pub fn owned_wf_rec_type(
  tm: &mut TState,
  schema: &WfRootSchema,
  source_point: &Expr,
  target_point: &Expr,
  typ: &Expr,
) -> R<Expr> {
  let (locals, result) = open_binders(tm, false, 2, typ)?;
  let [argument, proof] = locals.as_slice() else {
    return Err("WF schema: incomplete recursive telescope".into());
  };
  let source_type = spine_type_m(&schema.source_spine, "WF schema")?;
  let target_type = spine_type_m(&schema.target_spine, "WF schema")?;
  if !alpha_eq_skip_mdata(&argument.typ, &source_type) {
    return Err("WF schema: recursive argument has a foreign domain".into());
  }
  let relation = match (&schema.source_relation, &schema.target_relation) {
    (Some(source), Some(target)) => {
      let (head, args) = get_app_fn_args(&proof.typ);
      let foreign = || {
        "WF schema: decreasing obligation has a foreign root relation or \
         argument identity"
          .to_string()
      };
      let [first, second] = args.as_slice() else { return Err(foreign()) };
      if !(alpha_eq_skip_mdata(&head, source)
        && alpha_eq_skip_mdata(first, &argument.expr())
        && alpha_eq_skip_mdata(second, source_point))
      {
        return Err(foreign());
      }
      mk_app_n(target.clone(), &[argument.expr(), target_point.clone()])
    },
    _ => {
      let Some((name, levels, args)) = const_app(&proof.typ) else {
        return Err("WF schema: decreasing obligation is not invImage".into());
      };
      let foreign = || {
        "WF schema: decreasing obligation has foreign measure or argument \
         identities"
          .to_string()
      };
      let [domain, a1, a2, measure, first, second] = args.as_slice() else {
        return Err(foreign());
      };
      if !(name == n_inv_image()
        && alpha_eq_skip_mdata(domain, &source_type)
        && alpha_eq_skip_mdata(measure, &schema.source_measure)
        && alpha_eq_skip_mdata(first, &argument.expr())
        && alpha_eq_skip_mdata(second, source_point))
      {
        return Err(foreign());
      }
      mk_app_n(
        cnst(&name, &levels),
        &[
          target_type.clone(),
          a1.clone(),
          a2.clone(),
          schema.target_measure.clone(),
          argument.expr(),
          target_point.clone(),
        ],
      )
    },
  };
  if !alpha_eq_skip_mdata(
    &result,
    &apply_wf_case(&schema.source_codomain, &argument.expr()),
  ) {
    return Err(
      "WF schema: recursive result differs from the root codomain".into(),
    );
  }
  close_binders(
    false,
    &[
      Local { typ: target_type, ..argument.clone() },
      Local { typ: relation, ..proof.clone() },
    ],
    &apply_wf_case(&schema.target_codomain, &argument.expr()),
  )
}

// ---------------------------------------------------------------------------
// Matchers (`WFMatcher.lean`)
// ---------------------------------------------------------------------------

/// A declaration-checked `Nat` dispatcher (`WFNatMatcher`). The zero
/// expression comes from the declared minor telescope, whose application is
/// checked against `Nat.casesOn`. No generated-name spelling or
/// coincidentally equal instantiated type grants this capability.
#[derive(Clone, Debug)]
pub struct WfNatMatcher {
  pub zero: Expr,
}

/// `decodeWFNatMatcher`: the matcher `name` at `levels` is, symbolically,
/// exactly the `Nat.casesOn` dispatch.
pub fn decode_wf_nat_matcher(
  tm: &mut TState,
  const_of: ConstOf<'_>,
  name: &Name,
  levels: &[Level],
) -> R<WfNatMatcher> {
  let Some(declaration) =
    const_of(name).and_then(|c| Decl::of_constant_info(&c))
  else {
    return Err(format!(
      "WF matcher: source declaration {} unavailable",
      name_to_string(name)
    ));
  };
  if declaration.name != *name {
    return Err(
      "WF matcher: lookup returned another source declaration identity".into(),
    );
  }
  if levels.len() != declaration.level_params.len() {
    return Err(
      "WF matcher: universe arity differs from source declaration".into(),
    );
  }
  let value =
    subst_levels(&declaration.level_params, levels, &declaration.value);
  let (parameters, body) = open_binders(tm, true, 4, &value)?;
  let [motive, major, zero_minor, succ_minor] = parameters.as_slice() else {
    return Err(
      "WF matcher: the dispatcher does not bind its motive, major and minors"
        .into(),
    );
  };
  let nat = cnst(&dotted("Nat"), &[]);
  let unit = cnst(&dotted("Unit"), &[]);
  let (motive_args, motive_sort) = open_binders(tm, false, 1, &motive.typ)?;
  let not_nat = || "WF matcher: motive domain is not Nat".to_string();
  let [motive_arg] = motive_args.as_slice() else { return Err(not_nat()) };
  if !alpha_eq_skip_mdata(&motive_arg.typ, &nat) {
    return Err(not_nat());
  }
  let motive_sort = strip_mdata(&motive_sort);
  let ExprData::Sort(result_level, _) = motive_sort.as_data() else {
    return Err("WF matcher: motive does not return a sort".into());
  };
  if !alpha_eq_skip_mdata(&major.typ, &nat) {
    return Err("WF matcher: major domain is not Nat".into());
  }
  let (zero_args, zero_result) = open_binders(tm, false, 1, &zero_minor.typ)?;
  let foreign_zero =
    || "WF matcher: zero minor has a foreign argument".to_string();
  let [zero_arg] = zero_args.as_slice() else { return Err(foreign_zero()) };
  if !alpha_eq_skip_mdata(&zero_arg.typ, &unit) {
    return Err(foreign_zero());
  }
  let stripped = strip_mdata(&zero_result);
  let ExprData::App(zero_head, zero, _) = stripped.as_data() else {
    return Err("WF matcher: zero minor does not return its motive".into());
  };
  if !(alpha_eq_skip_mdata(zero_head, &motive.expr())
    && !parameters
      .iter()
      .chain(&zero_args)
      .any(|p| mentions_fvar(&p.fvar, zero)))
  {
    return Err(
      "WF matcher: zero minor has a foreign motive or dependent index".into(),
    );
  }
  let (succ_args, succ_result) = open_binders(tm, false, 1, &succ_minor.typ)?;
  let foreign_succ =
    || "WF matcher: successor minor has a foreign motive or index".to_string();
  let [succ_arg] = succ_args.as_slice() else { return Err(foreign_succ()) };
  if !(alpha_eq_skip_mdata(&succ_arg.typ, &nat)
    && alpha_eq_skip_mdata(
      &succ_result,
      &Expr::app(
        motive.expr(),
        Expr::app(cnst(&n_nat_succ(), &[]), succ_arg.expr()),
      ),
    ))
  {
    return Err(foreign_succ());
  }
  let expected_motive =
    mk_lambda(&motive_args, &Expr::app(motive.expr(), motive_arg.expr()));
  let expected_succ =
    mk_lambda(&succ_args, &Expr::app(succ_minor.expr(), succ_arg.expr()));
  let expected = mk_app_n(
    cnst(&dotted("Nat.casesOn"), slice::from_ref(result_level)),
    &[
      expected_motive,
      major.expr(),
      Expr::app(zero_minor.expr(), cnst(&dotted("Unit.unit"), &[])),
      expected_succ,
    ],
  );
  if !alpha_eq_skip_mdata(&body, &expected) {
    return Err(
      "WF matcher: body is not the exact symbolic Nat dispatch".into(),
    );
  }
  let declared_type =
    subst_levels(&declaration.level_params, levels, &declaration.typ);
  if !alpha_eq_skip_mdata(
    &declared_type,
    &mk_forall(&parameters, &Expr::app(motive.expr(), major.expr())),
  ) {
    return Err(
      "WF matcher: declaration telescope differs from the symbolic dispatch"
        .into(),
    );
  }
  Ok(WfNatMatcher { zero: zero.clone() })
}

// ---------------------------------------------------------------------------
// The decoder-owned transport (`WFConjugation.lean`)
// ---------------------------------------------------------------------------

/// `ownedWFCalls`: substitute only the decoder-established recursive binder
/// (`bvar depth`). A call at a decoded constructor reduces the explicit
/// adapter directly; other uses keep the adapter, including copies threaded
/// through arbitrary user functions.
pub fn owned_wf_calls(
  tm: &mut TState,
  l: &WfLayout,
  adapter: &Expr,
  fuel: usize,
  depth: usize,
  e: &Expr,
) -> R<Expr> {
  calls_visit(tm, &mut TransportMemo::default(), l, adapter, fuel, depth, e)
}

fn calls_visit(
  tm: &mut TState,
  memo: &mut TransportMemo,
  l: &WfLayout,
  adapter: &Expr,
  fuel: usize,
  depth: usize,
  e: &Expr,
) -> R<Expr> {
  let Some(next) = fuel.checked_sub(1) else {
    return Err("WF ownership: body recursion bound".into());
  };
  memo_transport(tm, memo, e, fuel, depth, |tm, memo| {
    if l.sigma == id_perm(l.n) {
      return Ok(e.clone());
    }
    let go = |tm: &mut TState, memo: &mut TransportMemo, x: &Expr| {
      calls_visit(tm, memo, l, adapter, next, depth, x)
    };
    if let ExprData::App(..) = e.as_data() {
      let (head, args) = get_app_fn_args(e);
      if alpha_eq_skip_mdata(&head, &bvar(depth)) {
        let adapted = |tm: &mut TState, memo: &mut TransportMemo| -> R<Expr> {
          let mut out = Vec::with_capacity(args.len());
          for x in &args {
            out.push(go(tm, memo, x)?);
          }
          Ok(mk_app_n(lift_loose(adapter, depth, 0), &out))
        };
        let (Some(first), Some(second)) = (args.first(), args.get(1)) else {
          return adapted(tm, memo);
        };
        let Some((spine, index, payload)) = decode_inj(l.n, first) else {
          return adapted(tm, memo);
        };
        let foreign =
          || "WF ownership: foreign recursive injection".to_string();
        if !l.is_clique(&spine) {
          return Err(foreign());
        }
        let payload = go(tm, memo, &payload)?;
        let Some(target) = spine.permute(&l.sigma) else {
          return Err(foreign());
        };
        let position =
          *tm_idx(&l.sigma, index, "WF ownership: recursive injection")?;
        let Some(argument) = mk_inj(&target, position, &payload) else {
          return Err(
            "WF ownership: recursive injection reconstruction failed".into(),
          );
        };
        let proof = go(tm, memo, second)?;
        let mut out = vec![argument, proof];
        for x in args.iter().skip(2) {
          out.push(go(tm, memo, x)?);
        }
        return Ok(mk_app_n(head, &out));
      }
    }
    Ok(match e.as_data() {
      ExprData::Bvar(..) => {
        if is_bvar(e, depth) {
          lift_loose(adapter, depth, 0)
        } else {
          e.clone()
        }
      },
      ExprData::App(f, a, _) => Expr::app(go(tm, memo, f)?, go(tm, memo, a)?),
      ExprData::Lam(n, t, b, bi, _) => Expr::lam(
        n.clone(),
        go(tm, memo, t)?,
        calls_visit(tm, memo, l, adapter, next, depth + 1, b)?,
        bi.clone(),
      ),
      ExprData::ForallE(n, t, b, bi, _) => Expr::all(
        n.clone(),
        go(tm, memo, t)?,
        calls_visit(tm, memo, l, adapter, next, depth + 1, b)?,
        bi.clone(),
      ),
      ExprData::LetE(n, t, v, b, nd, _) => Expr::letE(
        n.clone(),
        go(tm, memo, t)?,
        go(tm, memo, v)?,
        calls_visit(tm, memo, l, adapter, next, depth + 1, b)?,
        *nd,
      ),
      ExprData::Proj(s, i, x, _) => {
        Expr::proj(s.clone(), i.clone(), go(tm, memo, x)?)
      },
      ExprData::Mdata(d, x, _) => Expr::mdata(d.clone(), go(tm, memo, x)?),
      _ => e.clone(),
    })
  })
}

/// `ownedWFRecAdapter`: an inverse-input adapter for the exact decoded
/// recursive binder. Splitting the source argument into constructors makes
/// the source and target decreasing obligations definitionally equal in every
/// branch; no arbitrary user relation is rewritten. The result retains the
/// source recursive function's type.
pub fn owned_wf_rec_adapter(
  tm: &mut TState,
  l: &WfLayout,
  spine: &Spine,
  w: &Level,
  recursive: &Local,
) -> R<Expr> {
  let (arguments, result) = open_binders(tm, false, 1, &recursive.typ)?;
  let Some(argument) = arguments.first() else {
    return Err("WF ownership: missing recursive argument".into());
  };
  let spine_type = spine_type_m(spine, "WF ownership")?;
  if !alpha_eq_skip_mdata(&argument.typ, &spine_type) {
    return Err("WF ownership: wrong recursive argument domain".into());
  }
  let argument_fvar = slice::from_ref(&argument.fvar);
  let injection_failed =
    || "WF ownership: recursive adapter injection failed".to_string();
  let mut leaves = Vec::new();
  for j in 0..l.n {
    let payload_name = tm.fresh_fvar();
    let summand =
      tm_idx(&spine.leaves, j, "WF ownership: recursive adapter summand")?;
    let payload = Local {
      fvar: payload_name,
      user_name: root_name("value"),
      typ: summand.clone(),
      bi: BinderInfo::Default,
    };
    let Some(source) = mk_inj(spine, j, &payload.expr()) else {
      return Err(injection_failed());
    };
    let at_constructor =
      inst_locals(&abstract_fvars(argument_fvar, &result), &[source]);
    let (proofs, _) = open_binders(tm, false, 1, &at_constructor)?;
    let Some(proof) = proofs.first() else {
      return Err("WF ownership: missing decreasing proof binder".into());
    };
    let Some(target) = spine.permute(&l.sigma) else {
      return Err(
        "WF ownership: recursive adapter domain does not take the permutation"
          .into(),
      );
    };
    let position = *tm_idx(&l.sigma, j, "WF ownership: recursive adapter")?;
    let Some(target_inj) = mk_inj(&target, position, &payload.expr()) else {
      return Err(injection_failed());
    };
    let value = mk_app_n(recursive.expr(), &[target_inj, proof.expr()]);
    leaves.push(close_binders(true, &[payload, proof.clone()], &value)?);
  }
  let tree = Tree {
    spine: spine.clone(),
    w: w.clone(),
    motive_name: argument.user_name.clone(),
    motive_body: abstract_fvars(argument_fvar, &result),
    major: argument.expr(),
    leaves,
    extras: Vec::new(),
    alt_names: Vec::new(),
  };
  let Some(body) = tree.build() else {
    return Err("WF ownership: inverse-input case tree failed".into());
  };
  close_binders(true, slice::from_ref(argument), &body)
}

/// `substituteWFLocal`: `value` with the free variable `identity` replaced by
/// `replacement`.
pub fn substitute_wf_local(
  identity: &Name,
  value: &Expr,
  replacement: &Expr,
) -> Expr {
  inst_locals(
    &abstract_fvars(slice::from_ref(identity), value),
    slice::from_ref(replacement),
  )
}

/// The fixed arguments of [`owned_wf_body`] (Lean's parameters before the
/// colon): the layout, the decoded root, the refinement tree's motive level
/// and the constant lookup.
pub struct WfBodyCx<'a> {
  pub layout: &'a WfLayout,
  pub schema: &'a WfRootSchema,
  pub w: &'a Level,
  pub const_of: ConstOf<'a>,
}

/// `ownedWFBody`: transport a leaf body whose payload is `payload` and whose
/// recursive binder is `recursive`, at the source and target points of the
/// payload. An exact recursive argument is followed through the standard
/// `PSigma` eliminator at the decoded payload (its minor's third binder
/// receives that argument by the eliminator's declared semantics) and through
/// a declaration-checked `Nat` dispatcher; all other user binders remain
/// opaque to ownership, and general forwarding uses the typed inverse-input
/// adapter.
pub fn owned_wf_body(
  tm: &mut TState,
  cx: &WfBodyCx<'_>,
  fuel: usize,
  payload: &Local,
  recursive: &Local,
  source_point: &Expr,
  target_point: &Expr,
  body: &Expr,
) -> R<Expr> {
  let Some(fuel) = fuel.checked_sub(1) else {
    return Err("WF ownership: payload refinement recursion bound".into());
  };
  if let Some((name, levels, args)) = const_app(body) {
    if let [pair_type, pair_family, motive_arg, major, minor_arg, recursive_arg] =
      args.as_slice()
      && name == dotted("PSigma.casesOn")
      && alpha_eq_skip_mdata(major, &payload.expr())
      && alpha_eq_skip_mdata(recursive_arg, &recursive.expr())
      && !mentions_fvar(&recursive.fvar, motive_arg)
      && !mentions_fvar(&recursive.fvar, minor_arg)
    {
      let Some((payload_name, payload_levels, payload_args)) =
        const_app(&payload.typ)
      else {
        return Err(
          "WF ownership: refined payload is not a dependent pair".into(),
        );
      };
      let foreign_payload = || {
        "WF ownership: dependent-pair eliminator has a foreign payload type"
          .to_string()
      };
      let [payload_alpha, payload_beta] = payload_args.as_slice() else {
        return Err(foreign_payload());
      };
      if !(payload_name == n_psigma()
        && alpha_eq_skip_mdata(payload_alpha, pair_type)
        && alpha_eq_skip_mdata(payload_beta, pair_family))
      {
        return Err(foreign_payload());
      }
      let (motive_locals, motive_body) = open_binders(tm, true, 1, motive_arg)?;
      let [motive_payload] = motive_locals.as_slice() else {
        return Err(
          "WF ownership: refinement motive has no payload binder".into(),
        );
      };
      let (motive_binders, motive_result) =
        open_binders(tm, false, 1, &motive_body)?;
      let [motive_recursive] = motive_binders.as_slice() else {
        return Err(
          "WF ownership: refinement motive has no recursive binder".into(),
        );
      };
      if mentions_fvar(&motive_recursive.fvar, &motive_result) {
        return Err(
          "WF ownership: refinement result depends on its recursive value"
            .into(),
        );
      }
      let motive_rec_type = owned_wf_rec_type(
        tm,
        cx.schema,
        &substitute_wf_local(
          &payload.fvar,
          source_point,
          &motive_payload.expr(),
        ),
        &substitute_wf_local(
          &payload.fvar,
          target_point,
          &motive_payload.expr(),
        ),
        &motive_recursive.typ,
      )?;
      let motive_body = close_binders(
        false,
        &[Local { typ: motive_rec_type, ..motive_recursive.clone() }],
        &motive_result,
      )?;
      let motive = close_binders(true, &motive_locals, &motive_body)?;
      let (minor_locals, minor_body) = open_binders(tm, true, 3, minor_arg)?;
      let [first, second, minor_recursive] = minor_locals.as_slice() else {
        return Err(
          "WF ownership: refinement minor does not bind its components and \
           recursive value"
            .into(),
        );
      };
      let pair = mk_app_n(
        cnst(&dotted("PSigma.mk"), &payload_levels),
        &[
          payload_alpha.clone(),
          payload_beta.clone(),
          first.expr(),
          second.expr(),
        ],
      );
      let source_point =
        substitute_wf_local(&payload.fvar, source_point, &pair);
      let target_point =
        substitute_wf_local(&payload.fvar, target_point, &pair);
      let rec_type = owned_wf_rec_type(
        tm,
        cx.schema,
        &source_point,
        &target_point,
        &minor_recursive.typ,
      )?;
      let minor_body = owned_wf_body(
        tm,
        cx,
        fuel,
        second,
        minor_recursive,
        &source_point,
        &target_point,
        &minor_body,
      )?;
      let minor = close_binders(
        true,
        &[
          first.clone(),
          second.clone(),
          Local { typ: rec_type, ..minor_recursive.clone() },
        ],
        &minor_body,
      )?;
      return Ok(mk_app_n(
        cnst(&name, &levels),
        &[
          pair_type.clone(),
          pair_family.clone(),
          motive,
          major.clone(),
          minor,
          recursive_arg.clone(),
        ],
      ));
    }
    if let [motive_arg, major, zero_arg, succ_arg, recursive_arg] =
      args.as_slice()
      && alpha_eq_skip_mdata(major, &payload.expr())
      && alpha_eq_skip_mdata(recursive_arg, &recursive.expr())
      && !args.iter().take(4).any(|a| mentions_fvar(&recursive.fvar, a))
    {
      // Lean runs the decoder on a copy of the state and keeps it only on
      // success; the decoder changes nothing but the fresh-variable counter
      let saved = tm.next;
      match decode_wf_nat_matcher(tm, cx.const_of, &name, &levels) {
        Err(reason) => {
          tm.next = saved;
          tm.trace(format!(
            "{reason}; retaining the faithful recursive-input adapter"
          ));
        },
        Ok(flow) => {
          let (motive_locals, motive_body) =
            open_binders(tm, true, 1, motive_arg)?;
          let [motive_payload] = motive_locals.as_slice() else {
            return Err("WF matcher: motive has no payload binder".into());
          };
          if !alpha_eq_skip_mdata(&motive_payload.typ, &payload.typ) {
            return Err(
              "WF matcher: motive payload differs from owned input".into(),
            );
          }
          let (motive_binders, motive_result) =
            open_binders(tm, false, 1, &motive_body)?;
          let [motive_recursive] = motive_binders.as_slice() else {
            return Err("WF matcher: motive has no recursive binder".into());
          };
          if mentions_fvar(&motive_recursive.fvar, &motive_result) {
            return Err(
              "WF matcher: result depends on the recursive value".into(),
            );
          }
          let motive_rec_type = owned_wf_rec_type(
            tm,
            cx.schema,
            &substitute_wf_local(
              &payload.fvar,
              source_point,
              &motive_payload.expr(),
            ),
            &substitute_wf_local(
              &payload.fvar,
              target_point,
              &motive_payload.expr(),
            ),
            &motive_recursive.typ,
          )?;
          let motive_body = close_binders(
            false,
            &[Local { typ: motive_rec_type, ..motive_recursive.clone() }],
            &motive_result,
          )?;
          let motive = close_binders(true, &motive_locals, &motive_body)?;
          let mut minors = Vec::new();
          for (index, minor_arg) in [zero_arg, succ_arg].into_iter().enumerate()
          {
            let (locals, minor_body) = open_binders(tm, true, 2, minor_arg)?;
            let [branch_argument, minor_recursive] = locals.as_slice() else {
              return Err(
                "WF matcher: minor does not bind its argument and recursive \
                 value"
                  .into(),
              );
            };
            let point = if index == 0 {
              flow.zero.clone()
            } else {
              Expr::app(cnst(&n_nat_succ(), &[]), branch_argument.expr())
            };
            let source_point =
              substitute_wf_local(&payload.fvar, source_point, &point);
            let target_point =
              substitute_wf_local(&payload.fvar, target_point, &point);
            let rec_type = owned_wf_rec_type(
              tm,
              cx.schema,
              &source_point,
              &target_point,
              &minor_recursive.typ,
            )?;
            let minor_body = owned_wf_body(
              tm,
              cx,
              fuel,
              branch_argument,
              minor_recursive,
              &source_point,
              &target_point,
              &minor_body,
            )?;
            minors.push(close_binders(
              true,
              &[
                branch_argument.clone(),
                Local { typ: rec_type, ..minor_recursive.clone() },
              ],
              &minor_body,
            )?);
          }
          let [zero_minor, succ_minor] = minors.as_slice() else {
            return Err("WF matcher: minor reconstruction failed".into());
          };
          return Ok(mk_app_n(
            cnst(&name, &levels),
            &[
              motive,
              major.clone(),
              zero_minor.clone(),
              succ_minor.clone(),
              recursive_arg.clone(),
            ],
          ));
        },
      }
    }
  }
  let body = rewrite_wf_obligations(
    tm,
    cx.schema,
    &cx.layout.sigma,
    TRANSPORT_FUEL,
    body,
  )?;
  let adapter = owned_wf_rec_adapter(
    tm,
    cx.layout,
    &cx.schema.source_spine,
    cx.w,
    recursive,
  )?;
  let recursive_fvar = slice::from_ref(&recursive.fvar);
  let adapter = abstract_fvars(recursive_fvar, &adapter);
  let transformed = owned_wf_calls(
    tm,
    cx.layout,
    &adapter,
    TRANSPORT_FUEL,
    0,
    &abstract_fvars(recursive_fvar, &body),
  )?;
  Ok(inst_locals(&transformed, &[recursive.expr()]))
}

/// `conjugateWFRoot`: decode the exact root relationship and preserve user
/// syntax by transporting only its owned entry, recursive argument flow and
/// output positions.
pub fn conjugate_wf_root(
  tm: &mut TState,
  l: &WfLayout,
  value: &Expr,
  const_of: ConstOf<'_>,
) -> R<Expr> {
  let schema = decode_wf_root(tm, l, value)?;
  let missing = || "WF ownership: missing root functional".to_string();
  let Some(functional) = schema.source_arguments.last() else {
    return Err(missing());
  };
  let (locals, body) = open_binders(tm, true, 2, functional)?;
  let [x, recursive] = locals.as_slice() else { return Err(missing()) };
  let source_type = spine_type_m(&schema.source_spine, "WF ownership")?;
  let target_type = spine_type_m(&schema.target_spine, "WF ownership")?;
  if !alpha_eq_skip_mdata(&x.typ, &source_type) {
    return Err("WF ownership: functional domain differs from root".into());
  }
  let recursive_type =
    owned_wf_rec_type(tm, &schema, &x.expr(), &x.expr(), &recursive.typ)?;
  let Some(tree) = decode_tree(l.n, &body) else {
    return Err("WF ownership: missing root refinement tree".into());
  };
  let tree_type = spine_type_m(&tree.spine, "WF ownership")?;
  let threads_recursive = matches!(
    tree.extras.as_slice(),
    [extra] if alpha_eq_skip_mdata(extra, &recursive.expr())
  );
  if !(alpha_eq_skip_mdata(&tree_type, &source_type)
    && alpha_eq_skip_mdata(&tree.major, &x.expr())
    && threads_recursive)
  {
    return Err(
      "WF ownership: root refinement has foreign entry identities".into(),
    );
  }
  let recursive_at_x = abstract_fvars(slice::from_ref(&x.fvar), &recursive.typ);
  let source_type_at =
    |point: &Expr| inst_locals(&recursive_at_x, slice::from_ref(point));
  let injection_failed =
    || "WF ownership: leaf injection reconstruction failed".to_string();
  let cx = WfBodyCx { layout: l, schema: &schema, w: &tree.w, const_of };
  let mut leaves = Vec::new();
  for index in 0..l.n {
    let leaf = tm_idx(&tree.leaves, index, "WF ownership: refinement leaf")?;
    if mentions_fvar(&x.fvar, leaf) || mentions_fvar(&recursive.fvar, leaf) {
      return Err(
        "WF ownership: leaf captures an unthreaded root identity".into(),
      );
    }
    let (entry, leaf_body) = open_binders(tm, true, 2, leaf)?;
    let [payload, recursor] = entry.as_slice() else {
      return Err(
        "WF ownership: leaf does not bind its payload and recursive value"
          .into(),
      );
    };
    let summand =
      tm_idx(&schema.source_spine.leaves, index, "WF ownership: root summand")?;
    if !alpha_eq_skip_mdata(&payload.typ, summand) {
      return Err(
        "WF ownership: leaf payload differs from root summand".into(),
      );
    }
    let Some(source_point) =
      mk_inj(&schema.source_spine, index, &payload.expr())
    else {
      return Err(injection_failed());
    };
    let position = *tm_idx(&l.sigma, index, "WF ownership: refinement leaf")?;
    let Some(target_point) =
      mk_inj(&schema.target_spine, position, &payload.expr())
    else {
      return Err(injection_failed());
    };
    if !alpha_eq_skip_mdata(&recursor.typ, &source_type_at(&source_point)) {
      return Err(
        "WF ownership: leaf recursive binder differs from root telescope"
          .into(),
      );
    }
    let recursor_type = owned_wf_rec_type(
      tm,
      &schema,
      &source_point,
      &target_point,
      &recursor.typ,
    )?;
    let transformed = owned_wf_body(
      tm,
      &cx,
      TRANSPORT_FUEL,
      payload,
      recursor,
      &source_point,
      &target_point,
      &leaf_body,
    )?;
    leaves.push(close_binders(
      true,
      &[payload.clone(), Local { typ: recursor_type, ..recursor.clone() }],
      &transformed,
    )?);
  }
  let point_name = tm.fresh_fvar();
  let point = fvar(&point_name);
  let point_fvar = slice::from_ref(&point_name);
  let source_motive = mk_forall(
    &[Local { typ: source_type_at(&point), ..recursive.clone() }],
    &apply_wf_case(&schema.source_codomain, &point),
  );
  if !alpha_eq_skip_mdata(
    &tree.motive_body,
    &abstract_fvars(point_fvar, &source_motive),
  ) {
    return Err(
      "WF ownership: refinement motive differs from root telescope".into(),
    );
  }
  let target_recursive =
    owned_wf_rec_type(tm, &schema, &point, &point, &source_type_at(&point))?;
  let target_motive = mk_forall(
    &[Local { typ: target_recursive, ..recursive.clone() }],
    &apply_wf_case(&schema.target_codomain, &point),
  );
  let tree = Tree {
    leaves,
    motive_body: abstract_fvars(point_fvar, &target_motive),
    ..tree
  };
  let Some(body) = tree.permute(&l.sigma).and_then(|t| t.build()) else {
    return Err("WF ownership: root refinement reconstruction failed".into());
  };
  let functional = close_binders(
    true,
    &[
      Local { typ: target_type, ..x.clone() },
      Local { typ: recursive_type, ..recursive.clone() },
    ],
    &body,
  )?;
  let mut target_arguments = schema.target_arguments.clone();
  target_arguments.push(functional);
  Ok(mk_app_n(schema.head.clone(), &target_arguments))
}

/// `conjugateWFType`: the packed function's type `∀ x : α, C x` with its
/// domain and codomain case tree permuted.
pub fn conjugate_wf_type(tm: &mut TState, l: &WfLayout, typ: &Expr) -> R<Expr> {
  let stripped = strip_mdata(typ);
  let ExprData::ForallE(name, domain, body, bi, _) = stripped.as_data() else {
    return Err("WF schema: packed type has no input binder".into());
  };
  let Some(spine) = decode_spine(PackKind::Psum, l.n, domain) else {
    return Err("WF schema: packed type has no sum domain".into());
  };
  if !l.is_clique(&spine) {
    return Err("WF schema: packed type has a foreign domain".into());
  }
  let transformed = decode_wf_case(
    tm,
    &spine,
    &l.sigma,
    &Expr::lam(name.clone(), domain.clone(), body.clone(), bi.clone()),
  )?;
  match transformed.as_data() {
    ExprData::Lam(n, d, b, bi, _) => {
      Ok(Expr::all(n.clone(), d.clone(), b.clone(), bi.clone()))
    },
    _ => Err("WF schema: transformed codomain has no binder".into()),
  }
}

/// `wfPackedDomain`: the source packing, the codomain and the result level
/// of the packed function at `levels` and the fixed arguments `fixed`.
pub fn wf_packed_domain(
  l: &WfLayout,
  packed: &Decl,
  levels: &[Level],
  fixed: &[Expr],
) -> R<(Spine, Expr, Level)> {
  if fixed.len() != l.num_fixed {
    return Err("WF adapter: incomplete fixed arguments".into());
  }
  let typ = subst_levels(&packed.level_params, levels, &packed.typ);
  let (_, result) = peel_foralls(l.num_fixed, &typ);
  let result = strip_mdata(&inst_locals(&result, fixed));
  let ExprData::ForallE(_, domain, codomain, _, _) = result.as_data() else {
    return Err("WF adapter: packed type has no dependent input".into());
  };
  let Some(spine) = decode_spine(PackKind::Psum, l.n, domain) else {
    return Err("WF adapter: missing source sum domain".into());
  };
  let value = subst_levels(&packed.level_params, levels, &packed.value);
  let (_, root) = peel_lams(l.num_fixed, &value);
  let Some((_, root_levels, _)) = const_app(&strip_mdata(&root)) else {
    return Err("WF adapter: missing fixpoint root".into());
  };
  let Some(result_level) = root_levels.get(1) else {
    return Err("WF adapter: missing result universe".into());
  };
  Ok((spine, codomain.clone(), result_level.clone()))
}

/// `applyWFPackedAdapter`: the dependent pullback of the target packed
/// function at `argument`. Case analysis on the source input makes
/// `C'(inj' i p)` and `C(inj i p)` definitionally equal at every leaf; a bare
/// `f'(post x)` at an arbitrary `x` would not establish that.
pub fn apply_wf_packed_adapter(
  tm: &mut TState,
  l: &WfLayout,
  packed: &Decl,
  levels: &[Level],
  fixed: &[Expr],
  argument: &Expr,
) -> R<Expr> {
  let (spine, codomain, result_level) =
    wf_packed_domain(l, packed, levels, fixed)?;
  let Some(target) = spine.permute(&l.sigma) else {
    return Err(
      "WF adapter: packed domain does not take the permutation".into(),
    );
  };
  let Some(target_fixed) = reorder(&l.fixed_perm, fixed) else {
    return Err("WF adapter: incomplete fixed arguments".into());
  };
  let call = |index: usize, payload: &Expr| -> R<Expr> {
    let position = *tm_idx(&l.sigma, index, "WF adapter: packed input")?;
    let Some(input) = mk_inj(&target, position, payload) else {
      return Err("WF adapter: target injection reconstruction failed".into());
    };
    let mut args = target_fixed.clone();
    args.push(input);
    Ok(mk_app_n(cnst(&l.new_mutual_name, levels), &args))
  };
  if let Some((actual, index, payload)) = decode_inj(l.n, argument) {
    let actual_type = spine_type_m(&actual, "WF adapter")?;
    let spine_type = spine_type_m(&spine, "WF adapter")?;
    if !alpha_eq_skip_mdata(&actual_type, &spine_type) {
      return Err("WF adapter: injected argument has a foreign type".into());
    }
    return call(index, &payload);
  }
  let mut leaves = Vec::new();
  for index in 0..l.n {
    let name = tm.fresh_fvar();
    let summand = tm_idx(&spine.leaves, index, "WF adapter: packed summand")?;
    let payload = Local {
      fvar: name,
      user_name: root_name("payload"),
      typ: summand.clone(),
      bi: BinderInfo::Default,
    };
    let leaf = call(index, &payload.expr())?;
    leaves.push(mk_lambda(&[payload], &leaf));
  }
  let tree = Tree {
    spine,
    w: result_level,
    motive_name: root_name("input"),
    motive_body: codomain,
    major: argument.clone(),
    leaves,
    extras: Vec::new(),
    alt_names: Vec::new(),
  };
  tree.build().ok_or_else(|| {
    "WF adapter: dependent input case reconstruction failed".into()
  })
}

/// `rewriteOwnedWFUses`: rewrite exact constant identities only: the
/// proof-prefix reordering and the decoded member call into the packed root.
/// No user types, binders or relations grant entry to the encoding. General
/// packed inputs use the dependent adapter; an incomplete fixed-parameter
/// prefix remains an explicit decline.
pub fn rewrite_owned_wf_uses(
  tm: &mut TState,
  l: &WfLayout,
  packed: &Decl,
  fuel: usize,
  e: &Expr,
) -> R<Expr> {
  uses_visit(tm, &mut TransportMemo::default(), l, packed, fuel, e)
}

fn uses_visit(
  tm: &mut TState,
  memo: &mut TransportMemo,
  l: &WfLayout,
  packed: &Decl,
  fuel: usize,
  e: &Expr,
) -> R<Expr> {
  let Some(next) = fuel.checked_sub(1) else {
    return Err("WF ownership: constant-use recursion bound".into());
  };
  memo_transport(tm, memo, e, fuel, 0, |tm, memo| {
    let go = |tm: &mut TState, memo: &mut TransportMemo, x: &Expr| {
      uses_visit(tm, memo, l, packed, next, x)
    };
    Ok(match e.as_data() {
      ExprData::App(..) => {
        let (head, args) = get_app_fn_args(e);
        if let ExprData::Const(name, levels, _) = head.as_data() {
          if *name == l.mutual_name {
            return packed_use(tm, memo, l, packed, next, levels, &args);
          }
          if let Some(permutation) = l.proof_perm.get(name) {
            let partial = || "WF ownership: partial proof use".to_string();
            if args.len() < permutation.len() {
              return Err(partial());
            }
            let mut out = Vec::with_capacity(args.len());
            for x in &args {
              out.push(go(tm, memo, x)?);
            }
            let Some(mut fixed_args) = reorder(permutation, &out) else {
              return Err(partial());
            };
            fixed_args.extend(extract(&out, permutation.len(), out.len()));
            return Ok(mk_app_n(head.clone(), &fixed_args));
          }
        }
        let head = go(tm, memo, &head)?;
        let mut out = Vec::with_capacity(args.len());
        for x in &args {
          out.push(go(tm, memo, x)?);
        }
        mk_app_n(head, &out)
      },
      ExprData::Const(name, levels, _) => {
        if *name == l.mutual_name {
          return packed_use(tm, memo, l, packed, next, levels, &[]);
        }
        if let Some(permutation) = l.proof_perm.get(name)
          && !permutation.is_empty()
        {
          return Err("WF ownership: bare proof use".into());
        }
        e.clone()
      },
      ExprData::Lam(n, t, b, bi, _) => {
        Expr::lam(n.clone(), go(tm, memo, t)?, go(tm, memo, b)?, bi.clone())
      },
      ExprData::ForallE(n, t, b, bi, _) => {
        Expr::all(n.clone(), go(tm, memo, t)?, go(tm, memo, b)?, bi.clone())
      },
      ExprData::LetE(n, t, v, b, nd, _) => Expr::letE(
        n.clone(),
        go(tm, memo, t)?,
        go(tm, memo, v)?,
        go(tm, memo, b)?,
        *nd,
      ),
      ExprData::Proj(s, i, x, _) => {
        Expr::proj(s.clone(), i.clone(), go(tm, memo, x)?)
      },
      ExprData::Mdata(d, x, _) => Expr::mdata(d.clone(), go(tm, memo, x)?),
      _ => e.clone(),
    })
  })
}

/// `packedUse` of [`rewrite_owned_wf_uses`]: an application of the packed
/// function at `levels` to `args` (its arguments transported at `fuel`).
fn packed_use(
  tm: &mut TState,
  memo: &mut TransportMemo,
  l: &WfLayout,
  packed: &Decl,
  fuel: usize,
  levels: &[Level],
  args: &[Expr],
) -> R<Expr> {
  if args.len() < l.num_fixed {
    return Err("WF ownership: partial fixed prefix of packed root".into());
  }
  let mut out = Vec::with_capacity(args.len());
  for x in args {
    out.push(uses_visit(tm, memo, l, packed, fuel, x)?);
  }
  let fixed = extract(&out, 0, l.num_fixed);
  let Some(packed_arg) = out.get(l.num_fixed) else {
    let (spine, _, _) = wf_packed_domain(l, packed, levels, &fixed)?;
    let spine_type = spine_type_m(&spine, "WF ownership")?;
    let identity = tm.fresh_fvar();
    let argument = Local {
      fvar: identity,
      user_name: root_name("input"),
      typ: spine_type,
      bi: BinderInfo::Default,
    };
    let value =
      apply_wf_packed_adapter(tm, l, packed, levels, &fixed, &argument.expr())?;
    return Ok(mk_lambda(&[argument], &value));
  };
  let value =
    apply_wf_packed_adapter(tm, l, packed, levels, &fixed, packed_arg)?;
  Ok(mk_app_n(value, &extract(&out, l.num_fixed + 1, out.len())))
}

/// `transportOwnedWFEqDef`: the packed equation lemma `equation` of `packed`
/// for its transported `target`, renamed `new_name`. The equation keeps its
/// source-domain indexing through a dependent input adapter; at each decoded
/// constructor, the target `fix_eq` is exactly the required equation by β/ι
/// conversion. No arbitrary proof syntax is transported, and no equality
/// between arbitrary `C'(post x)` and `C(x)` is assumed.
pub fn transport_owned_wf_eq_def(
  tm: &mut TState,
  l: &WfLayout,
  packed: &Decl,
  target: &Decl,
  equation: &Decl,
  new_name: &Name,
) -> R<Decl> {
  let keep = |_: &mut TState, x: &Expr| -> R<Expr> { Ok(x.clone()) };
  let rewrite = |tm: &mut TState, x: &Expr| {
    rewrite_owned_wf_uses(tm, l, packed, TRANSPORT_FUEL, x)
  };
  let typ = with_reordered_binders2(
    tm,
    false,
    l.num_fixed,
    &l.fixed_perm,
    &equation.typ,
    &keep,
    &rewrite,
  )?;
  let (parameters, statement) = open_binders(tm, false, l.num_fixed + 1, &typ)?;
  let point = tm_idx(&parameters, l.num_fixed, "WF equation: packed argument")?;
  let Some(inverse) = inv_perm(&l.fixed_perm) else {
    return Err(
      "WF equation: the fixed-parameter order is not a permutation".into(),
    );
  };
  let mut source_fixed = Vec::with_capacity(l.num_fixed);
  for index in id_perm(l.num_fixed) {
    let position =
      *tm_idx(&inverse, index, "WF equation: fixed-parameter order")?;
    let parameter =
      tm_idx(&parameters, position, "WF equation: fixed parameter")?;
    source_fixed.push(parameter.expr());
  }
  let target_fixed = exprs(&extract(&parameters, 0, l.num_fixed));
  let mut source_inputs = source_fixed.clone();
  source_inputs.push(point.expr());
  let source_step = eq_def_fix_step(equation, l.num_fixed, &source_inputs)?;
  let (source_binders, source_body) = peel_lams(l.num_fixed, &packed.value);
  let (target_binders, target_body) = peel_lams(l.num_fixed, &target.value);
  if !(source_binders.len() == l.num_fixed
    && target_binders.len() == l.num_fixed)
  {
    return Err(
      "WF equation: packed fixed telescope differs from its layout".into(),
    );
  }
  let source_root = inst_locals(&source_body, &source_fixed);
  let target_root = inst_locals(&target_body, &target_fixed);
  let Some((root, root_levels, source_args)) = const_app(&source_root) else {
    return Err("WF equation: source root is not a fixpoint".into());
  };
  let Some((_, _, target_args)) = const_app(&target_root) else {
    return Err("WF equation: target root is not a fixpoint".into());
  };
  let Some((step_name, step_levels, step_args)) =
    const_app(&strip_id(&source_step))
  else {
    return Err("WF equation: source proof has no fix_eq step".into());
  };
  let expected_step = if root == dotted("WellFounded.Nat.fix") {
    dotted("WellFounded.Nat.fix_eq")
  } else if root == dotted("WellFounded.fix") {
    dotted("WellFounded.fix_eq")
  } else {
    Name::anon()
  };
  let foreign_root = || {
    "WF equation: fix_eq does not refer to the exact decoded source root"
      .to_string()
  };
  if !(step_name == expected_step
    && step_levels == root_levels
    && step_args.len() == source_args.len() + 1
    && step_args
      .iter()
      .zip(&source_args)
      .all(|(a, b)| alpha_eq_skip_mdata(a, b)))
  {
    return Err(foreign_root());
  }
  let Some(step_point) = step_args.get(source_args.len()) else {
    return Err(foreign_root());
  };
  if !alpha_eq_skip_mdata(step_point, &point.expr()) {
    return Err("WF equation: fix_eq uses a foreign input identity".into());
  }
  let Some(spine) = decode_spine(PackKind::Psum, l.n, &point.typ) else {
    return Err("WF equation: source equation has no sum input".into());
  };
  let spine_type = spine_type_m(&spine, "WF equation")?;
  let input_differs =
    || "WF equation: equation input differs from source root".to_string();
  let Some(source_domain) = source_args.first() else {
    return Err(input_differs());
  };
  if !alpha_eq_skip_mdata(&spine_type, source_domain) {
    return Err(input_differs());
  }
  let domain_differs =
    || "WF equation: target domain differs from permutation".to_string();
  let Some(target_spine) = spine.permute(&l.sigma) else {
    return Err(domain_differs());
  };
  let target_type = spine_type_m(&target_spine, "WF equation")?;
  let Some(target_domain) = target_args.first() else {
    return Err(domain_differs());
  };
  if !alpha_eq_skip_mdata(&target_type, target_domain) {
    return Err(domain_differs());
  }
  let at_point =
    |argument: &Expr| substitute_wf_local(&point.fvar, &statement, argument);
  let step_head = cnst(&step_name, &step_levels);
  let mut leaves = Vec::new();
  for index in 0..l.n {
    let name = tm.fresh_fvar();
    let summand = tm_idx(&spine.leaves, index, "WF equation: summand")?;
    let payload = Local {
      fvar: name,
      user_name: root_name("payload"),
      typ: summand.clone(),
      bi: BinderInfo::Default,
    };
    let position = *tm_idx(&l.sigma, index, "WF equation: permutation")?;
    let source_input = |_: &mut TState, value: Expr| -> R<Expr> {
      let Some(input) = mk_inj(&spine, index, &value) else {
        return Err(
          "WF equation: source injection reconstruction failed".into(),
        );
      };
      Ok(at_point(&input))
    };
    let target_input = |_: &mut TState, value: Expr| -> R<Expr> {
      let Some(input) = mk_inj(&target_spine, position, &value) else {
        return Err(
          "WF equation: target injection reconstruction failed".into(),
        );
      };
      let mut args = target_args.clone();
      args.push(input);
      Ok(mk_app_n(step_head.clone(), &args))
    };
    let body = split_psigma(
      tm,
      &source_input,
      &target_input,
      WF_DEPTH,
      &payload.typ,
      &|x| x,
      &payload.expr(),
    )?;
    leaves.push(mk_lambda(&[payload], &body));
  }
  let tree = Tree {
    spine,
    w: Level::zero(),
    motive_name: point.user_name.clone(),
    motive_body: abstract_fvars(slice::from_ref(&point.fvar), &statement),
    major: point.expr(),
    leaves,
    extras: Vec::new(),
    alt_names: Vec::new(),
  };
  let Some(body) = tree.build() else {
    return Err("WF equation: source-domain case reconstruction failed".into());
  };
  let value = close_binders(true, &parameters, &body)?;
  Ok(Decl { name: new_name.clone(), typ, value, ..equation.clone() })
}

/// `transportWF`: the owned root, proof, member and equation transport of a
/// well-founded clique: the packed function `packed` (renamed `new_name`),
/// its abstracted `proofs`, the `members` (Lean's order) and the carried
/// `lemmas` (each with its new name), under the clique permutation `sigma`.
/// The prologue (the proofs' fixed prefixes, [`fixed_proof_perms`]) and the
/// epilogue (the proofs' numbering and the renames, [`number_proofs`]) are the
/// ones the `partial_fixpoint` transport shares.
pub fn transport_wf(
  tm: &mut TState,
  members: &[Decl],
  packed: &Decl,
  proofs: &[Decl],
  sigma: &[usize],
  new_name: &Name,
  lemmas: &[(Decl, Name)],
  const_of: ConstOf<'_>,
) -> R<TransportOutput> {
  let initial = wf_layout(members, packed, sigma, new_name)?;
  let FixedProofs { fixed, body, uses, proof_perm, .. } = fixed_proof_perms(
    tm,
    proofs,
    initial.num_fixed,
    &initial.fixed_perm,
    &packed.value,
  )?;
  let is_packed_lemma = |name: &Name| matches!(name.as_data(), NameData::Str(parent, _, _) if *parent == packed.name);
  // the packed function's own lemmas take its fixed parameters in the new
  // order
  let mut proof_perm = proof_perm;
  for (declaration, _) in lemmas {
    if is_packed_lemma(&declaration.name) {
      proof_perm.insert(declaration.name.clone(), initial.fixed_perm.clone());
    }
  }
  let l = WfLayout { proof_perm, ..initial };
  let keep = |_: &mut TState, x: &Expr| -> R<Expr> { Ok(x.clone()) };
  let rewrite = |tm: &mut TState, x: &Expr| {
    rewrite_owned_wf_uses(tm, &l, packed, TRANSPORT_FUEL, x)
  };
  let schema = decode_wf_root(tm, &l, &body)?;
  let mut well_founded_proof: Option<(Name, Expr, Expr)> = None;
  if let [_, _, _, source_witness, _] = schema.source_arguments.as_slice()
    && let Some((name, levels, arguments)) = const_app(source_witness)
    && let Some(declaration) = proofs.iter().find(|p| p.name == name)
  {
    let identity: Vec<Level> = declaration
      .level_params
      .iter()
      .map(|p| Level::param(p.clone()))
      .collect();
    if levels != identity {
      return Err(
        "WF ownership: well-founded proof uses a nonidentity universe \
         substitution"
          .into(),
      );
    }
    let mut parameters: Vec<Local> = Vec::new();
    for argument in &arguments {
      let stripped = strip_mdata(argument);
      let ExprData::Fvar(identity, _) = stripped.as_data() else {
        return Err(
          "WF ownership: well-founded proof argument is not a fixed parameter"
            .into(),
        );
      };
      let Some(parameter) = fixed.iter().find(|f| f.fvar == *identity) else {
        return Err(
          "WF ownership: well-founded proof uses a foreign parameter".into(),
        );
      };
      parameters.push(parameter.clone());
    }
    let permutation = l.proof_perm.get(&name).cloned().unwrap_or_default();
    let prefix_differs = || {
      "WF ownership: well-founded proof prefix differs from its decoded \
       application"
        .to_string()
    };
    if permutation.len() != parameters.len() {
      return Err(prefix_differs());
    }
    let ExprData::Const(_, root_levels, _) = schema.head.as_data() else {
      return Err("WF ownership: missing fixpoint universe".into());
    };
    let Some(domain_level) = root_levels.first() else {
      return Err("WF ownership: missing domain universe".into());
    };
    let [_, _, target_relation, target_witness] =
      schema.target_arguments.as_slice()
    else {
      return Err(
        "WF ownership: the decoded root has no well-founded witness".into(),
      );
    };
    let target_type = spine_type_m(&schema.target_spine, "WF ownership")?;
    let goal = mk_app_n(
      cnst(&dotted("WellFounded"), slice::from_ref(domain_level)),
      &[target_type, target_relation.clone()],
    );
    let witness = mk_app_n(
      cnst(&dotted("Lean.opaqueId"), &[Level::zero()]),
      &[goal.clone(), target_witness.clone()],
    );
    let Some(reordered) = reorder(&permutation, &parameters) else {
      return Err(prefix_differs());
    };
    well_founded_proof = Some((
      name,
      close_binders(false, &reordered, &goal)?,
      close_binders(true, &reordered, &witness)?,
    ));
  }
  let transform_root = |tm: &mut TState, value: &Expr| -> R<Expr> {
    let transformed = conjugate_wf_root(tm, &l, value, const_of)?;
    let transformed = match &well_founded_proof {
      Some(_) => {
        // the root keeps Lean's witness argument, an application of the
        // abstracted proof (which is transported below)
        let (_, source_args) = get_app_fn_args(value);
        let (head, mut target_args) = get_app_fn_args(&transformed);
        let Some(source_witness) = source_args.get(3) else {
          return Err(
            "WF ownership: the fixpoint root has no well-founded witness \
             argument"
              .into(),
          );
        };
        let Some(slot) = target_args.get_mut(3) else {
          return Err(
            "WF ownership: the transported root has no well-founded witness \
             argument"
              .into(),
          );
        };
        *slot = source_witness.clone();
        mk_app_n(head, &target_args)
      },
      None => transformed,
    };
    rewrite(tm, &transformed)
  };
  let value = with_reordered_binders2(
    tm,
    true,
    l.num_fixed,
    &l.fixed_perm,
    &packed.value,
    &keep,
    &transform_root,
  )?;
  let conjugate_type = |tm: &mut TState, x: &Expr| conjugate_wf_type(tm, &l, x);
  let typ = with_reordered_binders2(
    tm,
    false,
    l.num_fixed,
    &l.fixed_perm,
    &packed.typ,
    &keep,
    &conjugate_type,
  )?;
  let packed_target =
    Decl { name: new_name.clone(), typ, value, ..packed.clone() };
  let mut output = vec![Transported::ok(packed_target.clone())];
  let fixed_names: Vec<Name> = fixed.iter().map(|x| x.fvar.clone()).collect();
  let fixed_exprs = exprs(&fixed);
  for proof in proofs {
    if let Some((name, typ, value)) = &well_founded_proof
      && *name == proof.name
    {
      output.push(Transported::ok(Decl {
        typ: typ.clone(),
        value: value.clone(),
        ..proof.clone()
      }));
      continue;
    }
    let permutation =
      l.proof_perm.get(&proof.name).cloned().unwrap_or_default();
    let positions = uses.get(&proof.name).cloned().unwrap_or_default();
    let transform =
      |tm: &mut TState, is_lam: bool, expression: &Expr| -> R<Expr> {
        let (parameters, body) =
          open_binders(tm, is_lam, permutation.len(), expression)?;
        let disagrees =
          || "WF obligation: proof prefix disagrees with its use".to_string();
        if positions.len() != parameters.len() {
          return Err(disagrees());
        }
        let mut arguments = fixed_exprs.clone();
        for (&position, parameter) in positions.iter().zip(&parameters) {
          let Some(slot) = arguments.get_mut(position) else {
            return Err(
              "WF obligation: fixed proof argument is out of scope".into(),
            );
          };
          *slot = parameter.expr();
        }
        let instantiate =
          |x: &Expr| inst_locals(&abstract_fvars(&fixed_names, x), &arguments);
        let proof_schema = schema.map_expressions(&instantiate);
        let body = rewrite_wf_obligations(
          tm,
          &proof_schema,
          &l.sigma,
          TRANSPORT_FUEL,
          &body,
        )?;
        let body = rewrite(tm, &body)?;
        let Some(reordered) = reorder(&permutation, &parameters) else {
          return Err(disagrees());
        };
        close_binders(is_lam, &reordered, &body)
      };
    let typ = transform(tm, false, &proof.typ)?;
    let value = transform(tm, true, &proof.value)?;
    output.push(Transported::ok(Decl { typ, value, ..proof.clone() }));
  }
  for member in members {
    let typ = rewrite(tm, &member.typ)?;
    let value = rewrite(tm, &member.value)?;
    output.push(Transported::ok(Decl { typ, value, ..member.clone() }));
  }
  let eq_def = mk_str(&packed.name, "eq_def");
  for (lemma, name) in lemmas {
    if lemma.name == eq_def {
      let Some(functional) = schema.source_arguments.last() else {
        return Err("WF equation: missing functional".into());
      };
      let (_, body) = peel_lams(2, functional);
      let Some(tree) = decode_tree(l.n, &body) else {
        return Err("WF equation: missing source refinement tree".into());
      };
      if !tree.leaves.iter().all(|x| leaf_reduces(WF_DEPTH, x)) {
        return Err(
          "WF equation: source matcher needs argument-pushing proof \
           reconstruction"
            .into(),
        );
      }
      output.push(Transported::ok(transport_owned_wf_eq_def(
        tm,
        &l,
        packed,
        &packed_target,
        lemma,
        name,
      )?));
    } else if is_packed_lemma(&lemma.name) {
      let typ = with_reordered_binders2(
        tm,
        false,
        l.num_fixed,
        &l.fixed_perm,
        &lemma.typ,
        &keep,
        &rewrite,
      )?;
      let value = with_reordered_binders2(
        tm,
        true,
        l.num_fixed,
        &l.fixed_perm,
        &lemma.value,
        &keep,
        &rewrite,
      )?;
      output.push(Transported::ok(Decl {
        name: name.clone(),
        typ,
        value,
        ..lemma.clone()
      }));
    } else {
      let typ = rewrite(tm, &lemma.typ)?;
      let value = rewrite(tm, &lemma.value)?;
      output.push(Transported::ok(Decl {
        name: name.clone(),
        typ,
        value,
        ..lemma.clone()
      }));
    }
  }
  Ok(number_proofs(
    output,
    &packed.name,
    new_name,
    proofs,
    lemmas,
    &packed_target.value,
  ))
}

#[cfg(test)]
mod tests {
  use std::slice;

  use rustc_hash::FxHashMap;

  use ix_common::env::{BinderInfo, Expr, Level, Name};

  use super::{
    Transported, WfLayout, fixed_proof_perms, number_proofs, owned_wf_calls,
    rewrite_owned_wf_uses, sort_idx_by_key, transport_wf,
  };
  use crate::compile::pass3::clique::basic::{
    Decl, Local, TState, abstract_fvars, alpha_eq_skip_mdata, bvar, cnst,
    dotted, fvar, mk_app_n, mk_forall, mk_lambda, peel_lams, root_name, sort0,
  };
  use crate::compile::pass3::clique::packing::{
    PackKind, Spine, Tree, decode_tree, mk_inj,
  };
  use crate::compile::pass3::expr::get_app_fn_args;

  fn c(s: &str) -> Expr {
    cnst(&dotted(s), &[])
  }

  fn one() -> Level {
    Level::succ(Level::zero())
  }

  fn local(fvar: &str, user: &str, typ: Expr) -> Local {
    Local {
      fvar: dotted(fvar),
      user_name: root_name(user),
      typ,
      bi: BinderInfo::Default,
    }
  }

  fn def(name: &str, typ: Expr, value: Expr) -> Decl {
    Decl { name: dotted(name), level_params: vec![], typ, value, is_thm: false }
  }

  fn names(xs: &[&str]) -> Vec<Name> {
    xs.iter().map(|x| dotted(x)).collect()
  }

  #[test]
  fn sort_idx_by_key_keeps_ties_in_index_order() {
    assert_eq!(sort_idx_by_key(&[2, 0, 2, 1, 0]), vec![1, 4, 3, 0, 2]);
    assert_eq!(sort_idx_by_key(&[1, 1]), vec![0, 1]);
    assert_eq!(sort_idx_by_key(&[3, 1, 2]), vec![1, 2, 0]);
    assert_eq!(sort_idx_by_key(&[]), Vec::<usize>::new());
  }

  #[test]
  fn fixed_proof_perms_and_numbering() {
    // `λ (A B : Type). F (p1 B A x) (p2 A) (p3 A A) (p1 A B)`: under the two
    // binders `A` is `bvar 1` and `B` is `bvar 0`
    let ty = Expr::sort(one());
    let (a, b) = (bvar(1), bvar(0));
    let body = mk_app_n(
      c("F"),
      &[
        mk_app_n(c("p1"), &[b.clone(), a.clone(), c("x")]),
        Expr::app(c("p2"), a.clone()),
        mk_app_n(c("p3"), &[a.clone(), a.clone()]),
        mk_app_n(c("p1"), &[a, b]),
      ],
    );
    let value = Expr::lam(
      root_name("A"),
      ty.clone(),
      Expr::lam(root_name("B"), ty.clone(), body, BinderInfo::Default),
      BinderInfo::Default,
    );
    let proofs: Vec<Decl> =
      ["p1", "p2", "p3"].iter().map(|p| def(p, sort0(), sort0())).collect();
    let mut tm = TState::default();
    // the new fixed order is `B, A`
    let fp = fixed_proof_perms(&mut tm, &proofs, 2, &[1, 0], &value).unwrap();
    assert_eq!(tm.next, 2);
    assert_eq!(fp.fixed.len(), 2);
    assert_eq!(fp.proof_names.len(), 3);
    // the first application met records the fixed prefix
    let uses: FxHashMap<Name, Vec<usize>> = [
      (dotted("p1"), vec![1, 0]),
      (dotted("p2"), vec![0]),
      (dotted("p3"), vec![0, 0]),
    ]
    .into_iter()
    .collect();
    assert_eq!(fp.uses, uses);
    let perms: FxHashMap<Name, Vec<usize>> = [
      (dotted("p1"), vec![0, 1]),
      (dotted("p2"), vec![0]),
      // the same fixed parameter twice: index order
      (dotted("p3"), vec![0, 1]),
    ]
    .into_iter()
    .collect();
    assert_eq!(fp.proof_perm, perms);
    // Lean's fixed order kept: `p1`'s binders are swapped
    let fp = fixed_proof_perms(&mut tm, &proofs, 2, &[0, 1], &value).unwrap();
    assert_eq!(fp.proof_perm.get(&dotted("p1")), Some(&vec![1, 0]));
    // refusals
    assert_eq!(
      fixed_proof_perms(&mut tm, &proofs, 2, &[0, 0], &value).err(),
      Some(
        "clique transport: the fixed-parameter order is not a permutation"
          .to_string()
      )
    );
    assert_eq!(
      fixed_proof_perms(&mut tm, &proofs, 2, &[0], &value).err(),
      Some(
        "clique transport: proof p1 receives a fixed parameter outside the \
         fixed order"
          .to_string()
      )
    );

    // numbering: the proofs the value mentions first, in first-occurrence
    // order, then the others; lemma renames; every declaration renamed
    let packed_value = mk_app_n(c("G"), &[c("p3"), c("p1")]);
    let output = vec![
      Transported::ok(def("new", sort0(), packed_value.clone())),
      Transported::ok(def("p2", c("L"), sort0())),
      Transported {
        decl: def("L", sort0(), c("p1")),
        fallback: Some("kept".into()),
      },
    ];
    let lemmas = vec![
      (def("L", sort0(), sort0()), dotted("L2")),
      (def("M", sort0(), sort0()), dotted("M")),
    ];
    let out = number_proofs(
      output,
      &dotted("old"),
      &dotted("new"),
      &proofs,
      &lemmas,
      &packed_value,
    );
    let renames: Vec<(Name, Name)> = [
      ("old", "new"),
      ("p3", "new._proof_1"),
      ("p1", "new._proof_2"),
      ("p2", "new._proof_3"),
      ("L", "L2"),
    ]
    .iter()
    .map(|(a, b)| (dotted(a), dotted(b)))
    .collect();
    assert_eq!(out.renames, renames);
    let got: Vec<Name> =
      out.decls.iter().map(|t| t.decl.name.clone()).collect();
    assert_eq!(got, names(&["new", "new._proof_3", "L2"]));
    assert_eq!(
      out.decls[0].decl.value,
      mk_app_n(c("G"), &[c("new._proof_1"), c("new._proof_2")])
    );
    assert_eq!(out.decls[1].decl.typ, c("L2"));
    assert_eq!(out.decls[2].decl.value, c("new._proof_2"));
    assert_eq!(out.decls[2].fallback.as_deref(), Some("kept"));
  }

  /// A two-member well-founded clique by hand, as Lean encodes
  /// `f : Nat → Nat` and `g : Int → Nat` by `WellFounded.Nat.fix` with a
  /// constant measure: `f` calls `g` through an abstracted decreasing proof.
  struct Clique {
    members: Vec<Decl>,
    packed: Decl,
    proofs: Vec<Decl>,
  }

  /// `∀ (y : α), InvImage α Nat lt h y x → Nat`, the recursive binder's
  /// type at the point `x`.
  fn rec_type(alpha: &Expr, h: &Expr, x: &Expr) -> Expr {
    let y = local("t.y", "y", alpha.clone());
    let rel = mk_app_n(
      cnst(&dotted("InvImage"), &[one(), one()]),
      &[alpha.clone(), c("Nat"), c("Nat.lt"), h.clone(), y.expr(), x.clone()],
    );
    let hy = local("t.h", "h", rel);
    mk_forall(&[y, hy], &c("Nat"))
  }

  /// The constant measure `λ (x : α). Nat.zero`.
  fn measure(alpha: &Expr) -> Expr {
    Expr::lam(root_name("x"), alpha.clone(), c("Nat.zero"), BinderInfo::Default)
  }

  fn spine(leaves: Vec<Expr>) -> Spine {
    Spine { kind: PackKind::Psum, leaves, lvls: vec![one(), one()] }
  }

  fn clique() -> Clique {
    let (nat, int) = (c("Nat"), c("Int"));
    let s = spine(vec![nat.clone(), int.clone()]);
    let alpha = s.typ().unwrap();
    let h = measure(&alpha);
    let proof_name = "f._mutual._proof_1";
    // the refinement tree `F = λ x a. PSum.casesOn x (λ p r. …) (λ p r. …) a`
    let leaf =
      |i: usize, summand: &Expr, body: &dyn Fn(&Local, &Local) -> Expr| {
        let p = local("t.p", "p", summand.clone());
        let point = mk_inj(&s, i, &p.expr()).unwrap();
        let r = local("t.r", "r", rec_type(&alpha, &h, &point));
        let body = body(&p, &r);
        mk_lambda(&[p, r], &body)
      };
    let to_g = mk_inj(&s, 1, &c("i0")).unwrap();
    let to_f = mk_inj(&s, 0, &c("n0")).unwrap();
    let leaves = vec![
      leaf(0, &nat, &|p, r| {
        mk_app_n(r.expr(), &[to_g.clone(), Expr::app(c(proof_name), p.expr())])
      }),
      leaf(1, &int, &|_, r| mk_app_n(r.expr(), &[to_f.clone(), c("h0")])),
    ];
    let m = local("t.m", "x", alpha.clone());
    let a = local("t.a", "a", rec_type(&alpha, &h, &m.expr()));
    let motive_body =
      abstract_fvars(slice::from_ref(&m.fvar), &mk_forall(&[a], &nat));
    let x = local("t.x", "x", alpha.clone());
    let a = local("t.a", "a", rec_type(&alpha, &h, &x.expr()));
    let tree = Tree {
      spine: s.clone(),
      w: one(),
      motive_body,
      motive_name: root_name("x"),
      major: x.expr(),
      leaves,
      extras: vec![a.expr()],
      alt_names: vec![],
    }
    .build()
    .unwrap();
    let functional = mk_lambda(&[x, a], &tree);
    let codomain = Expr::lam(
      root_name("x"),
      alpha.clone(),
      nat.clone(),
      BinderInfo::Default,
    );
    let root = mk_app_n(
      cnst(&dotted("WellFounded.Nat.fix"), &[one(), one()]),
      &[alpha.clone(), codomain, h.clone(), functional],
    );
    let packed = def(
      "f._mutual",
      Expr::all(
        root_name("x"),
        alpha.clone(),
        nat.clone(),
        BinderInfo::Default,
      ),
      root,
    );
    let member = |name: &str, i: usize, summand: &Expr| {
      let call = Expr::app(c("f._mutual"), mk_inj(&s, i, &bvar(0)).unwrap());
      def(
        name,
        Expr::all(
          root_name("n"),
          summand.clone(),
          nat.clone(),
          BinderInfo::Default,
        ),
        Expr::lam(root_name("n"), summand.clone(), call, BinderInfo::Default),
      )
    };
    let q = local("t.q", "p", nat.clone());
    let obligation = mk_app_n(
      cnst(&dotted("InvImage"), &[one(), one()]),
      &[
        alpha.clone(),
        nat.clone(),
        c("Nat.lt"),
        h,
        to_g.clone(),
        mk_inj(&s, 0, &q.expr()).unwrap(),
      ],
    );
    let proof = def(
      proof_name,
      mk_forall(slice::from_ref(&q), &obligation),
      mk_lambda(&[q], &c("pf0")),
    );
    Clique {
      members: vec![member("f", 0, &nat), member("g", 1, &int)],
      packed,
      proofs: vec![proof],
    }
  }

  #[test]
  fn transports_a_two_member_clique() {
    let k = clique();
    let mut tm = TState::default();
    let new_name = dotted("g._mutual");
    let out = transport_wf(
      &mut tm,
      &k.members,
      &k.packed,
      &k.proofs,
      &[1, 0],
      &new_name,
      &[],
      &|_| None,
    )
    .unwrap();
    let pairs = |xs: &[(&str, &str)]| -> Vec<(Name, Name)> {
      xs.iter().map(|(a, b)| (dotted(a), dotted(b))).collect()
    };
    assert_eq!(
      out.renames,
      pairs(&[
        ("f._mutual", "g._mutual"),
        ("f._mutual._proof_1", "g._mutual._proof_1")
      ])
    );
    let got: Vec<Name> =
      out.decls.iter().map(|t| t.decl.name.clone()).collect();
    assert_eq!(got, names(&["g._mutual", "g._mutual._proof_1", "f", "g"]));
    assert!(out.decls.iter().all(|t| t.fallback.is_none()));
    // the canonical packing is `PSum Int Nat`
    let (nat, int) = (c("Nat"), c("Int"));
    let t = spine(vec![int.clone(), nat.clone()]);
    let alpha = t.typ().unwrap();
    let h = measure(&alpha);
    assert_eq!(
      out.decls[0].decl.typ,
      Expr::all(
        root_name("x"),
        alpha.clone(),
        nat.clone(),
        BinderInfo::Default
      )
    );
    // the members call the canonical packed function at the permuted
    // injections
    let member = |i: usize, summand: &Expr| {
      let call = Expr::app(c("g._mutual"), mk_inj(&t, i, &bvar(0)).unwrap());
      Expr::lam(root_name("n"), summand.clone(), call, BinderInfo::Default)
    };
    assert_eq!(out.decls[2].decl.value, member(1, &nat));
    assert_eq!(out.decls[3].decl.value, member(0, &int));
    // the decreasing obligation is restated over the canonical packing
    let q = local("t.q", "p", nat.clone());
    let obligation = mk_app_n(
      cnst(&dotted("InvImage"), &[one(), one()]),
      &[
        alpha.clone(),
        nat.clone(),
        c("Nat.lt"),
        h.clone(),
        mk_inj(&t, 0, &c("i0")).unwrap(),
        mk_inj(&t, 1, &q.expr()).unwrap(),
      ],
    );
    assert!(alpha_eq_skip_mdata(
      &out.decls[1].decl.typ,
      &mk_forall(&[q], &obligation)
    ));
    // `f`'s body is the canonical second leaf, its call into `g` at the
    // canonical first summand, through the renamed proof
    let packed_value = &out.decls[0].decl.value;
    let (head, args) = get_app_fn_args(packed_value);
    assert_eq!(head, cnst(&dotted("WellFounded.Nat.fix"), &[one(), one()]));
    assert_eq!(args.len(), 4);
    assert_eq!(args[0], alpha);
    let (_, body) = peel_lams(2, &args[3]);
    let tree = decode_tree(2, &body).unwrap();
    let p = local("t.p", "p", nat.clone());
    let r = local(
      "t.r",
      "r",
      rec_type(&alpha, &h, &mk_inj(&t, 1, &p.expr()).unwrap()),
    );
    let call = mk_app_n(
      r.expr(),
      &[
        mk_inj(&t, 0, &c("i0")).unwrap(),
        Expr::app(c("g._mutual._proof_1"), p.expr()),
      ],
    );
    assert!(alpha_eq_skip_mdata(&tree.leaves[1], &mk_lambda(&[p, r], &call)));

    // transporting back gives Lean's clique again
    let mut tm = TState::default();
    let members = [out.decls[3].decl.clone(), out.decls[2].decl.clone()];
    let back = transport_wf(
      &mut tm,
      &members,
      &out.decls[0].decl,
      &[out.decls[1].decl.clone()],
      &[1, 0],
      &dotted("f._mutual"),
      &[],
      &|_| None,
    )
    .unwrap();
    let originals = [&k.packed, &k.proofs[0], &k.members[1], &k.members[0]];
    assert_eq!(back.decls.len(), originals.len());
    for (got, want) in back.decls.iter().zip(originals) {
      assert_eq!(got.decl.name, want.name);
      assert!(alpha_eq_skip_mdata(&got.decl.typ, &want.typ));
      assert!(alpha_eq_skip_mdata(&got.decl.value, &want.value));
    }
  }

  #[test]
  fn refusals_carry_the_lean_texts() {
    let k = clique();
    let mut tm = TState::default();
    let run = |tm: &mut TState, sigma: &[usize]| {
      transport_wf(
        tm,
        &k.members,
        &k.packed,
        &k.proofs,
        sigma,
        &dotted("g._mutual"),
        &[],
        &|_| None,
      )
      .err()
    };
    assert_eq!(run(&mut tm, &[0, 0]), Some("wfLayout: bad permutation".into()));
    assert_eq!(
      run(&mut tm, &[1, 0, 2]),
      Some("wfLayout: bad permutation".into())
    );
    // a member that does not call the packed function
    let mut members = k.members.clone();
    members[1].value =
      Expr::lam(root_name("n"), c("Int"), c("Nat.zero"), BinderInfo::Default);
    assert_eq!(
      transport_wf(
        &mut tm,
        &members,
        &k.packed,
        &k.proofs,
        &[1, 0],
        &dotted("g._mutual"),
        &[],
        &|_| None,
      )
      .err(),
      Some("member g: not an application of the packed function".into())
    );
  }

  // These neighbours distinguish fuel-sensitive and allocating visits even
  // when the same expression occurs more than once in the DAG.
  fn layout_and_packed() -> (WfLayout, Decl) {
    let s = Spine {
      kind: PackKind::Psum,
      leaves: vec![sort0(), sort0()],
      lvls: vec![Level::zero(), Level::zero()],
    };
    let layout = WfLayout {
      n: 2,
      sigma: vec![1, 0],
      mutual_name: root_name("source"),
      new_mutual_name: root_name("target"),
      num_fixed: 0,
      fixed_perm: vec![],
      leaves: s.leaves.clone(),
      proof_perm: FxHashMap::default(),
      packed_lemmas: Default::default(),
      member_fixed: vec![],
    };
    let packed = Decl {
      name: layout.mutual_name.clone(),
      level_params: vec![],
      typ: Expr::all(
        root_name("input"),
        s.typ().unwrap(),
        sort0(),
        BinderInfo::Default,
      ),
      value: cnst(
        &dotted("WellFounded.Nat.fix"),
        &[Level::zero(), Level::zero()],
      ),
      is_thm: false,
    };
    (layout, packed)
  }

  #[test]
  fn shared_visits_preserve_fuel_refusal_and_success() {
    let (layout, _) = layout_and_packed();
    let shared = Expr::app(c("f"), c("a"));
    let term = Expr::app(shared.clone(), Expr::app(shared.clone(), shared));
    let mut tm = TState::default();
    assert_eq!(
      owned_wf_calls(&mut tm, &layout, &bvar(0), 3, 0, &term),
      Err("WF ownership: body recursion bound".into())
    );
    assert_eq!(
      owned_wf_calls(&mut tm, &layout, &bvar(0), 4, 0, &term),
      Ok(term)
    );
  }

  #[test]
  fn shared_allocating_visits_preserve_fresh_counter() {
    let (layout, packed) = layout_and_packed();
    let use_packed = cnst(&layout.mutual_name, &[]);
    let term = mk_app_n(c("consume"), &[use_packed.clone(), use_packed]);
    let mut tm = TState::default();
    let out = rewrite_owned_wf_uses(&mut tm, &layout, &packed, 10, &term);
    assert!(out.is_ok());
    // each bare use allocates its input and one payload per summand
    assert_eq!(tm.next, 6);
    let plain = Expr::app(c("f"), fvar(&dotted("x")));
    assert_eq!(
      rewrite_owned_wf_uses(&mut tm, &layout, &packed, 10, &plain),
      Ok(plain)
    );
    assert_eq!(tm.next, 6);
  }
}
