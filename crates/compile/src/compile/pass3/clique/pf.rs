//! The `partial_fixpoint` transport (a port of
//! `Ix/Compile/Pass/Clique/PartialFixpoint.lean` and `PFConjugation.lean`).
//!
//! Lean's encoding (`Elab/PreDefinition/PartialFixpoint/Main.lean`,
//! `Elab/Tactic/Monotonicity.lean`, Lean 4.34.1), as the transport sees it:
//!
//! * `f₀.mutual : ∀ fixed, γ` with `γ = T₀ ×' (T₁ ×' …)` (`PProdN.pack`), its
//!   value `λ fixed. Order.fix γ I (λ x. ⟨F₀[x], …⟩) hmono`, where `I` is the
//!   instance tree `instCCPOPProd T₀ (…) i₀ (…)` (`mkPackedPPRodInstance`;
//!   `instCompleteLatticePProd` for the lattice-theoretic fixpoints) and the
//!   recursive calls in `F_i` are projection paths `x.2.1` of the packed
//!   variable (`PProdN.proj`);
//! * the monotonicity proof `hmono` (abstracted as `f₀.mutual._proof_1`):
//!   statement `monotone (α := γ) (toPartialOrder γ I) γ O (λ x. ⟨…⟩)`, `O`
//!   the tree `instPartialOrderPProd T₀ (…) (toPartialOrder T₀ i₀) (…)`;
//!   value the `PProd.monotone_mk` tree over the per-function proofs
//!   (`mkMonoPProd`, `PProdN.genMk`), whose `g` arguments are the remaining
//!   tuples;
//! * in each per-function proof, the sub-proof of a recursive call through
//!   the path to component `j` is built by `solveMonoCall` inside out:
//!   `monotone_id`, then one `PProd.monotone_fst`/`monotone_snd` per step (at
//!   that step's `PProd` node, with the instances `toPartialOrder` of the
//!   node's leaf and rest), then `monotone_apply` per argument; the path
//!   itself also occurs in application form (`PProd.fst (PProd.snd x)`);
//! * the members `f_i := λ ps. (f₀.mutual fixed).2.1 varying`.
//!
//! The first half of this module (`PartialFixpoint.lean`) holds the layout
//! ([`pf_layout`]), the decoding of packed paths and of `solveMonoCall`'s
//! chains, and their regeneration for a canonical path. The builders are
//! total: a spine whose leaves, levels or instances differ in number, or a
//! position past them, gives `None`, never a default term.
//!
//! The second half (`PFConjugation.lean`) is the decoder-owned transport.
//! Only the identities the decoders establish move: the recursive binder and
//! the output tuple of Lean's root functional, the packed constant at its
//! full fixed-argument application, the monotonicity proof's `monotone_mk`
//! tree and the per-function proofs' applied theorems (through the argument
//! roles of each theorem's declared telescope), and the equation proofs'
//! fixpoint equation, member projection and congruences. Inner user binders
//! keep their identity, even when their type is the packing; a
//! packing-shaped construct elsewhere in a term (a user value of the packed
//! type) is left alone. The monotonicity proofs' `monotone_fst`/
//! `monotone_snd` chains are regenerated for the canonical path, with the
//! composition fallback (`monotone_compose (mono φ) h`, recorded as `SHAPE`)
//! for a per-function proof the transport cannot follow. [`transport_pf`]
//! runs it over a whole clique.
//!
//! The lattice-theoretic fixpoints (`inductive_fixpoint`,
//! `coinductive_fixpoint`) spell a component `∀ x, ImplicationOrder` (or
//! `ReverseImplicationOrder`) where the packed constant's type says
//! `∀ x, Prop`; the packing is recognised up to that alias
//! ([`norm_order_alias`]).
//!
//! Why the members stay faithful (stated here, not checked in this tree):
//! with `φ` the re-association onto the canonical packing, an order
//! isomorphism of the `PProd` orders, the canonical functional is
//! `φ ∘ F ∘ φ⁻¹` up to β and projection of a constructor; `Lean.Order.fix`
//! (and the lattice's least fixpoint) commutes with an order isomorphism, so
//! component `σ i` of the canonical fixpoint is component `i` of Lean's.
//!
//! The walks over shared proof terms are memoised: [`transport_owned_mono`]
//! by [`memo_transport`] (its key carries the fuel; a visit that allocates
//! fresh variables is never cached), [`rewrite_pf_packed_uses`] by the
//! subterm and the fuel, and a subterm without the packed constant is
//! returned as it is (with the walk's own fuel check, [`mention_heights`]).
//! Neither changes a result, a refusal or the fresh-name stream; the
//! equation proof walk is a chain and needs neither. As everywhere in the
//! clique transport, a Rust memo confirms a hit by raw equality
//! ([`ExactMemo`]) where Lean's is keyed by the expression's hash; the
//! results agree whenever equal hashes denote equal expressions.

use std::slice;

use rustc_hash::FxHashMap;

use ix_common::env::{BinderInfo, Expr, ExprData, Level, Name};

use super::basic::{
  ConstOf, Decl, R, TState, TransportMemo, alpha_eq_skip_mdata, bvar, bvar_idx,
  cnst, const_app, dotted, eq_sorted, exprs, extract, forall_arity, fvar,
  inst_locals, instantiate_rev, inv_perm, is_bvar, is_perm, lam_arity,
  lift_loose, loose_all_at_least, memo_transport, mentions_fvar, mk_app_n,
  n_and, n_and_intro, n_pprod, n_pprod_fst, n_pprod_mk, n_pprod_snd,
  name_to_string, no_dups, peel_foralls, peel_lams, permute, root_name, sort0,
  tm_idx,
};
use super::bounds::TRANSPORT_FUEL;
use super::packing::{
  PackKind, Spine, apply_projs, decode_spine, decode_tuple,
  match_packing_leaves, mk_node, mk_tuple,
};
use super::structural::{path_prefix, proj_chain, steps_fit};
use super::telescope::{
  beta_app, close_binders, open_binders, reorder, with_reordered_binders2,
};
use super::wf::{
  FixedProofs, TransportOutput, Transported, fixed_proof_perms, number_proofs,
  sort_idx_by_key, spine_type_m,
};
use crate::compile::pass3::expr::{
  ExactMemo, get_app_fn_args, nat_usize, strip_mdata, subst_levels,
};

// ---------------------------------------------------------------------------
// Names
// ---------------------------------------------------------------------------

/// `nOrderFix`.
pub fn n_order_fix() -> Name {
  dotted("Lean.Order.fix")
}
/// `nInstCCPOPProd`.
pub fn n_inst_ccpo_pprod() -> Name {
  dotted("Lean.Order.instCCPOPProd")
}
/// `nInstLatticePProd`.
pub fn n_inst_lattice_pprod() -> Name {
  dotted("Lean.Order.instCompleteLatticePProd")
}
/// `nInstPOPProd`.
pub fn n_inst_po_pprod() -> Name {
  dotted("Lean.Order.instPartialOrderPProd")
}
/// `nCCPOToPO`.
pub fn n_ccpo_to_po() -> Name {
  dotted("Lean.Order.CCPO.toPartialOrder")
}
/// `nLatticeToPO`.
pub fn n_lattice_to_po() -> Name {
  dotted("Lean.Order.CompleteLattice.toPartialOrder")
}
/// `nMonoMk`.
pub fn n_mono_mk() -> Name {
  dotted("Lean.Order.PProd.monotone_mk")
}
/// `nMonoFst`.
pub fn n_mono_fst() -> Name {
  dotted("Lean.Order.PProd.monotone_fst")
}
/// `nMonoSnd`.
pub fn n_mono_snd() -> Name {
  dotted("Lean.Order.PProd.monotone_snd")
}
/// `nMonoId`.
pub fn n_mono_id() -> Name {
  dotted("Lean.Order.monotone_id")
}
/// `nMonoCompose`.
pub fn n_mono_compose() -> Name {
  dotted("Lean.Order.monotone_compose")
}
/// `nImplicationOrder`.
pub fn n_implication_order() -> Name {
  dotted("Lean.Order.ImplicationOrder")
}
/// `nReverseImplicationOrder`.
pub fn n_reverse_implication_order() -> Name {
  dotted("Lean.Order.ReverseImplicationOrder")
}
/// `nMonotone`.
pub fn n_monotone() -> Name {
  dotted("Lean.Order.monotone")
}

/// `Spine.typeE`: the packing type of a spine where the caller is an
/// `Except` (a decoded spine, and any permutation of one, always has it);
/// the twin of [`spine_type_m`], with the same refusal (both are an [`R`]
/// here).
pub fn spine_type_e(s: &Spine, what: &str) -> R<Expr> {
  spine_type_m(s, what)
}

// ---------------------------------------------------------------------------
// Packing-shaped instance trees
// ---------------------------------------------------------------------------

/// `mkInstTree`: `h.{l_k, lev_{k+1}} D_k S_{k+1} i_k (tree k+1)`, the leaf
/// instance last; `None` when the spine and the instances do not fit.
pub fn mk_inst_tree(h: &Name, s: &Spine, insts: &[Expr]) -> Option<Expr> {
  let suf = s.suffixes()?;
  // Lean's `n - 1` (truncated at 0)
  let last = s.size().saturating_sub(1);
  let mut acc = insts.get(last)?.clone();
  for k in (0..last).rev() {
    let (r, lr) = suf.get(k + 1)?;
    acc = mk_app_n(
      cnst(h, &[s.lvls.get(k)?.clone(), lr.clone()]),
      &[s.leaves.get(k)?.clone(), r.clone(), insts.get(k)?.clone(), acc],
    );
  }
  Some(acc)
}

/// `decodeInstTree`: decode an instance tree over an `n`-leaf product,
/// checked by re-encoding.
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
  let ty = mk_app_n(
    cnst(&n_pprod(), &us),
    &[args.first()?.clone(), args.get(1)?.clone()],
  );
  let s = decode_spine(PackKind::Pprod, n, &ty)?;
  let mut insts = Vec::new();
  let mut cur = e.clone();
  for _ in 0..n.saturating_sub(1) {
    let (h2, _, a) = const_app(&cur)?;
    let [_, _, i, rest] = a.as_slice() else { return None };
    if h2 != h {
      return None;
    }
    insts.push(i.clone());
    cur = rest.clone();
  }
  insts.push(cur);
  if alpha_eq_skip_mdata(&mk_inst_tree(&h, &s, &insts)?, e) {
    Some((h, s, insts))
  } else {
    None
  }
}

// ---------------------------------------------------------------------------
// Paths in application form
// ---------------------------------------------------------------------------

/// `mkPathApp`: `PProd.snd (… (PProd.fst x))` to component `j` (the
/// `.1`/`.2` of a theorem statement, after instantiation); `None` past the
/// spine.
pub fn mk_path_app(s: &Spine, j: usize, x: &Expr) -> Option<Expr> {
  let n = s.size();
  let suf = s.suffixes()?;
  let mut acc = x.clone();
  for k in 0..j {
    let (r, lr) = suf.get(k + 1)?;
    acc = mk_app_n(
      cnst(&n_pprod_snd(), &[s.lvls.get(k)?.clone(), lr.clone()]),
      &[s.leaves.get(k)?.clone(), r.clone(), acc],
    );
  }
  // Lean's `j + 1 < n`
  if j < n.saturating_sub(1) {
    let (r, lr) = suf.get(j + 1)?;
    acc = mk_app_n(
      cnst(&n_pprod_fst(), &[s.lvls.get(j)?.clone(), lr.clone()]),
      &[s.leaves.get(j)?.clone(), r.clone(), acc],
    );
  }
  Some(acc)
}

/// `decodePathApp`: decode an application-form path: the spine (read from
/// the innermost step's type arguments), the component and the base; checked
/// by re-encoding.
pub fn decode_path_app(n: usize, e: &Expr) -> Option<(Spine, usize, Expr)> {
  let (fst, snd) = (n_pprod_fst(), n_pprod_snd());
  // collect the steps from the outside in
  let mut cur = e.clone();
  let mut steps: Vec<(Name, Vec<Level>, Expr, Expr)> = Vec::new();
  for _ in 0..n {
    let Some((h, us, args)) = const_app(&cur) else { break };
    let [a, b, x] = args.as_slice() else { break };
    if !(h == fst || h == snd) {
      break;
    }
    steps.push((h, us, a.clone(), b.clone()));
    cur = x.clone();
  }
  // the innermost step is at the packing's root (none without a step)
  let (_, us, a, b) = steps.last()?;
  let s = decode_spine(
    PackKind::Pprod,
    n,
    &mk_app_n(cnst(&n_pprod(), us), &[a.clone(), b.clone()]),
  )?;
  let ones = steps.iter().rev().take_while(|st| st.0 == snd).count();
  let j = if ones + 1 < n { ones } else { n.saturating_sub(1) };
  if alpha_eq_skip_mdata(&mk_path_app(&s, j, &cur)?, e) {
    Some((s, j, cur))
  } else {
    None
  }
}

// ---------------------------------------------------------------------------
// The layout
// ---------------------------------------------------------------------------

/// What the transport needs to know about a `partial_fixpoint` clique
/// (`PFLayout`).
#[derive(Clone, Debug)]
pub struct PfLayout {
  pub n: usize,
  /// Lean index ↦ canonical position
  pub sigma: Vec<usize>,
  pub packed_name: Name,
  pub new_packed_name: Name,
  pub num_fixed: usize,
  /// new fixed position `p` ↦ Lean's fixed position
  pub fixed_perm: Vec<usize>,
  /// Lean's component types `T_i` (fixed parameters loose)
  pub leaves: Vec<Expr>,
  /// Lean's packed type (for the projections' structure names)
  pub spine: Spine,
  /// abstracted proof ↦ the permutation of its leading fixed-parameter
  /// binders (empty when it uses none)
  pub proof_perm: FxHashMap<Name, Vec<usize>>,
  /// `monotone_compose`'s universe parameters (for the fallback)
  pub compose_levels: Vec<Name>,
  /// per member (Lean's order): the member's parameter (outermost `0`) at
  /// each fixed position of its projection of the fixpoint
  pub member_fixed: Vec<Vec<usize>>,
}

/// `normOrderAlias`: `ImplicationOrder` and `ReverseImplicationOrder` (both
/// `:= Prop`) read as `Prop`. The lattice-theoretic fixpoints spell a
/// component type `∀ x, ImplicationOrder` where the packed constant's type
/// says `∀ x, Prop` (the functional's binder takes its type from the
/// instances, `Meta/Order.lean` and `PartialFixpoint/Main.lean`), so the
/// clique's packing is recognised up to the alias; each occurrence keeps its
/// own spelling when it is rebuilt.
pub fn norm_order_alias(e: &Expr) -> Expr {
  match e.as_data() {
    ExprData::Const(c, _, _) => {
      if *c == n_implication_order() || *c == n_reverse_implication_order() {
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
  /// `PFLayout.isClique`: `s` is this clique's packing (its leaves match
  /// Lean's components under one correspondence, up to the order alias).
  pub fn is_clique(&self, s: &Spine) -> bool {
    s.size() == self.n
      && match_packing_leaves(
        &s.leaves.iter().map(norm_order_alias).collect::<Vec<_>>(),
        &self.leaves.iter().map(norm_order_alias).collect::<Vec<_>>(),
      )
      .is_some()
  }
}

/// `toPO`: the `toPartialOrder` of a `CCPO`/`CompleteLattice` instance.
pub fn to_po(lattice: bool, lvl: &Level, ty: &Expr, inst: &Expr) -> Expr {
  let head = if lattice { n_lattice_to_po() } else { n_ccpo_to_po() };
  mk_app_n(cnst(&head, slice::from_ref(lvl)), &[ty.clone(), inst.clone()])
}

/// The order data of a clique, read off `toPartialOrder γ I`: the packed
/// type, Lean's spine, the leaf instances and the instance kind
/// (`OrderData`).
#[derive(Clone, Debug)]
pub struct OrderData {
  /// the packing as the instances spell it
  pub spine: Spine,
  pub insts: Vec<Expr>,
  pub lattice: bool,
  /// the packing as the component types spell it: the same as `spine` for
  /// a CCPO; for the lattice-theoretic fixpoints `∀ x, Prop` where the
  /// instances say `∀ x, ImplicationOrder`. Lean uses each spelling at fixed
  /// positions: the component types (the codomain of the monotonicity
  /// statement, `monotone_mk`'s `α`, `β` and their orders) and the domain of
  /// a path proof (`monotone_fst`'s `γ`, the functions' binders,
  /// `monotone_id`) take this one; the instances, the packed order and a
  /// path's nodes the other.
  pub tspine: Spine,
}

/// `decodeOrderData`.
pub fn decode_order_data(l: &PfLayout, po: &Expr) -> Option<OrderData> {
  let (h, _, args) = const_app(po)?;
  if !((h == n_ccpo_to_po() || h == n_lattice_to_po()) && args.len() == 2) {
    return None;
  }
  let (ih, s, insts) = decode_inst_tree(l.n, args.get(1)?)?;
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
  /// The head of the instance tree of this kind.
  fn inst_head(&self) -> Name {
    if self.lattice { n_inst_lattice_pprod() } else { n_inst_ccpo_pprod() }
  }

  /// `OrderData.packedPO`: `toPartialOrder γ I`.
  pub fn packed_po(&self) -> Option<Expr> {
    let suf = self.spine.suffixes()?;
    let (gamma, lgamma) = suf.first()?;
    let inst = mk_inst_tree(&self.inst_head(), &self.spine, &self.insts)?;
    Some(to_po(self.lattice, lgamma, gamma, &inst))
  }

  /// `OrderData.suffixPO`: the partial order of suffix `k` as
  /// `whnfUntil … instPartialOrderPProd` leaves it: `toPartialOrder S_k I_k`.
  pub fn suffix_po(&self, k: usize) -> Option<Expr> {
    let suf = self.spine.suffixes()?;
    let n = self.spine.size();
    // Lean's `k + 1 == n`
    let inst = if n.checked_sub(1) == Some(k) {
      self.insts.get(k)?.clone()
    } else {
      let rest = Spine {
        kind: self.spine.kind,
        leaves: extract(&self.spine.leaves, k, n),
        lvls: extract(&self.spine.lvls, k, n),
      };
      mk_inst_tree(&self.inst_head(), &rest, &extract(&self.insts, k, n))?
    };
    let (sk, lk) = suf.get(k)?;
    Some(to_po(self.lattice, lk, sk, &inst))
  }

  /// `OrderData.poTree`: the `instPartialOrderPProd` tree of suffix `k` (the
  /// codomain order of `monotone_mk`'s statement).
  pub fn po_tree(&self, k: usize) -> Option<Expr> {
    let t = &self.tspine;
    let n = t.size();
    let leaf_po = |j: usize| -> Option<Expr> {
      Some(to_po(
        self.lattice,
        t.lvls.get(j)?,
        t.leaves.get(j)?,
        self.insts.get(j)?,
      ))
    };
    // Lean's `k + 1 == n`
    if n.checked_sub(1) == Some(k) {
      return leaf_po(k);
    }
    let leaf_pos: Vec<Expr> = (0..n.saturating_sub(k))
      .map(|j| leaf_po(k + j))
      .collect::<Option<_>>()?;
    let rest = Spine {
      kind: t.kind,
      leaves: extract(&t.leaves, k, n),
      lvls: extract(&t.lvls, k, n),
    };
    mk_inst_tree(&n_inst_po_pprod(), &rest, &leaf_pos)
  }

  /// `OrderData.permute`: the order data over the canonical packing
  /// (`sigma[i]` the new position of component `i`); `None` when `sigma` is
  /// not a permutation of the components.
  pub fn permute(&self, sigma: &[usize]) -> Option<OrderData> {
    let spine = self.spine.permute(sigma)?;
    let insts = permute(sigma, &self.insts)?;
    let tspine = self.tspine.permute(sigma)?;
    Some(OrderData { spine, insts, lattice: self.lattice, tspine })
  }
}

// ---------------------------------------------------------------------------
// `solveMonoCall`'s path proofs
// ---------------------------------------------------------------------------

/// `mkPathProof`: the monotonicity proof of `λ x. x.π_j` (`solveMonoCall` on
/// the path, inside out): `monotone_id`, then `monotone_snd` per `.2`,
/// `monotone_fst` for the final `.1`. Returns the proof and the function it
/// is about; `None` past the spine.
pub fn mk_path_proof(d: &OrderData, j: usize) -> Option<(Expr, Expr)> {
  let s = &d.spine;
  let n = s.size();
  let suf = s.suffixes()?;
  // the domain as the component types spell it
  let gamma = d.tspine.typ()?;
  let (_, lgamma) = suf.first()?;
  let po_gamma = d.packed_po()?;
  let x_name = root_name("x");
  let mut f =
    Expr::lam(x_name.clone(), gamma.clone(), bvar(0), BinderInfo::Default);
  let mut h = mk_app_n(
    cnst(&n_mono_id(), slice::from_ref(lgamma)),
    &[gamma.clone(), po_gamma.clone()],
  );
  let mut body = bvar(0);
  // `j` times `.2`, then `.1` unless last (Lean's `j + 1 < n`); the steps
  // are generated lazily, a position past the spine fails at its first node
  let steps = (0..j)
    .map(|k| (k, false))
    .chain((j < n.saturating_sub(1)).then_some((j, true)));
  for (k, is_fst) in steps {
    let (r, lr) = suf.get(k + 1)?;
    let lk = s.lvls.get(k)?;
    let leaf = s.leaves.get(k)?;
    let leaf_po = to_po(d.lattice, lk, leaf, d.insts.get(k)?);
    let rest_po = d.suffix_po(k + 1)?;
    let lem = if is_fst { n_mono_fst() } else { n_mono_snd() };
    h = mk_app_n(
      cnst(&lem, &[lk.clone(), lr.clone(), lgamma.clone()]),
      &[
        leaf.clone(),
        r.clone(),
        gamma.clone(),
        leaf_po,
        rest_po,
        po_gamma.clone(),
        f,
        h,
      ],
    );
    let pr = if is_fst { n_pprod_fst() } else { n_pprod_snd() };
    body = mk_app_n(
      cnst(&pr, &[lk.clone(), lr.clone()]),
      &[leaf.clone(), r.clone(), body],
    );
    f = Expr::lam(
      x_name.clone(),
      gamma.clone(),
      body.clone(),
      BinderInfo::Default,
    );
  }
  Some((h, f))
}

/// `decodePathProof`: decode a `monotone_fst`/`monotone_snd` chain: the
/// order data and the component; checked by regenerating it with Lean's
/// order.
pub fn decode_path_proof(l: &PfLayout, e: &Expr) -> Option<(OrderData, usize)> {
  let (h, _, args) = const_app(e)?;
  let (mono_fst, mono_snd, mono_id) = (n_mono_fst(), n_mono_snd(), n_mono_id());
  if !(h == mono_fst || h == mono_snd || h == mono_id) {
    return None;
  }
  let po = if h == mono_id {
    if args.len() == 2 { args.get(1)? } else { return None }
  } else if args.len() == 8 {
    args.get(5)?
  } else {
    return None;
  };
  let d = decode_order_data(l, po)?;
  // the domain's spelling
  let dom = if h == mono_id { args.first()? } else { args.get(2)? };
  let ts = decode_spine(PackKind::Pprod, l.n, dom)?;
  if !l.is_clique(&ts) {
    return None;
  }
  let d = OrderData { tspine: ts, ..d };
  // count the steps
  let mut cur = e.clone();
  let mut snds = 0;
  let mut fst = false;
  for _ in 0..l.n {
    let Some((h2, _, a)) = const_app(&cur) else { break };
    let [_, _, _, _, _, _, _, inner] = a.as_slice() else { break };
    if h2 == mono_snd {
      snds += 1;
    } else if h2 == mono_fst {
      if fst || snds > 0 {
        return None;
      }
      fst = true;
    } else {
      break;
    }
    cur = inner.clone();
  }
  let j = snds;
  if !((fst && j + 1 < l.n) || (!fst && j + 1 == l.n)) {
    return None;
  }
  let (proof, _) = mk_path_proof(&d, j)?;
  if alpha_eq_skip_mdata(&proof, e) { Some((d, j)) } else { None }
}

// ---------------------------------------------------------------------------
// The `monotone_mk` tree
// ---------------------------------------------------------------------------

/// `mkMonoTreeOver`: `PProd.monotone_mk` over the per-function proofs
/// (`mkMonoPProd` folded from the right): `fs` the functionals `F_k` (each
/// `λ x. …`), `hs` their proofs, over the domain `gamma` (of level `lgamma`,
/// ordered by `po_gamma`).
pub fn mk_mono_tree_over(
  gamma: &Expr,
  lgamma: &Level,
  po_gamma: &Expr,
  d: &OrderData,
  fs: &[Expr],
  hs: &[Expr],
) -> Option<Expr> {
  // the components as their types spell them
  let s = &d.tspine;
  let suf = s.suffixes()?;
  let x_name = root_name("x");
  // `g` for the rest from `k`: `F_{n-1}`, or `λ x. ⟨F_k[x], g_{k+1}[x]⟩`
  let inst_body = |f: &Expr| -> Expr {
    let f = strip_mdata(f);
    match f.as_data() {
      ExprData::Lam(_, _, b, _, _) => b.clone(),
      _ => Expr::app(lift_loose(&f, 1, 0), bvar(0)),
    }
  };
  // Lean's `n - 1` (truncated at 0)
  let last = s.size().saturating_sub(1);
  let mut g = fs.get(last)?.clone();
  let mut h = hs.get(last)?.clone();
  for k in (0..last).rev() {
    let (r, lr) = suf.get(k + 1)?;
    let lk = s.lvls.get(k)?;
    let leaf = s.leaves.get(k)?;
    let fk = fs.get(k)?;
    let leaf_po = to_po(d.lattice, lk, leaf, d.insts.get(k)?);
    h = mk_app_n(
      cnst(&n_mono_mk(), &[lk.clone(), lr.clone(), lgamma.clone()]),
      &[
        leaf.clone(),
        r.clone(),
        gamma.clone(),
        leaf_po,
        d.po_tree(k + 1)?,
        po_gamma.clone(),
        fk.clone(),
        g.clone(),
        hs.get(k)?.clone(),
        h,
      ],
    );
    if k > 0 {
      let tup = mk_app_n(
        cnst(&n_pprod_mk(), &[lk.clone(), lr.clone()]),
        &[
          lift_loose(leaf, 1, 0),
          lift_loose(r, 1, 0),
          inst_body(fk),
          inst_body(&g),
        ],
      );
      g = Expr::lam(x_name.clone(), gamma.clone(), tup, BinderInfo::Default);
    }
  }
  Some(h)
}

/// `mkMonoTree`: the `monotone_mk` tree of a fixpoint, over its own packed
/// type.
pub fn mk_mono_tree(d: &OrderData, fs: &[Expr], hs: &[Expr]) -> Option<Expr> {
  let suf = d.spine.suffixes()?;
  let (gamma, lgamma) = suf.first()?;
  mk_mono_tree_over(gamma, lgamma, &d.packed_po()?, d, fs, hs)
}

/// `mkComposeFallback`: the composition fallback for the per-function proof
/// `h : monotone F` (Lean's, over Lean's packing `d`):
/// `monotone_compose (mono φ) h`, a proof of `monotone (λ y. F (φ y))`,
/// which is `monotone F'` by β and projection of a constructor (`F'` the
/// transported functional), where `φ : γ' → γ` is `y ↦ ⟨y.π'_{σ 0}, …⟩` and
/// `mono φ` a `monotone_mk` tree over regenerated path proofs.
/// `compose_levels` are `monotone_compose`'s universe parameters. A builder
/// refusal comes before the universe-parameter refusal.
pub fn mk_compose_fallback(
  sigma: &[usize],
  d: &OrderData,
  d2: &OrderData,
  k: usize,
  f: &Expr,
  h: &Expr,
  compose_levels: &[Name],
) -> R<Expr> {
  let fail = || "monotone_compose: the packings do not rebuild".to_string();
  let s = &d.spine;
  let n = s.size();
  let suf2 = d2.spine.suffixes().ok_or_else(fail)?;
  let (gamma2, lgamma2) = suf2.first().cloned().ok_or_else(fail)?;
  let suf = s.suffixes().ok_or_else(fail)?;
  let (gamma, lgamma) = suf.first().cloned().ok_or_else(fail)?;
  let y_name = root_name("y");
  // φ = λ y. ⟨y.π'_{σ 0}, …⟩ over Lean's packing
  let lifted = s.map_leaves(&|x| lift_loose(x, 1, 0));
  let lifted2 = d2.spine.map_leaves(&|x| lift_loose(x, 1, 0));
  let comps: Vec<Expr> = (0..n)
    .map(|i| mk_path_app(&lifted2, *sigma.get(i)?, &bvar(0)))
    .collect::<Option<_>>()
    .ok_or_else(fail)?;
  let tuple = mk_tuple(&lifted, &comps).ok_or_else(fail)?;
  let phi = Expr::lam(y_name, gamma2.clone(), tuple, BinderInfo::Default);
  // mono φ: the component functions and their path proofs
  let paths: Vec<(Expr, Expr)> = (0..n)
    .map(|i| mk_path_proof(d2, *sigma.get(i)?))
    .collect::<Option<_>>()
    .ok_or_else(fail)?;
  let po_gamma2 = d2.packed_po().ok_or_else(fail)?;
  let po_gamma = d.packed_po().ok_or_else(fail)?;
  let path_fns: Vec<Expr> = paths.iter().map(|p| p.1.clone()).collect();
  let path_proofs: Vec<Expr> = paths.iter().map(|p| p.0.clone()).collect();
  let mono_phi = mk_mono_tree_over(
    &gamma2,
    &lgamma2,
    &po_gamma2,
    d,
    &path_fns,
    &path_proofs,
  )
  .ok_or_else(fail)?;
  let lk = s.lvls.get(k).ok_or_else(fail)?;
  let leaf = s.leaves.get(k).ok_or_else(fail)?;
  let inst = d.insts.get(k).ok_or_else(fail)?;
  let po_d = to_po(d.lattice, lk, leaf, inst);
  let mut us = Vec::with_capacity(compose_levels.len());
  for nm in compose_levels {
    if *nm == root_name("u") {
      us.push(lgamma2.clone());
    } else if *nm == root_name("v") {
      us.push(lgamma.clone());
    } else if *nm == root_name("w") {
      us.push(lk.clone());
    } else {
      return Err("monotone_compose: unexpected universe parameter".into());
    }
  }
  Ok(mk_app_n(
    cnst(&n_mono_compose(), &us),
    &[
      gamma2,
      po_gamma2,
      gamma,
      po_gamma,
      leaf.clone(),
      po_d,
      phi,
      f.clone(),
      mono_phi,
      h.clone(),
    ],
  ))
}

/// `decodeMonoTree`: decode a `monotone_mk` tree over the clique's packing,
/// checked by re-encoding.
pub fn decode_mono_tree(
  l: &PfLayout,
  e: &Expr,
) -> Option<(OrderData, Vec<Expr>, Vec<Expr>)> {
  let (h, us, args) = const_app(e)?;
  let mono_mk = n_mono_mk();
  if !(h == mono_mk && args.len() == 10) {
    return None;
  }
  let d = decode_order_data(l, args.get(5)?)?;
  // the components' spelling, from the outermost node's `α` and `β`
  let node = mk_node(
    PackKind::Pprod,
    us.first()?,
    us.get(1)?,
    args.first()?,
    args.get(1)?,
  );
  let ts = decode_spine(PackKind::Pprod, l.n, &node)?;
  if !l.is_clique(&ts) {
    return None;
  }
  let d = OrderData { tspine: ts, ..d };
  let mut fs = Vec::new();
  let mut hs = Vec::new();
  let mut cur = e.clone();
  for _ in 0..l.n.saturating_sub(1) {
    let (h2, _, a) = const_app(&cur)?;
    let [_, _, _, _, _, _, f, g, hk, rest] = a.as_slice() else {
      return None;
    };
    if h2 != mono_mk {
      return None;
    }
    fs.push(f.clone());
    hs.push(hk.clone());
    if fs.len() + 1 == l.n {
      fs.push(g.clone());
      hs.push(rest.clone());
    }
    cur = rest.clone();
  }
  if fs.len() != l.n {
    return None;
  }
  if alpha_eq_skip_mdata(&mk_mono_tree(&d, &fs, &hs)?, e) {
    Some((d, fs, hs))
  } else {
    None
  }
}

/// `pfLayout`: the layout from the members (Lean's order) and the packed
/// fixpoint, under the permutation `sigma` (Lean index ↦ canonical
/// position), with the packed fixpoint renamed `new_packed_name`.
pub fn pf_layout(
  members: &[Decl],
  packed: &Decl,
  sigma: &[usize],
  new_packed_name: &Name,
) -> R<PfLayout> {
  let bad = || "pfLayout: bad permutation".to_string();
  let n = members.len();
  if !(n >= 2 && sigma.len() == n && is_perm(sigma)) {
    return Err(bad());
  }
  let m = forall_arity(&packed.typ);
  let (_, gamma) = peel_foralls(m, &packed.typ);
  let Some(s) = decode_spine(PackKind::Pprod, n, &gamma) else {
    return Err("pfLayout: the packed type is not Lean's PProd packing".into());
  };
  // each member projects its own component of `f₀.mutual fixed`
  let mut qss: Vec<Vec<usize>> = Vec::new();
  for (i, d) in members.iter().enumerate() {
    let (ps, body) = peel_lams(lam_arity(&d.value), &d.value);
    let (h, _) = get_app_fn_args(&strip_mdata(&body));
    let (steps, base) = proj_chain(&h);
    let not_projection =
      || format!("pfLayout: member {i} is not a projection of the fixpoint");
    let Some((c, _, args)) = const_app(&base) else {
      return Err(not_projection());
    };
    if !(c == packed.name && args.len() == m) {
      return Err(not_projection());
    }
    match path_prefix(n, &steps) {
      Some((j, len)) => {
        if !(j == i && len == steps.len()) {
          return Err(format!("pfLayout: member {i} projects component {j}"));
        }
      },
      None => return Err(format!("pfLayout: member {i}: not a path")),
    }
    let mut qs = Vec::with_capacity(args.len());
    for a in &args {
      match bvar_idx(&strip_mdata(a)) {
        Some(b) => {
          if b < ps.len() {
            qs.push(ps.len() - 1 - b);
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
  // Lean's fixed order is its first member's order
  let q0 = qss.first().ok_or_else(bad)?;
  if !eq_sorted(q0) {
    return Err(
      "pfLayout: the fixed parameters are not in the first member's order"
        .into(),
    );
  }
  // the canonical first member's order
  let inv = inv_perm(sigma).ok_or_else(bad)?;
  let g = *inv.first().ok_or_else(bad)?;
  let qg = qss.get(g).ok_or_else(bad)?;
  // `qg` has one entry per fixed position, all distinct (checked above)
  let fixed_perm = sort_idx_by_key(qg);
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
// The conjugation of the root functional
// ---------------------------------------------------------------------------

/// `project` of `reduceConjugation.reduceHead`: field `i` of `base` when it
/// is the constructor of the structure `s` (`PProd.mk` or `And.intro`).
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

/// `reduceConjugation.reduceHead`: ordinary constructor projection reduction
/// at the head of `e`. No type-shape recognition and no delta reduction: a
/// projection (`.proj` or `PProd.fst`/`PProd.snd`) reduces only when its
/// actual operand is the corresponding constructor, including constructors
/// introduced by substitution. (Lean's whole-term `reduceConjugation` is
/// unused; only its head step is.)
pub fn reduce_head(e: &Expr) -> Expr {
  match e.as_data() {
    ExprData::Proj(s, i, x, _) => {
      project(s, nat_usize(i), x).unwrap_or_else(|| e.clone())
    },
    _ => {
      let (h, args) = get_app_fn_args(e);
      if let ExprData::Const(c, _, _) = h.as_data()
        && (*c == n_pprod_fst() || *c == n_pprod_snd())
        && args.len() >= 3
        && let Some(base) = args.get(2)
        && let Some(value) =
          project(&n_pprod(), if *c == n_pprod_fst() { 0 } else { 1 }, base)
      {
        return mk_app_n(value, &extract(&args, 3, args.len()));
      }
      e.clone()
    },
  }
}

/// `substitutePFInput`: evaluate inverse-packing substitution at paths of
/// the exact recursive binder (`bvar 0` of `body`), retaining Lean's
/// projection-vs-application spelling at each owned site. This is
/// constructor projection reduction of the explicit inverse tuple, not a
/// rewrite selected by a binder's type. Other binders are visited only to
/// adjust de Bruijn depth. A bare recursive value becomes the inverse tuple
/// itself.
pub fn substitute_pf_input(
  input: &Spine,
  sigma: &[usize],
  body: &Expr,
) -> R<Expr> {
  pf_input_visit(input, sigma, body, 0)
}

/// `substitutePFInput.go`: [`substitute_pf_input`] at binder depth `depth`.
fn pf_input_visit(
  input: &Spine,
  sigma: &[usize],
  e: &Expr,
  depth: usize,
) -> R<Expr> {
  // the packing at this depth, and over the canonical order: pure, and
  // built only at the sites of the recursive binder
  let source = || input.map_leaves(&|x| lift_loose(x, depth + 1, 0));
  let target = || source().permute(sigma);
  let no_target =
    || "PF conjugation: the recursive packing does not permute".to_string();
  if let Some((spine, j, base)) = decode_path_app(input.size(), e)
    && alpha_eq_skip_mdata(&base, &bvar(depth))
  {
    let spine_type = spine_type_e(&spine, "PF conjugation")?;
    let source_type = spine_type_e(&source(), "PF conjugation")?;
    if !alpha_eq_skip_mdata(
      &norm_order_alias(&spine_type),
      &norm_order_alias(&source_type),
    ) {
      return Err("PF conjugation: recursive path has a foreign type".into());
    }
    let permuted = spine.permute(sigma).ok_or_else(no_target)?;
    let position = *sigma.get(j).ok_or_else(no_target)?;
    return mk_path_app(&permuted, position, &base).ok_or_else(|| {
      "PF conjugation: recursive path reconstruction failed".to_string()
    });
  }
  if let ExprData::Proj(..) = e.as_data() {
    let (steps, base) = proj_chain(e);
    if alpha_eq_skip_mdata(&base, &bvar(depth)) {
      let Some((j, used)) = path_prefix(input.size(), &steps) else {
        return Err(
          "PF conjugation: recursive projection is not a component path".into(),
        );
      };
      if !steps_fit(&source(), j, &extract(&steps, 0, used)) {
        return Err(
          "PF conjugation: recursive projection has a foreign structure".into(),
        );
      }
      let target = target().ok_or_else(no_target)?;
      let position = *sigma.get(j).ok_or_else(no_target)?;
      let Some(mut canonical) = target.proj_steps(position) else {
        return Err(
          "PF conjugation: recursive projection reconstruction failed".into(),
        );
      };
      canonical.extend(extract(&steps, used, steps.len()));
      return Ok(apply_projs(&canonical, &base));
    }
  }
  let go = |x: &Expr, d: usize| pf_input_visit(input, sigma, x, d);
  Ok(match e.as_data() {
    ExprData::Bvar(..) => {
      if is_bvar(e, depth) {
        let target = target().ok_or_else(no_target)?;
        let rebuild =
          || "PF conjugation: inverse tuple reconstruction failed".to_string();
        let components: Vec<Expr> = sigma
          .iter()
          .map(|&j| target.proj_steps(j).map(|st| apply_projs(&st, e)))
          .collect::<Option<_>>()
          .ok_or_else(rebuild)?;
        mk_tuple(&source(), &components).ok_or_else(rebuild)?
      } else {
        e.clone()
      }
    },
    ExprData::App(f, a, _) => Expr::app(go(f, depth)?, go(a, depth)?),
    ExprData::Proj(s, i, x, _) => {
      Expr::proj(s.clone(), i.clone(), go(x, depth)?)
    },
    ExprData::Lam(n, t, b, bi, _) => {
      Expr::lam(n.clone(), go(t, depth)?, go(b, depth + 1)?, bi.clone())
    },
    ExprData::ForallE(n, t, b, bi, _) => {
      Expr::all(n.clone(), go(t, depth)?, go(b, depth + 1)?, bi.clone())
    },
    ExprData::LetE(n, t, v, b, nd, _) => Expr::letE(
      n.clone(),
      go(t, depth)?,
      go(v, depth)?,
      go(b, depth + 1)?,
      *nd,
    ),
    ExprData::Mdata(d, x, _) => Expr::mdata(d.clone(), go(x, depth)?),
    _ => e.clone(),
  })
}

/// `conjugatePF`: `φ ∘ F ∘ φ⁻¹`, with the input binder and output tuple
/// established by decoding this functional. The inverse tuple replaces that
/// exact binder by de Bruijn identity; same-typed or shadowing user binders
/// are never selected. (Semantically, `Lean.Order.fix` commutes with the
/// re-association, an order isomorphism; see the module documentation.)
pub fn conjugate_pf(n: usize, sigma: &[usize], functional: &Expr) -> R<Expr> {
  let invalid = || "PF conjugation: invalid permutation".to_string();
  if !(n >= 2 && sigma.len() == n && is_perm(sigma)) {
    return Err(invalid());
  }
  let stripped = strip_mdata(functional);
  let ExprData::Lam(name, domain, body, bi, _) = stripped.as_data() else {
    return Err("PF conjugation: missing recursive binder".into());
  };
  let Some(input) = decode_spine(PackKind::Pprod, n, domain) else {
    return Err(
      "PF conjugation: recursive binder is not a packed product".into(),
    );
  };
  let Some((output, components)) = decode_tuple(n, &strip_mdata(body)) else {
    return Err("PF conjugation: missing encoded result tuple".into());
  };
  let output_type = spine_type_e(&output, "PF conjugation")?;
  let input_type = spine_type_e(&input, "PF conjugation")?;
  if !alpha_eq_skip_mdata(
    &norm_order_alias(&output_type),
    &norm_order_alias(&lift_loose(&input_type, 1, 0)),
  ) {
    return Err("PF conjugation: input and output packing differ".into());
  }
  let mut substituted = Vec::with_capacity(components.len());
  for c in &components {
    substituted.push(substitute_pf_input(&input, sigma, c)?);
  }
  let target = input.permute(sigma).ok_or_else(invalid)?;
  let output_target = output.permute(sigma).ok_or_else(invalid)?;
  let permuted = permute(sigma, &substituted).ok_or_else(invalid)?;
  let Some(tuple) = mk_tuple(&output_target, &permuted) else {
    return Err("PF conjugation: result tuple reconstruction failed".into());
  };
  Ok(Expr::lam(
    name.clone(),
    spine_type_e(&target, "PF conjugation")?,
    tuple,
    bi.clone(),
  ))
}

/// `conjugatePFInput`: precompose a decoded component functional with the
/// inverse packing. This is the function occurring in the composition
/// fallback.
pub fn conjugate_pf_input(
  input: &Spine,
  sigma: &[usize],
  functional: &Expr,
) -> R<Expr> {
  let invalid = || "PF input conjugation: invalid permutation".to_string();
  if !(input.size() >= 2 && sigma.len() == input.size() && is_perm(sigma)) {
    return Err(invalid());
  }
  let stripped = strip_mdata(functional);
  let ExprData::Lam(name, domain, body, bi, _) = stripped.as_data() else {
    return Err("PF input conjugation: missing recursive binder".into());
  };
  let input_type = spine_type_e(input, "PF input conjugation")?;
  if !alpha_eq_skip_mdata(
    &norm_order_alias(domain),
    &norm_order_alias(&input_type),
  ) {
    return Err("PF input conjugation: wrong binder domain".into());
  }
  let Some(actual_input) = decode_spine(PackKind::Pprod, input.size(), domain)
  else {
    return Err("PF input conjugation: missing functional packing".into());
  };
  let target = actual_input.permute(sigma).ok_or_else(invalid)?;
  let target_type = spine_type_e(&target, "PF input conjugation")?;
  Ok(Expr::lam(
    name.clone(),
    target_type,
    substitute_pf_input(&actual_input, sigma, body)?,
    bi.clone(),
  ))
}

// ---------------------------------------------------------------------------
// The monotonicity proofs
// ---------------------------------------------------------------------------

/// `conjugatePFMono`: transport a decoded monotonicity tree by the
/// composition construction alone, keeping every source per-component proof
/// verbatim (no user proof syntax is recognised by its type).
pub fn conjugate_pf_mono(layout: &PfLayout, proof: &Expr) -> R<Expr> {
  let Some((data, fs, hs)) = decode_mono_tree(layout, proof) else {
    return Err(
      "PF conjugation: monotonicity proof is not a decoded tuple tree".into(),
    );
  };
  let Some(target) = data.permute(&layout.sigma) else {
    return Err(
      "PF conjugation: monotonicity proof packing does not permute".into(),
    );
  };
  let mut fs2 = Vec::with_capacity(fs.len());
  for f in &fs {
    fs2.push(conjugate_pf_input(&data.tspine, &layout.sigma, f)?);
  }
  let too_few =
    || "PF conjugation: monotonicity proof has too few components".to_string();
  let mut hs2 = Vec::with_capacity(layout.n);
  for k in 0..layout.n {
    let fk = fs.get(k).ok_or_else(too_few)?;
    let hk = hs.get(k).ok_or_else(too_few)?;
    hs2.push(mk_compose_fallback(
      &layout.sigma,
      &data,
      &target,
      k,
      fk,
      hk,
      &layout.compose_levels,
    )?);
  }
  let invalid = || "PF conjugation: invalid permutation".to_string();
  let fs_p = permute(&layout.sigma, &fs2).ok_or_else(invalid)?;
  let hs_p = permute(&layout.sigma, &hs2).ok_or_else(invalid)?;
  mk_mono_tree(&target, &fs_p, &hs_p).ok_or_else(|| {
    "PF conjugation: monotonicity tree reconstruction failed".to_string()
  })
}

/// `ownedMonoPremise`: a premise about the exact symbolic recursive-domain
/// parameter. Opening the theorem telescope before this test distinguishes
/// parameters that merely receive equal types at an application. Quantified
/// user parameters stay user parameters, even if their instantiated type is
/// the packing.
pub fn owned_mono_premise(domain: &Name, order: &Name, e: &Expr) -> bool {
  match e.as_data() {
    ExprData::ForallE(_, t, b, _, _) => {
      !mentions_fvar(domain, t)
        && !mentions_fvar(order, t)
        && owned_mono_premise(domain, order, b)
    },
    _ => match const_app(&strip_mdata(e)) {
      Some((c, _, args)) => match args.as_slice() {
        [d, o, _, _, _] => {
          c == n_monotone()
            && alpha_eq_skip_mdata(d, &fvar(domain))
            && alpha_eq_skip_mdata(o, &fvar(order))
        },
        _ => false,
      },
      None => false,
    },
  }
}

/// `transportOwnedMono`: transport a proof only through the argument roles
/// of its applied theorem's declared telescope. The domain/order are exact
/// fresh identities from its `monotone` conclusion, never inferred from a
/// user's matching type. Unknown dependent roles decline to the composition
/// construction.
///
/// The walk is memoised ([`memo_transport`], keyed by the subterm and the
/// fuel): a regenerated path proof shared by several theorem applications is
/// decoded once. A visit that opens a theorem's telescope allocates fresh
/// variables and is never cached, so the fresh-name stream is the
/// unmemoised walk's.
pub fn transport_owned_mono(
  tm: &mut TState,
  l: &PfLayout,
  const_of: ConstOf<'_>,
  fuel: usize,
  e: &Expr,
) -> R<Expr> {
  owned_mono_visit(tm, &mut TransportMemo::default(), l, const_of, fuel, e)
}

/// `transportOwnedMono.visit`: one memoised visit at `fuel`.
fn owned_mono_visit(
  tm: &mut TState,
  memo: &mut TransportMemo,
  l: &PfLayout,
  const_of: ConstOf<'_>,
  fuel: usize,
  e: &Expr,
) -> R<Expr> {
  let Some(next) = fuel.checked_sub(1) else {
    return Err("PF proof ownership: recursion bound exhausted".into());
  };
  memo_transport(tm, memo, e, fuel, 0, |tm, memo| {
    owned_mono_step(tm, memo, l, const_of, next, e)
  })
}

/// The body of [`owned_mono_visit`], its recursive visits at `fuel`.
fn owned_mono_step(
  tm: &mut TState,
  memo: &mut TransportMemo,
  l: &PfLayout,
  const_of: ConstOf<'_>,
  fuel: usize,
  e: &Expr,
) -> R<Expr> {
  if let Some((data, j)) = decode_path_proof(l, e) {
    let Some(target) = data.permute(&l.sigma) else {
      return Err("PF proof ownership: path packing does not permute".into());
    };
    let position = *tm_idx(&l.sigma, j, "PF proof ownership: path component")?;
    let Some((proof, _)) = mk_path_proof(&target, position) else {
      return Err(
        "PF proof ownership: path proof reconstruction failed".into(),
      );
    };
    return Ok(proof);
  }
  match e.as_data() {
    ExprData::Lam(n, t, b, bi, _) => {
      let b = owned_mono_visit(tm, memo, l, const_of, fuel, b)?;
      return Ok(Expr::lam(n.clone(), t.clone(), b, bi.clone()));
    },
    ExprData::Mdata(d, x, _) => {
      let x = owned_mono_visit(tm, memo, l, const_of, fuel, x)?;
      return Ok(Expr::mdata(d.clone(), x));
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
  let not_monotone =
    || "PF proof ownership: theorem conclusion is not monotonicity".to_string();
  let Some((head, _, result_args)) = const_app(&conclusion) else {
    return Err(not_monotone());
  };
  if head != n_monotone() {
    return Err(not_monotone());
  }
  let [domain_arg, order_arg, output_type, output_order, _] =
    result_args.as_slice()
  else {
    return Err(not_monotone());
  };
  let ExprData::Fvar(domain, _) = domain_arg.as_data() else {
    return Err("PF proof ownership: domain is not a theorem parameter".into());
  };
  let ExprData::Fvar(order, _) = order_arg.as_data() else {
    return Err("PF proof ownership: order is not a theorem parameter".into());
  };
  // This transport precomposes the recursive input and leaves the output
  // type/order alone. `monotone_id`, for example, has no function argument
  // to inspect but changes *both* ends when its one type parameter changes.
  // Such a theorem needs the separately checked path or composition route.
  if mentions_fvar(domain, output_type)
    || mentions_fvar(order, output_type)
    || mentions_fvar(domain, output_order)
    || mentions_fvar(order, output_order)
  {
    return Err(
      "PF proof ownership: conclusion output depends on the recursive-domain \
       parameter"
        .into(),
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
  let domain_value =
    tm_idx(&args, domain_index, "PF proof ownership: domain argument")?;
  let order_value =
    tm_idx(&args, order_index, "PF proof ownership: order argument")?;
  let Some(spine) = decode_spine(PackKind::Pprod, l.n, domain_value) else {
    return Err(
      "PF proof ownership: recursive domain is not the decoded packing".into(),
    );
  };
  let Some(data) = decode_order_data(l, order_value) else {
    return Err(
      "PF proof ownership: recursive order is not the decoded order".into(),
    );
  };
  let spine_type = spine_type_m(&spine, "PF proof ownership")?;
  let data_type = spine_type_m(&data.spine, "PF proof ownership")?;
  if !(l.is_clique(&spine)
    && alpha_eq_skip_mdata(
      &norm_order_alias(&spine_type),
      &norm_order_alias(&data_type),
    ))
  {
    return Err("PF proof ownership: domain/order mismatch".into());
  }
  let Some(target) =
    (OrderData { tspine: spine.clone(), ..data }).permute(&l.sigma)
  else {
    return Err(
      "PF proof ownership: recursive packing does not permute".into(),
    );
  };
  let target_type = spine_type_m(&target.tspine, "PF proof ownership")?;
  let Some(target_order) = target.packed_po() else {
    return Err(
      "PF proof ownership: recursive order reconstruction failed".into(),
    );
  };
  let mut args2 = Vec::with_capacity(args.len());
  for (i, parameter) in parameters.iter().enumerate() {
    let arg = tm_idx(&args, i, "PF proof ownership: theorem argument")?;
    if i == domain_index {
      args2.push(target_type.clone());
    } else if i == order_index {
      args2.push(target_order.clone());
    } else if mentions_fvar(domain, &parameter.typ)
      || mentions_fvar(order, &parameter.typ)
    {
      if owned_mono_premise(domain, order, &parameter.typ) {
        args2.push(owned_mono_visit(tm, memo, l, const_of, fuel, arg)?);
      } else {
        let stripped = strip_mdata(&parameter.typ);
        let ExprData::ForallE(_, input, output, _, _) = stripped.as_data()
        else {
          return Err(
            "PF proof ownership: unsupported dependent argument role".into(),
          );
        };
        if !(alpha_eq_skip_mdata(input, &fvar(domain))
          && !mentions_fvar(domain, output)
          && !mentions_fvar(order, output)
          && loose_all_at_least(output, 1))
        {
          return Err(
            "PF proof ownership: unsupported dependent functional role".into(),
          );
        }
        args2.push(conjugate_pf_input(&spine, &l.sigma, arg)?);
      }
    } else {
      args2.push(arg.clone());
    }
  }
  // (`open_binders` opened one binder per argument: nothing is left over)
  args2.extend(extract(&args, parameters.len(), args.len()));
  Ok(mk_app_n(cnst(&name, &levels), &args2))
}

/// `conjugatePFMonoChecked`: regenerate recognised source proof syntax; keep
/// each unknown component proof verbatim inside the composition
/// construction. The functional arguments always come from
/// binder-identified precomposition, including the fallback branch. A
/// component that takes the fallback leaves the transport state as it was
/// before its attempt and records why in [`TState::fallbacks`].
pub fn conjugate_pf_mono_checked(
  tm: &mut TState,
  l: &PfLayout,
  const_of: ConstOf<'_>,
  proof: &Expr,
) -> R<Expr> {
  let Some((data, fs, hs)) = decode_mono_tree(l, proof) else {
    return Err(
      "PF conjugation: monotonicity proof is not a decoded tuple tree".into(),
    );
  };
  let Some(target) = data.permute(&l.sigma) else {
    return Err(
      "PF conjugation: monotonicity proof packing does not permute".into(),
    );
  };
  let mut fs2 = Vec::with_capacity(fs.len());
  for f in &fs {
    fs2.push(conjugate_pf_input(&data.tspine, &l.sigma, f)?);
  }
  let mut hs2 = Vec::with_capacity(l.n);
  for k in 0..l.n {
    let fk = tm_idx(&fs, k, "PF conjugation: monotonicity functional")?;
    let hk = tm_idx(&hs, k, "PF conjugation: monotonicity proof")?;
    // Lean runs the walk on a copy of the state and keeps it only on
    // success; the walk changes nothing but the fresh-variable counter
    let saved = tm.next;
    match transport_owned_mono(tm, l, const_of, TRANSPORT_FUEL, hk) {
      Ok(h) => hs2.push(h),
      Err(reason) => {
        tm.next = saved;
        hs2.push(mk_compose_fallback(
          &l.sigma,
          &data,
          &target,
          k,
          fk,
          hk,
          &l.compose_levels,
        )?);
        tm.fallbacks.push(format!("monotonicity proof {k}: {reason}"));
      },
    }
  }
  let invalid = || "PF conjugation: invalid permutation".to_string();
  let fs_p = permute(&l.sigma, &fs2).ok_or_else(invalid)?;
  let hs_p = permute(&l.sigma, &hs2).ok_or_else(invalid)?;
  mk_mono_tree(&target, &fs_p, &hs_p).ok_or_else(|| {
    "PF conjugation: monotonicity tree reconstruction failed".to_string()
  })
}

// ---------------------------------------------------------------------------
// The packed constant's uses
// ---------------------------------------------------------------------------

/// The table of [`mention_heights`]: per distinct subterm, whether it
/// mentions the constant and its height.
pub type MentionHeights = ExactMemo<(), (bool, usize)>;

/// `mentionHeights`: for every distinct subterm of `e`, whether it mentions
/// the constant `c`, and its height (`0` for a leaf, one more than its
/// highest child otherwise, binder domains and `mdata` included). A walk
/// that rebuilds every node of a subterm without `c` from the same parts
/// returns it unchanged, and succeeds exactly when its fuel exceeds the
/// height; [`rewrite_pf_packed_uses`] uses this to return such a subterm at
/// once.
pub fn mention_heights(c: &Name, e: &Expr) -> MentionHeights {
  fn go(c: &Name, e: &Expr, table: &mut MentionHeights) -> (bool, usize) {
    if let Some(r) = table.get(e, ()) {
      return r;
    }
    let r = match e.as_data() {
      ExprData::Const(n, _, _) => (n == c, 0),
      ExprData::App(f, a, _) => {
        let (mf, hf) = go(c, f, table);
        let (ma, ha) = go(c, a, table);
        (mf || ma, hf.max(ha) + 1)
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        let (mt, ht) = go(c, t, table);
        let (mb, hb) = go(c, b, table);
        (mt || mb, ht.max(hb) + 1)
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        let (mt, ht) = go(c, t, table);
        let (mv, hv) = go(c, v, table);
        let (mb, hb) = go(c, b, table);
        (mt || mv || mb, ht.max(hv).max(hb) + 1)
      },
      ExprData::Proj(_, _, x, _) | ExprData::Mdata(_, x, _) => {
        let (m, h) = go(c, x, table);
        (m, h + 1)
      },
      _ => (false, 0),
    };
    table.insert(e, (), r);
    r
  }
  let mut table = MentionHeights::default();
  go(c, e, &mut table);
  table
}

/// The error of an exhausted [`rewrite_pf_packed_uses`] bound.
const PACKED_USE_EXHAUSTED: &str =
  "PF ownership: packed-use recursion bound exhausted";

/// `rewritePFPackedUses`: the packed root is identified by its declaration
/// and full fixed-argument application. Replacing it by the inverse output
/// tuple preserves its old type and meaning everywhere in user syntax.
/// Reducing surrounding projections then yields canonical member paths
/// without selecting user binders.
///
/// The walk is a function of the subterm and the fuel, memoised by both. A
/// subterm without the packed constant is rebuilt unchanged by the walk
/// (which then succeeds exactly when the fuel exceeds its height,
/// [`mention_heights`]), so it is returned as it is, or the bound's refusal
/// raised, without descending.
pub fn rewrite_pf_packed_uses(l: &PfLayout, e: &Expr) -> R<Expr> {
  let table = mention_heights(&l.packed_name, e);
  packed_uses_visit(l, &table, &mut ExactMemo::default(), TRANSPORT_FUEL, e)
}

/// `rewritePFPackedUses.go`: one visit at `fuel`, with the subterm table and
/// the memo of one call.
fn packed_uses_visit(
  l: &PfLayout,
  table: &MentionHeights,
  memo: &mut ExactMemo<usize, Expr>,
  fuel: usize,
  e: &Expr,
) -> R<Expr> {
  let Some(next) = fuel.checked_sub(1) else {
    return Err(PACKED_USE_EXHAUSTED.into());
  };
  // a subterm without the packed constant: the walk below would rebuild it
  // unchanged, and run out of fuel exactly when its height reaches the fuel
  if let Some((false, height)) = table.get(e, ()) {
    if height <= next {
      return Ok(e.clone());
    }
    return Err(PACKED_USE_EXHAUSTED.into());
  }
  if let Some(out) = memo.get(e, fuel) {
    return Ok(out);
  }
  let out = packed_uses_step(l, table, memo, next, e)?;
  memo.insert(e, fuel, out.clone());
  Ok(out)
}

/// The body of [`packed_uses_visit`], its recursive visits at `fuel`.
fn packed_uses_step(
  l: &PfLayout,
  table: &MentionHeights,
  memo: &mut ExactMemo<usize, Expr>,
  fuel: usize,
  e: &Expr,
) -> R<Expr> {
  let mut go = |x: &Expr| packed_uses_visit(l, table, memo, fuel, x);
  if let Some((name, levels, args)) = const_app(e)
    && name == l.packed_name
  {
    if args.len() != l.num_fixed {
      return Err(
        "PF ownership: partial/over-applied packed declaration".into(),
      );
    }
    let mut args2 = Vec::with_capacity(args.len());
    for a in &args {
      args2.push(go(a)?);
    }
    let rev: Vec<Expr> = args.iter().rev().cloned().collect();
    let source = l.spine.map_leaves(&|t| instantiate_rev(t, &rev));
    let Some(target) = source.permute(&l.sigma) else {
      return Err("PF ownership: the packing does not permute".into());
    };
    let Some(fixed) = reorder(&l.fixed_perm, &args2) else {
      return Err(
        "PF ownership: the fixed-parameter order indexes past the packed \
         arguments"
          .into(),
      );
    };
    let value = mk_app_n(cnst(&l.new_packed_name, &levels), &fixed);
    let rebuild =
      || "PF ownership: inverse tuple reconstruction failed".to_string();
    let components: Vec<Expr> = l
      .sigma
      .iter()
      .map(|&j| target.proj_steps(j).map(|st| apply_projs(&st, &value)))
      .collect::<Option<_>>()
      .ok_or_else(rebuild)?;
    return mk_tuple(&source, &components).ok_or_else(rebuild);
  }
  Ok(match e.as_data() {
    ExprData::App(f, a, _) => {
      let f2 = go(f)?;
      let a2 = go(a)?;
      if f2 == *f && a2 == *a {
        return Ok(e.clone());
      }
      reduce_head(&Expr::app(f2, a2))
    },
    ExprData::Proj(s, i, x, _) => {
      let x2 = go(x)?;
      if x2 == *x {
        return Ok(e.clone());
      }
      reduce_head(&Expr::proj(s.clone(), i.clone(), x2))
    },
    ExprData::Lam(n, t, b, bi, _) => {
      let t = go(t)?;
      Expr::lam(n.clone(), t, go(b)?, bi.clone())
    },
    ExprData::ForallE(n, t, b, bi, _) => {
      let t = go(t)?;
      Expr::all(n.clone(), t, go(b)?, bi.clone())
    },
    ExprData::LetE(n, t, v, b, nd, _) => {
      let t = go(t)?;
      let v = go(v)?;
      Expr::letE(n.clone(), t, v, go(b)?, *nd)
    },
    ExprData::Mdata(d, x, _) => Expr::mdata(d.clone(), go(x)?),
    _ => e.clone(),
  })
}

// ---------------------------------------------------------------------------
// The monotonicity statement
// ---------------------------------------------------------------------------

/// `conjugatePFStatement`: transform the exact monotonicity statement of an
/// abstracted tuple proof. Every modified position is supplied by the
/// `monotone` application schema.
pub fn conjugate_pf_statement(l: &PfLayout, typ: &Expr) -> R<Expr> {
  let not_statement =
    || "PF ownership: expected a monotonicity statement".to_string();
  let Some((head, levels, args)) = const_app(&strip_mdata(typ)) else {
    return Err(not_statement());
  };
  if head != n_monotone() {
    return Err(not_statement());
  }
  let [input_type, input_order, output_type, output_order, functional] =
    args.as_slice()
  else {
    return Err(not_statement());
  };
  let Some(input) = decode_spine(PackKind::Pprod, l.n, input_type) else {
    return Err("PF ownership: statement has no input packing".into());
  };
  let Some(output) = decode_spine(PackKind::Pprod, l.n, output_type) else {
    return Err("PF ownership: statement has no output packing".into());
  };
  let Some(data) = decode_order_data(l, input_order) else {
    return Err("PF ownership: statement has no packed input order".into());
  };
  let data = OrderData { tspine: output.clone(), ..data };
  let input_spine_type = spine_type_e(&input, "PF ownership")?;
  let output_spine_type = spine_type_e(&output, "PF ownership")?;
  if !(l.is_clique(&input)
    && alpha_eq_skip_mdata(
      &norm_order_alias(&input_spine_type),
      &norm_order_alias(&output_spine_type),
    )
    && data.po_tree(0).is_some_and(|t| alpha_eq_skip_mdata(output_order, &t)))
  {
    return Err("PF ownership: statement input/output orders differ".into());
  }
  let functional2 = conjugate_pf(l.n, &l.sigma, functional)?;
  let rebuild =
    || "PF ownership: monotonicity statement reconstruction failed".to_string();
  let target = data.permute(&l.sigma).ok_or_else(rebuild)?;
  let input_target = input.permute(&l.sigma).ok_or_else(rebuild)?;
  let packed_order = target.packed_po().ok_or_else(rebuild)?;
  let output_order2 = target.po_tree(0).ok_or_else(rebuild)?;
  let input_target_type = spine_type_e(&input_target, "PF ownership")?;
  let output_target_type = spine_type_e(&target.tspine, "PF ownership")?;
  Ok(mk_app_n(
    cnst(&head, &levels),
    &[
      input_target_type,
      packed_order,
      output_target_type,
      output_order2,
      functional2,
    ],
  ))
}

// ---------------------------------------------------------------------------
// The equation lemmas
// ---------------------------------------------------------------------------

/// One rebuilt step of an equation proof (`PFEquationStep`): the proof of
/// `left = right` at `typ`.
#[derive(Clone, Debug)]
pub struct PfEquationStep {
  pub typ: Expr,
  pub left: Expr,
  pub right: Expr,
  pub proof: Expr,
}

/// `conjugatePFEquationProof`: rebuild the equation proof from the owned
/// fixpoint equation, its member projection, and ordinary congruence
/// applications. User expressions in the component body are never traversed
/// or recognised.
///
/// The walk is a chain (each accepted node has exactly one recursive child,
/// and every accepted node is rebuilt over the target fixpoint), so it has
/// neither a memo nor an unchanged-subterm shortcut.
pub fn conjugate_pf_equation_proof(
  l: &PfLayout,
  component: usize,
  source_fix: &Expr,
  target_fix: &Expr,
  fuel: usize,
  e: &Expr,
) -> R<PfEquationStep> {
  let Some(fuel) = fuel.checked_sub(1) else {
    return Err(
      "PF equation ownership: proof recursion bound exhausted".into(),
    );
  };
  let recurse = |x: &Expr| {
    conjugate_pf_equation_proof(l, component, source_fix, target_fix, fuel, x)
  };
  let Some((head, levels, args)) = const_app(&strip_mdata(e)) else {
    return Err("PF equation ownership: unsupported proof constructor".into());
  };
  if head == dotted("id")
    && let [_, proof] = args.as_slice()
  {
    return recurse(proof);
  }
  if head == dotted("Eq.trans")
    && let [_, _, _, _, step, last] = args.as_slice()
  {
    let non_reflexive =
      || "PF equation ownership: non-reflexive final equation step".to_string();
    let Some((last_head, _, last_args)) = const_app(last) else {
      return Err(non_reflexive());
    };
    if !(last_head == dotted("Eq.refl") && last_args.len() == 2) {
      return Err(non_reflexive());
    }
    return recurse(step);
  }
  let (fix_eq, lfp_fix) =
    (dotted("Lean.Order.fix_eq"), dotted("Lean.Order.lfp_monotone_fix"));
  if (head == fix_eq || head == lfp_fix) && args.len() == 4 {
    let Some((source_head, _, source_args)) = const_app(source_fix) else {
      return Err("PF equation ownership: missing source fixpoint".into());
    };
    let Some((_, _, target_args)) = const_app(target_fix) else {
      return Err("PF equation ownership: missing target fixpoint".into());
    };
    let expected = if source_head == n_order_fix() { fix_eq } else { lfp_fix };
    let foreign = || {
      "PF equation ownership: equation belongs to another fixpoint".to_string()
    };
    if !(head == expected
      && args.len() == source_args.len()
      && target_args.len() == 4
      && args.iter().zip(&source_args).all(|(a, b)| alpha_eq_skip_mdata(a, b)))
    {
      return Err(foreign());
    }
    let [target_type, _, target_functional, _] = target_args.as_slice() else {
      return Err(foreign());
    };
    return Ok(PfEquationStep {
      typ: target_type.clone(),
      left: target_fix.clone(),
      right: Expr::app(target_functional.clone(), target_fix.clone()),
      proof: mk_app_n(cnst(&head, &levels), &target_args),
    });
  }
  if head == dotted("congrArg")
    && let [_, result_type, _, _, function, proof] = args.as_slice()
  {
    let stripped = strip_mdata(function);
    let ExprData::Lam(binder, domain, body, bi, _) = stripped.as_data() else {
      return Err(
        "PF equation ownership: congruence is not a member projection".into(),
      );
    };
    let Some(source) = decode_spine(PackKind::Pprod, l.n, domain) else {
      return Err(
        "PF equation ownership: congruence has no packed binder".into(),
      );
    };
    let (steps, base) = proj_chain(body);
    let Some((index, used)) = path_prefix(l.n, &steps) else {
      return Err(
        "PF equation ownership: congruence is not a complete member path"
          .into(),
      );
    };
    if !(index == component
      && used == steps.len()
      && alpha_eq_skip_mdata(&base, &bvar(0))
      && steps_fit(&source, index, &steps))
    {
      return Err(
        "PF equation ownership: congruence selects another binder/component"
          .into(),
      );
    }
    let previous = recurse(proof)?;
    let rebuild = || {
      "PF equation ownership: member projection reconstruction failed"
        .to_string()
    };
    let target = source.permute(&l.sigma).ok_or_else(rebuild)?;
    let target_type = spine_type_e(&target, "PF equation ownership")?;
    let position = *l.sigma.get(component).ok_or_else(rebuild)?;
    let steps2 = target.proj_steps(position).ok_or_else(rebuild)?;
    let projection = Expr::lam(
      binder.clone(),
      target_type.clone(),
      apply_projs(&steps2, &bvar(0)),
      bi.clone(),
    );
    return Ok(PfEquationStep {
      typ: result_type.clone(),
      left: Expr::app(projection.clone(), previous.left.clone()),
      right: Expr::app(projection.clone(), previous.right.clone()),
      proof: mk_app_n(
        cnst(&head, &levels),
        &[
          target_type,
          result_type.clone(),
          previous.left,
          previous.right,
          projection,
          previous.proof,
        ],
      ),
    });
  }
  if head == dotted("congrFun")
    && let [domain_type, result_type, _, _, proof, argument] = args.as_slice()
  {
    let previous = recurse(proof)?;
    return Ok(PfEquationStep {
      typ: Expr::app(result_type.clone(), argument.clone()),
      left: Expr::app(previous.left.clone(), argument.clone()),
      right: Expr::app(previous.right.clone(), argument.clone()),
      proof: mk_app_n(
        cnst(&head, &levels),
        &[
          domain_type.clone(),
          result_type.clone(),
          previous.left,
          previous.right,
          previous.proof,
          argument.clone(),
        ],
      ),
    });
  }
  Err(format!(
    "PF equation ownership: unsupported proof constructor {}",
    name_to_string(&head)
  ))
}

/// `conjugatePFEquation`: the carried equation lemma `lemma` of a member,
/// renamed `new_name`: its statement is kept, its proof rebuilt over the
/// transported fixpoint `target_packed` ([`conjugate_pf_equation_proof`]).
pub fn conjugate_pf_equation(
  tm: &mut TState,
  l: &PfLayout,
  members: &[Decl],
  source_packed: &Decl,
  target_packed: &Decl,
  lemma: &Decl,
  new_name: &Name,
) -> R<Decl> {
  let arity = forall_arity(&lemma.typ);
  let (parameters, statement) = open_binders(tm, false, arity, &lemma.typ)?;
  let not_equality =
    || "PF equation ownership: statement is not an equality".to_string();
  let Some((eq, _, eq_args)) = const_app(&statement) else {
    return Err(not_equality());
  };
  if eq != dotted("Eq") {
    return Err(not_equality());
  }
  let [_, lhs, _] = eq_args.as_slice() else { return Err(not_equality()) };
  let Some((member_name, _, member_args)) = const_app(lhs) else {
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
  let member = tm_idx(members, component, "PF equation ownership: member")?;
  let applied_member = beta_app(&member.value, &member_args);
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
  let Some(target_fixed) = reorder(&l.fixed_perm, &fixed_args) else {
    return Err(
      "PF equation ownership: the fixed-parameter order indexes past the \
       packed arguments"
        .into(),
    );
  };
  let target_fix = beta_app(&target_packed.value, &target_fixed);
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
    TRANSPORT_FUEL,
    &proof_body,
  )?;
  let value = close_binders(true, &parameters, &proof.proof)?;
  Ok(Decl { name: new_name.clone(), value, ..lemma.clone() })
}

// ---------------------------------------------------------------------------
// The clique
// ---------------------------------------------------------------------------

/// `transportPF`: ownership-preserving transport of a `partial_fixpoint`
/// clique: the packed fixpoint `packed` (renamed `new_packed_name`), its
/// abstracted `proofs`, the `members` and the carried equation `lemmas`
/// (each with its new name), under the clique permutation `sigma`. The
/// packed declaration, its fixed binders, fixpoint arguments and abstracted
/// proof positions are decoded once; user syntax is transported only by
/// substitution of those exact identities. Unsupported roles leave the
/// entire clique to the caller's faithful baseline. The prologue (the
/// proofs' fixed prefixes) and the epilogue (the proofs' numbering and the
/// renames) are the ones [`super::wf::transport_wf`] shares
/// ([`fixed_proof_perms`], [`number_proofs`]).
pub fn transport_pf(
  tm: &mut TState,
  members: &[Decl],
  packed: &Decl,
  proofs: &[Decl],
  sigma: &[usize],
  new_packed_name: &Name,
  const_of: ConstOf<'_>,
  lemmas: &[(Decl, Name)],
) -> R<TransportOutput> {
  let initial = pf_layout(members, packed, sigma, new_packed_name)?;
  let compose_levels = match const_of(&n_mono_compose()) {
    Some(info) => info.get_level_params().clone(),
    None => Vec::new(),
  };
  let FixedProofs { proof_names, proof_perm, .. } = fixed_proof_perms(
    tm,
    proofs,
    initial.num_fixed,
    &initial.fixed_perm,
    &packed.value,
  )?;
  let l = PfLayout { compose_levels, proof_perm, ..initial };
  let unchanged = |_: &mut TState, e: &Expr| -> R<Expr> { Ok(e.clone()) };
  let packed_type = |_: &mut TState, e: &Expr| -> R<Expr> {
    let Some(spine) = decode_spine(PackKind::Pprod, l.n, &strip_mdata(e))
    else {
      return Err("PF ownership: packed result type is not a product".into());
    };
    if !l.is_clique(&spine) {
      return Err(
        "PF ownership: packed result type differs from the layout".into(),
      );
    }
    let Some(target) = spine.permute(sigma) else {
      return Err("PF ownership: packed result type does not permute".into());
    };
    spine_type_m(&target, "PF ownership")
  };
  let packed_value = |_: &mut TState, e: &Expr| -> R<Expr> {
    let Some((head, levels, args)) = const_app(&strip_mdata(e)) else {
      return Err(
        "PF ownership: packed value is not a fixpoint application".into(),
      );
    };
    let unsupported = || "PF ownership: unsupported fixpoint root".to_string();
    if !(head == n_order_fix() || head == dotted("Lean.Order.lfp_monotone")) {
      return Err(unsupported());
    }
    let [domain, instances, functional, proof_arg] = args.as_slice() else {
      return Err(unsupported());
    };
    let Some(spine) = decode_spine(PackKind::Pprod, l.n, domain) else {
      return Err("PF ownership: fixpoint has no packed domain".into());
    };
    let Some((instance_name, instance_spine, leaf_instances)) =
      decode_inst_tree(l.n, instances)
    else {
      return Err("PF ownership: fixpoint has no decoded instance tree".into());
    };
    let spine_type = spine_type_m(&spine, "PF ownership")?;
    let instance_type = spine_type_m(&instance_spine, "PF ownership")?;
    if !(l.is_clique(&spine)
      && alpha_eq_skip_mdata(
        &norm_order_alias(&spine_type),
        &norm_order_alias(&instance_type),
      ))
    {
      return Err("PF ownership: fixpoint type/instance mismatch".into());
    }
    let Some((proof_name, proof_levels, proof_args)) = const_app(proof_arg)
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
    let arity =
      || "PF ownership: proof fixed-argument arity mismatch".to_string();
    let permutation =
      l.proof_perm.get(&proof_name).cloned().unwrap_or_default();
    if proof_args.len() != permutation.len() {
      return Err(arity());
    }
    let reordered = reorder(&permutation, &proof_args).ok_or_else(arity)?;
    let proof = mk_app_n(cnst(&proof_name, &proof_levels), &reordered);
    let functional2 = conjugate_pf(l.n, sigma, functional)?;
    let rebuild =
      || "PF ownership: fixpoint root reconstruction failed".to_string();
    let target = spine.permute(sigma).ok_or_else(rebuild)?;
    let instance_target = instance_spine.permute(sigma).ok_or_else(rebuild)?;
    let leaf_instances2 =
      permute(sigma, &leaf_instances).ok_or_else(rebuild)?;
    let instances2 =
      mk_inst_tree(&instance_name, &instance_target, &leaf_instances2)
        .ok_or_else(rebuild)?;
    Ok(mk_app_n(
      cnst(&head, &levels),
      &[spine_type_m(&target, "PF ownership")?, instances2, functional2, proof],
    ))
  };
  let typ = with_reordered_binders2(
    tm,
    false,
    l.num_fixed,
    &l.fixed_perm,
    &packed.typ,
    &unchanged,
    &packed_type,
  )?;
  let value = with_reordered_binders2(
    tm,
    true,
    l.num_fixed,
    &l.fixed_perm,
    &packed.value,
    &unchanged,
    &packed_value,
  )?;
  let target_packed =
    Decl { name: new_packed_name.clone(), typ, value, ..packed.clone() };
  let mut out = vec![Transported::ok(target_packed.clone())];
  let statement = |_: &mut TState, e: &Expr| conjugate_pf_statement(&l, e);
  let mono =
    |tm: &mut TState, e: &Expr| conjugate_pf_mono_checked(tm, &l, const_of, e);
  for proof in proofs {
    let permutation =
      l.proof_perm.get(&proof.name).cloned().unwrap_or_default();
    let typ = with_reordered_binders2(
      tm,
      false,
      permutation.len(),
      &permutation,
      &proof.typ,
      &unchanged,
      &statement,
    )?;
    let before = tm.fallbacks.len();
    let value = with_reordered_binders2(
      tm,
      true,
      permutation.len(),
      &permutation,
      &proof.value,
      &unchanged,
      &mono,
    )?;
    let causes = extract(&tm.fallbacks, before, tm.fallbacks.len());
    out.push(Transported {
      decl: Decl { typ, value, ..proof.clone() },
      fallback: if causes.is_empty() { None } else { Some(causes.join("; ")) },
    });
  }
  for member in members {
    let typ = rewrite_pf_packed_uses(&l, &member.typ)?;
    let value = rewrite_pf_packed_uses(&l, &member.value)?;
    out.push(Transported::ok(Decl { typ, value, ..member.clone() }));
  }
  for (lemma, name) in lemmas {
    let declaration = conjugate_pf_equation(
      tm,
      &l,
      members,
      packed,
      &target_packed,
      lemma,
      name,
    )?;
    out.push(Transported::ok(declaration));
  }
  Ok(number_proofs(
    out,
    &packed.name,
    new_packed_name,
    proofs,
    lemmas,
    &target_packed.value,
  ))
}

#[cfg(test)]
mod tests {
  use rustc_hash::FxHashMap;

  use ix_common::env::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, DataValue, Expr, ExprData,
    Level, Name,
  };

  use super::{
    OrderData, PACKED_USE_EXHAUSTED, PfLayout, conjugate_pf, conjugate_pf_mono,
    decode_inst_tree, decode_mono_tree, decode_path_app, decode_path_proof,
    mention_heights, mk_compose_fallback, mk_inst_tree, mk_mono_tree,
    mk_path_app, mk_path_proof, n_inst_ccpo_pprod, n_mono_compose, n_mono_mk,
    n_monotone, n_order_fix, owned_mono_visit, packed_uses_visit, pf_layout,
    reduce_head, rewrite_pf_packed_uses, spine_type_e, substitute_pf_input,
    transport_owned_mono, transport_pf,
  };
  use crate::compile::pass3::clique::basic::{
    Decl, Local, R, TState, TransportMemo, bvar, cnst, const_app, dotted,
    instantiate_rev, mk_app_n, mk_forall, n_pprod, n_pprod_fst, proj,
    root_name, sort0,
  };
  use crate::compile::pass3::clique::bounds::TRANSPORT_FUEL;
  use crate::compile::pass3::clique::packing::{
    PackKind, Spine, apply_projs, mk_tuple,
  };
  use crate::compile::pass3::clique::telescope::reorder;
  use crate::compile::pass3::expr::ExactMemo;

  /// The clique permutation of the tests: Lean's `f, g` become `g, f`.
  const SIGMA: [usize; 2] = [1, 0];

  fn c(s: &str) -> Expr {
    cnst(&dotted(s), &[])
  }

  fn one() -> Level {
    Level::succ(Level::zero())
  }

  fn lam(x: &str, t: Expr, b: Expr) -> Expr {
    Expr::lam(root_name(x), t, b, BinderInfo::Default)
  }

  fn pi(x: &str, t: Expr, b: Expr) -> Expr {
    Expr::all(root_name(x), t, b, BinderInfo::Default)
  }

  fn local(fvar: &str, user: &str, typ: Expr) -> Local {
    Local {
      fvar: dotted(fvar),
      user_name: root_name(user),
      typ,
      bi: BinderInfo::Default,
    }
  }

  fn decl(name: &str, typ: Expr, value: Expr) -> Decl {
    Decl { name: dotted(name), level_params: vec![], typ, value, is_thm: false }
  }

  fn monotone(a: &Expr, o: &Expr, b: &Expr, pb: &Expr, f: &Expr) -> Expr {
    mk_app_n(
      cnst(&n_monotone(), &[one(), one()]),
      &[a.clone(), o.clone(), b.clone(), pb.clone(), f.clone()],
    )
  }

  fn compose_levels() -> Vec<Name> {
    ["u", "v", "w"].map(dotted).to_vec()
  }

  /// The packing `(Nat → Nat) ×' (Int → Nat)` of `f : Nat → Nat` and
  /// `g : Int → Nat`.
  fn spine() -> Spine {
    Spine {
      kind: PackKind::Pprod,
      leaves: vec![pi("n", c("Nat"), c("Nat")), pi("i", c("Int"), c("Nat"))],
      lvls: vec![one(), one()],
    }
  }

  fn order(s: &Spine) -> OrderData {
    OrderData {
      spine: s.clone(),
      insts: vec![c("inst0"), c("inst1")],
      lattice: false,
      tspine: s.clone(),
    }
  }

  /// `f`'s body under the recursive binder `x`: `λ n. x.π_j i0`, the path in
  /// application form over `s`.
  fn body0(s: &Spine, j: usize) -> Expr {
    let path = mk_path_app(s, j, &bvar(1)).unwrap();
    lam("n", c("Nat"), Expr::app(path, c("i0")))
  }

  /// `g`'s body under the recursive binder `x`: `λ i. x.π_j n0`, the path in
  /// projection form over `s`.
  fn body1(s: &Spine, j: usize) -> Expr {
    let path = apply_projs(&s.proj_steps(j).unwrap(), &bvar(1));
    lam("i", c("Int"), Expr::app(path, c("n0")))
  }

  /// `∀ (α : Type) (o : PO α) (f : α → Nat → Nat) (h₁ … : monotone o PB f),
  /// monotone o PB f`: a theorem with a functional role and `premises`
  /// monotonicity premises.
  fn mono_theorem(premises: usize) -> Expr {
    let b = pi("n", c("Nat"), c("Nat"));
    let alpha = local("t.a", "α", Expr::sort(one()));
    let o = local("t.o", "o", Expr::app(c("PO"), alpha.expr()));
    let f = local("t.f", "f", pi("x", alpha.expr(), b.clone()));
    let goal = monotone(&alpha.expr(), &o.expr(), &b, &c("PB"), &f.expr());
    let mut xs = vec![alpha, o, f];
    for k in 0..premises {
      xs.push(local(&format!("t.h{k}"), "h", goal.clone()));
    }
    mk_forall(&xs, &goal)
  }

  fn axiom(name: &str, level_params: Vec<Name>, typ: Expr) -> ConstantInfo {
    ConstantInfo::AxiomInfo(AxiomVal {
      cnst: ConstantVal { name: dotted(name), level_params, typ },
      is_unsafe: false,
    })
  }

  fn env(n: &Name) -> Option<ConstantInfo> {
    if *n == dotted("T.mono") {
      Some(axiom("T.mono", vec![], mono_theorem(1)))
    } else if *n == dotted("T.mono2") {
      Some(axiom("T.mono2", vec![], mono_theorem(2)))
    } else if *n == n_mono_compose() {
      Some(axiom("Lean.Order.monotone_compose", compose_levels(), sort0()))
    } else {
      None
    }
  }

  /// A two-member `partial_fixpoint` clique by hand, as Lean encodes `f`
  /// and `g` (each calls the other): the packed fixpoint, its abstracted
  /// monotonicity proof (one per-function proof through a theorem
  /// application over a path proof, one the transport cannot follow), the
  /// members and `f`'s equation lemma.
  struct Clique {
    members: Vec<Decl>,
    packed: Decl,
    proofs: Vec<Decl>,
    lemmas: Vec<(Decl, Name)>,
    /// the monotonicity tree's functionals and per-function proofs
    fs: Vec<Expr>,
    hs: Vec<Expr>,
  }

  fn clique() -> Clique {
    let s = spine();
    let d = order(&s);
    let gamma = s.typ().unwrap();
    let po = d.packed_po().unwrap();
    let inst = mk_inst_tree(&n_inst_ccpo_pprod(), &s, &d.insts).unwrap();
    let (t0, t1) = (s.leaves[0].clone(), s.leaves[1].clone());
    let tuple = mk_tuple(&s, &[body0(&s, 1), body1(&s, 0)]).unwrap();
    let functional = lam("x", gamma.clone(), tuple);
    let fs = vec![
      lam("x", gamma.clone(), body0(&s, 1)),
      lam("x", gamma.clone(), body1(&s, 0)),
    ];
    let path = mk_path_proof(&d, 1).unwrap().0;
    let hs = vec![
      mk_app_n(c("T.mono"), &[gamma.clone(), po.clone(), fs[0].clone(), path]),
      c("h1const"),
    ];
    let proof_name = "f.mutual._proof_1";
    let statement =
      monotone(&gamma, &po, &gamma, &d.po_tree(0).unwrap(), &functional);
    let proof = Decl {
      is_thm: true,
      ..decl(proof_name, statement, mk_mono_tree(&d, &fs, &hs).unwrap())
    };
    let fix_args = [gamma.clone(), inst, functional, c(proof_name)];
    let root = mk_app_n(cnst(&n_order_fix(), &[one()]), &fix_args);
    let packed = decl("f.mutual", gamma.clone(), root);
    let member = |name: &str, x: &str, domain: &str, typ: &Expr, j: usize| {
      let call = Expr::app(proj(&n_pprod(), j, c("f.mutual")), bvar(0));
      decl(name, typ.clone(), lam(x, c(domain), call))
    };
    let members =
      vec![member("f", "n", "Nat", &t0, 0), member("g", "i", "Int", &t1, 1)];
    // `f.eq_1 : ∀ n, f n = rhs`, proved as Lean proves it:
    // `congrFun (congrArg (·.1) (fix_eq …)) n`
    let eq = mk_app_n(
      cnst(&dotted("Eq"), &[one()]),
      &[c("Nat"), Expr::app(c("f"), bvar(0)), c("rhs")],
    );
    let fix_eq =
      mk_app_n(cnst(&dotted("Lean.Order.fix_eq"), &[one()]), &fix_args);
    let congr_arg = mk_app_n(
      cnst(&dotted("congrArg"), &[one(), one()]),
      &[
        gamma.clone(),
        t0,
        c("A"),
        c("B"),
        lam("x", gamma, proj(&n_pprod(), 0, bvar(0))),
        fix_eq,
      ],
    );
    let congr_fun = mk_app_n(
      cnst(&dotted("congrFun"), &[one(), one()]),
      &[
        c("Nat"),
        lam("m", c("Nat"), c("Nat")),
        c("L"),
        c("R"),
        congr_arg,
        bvar(0),
      ],
    );
    let lemma =
      decl("f.eq_1", pi("n", c("Nat"), eq), lam("n", c("Nat"), congr_fun));
    Clique {
      members,
      packed,
      proofs: vec![proof],
      lemmas: vec![(lemma, dotted("f.eq_1"))],
      fs,
      hs,
    }
  }

  fn layout(k: &Clique) -> PfLayout {
    let mut l =
      pf_layout(&k.members, &k.packed, &SIGMA, &dotted("g.mutual")).unwrap();
    l.compose_levels = compose_levels();
    l
  }

  #[test]
  fn builders_refuse_what_does_not_fit() {
    let s = spine();
    let d = order(&s);
    let x = c("x");
    let ccpo = n_inst_ccpo_pprod();
    let (fs, hs) = ([c("f0"), c("f1")], [c("h0"), c("h1")]);
    // a spine whose leaves and levels differ in number
    let bad = Spine { lvls: vec![one()], ..s.clone() };
    assert_eq!(mk_inst_tree(&ccpo, &bad, &d.insts), None);
    assert_eq!(mk_path_app(&bad, 0, &x), None);
    assert_eq!(
      spine_type_e(&bad, "PF conjugation"),
      Err(
        "PF conjugation: the packing has no type (no leaves, or leaves and \
         levels differ in number)"
          .to_string()
      )
    );
    // too few instances
    assert_eq!(mk_inst_tree(&ccpo, &s, &d.insts[..1]), None);
    let short = OrderData { insts: vec![c("inst0")], ..d.clone() };
    assert_eq!(short.packed_po(), None);
    assert_eq!(short.suffix_po(1), None);
    assert_eq!(short.po_tree(0), None);
    assert_eq!(mk_path_proof(&short, 1), None);
    assert_eq!(mk_mono_tree(&short, &fs, &hs), None);
    // positions past the spine
    assert_eq!(mk_path_app(&s, 2, &x), None);
    assert_eq!(d.suffix_po(2), None);
    assert_eq!(d.po_tree(2), None);
    assert_eq!(mk_path_proof(&d, 2), None);
    assert_eq!(mk_path_proof(&d, usize::MAX), None);
    assert_eq!(mk_mono_tree(&d, &fs[..1], &hs), None);
    assert!(d.permute(&[0, 0]).is_none());
    // what fits round-trips through its decoder
    let inst = mk_inst_tree(&ccpo, &s, &d.insts).unwrap();
    let (head, decoded, insts) = decode_inst_tree(2, &inst).unwrap();
    assert_eq!(
      (head, decoded.leaves, insts),
      (ccpo, s.leaves.clone(), d.insts.clone())
    );
    let k = clique();
    let l = layout(&k);
    for j in 0..2 {
      let path = mk_path_app(&s, j, &x).unwrap();
      let (_, j2, base) = decode_path_app(2, &path).unwrap();
      assert_eq!((j2, base), (j, x.clone()));
      let (proof, _) = mk_path_proof(&d, j).unwrap();
      assert_eq!(decode_path_proof(&l, &proof).map(|(_, j2)| j2), Some(j));
    }
    let tree = mk_mono_tree(&d, &fs, &hs).unwrap();
    let (_, fs2, hs2) = decode_mono_tree(&l, &tree).unwrap();
    assert_eq!((fs2, hs2), (fs.to_vec(), hs.to_vec()));
    // a `monotone_mk` node with one universe level is not a tree
    let (_, us, args) = const_app(&tree).unwrap();
    let one_level = mk_app_n(cnst(&n_mono_mk(), &us[..1]), &args);
    assert!(decode_mono_tree(&l, &one_level).is_none());
    // the composition fallback: a builder refusal, then the universes
    let d2 = d.permute(&SIGMA).unwrap();
    let levels = compose_levels();
    let rebuild =
      Err("monotone_compose: the packings do not rebuild".to_string());
    let foreign = [dotted("x")];
    assert_eq!(
      mk_compose_fallback(&[5, 0], &d, &d2, 0, &x, &x, &levels),
      rebuild
    );
    assert_eq!(
      mk_compose_fallback(&SIGMA, &d, &d2, 2, &x, &x, &levels),
      rebuild
    );
    assert_eq!(
      mk_compose_fallback(&[5, 0], &d, &d2, 0, &x, &x, &foreign),
      rebuild
    );
    assert_eq!(
      mk_compose_fallback(&SIGMA, &d, &d2, 0, &x, &x, &foreign),
      Err("monotone_compose: unexpected universe parameter".to_string())
    );
    assert!(mk_compose_fallback(&SIGMA, &d, &d2, 0, &x, &x, &levels).is_ok());
  }

  #[test]
  fn conjugation_moves_only_the_recursive_binder() {
    let s = spine();
    let s2 = s.permute(&SIGMA).unwrap();
    let gamma = s.typ().unwrap();
    // a bare recursive value becomes the inverse tuple
    let inverse = mk_tuple(
      &s,
      &[proj(&n_pprod(), 1, bvar(0)), proj(&n_pprod(), 0, bvar(0))],
    )
    .unwrap();
    assert_eq!(substitute_pf_input(&s, &SIGMA, &bvar(0)), Ok(inverse));
    // a user binder of the packed type keeps its identity
    let user = lam("y", gamma.clone(), proj(&n_pprod(), 0, bvar(0)));
    assert_eq!(substitute_pf_input(&s, &SIGMA, &user), Ok(user.clone()));
    // a path of the recursive binder keeps its spelling
    assert_eq!(
      substitute_pf_input(&s, &SIGMA, &body0(&s, 1)),
      Ok(body0(&s2, 0))
    );
    assert_eq!(
      substitute_pf_input(&s, &SIGMA, &body1(&s, 0)),
      Ok(body1(&s2, 1))
    );
    assert_eq!(
      substitute_pf_input(&s, &SIGMA, &proj(&n_pprod(), 2, bvar(0))),
      Err(
        "PF conjugation: recursive projection is not a component path".into()
      )
    );
    // the functional
    let tuple = mk_tuple(&s, &[body0(&s, 1), body1(&s, 0)]).unwrap();
    let functional = lam("x", gamma, tuple);
    let tuple2 = mk_tuple(&s2, &[body1(&s2, 1), body0(&s2, 0)]).unwrap();
    assert_eq!(
      conjugate_pf(2, &SIGMA, &functional),
      Ok(lam("x", s2.typ().unwrap(), tuple2))
    );
    assert_eq!(
      conjugate_pf(2, &[0, 0], &functional),
      Err("PF conjugation: invalid permutation".into())
    );
    assert_eq!(
      conjugate_pf(2, &SIGMA, &c("F")),
      Err("PF conjugation: missing recursive binder".into())
    );
    // projection of a constructor, and nothing else
    let pair = mk_tuple(&s, &[c("a"), c("b")]).unwrap();
    assert_eq!(reduce_head(&proj(&n_pprod(), 1, pair.clone())), c("b"));
    let fst = mk_app_n(
      cnst(&n_pprod_fst(), &[one(), one()]),
      &[s.leaves[0].clone(), s.leaves[1].clone(), pair, c("arg")],
    );
    assert_eq!(reduce_head(&fst), Expr::app(c("a"), c("arg")));
    let stuck = proj(&n_pprod(), 0, c("p"));
    assert_eq!(reduce_head(&stuck), stuck);
  }

  /// [`super::rewrite_pf_packed_uses`]'s walk without the memo or the
  /// subterm table, the reference for its results and refusals.
  fn plain(l: &PfLayout, fuel: usize, e: &Expr) -> R<Expr> {
    let Some(next) = fuel.checked_sub(1) else {
      return Err(PACKED_USE_EXHAUSTED.into());
    };
    let go = |x: &Expr| plain(l, next, x);
    if let Some((name, levels, args)) = const_app(e)
      && name == l.packed_name
    {
      if args.len() != l.num_fixed {
        return Err(
          "PF ownership: partial/over-applied packed declaration".into(),
        );
      }
      let args2 = args.iter().map(go).collect::<R<Vec<_>>>()?;
      let rev: Vec<Expr> = args.iter().rev().cloned().collect();
      let source = l.spine.map_leaves(&|t| instantiate_rev(t, &rev));
      let target = source.permute(&l.sigma).unwrap();
      let fixed = reorder(&l.fixed_perm, &args2).unwrap();
      let value = mk_app_n(cnst(&l.new_packed_name, &levels), &fixed);
      let cs: Vec<Expr> = l
        .sigma
        .iter()
        .map(|&j| apply_projs(&target.proj_steps(j).unwrap(), &value))
        .collect();
      return Ok(mk_tuple(&source, &cs).unwrap());
    }
    Ok(match e.as_data() {
      ExprData::App(f, a, _) => {
        let (f2, a2) = (go(f)?, go(a)?);
        if f2 == *f && a2 == *a {
          return Ok(e.clone());
        }
        reduce_head(&Expr::app(f2, a2))
      },
      ExprData::Proj(s, i, x, _) => {
        let x2 = go(x)?;
        if x2 == *x {
          return Ok(e.clone());
        }
        reduce_head(&Expr::proj(s.clone(), i.clone(), x2))
      },
      ExprData::Lam(n, t, b, bi, _) => {
        Expr::lam(n.clone(), go(t)?, go(b)?, bi.clone())
      },
      ExprData::ForallE(n, t, b, bi, _) => {
        Expr::all(n.clone(), go(t)?, go(b)?, bi.clone())
      },
      ExprData::LetE(n, t, v, b, nd, _) => {
        Expr::letE(n.clone(), go(t)?, go(v)?, go(b)?, *nd)
      },
      ExprData::Mdata(d, x, _) => Expr::mdata(d.clone(), go(x)?),
      _ => e.clone(),
    })
  }

  #[test]
  fn mention_heights_skip_agrees_with_the_plain_walk() {
    // `P : ∀ (A : Type), L0 A ×' L1 A`, renamed `Q`
    let s = Spine {
      kind: PackKind::Pprod,
      leaves: vec![Expr::app(c("L0"), bvar(0)), Expr::app(c("L1"), bvar(0))],
      lvls: vec![one(), one()],
    };
    let l = PfLayout {
      n: 2,
      sigma: SIGMA.to_vec(),
      packed_name: dotted("P"),
      new_packed_name: dotted("Q"),
      num_fixed: 1,
      fixed_perm: vec![0],
      leaves: s.leaves.clone(),
      spine: s,
      proof_perm: FxHashMap::default(),
      compose_levels: vec![],
      member_fixed: vec![],
    };
    // a DAG: `y` and `x` (without `P`) shared, met at several depths
    let md = vec![(dotted("k"), DataValue::OfBool(true))];
    let y = Expr::mdata(md, lam("y", c("A"), Expr::app(c("K"), bvar(0))));
    let x = mk_app_n(c("H"), &[y.clone(), y.clone()]);
    let p = |arg: &Expr| Expr::app(c("P"), arg.clone());
    let q = |arg: &Expr| Expr::app(c("Q"), arg.clone());
    let pr = |i: usize, e: Expr| proj(&n_pprod(), i, e);
    let body = Expr::app(pr(1, p(&y)), bvar(0));
    let e = mk_app_n(
      c("F"),
      &[
        x.clone(),
        Expr::app(pr(0, p(&x)), x.clone()),
        Expr::letE(root_name("z"), c("T"), x.clone(), body, false),
      ],
    );
    let table = mention_heights(&dotted("P"), &e);
    assert_eq!(table.get(&c("P"), ()), Some((true, 0)));
    assert_eq!(table.get(&y, ()), Some((false, 3)));
    assert_eq!(table.get(&x, ()), Some((false, 5)));
    let Some((true, height)) = table.get(&e, ()) else { panic!("no height") };
    let mut refused = 0;
    for fuel in 0..=height + 2 {
      let mut memo = ExactMemo::default();
      let got = packed_uses_visit(&l, &table, &mut memo, fuel, &e);
      let want = plain(&l, fuel, &e);
      refused += usize::from(want.is_err());
      assert_eq!(got, want, "fuel {fuel}");
    }
    // every path of this term descends node by node, so the walk needs a
    // fuel above the height: the bound decides the fuels up to it
    assert_eq!(refused, height + 1);
    let body2 = Expr::app(pr(0, q(&y)), bvar(0));
    let want = mk_app_n(
      c("F"),
      &[
        x.clone(),
        Expr::app(pr(1, q(&x)), x.clone()),
        Expr::letE(root_name("z"), c("T"), x.clone(), body2, false),
      ],
    );
    assert_eq!(rewrite_pf_packed_uses(&l, &e), Ok(want));
    // a partial application is refused
    assert_eq!(
      rewrite_pf_packed_uses(&l, &c("P")),
      Err("PF ownership: partial/over-applied packed declaration".into())
    );
  }

  #[test]
  fn owned_mono_memo_hits_keep_the_fresh_names() {
    let k = clique();
    let l = layout(&k);
    let s = spine();
    let d = order(&s);
    let s2 = s.permute(&SIGMA).unwrap();
    let d2 = d.permute(&SIGMA).unwrap();
    let (gamma, gamma2) = (s.typ().unwrap(), s2.typ().unwrap());
    let (po, po2) = (d.packed_po().unwrap(), d2.packed_po().unwrap());
    let p = mk_path_proof(&d, 1).unwrap().0;
    let p2 = mk_path_proof(&d2, 0).unwrap().0;
    // one theorem application over one path proof, shared
    let shared = mk_app_n(
      c("T.mono2"),
      &[gamma, po, k.fs[0].clone(), p.clone(), p.clone()],
    );
    let f2 = lam("x", gamma2.clone(), body0(&s2, 0));
    let want =
      mk_app_n(c("T.mono2"), &[gamma2, po2, f2, p2.clone(), p2.clone()]);
    let fuel = TRANSPORT_FUEL;
    let mut tm = TState::default();
    let mut memo = TransportMemo::default();
    let visit = |tm: &mut TState, memo: &mut TransportMemo, fuel, e: &Expr| {
      owned_mono_visit(tm, memo, &l, &env, fuel, e)
    };
    assert_eq!(visit(&mut tm, &mut memo, fuel, &shared), Ok(want.clone()));
    // the telescope took five fresh variables, so the theorem's visit is not
    // cached; the path proof's (at the next fuel) is
    assert_eq!(tm.next, 5);
    assert!(memo.get(&shared, (fuel, 0)).is_none());
    assert_eq!(memo.get(&p, (fuel - 1, 0)), Some(p2.clone()));
    // again: the telescope is opened again, the path proof is a hit
    assert_eq!(visit(&mut tm, &mut memo, fuel, &shared), Ok(want.clone()));
    assert_eq!(tm.next, 10);
    assert_eq!(visit(&mut tm, &mut memo, fuel - 1, &p), Ok(p2.clone()));
    assert_eq!(tm.next, 10);
    // the entry point (its own memo) agrees, with the same fresh names
    let mut fresh = TState::default();
    assert_eq!(
      transport_owned_mono(&mut fresh, &l, &env, fuel, &shared),
      Ok(want)
    );
    assert_eq!(fresh.next, 5);
    // the bound, and an unknown theorem
    let exhausted = Err("PF proof ownership: recursion bound exhausted".into());
    assert_eq!(transport_owned_mono(&mut fresh, &l, &env, 0, &p), exhausted);
    assert_eq!(
      transport_owned_mono(&mut fresh, &l, &env, 1, &shared),
      exhausted
    );
    assert_eq!(transport_owned_mono(&mut fresh, &l, &env, 1, &p), Ok(p2));
    assert_eq!(
      transport_owned_mono(&mut fresh, &l, &env, fuel, &c("h1const")),
      Err("PF proof ownership: missing theorem h1const".into())
    );
  }

  #[test]
  fn transports_a_two_member_clique() {
    let k = clique();
    let new_name = dotted("g.mutual");
    let mut tm = TState::default();
    let out = transport_pf(
      &mut tm, &k.members, &k.packed, &k.proofs, &SIGMA, &new_name, &env,
      &k.lemmas,
    )
    .unwrap();
    // the theorem's telescope and the lemma's binder
    assert_eq!(tm.next, 5);
    let renames = vec![
      (dotted("f.mutual"), dotted("g.mutual")),
      (dotted("f.mutual._proof_1"), dotted("g.mutual._proof_1")),
    ];
    assert_eq!(out.renames, renames);
    let names: Vec<Name> =
      out.decls.iter().map(|t| t.decl.name.clone()).collect();
    assert_eq!(
      names,
      ["g.mutual", "g.mutual._proof_1", "f", "g", "f.eq_1"].map(dotted)
    );
    let [packed, proof, f, g, lemma] = out.decls.as_slice() else {
      panic!("five declarations")
    };
    let s = spine();
    let s2 = s.permute(&SIGMA).unwrap();
    let d = order(&s);
    let d2 = d.permute(&SIGMA).unwrap();
    let gamma2 = s2.typ().unwrap();
    let t0 = s.leaves[0].clone();
    let prf = c("g.mutual._proof_1");
    // the packed fixpoint: `fix γ' I' F' prf`
    let tuple2 = mk_tuple(&s2, &[body1(&s2, 1), body0(&s2, 0)]).unwrap();
    let functional2 = lam("x", gamma2.clone(), tuple2);
    let inst2 = mk_inst_tree(&n_inst_ccpo_pprod(), &s2, &d2.insts).unwrap();
    let fix_args2 = [gamma2.clone(), inst2, functional2.clone(), prf.clone()];
    let value2 = mk_app_n(cnst(&n_order_fix(), &[one()]), &fix_args2);
    assert_eq!(packed.decl.typ, gamma2);
    assert_eq!(packed.decl.value, value2);
    assert!(packed.fallback.is_none());
    // the monotonicity proof: the theorem application transported, the
    // unknown proof by composition (recorded)
    let po2 = d2.packed_po().unwrap();
    let statement2 =
      monotone(&gamma2, &po2, &gamma2, &d2.po_tree(0).unwrap(), &functional2);
    assert_eq!(proof.decl.typ, statement2);
    let fs2 = [
      lam("x", gamma2.clone(), body0(&s2, 0)),
      lam("x", gamma2.clone(), body1(&s2, 1)),
    ];
    let path2 = mk_path_proof(&d2, 0).unwrap().0;
    let h0 = mk_app_n(
      c("T.mono"),
      &[gamma2.clone(), po2.clone(), fs2[0].clone(), path2],
    );
    let levels = compose_levels();
    let h1 =
      mk_compose_fallback(&SIGMA, &d, &d2, 1, &k.fs[1], &k.hs[1], &levels)
        .unwrap();
    let canonical_fs = [fs2[1].clone(), fs2[0].clone()];
    let tree = mk_mono_tree(&d2, &canonical_fs, &[h1.clone(), h0]).unwrap();
    assert_eq!(proof.decl.value, tree);
    assert_eq!(
      proof.fallback.as_deref(),
      Some("monotonicity proof 1: PF proof ownership: missing theorem h1const")
    );
    assert_eq!(tm.fallbacks.len(), 1);
    // the members project their canonical components
    let member = |x: &str, domain: &str, j: usize| {
      let call = Expr::app(proj(&n_pprod(), j, c("g.mutual")), bvar(0));
      lam(x, c(domain), call)
    };
    assert_eq!(f.decl.value, member("n", "Nat", 1));
    assert_eq!(g.decl.value, member("i", "Int", 0));
    assert_eq!(f.decl.typ, k.members[0].typ);
    // the lemma: its statement kept, its proof over the new fixpoint
    let projection = lam("x", gamma2.clone(), proj(&n_pprod(), 1, bvar(0)));
    let right = Expr::app(functional2, value2.clone());
    let fix_eq2 =
      mk_app_n(cnst(&dotted("Lean.Order.fix_eq"), &[one()]), &fix_args2);
    let congr_arg2 = mk_app_n(
      cnst(&dotted("congrArg"), &[one(), one()]),
      &[gamma2, t0, value2.clone(), right.clone(), projection.clone(), fix_eq2],
    );
    let congr_fun2 = mk_app_n(
      cnst(&dotted("congrFun"), &[one(), one()]),
      &[
        c("Nat"),
        lam("m", c("Nat"), c("Nat")),
        Expr::app(projection.clone(), value2),
        Expr::app(projection, right),
        congr_arg2,
        bvar(0),
      ],
    );
    assert_eq!(lemma.decl.typ, k.lemmas[0].0.typ);
    assert_eq!(lemma.decl.value, lam("n", c("Nat"), congr_fun2));
    // the output is a clique of the canonical order, under the identity
    let canonical = [g.decl.clone(), f.decl.clone()];
    let l2 = pf_layout(&canonical, &packed.decl, &[0, 1], &new_name).unwrap();
    assert!(decode_mono_tree(&l2, &proof.decl.value).is_some());
    // the composition construction alone, for every component
    let l = layout(&k);
    let h0c =
      mk_compose_fallback(&SIGMA, &d, &d2, 0, &k.fs[0], &k.hs[0], &levels)
        .unwrap();
    let all_composed = mk_mono_tree(&d2, &canonical_fs, &[h1, h0c]).unwrap();
    assert_eq!(conjugate_pf_mono(&l, &k.proofs[0].value), Ok(all_composed));
    // refusals leave the clique to the caller
    let refuse = |sigma: &[usize], proofs: &[Decl]| {
      let mut tm = TState::default();
      transport_pf(
        &mut tm, &k.members, &k.packed, proofs, sigma, &new_name, &env,
        &k.lemmas,
      )
      .err()
    };
    assert_eq!(
      refuse(&[0, 0], &k.proofs),
      Some("pfLayout: bad permutation".into())
    );
    assert_eq!(
      refuse(&SIGMA, &[]),
      Some(
        "PF ownership: fixpoint proof is not among the owned declarations"
          .into()
      )
    );
  }
}
