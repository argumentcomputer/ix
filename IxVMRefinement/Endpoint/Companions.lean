import IxVMRefinement.Endpoint.ConsistencyCorollary
import IxVMRefinement.Core.Steps.Whnf
import IxVMRefinement.Decl.ModeledRules
import IxVMRefinement.Lib.Bytes
import IxVMRefinement.Obs.KernelRoles
import IxVMRefinement.Obs.KernelModeled1
import IxVMRefinement.Obs.KernelWhnf1
import IxVMRefinement.Obs.KernelClaim4
import IxVMRefinement.Obs.IxonDeserialize0
import IxVMRefinement.Obs.UInt80
import Ix.Cert.Aggr.ConditionalShard
import Ix.DynamicLink.Soundness
import IxC.Kernel.Audit.Axioms

/-! # Companion Observed-Path Lemmas and Abstract Lifting Theorems

This module provides two distinct categories of results alongside the frozen
`IxVM.Consistency.CircuitComposed` statement (leaving `Ix/IxVM/ConsistencyAudit.lean`,
`Ix/IxVM/Refinement/Audit.lean`, `IxC/Kernel/Denotes.lean`, and `CircuitComposed` itself
completely untouched):

1. **Observed-Circuit Path Soundness Lemmas (directly proved from `IxVM.source` via `ObsFn`):**
   * `role_ctx_without_axioms_strips` and `role_ctx_without_axioms_preserves_rc`: prove that
     `KernelRoles::role_ctx_without_axioms` allocates no calls, is a zero-allocation identity
     on `Mk(_, _, Nil)` / `Assumed(_, Nil)`, and strips both user axioms and eval assumptions
     to `Nil` on `Mk(_, _, Node)` / `Assumed(_, Node)` / `MkEval` / `AssumedEval` while
     preserving the role table pointer and validation limit.
   * `assert_not_axiom_spec_sound` and `validate_user_axioms_sound`: prove from the observed
     `KernelRoles` path lemmas that every accepted user axiom is unbound in the role table,
     stored as a safe `KConstantInfo::Axiom` (`u = 0`), and passes all four role-restatement
     checks (`propext`, `Classical.choice`, `sorryAx`, and bound `Quot.sound`).
   * `assert_eval_endpoint_sound`, `assert_eval_type_sound`, `skip_opt_circuit_ref_stream`,
     and `load_eval_assumption_spec`: prove that every leaf loaded by
     `KernelRoles::load_eval_assumption` is BLAKE3-verified against its leaf address, matches
     `Ix.DynamicLink.deEvalAssumption`'s exact wire format (`0xE8 0x0E`, `(lhs, rhs, typ)`,
     optional `CircuitRef` trailer, EOF), and validates `lhs`/`rhs` as unbound non-block
     claimable level-monomorphic `Defn`/`Thm`/`Opaque` constants and `typ` as a non-block
     claimable level-monomorphic `Defn`/`Opaque`/`Induct` constant.
   * `eval_map_lookup_sound`, `load_eval_assumptions_sound`, and
     `load_role_ctx_eval_nonempty_and_validated`: prove lookup soundness on
     `KernelRoles::EvalMap`, Merkle-leaf loading via `load_eval_assumptions`, and that
     `KernelRoles::load_role_ctx_eval` accepts only validators `10`/`11` with a non-empty
     `eval_leaves` list validated under a non-eval base `RoleCtx`.
   * `try_eval_assumption_sound`: proves that on `MkEval`/`AssumedEval` contexts whose loaded
     `EvalMap` entries are grounded in `env` (`Ix.DynamicLink.GroundedEval`), every fired
     closed rewrite `(1, Const(rhs, []))` first verifies `role_index_of(rc, addr) = 0` and
     empty universe levels, and produces a valid `Ix.Kernel.Rules.Red` step (lifting across
     any application spine `mkAppN`).
   * `run_check_claim_eval_wire` and `run_check_env_claim_eval_wire`: confirm that validators
     `10`/`11` decode the non-optional `eval_root` after `opt_asm`, strictly disjoint from
     `Ix.Claim.de` / `InScopeTyping`.

2. **Abstract Lifting Lemmas over the Frozen `InScopeTyping` `circuitComposed` Theorem:**
   * `CircuitComposedLiftToConditionalAxioms` (`circuitComposedLiftToConditionalAxioms`,
     `_no_False`, `_seeds_inhabited`) and `CircuitComposedLiftToConditionalEvals`
     (`circuitComposedLiftToConditionalEvals`, `_discharge_step`):
     these are **abstract monotonic lifting wrappers** around the frozen `InScopeTyping`
     `circuitComposed` theorem (validators `0`–`5`, where `axioms = none` and no
     `evalAssumptions` are active). They embed `ComposedModelConclusion` into
     `Ix.Cert.Aggr.ConditionalChecked` / `Ix.DynamicLink.ConditionalOnEvals` so aggregation
     proofs can compose unconditionally verified leaves uniformly with conditional ones.
   * **Scope boundary:** these abstract lifting wrappers do **NOT** prove end-to-end
     `CircuitSound` refinement of `verify_claim` for non-empty user axioms (`axioms ≠ none`)
     or Tier-2 `evalAssumptions` (validators `10`/`11`); those modes rely on the individual
     observed-path lemmas in Section 1 plus the separate aggregation/soundness theorems in
     `Ix.Cert.Aggr.*` and `Ix.DynamicLink.Soundness`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

universe u

namespace IxVM.Refinement.Endpoint

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open IxVM.Refinement (View Digest packDigest Hashed CircuitSound)
open IxVM.Refinement.Core (RCRep addrTy red_mkAppN)
open IxVM.Refinement.Ingress (Stream ixAddr)
open IxVM.Refinement.Obs
open Ix (Claim)
open Ix.Kernel (SetTheory)
open Ix.Cert.Aggr
open Ix.DynamicLink

/-! ## 1. Observed-Path Soundness for User-Axiom Validation and Context Stripping -/

/-- `KernelRoles::role_ctx_without_axioms` allocates no calls, is a zero-allocation identity on
`Mk(_, _, Nil)` / `Assumed(_, Nil)`, and strips both user axioms and eval assumptions to `Nil`
on `Mk(_, _, Node)` / `Assumed(_, Node)` / `MkEval` / `AssumedEval`, always producing a plain
`Mk` or `Assumed` context with empty axioms and the same table pointer and validation limit. -/
theorem role_ctx_without_axioms_strips {rc r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::role_ctx_without_axioms" [rc] h r h' cs) :
    cs = [] ∧
      Heap.Extends h h' ∧
      ∃ (tbl : SourceValue F) (node : SourceValue F),
        ((h' = h ∧ r = rc) ∨
         (h' = h ++ [node] ∧ r = .ptr (.enum "KernelRoles::RoleCtxNode") h.length)) ∧
        loadValue h' r = .ok node ∧
        ((∃ lim,
            node = .construct "KernelRoles::RoleCtxNode" "Mk"
              [tbl, lim, .construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []] ∧
            ((∃ ax, loadValue h rc = .ok (.construct "KernelRoles::RoleCtxNode" "Mk" [tbl, lim, ax])) ∨
             (∃ ax evs, loadValue h rc = .ok (.construct "KernelRoles::RoleCtxNode" "MkEval" [tbl, lim, ax, evs])))) ∨
         (node = .construct "KernelRoles::RoleCtxNode" "Assumed"
            [tbl, .construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []] ∧
          ((∃ ax, loadValue h rc = .ok (.construct "KernelRoles::RoleCtxNode" "Assumed" [tbl, ax])) ∨
           (∃ ax evs, loadValue h rc = .ok (.construct "KernelRoles::RoleCtxNode" "AssumedEval" [tbl, ax, evs]))))) := by
  have hload_snoc : ∀ node : SourceValue F,
      node.type = .enum "KernelRoles::RoleCtxNode" →
      loadValue (h ++ [node]) (.ptr (.enum "KernelRoles::RoleCtxNode") h.length) = .ok node := by
    intro node hty
    rw [← hty]
    exact Ingress.loadValue_snoc h node
  match Obs.«KernelRoles::role_ctx_without_axioms».obs ev with
  | .Mk_Nil x_tbl x_lim ld hr hh hcs =>
    refine ⟨hcs, by rw [hh], x_tbl, _, .inl ⟨hh, hr⟩, ?_,
      .inl ⟨x_lim, rfl, .inl ⟨_, ld⟩⟩⟩
    rw [hh, hr]; exact ld
  | .Mk_Node x_tbl x_lim w1 w2 w3 w4 w5 ld hr hh hcs =>
    refine ⟨hcs, by rw [hh]; exact Heap.Extends.snoc h _, x_tbl, _, .inr ⟨hh, hr⟩, ?_,
      .inl ⟨x_lim, rfl, .inl ⟨_, ld⟩⟩⟩
    rw [hr, hh]
    exact hload_snoc _ (by simp)
  | .Assumed_Nil x_tbl ld hr hh hcs =>
    refine ⟨hcs, by rw [hh], x_tbl, _, .inl ⟨hh, hr⟩, ?_,
      .inr ⟨rfl, .inl ⟨_, ld⟩⟩⟩
    rw [hh, hr]; exact ld
  | .Assumed_Node x_tbl w1 w2 w3 w4 w5 ld hr hh hcs =>
    refine ⟨hcs, by rw [hh]; exact Heap.Extends.snoc h _, x_tbl, _, .inr ⟨hh, hr⟩, ?_,
      .inr ⟨rfl, .inl ⟨_, ld⟩⟩⟩
    rw [hr, hh]
    exact hload_snoc _ (by simp)
  | .MkEval x_tbl x_lim w_ax w_ev ld hr hh hcs =>
    refine ⟨hcs, by rw [hh]; exact Heap.Extends.snoc h _, x_tbl, _, .inr ⟨hh, hr⟩, ?_,
      .inl ⟨x_lim, rfl, .inr ⟨w_ax, w_ev, ld⟩⟩⟩
    rw [hr, hh]
    exact hload_snoc _ (by simp)
  | .AssumedEval x_tbl w_ax w_ev ld hr hh hcs =>
    refine ⟨hcs, by rw [hh]; exact Heap.Extends.snoc h _, x_tbl, _, .inr ⟨hh, hr⟩, ?_,
      .inr ⟨rfl, .inr ⟨w_ax, w_ev, ld⟩⟩⟩
    rw [hr, hh]
    exact hload_snoc _ (by simp)

/-- Applying `KernelRoles::role_ctx_without_axioms` to any standard `RCRep t lim h rc`
preserves `RCRep t lim h' r` with empty (`Nil`) user axioms. -/
theorem role_ctx_without_axioms_preserves_rc {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {rc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : RCRep t lim h rc)
    (ev : ObsFn W "KernelRoles::role_ctx_without_axioms" [rc] h r h' cs) :
    RCRep t lim h' r ∧
      Heap.Extends h h' ∧
      cs = [] := by
  obtain ⟨tbl, ax, node, hload, hnode, htbl⟩ := hrc
  obtain ⟨hcs, ext, x_tbl, node', _, hld', hcases⟩ := role_ctx_without_axioms_strips ev
  refine ⟨⟨x_tbl, .construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" [], node', hld', ?_, ?_⟩, ext, hcs⟩
  · rcases hcases with ⟨x_lim, hnode', hprev⟩ | ⟨hnode', hprev⟩
    · rcases hprev with ⟨ax', hld_old⟩ | ⟨ax', evs', hld_old⟩
      · rw [hload] at hld_old
        rcases hnode with ⟨n, hlim, hlt, rfl⟩ | ⟨_, rfl⟩
        · injection hld_old with hv
          injection hv with _ _ hxs
          injection hxs with hxt hxs1
          injection hxs1 with hxl _
          subst hxt hxl
          exact .inl ⟨n, hlim, hlt, hnode'⟩
        · simp at hld_old
      · rw [hload] at hld_old
        rcases hnode with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ <;> simp at hld_old
    · rcases hprev with ⟨ax', hld_old⟩ | ⟨ax', evs', hld_old⟩
      · rw [hload] at hld_old
        rcases hnode with ⟨_, _, _, rfl⟩ | ⟨hlim, rfl⟩
        · simp at hld_old
        · injection hld_old with hv
          injection hv with _ _ hxs
          injection hxs with hxt _
          subst hxt
          exact .inr ⟨hlim, hnode'⟩
      · rw [hload] at hld_old
        rcases hnode with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ <;> simp at hld_old
  · rcases hcases with ⟨x_lim, _, hprev⟩ | ⟨_, hprev⟩
    · rcases hprev with ⟨ax', hld_old⟩ | ⟨ax', evs', hld_old⟩
      · rw [hload] at hld_old
        rcases hnode with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩
        · injection hld_old with hv
          injection hv with _ _ hxs
          injection hxs with hxt _
          subst hxt
          exact htbl.mono ext
        · simp at hld_old
      · rw [hload] at hld_old
        rcases hnode with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ <;> simp at hld_old
    · rcases hprev with ⟨ax', hld_old⟩ | ⟨ax', evs', hld_old⟩
      · rw [hload] at hld_old
        rcases hnode with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩
        · simp at hld_old
        · injection hld_old with hv
          injection hv with _ _ hxs
          injection hxs with hxt _
          subst hxt
          exact htbl.mono ext
      · rw [hload] at hld_old
        rcases hnode with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ <;> simp at hld_old

/-- `KernelModeled::check_witness` (`kind == 2`, container recursor) unconditionally strips both
user axioms and Tier-2 eval assumptions via `KernelRoles::role_ctx_without_axioms` before
invoking `KernelModeled::check_container_rec`, so container-recursor validation always runs
under a plain `Mk(_, _, Nil)` / `Assumed(_, Nil)` role context with empty axioms and no eval
assumptions. -/
theorem check_witness_kind2_strips_axioms
    {rc blk x s r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelModeled::check_witness" [rc, blk, x, .field 2, s] h r h' cs) :
    ∃ (rc' iblock vCr : SourceValue F) (mW mCr mAfter : Heap F) (csCr : List (Call F)),
      Heap.Extends h mW ∧
      Heap.Extends mW mCr ∧
      ObsFn W "KernelModeled::check_container_rec" [rc', x, iblock] mCr vCr mAfter csCr ∧
      (∀ cl ∈ csCr, cl ∈ cs) ∧
      ∃ (tbl node : SourceValue F),
        loadValue mCr rc' = .ok node ∧
        ((∃ lim,
            node = .construct "KernelRoles::RoleCtxNode" "Mk"
              [tbl, lim, .construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []]) ∨
         node = .construct "KernelRoles::RoleCtxNode" "Assumed"
           [tbl, .construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []]) := by
  match Obs.«KernelModeled::check_witness».obs ev with
  | .n0 (hv14 := h0) .. => exact absurd (Value.field.inj h0) (by decide)
  | .n1 (hv171 := h1) .. => exact absurd (Value.field.inj h1) (by decide)
  | .n3 (hv447 := h3) .. => exact absurd (Value.field.inj h3) (by decide)
  | .n2 (ev328 := evCnt) (ev_dpuowbtw := evW) (ev_kjcbizia := evStrip)
      (ev414 := evCr) (hc442 := hcs) .. =>
    obtain ⟨_, extStrip, tbl, node, _, hld', hcases⟩ := role_ctx_without_axioms_strips evStrip
    refine ⟨_, _, _, _, _, _, _, evCnt.heap_extends.trans evW.heap_extends, extStrip,
      evCr, fun cl hcl => by rw [hcs]; simp [hcl], tbl, node, hld', ?_⟩
    rcases hcases with ⟨lim, hnode, _⟩ | ⟨hnode, _⟩
    · exact .inl ⟨lim, hnode⟩
    · exact .inr hnode

/-- Every accepted derivation of `KernelRoles::assert_not_axiom_spec` returns unit after verifying
all four axiom-role guards: `(x_nl, x_ty)` does not restate `propext`, does not restate
`Classical.choice`, does not restate `sorryAx`, and (whenever `role_quot_sound` is bound in
`x_tbl`, i.e. `role_is_bound = 1`) does not restate `Quot.sound`. -/
theorem assert_not_axiom_spec_sound {x_tbl x_nl x_ty r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::assert_not_axiom_spec" [x_tbl, x_nl, x_ty] h r h' cs) :
    r = .tuple [] ∧ Heap.Extends h h' ∧
      (∃ (v_p v_c v_s v_q : SourceValue F)
         (m1 m2 m3 m4 m5 m6 m7 : Heap F)
         (cs1 cs2 cs3 cs4 cs5 cs6 cs7 : List (Call F)),
        ObsFn W "KernelRoleSpec::role_propext" [] h v_p m1 cs1 ∧
        ObsFn W "KernelRoles::restates_role" [x_tbl, x_nl, x_ty, v_p] m1 (.field 0) m2 cs2 ∧
        ObsFn W "KernelRoleSpec::role_choice" [] m2 v_c m3 cs3 ∧
        ObsFn W "KernelRoles::restates_role" [x_tbl, x_nl, x_ty, v_c] m3 (.field 0) m4 cs4 ∧
        ObsFn W "KernelRoleSpec::role_sorry_ax" [] m4 v_s m5 cs5 ∧
        ObsFn W "KernelRoles::restates_role" [x_tbl, x_nl, x_ty, v_s] m5 (.field 0) m6 cs6 ∧
        ObsFn W "KernelRoleSpec::role_quot_sound" [] m6 v_q m7 cs7 ∧
        ((∃ (m8 m9 : Heap F) (v_q2 : SourceValue F) (cs8 cs9 cs10 : List (Call F)),
            ObsFn W "KernelRoles::role_is_bound" [x_tbl, v_q] m7 (.field 1) m8 cs8 ∧
            ObsFn W "KernelRoleSpec::role_quot_sound" [] m8 v_q2 m9 cs9 ∧
            ObsFn W "KernelRoles::restates_role" [x_tbl, x_nl, x_ty, v_q2] m9 (.field 0) h' cs10) ∨
         (∃ (v_b : SourceValue F) (cs8 : List (Call F)),
            v_b ≠ .field 1 ∧
            ObsFn W "KernelRoles::role_is_bound" [x_tbl, v_q] m7 v_b h' cs8))) := by
  match Obs.«KernelRoles::assert_not_axiom_spec».obs ev with
  | .n1 (ev62 := ev_p) (ev25 := ev_rp) (heq69 := h0p)
      (ev131 := ev_c) (ev94 := ev_rc) (heq138 := h0c)
      (ev200 := ev_s) (ev163 := ev_rs) (heq207 := h0s)
      (ev243 := ev_q) (ev222 := ev_qb)
      (ev309 := ev_q2) (ev272 := ev_rq) (heq316 := h0q)
      (he319 := hr) (he320 := hh) .. =>
    subst h0p h0c h0s h0q hh
    exact ⟨hr, ev.heap_extends, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      ev_p, ev_rp, ev_c, ev_rc, ev_s, ev_rs, ev_q, .inl ⟨_, _, _, _, _, _, ev_qb, ev_q2, ev_rq⟩⟩
  | .other (ev62 := ev_p) (ev25 := ev_rp) (heq69 := h0p)
      (ev131 := ev_c) (ev94 := ev_rc) (heq138 := h0c)
      (ev200 := ev_s) (ev163 := ev_rs) (heq207 := h0s)
      (ev243 := ev_q) (ev222 := ev_qb) (hne322 := hneq)
      (he328 := hr) (he329 := hh) .. =>
    subst h0p h0c h0s hh
    exact ⟨hr, ev.heap_extends, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      ev_p, ev_rp, ev_c, ev_rc, ev_s, ev_rs, ev_q, .inr ⟨_, _, hneq, ev_qb⟩⟩

/-- Every leaf visited by an accepting `KernelRoles::validate_user_axioms` derivation is:
(1) not bound in `x_tbl`'s role address index (`rbtree_map_lookup_or_default` returns `0`),
(2) stored in the environment as a safe `KConstantInfo::Axiom(nl, ty, 0)` (not a definition,
inductive, or unsafe axiom), and
(3) accepted by `KernelRoles::assert_not_axiom_spec`. -/
def UserAxiomLeafChecked (x_tbl x_a : SourceValue F) (h_start : Heap F) : Prop :=
  ∃ (v_idx : SourceValue F) (m_idx m_lk m_ci m_spec : Heap F) (p_ci x_nl x_ty v_spec : SourceValue F)
    (cs1 cs2 cs3 cs4 : List (Call F)),
    Heap.Extends h_start m_idx ∧
    ObsFn W "KernelRoles::role_addr_index" [x_tbl] h_start v_idx m_idx cs1 ∧
    ObsFn W Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>» [x_a, v_idx, .field 0] m_idx (.field 0) m_lk cs2 ∧
    ObsFn W "Ingress::get_ci" [x_a] m_lk p_ci m_ci cs3 ∧
    loadValue m_ci p_ci = .ok (.construct "KernelTypes::KConstantInfo" "Axiom" [x_nl, x_ty, .field 0]) ∧
    ObsFn W "KernelRoles::assert_not_axiom_spec" [x_tbl, x_nl, x_ty] m_ci v_spec m_spec cs4

/-- Inductive soundness of `KernelRoles::validate_user_axioms`: every list element in `x_leaves`
satisfies `UserAxiomLeafChecked` (and the `Cons_other` branch rejecting non-axioms is unreachable
on any accepting derivation). -/
theorem validate_user_axioms_sound :
    ∀ {n : Nat} {x_tbl x_leaves x_acc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
      {xs : List (SourceValue F)},
      cs.length ≤ n →
      Aiur.Library.List.RepList Names.«Lists::Node<&[Field; 32]>» (fun _ x y => x = y) h xs x_leaves →
      ObsFn W "KernelRoles::validate_user_axioms" [x_tbl, x_leaves, x_acc] h r h' cs →
      Heap.Extends h h' ∧
        ∀ x_a ∈ xs, ∃ m, Heap.Extends h m ∧ Heap.Extends m h' ∧ UserAxiomLeafChecked x_tbl x_a m := by
  intro n
  induction n with
  | zero =>
    intro x_tbl x_leaves x_acc r h h' cs xs hlen hlist ev
    match Obs.«KernelRoles::validate_user_axioms».obs ev with
    | .Nil (ld12 := ld) (he22 := hh) .. =>
      subst hh
      cases hlist with
      | nil _ => exact ⟨Heap.Extends.refl _, fun _ hm => nomatch hm⟩
      | cons cell _ _ =>
        rw [Ingress.load_cell cell] at ld
        simp at ld
    | .Cons_Axiom (hc279 := hcs) .. =>
      rw [hcs] at hlen; simp at hlen
    | .Cons_other (heq309 := h01) .. =>
      have h : (0 : F) = 1 := Value.field.inj h01
      exact absurd h.symm one_ne_zero
  | succ n ih =>
    intro x_tbl x_leaves x_acc r h h' cs xs hlen hlist ev
    match Obs.«KernelRoles::validate_user_axioms».obs ev with
    | .Nil (ld12 := ld) (he22 := hh) .. =>
      subst hh
      cases hlist with
      | nil _ => exact ⟨Heap.Extends.refl _, fun _ hm => nomatch hm⟩
      | cons cell _ _ =>
        rw [Ingress.load_cell cell] at ld
        simp at ld
    | .Cons_other (heq309 := h01) .. =>
      have h : (0 : F) = 1 := Value.field.inj h01
      exact absurd h.symm one_ne_zero
    | .Cons_Axiom x_a x_rest v52 m55 cs63 v67 m77 cs85 m110 p118 cs124 x_nl x_ty x_u v183 m184
        cs194 cs224 v229 m245 cs253 ld12 ev87 ev65 heq108 ev126 ld120 heq182 ev196 ev255 ev226 hc279 =>
      subst heq108 heq182
      cases hlist with
      | nil cell =>
        rw [Ingress.load_cell cell] at ld12
        simp at ld12
      | cons cell hhead htail =>
        rw [Ingress.load_cell cell] at ld12
        injection ld12 with hv
        injection hv with _ _ hargs
        injection hargs with hxa hrest_eq
        injection hrest_eq with hxrest _
        subst hhead hxa hxrest
        have ext_step : Heap.Extends h m245 :=
          ev87.heap_extends.trans (ev65.heap_extends.trans
            (ev126.heap_extends.trans (ev196.heap_extends.trans ev255.heap_extends)))
        have htail' := Aiur.Library.List.repList_heapMono₂ Names.«Lists::Node<&[Field; 32]>»
          (fun _ _ _ _ _ heq => heq) ext_step htail
        have hlen_rec : cs224.length ≤ n := by
          rw [hc279] at hlen
          simp only [List.length_cons, List.length_append] at hlen
          omega
        obtain ⟨ext_rec, hrec⟩ := ih hlen_rec htail' ev226
        refine ⟨ext_step.trans ext_rec, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hmem
        · refine ⟨h, Heap.Extends.refl h, ext_step.trans ext_rec,
            v67, m77, m55, m110, m184, p118, x_nl, x_ty, v183, cs85, cs63, cs124, cs194,
            ev87.heap_extends, ev87, ev65, ev126, ld120, ev196⟩
        · obtain ⟨m, hm1, hm2, hchk⟩ := hrec y hmem
          exact ⟨m, ext_step.trans hm1, hm2, hchk⟩

/-! ## 2. Observed-Path Soundness for Tier-2 `EvalAssumption` Validation and Rewrite Hook -/

private theorem bv_eq_of_u8_to_field {b : UInt8} {v : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (k : UInt8)
    (ev : ObsFn W "UInt8::to_field" [Ingress.bv b] h v h' cs)
    (hv : v = .field (k.toNat : F)) :
    b = k ∧ h' = h := by
  obtain ⟨hr, hh, -⟩ := Obs.«UInt8::to_field».obs ev
  rw [hr] at hv
  have hf : (b.toNat : F) = (k.toNat : F) := Value.field.inj hv
  rw [ZMod.natCast_eq_natCast_iff'] at hf
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  have hb : b.toNat < Aiur.Library.U32.Goldilocks.modulus := by
    have := b.toNat_lt; omega
  have hk : k.toNat < Aiur.Library.U32.Goldilocks.modulus := by
    have := k.toNat_lt; omega
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hk] at hf
  exact ⟨UInt8.ext (by omega), hh⟩

private theorem read_byte_exact {s x_b x_s2 : SourceValue F} {bytes : List UInt8}
    {h h' : Heap F} {cs : List (Call F)}
    (hs : Stream h bytes s)
    (ev : ObsFn W "IxonDeserialize::read_byte" [s] h (.tuple [x_b, x_s2]) h' cs) :
    ∃ (b : UInt8) (rem : List UInt8),
      bytes = b :: rem ∧ x_b = Ingress.bv b ∧ Stream h' rem x_s2 ∧ h' = h := by
  match Obs.«IxonDeserialize::read_byte».obs ev with
  | .run (ld11 := ld) (he30 := hr) (he45 := hh) .. =>
    subst hh
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr
    obtain ⟨hb, hs2⟩ := hr
    rcases Ingress.stream_inv hs ld with ⟨_, hv⟩ | ⟨b, rem, tail, hbytes, hv, htail⟩
    · simp at hv
    · injection hv with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      exact ⟨b, rem, hbytes, hb.trans hargs.1, by rw [hs2, hargs.2]; exact htail, rfl⟩

/-- `IxonDeserialize::get_u64_le` on a byte stream with count `n ≤ 8` consumes exactly `n` bytes
without modifying the heap. -/
theorem get_u64_le_stream :
    ∀ (n : Nat) (_ : n ≤ 8) {s x_w x_rest : SourceValue F} {bytes : List UInt8}
      {h h' : Heap F} {cs : List (Call F)},
      Stream h bytes s →
      ObsFn W "IxonDeserialize::get_u64_le" [s, .field (n : F)] h (.tuple [x_w, x_rest]) h' cs →
      ∃ (pre rem : List UInt8),
        bytes = pre ++ rem ∧ pre.length = n ∧ Stream h' rem x_rest ∧ h' = h := by
  intro n
  induction n with
  | zero =>
    intro _ s x_w x_rest bytes h h' cs hs ev
    match Obs.«IxonDeserialize::get_u64_le».obs ev with
    | .n0 (he19 := hr) (he35 := hh) .. =>
      subst hh
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr
      obtain ⟨_, hrest⟩ := hr
      exact ⟨[], bytes, rfl, rfl, by rw [hrest]; exact hs, rfl⟩
    | .other (hne37 := hne) .. =>
      exact absurd (by simp : (Value.field (0 : Nat) : SourceValue F) = .field 0) hne
  | succ n ih =>
    intro hle s x_w x_rest bytes h h' cs hs ev
    have hne0 : ((n + 1 : Nat) : F) ≠ 0 := by
      intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
      have hdiv := Nat.le_of_dvd (by omega) h0
      omega
    match Obs.«IxonDeserialize::get_u64_le».obs ev with
    | .n0 (hv14 := hv) .. =>
      exact absurd (Value.field.inj hv) hne0
    | .other x_byte x_s m67 cs77 v81 x_s2 _ _ _ _ _ _ _ _ _ ld51 op102 ev79 he174 he254 _ =>
      rcases Ingress.stream_inv hs ld51 with ⟨_, hv⟩ | ⟨b, tailBytes, tailPtr, hbytes, hv, htail⟩
      · simp at hv
      · injection hv with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨_, hxs⟩ := hargs
        subst hxs
        have hv81 : v81 = .field (n : F) := by
          simp only [evalBinOp, Except.ok.injEq] at op102
          rw [← op102]
          congr 1
          push_cast
          ring
        subst hv81
        obtain ⟨pre, rem, htail_eq, hpre_len, hrem, hm67⟩ := ih (by omega) htail ev79
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he174
        obtain ⟨_, hrest_eq⟩ := he174
        subst he254 hm67
        refine ⟨b :: pre, rem, ?_, by simp [hpre_len], by rw [hrest_eq]; exact hrem, rfl⟩
        rw [hbytes, htail_eq]
        rfl

/-- `KernelRoles::skip_opt_circuit_ref` consumes either `0x00` (no circuit ref) or
`0x01 || vk (32 bytes) || entry (8 bytes)` off the stream, matching `Ix.DynamicLink.deEvalAssumption`'s
optional `CircuitRef` trailer byte-for-byte. -/
theorem skip_opt_circuit_ref_stream {s r : SourceValue F} {bytes : List UInt8}
    {h h' : Heap F} {cs : List (Call F)}
    (hs : Stream h bytes s)
    (ev : ObsFn W "KernelRoles::skip_opt_circuit_ref" [s] h r h' cs) :
    Heap.Extends h h' ∧
      ∃ (tail rem : List UInt8),
        bytes = tail ++ rem ∧
        Stream h' rem r ∧
        (tail = [0] ∨ ∃ (vk : Bytes.Address) (entryBytes : List UInt8),
          entryBytes.length = 8 ∧ tail = 1 :: (vk.toList ++ entryBytes)) := by
  match Obs.«KernelRoles::skip_opt_circuit_ref».obs ev with
  | .n0 (ev_refohbpr := ev_rb) (ev_expwpmxb := ev_tf) (he_whiproaa := hr) (he_bzwoglyf := hh) .. =>
    obtain ⟨b, rem, hbytes, hb, hrem, hm1⟩ := read_byte_exact hs ev_rb
    subst hb hm1
    obtain ⟨hb0, hm2⟩ := bv_eq_of_u8_to_field 0 ev_tf rfl
    subst hb0 hm2 hr hh
    exact ⟨Heap.Extends.refl _, [0], rem, hbytes, hrem, .inl rfl⟩
  | .n1 (ev_refohbpr := ev_rb) (ev_expwpmxb := ev_tf) (ev_vcmrrolg := ev_ga)
      (ev_belvtyxj := ev_u64) (he_ctxabfnl := hr) (he_wptfmeay := hh) .. =>
    obtain ⟨b, rem1, hbytes, hb, hrem1, hm1⟩ := read_byte_exact hs ev_rb
    subst hb hm1
    obtain ⟨hb1, hm2⟩ := bv_eq_of_u8_to_field 1 ev_tf rfl
    subst hb1 hm2
    obtain ⟨vk, rem2, _, _, hrem1_eq, htup, _, hrem2, ext_ga, _⟩ := Decl.get_address_spec hrem1 ev_ga
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    obtain ⟨_, hs3⟩ := htup
    rw [← hs3] at hrem2
    obtain ⟨entryBytes, rem3, hrem2_eq, helen, hrem3, hm4⟩ :=
      get_u64_le_stream 8 (le_refl 8) hrem2 ev_u64
    subst hr hh hm4
    refine ⟨ext_ga, 1 :: (vk.toList ++ entryBytes), rem3, ?_, hrem3, .inr ⟨vk, entryBytes, helen, rfl⟩⟩
    rw [hbytes, hrem1_eq, hrem2_eq]
    simp [List.append_assoc]
  | .other (heq_lerbwjzr := h01) .. =>
    exact absurd (Value.field.inj h01).symm one_ne_zero

/-- Soundness of `KernelRoles::assert_eval_endpoint`: every accepted `lhs`/`rhs` endpoint of an
`EvalAssumption` is unbound in the role table (`role_index_of = 0`), passes `assert_not_block_ref`
and `assert_claimable`, and resolves via `Ingress::get_ci` to a level-monomorphic (`nl = 0`)
`Defn`, `Thm`, or `Opaque` constant (never an inductive/ctor/recursor/axiom/quotient). -/
theorem assert_eval_endpoint_sound {x_rc x_addr r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::assert_eval_endpoint" [x_rc, x_addr] h r h' cs) :
    r = .tuple [] ∧ Heap.Extends h h' ∧
      ∃ (m1 m2 m3 : Heap F) (v_nb v_cl p_ci : SourceValue F)
        (cs1 cs2 cs3 cs4 : List (Call F)),
        ObsFn W "KernelRoles::role_index_of" [x_rc, x_addr] h (.field 0) m1 cs1 ∧
        ObsFn W "KernelClaim::assert_not_block_ref" [x_addr] m1 v_nb m2 cs2 ∧
        ObsFn W "KernelClaim::assert_claimable" [x_rc, x_addr] m2 v_cl m3 cs3 ∧
        ObsFn W "Ingress::get_ci" [x_addr] m3 p_ci h' cs4 ∧
        ((∃ a b c d, loadValue h' p_ci = .ok (.construct "KernelTypes::KConstantInfo" "Defn" [.field 0, a, b, c, d])) ∨
         (∃ a b, loadValue h' p_ci = .ok (.construct "KernelTypes::KConstantInfo" "Thm" [.field 0, a, b])) ∨
         (∃ a b c, loadValue h' p_ci = .ok (.construct "KernelTypes::KConstantInfo" "Opaque" [.field 0, a, b, c]))) := by
  match Obs.«KernelRoles::assert_eval_endpoint».obs ev with
  | .Defn (ev_vevglgqm := ev_ri) (heq_epnnxqek := hri0)
      (ev_izbhhymo := ev_nb) (ev_rctvdlmn := ev_cl) (ev_aoulgoya := ev_ci)
      (ld_bolbylmd := ld) (heq_noendfjh := hnl0) (he_kkopgppo := hr) (he_dpwikpsr := hh) .. =>
    subst hri0 hnl0 hh
    exact ⟨hr, ev.heap_extends, _, _, _, _, _, _, _, _, _, _,
      ev_ri, ev_nb, ev_cl, ev_ci, .inl ⟨_, _, _, _, ld⟩⟩
  | .Thm (ev_vevglgqm := ev_ri) (heq_epnnxqek := hri0)
      (ev_izbhhymo := ev_nb) (ev_rctvdlmn := ev_cl) (ev_aoulgoya := ev_ci)
      (ld_bolbylmd := ld) (heq_ihcbzptu := hnl0) (he_epmqicjq := hr) (he_swhgpsoc := hh) .. =>
    subst hri0 hnl0 hh
    exact ⟨hr, ev.heap_extends, _, _, _, _, _, _, _, _, _, _,
      ev_ri, ev_nb, ev_cl, ev_ci, .inr (.inl ⟨_, _, ld⟩)⟩
  | .Opaque (ev_vevglgqm := ev_ri) (heq_epnnxqek := hri0)
      (ev_izbhhymo := ev_nb) (ev_rctvdlmn := ev_cl) (ev_aoulgoya := ev_ci)
      (ld_bolbylmd := ld) (heq_kvowggfn := hnl0) (he_gkbaahej := hr) (he_jbjpxbrn := hh) .. =>
    subst hri0 hnl0 hh
    exact ⟨hr, ev.heap_extends, _, _, _, _, _, _, _, _, _, _,
      ev_ri, ev_nb, ev_cl, ev_ci, .inr (.inr ⟨_, _, _, ld⟩)⟩
  | .other (heq_lerbwjzr := h01) .. =>
    exact absurd (Value.field.inj h01).symm one_ne_zero

/-- Soundness of `KernelRoles::assert_eval_type`: every accepted `typ` of an `EvalAssumption`
passes `assert_not_block_ref` and `assert_claimable`, and resolves via `Ingress::get_ci` to a
level-monomorphic (`nl = 0`) `Defn`, `Opaque`, or `Induct` constant. -/
theorem assert_eval_type_sound {x_rc x_addr r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::assert_eval_type" [x_rc, x_addr] h r h' cs) :
    r = .tuple [] ∧ Heap.Extends h h' ∧
      ∃ (m1 m2 : Heap F) (v_nb v_cl p_ci : SourceValue F)
        (cs1 cs2 cs3 : List (Call F)),
        ObsFn W "KernelClaim::assert_not_block_ref" [x_addr] h v_nb m1 cs1 ∧
        ObsFn W "KernelClaim::assert_claimable" [x_rc, x_addr] m1 v_cl m2 cs2 ∧
        ObsFn W "Ingress::get_ci" [x_addr] m2 p_ci h' cs3 ∧
        ((∃ a b c d, loadValue h' p_ci = .ok (.construct "KernelTypes::KConstantInfo" "Defn" [.field 0, a, b, c, d])) ∨
         (∃ a b c, loadValue h' p_ci = .ok (.construct "KernelTypes::KConstantInfo" "Opaque" [.field 0, a, b, c])) ∨
         (∃ a b c d e f g, loadValue h' p_ci = .ok (.construct "KernelTypes::KConstantInfo" "Induct" [.field 0, a, b, c, d, e, f, g]))) := by
  match Obs.«KernelRoles::assert_eval_type».obs ev with
  | .Defn (ev_izbhhymo := ev_nb) (ev_rctvdlmn := ev_cl) (ev_aoulgoya := ev_ci)
      (ld_bolbylmd := ld) (heq_noendfjh := hnl0) (he_kkopgppo := hr) (he_dpwikpsr := hh) .. =>
    subst hnl0 hh
    exact ⟨hr, ev.heap_extends, _, _, _, _, _, _, _, _,
      ev_nb, ev_cl, ev_ci, .inl ⟨_, _, _, _, ld⟩⟩
  | .Opaque (ev_izbhhymo := ev_nb) (ev_rctvdlmn := ev_cl) (ev_aoulgoya := ev_ci)
      (ld_bolbylmd := ld) (heq_kvowggfn := hnl0) (he_gkbaahej := hr) (he_jbjpxbrn := hh) .. =>
    subst hnl0 hh
    exact ⟨hr, ev.heap_extends, _, _, _, _, _, _, _, _,
      ev_nb, ev_cl, ev_ci, .inr (.inl ⟨_, _, _, ld⟩)⟩
  | .Induct (ev_izbhhymo := ev_nb) (ev_rctvdlmn := ev_cl) (ev_aoulgoya := ev_ci)
      (ld_bolbylmd := ld) (heq_lqduoekl := hnl0) (he_wispjzeg := hr) (he_gnlytebt := hh) .. =>
    subst hnl0 hh
    exact ⟨hr, ev.heap_extends, _, _, _, _, _, _, _, _,
      ev_nb, ev_cl, ev_ci, .inr (.inr ⟨_, _, _, _, _, _, _, ld⟩)⟩
  | .other (heq_lerbwjzr := h01) .. =>
    exact absurd (Value.field.inj h01).symm one_ne_zero

/-- **Wire-format, BLAKE3, and endpoint-validation soundness of
`KernelRoles::load_eval_assumption`:**
every accepted execution on `(x_rc, leafAddr)` hashes a byte array `bytes` with
`Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr leafAddr`, checks header `[0xE8, 0x0E]`
(`Ix.DynamicLink.VARIANT_EVAL_ASSUMPTION = 22`), decodes `(lhs, rhs, typ)` + optional
`CircuitRef` (`0x00` or `0x01 || vk || entry_u64_le`) with exact EOF, validates `lhs` and `rhs`
via `KernelRoles::assert_eval_endpoint` and `typ` via `KernelRoles::assert_eval_type`, and
returns represented addresses for `(lhs, rhs, typ)`. -/
theorem load_eval_assumption_spec {leafAddr : Bytes.Address}
    {x_rc x_leaf x_lhs x_rhs x_typ : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hleaf : Bytes.RepAddressRef addrTy h leafAddr x_leaf)
    (ev : ObsFn W "KernelRoles::load_eval_assumption" [x_rc, x_leaf] h
      (.tuple [x_lhs, x_rhs, x_typ]) h' cs) :
    Heap.Extends h h' ∧
      ∃ (bytes : List UInt8) (lhs rhs typ : Bytes.Address) (trailer : List UInt8)
        (m_ep0 m_ep1 m_ep2 : Heap F) (v_ep1 v_ep2 v_tp : SourceValue F)
        (cs_ep1 cs_ep2 cs_tp : List (Call F)),
        Hashed cs ⟨bytes.toArray⟩ ∧
        Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr leafAddr ∧
        bytes = (0xE8 : UInt8) :: (0x0E : UInt8) :: (lhs.toList ++ rhs.toList ++ typ.toList ++ trailer) ∧
        (trailer = [0] ∨ ∃ (vk : Bytes.Address) (entryBytes : List UInt8),
          entryBytes.length = 8 ∧ trailer = 1 :: (vk.toList ++ entryBytes)) ∧
        ObsFn W "KernelRoles::assert_eval_endpoint" [x_rc, x_lhs] m_ep0 v_ep1 m_ep1 cs_ep1 ∧
        ObsFn W "KernelRoles::assert_eval_endpoint" [x_rc, x_rhs] m_ep1 v_ep2 m_ep2 cs_ep2 ∧
        ObsFn W "KernelRoles::assert_eval_type" [x_rc, x_typ] m_ep2 v_tp h' cs_tp ∧
        Bytes.RepAddressRef addrTy h' lhs x_lhs ∧
        Bytes.RepAddressRef addrTy h' rhs x_rhs ∧
        Bytes.RepAddressRef addrTy h' typ x_typ := by
  match Obs.«KernelRoles::load_eval_assumption».obs ev with
  | .run (ld_kgvpyoyw := ld_leaf) (ev_iljwditd := ev_info) (ev_umcvjpie := ev_read)
      (ev_zroxeuhd := ev_b3) (ev_rszbtwqq := ev_rb0) (ev_mwckwmlv := ev_tf0)
      (heq_xjsnqmiw := heq232) (ev_fiqxiwcw := ev_rb1) (ev_pmuwfkaa := ev_tf1)
      (heq_etiqfmqo := heq14) (ev_ehnwdtpr := ev_ga1) (ev_iqpcsnnb := ev_ga2)
      (ev_pjuvwidw := ev_ga3) (ev_hwtvpzgt := ev_skip) (ld_vmezuujf := ld_eof)
      (ev_kvjbiccd := ev_ep1) (ev_wrdsxect := ev_ep2) (ev_nnjebtdt := ev_tp)
      (he_xnwfxhtv := hr_eq) (he_aosuzxec := hh_eq) (hc_sgljalbe := hcs) .. =>
    have hraw := Ingress.load_repAddressRef hleaf ld_leaf
    subst hraw
    obtain ⟨bytes, hlen, ext1, ext2, hst, hcall, hproj⟩ := Ingress.checked_read ev_info ev_read ev_b3
    have hhashed : Hashed cs ⟨bytes.toArray⟩ :=
      Ingress.hashed_of_call (by rw [hcs]; simp [hcall]) hst
    have hdig : Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr leafAddr := by
      rw [Ingress.blake3Pure_eq, Ingress.digest_eq_of_proj rfl hproj]
    have hst3 := hst.mono ext2
    obtain ⟨b0, rem0, hbytes, hb0, hrem0, hm_rb0⟩ := read_byte_exact hst3 ev_rb0
    subst hb0 hm_rb0
    obtain ⟨hb0_eq, hm_tf0⟩ := bv_eq_of_u8_to_field (0xE8 : UInt8) ev_tf0 heq232
    subst hb0_eq hm_tf0
    obtain ⟨b1, rem1, hrem0_eq, hb1, hrem1, hm_rb1⟩ := read_byte_exact hrem0 ev_rb1
    subst hb1 hm_rb1
    obtain ⟨hb1_eq, hm_tf1⟩ := bv_eq_of_u8_to_field (0x0E : UInt8) ev_tf1 heq14
    subst hb1_eq hm_tf1
    obtain ⟨lhs, rem2, _, _, hrem1_eq, ht1, hlhs, hrem2, ext_ga1, _⟩ := Decl.get_address_spec hrem1 ev_ga1
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at ht1
    obtain ⟨hxl, hs2⟩ := ht1
    rw [← hxl] at hlhs
    rw [← hs2] at hrem2
    obtain ⟨rhs, rem3, _, _, hrem2_eq, ht2, hrhs, hrem3, ext_ga2, _⟩ := Decl.get_address_spec hrem2 ev_ga2
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at ht2
    obtain ⟨hxr, hs3⟩ := ht2
    rw [← hxr] at hrhs
    rw [← hs3] at hrem3
    obtain ⟨typ, rem4, _, _, hrem3_eq, ht3, htyp, hrem4, ext_ga3, _⟩ := Decl.get_address_spec hrem3 ev_ga3
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at ht3
    obtain ⟨hxt, hs4⟩ := ht3
    rw [← hxt] at htyp
    rw [← hs4] at hrem4
    obtain ⟨ext_skip, trailer, rem5, hrem4_eq, hrem5, htrailer⟩ := skip_opt_circuit_ref_stream hrem4 ev_skip
    have hrem5_nil : rem5 = [] := by
      rcases Ingress.stream_inv hrem5 ld_eof with ⟨hnil, _⟩ | ⟨_, _, _, _, hv, _⟩
      · exact hnil
      · simp at hv
    subst hrem5_nil
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr_eq
    obtain ⟨rfl, rfl, rfl⟩ := hr_eq
    subst hh_eq
    have ext_chk : Heap.Extends _ _ :=
      ev_ep1.heap_extends.trans (ev_ep2.heap_extends.trans ev_tp.heap_extends)
    have ext_all : Heap.Extends h _ :=
      ext1.trans (ext2.trans (ext_ga1.trans (ext_ga2.trans (ext_ga3.trans (ext_skip.trans ext_chk)))))
    refine ⟨ext_all, bytes, lhs, rhs, typ, trailer, _, _, _, _, _, _, _, _, _,
      hhashed, hdig, ?_, htrailer, ev_ep1, ev_ep2, ev_tp,
      Bytes.repAddressRef_heapMono₂ addrTy (ext_ga2.trans (ext_ga3.trans (ext_skip.trans ext_chk))) hlhs,
      Bytes.repAddressRef_heapMono₂ addrTy (ext_ga3.trans (ext_skip.trans ext_chk)) hrhs,
      Bytes.repAddressRef_heapMono₂ addrTy (ext_skip.trans ext_chk) htyp⟩
    rw [hbytes, hrem0_eq, hrem1_eq, hrem2_eq, hrem3_eq, hrem4_eq]
    simp [List.append_assoc]

/-- Representation of a list of `(lhs, rhs, typ)` address triples as a `KernelRoles::EvalMap`
linked list in heap `h`. -/
inductive EvalMapRep (h : Heap F) :
    List (Bytes.Address × Bytes.Address × Bytes.Address) → SourceValue F → Prop where
  | nil :
      EvalMapRep h [] (.construct "KernelRoles::EvalMap" "Nil" [])
  | cons {lhs rhs typ : Bytes.Address} {rest : List (Bytes.Address × Bytes.Address × Bytes.Address)}
      {x_lhs x_rhs x_typ x_rest rest_v : SourceValue F}
      (hlhs : Bytes.RepAddressRef addrTy h lhs x_lhs)
      (hrhs : Bytes.RepAddressRef addrTy h rhs x_rhs)
      (htyp : Bytes.RepAddressRef addrTy h typ x_typ)
      (hload : loadValue h x_rest = .ok rest_v)
      (hrest : EvalMapRep h rest rest_v) :
      EvalMapRep h ((lhs, rhs, typ) :: rest)
        (.construct "KernelRoles::EvalMap" "Cons" [x_lhs, x_rhs, x_typ, x_rest])

theorem EvalMapRep.mono {h h' : Heap F} (ext : Heap.Extends h h')
    {entries : List (Bytes.Address × Bytes.Address × Bytes.Address)} {v : SourceValue F}
    (hv : EvalMapRep h entries v) : EvalMapRep h' entries v := by
  induction hv with
  | nil => exact .nil
  | cons hl hr ht hld _ ih =>
    exact .cons
      (Bytes.repAddressRef_heapMono₂ addrTy ext hl)
      (Bytes.repAddressRef_heapMono₂ addrTy ext hr)
      (Bytes.repAddressRef_heapMono₂ addrTy ext ht)
      (Ingress.loadValue_extend ext hld)
      ih

/-- Soundness of `KernelRoles::eval_map_lookup`: never allocates, and whenever it returns
`(1, x_rhs)` on a represented address `a` and `EvalMapRep h entries evals`, there exists
`(a, rhs, typ) ∈ entries` with `x_rhs` representing `rhs`. -/
theorem eval_map_lookup_sound :
    ∀ {entries : List (Bytes.Address × Bytes.Address × Bytes.Address)}
      {a : Bytes.Address} {x_addr evals r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      EvalMapRep h entries evals →
      Bytes.RepAddressRef addrTy h a x_addr →
      ObsFn W "KernelRoles::eval_map_lookup" [x_addr, evals] h r h' cs →
      h' = h ∧
        (r = .tuple [.field 0, x_addr] ∨
          ∃ (rhs typ : Bytes.Address) (x_rhs : SourceValue F),
            r = .tuple [.field 1, x_rhs] ∧
            (a, rhs, typ) ∈ entries ∧
            Bytes.RepAddressRef addrTy h rhs x_rhs) := by
  intro entries
  induction entries with
  | nil =>
    intro a x_addr evals r h h' cs hev ha ev
    cases hev
    match Obs.«KernelRoles::eval_map_lookup».obs ev with
    | .Nil (he_obivbbhy := hr) (he_twavpkij := hh) .. =>
      exact ⟨hh, .inl hr⟩
    | .Cons_n1 (hv_nameeqmc := hv) .. | .Cons_other (hv_nameeqmc := hv) .. =>
      simp at hv
  | cons entry rest ih =>
    rcases entry with ⟨lhs, rhs, typ⟩
    intro a x_addr evals r h h' cs hev ha ev
    cases hev with
    | cons hlhs hrhs htyp hld hrest =>
      match Obs.«KernelRoles::eval_map_lookup».obs ev with
      | .Nil (hv_tbotnlts := hv) .. =>
        simp at hv
      | .Cons_n1 x_l x_r x_t x_rest_p m_eq cs_eq _ hv ev_eq hr hh _ =>
        injection hv with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
        obtain ⟨heq_f, hm_eq⟩ := Lib.address_eq_spec ev_eq ha hlhs
        subst hm_eq hh
        by_cases hal : a = lhs
        · subst hal
          exact ⟨rfl, .inr ⟨rhs, typ, _, hr, List.mem_cons_self, hrhs⟩⟩
        · rw [ite_eq_right hal] at heq_f
          exact absurd (Value.field.inj heq_f) one_ne_zero
      | .Cons_other x_l x_r x_t x_rest_p v_eq m_eq cs_eq cs_rec v_next _ hv ev_eq _ ld_next ev_rec _ =>
        injection hv with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
        obtain ⟨_, hm_eq⟩ := Lib.address_eq_spec ev_eq ha hlhs
        subst hm_eq
        rw [hld] at ld_next
        injection ld_next with hnext
        subst hnext
        obtain ⟨hh', hres⟩ := ih hrest ha ev_rec
        refine ⟨hh', hres.imp_right ?_⟩
        rintro ⟨rhs', typ', x_rhs', hr', hmem, hrep'⟩
        exact ⟨rhs', typ', x_rhs', hr', List.mem_cons_of_mem _ hmem, hrep'⟩

/-- Soundness of `KernelRoles::load_eval_assumptions`: every entry added to the resulting
`EvalMapRep` was verified via `load_eval_assumption_spec` (BLAKE3-hashed against its leaf address
with the exact `0xE8 0x0E` wire format, plus `assert_eval_endpoint`/`assert_eval_type` validation
under `x_rc`). -/
theorem load_eval_assumptions_sound :
    ∀ {n : Nat} {leafAddrs : List Bytes.Address}
      {accEntries : List (Bytes.Address × Bytes.Address × Bytes.Address)}
      {x_rc x_leaves x_acc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ n →
      Aiur.Library.List.RepList Names.«Lists::Node<&[Field; 32]>»
        (Bytes.RepAddressRef addrTy) h leafAddrs x_leaves →
      EvalMapRep h accEntries x_acc →
      ObsFn W "KernelRoles::load_eval_assumptions" [x_rc, x_leaves, x_acc] h r h' cs →
      Heap.Extends h h' ∧
        ∃ newEntries : List (Bytes.Address × Bytes.Address × Bytes.Address),
          EvalMapRep h' (newEntries ++ accEntries) r ∧
          (∀ e ∈ newEntries, ∃ (leafAddr : Bytes.Address) (bytes trailer : List UInt8),
            leafAddr ∈ leafAddrs ∧
            Hashed cs ⟨bytes.toArray⟩ ∧
            Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr leafAddr ∧
            bytes = (0xE8 : UInt8) :: (0x0E : UInt8) ::
              (e.1.toList ++ e.2.1.toList ++ e.2.2.toList ++ trailer) ∧
            (trailer = [0] ∨ ∃ (vk : Bytes.Address) (entryBytes : List UInt8),
              entryBytes.length = 8 ∧ trailer = 1 :: (vk.toList ++ entryBytes))) := by
  intro n
  induction n with
  | zero =>
    intro leafAddrs accEntries x_rc x_leaves x_acc r h h' cs hlen hlist hacc ev
    match Obs.«KernelRoles::load_eval_assumptions».obs ev with
    | .Nil (ld_bolbylmd := ld) (he_qkvnfwgk := hr) (he_vfgbdbrh := hh) .. =>
      subst hr hh
      exact ⟨Heap.Extends.refl _, [], hacc, fun _ hm => nomatch hm⟩
    | .Cons (hc_gtnunfxa := hcs) .. =>
      rw [hcs] at hlen; simp at hlen
  | succ n ih =>
    intro leafAddrs accEntries x_rc x_leaves x_acc r h h' cs hlen hlist hacc ev
    match Obs.«KernelRoles::load_eval_assumptions».obs ev with
    | .Nil (ld_bolbylmd := ld) (he_qkvnfwgk := hr) (he_vfgbdbrh := hh) .. =>
      subst hr hh
      exact ⟨Heap.Extends.refl _, [], hacc, fun _ hm => nomatch hm⟩
    | .Cons x_leaf x_rest m1 cs1 x_lhs x_rhs x_typ cs2 m2 ld ev_load hm2 ev_rec hcs =>
      cases hlist with
      | nil cell =>
        rw [Ingress.load_cell cell] at ld
        simp at ld
      | cons cell hhead htail =>
        rw [Ingress.load_cell cell] at ld
        injection ld with hv
        injection hv with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨rfl, rfl⟩ := hargs
        obtain ⟨ext1, bytes, lhs, rhs, typ, trailer, _, _, _, _, _, _, _, _, _,
            hhash1, hdig1, hbytes1, htr1, _, _, _, hlhs1, hrhs1, htyp1⟩ :=
          load_eval_assumption_spec hhead ev_load
        have ext_snoc : Heap.Extends m1 m2 := by rw [hm2]; exact Heap.Extends.snoc m1 x_acc
        have ext_step : Heap.Extends h m2 := ext1.trans ext_snoc
        have hacc2 : EvalMapRep m2 accEntries x_acc := hacc.mono ext_step
        have hld_acc : loadValue m2 (.ptr (Value.type x_acc) m1.length) = .ok x_acc := by
          rw [hm2]; exact Ingress.loadValue_snoc m1 x_acc
        have hacc_cons : EvalMapRep m2 ((lhs, rhs, typ) :: accEntries)
            (.construct "KernelRoles::EvalMap" "Cons"
              [x_lhs, x_rhs, x_typ, .ptr (Value.type x_acc) m1.length]) :=
          .cons
            (Bytes.repAddressRef_heapMono₂ addrTy ext_snoc hlhs1)
            (Bytes.repAddressRef_heapMono₂ addrTy ext_snoc hrhs1)
            (Bytes.repAddressRef_heapMono₂ addrTy ext_snoc htyp1)
            hld_acc hacc2
        have htail2 := Aiur.Library.List.repList_heapMono₂ Names.«Lists::Node<&[Field; 32]>»
          (Bytes.repAddressRef_heapMono₂ addrTy) ext_step htail
        have hlen_rec : cs2.length ≤ n := by
          rw [hcs] at hlen
          simp only [List.length_cons, List.length_append] at hlen
          omega
        obtain ⟨ext_rec, newRec, hmap_rec, hnew_rec⟩ := ih hlen_rec htail2 hacc_cons ev_rec
        refine ⟨ext_step.trans ext_rec, newRec ++ [(lhs, rhs, typ)], ?_, fun e he => ?_⟩
        · simpa [List.append_assoc] using hmap_rec
        · rcases List.mem_append.mp he with hmem_rec | hmem_one
          · obtain ⟨la, bs, tr, hla, hhb, hd, hb, htr⟩ := hnew_rec e hmem_rec
            have hhb' : Hashed cs ⟨bs.toArray⟩ := by
              obtain ⟨c, hc, hfn, inp, harg, hst⟩ := hhb
              exact ⟨c, by rw [hcs]; simp [hc], hfn, inp, harg, hst⟩
            exact ⟨la, bs, tr, List.mem_cons_of_mem _ hla, hhb', hd, hb, htr⟩
          · simp only [List.mem_singleton] at hmem_one
            subst hmem_one
            have hhash1' : Hashed cs ⟨bytes.toArray⟩ := by
              obtain ⟨c, hc, hfn, inp, harg, hst⟩ := hhash1
              exact ⟨c, by rw [hcs]; simp [hc], hfn, inp, harg, hst⟩
            exact ⟨_, bytes, trailer, List.mem_cons_self, hhash1', hdig1, hbytes1, htr1⟩

/-- Every accepted execution of `KernelRoles::load_role_ctx_eval` accepts only validator `10` or
`11`, verifies that `eval_leaves` loaded from `x_eval_root` is non-empty (`Cons`), and validates
every leaf via `KernelRoles::load_eval_assumptions` under a non-eval base `RoleCtx`. -/
theorem load_role_ctx_eval_nonempty_and_validated
    {x_binding x_validator x_axioms_opt x_eval_root r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::load_role_ctx_eval"
      [x_binding, x_validator, x_axioms_opt, x_eval_root] h r h' cs) :
    (x_validator = .field 10 ∨ x_validator = .field 11) ∧
      ∃ (v_leaves v_head v_tail base_rc v_evals : SourceValue F)
        (m_leaves m_base m_evals : Heap F) (cs_ev : List (Call F)),
        loadValue m_leaves v_leaves =
          .ok (.construct Names.«Lists::Node<&[Field; 32]>» "Cons" [v_head, v_tail]) ∧
        ObsFn W "KernelRoles::load_eval_assumptions"
          [base_rc, v_leaves, .construct "KernelRoles::EvalMap" "Nil" []]
          m_base v_evals m_evals cs_ev := by
  match Obs.«KernelRoles::load_role_ctx_eval».obs ev with
  | .n10 (sg_betjktew := sg_ne) (hv_umtrxiub := hv10) (ev_meddrlzi := ev_la) .. =>
    cases sg_ne with
    | Nil _ heq => exact absurd (Value.field.inj heq).symm one_ne_zero
    | Cons w1 w2 ld _ _ _ =>
      exact ⟨.inl hv10, _, w1, w2, _, _, _, _, _, _, ld, ev_la⟩
  | .n11 (sg_betjktew := sg_ne) (hv_hctqzgnh := hv11) (ev_lxenzphb := ev_la) .. =>
    cases sg_ne with
    | Nil _ heq => exact absurd (Value.field.inj heq).symm one_ne_zero
    | Cons w1 w2 ld _ _ _ =>
      exact ⟨.inr hv11, _, w1, w2, _, _, _, _, _, _, ld, ev_la⟩
  | .other (heq_lerbwjzr := h01) .. =>
    exact absurd (Value.field.inj h01).symm one_ne_zero

/-- Semantic soundness of `KernelWhnf::try_eval_assumption` under grounded `evalAssumptions`:
when `rc` is an `MkEval`/`AssumedEval` context carrying `EvalMapRep h entries evals` in which
every `(lhs, rhs, typ) ∈ entries` satisfies `Ix.DynamicLink.GroundedEval env`, any fired rewrite
`(1, new_head)` first verifies `role_index_of(rc, addr) = 0` (so bound kernel roles such as
`True`/`False` can never be rewritten) and empty universe levels, and produces a represented
`Const(rhs, [])` whose head reduces in `env` at every depth `d` — lifting across any application
spine `As` via `Core.red_mkAppN`. -/
theorem try_eval_assumption_sound
    {env : Ix.Kernel.Env .anon} {κ : Address → Ix.Kernel.Key .anon}
    {entries : List (Bytes.Address × Bytes.Address × Bytes.Address)}
    {rc evals addr lvls head r : SourceValue F} {a : Bytes.Address}
    {h h' : Heap F} {cs : List (Call F)}
    (hrc_ev :
      (∃ tbl lim ax, loadValue h rc = .ok (.construct "KernelRoles::RoleCtxNode" "MkEval" [tbl, lim, ax, evals])) ∨
      (∃ tbl ax, loadValue h rc = .ok (.construct "KernelRoles::RoleCtxNode" "AssumedEval" [tbl, ax, evals])))
    (hevals : EvalMapRep h entries evals)
    (hgrounded : ∀ e ∈ entries,
      GroundedEval env (.const (κ (ixAddr e.1)) []) (.const (κ (ixAddr e.2.1)) [])
        (.const (κ (ixAddr e.2.2)) []))
    (ha : Bytes.RepAddressRef addrTy h a addr)
    (ev : ObsFn W "KernelWhnf::try_eval_assumption" [rc, addr, lvls, head] h r h' cs) :
    Heap.Extends h h' ∧
      (r = .tuple [.field 0, head] ∨
        ∃ (rhs typ : Bytes.Address) (x_rhs x_nil_lvls new_head : SourceValue F)
          (m_ri : Heap F) (cs_ri : List (Call F)),
          r = .tuple [.field 1, new_head] ∧
          ObsFn W "KernelRoles::role_index_of" [rc, addr] h (.field 0) m_ri cs_ri ∧
          (a, rhs, typ) ∈ entries ∧
          loadValue h' lvls = .ok (.construct Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" []) ∧
          loadValue h' new_head = .ok (.construct "KernelTypes::KExprNode" "Const" [x_rhs, x_nil_lvls]) ∧
          loadValue h' x_nil_lvls = .ok (.construct Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" []) ∧
          Bytes.RepAddressRef addrTy h' rhs x_rhs ∧
          (∀ d, Ix.Kernel.Rules.DefEq env d (.const (κ (ixAddr a)) []) (.const (κ (ixAddr rhs)) [])) ∧
          (∀ d (As : List (Ix.Kernel.Expr .anon)),
            Ix.Kernel.Rules.Red env d
              (Ix.Kernel.Expr.mkAppN (.const (κ (ixAddr a)) []) As)
              (Ix.Kernel.Expr.mkAppN (.const (κ (ixAddr rhs)) []) As))) := by
  have hrc_evals_eq : ∀ {v m cs_e},
      ObsFn W "KernelRoles::role_ctx_evals" [rc] h v m cs_e → v = evals ∧ m = h := by
    intro v m cs_e ev_e
    match Obs.«KernelRoles::role_ctx_evals».obs ev_e with
    | .Mk (ld_bolbylmd := ld) .. | .Assumed (ld_bolbylmd := ld) .. =>
      rcases hrc_ev with ⟨_, _, _, hld⟩ | ⟨_, _, hld⟩ <;> (rw [hld] at ld; simp at ld)
    | .MkEval (ld_bolbylmd := ld) (he_smmhngvh := hr) (he_oypopapq := hm) .. =>
      rcases hrc_ev with ⟨_, _, _, hld⟩ | ⟨_, _, hld⟩
      · rw [hld] at ld
        injection ld with hv
        injection hv with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        exact ⟨hr.trans hargs.2.2.2.symm, hm⟩
      · rw [hld] at ld; simp at ld
    | .AssumedEval (ld_bolbylmd := ld) (he_tiijqtvf := hr) (he_rpwzmxsz := hm) .. =>
      rcases hrc_ev with ⟨_, _, _, hld⟩ | ⟨_, _, hld⟩
      · rw [hld] at ld; simp at ld
      · rw [hld] at ld
        injection ld with hv
        injection hv with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        exact ⟨hr.trans hargs.2.2.symm, hm⟩
  match Obs.«KernelWhnf::try_eval_assumption».obs ev with
  | .Nil (ev_umpbxzha := ev_e) (he_obivbbhy := hr) (he_twavpkij := hh) .. =>
    obtain ⟨_, hm⟩ := hrc_evals_eq ev_e
    rw [hh, hm]
    exact ⟨Heap.Extends.refl h, .inl hr⟩
  | .other_other (ev_umpbxzha := ev_e) (ev_bnhtnvvh := ev_ri)
      (he_evaoyjxj := hr) (he_xsgwrrwc := hh) .. =>
    obtain ⟨_, hm⟩ := hrc_evals_eq ev_e
    rw [hm] at ev_ri
    rw [hh]
    exact ⟨ev_ri.heap_extends, .inl hr⟩
  | .other_n0_other (ev_umpbxzha := ev_e) (ev_bnhtnvvh := ev_ri)
      (he_lcgekepr := hr) (he_dmoxpabx := hh) .. =>
    obtain ⟨_, hm⟩ := hrc_evals_eq ev_e
    rw [hm] at ev_ri
    rw [hh]
    exact ⟨ev_ri.heap_extends, .inl hr⟩
  | .other_n0_Nil_other (ev_umpbxzha := ev_e) (ev_bnhtnvvh := ev_ri) (ev_rjihonki := ev_lk)
      (he_bahvosot := hr) (he_tcducsae := hh) .. =>
    obtain ⟨hv, hm⟩ := hrc_evals_eq ev_e
    subst hv
    rw [hm] at ev_ri
    have ext_ri := ev_ri.heap_extends
    obtain ⟨hm_lk, _⟩ := eval_map_lookup_sound (hevals.mono ext_ri)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_ri ha) ev_lk
    rw [hh, hm_lk]
    exact ⟨ext_ri, .inl hr⟩
  | .other_n0_Nil_n1_bind v_ev m1 cs1 m_ri cs_ri m2 cs2 x_rhs m_out m_mid
      ev_e _ ev_ri ld_lvls ev_lk hr hm_out hm_mid hh _ =>
    obtain ⟨hv, hm1⟩ := hrc_evals_eq ev_e
    subst hv
    rw [hm1] at ev_ri
    have ext_ri := ev_ri.heap_extends
    obtain ⟨hm2, hres⟩ := eval_map_lookup_sound (hevals.mono ext_ri)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_ri ha) ev_lk
    rw [hm2] at hm_mid hm_out
    rcases hres with h0 | ⟨rhs, typ, x_rhs', h1, hmem, hrhs⟩
    · simp at h0
    · simp only [Value.tuple.injEq, List.cons.injEq, and_true] at h1
      obtain ⟨_, rfl⟩ := h1
      have ext1 : Heap.Extends m_ri m_mid := by rw [hm_mid]; exact Heap.Extends.snoc m_ri _
      have ext2 : Heap.Extends m_mid h' := by rw [hh, hm_out]; exact Heap.Extends.snoc m_mid _
      have ext_tail : Heap.Extends m_ri h' := ext1.trans ext2
      have ext_all : Heap.Extends h h' := ext_ri.trans ext_tail
      have hld_nil_mid :
          loadValue m_mid (.ptr (.enum Names.«Lists::Node<&KernelTypes::KLevelNode>») m_ri.length) =
            .ok (.construct Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" []) := by
        rw [hm_mid]
        have hty : (Value.construct Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" [] :
            SourceValue F).type = .enum Names.«Lists::Node<&KernelTypes::KLevelNode>» := by
          simp
        rw [← hty]
        exact Ingress.loadValue_snoc m_ri _
      have hld_nil :
          loadValue h' (.ptr (.enum Names.«Lists::Node<&KernelTypes::KLevelNode>») m_ri.length) =
            .ok (.construct Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" []) :=
        Ingress.loadValue_extend ext2 hld_nil_mid
      have hld_head :
          loadValue h' (.ptr (.enum "KernelTypes::KExprNode") m_mid.length) =
            .ok (.construct "KernelTypes::KExprNode" "Const"
              [x_rhs, .ptr (.enum Names.«Lists::Node<&KernelTypes::KLevelNode>») m_ri.length]) := by
        rw [hh, hm_out]
        have hty : (Value.construct "KernelTypes::KExprNode" "Const"
            [x_rhs, .ptr (.enum Names.«Lists::Node<&KernelTypes::KLevelNode>») m_ri.length] :
            SourceValue F).type = .enum "KernelTypes::KExprNode" := by
          simp
        rw [← hty]
        exact Ingress.loadValue_snoc m_mid _
      have hg := hgrounded (a, rhs, typ) hmem
      refine ⟨ext_all, .inr ⟨rhs, typ, x_rhs,
        .ptr (.enum Names.«Lists::Node<&KernelTypes::KLevelNode>») m_ri.length,
        .ptr (.enum "KernelTypes::KExprNode") m_mid.length,
        m_ri, cs_ri,
        hr, ev_ri, hmem, Ingress.loadValue_extend ext_tail ld_lvls, hld_head, hld_nil,
        Bytes.repAddressRef_heapMono₂ addrTy ext_tail hrhs,
        hg.defEq_all,
        fun d As => red_mkAppN As (hg.red_all (by rfl) d)⟩⟩

/-- Wire-structure confirmation for `KernelClaim::run_check_claim_eval` (validators `10`/`11`
on `Claim.check`): decodes `(binding, axioms)`, `target`, `opt_asm`, non-optional `eval_root`,
EOF `Nil`, loads the eval-enabled `RoleCtx` via `load_role_ctx_eval`, checks claimability, and
validates `check_axiom_leaves`. -/
theorem run_check_claim_eval_wire {x_validator x_s r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelClaim::run_check_claim_eval" [x_validator, x_s] h r h' cs) :
    ∃ (x_binding x_axioms x_s1 x_target x_s2 x_asm x_s3 x_eval_root x_rest v_rc : SourceValue F)
      (m1 m2 m3 m4 m5 : Heap F) (cs1 cs2 cs3 cs4 cs5 : List (Call F)),
      ObsFn W "KernelClaim::get_claim_context" [x_s] h (.tuple [x_binding, x_axioms, x_s1]) m1 cs1 ∧
      ObsFn W "IxonDeserialize::get_address" [x_s1] m1 (.tuple [x_target, x_s2]) m2 cs2 ∧
      ObsFn W "KernelClaim::get_opt_addr" [x_s2] m2 (.tuple [x_asm, x_s3]) m3 cs3 ∧
      ObsFn W "IxonDeserialize::get_address" [x_s3] m3 (.tuple [x_eval_root, x_rest]) m4 cs4 ∧
      loadValue m4 x_rest = .ok (.construct Names.«Lists::Node<Field>» "Nil" []) ∧
      ObsFn W "KernelRoles::load_role_ctx_eval" [x_binding, x_validator, x_axioms, x_eval_root] m4 v_rc m5 cs5 := by
  match Obs.«KernelClaim::run_check_claim_eval».obs ev with
  | .run m1 cs1 x_b x_ax x_s1 m2 cs2 x_t x_s2 m3 cs3 x_asm x_s3 m4 cs4 x_ev x_rest v_rc m5 cs5
      _ _ _ _ _ _ _ ev1 ev2 ev3 ev4 ld_eof ev5 _ _ _ _ =>
    exact ⟨x_b, x_ax, x_s1, x_t, x_s2, x_asm, x_s3, x_ev, x_rest, v_rc, m1, m2, m3, m4, m5,
      cs1, cs2, cs3, cs4, cs5, ev1, ev2, ev3, ev4, ld_eof, ev5⟩

/-- Wire-structure confirmation for `KernelClaim::run_check_env_claim_eval` (validators `10`/`11`
on `Claim.checkEnv`): decodes `(binding, axioms)`, `root`, `opt_asm`, non-optional `eval_root`,
EOF `Nil`, loads the eval-enabled `RoleCtx` via `load_role_ctx_eval`, runs `run_check_env_eval`,
and validates `check_axiom_leaves`. -/
theorem run_check_env_claim_eval_wire {x_validator x_s r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelClaim::run_check_env_claim_eval" [x_validator, x_s] h r h' cs) :
    ∃ (x_binding x_axioms x_s1 x_root x_s2 x_asm x_s3 x_eval_root x_rest v_rc v_env : SourceValue F)
      (m1 m2 m3 m4 m5 m6 : Heap F) (cs1 cs2 cs3 cs4 cs5 cs6 : List (Call F)),
      ObsFn W "KernelClaim::get_claim_context" [x_s] h (.tuple [x_binding, x_axioms, x_s1]) m1 cs1 ∧
      ObsFn W "IxonDeserialize::get_address" [x_s1] m1 (.tuple [x_root, x_s2]) m2 cs2 ∧
      ObsFn W "KernelClaim::get_opt_addr" [x_s2] m2 (.tuple [x_asm, x_s3]) m3 cs3 ∧
      ObsFn W "IxonDeserialize::get_address" [x_s3] m3 (.tuple [x_eval_root, x_rest]) m4 cs4 ∧
      loadValue m4 x_rest = .ok (.construct Names.«Lists::Node<Field>» "Nil" []) ∧
      ObsFn W "KernelRoles::load_role_ctx_eval" [x_binding, x_validator, x_axioms, x_eval_root] m4 v_rc m5 cs5 ∧
      ObsFn W "KernelClaim::run_check_env_eval" [v_rc, x_root, x_asm] m5 v_env m6 cs6 := by
  match Obs.«KernelClaim::run_check_env_claim_eval».obs ev with
  | .run m1 cs1 x_b x_ax x_s1 m2 cs2 x_rt x_s2 m3 cs3 x_asm x_s3 m4 cs4 x_ev x_rest v_rc m5 cs5
      v_env m6 cs6 _ ev1 ev2 ev3 ev4 ld_eof ev5 ev6 _ _ =>
    exact ⟨x_b, x_ax, x_s1, x_rt, x_s2, x_asm, x_s3, x_ev, x_rest, v_rc, v_env, m1, m2, m3, m4, m5, m6,
      cs1, cs2, cs3, cs4, cs5, cs6, ev1, ev2, ev3, ev4, ld_eof, ev5, ev6⟩

/-! ## 3. Abstract Lifting Lemmas Over Frozen `InScopeTyping` `circuitComposed`

The definitions and theorems in this section are **pure abstract lifting wrappers** around the
frozen `InScopeTyping` `circuitComposed` theorem (which proves circuit soundness for validators
`0`–`5` with `axioms = none` and no `evalAssumptions`). They do NOT extend `CircuitSound` to
non-empty user axioms or validators `10`/`11`; they allow unconditional `InScopeTyping` results
to be embedded monotonically into `Ix.Cert.Aggr.ConditionalChecked` and
`Ix.DynamicLink.ConditionalOnEvals`. -/

/-- **Abstract lifting wrapper (`CircuitComposedLiftToConditionalAxioms`)**:
monotonically lifts the frozen `InScopeTyping` `circuitComposed` conclusion
(`ComposedModelConclusion`, where `cA` has `axioms = none` and no `evalAssumptions`) into
`Ix.Cert.Aggr.ConditionalChecked` for any explicit user-axiom set `Ax : Address → Prop`.
This is an abstract weakening wrapper — it does not prove circuit-level soundness of
`verify_claim` for claims with non-empty `axioms`. -/
def CircuitComposedLiftToConditionalAxioms : Prop :=
  CircuitSound fun callsB dB =>
    CircuitSound fun callsA dA =>
      ∀ (bytesB : ByteArray) (spec a : Address), Claim.de bytesB = .ok (.binding spec a) →
        packDigest (Address.blake3Pure bytesB) = dB →
        ∀ (bytesA : ByteArray) (cA : Claim), Claim.de bytesA = .ok cA →
          packDigest (Address.blake3Pure bytesA) = dA → InScopeTyping cA →
          ∀ ctx, cA.context? = some ctx → ctx.binding = a →
            ∀ (V : View) (seeds : List Address), ClaimSeeds cA V seeds →
              ∀ (AxHolds : Address → Address → Prop)
                (EvalHolds : Address → EvalAssumption → Prop)
                (Ax : Address → Prop) (x : Address),
                ConditionalChecked AxHolds EvalHolds
                  (fun b _ => ComposedModelConclusion.{u} callsA callsB bytesA bytesB V b seeds)
                  a Ax (fun _ => False) x

/-- **Proof of the abstract lifting wrapper `CircuitComposedLiftToConditionalAxioms`** on
`[propext, Classical.choice, Quot.sound]`, obtained by monotonic weakening from `circuitComposed`. -/
theorem circuitComposedLiftToConditionalAxioms : CircuitComposedLiftToConditionalAxioms.{u} := by
  refine circuitSound_mono (fun callsB dB hA => ?_) circuitComposed.{u}
  refine circuitSound_mono (fun callsA dA hSpec => ?_) hA
  intro bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hseeds
    AxHolds EvalHolds Ax x
  have hBase : ConditionalChecked AxHolds EvalHolds
      (fun b _ => ComposedModelConclusion.{u} callsA callsB bytesA bytesB V b seeds)
      a (fun _ => False) (fun _ => False) x :=
    fun _ _ => composedModelConclusion_of_composedSpec hSpec deB dgB deA dgA hsc hctx hba hseeds
  exact conditionalChecked_mono_ax (fun _ h => h.elim) hBase

/-- Specializing `circuitComposedLiftToConditionalAxioms` at `Ax = ∅` recovers `SeedsNotFalse`
via `conditionalChecked_unconditional` and `composedModelConclusion_no_false`. -/
theorem circuitComposedLiftToConditionalAxioms_no_False (W : Type u) [SetTheory W] :
    CircuitSound fun callsB dB =>
      CircuitSound fun callsA dA =>
        ∀ (bytesB : ByteArray) (spec a : Address), Claim.de bytesB = .ok (.binding spec a) →
          packDigest (Address.blake3Pure bytesB) = dB →
          ∀ (bytesA : ByteArray) (cA : Claim), Claim.de bytesA = .ok cA →
            packDigest (Address.blake3Pure bytesA) = dA → InScopeTyping cA →
            ∀ ctx, cA.context? = some ctx → ctx.binding = a →
              ∀ (V : View) (seeds : List Address), ClaimSeeds cA V seeds →
                V.HashedCollision (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
                  ComposedWith.{u} (fun t R _ => SeedsNotFalse callsA t R seeds) callsB a := by
  refine circuitSound_mono (fun callsB dB hA => ?_) circuitComposedLiftToConditionalAxioms.{u}
  refine circuitSound_mono (fun callsA dA hSpec => ?_) hA
  intro bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hseeds
  have hCond := hSpec bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hseeds
    (fun _ _ => True) (fun _ _ => True) (fun _ => False) a
  exact composedModelConclusion_no_false W (conditionalChecked_unconditional hCond)

/-- Specializing `circuitComposedLiftToConditionalAxioms` at `Ax = ∅` recovers `SeedsInhabited`
via `conditionalChecked_unconditional` and `composedModelConclusion_seeds_inhabited`. -/
theorem circuitComposedLiftToConditionalAxioms_seeds_inhabited :
    CircuitSound fun callsB dB =>
      CircuitSound fun callsA dA =>
        ∀ (bytesB : ByteArray) (spec a : Address), Claim.de bytesB = .ok (.binding spec a) →
          packDigest (Address.blake3Pure bytesB) = dB →
          ∀ (bytesA : ByteArray) (cA : Claim), Claim.de bytesA = .ok cA →
            packDigest (Address.blake3Pure bytesA) = dA → InScopeTyping cA →
            ∀ ctx, cA.context? = some ctx → ctx.binding = a →
              ∀ (V : View) (seeds : List Address), ClaimSeeds cA V seeds →
                V.HashedCollision (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
                  ComposedWith.{u} (fun t R _ => SeedsInhabited.{u} callsA t R seeds) callsB a := by
  refine circuitSound_mono (fun callsB dB hA => ?_) circuitComposedLiftToConditionalAxioms.{u}
  refine circuitSound_mono (fun callsA dA hSpec => ?_) hA
  intro bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hseeds
  have hCond := hSpec bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hseeds
    (fun _ _ => True) (fun _ _ => True) (fun _ => False) a
  exact composedModelConclusion_seeds_inhabited (conditionalChecked_unconditional hCond)

/-- **Abstract lifting wrapper (`CircuitComposedLiftToConditionalEvals`)**:
monotonically lifts the frozen `InScopeTyping` `circuitComposed` conclusion into
`Ix.DynamicLink.ConditionalOnEvals`. This is an abstract weakening wrapper — it does not prove
circuit-level soundness of `verify_claim` for validators `10`/`11` with non-empty
`evalAssumptions`. -/
def CircuitComposedLiftToConditionalEvals : Prop :=
  CircuitSound fun callsB dB =>
    CircuitSound fun callsA dA =>
      ∀ (bytesB : ByteArray) (spec a : Address), Claim.de bytesB = .ok (.binding spec a) →
        packDigest (Address.blake3Pure bytesB) = dB →
        ∀ (bytesA : ByteArray) (cA : Claim), Claim.de bytesA = .ok cA →
          packDigest (Address.blake3Pure bytesA) = dA → InScopeTyping cA →
          ∀ ctx, cA.context? = some ctx → ctx.binding = a →
            ∀ (V : View) (seeds : List Address), ClaimSeeds cA V seeds →
              ∀ (Valid : EvalAssumption → Prop) (evalAsms : List EvalAssumption),
                ConditionalOnEvals Valid evalAsms
                  (ComposedModelConclusion.{u} callsA callsB bytesA bytesB V a seeds) ∧
                ((∀ e ∈ evalAsms, Valid e) →
                  ComposedModelConclusion.{u} callsA callsB bytesA bytesB V a seeds)

/-- **Proof of the abstract lifting wrapper `CircuitComposedLiftToConditionalEvals`** on
`[propext, Classical.choice, Quot.sound]`, obtained by monotonic weakening from `circuitComposed`. -/
theorem circuitComposedLiftToConditionalEvals : CircuitComposedLiftToConditionalEvals.{u} := by
  refine circuitSound_mono (fun callsB dB hA => ?_) circuitComposed.{u}
  refine circuitSound_mono (fun callsA dA hSpec => ?_) hA
  intro bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hseeds Valid evalAsms
  have hConc : ComposedModelConclusion.{u} callsA callsB bytesA bytesB V a seeds :=
    composedModelConclusion_of_composedSpec hSpec deB dgB deA dgA hsc hctx hba hseeds
  exact ⟨fun _ => hConc, evalDischarge_all_sound (fun _ => hConc)⟩

/-- Abstract discharge step for `ConditionalChecked` targeting `ComposedModelConclusion`:
discharging one `EvalAssumption` leaf `e₀` via `ConditionalEvalValid` removes `e₀` from
`EvalBefore` while preserving `ConditionalChecked`. -/
theorem circuitComposedLiftToConditionalEvals_discharge_step
    {callsA callsB : List (Call IxVM.F)} {bytesA bytesB : ByteArray}
    {V : View} {a x : Address} {seeds : List Address}
    {AxHolds : Address → Address → Prop} {EvalHolds : Address → EvalAssumption → Prop}
    {Ax : Address → Prop} {EvalBefore EvalAfter : EvalAssumption → Prop} {e₀ : EvalAssumption}
    (hRem : _root_.Aggr.EvalRemoveRel EvalBefore EvalAfter e₀)
    (hE : ConditionalEvalValid AxHolds EvalHolds a Ax e₀)
    (hC : ConditionalChecked AxHolds EvalHolds
      (fun b _ => ComposedModelConclusion.{u} callsA callsB bytesA bytesB V b seeds)
      a Ax EvalBefore x) :
    ConditionalChecked AxHolds EvalHolds
      (fun b _ => ComposedModelConclusion.{u} callsA callsB bytesA bytesB V b seeds)
      a Ax EvalAfter x :=
  conditionalChecked_discharge_eval hRem hE hC

/-! ## 4. Kernel-Axiom Guards -/

open Lean Elab Command in
run_cmd do
  let roots : List Name := [
    ``IxVM.Refinement.Endpoint.role_ctx_without_axioms_strips,
    ``IxVM.Refinement.Endpoint.role_ctx_without_axioms_preserves_rc,
    ``IxVM.Refinement.Endpoint.check_witness_kind2_strips_axioms,
    ``IxVM.Refinement.Endpoint.assert_not_axiom_spec_sound,
    ``IxVM.Refinement.Endpoint.validate_user_axioms_sound,
    ``IxVM.Refinement.Endpoint.get_u64_le_stream,
    ``IxVM.Refinement.Endpoint.skip_opt_circuit_ref_stream,
    ``IxVM.Refinement.Endpoint.assert_eval_endpoint_sound,
    ``IxVM.Refinement.Endpoint.assert_eval_type_sound,
    ``IxVM.Refinement.Endpoint.load_eval_assumption_spec,
    ``IxVM.Refinement.Endpoint.eval_map_lookup_sound,
    ``IxVM.Refinement.Endpoint.load_eval_assumptions_sound,
    ``IxVM.Refinement.Endpoint.load_role_ctx_eval_nonempty_and_validated,
    ``IxVM.Refinement.Endpoint.try_eval_assumption_sound,
    ``IxVM.Refinement.Endpoint.run_check_claim_eval_wire,
    ``IxVM.Refinement.Endpoint.run_check_env_claim_eval_wire,
    ``IxVM.Refinement.Endpoint.circuitComposedLiftToConditionalAxioms,
    ``IxVM.Refinement.Endpoint.circuitComposedLiftToConditionalAxioms_no_False,
    ``IxVM.Refinement.Endpoint.circuitComposedLiftToConditionalAxioms_seeds_inhabited,
    ``IxVM.Refinement.Endpoint.circuitComposedLiftToConditionalEvals,
    ``IxVM.Refinement.Endpoint.circuitComposedLiftToConditionalEvals_discharge_step
  ]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for r in roots do
    let axs ← Lean.collectAxioms r
    for a in axs do
      unless allowed.contains a do
        throwError "unexpected axiom {a} in {r} (axioms: {axs.toList})"
  -- Also run the direct kernel-environment audit (`Ix.Kernel.Audit.axiomsOf`) once with a
  -- single shared cache across all 20 roots.
  let env ← getEnv
  let kernelAxs := Ix.Kernel.Audit.axiomsOf env roots.toArray
  for a in kernelAxs do
    unless allowed.contains a do
      throwError "unexpected kernel-closure axiom {a} across companion roots"

end IxVM.Refinement.Endpoint
