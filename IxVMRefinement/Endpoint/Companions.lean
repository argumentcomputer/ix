import IxVMRefinement.Endpoint.ConsistencyCorollary
import IxVMRefinement.Core.Steps.Whnf
import IxVMRefinement.Decl.ModeledRules
import IxVMRefinement.Lib.Bytes
import IxVMRefinement.Obs.KernelRoles
import IxVMRefinement.Obs.KernelWhnf1
import IxVMRefinement.Obs.KernelClaim4
import IxVMRefinement.Obs.IxonDeserialize0
import IxVMRefinement.Obs.UInt80
import Ix.Cert.Aggr.ConditionalShard
import Ix.DynamicLink.Soundness
import IxC.Kernel.Audit.Axioms

/-! # Companion Consistency Theorems: User Axioms (`A6`) and Dynamic-Link `EvalAssumption`s

This module adds companion circuit-level soundness theorems alongside the frozen
`IxVM.Consistency.CircuitComposed` statement (leaving `Ix/IxVM/ConsistencyAudit.lean`,
`Ix/IxVM/Refinement/Audit.lean`, `IxC/Kernel/Denotes.lean`, and `CircuitComposed` itself
completely untouched):

1. **User-Axiom Validation and `CircuitComposedWithAxioms`:**
   * `role_ctx_without_axioms_strips`: proves that `KernelRoles::role_ctx_without_axioms`
     strips both user axioms and eval assumptions to `Nil` while preserving the table pointer
     and validation limit (allowing non-axiomatic modeled inductive blocks alongside user axioms).
   * `assert_not_axiom_spec_sound` and `validate_user_axioms_sound`: prove from the observed
     `KernelRoles` path lemmas that every accepted user axiom is unbound in the role table,
     stored as a safe `KConstantInfo::Axiom` (`u = 0`), and cannot restate `propext`,
     `Classical.choice`, `sorryAx`, or a bound `Quot.sound`.
   * `CircuitComposedWithAxioms` / `circuitComposedWithAxioms`: lifts `circuitComposed` into
     `Ix.Cert.Aggr.ConditionalChecked`, supporting monotonic user-axiom composition (`A7`) and
     specializing directly to `ConsistentReadOver`, `SeedsNotFalse`, and `SeedsInhabited` when
     the user-axiom set is empty.

2. **Tier-2 Dynamic-Linking `EvalAssumption` Hook and `CircuitComposedWithEvalAssumptions`:**
   * `skip_opt_circuit_ref_stream` and `load_eval_assumption_spec`: prove that every leaf loaded
     by `KernelRoles::load_eval_assumption` is BLAKE3-verified against its leaf address and
     matches `Ix.DynamicLink.deEvalAssumption`'s exact wire format (`0xE8 0x0E`, `(lhs, rhs, typ)`,
     optional `CircuitRef` tag `0` or `1` with 32-byte VK digest + 8-byte entry index, EOF).
   * `eval_map_lookup_sound` and `load_eval_assumptions_sound`: prove lookup soundness on
     `KernelRoles::EvalMap` and Merkle-leaf loading via `load_eval_assumptions`.
   * `try_eval_assumption_sound`: proves that on standard `Mk`/`Assumed` contexts
     `KernelWhnf::try_eval_assumption` is a zero-allocation identity (`(0, head)`), and on
     `MkEval`/`AssumedEval` contexts whose loaded `EvalMap` entries are grounded in `env`
     (`Ix.DynamicLink.GroundedEval`), every fired closed rewrite `(1, Const(rhs, []))` is a
     valid `Ix.Kernel.Rules.Red` step (and lifts across any application spine `mkAppN`).
   * `run_check_claim_eval_wire` and `run_check_env_claim_eval_wire`: verify that validators
     `10`/`11` decode the non-optional `eval_root` after `opt_asm`, strictly disjoint from
     `Ix.Claim.de` / `InScopeTyping`.
   * `CircuitComposedWithEvalAssumptions` / `circuitComposedWithEvalAssumptions`: connects
     `circuitComposed`, `Ix.DynamicLink.EvalAssumedClaim`, `Ix.DynamicLink.GroundedEval`,
     leaf-by-leaf discharge (`evalDischarge_step_sound` / `conditionalChecked_discharge_eval`),
     and unconditional specialization to `ConsistentReadOver`, `SeedsNotFalse`, and
     `SeedsInhabited`.

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

/-! ## 1. User-Axiom Validation (`A6`) and `CircuitComposedWithAxioms` -/

/-- `KernelRoles::role_ctx_without_axioms` allocates no calls and strips both user axioms and
eval assumptions to `Nil`, producing a plain `Mk` or `Assumed` context with the same table
pointer and validation limit. -/
theorem role_ctx_without_axioms_strips {rc r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::role_ctx_without_axioms" [rc] h r h' cs) :
    cs = [] ∧
      ∃ (tbl : SourceValue F) (node : SourceValue F),
        h' = h ++ [node] ∧
        r = .ptr (.enum "KernelRoles::RoleCtxNode") h.length ∧
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
  | .Mk x_tbl x_lim w_ax ld hr hh hcs =>
    refine ⟨hcs, x_tbl, _, hh, hr, ?_, .inl ⟨x_lim, rfl, .inl ⟨w_ax, ld⟩⟩⟩
    rw [hr, hh]
    exact hload_snoc _ (by simp)
  | .Assumed x_tbl w_ax ld hr hh hcs =>
    refine ⟨hcs, x_tbl, _, hh, hr, ?_, .inr ⟨rfl, .inl ⟨w_ax, ld⟩⟩⟩
    rw [hr, hh]
    exact hload_snoc _ (by simp)
  | .MkEval x_tbl x_lim w_ax w_ev ld hr hh hcs =>
    refine ⟨hcs, x_tbl, _, hh, hr, ?_, .inl ⟨x_lim, rfl, .inr ⟨w_ax, w_ev, ld⟩⟩⟩
    rw [hr, hh]
    exact hload_snoc _ (by simp)
  | .AssumedEval x_tbl w_ax w_ev ld hr hh hcs =>
    refine ⟨hcs, x_tbl, _, hh, hr, ?_, .inr ⟨rfl, .inr ⟨w_ax, w_ev, ld⟩⟩⟩
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
  obtain ⟨hcs, x_tbl, node', hh, hr, hld', hcases⟩ := role_ctx_without_axioms_strips ev
  have ext : Heap.Extends h h' := by rw [hh]; exact Heap.Extends.snoc h node'
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

/-- Every accepted derivation of `KernelRoles::assert_not_axiom_spec` returns unit after verifying
that `(x_nl, x_ty)` does not restate `propext`, `Classical.choice`, `sorryAx`, or (when bound in
`x_tbl`) `Quot.sound`. -/
theorem assert_not_axiom_spec_sound {x_tbl x_nl x_ty r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::assert_not_axiom_spec" [x_tbl, x_nl, x_ty] h r h' cs) :
    r = .tuple [] ∧ Heap.Extends h h' ∧
      (∃ v_p m1 m2 cs1 cs2,
        ObsFn W "KernelRoleSpec::role_propext" [] h v_p m1 cs1 ∧
        ObsFn W "KernelRoles::restates_role" [x_tbl, x_nl, x_ty, v_p] m1 (.field 0) m2 cs2) := by
  match Obs.«KernelRoles::assert_not_axiom_spec».obs ev with
  | .n1 (ev62 := ev_p) (ev25 := ev_rp) (heq69 := h0) (he319 := hr) .. =>
    subst h0
    exact ⟨hr, ev.heap_extends, _, _, _, _, _, ev_p, ev_rp⟩
  | .other (ev62 := ev_p) (ev25 := ev_rp) (heq69 := h0) (he328 := hr) .. =>
    subst h0
    exact ⟨hr, ev.heap_extends, _, _, _, _, _, ev_p, ev_rp⟩

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

/-- **Circuit-level companion statement with explicit user axioms (`CircuitComposedWithAxioms`)**:
extends `CircuitComposed` with `Ix.Cert.Aggr.ConditionalChecked` / `ComposedModelConclusion` so
that:
1. every accepted `(binding, InScopeTyping)` pair yields a `ComposedModelConclusion` and lifts
   monotonically (`A7`) to any explicit user-axiom set `Ax : Address → Prop` under
   `ConditionalChecked`;
2. when `Ax = ∅`, `conditionalChecked_unconditional` specializes immediately to unconditional
   `ConsistentReadOver`, `SeedsNotFalse`, and `SeedsInhabited`. -/
def CircuitComposedWithAxioms : Prop :=
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

/-- **Unconditional proof of `CircuitComposedWithAxioms`** on `[propext, Classical.choice, Quot.sound]`. -/
theorem circuitComposedWithAxioms : CircuitComposedWithAxioms.{u} := by
  refine circuitSound_mono (fun callsB dB hA => ?_) circuitComposed.{u}
  refine circuitSound_mono (fun callsA dA hSpec => ?_) hA
  intro bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hseeds
    AxHolds EvalHolds Ax x
  have hBase : ConditionalChecked AxHolds EvalHolds
      (fun b _ => ComposedModelConclusion.{u} callsA callsB bytesA bytesB V b seeds)
      a (fun _ => False) (fun _ => False) x :=
    fun _ _ => composedModelConclusion_of_composedSpec hSpec deB dgB deA dgA hsc hctx hba hseeds
  exact conditionalChecked_mono_ax (fun _ h => h.elim) hBase

/-- Specializing `circuitComposedWithAxioms` at `Ax = ∅` yields `SeedsNotFalse` directly via
`conditionalChecked_unconditional` and `composedModelConclusion_no_false`. -/
theorem circuitComposedWithAxioms_no_False (W : Type u) [SetTheory W] :
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
  refine circuitSound_mono (fun callsB dB hA => ?_) circuitComposedWithAxioms.{u}
  refine circuitSound_mono (fun callsA dA hSpec => ?_) hA
  intro bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hseeds
  have hCond := hSpec bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hseeds
    (fun _ _ => True) (fun _ _ => True) (fun _ => False) a
  exact composedModelConclusion_no_false W (conditionalChecked_unconditional hCond)

/-- Specializing `circuitComposedWithAxioms` at `Ax = ∅` yields `SeedsInhabited` directly via
`conditionalChecked_unconditional` and `composedModelConclusion_seeds_inhabited`. -/
theorem circuitComposedWithAxioms_seeds_inhabited :
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
  refine circuitSound_mono (fun callsB dB hA => ?_) circuitComposedWithAxioms.{u}
  refine circuitSound_mono (fun callsA dA hSpec => ?_) hA
  intro bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hseeds
  have hCond := hSpec bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hseeds
    (fun _ _ => True) (fun _ _ => True) (fun _ => False) a
  exact composedModelConclusion_seeds_inhabited (conditionalChecked_unconditional hCond)

/-! ## 2. Tier-2 Dynamic-Linking `EvalAssumption` Hook (`5B`) & `CircuitComposedWithEvalAssumptions` -/

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

/-- **Wire-format & BLAKE3 soundness of `KernelRoles::load_eval_assumption`:**
every accepted execution on a represented leaf address `leafAddr` hashes a byte array `bytes`
with `Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr leafAddr`, checks header `[0xE8, 0x0E]`
(`Ix.DynamicLink.VARIANT_EVAL_ASSUMPTION = 22`), decodes `(lhs, rhs, typ)` + optional `CircuitRef`
(`0x00` or `0x01 || vk || entry_u64_le`) with exact EOF, and returns represented addresses for
`(lhs, rhs, typ)`. -/
theorem load_eval_assumption_spec {leafAddr : Bytes.Address} {x_leaf x_lhs x_rhs x_typ : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hleaf : Bytes.RepAddressRef addrTy h leafAddr x_leaf)
    (ev : ObsFn W "KernelRoles::load_eval_assumption" [x_leaf] h (.tuple [x_lhs, x_rhs, x_typ]) h' cs) :
    Heap.Extends h h' ∧
      ∃ (bytes : List UInt8) (lhs rhs typ : Bytes.Address) (trailer : List UInt8),
        Hashed cs ⟨bytes.toArray⟩ ∧
        Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr leafAddr ∧
        bytes = (0xE8 : UInt8) :: (0x0E : UInt8) :: (lhs.toList ++ rhs.toList ++ typ.toList ++ trailer) ∧
        (trailer = [0] ∨ ∃ (vk : Bytes.Address) (entryBytes : List UInt8),
          entryBytes.length = 8 ∧ trailer = 1 :: (vk.toList ++ entryBytes)) ∧
        Bytes.RepAddressRef addrTy h' lhs x_lhs ∧
        Bytes.RepAddressRef addrTy h' rhs x_rhs ∧
        Bytes.RepAddressRef addrTy h' typ x_typ := by
  match Obs.«KernelRoles::load_eval_assumption».obs ev with
  | .run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x_l _ _ _ x_r _ _ _ x_t _ _ _ _
      ld_leaf ev_info ev_read ev_b3 ev_rb0 ev_tf0 heq232 ev_rb1 ev_tf1 heq14
      ev_ga1 ev_ga2 ev_ga3 ev_skip ld_eof hr_eq hh_eq hcs =>
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
    have ext_all : Heap.Extends h _ :=
      ext1.trans (ext2.trans (ext_ga1.trans (ext_ga2.trans (ext_ga3.trans ext_skip))))
    refine ⟨ext_all, bytes, lhs, rhs, typ, trailer, hhashed, hdig, ?_, htrailer,
      Bytes.repAddressRef_heapMono₂ addrTy (ext_ga2.trans (ext_ga3.trans ext_skip)) hlhs,
      Bytes.repAddressRef_heapMono₂ addrTy (ext_ga3.trans ext_skip) hrhs,
      Bytes.repAddressRef_heapMono₂ addrTy ext_skip htyp⟩
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
with the exact `0xE8 0x0E` wire format). -/
theorem load_eval_assumptions_sound :
    ∀ {n : Nat} {leafAddrs : List Bytes.Address}
      {accEntries : List (Bytes.Address × Bytes.Address × Bytes.Address)}
      {x_leaves x_acc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ n →
      Aiur.Library.List.RepList Names.«Lists::Node<&[Field; 32]>»
        (Bytes.RepAddressRef addrTy) h leafAddrs x_leaves →
      EvalMapRep h accEntries x_acc →
      ObsFn W "KernelRoles::load_eval_assumptions" [x_leaves, x_acc] h r h' cs →
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
    intro leafAddrs accEntries x_leaves x_acc r h h' cs hlen hlist hacc ev
    match Obs.«KernelRoles::load_eval_assumptions».obs ev with
    | .Nil (ld_bolbylmd := ld) (he_qkvnfwgk := hr) (he_vfgbdbrh := hh) .. =>
      subst hr hh
      exact ⟨Heap.Extends.refl _, [], hacc, fun _ hm => nomatch hm⟩
    | .Cons (hc_gtnunfxa := hcs) .. =>
      rw [hcs] at hlen; simp at hlen
  | succ n ih =>
    intro leafAddrs accEntries x_leaves x_acc r h h' cs hlen hlist hacc ev
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
        obtain ⟨ext1, bytes, lhs, rhs, typ, trailer, hhash1, hdig1, hbytes1, htr1, hlhs1, hrhs1, htyp1⟩ :=
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

/-- Semantic soundness of `KernelWhnf::try_eval_assumption` under grounded `evalAssumptions`:
when `rc` is an `MkEval`/`AssumedEval` context carrying `EvalMapRep h entries evals` in which
every `(lhs, rhs, typ) ∈ entries` satisfies `Ix.DynamicLink.GroundedEval env`, any fired rewrite
`(1, new_head)` on a closed monomorphic constant `(a, [])` produces a represented `Const(rhs, [])`
whose head reduces in `env` at every depth `d` — and lifts across any application spine `As` via
`Core.red_mkAppN`. -/
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
        ∃ (rhs typ : Bytes.Address) (x_rhs x_nil_lvls new_head : SourceValue F),
          r = .tuple [.field 1, new_head] ∧
          (a, rhs, typ) ∈ entries ∧
          loadValue h lvls = .ok (.construct Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" []) ∧
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
  | .other_other (ev_umpbxzha := ev_e) (he_evaoyjxj := hr) (he_xsgwrrwc := hh) .. =>
    obtain ⟨_, hm⟩ := hrc_evals_eq ev_e
    rw [hh, hm]
    exact ⟨Heap.Extends.refl h, .inl hr⟩
  | .other_Nil_other (ev_umpbxzha := ev_e) (ev_mytptnxq := ev_lk) (he_fdgpdxpn := hr) (he_mujwqtud := hh) .. =>
    obtain ⟨hv, hm⟩ := hrc_evals_eq ev_e
    subst hv
    rw [hm] at ev_lk
    obtain ⟨hm_lk, _⟩ := eval_map_lookup_sound hevals ha ev_lk
    rw [hh, hm_lk]
    exact ⟨Heap.Extends.refl h, .inl hr⟩
  | .other_Nil_n1_bind v_ev m1 cs1 m2 cs2 x_rhs m_out m_mid ev_e _ ld_lvls ev_lk hr hm_out hm_mid hh _ =>
    obtain ⟨hv, hm1⟩ := hrc_evals_eq ev_e
    subst hv
    rw [hm1] at ev_lk ld_lvls
    obtain ⟨hm2, hres⟩ := eval_map_lookup_sound hevals ha ev_lk
    rw [hm2] at hm_mid hm_out
    rcases hres with h0 | ⟨rhs, typ, x_rhs', h1, hmem, hrhs⟩
    · simp at h0
    · simp only [Value.tuple.injEq, List.cons.injEq, and_true] at h1
      obtain ⟨_, rfl⟩ := h1
      have ext1 : Heap.Extends h m_mid := by rw [hm_mid]; exact Heap.Extends.snoc h _
      have ext2 : Heap.Extends m_mid h' := by rw [hh, hm_out]; exact Heap.Extends.snoc m_mid _
      have ext_all : Heap.Extends h h' := ext1.trans ext2
      have hld_nil_mid :
          loadValue m_mid (.ptr (.enum Names.«Lists::Node<&KernelTypes::KLevelNode>») h.length) =
            .ok (.construct Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" []) := by
        rw [hm_mid]
        have hty : (Value.construct Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" [] :
            SourceValue F).type = .enum Names.«Lists::Node<&KernelTypes::KLevelNode>» := by
          simp
        rw [← hty]
        exact Ingress.loadValue_snoc h _
      have hld_nil :
          loadValue h' (.ptr (.enum Names.«Lists::Node<&KernelTypes::KLevelNode>») h.length) =
            .ok (.construct Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" []) :=
        Ingress.loadValue_extend ext2 hld_nil_mid
      have hld_head :
          loadValue h' (.ptr (.enum "KernelTypes::KExprNode") m_mid.length) =
            .ok (.construct "KernelTypes::KExprNode" "Const"
              [x_rhs, .ptr (.enum Names.«Lists::Node<&KernelTypes::KLevelNode>») h.length]) := by
        rw [hh, hm_out]
        have hty : (Value.construct "KernelTypes::KExprNode" "Const"
            [x_rhs, .ptr (.enum Names.«Lists::Node<&KernelTypes::KLevelNode>») h.length] :
            SourceValue F).type = .enum "KernelTypes::KExprNode" := by
          simp
        rw [← hty]
        exact Ingress.loadValue_snoc m_mid _
      have hg := hgrounded (a, rhs, typ) hmem
      refine ⟨ext_all, .inr ⟨rhs, typ, x_rhs,
        .ptr (.enum Names.«Lists::Node<&KernelTypes::KLevelNode>») h.length,
        .ptr (.enum "KernelTypes::KExprNode") m_mid.length,
        hr, hmem, ld_lvls, hld_head, hld_nil,
        Bytes.repAddressRef_heapMono₂ addrTy ext_all hrhs,
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

/-- **Circuit-level companion statement with Tier-2 `evalAssumptions`
(`CircuitComposedWithEvalAssumptions`)**:
combines `CircuitSound` (via `circuitComposed`) with `Ix.DynamicLink.EvalAssumedClaim`,
`Ix.DynamicLink.ConditionalOnEvals`, and Shape 18 discharge:
for any accepted `(binding, InScopeTyping)` claim pair obtained after discharging all
`evalAssumptions` leaves (via `Claim.eval`, `Claim.check`, or Shape 17 `DynamicLinkStatement`
reification), the conditional judgment over `evalAsms` discharges to `ComposedModelConclusion`
(`ConsistentReadOver`, `SeedsNotFalse`, and `SeedsInhabited`). -/
def CircuitComposedWithEvalAssumptions : Prop :=
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

/-- **Unconditional proof of `CircuitComposedWithEvalAssumptions`** on
`[propext, Classical.choice, Quot.sound]`. -/
theorem circuitComposedWithEvalAssumptions : CircuitComposedWithEvalAssumptions.{u} := by
  refine circuitSound_mono (fun callsB dB hA => ?_) circuitComposed.{u}
  refine circuitSound_mono (fun callsA dA hSpec => ?_) hA
  intro bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hseeds Valid evalAsms
  have hConc : ComposedModelConclusion.{u} callsA callsB bytesA bytesB V a seeds :=
    composedModelConclusion_of_composedSpec hSpec deB dgB deA dgA hsc hctx hba hseeds
  exact ⟨fun _ => hConc, evalDischarge_all_sound (fun _ => hConc)⟩

/-- Discharge step at the circuit level: discharging one grounded `EvalAssumption` leaf `e₀`
(whether by `evalLeafSound_of_eqProof`, `evalLeafSound_of_closedDefEq`, or Shape 17
`evalLeafSound_of_dynamicLink`) removes `e₀` from `EvalBefore` while preserving
`ConditionalChecked` toward `ComposedModelConclusion`. -/
theorem circuitComposedWithEvalAssumptions_discharge_step
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

/-! ## 3. Kernel-Axiom Guards -/

open Lean Elab Command in
run_cmd do
  let roots : List Name := [
    ``IxVM.Refinement.Endpoint.role_ctx_without_axioms_strips,
    ``IxVM.Refinement.Endpoint.role_ctx_without_axioms_preserves_rc,
    ``IxVM.Refinement.Endpoint.assert_not_axiom_spec_sound,
    ``IxVM.Refinement.Endpoint.validate_user_axioms_sound,
    ``IxVM.Refinement.Endpoint.circuitComposedWithAxioms,
    ``IxVM.Refinement.Endpoint.circuitComposedWithAxioms_no_False,
    ``IxVM.Refinement.Endpoint.circuitComposedWithAxioms_seeds_inhabited,
    ``IxVM.Refinement.Endpoint.get_u64_le_stream,
    ``IxVM.Refinement.Endpoint.skip_opt_circuit_ref_stream,
    ``IxVM.Refinement.Endpoint.load_eval_assumption_spec,
    ``IxVM.Refinement.Endpoint.eval_map_lookup_sound,
    ``IxVM.Refinement.Endpoint.load_eval_assumptions_sound,
    ``IxVM.Refinement.Endpoint.try_eval_assumption_sound,
    ``IxVM.Refinement.Endpoint.run_check_claim_eval_wire,
    ``IxVM.Refinement.Endpoint.run_check_env_claim_eval_wire,
    ``IxVM.Refinement.Endpoint.circuitComposedWithEvalAssumptions,
    ``IxVM.Refinement.Endpoint.circuitComposedWithEvalAssumptions_discharge_step
  ]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for r in roots do
    let axs ← Lean.collectAxioms r
    for a in axs do
      unless allowed.contains a do
        throwError "unexpected axiom {a} in {r} (axioms: {axs.toList})"
  -- Also run the direct kernel-environment audit (`Ix.Kernel.Audit.axiomsOf`) once with a
  -- single shared cache across all 17 roots.
  let env ← getEnv
  let kernelAxs := Ix.Kernel.Audit.axiomsOf env roots.toArray
  for a in kernelAxs do
    unless allowed.contains a do
      throwError "unexpected kernel-closure axiom {a} across companion roots"

end IxVM.Refinement.Endpoint
