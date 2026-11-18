import IxVMRefinement.Assembly.GuardRawInst
import IxVMRefinement.Guard.KeyedLoads
import IxVMRefinement.Core.RawDet

/-! # Actual raw head traces with recorded definition-load origins

These are data traces for the structural normalizer. Delta steps retain the actual get_ci
origin and its physical raw value. A later canonical-origin argument can compare those steps
across runs; this module does not assume that arbitrary loaded raw roots are identical.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open Ix.Kernel (Expr ConstantVal ReducibilityHint BinderMeta)

/-- One delta answer retains its actual observed definition load. Raw keys can be globally
fixed even when the scoped keying that licenses the load changes with the prefix. -/
def RawDeltaAt (c : ScopedCtx) (κ : _root_.Address → KKey) (rootCalls : List (Call F))
    (key : KKey) (parameters : List KLevel) (output : KExpr) : Prop :=
  ∃ (address : Bytes.Address) (cv : ConstantVal .anon) (body raw : KExpr)
    (hint : ReducibilityHint) (ap ptr levels ty value safety hintPtr : SourceValue F)
    (before loaded : Heap F) (loadCalls : List (Call F)),
    key = κ (ixAddr address) ∧
    c.env.find? (c.κ (ixAddr address)) = some (.defnInfo cv body hint) ∧
    parameters.length = cv.levelParams.length ∧
    Bytes.RepAddressRef addrTy before address ap ∧
    ObsFn W "Ingress::get_ci" [ap] before ptr loaded loadCalls ∧
    (⟨"Ingress::get_ci", [ap], before⟩ : Call F) ∈ rootCalls ∧
    loadValue loaded ptr = .ok (.construct kciEnum "Defn" [levels, ty, value, safety, hintPtr]) ∧
    RawExprRep κ loaded 0 raw value ∧
    (∀ call ∈ loadCalls, call ∈ rootCalls) ∧
    output = raw.instantiateLevelParams (List.range parameters.length) parameters ∧
    levels = .field (parameters.length : F) ∧ parameters.length < 549755813888

/-- Deterministic head strategy over raw syntax, with explicit delta evidence. No constructor
asserts a Rules.Red judgement; beta and zeta are capture-avoiding data substitutions. -/
inductive RawHeadTrace (delta : KKey → List KLevel → KExpr → Prop) : KExpr → KExpr → Prop
  | sort (level : KLevel) : RawHeadTrace delta (.sort level) (.sort level)
  | forallE (dom body : KExpr) (binderData : BinderMeta) :
      RawHeadTrace delta (.forallE dom body binderData) (.forallE dom body binderData)
  | lam (dom body : KExpr) (binderData : BinderMeta) :
      RawHeadTrace delta (.lam dom body binderData) (.lam dom body binderData)
  | const {key : KKey} {parameters : List KLevel} {value result : KExpr} :
      delta key parameters value → RawHeadTrace delta value result →
      RawHeadTrace delta (.const key parameters) result
  | app {func arg dom body result : KExpr} {binderData : BinderMeta} :
      RawHeadTrace delta func (.lam dom body binderData) →
      RawHeadTrace delta (body.instantiate1Lift arg) result →
      RawHeadTrace delta (.app func arg) result
  | letE {ty value body result : KExpr} {binderData : Ix.Kernel.LetMeta} :
      RawHeadTrace delta (body.instantiate1Lift value) result →
      RawHeadTrace delta (.letE ty value body binderData) result

/-- Any produced interpretation of the actual delta origins transports the complete trace. -/
theorem RawHeadTrace.map {delta other : KKey → List KLevel → KExpr → Prop}
    (preserves : ∀ key parameters value, delta key parameters value → other key parameters value)
    {input result : KExpr} (trace : RawHeadTrace delta input result) :
    RawHeadTrace other input result := by
  induction trace with
  | sort level => exact .sort level
  | forallE dom body binderData => exact .forallE dom body binderData
  | lam dom body binderData => exact .lam dom body binderData
  | const loaded child ih => exact .const (preserves _ _ _ loaded) ih
  | app func body ihf ihb => exact .app ihf ihb
  | letE body ih => exact .letE ih

/-- Successful traces agree once their actual delta answers have been identified. This
hypothesis is an explicit remaining canonical-origin obligation, not registry closure. -/
theorem RawHeadTrace.unique {delta other : KKey → List KLevel → KExpr → Prop}
    (answers : ∀ key parameters first second,
      delta key parameters first → other key parameters second → first = second)
    {input first second : KExpr} (left : RawHeadTrace delta input first)
    (right : RawHeadTrace other input second) : first = second := by
  induction left generalizing second with
  | sort level => cases right; rfl
  | forallE dom body binderData => cases right; rfl
  | lam dom body binderData => cases right; rfl
  | const loaded child ih =>
    cases right with
    | const loaded' child' =>
      have same := answers _ _ _ _ loaded loaded'
      subst same
      exact ih child'
  | app func body ihf ihb =>
    cases right with
    | app func' body' =>
      obtain ⟨rfl, rfl, rfl⟩ := Expr.lam.inj (ihf func')
      exact ihb body'
  | letE body ih => cases right with | letE body' => exact ih body'

end IxVM.Refinement.Decl

namespace IxVM.Refinement.Core.GuardData

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Decl (RawExprRep RawDeltaAt RawHeadTrace)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem head_raw_go (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    {c : ScopedCtx} (facts : ScopedCoreFacts c) (rootCalls : List (Call F)) :
    ∀ fuel : Nat, ∀ {d k : Nat} {Γ : Nat → KExpr} {R E : KExpr}
      {p budget r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ fuel → CoreGood c calls → (∀ call ∈ calls, call ∈ rootCalls) →
      Tm c.κ d Γ h 0 E p → RawExprRep rawKey h k R p →
      ObsFn W "KernelGuard::head" [p, budget] h r h' calls →
      ∃ bound result, RawExprRep rawKey h' bound result r ∧
        RawHeadTrace (RawDeltaAt c rawKey rootCalls) R result := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro d k Γ R E p budget r h h' calls length good subset scopedRep physical observed
    obtain ⟨semantic, raw⟩ := physical
    match Obs.«KernelGuard::head».obs observed with
    | .n0 (heq40 := impossible) .. | .other_other (heq453 := impossible) .. =>
      exact (zero_ne_one (Value.field.inj impossible)).elim
    | .other_Srt (ld60 := loaded) (he75 := result) (he76 := heap) .. =>
      obtain ⟨level, rfl, rfl, _⟩ := raw.raw_sort_view loaded
      subst result heap
      exact ⟨k, .sort level, ⟨_, raw⟩, .sort level⟩
    | .other_Forall (ld60 := loaded) (he104 := result) (he105 := heap) .. =>
      obtain ⟨RD, RB, D, B, level, rfl, rfl, _, _, _⟩ := raw.raw_forallE_view loaded
      subst result heap
      exact ⟨k, .forallE RD RB (bmeta level), ⟨_, raw⟩, .forallE RD RB (bmeta level)⟩
    | .other_Lam (ld60 := loaded) (he133 := result) (he134 := heap) .. =>
      obtain ⟨RD, RB, D, B, level, rfl, rfl, _, _, _⟩ := raw.raw_lam_view loaded
      subst result heap
      exact ⟨k, .lam RD RB (bmeta level), ⟨_, raw⟩, .lam RD RB (bmeta level)⟩
    | .other_Const (cs156 := children) (cs170 := loadBranch) (ld60 := loaded)
        (ev172 := valueCall) (ev158 := child) (hc204 := events) .. =>
      obtain ⟨address, parameters, rfl, rfl, addressRep, paramsRep⟩ := raw.raw_const_view loaded
      obtain ⟨scopedAddress, _, rfl, scopedAddressRep, _, _, _⟩ := scopedRep.const_of_load loaded
      have same := addr_det addressRep scopedAddressRep
      subst scopedAddress
      have loadInside : ∀ call ∈ loadBranch, call ∈ calls := by
        intro call member; rw [events]; simp [member]
      have childInside : ∀ call ∈ children, call ∈ calls := by
        intro call member; rw [events]; simp [member]
      obtain ⟨cv, value, origin, hint, ptr, nl, ty, valuePtr, safety, hintPtr, loadedHeap,
        beforeInst, loadCalls, instCalls, found, arity, load, member, node, rawOrigin, extension,
        inst, loadSubset, _, valueRep, countEq, countBound⟩ :=
          definition_value_keyed_raw_origin rawKey facts
          (good.sub loadInside) addressRep scopedRep.const_key_ne paramsRep valueCall
      obtain ⟨valueSemantic, valueScoped⟩ := definition_value_rep (d := d) (Γ := Γ) facts (good.sub loadInside)
        addressRep scopedRep.const_key_ne paramsRep valueCall
      have shorter : children.length < fuel := by
        rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
      obtain ⟨bound, result, resultRep, resultTrace⟩ := ih children.length shorter (Nat.le_refl _)
        (good.sub childInside) (fun call inside => subset call (childInside call inside))
        valueScoped valueRep child
      have delta : RawDeltaAt c rawKey rootCalls (rawKey (ixAddr address)) parameters
          (origin.instantiateLevelParams (List.range parameters.length) parameters) := by
        exact ⟨address, cv, value, origin, hint, _, ptr, nl, ty, valuePtr, safety, hintPtr,
          h, loadedHeap, loadCalls, rfl, found, arity, addressRep, load,
          subset _ (loadInside _ member), node, rawOrigin,
          fun call inside => subset call (loadInside call (loadSubset call inside)), rfl,
          countEq, countBound⟩
      exact ⟨bound, result, resultRep, .const delta resultTrace⟩
    | .other_App (cs236 := first) (cs300 := instCalls) (cs286 := children)
        (ld60 := loaded) (ev238 := functionCall) (ld232 := lambda) (ev302 := inst)
        (ev288 := child) (hc341 := events) .. =>
      obtain ⟨RF, RA, EF, EA, rfl, rfl, rawFunc, rawArg⟩ := raw.raw_app_view loaded
      obtain ⟨functionTerm, argumentTerm, rfl, scopedFunc, scopedArg⟩ := scopedRep.app_of_load loaded
      have firstInside : ∀ call ∈ first, call ∈ calls := by intro call member; rw [events]; simp [member]
      have instInside : ∀ call ∈ instCalls, call ∈ calls := by intro call member; rw [events]; simp [member]
      have childInside : ∀ call ∈ children, call ∈ calls := by intro call member; rw [events]; simp [member]
      have shorter1 : first.length < fuel := by
        rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
      have shorter2 : children.length < fuel := by
        rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
      obtain ⟨functionBound, functionRaw, functionRep, functionTrace⟩ :=
        ih first.length shorter1 (Nat.le_refl _) (good.sub firstInside)
          (fun call inside => subset call (firstInside call inside)) scopedFunc ⟨_, rawFunc⟩ functionCall
      obtain ⟨functionSemantic, functionScoped, _⟩ := head_rep facts (good.sub firstInside) scopedFunc functionCall
      obtain ⟨D, B, _, rfl, _, bodyScoped, _⟩ := functionScoped.lam_of_load lambda
      let common := max k functionBound
      obtain ⟨functionImage, functionExact⟩ := functionRep.weaken (show functionBound ≤ common from Nat.le_max_right _ _)
      obtain ⟨RD, RB, ED, EB, level, rfl, rfl, _, bodyExact, _⟩ := functionExact.raw_lam_view lambda
      have argRep : RawExprRep rawKey _ common RA _ :=
        (show RawExprRep rawKey h k RA _ from ⟨_, rawArg⟩).mono functionCall.heap_extends |>.weaken (Nat.le_max_left _ _)
      have rawBeta := RawExprRep.inst1
        (by simpa only [ZMod.val_zero, Nat.add_zero] using
          (show RawExprRep rawKey _ (common + 1) RB _ from ⟨_, bodyExact⟩))
        argRep (bounded_sub instInside good.2) inst
      simp only [ZMod.val_zero, Nat.add_zero] at rawBeta
      have semanticBeta := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ inst _ _ (0 : F) rfl
        (bounded_sub instInside good.2) d Γ B argumentTerm
        (by simpa only [ZMod.val_zero, Nat.zero_add] using bodyScoped)
        (scopedArg.mono functionCall.heap_extends)
      simp only [ZMod.val_zero] at semanticBeta
      obtain ⟨bound, result, resultRep, resultTrace⟩ := ih children.length shorter2 (Nat.le_refl _)
        (good.sub childInside) (fun call inside => subset call (childInside call inside))
        semanticBeta rawBeta child
      exact ⟨bound, result, resultRep, .app functionTrace resultTrace⟩
    | .other_Let (cs382 := instCalls) (cs368 := children) (ld60 := loaded)
        (ev384 := inst) (ev370 := child) (hc423 := events) .. =>
      obtain ⟨RT, RV, RB, ET, EV, EB, rfl, rfl, _, rawValue, rawBody⟩ := raw.raw_let_view loaded
      obtain ⟨T, V, B, rfl, _, valueScoped, bodyScoped⟩ := scopedRep.letE_of_load loaded
      have instInside : ∀ call ∈ instCalls, call ∈ calls := by intro call member; rw [events]; simp [member]
      have childInside : ∀ call ∈ children, call ∈ calls := by intro call member; rw [events]; simp [member]
      have shorter : children.length < fuel := by
        rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
      have rawBeta := RawExprRep.inst1
        (by simpa only [ZMod.val_zero, Nat.add_zero] using
          (show RawExprRep rawKey h (k + 1) RB _ from ⟨_, rawBody⟩))
        (show RawExprRep rawKey h k RV _ from ⟨_, rawValue⟩)
        (bounded_sub instInside good.2) inst
      simp only [ZMod.val_zero, Nat.add_zero] at rawBeta
      have semanticBeta := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ inst _ _ (0 : F) rfl
        (bounded_sub instInside good.2) d Γ B V
        (by simpa only [ZMod.val_zero, Nat.zero_add] using bodyScoped) valueScoped
      simp only [ZMod.val_zero] at semanticBeta
      obtain ⟨bound, result, resultRep, resultTrace⟩ := ih children.length shorter (Nat.le_refl _)
        (good.sub childInside) (fun call inside => subset call (childInside call inside))
        semanticBeta rawBeta child
      exact ⟨bound, result, resultRep, .letE resultTrace⟩

/-- The actual normalizer produces a raw trace whose delta steps contain their actual
scoped-licensed definition loads. No common-lookup or prefix-equality premise is assumed. -/
theorem head_raw_trace (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    {c : ScopedCtx} (facts : ScopedCoreFacts c) {rootCalls : List (Call F)}
    {d k : Nat} {Γ : Nat → KExpr} {R E : KExpr}
    {p budget r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (good : CoreGood c calls) (subset : ∀ call ∈ calls, call ∈ rootCalls)
    (scopedRep : Tm c.κ d Γ h 0 E p) (physical : RawExprRep rawKey h k R p)
    (observed : ObsFn W "KernelGuard::head" [p, budget] h r h' calls) :
    ∃ bound result, RawExprRep rawKey h' bound result r ∧
      RawHeadTrace (RawDeltaAt c rawKey rootCalls) R result :=
  head_raw_go rawKey facts rootCalls calls.length (Nat.le_refl _) good subset scopedRep physical observed

end IxVM.Refinement.Core.GuardData
