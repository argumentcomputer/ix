import IxVMRefinement.Assembly.GuardRawInst
import IxVMRefinement.Guard.Loads
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
    output = raw.instantiateLevelParams (List.range parameters.length) parameters

/-- Deterministic head strategy over raw syntax, with explicit delta evidence. No constructor
asserts a Rules.Red judgement; beta and zeta are capture-avoiding data substitutions. -/
inductive RawHeadTrace (delta : KKey → List KLevel → KExpr → Prop) : KExpr → KExpr → Prop
  | sort (level : KLevel) : RawHeadTrace delta (.sort level) (.sort level)
  | forallE (dom body : KExpr) (meta : BinderMeta) :
      RawHeadTrace delta (.forallE dom body meta) (.forallE dom body meta)
  | lam (dom body : KExpr) (meta : BinderMeta) :
      RawHeadTrace delta (.lam dom body meta) (.lam dom body meta)
  | const {key : KKey} {parameters : List KLevel} {value result : KExpr} :
      delta key parameters value → RawHeadTrace delta value result →
      RawHeadTrace delta (.const key parameters) result
  | app {func arg dom body result : KExpr} {meta : BinderMeta} :
      RawHeadTrace delta func (.lam dom body meta) →
      RawHeadTrace delta (body.instantiate1Lift arg) result →
      RawHeadTrace delta (.app func arg) result
  | letE {ty value body result : KExpr} {meta : Ix.Kernel.LetMeta} :
      RawHeadTrace delta (body.instantiate1Lift value) result →
      RawHeadTrace delta (.letE ty value body meta) result

/-- Any produced interpretation of the actual delta origins transports the complete trace. -/
theorem RawHeadTrace.map {delta other : KKey → List KLevel → KExpr → Prop}
    (preserves : ∀ key parameters value, delta key parameters value → other key parameters value)
    {input result : KExpr} (trace : RawHeadTrace delta input result) :
    RawHeadTrace other input result := by
  induction trace with
  | sort level => exact .sort level
  | forallE dom body meta => exact .forallE dom body meta
  | lam dom body meta => exact .lam dom body meta
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
  | forallE dom body meta => cases right; rfl
  | lam dom body meta => cases right; rfl
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
