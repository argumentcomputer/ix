import IxVMRefinement.Ingress.AnnotationTrace
import IxCK.Kernel.Model.GuardClassifierErase

/-! # Raw binder annotation preserves the metadata-erased serialized expression

Unlike semantic annotation, raw annotation keeps let cells. Erasing the annotated metadata
therefore recovers the original reader syntax with exactly its metadata erased.
-/

namespace IxVM.Refinement.Ingress

open Ix.Kernel (Expr)

/-- A successful raw binder annotation changes only metadata, including under retained lets. -/
theorem applyRawBinderTrace_eraseMeta {metadata : Core.KLevel → Ix.Kernel.BinderMeta} :
    ∀ (e : Core.KExpr) {levels : List Core.KLevel} {raw : Core.KExpr} {rest : List Core.KLevel},
      applyRawBinderTrace metadata e levels = some (raw, rest) → raw.eraseMeta = e.eraseMeta := by
  intro e
  induction e with
  | bvar | sort | const | lit =>
    intro levels raw rest observed
    simp only [applyRawBinderTrace, Option.some.injEq, Prod.mk.injEq] at observed
    obtain ⟨rfl, rfl⟩ := observed
    rfl
  | fvar i type ih =>
    intro levels raw rest observed
    simp only [applyRawBinderTrace] at observed
    obtain ⟨⟨type', remaining⟩, read, result⟩ := Option.bind_eq_some_iff.mp observed
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj result)
    simp only [Expr.eraseMeta, ih read]
  | app func arg ihf iha =>
    intro levels raw rest observed
    simp only [applyRawBinderTrace] at observed
    obtain ⟨⟨func', afterFunc⟩, readFunc, later⟩ := Option.bind_eq_some_iff.mp observed
    obtain ⟨⟨arg', afterArg⟩, readArg, result⟩ := Option.bind_eq_some_iff.mp later
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj result)
    simp only [Expr.eraseMeta, ihf readFunc, iha readArg]
  | lam dom body _ ihd ihb | forallE dom body _ ihd ihb =>
    intro levels raw rest observed
    cases levels with
    | nil => simp [applyRawBinderTrace] at observed
    | cons level remaining =>
      simp only [applyRawBinderTrace] at observed
      obtain ⟨⟨dom', afterDom⟩, readDom, later⟩ := Option.bind_eq_some_iff.mp observed
      obtain ⟨⟨body', afterBody⟩, readBody, result⟩ := Option.bind_eq_some_iff.mp later
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj result)
      simp only [Expr.eraseMeta, ihd readDom, ihb readBody]
  | letE type value body _ iht ihv ihb =>
    intro levels raw rest observed
    simp only [applyRawBinderTrace] at observed
    obtain ⟨⟨type', afterType⟩, readType, second⟩ := Option.bind_eq_some_iff.mp observed
    obtain ⟨⟨value', afterValue⟩, readValue, third⟩ := Option.bind_eq_some_iff.mp second
    obtain ⟨⟨body', afterBody⟩, readBody, result⟩ := Option.bind_eq_some_iff.mp third
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj result)
    simp only [Expr.eraseMeta, iht readType, ihv readValue, ihb readBody]
  | proj name index inner ih =>
    intro levels raw rest observed
    simp only [applyRawBinderTrace] at observed
    obtain ⟨⟨inner', remaining⟩, read, result⟩ := Option.bind_eq_some_iff.mp observed
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj result)
    simp only [Expr.eraseMeta, ih read]

end IxVM.Refinement.Ingress
