import IxVMRefinement.Decl.ReferenceChecks
import IxVMRefinement.Decl.ReferenceScope

/-! # Paired source and annotated reference prefixes

The replay records the source checker call and its annotated target step together. This
retains the exact original checking prefix needed to derive name scopes and later-unit
noninterference, while projecting to the existing checked and storage traces.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics

/-- The actual source fold and its checked annotated replay, with agreement at every prefix. -/
inductive ReferenceReplay (fuel : Nat) (ev : Evidences .anon) :
    Env .anon → Env .anon → List (Declaration .anon) → Env .anon → Env .anon → Prop
  | nil {source target} (agreement : ThmBodyView.Agrees source target) :
      ReferenceReplay fuel ev source target [] source target
  | cons {source target sourceNext targetNext sourceOut targetOut d ds}
      (agreement : ThmBodyView.Agrees source target)
      (sourceCheck : checkDecl .verified (fueledOps .verified fuel) ev source d = .ok sourceNext)
      (targetCheck : CheckedReferenceStep fuel target d targetNext)
      (tail : ReferenceReplay fuel ev sourceNext targetNext ds sourceOut targetOut) :
      ReferenceReplay fuel ev source target (d :: ds) sourceOut targetOut

theorem ReferenceReplay.startAgreement {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut targetOut : Env .anon} {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev source target ds sourceOut targetOut) :
    ThmBodyView.Agrees source target := by
  cases replay with
  | nil agreement => exact agreement
  | cons agreement _ _ _ => exact agreement

theorem ReferenceReplay.endAgreement {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut targetOut : Env .anon} {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev source target ds sourceOut targetOut) :
    ThmBodyView.Agrees sourceOut targetOut := by
  induction replay with
  | nil agreement => exact agreement
  | cons _ _ _ _ ih => exact ih

theorem ReferenceReplay.sourceRun {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut targetOut : Env .anon} {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev source target ds sourceOut targetOut) :
    ds.foldlM (checkDecl .verified (fueledOps .verified fuel) ev) source = .ok sourceOut := by
  induction replay with
  | nil => rfl
  | cons _ checked _ _ ih =>
    simpa only [List.foldlM_cons, checked, Bind.bind, Except.bind] using ih

theorem ReferenceReplay.checked {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut targetOut : Env .anon} {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev source target ds sourceOut targetOut) :
    CheckedReferenceTrace fuel target ds targetOut := by
  induction replay with
  | nil => exact .nil _
  | cons _ _ step _ ih => exact .cons step ih

/-- Source name bounds transfer to the actual annotated endpoint. -/
theorem ReferenceReplay.findOver {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut targetOut : Env .anon} {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev source target ds sourceOut targetOut)
    {known : List (Key .anon)} (confined : FindOver known source) :
    FindOver (known ++ ds.flatMap Declaration.names) targetOut :=
  replay.endAgreement.findOver (checkedDecls_findOver .verified fuel ev ds known confined replay.sourceRun)

/-- The accepted replay from the empty environment has exactly the declared base scope. -/
theorem ReferenceReplay.declaredScope {fuel : Nat} {ev : Evidences .anon}
    {target sourceOut targetOut : Env .anon} {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev Env.empty target ds sourceOut targetOut) :
    FindOver (ds.flatMap Declaration.names) targetOut := by
  have empty : FindOver [] (Env.empty : Env .anon) := by
    intro name ci found
    simp [Env.find?, Env.empty] at found
  simpa only [List.nil_append] using replay.findOver empty

/-- Locate both actual checking prefixes at a declaration in the accepted order. -/
theorem ReferenceReplay.declarationStep {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut targetOut : Env .anon} {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev source target ds sourceOut targetOut)
    {d : Declaration .anon} (member : d ∈ ds) :
    ∃ before after sourceBefore targetBefore sourceAfter targetAfter,
      ds = before ++ d :: after ∧
      ReferenceReplay fuel ev source target before sourceBefore targetBefore ∧
      checkDecl .verified (fueledOps .verified fuel) ev sourceBefore d = .ok sourceAfter ∧
      CheckedReferenceStep fuel targetBefore d targetAfter ∧
      ReferenceReplay fuel ev sourceAfter targetAfter after sourceOut targetOut := by
  induction replay with
  | nil => cases member
  | @cons source target sourceNext targetNext sourceOut targetOut head rest agreement sourceCheck targetCheck tail ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨[], rest, source, target, sourceNext, targetNext, rfl,
        .nil agreement, sourceCheck, targetCheck, tail⟩
    · obtain ⟨before, after, sourceBefore, targetBefore, sourceAfter, targetAfter,
        split, prefixRun, selectedSource, selectedTarget, suffixRun⟩ := ih later
      refine ⟨head :: before, after, sourceBefore, targetBefore, sourceAfter, targetAfter,
        ?_, .cons agreement sourceCheck targetCheck prefixRun, selectedSource, selectedTarget, suffixRun⟩
      rw [split]
      rfl

end IxVM.Refinement.Decl
