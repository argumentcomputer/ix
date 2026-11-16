import IxVMRefinement.Decl.TheoremAllowedKey

/-! # Frames at a supplied actual checking prefix -/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

universe u

/-- An earlier accepted definition would already occupy a freshly checked definition's name. -/
theorem ReferenceReplay.definition_not_mem_of_fresh {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut targetOut : Env .anon} {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev source target ds sourceOut targetOut)
    {cv : ConstantVal .anon} {value : Expr .anon} {hint : ReducibilityHint}
    (fresh : targetOut.find? cv.name = none) : .defnDecl cv value hint ∉ ds := by
  intro member
  have present := replay.checked.storage.declared member
    (show ConstantInfo.defnInfo cv value hint ∈ IxVM.Consistency.installs (.defnDecl cv value hint)
      from List.mem_cons_self)
  change (targetOut.find? cv.name).isSome = true at present
  rw [fresh] at present
  cases present

/-- A later definition cannot reuse a name already present at this actual prefix. -/
theorem ReferenceReplay.definition_not_mem_after_found {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut targetOut : Env .anon} {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev source target ds sourceOut targetOut)
    {cv : ConstantVal .anon} {value : Expr .anon} {hint : ReducibilityHint} {ci : ConstantInfo .anon}
    (found : target.find? cv.name = some ci) : .defnDecl cv value hint ∉ ds := by
  induction replay with
  | nil => intro member; cases member
  | cons _ _ checked _ ih =>
    intro member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨_, _, header, _, _, _, _⟩ := checked.definition
      have fresh := header.1
      rw [found] at fresh
      cases fresh
    · exact ih (checked.envExt.find found) member

/-- A list's prefix before its first occurrence of an element is unique. -/
theorem first_prefix_unique {α : Type} {a : α} :
    ∀ {left right left' right' : List α},
      left ++ a :: right = left' ++ a :: right' → a ∉ left → a ∉ left' → left = left'
  | [], _, [], _, _, _, _ => rfl
  | [], _, x :: xs, _, same, _, absent => by
    have head := (List.cons.inj same).1
    exact (absent (List.mem_cons.mpr (Or.inl head))).elim
  | x :: xs, _, [], _, same, absent, _ => by
    have head := (List.cons.inj same).1
    exact (absent (List.mem_cons.mpr (Or.inl head.symm))).elim
  | x :: xs, right, y :: ys, right', same, absent, absent' => by
    obtain ⟨rfl, tail⟩ := List.cons.inj same
    exact congrArg (List.cons x) (first_prefix_unique tail
      (fun h => absent (List.mem_cons_of_mem _ h))
      (fun h => absent' (List.mem_cons_of_mem _ h)))

private theorem find_eq_of_common_extension {left right final : Env .anon}
    (leftExt : EnvExt left final) (rightExt : EnvExt right final)
    (samePresence : ∀ name, (left.find? name).isSome = (right.find? name).isSome) :
    ∀ name, left.find? name = right.find? name := by
  intro name
  cases first : left.find? name with
  | none =>
    cases second : right.find? name with
    | none => rfl
    | some ci => have impossible := samePresence name; rw [first, second] at impossible; cases impossible
  | some ci =>
    cases second : right.find? name with
    | none => have impossible := samePresence name; rw [first, second] at impossible; cases impossible
    | some other => exact (leftExt.find first).symm.trans (rightExt.find second)

/-- Actual prefixes before the same fresh definition have equal lookups when they share the final store. -/
theorem ReferenceReplay.prefix_find_eq_of_fresh {fuel : Nat} {ev : Evidences .anon}
    {sourceLeft targetLeft sourceRight targetRight final : Env .anon}
    {left right leftRest rightRest : List (Declaration .anon)}
    (first : ReferenceReplay fuel ev Env.empty Env.empty left sourceLeft targetLeft)
    (second : ReferenceReplay fuel ev Env.empty Env.empty right sourceRight targetRight)
    {cv : ConstantVal .anon} {value : Expr .anon} {hint : ReducibilityHint}
    (same : left ++ .defnDecl cv value hint :: leftRest = right ++ .defnDecl cv value hint :: rightRest)
    (leftFresh : targetLeft.find? cv.name = none) (rightFresh : targetRight.find? cv.name = none)
    (leftExt : EnvExt targetLeft final) (rightExt : EnvExt targetRight final) :
    ∀ name, targetLeft.find? name = targetRight.find? name := by
  have samePrefix := first_prefix_unique same (first.definition_not_mem_of_fresh leftFresh)
    (second.definition_not_mem_of_fresh rightFresh)
  subst right
  have sameSource : sourceLeft = sourceRight :=
    Except.ok.inj (first.sourceRun.symm.trans second.sourceRun)
  subst sourceRight
  apply find_eq_of_common_extension leftExt rightExt
  intro name
  exact (first.endAgreement.isSome name).symm.trans (second.endAgreement.isSome name)

/-- A frame depends only on lookups in its starting environment. -/
theorem frame_of_same_lookups {P : KeyScope .anon} {first second final : Env .anon}
    (same : ∀ name, first.find? name = second.find? name) (frame : EnvFrame P first final) :
    EnvFrame P second final := by
  apply EnvFrame.mk
  · intro name good
    exact (frame.find_eq good).trans (same name)
  · intro name ci good found
    exact frame.good name ci good ((same name).trans found)
  · intro role outside
    exact (same _).symm.trans (frame.absent role outside)
  · exact frame.pre

/-- Admission constructs a theorem frame at the caller's supplied actual prefix and step. -/
theorem ReferenceReplay.admitted_theorem_frame_at {S : Type u} [SetTheory S]
    {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b)
    {fuel : Nat} {ev : Evidences .anon}
    {sourceBefore targetBefore sourceAfter targetAfter targetOut : Env .anon}
    {past future : List (Declaration .anon)} {cv : ConstantVal .anon} {value : Expr .anon}
    (declarations : (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList.map
      IxVM.Refinement.thmToOpaqueDefn = past ++ .defnDecl cv value .opaque :: future)
    (prefixRun : ReferenceReplay fuel ev Env.empty Env.empty past sourceBefore targetBefore)
    (sourceStep : checkDecl .verified (fueledOps .verified fuel) ev sourceBefore
      (.defnDecl cv value .opaque) = .ok sourceAfter)
    (targetStep : CheckedReferenceStep fuel targetBefore (.defnDecl cv value .opaque) targetAfter)
    (suffixRun : ReferenceReplay fuel ev sourceAfter targetAfter future w.checkedEnv targetOut)
    (member : Declaration.thmDecl cv value ∈ (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList)
    (publicName : cv.name.isAux = false) :
    ∃ P : KeyScope .anon, EnvFrame P targetBefore targetOut ∧ cv.type.Good P := by
  have remaining := ReferenceReplay.cons prefixRun.endAgreement sourceStep targetStep suffixRun
  have full : ReferenceReplay fuel ev Env.empty Env.empty
      ((Frontend.preparePrelude w.prelude.ix w.fullDecls).toList.map IxVM.Refinement.thmToOpaqueDefn)
      w.checkedEnv targetOut := by
    rw [declarations]
    exact prefixRun.append remaining
  obtain ⟨_, _, _, _, _, _, P, computedSplit, computedPrefix, computedSource, computedStep,
      computedSuffix, frame, good⟩ := full.admitted_theorem_frame (S := S) w member publicName
  have computedRemaining := ReferenceReplay.cons computedPrefix.endAgreement computedSource computedStep computedSuffix
  obtain ⟨_, _, actualHeader, _, _, _, _⟩ := targetStep.definition
  obtain ⟨_, _, computedHeader, _, _, _, _⟩ := computedStep.definition
  have same := computedPrefix.prefix_find_eq_of_fresh prefixRun
    (computedSplit.symm.trans declarations)
    (Option.isNone_iff_eq_none.mp computedHeader.1) (Option.isNone_iff_eq_none.mp actualHeader.1)
    computedRemaining.checked.envExt remaining.checked.envExt
  exact ⟨P, frame_of_same_lookups same frame, good⟩

end IxVM.Refinement.Decl
