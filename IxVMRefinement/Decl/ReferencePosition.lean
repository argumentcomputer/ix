import IxVMRefinement.Decl.ReferencePublicScope

/-! # Locating actual declaration frames in checked units -/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

universe u

private theorem unitsGo_closer {md : Mode} :
    ∀ (ds acc : List (Declaration md)), (∀ d ∈ acc, d.isGenerated = true) →
      ∀ {d : Declaration md}, d ∈ ds → d.isGenerated = false →
        ∃ before after generated,
          unitsGo acc ds = before ++ (generated ++ [d]) :: after ∧
          (∀ g ∈ generated, g.isGenerated = true)
  | [], _, _, _, member, _ => by cases member
  | first :: ds, acc, allGenerated, d, member, notGenerated => by
    by_cases firstGenerated : first.isGenerated = true
    · have memberTail : d ∈ ds := by
        rcases List.mem_cons.mp member with rfl | rest
        · rw [notGenerated] at firstGenerated
          cases firstGenerated
        · exact rest
      obtain ⟨before, after, generated, equation, allAux⟩ :=
        unitsGo_closer ds (first :: acc)
          (fun g hg => by
            rcases List.mem_cons.mp hg with rfl | hg
            · exact firstGenerated
            · exact allGenerated g hg) memberTail notGenerated
      exact ⟨before, after, generated, by rw [unitsGo, ite_eq_left firstGenerated, equation], allAux⟩
    · rw [unitsGo, ite_eq_right firstGenerated]
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨[], unitsGo [] ds, acc.reverse, ?_, ?_⟩
        · simp only [List.nil_append, List.reverse_cons]
        · intro g hg
          exact allGenerated g (List.mem_reverse.mp hg)
      · obtain ⟨before, after, generated, equation, allAux⟩ :=
          unitsGo_closer ds [] (by intro g hg; cases hg) member notGenerated
        refine ⟨(first :: acc).reverse :: before, after, generated, ?_, allAux⟩
        rw [equation]
        rfl

/-- Every ungenerated declaration closes its actual unit, after a generated prefix. -/
theorem unitsOf_closer {md : Mode} {ds : List (Declaration md)} {d : Declaration md}
    (member : d ∈ ds) (notGenerated : d.isGenerated = false) :
    ∃ before after generated,
      unitsOf ds = before ++ (generated ++ [d]) :: after ∧
      (∀ g ∈ generated, g.isGenerated = true) :=
  unitsGo_closer ds [] (by intro g hg; cases hg) member notGenerated

theorem ReferenceReplay.append {fuel : Nat} {ev : Evidences .anon}
    {source target sourceMiddle targetMiddle sourceOut targetOut : Env .anon}
    {left right : List (Declaration .anon)}
    (first : ReferenceReplay fuel ev source target left sourceMiddle targetMiddle)
    (rest : ReferenceReplay fuel ev sourceMiddle targetMiddle right sourceOut targetOut) :
    ReferenceReplay fuel ev source target (left ++ right) sourceOut targetOut := by
  induction first with
  | nil => exact rest
  | cons agreement checked installed _ ih => exact .cons agreement checked installed (ih rest)

/-- An actual post-prelude definition step has its unit's smaller scope and a final frame. -/
theorem ReferenceReplay.definition_unit_frame {V : Type u} [SetTheory V]
    {fuel : Nat} {ev : Evidences .anon} {sourceOut targetOut : Env .anon}
    {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty ds sourceOut targetOut)
    (checked : checkUnits ds.toArray = .ok ())
    {before after : List (List (Declaration .anon))} {generated : List (Declaration .anon)}
    {cv : ConstantVal .anon} {value : Expr .anon} {hint : ReducibilityHint}
    (split : unitsOf ds = before ++ (generated ++ [.defnDecl cv value hint]) :: after)
    (allGenerated : ∀ d ∈ generated, d.isGenerated = true)
    (pastPrelude : preludeSize ≤ before.flatten.length)
    (publicKeys : cv.type.constsResolveBy (fun key => !key.isAux) = true) :
    ∃ sourceBefore targetBefore sourceAfter targetAfter,
      ReferenceReplay fuel ev Env.empty Env.empty (before.flatten ++ generated) sourceBefore targetBefore ∧
      checkDecl .verified (fueledOps .verified fuel) ev sourceBefore (.defnDecl cv value hint) =
        .ok sourceAfter ∧
      CheckedReferenceStep fuel targetBefore (.defnDecl cv value hint) targetAfter ∧
      ReferenceReplay fuel ev sourceAfter targetAfter after.flatten sourceOut targetOut ∧
      EnvFrame (nameScope (namesOf before.flatten)) targetBefore targetOut ∧
      cv.type.Good (nameScope (namesOf before.flatten)) := by
  obtain ⟨sourceStart, targetStart, completed, suffixRun, frame⟩ :=
    replay.unit_frame (V := V) checked split pastPrelude
  have flattened : ((generated ++ [Declaration.defnDecl cv value hint]) :: after).flatten =
      generated ++ .defnDecl cv value hint :: after.flatten := by
    simp only [List.flatten_cons, List.append_assoc, List.singleton_append]
  rw [flattened] at suffixRun
  obtain ⟨sourceBefore, targetBefore, auxiliary, definition⟩ := suffixRun.split
  have actualFrame := auxiliary.frame_after_generated definition allGenerated frame
  cases definition with
  | cons agreement sourceCheck targetCheck rest =>
    obtain ⟨type, value', header, _, _, _, _⟩ := targetCheck.definition
    exact ⟨_, _, _, _, completed.append auxiliary, sourceCheck, targetCheck, rest,
      actualFrame, completed.public_type_scope (V := V) auxiliary allGenerated header publicKeys⟩

end IxVM.Refinement.Decl
