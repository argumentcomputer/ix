import IxVMRefinement.Assembly.ReaderPublicTypes
import IxVMRefinement.Decl.ReferencePreludeFront
import IxVMRefinement.Decl.ThmKindProposition

/-! # Theorem prefix frames produced by coherent admission

The actual reader supplies raw type support, the selected prelude cannot contain an accepted
theorem, and the executed units check separates later keys. Together these construct each
public theorem's frame at its actual checked prefix, without a frame or closure hypothesis.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Semantics Ix.Kernel.Model

universe u

/-- Admission and the actual replay construct the complete frame at a public theorem step. -/
theorem ReferenceReplay.admitted_theorem_frame {S : Type u} [SetTheory S]
    {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b)
    {fuel : Nat} {ev : Evidences .anon} {targetOut : Env .anon}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty
      ((Frontend.preparePrelude w.prelude.ix w.fullDecls).toList.map IxVM.Refinement.thmToOpaqueDefn)
      w.checkedEnv targetOut)
    {cv : ConstantVal .anon} {value : Expr .anon}
    (member : Declaration.thmDecl cv value ∈ (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList)
    (publicName : cv.name.isAux = false) :
    ∃ before after sourceBefore targetBefore sourceAfter targetAfter (P : KeyScope .anon),
      (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList.map IxVM.Refinement.thmToOpaqueDefn =
        before ++ .defnDecl cv value .opaque :: after ∧
      ReferenceReplay fuel ev Env.empty Env.empty before sourceBefore targetBefore ∧
      checkDecl .verified (fueledOps .verified fuel) ev sourceBefore (.defnDecl cv value .opaque) =
        .ok sourceAfter ∧
      CheckedReferenceStep fuel targetBefore (.defnDecl cv value .opaque) targetAfter ∧
      ReferenceReplay fuel ev sourceAfter targetAfter after w.checkedEnv targetOut ∧
      EnvFrame P targetBefore targetOut ∧ cv.type.Good P := by
  obtain ⟨before, after, generated, split, allGenerated, pastPrelude⟩ :=
    replay.prepared_theorem_unit w.preludeRead w.theorems w.specifications.2.1 member publicName
  have mappedTheorem : IxVM.Refinement.thmToOpaqueDefn (.thmDecl cv value) =
      .defnDecl cv value .opaque := by
    cases name : cv.name with
    | id _ | role _ => simp only [IxVM.Refinement.thmToOpaqueDefn, name]
    | aux _ _ => rw [name] at publicName; cases publicName
  have mappedSplit :
      unitsOf ((Frontend.preparePrelude w.prelude.ix w.fullDecls).toList.map IxVM.Refinement.thmToOpaqueDefn) =
      before.map (List.map IxVM.Refinement.thmToOpaqueDefn) ++
        (generated.map IxVM.Refinement.thmToOpaqueDefn ++ [.defnDecl cv value .opaque]) ::
          after.map (List.map IxVM.Refinement.thmToOpaqueDefn) := by
    rw [unitsOf_thmToOpaqueDefn, split]
    simp only [List.map_append, List.map_cons, List.map_nil, mappedTheorem]
  have mappedGenerated : ∀ d ∈ generated.map IxVM.Refinement.thmToOpaqueDefn,
      d.isGenerated = true := by
    intro d member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    simpa only [Declaration.isGenerated, thmToOpaqueDefn_names] using allGenerated original originalMember
  have mappedPast : preludeSize ≤ (before.map (List.map IxVM.Refinement.thmToOpaqueDefn)).flatten.length := by
    rw [← List.map_flatten, List.length_map]
    exact pastPrelude
  have checkedUnits : checkUnits
      ((Frontend.preparePrelude w.prelude.ix w.fullDecls).toList.map IxVM.Refinement.thmToOpaqueDefn).toArray =
      .ok () := by
    rw [← List.map_toArray, Array.toArray_toList, checkUnits_thmToOpaqueDefn]
    exact w.units
  have notGenerated : (Declaration.thmDecl cv value).isGenerated = false := by
    simp only [Declaration.isGenerated, Declaration.names, List.isEmpty_cons, Bool.not_false,
      List.all_cons, List.all_nil, publicName, Bool.false_and, Bool.and_false]
  have publicType := IxVM.Refinement.Assembly.admitted_publicValueTypes w _ member notGenerated
  obtain ⟨sourceBefore, targetBefore, sourceAfter, targetAfter, earlier, sourceCheck, targetCheck,
      remaining, frame, good⟩ :=
    replay.definition_unit_frame (V := S) checkedUnits mappedSplit mappedGenerated mappedPast publicType
  refine ⟨_, _, sourceBefore, targetBefore, sourceAfter, targetAfter, _, ?_,
    earlier, sourceCheck, targetCheck, remaining, frame, good⟩
  rw [← unitsOf_flatten ((Frontend.preparePrelude w.prelude.ix w.fullDecls).toList.map
    IxVM.Refinement.thmToOpaqueDefn), mappedSplit]
  simp only [List.flatten_append, List.flatten_cons, List.append_assoc, List.singleton_append]

/-- The actual checked theorem row is proposition-typed in every local theorem-kind simulation. -/
theorem ReferenceReplay.admitted_theorem_typed {S : Type u} [SetTheory S]
    {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b)
    {fuel : Nat} {ev : Evidences .anon} {targetOut : Env .anon}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty
      ((Frontend.preparePrelude w.prelude.ix w.fullDecls).toList.map IxVM.Refinement.thmToOpaqueDefn)
      w.checkedEnv targetOut)
    {cv : ConstantVal .anon} {value : Expr .anon}
    (member : Declaration.thmDecl cv value ∈ (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList)
    (publicName : cv.name.isAux = false) :
    ∃ before after sourceBefore targetBefore sourceAfter targetAfter type checkedValue,
      (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList.map IxVM.Refinement.thmToOpaqueDefn =
        before ++ .defnDecl cv value .opaque :: after ∧
      ReferenceReplay fuel ev Env.empty Env.empty before sourceBefore targetBefore ∧
      checkDecl .verified (fueledOps .verified fuel) ev sourceBefore (.defnDecl cv value .opaque) =
        .ok sourceAfter ∧
      CheckedReferenceStep fuel targetBefore (.defnDecl cv value .opaque) targetAfter ∧
      ReferenceReplay fuel ev sourceAfter targetAfter after w.checkedEnv targetOut ∧
      ConstantValRun .verified fuel targetBefore cv type ∧
      ValueFrontRun .verified fuel targetBefore cv value type checkedValue ∧
      (∀ restored, IxVM.Refinement.Assembly.ThmSimAt targetBefore restored →
        IxVM.Refinement.Assembly.ThmValueTyped restored { cv with type } checkedValue) := by
  obtain ⟨before, after, sourceBefore, targetBefore, sourceAfter, targetAfter, scope,
      split, earlier, sourceCheck, targetCheck, remaining, frame, good⟩ :=
    replay.admitted_theorem_frame (S := S) w member publicName
  obtain ⟨type, checkedValue, header, body, _, _, _⟩ := targetCheck.definition
  refine ⟨before, after, sourceBefore, targetBefore, sourceAfter, targetAfter, type, checkedValue,
    split, earlier, sourceCheck, targetCheck, remaining, header, body, ?_⟩
  intro restored simulation
  exact ThmKind.value_typed_from_final frame simulation good header body
    (replay.endAgreement.theoremsInProp w.theorems cv value member)

end IxVM.Refinement.Decl
