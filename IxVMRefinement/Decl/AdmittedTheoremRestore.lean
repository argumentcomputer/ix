import IxVMRefinement.Decl.TheoremRestoreSim

/-! # The theorem-kind fold into the actual restored final store

Only a public theorem at the current checked step can introduce a newly selected row. An
older occurrence would already occupy its name, and a later occurrence would fail freshness.
Its actual prefix frame and value check establish the row before the fold advances.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open IxVM.Refinement.Assembly (ThmSimAt ThmValueTyped)

universe u

/-- The actual admission replay constructs theorem-kind simulation into its restored final store. -/
theorem ReferenceReplay.admitted_theorem_simulation {S : Type u} [SetTheory S]
    {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b)
    {fuel : Nat} {ev : Evidences .anon} {targetOut : Env .anon}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty
      ((Frontend.preparePrelude w.prelude.ix w.fullDecls).toList.map IxVM.Refinement.thmToOpaqueDefn)
      w.checkedEnv targetOut) :
    ThmSimAt targetOut (TheoremRestore.environment
      (selectedTheorems (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList) targetOut) := by
  let declarations := (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList
  let selected := selectedTheorems declarations
  let restored := TheoremRestore.environment selected targetOut
  have allowed : ∀ name, selected name = true → ThmKind.AllowedKey name := by
    intro name chosen
    obtain ⟨cv, value, member, publicName, rfl⟩ := selectedTheorems_iff.mp chosen
    exact replay.admitted_theorem_allowed (S := S) w member publicName
  have finalPropositions := replay.endAgreement.theoremsInProp w.theorems
  have go : ∀ (future past : List (Declaration .anon)) (sourceBefore targetBefore : Env .anon),
      declarations = past ++ future →
      ReferenceReplay fuel ev Env.empty Env.empty (past.map IxVM.Refinement.thmToOpaqueDefn)
        sourceBefore targetBefore →
      ReferenceReplay fuel ev sourceBefore targetBefore (future.map IxVM.Refinement.thmToOpaqueDefn)
        w.checkedEnv targetOut →
      (∀ name cv value, targetBefore.find? name = some (.defnInfo cv value .opaque) →
        selected name = true → ThmValueTyped restored cv value) →
      (∀ name cv value, targetOut.find? name = some (.defnInfo cv value .opaque) →
        selected name = true → ThmValueTyped restored cv value) := by
    intro future
    induction future with
    | nil =>
      intro past sourceBefore targetBefore split prefixRun suffixRun rows
      cases suffixRun with
      | nil => exact rows
    | cons d future ih =>
      intro past sourceBefore targetBefore split prefixRun suffixRun rows
      cases suffixRun with
      | @cons _ _ sourceNext targetNext _ _ _ _ agreement sourceCheck targetCheck tail =>
        have simulation : ThmSimAt targetBefore restored :=
          TheoremRestore.simulation_of_rows selected
            (ReferenceReplay.cons agreement sourceCheck targetCheck tail).checked.envExt allowed rows
        have nextRows : ∀ name cv value,
            targetNext.find? name = some (.defnInfo cv value .opaque) →
            selected name = true → ThmValueTyped restored cv value := by
          intro name cv value found chosen
          cases previous : targetBefore.find? name with
          | some old =>
            have same := targetCheck.envExt.find previous
            rw [found] at same
            obtain rfl := Option.some.inj same
            exact rows name cv value previous chosen
          | none =>
            obtain ⟨rawCv, rawValue, member, publicName, sameName⟩ := selectedTheorems_iff.mp chosen
            have admittedMember := member
            rw [split, List.mem_append, List.mem_cons] at member
            rcases member with earlier | current | later
            · have mappedMember : Declaration.defnDecl rawCv rawValue .opaque ∈
                  past.map IxVM.Refinement.thmToOpaqueDefn := by
                rw [← thmToOpaqueDefn_of_public publicName]
                exact List.mem_map_of_mem earlier
              have present := prefixRun.checked.storage.declared mappedMember
                (show ConstantInfo.defnInfo rawCv rawValue .opaque ∈
                    IxVM.Consistency.installs (.defnDecl rawCv rawValue .opaque) from List.mem_cons_self)
              change (targetBefore.find? rawCv.name).isSome = true at present
              rw [sameName, previous] at present
              cases present
            · subst d
              have mapped := thmToOpaqueDefn_of_public (value := rawValue) publicName
              rw [mapped] at sourceCheck targetCheck
              obtain ⟨type, checkedValue, header, body, output, _, _⟩ := targetCheck.definition
              have mappedSplit : (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList.map
                  IxVM.Refinement.thmToOpaqueDefn = past.map IxVM.Refinement.thmToOpaqueDefn ++
                    .defnDecl rawCv rawValue .opaque :: future.map IxVM.Refinement.thmToOpaqueDefn := by
                rw [show (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList =
                  past ++ .thmDecl rawCv rawValue :: future from split]
                simp only [List.map_append, List.map_cons, mapped]
              obtain ⟨scope, frame, good⟩ := ReferenceReplay.admitted_theorem_frame_at (S := S) w
                mappedSplit prefixRun sourceCheck targetCheck tail admittedMember publicName
              have typed := ThmKind.value_typed_from_final frame simulation good header body
                (finalPropositions rawCv rawValue admittedMember)
              have currentFound : targetNext.find? rawCv.name =
                  some (.defnInfo { rawCv with type } checkedValue .opaque) := by
                rw [output]
                exact Env.find?_cons_self _ _
              rw [sameName, found] at currentFound
              obtain ⟨sameCv, sameValue, _⟩ := ConstantInfo.defnInfo.inj (Option.some.inj currentFound)
              rw [sameCv, sameValue]
              exact typed
            · have mappedMember : Declaration.defnDecl rawCv rawValue .opaque ∈
                  future.map IxVM.Refinement.thmToOpaqueDefn := by
                rw [← thmToOpaqueDefn_of_public publicName]
                exact List.mem_map_of_mem later
              exact (tail.definition_not_mem_after_found (by rw [sameName]; exact found) mappedMember).elim
        apply ih (past ++ [d]) sourceNext targetNext ?_ ?_ tail nextRows
        · simpa only [List.append_assoc, List.singleton_append] using split
        · have one : ReferenceReplay fuel ev sourceBefore targetBefore
              [IxVM.Refinement.thmToOpaqueDefn d] sourceNext targetNext :=
            .cons agreement sourceCheck targetCheck (.nil tail.startAgreement)
          simpa only [List.map_append, List.map_cons, List.map_nil] using prefixRun.append one
  have finalRows := go declarations [] Env.empty Env.empty rfl
    (.nil replay.startAgreement) replay (by
      intro name cv value found _
      simp only [Env.find?, Env.empty, List.find?_nil] at found
      cases found)
  exact TheoremRestore.simulation_of_rows selected (EnvExt.refl targetOut) allowed finalRows

/-- The restored final store also has actual typed theorem rows, including original auxiliary theorems. -/
theorem ReferenceReplay.admitted_restored_thmTyped {S : Type u} [SetTheory S]
    {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b)
    {fuel : Nat} {ev : Evidences .anon} {targetOut : Env .anon}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty
      ((Frontend.preparePrelude w.prelude.ix w.fullDecls).toList.map IxVM.Refinement.thmToOpaqueDefn)
      w.checkedEnv targetOut) :
    ThmTyped (TheoremRestore.environment
      (selectedTheorems (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList) targetOut) :=
  TheoremRestore.thmTyped _ (replay.admitted_theorem_simulation (S := S) w)
    (replay.checked.thmTyped ThmTyped.empty)

/-- Coherent admission constructs the replay, its final theorem-kind simulation and all theorem rows. -/
theorem admitted_theorem_restore {S : Type u} [SetTheory S]
    {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b) :
    ∃ fuel target,
      ReferenceReplay fuel
        (Reader.evidenceOf (Admission.streamContext _root_.Address.admissionHash w.table w.prelude
          (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order) (Ix.Cert.hintsOf w.env))
          w.state w.table)
        Env.empty Env.empty
        ((Frontend.preparePrelude w.prelude.ix w.fullDecls).toList.map IxVM.Refinement.thmToOpaqueDefn)
        w.checkedEnv target ∧
      ThmSimAt target (TheoremRestore.environment
        (selectedTheorems (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList) target) ∧
      ThmTyped (TheoremRestore.environment
        (selectedTheorems (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList) target) := by
  obtain ⟨fuel, target, replay⟩ := acceptsRef_referenceReplay w.accepted
  exact ⟨fuel, target, replay, replay.admitted_theorem_simulation (S := S) w,
    replay.admitted_restored_thmTyped (S := S) w⟩

end IxVM.Refinement.Decl
