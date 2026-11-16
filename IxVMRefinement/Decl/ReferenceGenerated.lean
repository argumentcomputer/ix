import IxVMRefinement.Decl.ReferenceReplay
import IxVMRefinement.Decl.ReferenceUnits
import IxVMRefinement.Assembly.GroupedInstall

/-! # Actual generated prefixes preserve public lookups

The source checker rules out a quotient pin masquerading under an auxiliary name. With that
checked fact, generated declarations install only auxiliary entries, including the derived
functions and tables of native or modeled blocks.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics
open IxVM.Consistency (InstallStep)
open IxVM.Refinement.Assembly (DeclAllAux)

private theorem generated_names_aux {d : Declaration .anon} (generated : d.isGenerated = true) :
    ∀ name ∈ d.names, ∃ base derived, name = .aux base derived := by
  simp only [Declaration.isGenerated, Bool.and_eq_true] at generated
  intro name member
  have auxiliary := List.all_eq_true.mp generated.2 name member
  cases name with
  | id _ | role _ => cases auxiliary
  | aux base derived => exact ⟨base, derived, rfl⟩

/-- Successful generated declarations have only auxiliary public-install entries. -/
theorem checked_generated_allAux {fuel : Nat} {ev : Evidences .anon}
    {before after : Env .anon} {d : Declaration .anon}
    (generated : d.isGenerated = true)
    (checked : checkDecl .verified (fueledOps .verified fuel) ev before d = .ok after) :
    DeclAllAux d := by
  have names := generated_names_aux generated
  cases d with
  | defnDecl cv value hint | thmDecl cv value | opaqueDecl cv value =>
    intro ci member
    obtain rfl := List.mem_singleton.mp member
    exact names cv.name List.mem_cons_self
  | axiomDecl cv =>
    intro ci member
    simp only [IxVM.Consistency.installs] at member
    split at member
    · cases member
    · obtain rfl := List.mem_singleton.mp member
      exact names cv.name List.mem_cons_self
  | indDecl block nP =>
    intro ci member
    apply names ci.name
    rw [← indDecl_installs_names]
    exact List.mem_map_of_mem member
  | basisDecl kind =>
    simp only [Declaration.isGenerated, Declaration.names, List.isEmpty_nil,
      Bool.not_true, Bool.false_and, Bool.false_eq_true] at generated
  | quotDecl kind cv =>
    cases kind with
    | ctor | lift | ind | sound => intro ci member; cases member
    | type =>
      simp only [checkDecl] at checked
      split at checked
      · next pin =>
        have equal : ConstantVal.canon cv =
            ConstantVal.canon (BasisKind.quotK.decls.getD QuotKind.type.slot (.axiomInfo default)).toConstantVal :=
          of_decide_eq_true pin
        have sameName := congrArg ConstantVal.name equal
        change cv.name = quotName at sameName
        obtain ⟨base, derived, auxiliary⟩ := names cv.name List.mem_cons_self
        rw [sameName] at auxiliary
        cases auxiliary
      · cases checked

/-- A generated target step has a concrete prefix consisting entirely of auxiliary constants. -/
theorem ReferenceStep.aux_prefix {fuel : Nat} {before after : Env .anon} {d : Declaration .anon}
    (step : ReferenceStep fuel before d after) (auxiliary : DeclAllAux d) :
    ∃ added, after = ⟨added ++ before.consts⟩ ∧
      ∀ ci ∈ added, ∃ base derived, ci.name = .aux base derived := by
  cases step with
  | stored installed =>
    obtain ⟨added, equation, _, _, _, shape⟩ := installed
    refine ⟨added, equation, ?_⟩
    intro ci member
    rcases shape ci member with ⟨raw, declared, same⟩ | auxiliaryName
    · obtain ⟨base, derived, rawAux⟩ := auxiliary raw declared
      exact ⟨base, derived, same.symm.trans rawAux⟩
    · exact auxiliaryName
  | native notPinned recognized run =>
    obtain ⟨added, chain, shape, _⟩ :=
      nativeRunJ_freshChain recognized ((verifiedRunMap _).native (declNativeRun_runJ run))
    refine ⟨added, chain.eq, ?_⟩
    intro ci member
    rcases shape ci member with ⟨raw, declared, same⟩ | auxiliaryName
    · obtain ⟨base, derived, rawAux⟩ := auxiliary raw
        (by simpa only [IxVM.Consistency.installs, notPinned] using declared)
      exact ⟨base, derived, same.symm.trans rawAux⟩
    · exact auxiliaryName

theorem ReferenceStep.find_nonAux {fuel : Nat} {before after : Env .anon} {d : Declaration .anon}
    (step : ReferenceStep fuel before d after) (auxiliary : DeclAllAux d)
    {name : Key .anon} (publicName : NonAuxKey name) :
    after.find? name = before.find? name := by
  obtain ⟨added, equation, names⟩ := step.aux_prefix auxiliary
  rw [equation]
  apply EnvExt.find?_append_of_fresh
  intro ci member same
  obtain ⟨base, derived, auxiliaryName⟩ := names ci member
  exact publicName base derived (same.symm.trans auxiliaryName)

/-- Every actual generated replay preserves all non-auxiliary lookups. -/
theorem ReferenceReplay.generated_nonAux {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut targetOut : Env .anon} {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev source target ds sourceOut targetOut)
    (generated : ∀ d ∈ ds, d.isGenerated = true)
    {name : Key .anon} (publicName : NonAuxKey name) :
    targetOut.find? name = target.find? name := by
  induction replay with
  | nil => rfl
  | cons _ sourceCheck targetCheck tail ih =>
    have first := targetCheck.storage.find_nonAux
      (checked_generated_allAux (generated _ List.mem_cons_self) sourceCheck) publicName
    exact (ih (fun d member => generated d (List.mem_cons_of_mem _ member))).trans first

end IxVM.Refinement.Decl
