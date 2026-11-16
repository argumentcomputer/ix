import IxVMRefinement.Decl.AdmittedTheoremFrames
import IxC.Kernel.Model.NatEqs
import IxC.Kernel.Verify.DivModInv

/-! # Actual theorem checks exclude arithmetic acceleration keys -/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

private theorem binary_name_facts {name : Key .anon} (member : name ∈ Rules.natBinOpNames) :
    name ≠ natPredName ∧ name ≠ natName ∧ name ≠ boolName ∧ name ∈ natOpDeps name ∧
      (natOpNames.contains name = true ∨ natDivModNames.contains name = true) := by
  simp only [Rules.natBinOpNames, natDivModNames, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals decide

private theorem definition_lookup_other {before : Env .anon} {cv : ConstantVal .anon}
    {value : Expr .anon} {hint : ReducibilityHint} {key : Key .anon}
    (different : cv.name ≠ key) :
    (Env.mk (.defnInfo cv value hint :: before.consts)).find? key = before.find? key := by
  rw [Env.find?_cons]
  exact ite_eq_right different

private theorem pinned_codomain {before : Env .anon} {cv : ConstantVal .anon}
    {value type : Expr .anon} {hint : ReducibilityHint}
    (notNat : cv.name ≠ natName) (notBool : cv.name ≠ boolName)
    (natSupported : natLitSupported ⟨.defnInfo cv value hint :: before.consts⟩ = true)
    (pinned : natOpCod ⟨.defnInfo cv value hint :: before.consts⟩ cv.name type = true) :
    ∃ key ci, type = .const key [] ∧ before.find? key = some ci ∧
      ci.toConstantVal.levelParams = [] ∧ ci.toConstantVal.type = .sort (.succ .zero) := by
  unfold natOpCod at pinned
  split at pinned
  · simp only [Bool.and_eq_true, beq_iff_eq] at pinned
    obtain ⟨rfl, found⟩ := pinned
    cases stored : (Env.mk (.defnInfo cv value hint :: before.consts)).find? boolName with
    | none => rw [stored] at found; cases found
    | some ci =>
      rw [stored] at found
      simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at found
      rw [definition_lookup_other notBool] at stored
      exact ⟨boolName, ci, rfl, stored, found⟩
  · obtain rfl := beq_iff_eq.mp pinned
    obtain ⟨cvN, caps, _, _, _, _, _, _, found, _, _, levels, _, _, typeEq, _⟩ :=
      natLitSupported_inv natSupported
    rw [definition_lookup_other notNat] at found
    exact ⟨natName, .indInfo cvN caps, rfl, found, levels, typeEq⟩

private theorem binary_type_not_prop {before : Env .anon} {cv : ConstantVal .anon}
    {value type st : Expr .anon} {hint : ReducibilityHint} {fuel : Nat} {u : Level}
    (member : cv.name ∈ Rules.natBinOpNames)
    (natSupported : natLitSupported ⟨.defnInfo cv value hint :: before.consts⟩ = true)
    (pinned : natOpTyPinned ⟨.defnInfo cv value hint :: before.consts⟩ cv.name type = true)
    (inferred : inferTypeCore .verified before fuel 0 type = .ok st)
    (sorted : ensureSortCore .verified before fuel 0 st = .ok u)
    (zero : u.isZero = true) : False := by
  obtain ⟨notPred, notNat, notBool, _, _⟩ := binary_name_facts member
  obtain ⟨outerMeta, innerMeta, codomain, rfl, _, _⟩ := natOpTyPinned_shape_bin notPred pinned
  simp only [natOpTyPinned, ite_eq_right notPred, beq_self_eq_true, Bool.true_and] at pinned
  obtain ⟨key, ci, rfl, found, levels, typeEq⟩ :=
    pinned_codomain notNat notBool natSupported pinned
  match fuel, inferred with
  | 0, inferred => rw [inferTypeCore_zero] at inferred; cases inferred
  | firstFuel + 1, inferred =>
    obtain ⟨_, outerLevel, bodyType, _, _, _, bodyInferred, bodySorted, _, rfl⟩ :=
      inferTypeCore_forall_inv inferred
    change inferTypeCore .verified before firstFuel 1
      (.forallE (.const natName []) (.const key []) innerMeta) = .ok bodyType at bodyInferred
    match firstFuel, bodyInferred with
    | 0, bodyInferred => rw [inferTypeCore_zero] at bodyInferred; cases bodyInferred
    | innerFuel + 1, bodyInferred =>
      obtain ⟨_, innerLevel, lastType, _, _, _, lastInferred, lastSorted, _, rfl⟩ :=
        inferTypeCore_forall_inv bodyInferred
      change inferTypeCore .verified before innerFuel 2 (.const key []) = .ok lastType at lastInferred
      match innerFuel, lastInferred with
      | 0, lastInferred => rw [inferTypeCore_zero] at lastInferred; cases lastInferred
      | lastFuel + 1, lastInferred =>
        obtain ⟨actual, actualFound, _, _, lastTypeEq⟩ := Rules.inferTypeCore_const_inv_full lastInferred
        have same : actual = ci := Option.some.inj (actualFound.symm.trans found)
        rw [same, levels, typeEq] at lastTypeEq
        change lastType = .sort (.succ .zero) at lastTypeEq
        subst lastType
        obtain rfl := ensureSortCore_sort_eq lastSorted
        obtain rfl := ensureSortCore_sort_eq bodySorted
        obtain rfl := ensureSortCore_sort_eq sorted
        have simplified : Level.simplify (.imax outerLevel (.imax innerLevel (.succ .zero))) = .zero :=
          of_decide_eq_true zero
        have evaluation : Level.eval (fun _ => 0) (.imax outerLevel (.imax innerLevel (.succ .zero))) = 0 := by
          rw [← Level.eval_simplify, simplified]
          rfl
        have innerZero := (Ix.Kernel.SetModel.imax_eq_zero_iff _ _).mp evaluation
        have lastZero := (Ix.Kernel.SetModel.imax_eq_zero_iff _ _).mp innerZero
        cases lastZero

/-- The same actual run and derived frame establish the keys allowed by theorem-kind replay. -/
theorem ThmKind.allowed_from_final {P : KeyScope .anon} {before final after : Env .anon}
    (frame : EnvFrame P before final) {fuel : Nat} {cv : ConstantVal .anon}
    {rawValue : Expr .anon} {hint : ReducibilityHint}
    (good : cv.type.Good P)
    (run : DeclDefnRun .verified fuel before cv rawValue hint after)
    (proposition : ∃ propFuel type' st u,
      (fueledOps .verified propFuel).annotate final 0 cv.type = .ok type' ∧
      (fueledOps .verified propFuel).inferType final 0 type' = .ok st ∧
      (fueledOps .verified propFuel).ensureSort final 0 st = .ok u ∧ u.isZero = true) :
    AllowedKey cv.name := by
  obtain ⟨type, value, header, _, rfl, natRun, divRun⟩ := run
  obtain ⟨_, reserved, noProjection, _, _, _, annotated, _, _, st, u, inferred, sorted⟩ := header
  obtain ⟨propFuel, propType, propSt, propU, propAnnotation, propInference, propSort, zero⟩ := proposition
  have prefixZero := proposition_at_prefix frame good annotated inferred sorted
    propAnnotation propInference propSort zero
  refine ⟨?_, noProjection, ?_, ?_⟩
  · intro member
    obtain ⟨_, _, _, self, routes⟩ := binary_name_facts member
    have guarded : natOpGuard ⟨.defnInfo { cv with type } value hint :: before.consts⟩ cv.name = true ∧
        (natOpDeps cv.name).all (natOpStoredOk ⟨.defnInfo { cv with type } value hint :: before.consts⟩) = true := by
      rcases routes with ordinary | certified
      · exact ⟨(natRun ordinary).1, (natRun ordinary).2.1⟩
      · have guard := (divRun certified).1
        simp only [divModEnvGuard, Bool.and_eq_true] at guard
        exact guard.1.1.1
    have natSupported := guarded.1
    simp only [natOpGuard, Bool.and_eq_true] at natSupported
    have pinned := List.all_eq_true.mp guarded.2 cv.name self
    have foundSelf : (Env.mk (.defnInfo { cv with type } value hint :: before.consts)).find? cv.name =
        some (.defnInfo { cv with type } value hint) := Env.find?_cons_self _ _
    simp only [natOpStoredOk, foundSelf, ConstantInfo.toConstantVal, Bool.and_eq_true] at pinned
    exact binary_type_not_prop (cv := { cv with type }) member natSupported.1.1 pinned.2
      inferred sorted prefixZero
  · intro same
    rw [same] at reserved
    cases reserved
  · intro same
    rw [same] at reserved
    cases reserved

/-- Every admitted public theorem has a name that permits local theorem-kind replay. -/
theorem ReferenceReplay.admitted_theorem_allowed {S : Type u} [SetTheory S]
    {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b)
    {fuel : Nat} {ev : Evidences .anon} {targetOut : Env .anon}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty
      ((Frontend.preparePrelude w.prelude.ix w.fullDecls).toList.map IxVM.Refinement.thmToOpaqueDefn)
      w.checkedEnv targetOut)
    {cv : ConstantVal .anon} {value : Expr .anon}
    (member : Declaration.thmDecl cv value ∈ (Frontend.preparePrelude w.prelude.ix w.fullDecls).toList)
    (publicName : cv.name.isAux = false) : ThmKind.AllowedKey cv.name := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, targetCheck, _, frame, good⟩ :=
    replay.admitted_theorem_frame (S := S) w member publicName
  exact ThmKind.allowed_from_final frame good targetCheck.definition
    (replay.endAgreement.theoremsInProp w.theorems cv value member)

end IxVM.Refinement.Decl
