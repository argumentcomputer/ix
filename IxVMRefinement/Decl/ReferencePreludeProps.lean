import IxVMRefinement.Decl.ReferencePosition
import IxC.Kernel.Model.AxiomBits
import IxC.Kernel.Ixon.PreludeShape
import IxC.Kernel.Verify.Frontend.Prepare

/-! # Proposition checks exclude theorem declarations at prelude heads

Prepared fronts may contain a stream's own declarations. Reserved names are rejected by the
actual constant check; the remaining former heads are pinned to types whose sorts are positive.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open IxVM.Refinement.Assembly (exprNoLet exprNoLet_of_erasePw_eq annotates_erasePw_of_noLet)

private theorem annotation_pin_shape {env : Env .anon} {fuel : Nat}
    {raw type pin : Expr .anon}
    (shape : raw.erasePw = pin.erasePw) (noLet : exprNoLet pin = true)
    (closed : raw.hasFvar = false) (bounded : raw.looseBVarsBounded 0 = true)
    (annotated : annotateCore .verified env fuel 0 raw = .ok type) :
    type.erasePw = pin.erasePw :=
  (annotates_erasePw_of_noLet (annotateCore_to_annotates annotated closed bounded)
    (exprNoLet_of_erasePw_eq shape noLet)).trans shape

private theorem sort_type_not_prop {env : Env .anon} {fuel : Nat} {raw type st : Expr .anon}
    {u : Level} (shape : raw.erasePw = (.sort (.succ .zero) : Expr .anon).erasePw)
    (closed : raw.hasFvar = false) (bounded : raw.looseBVarsBounded 0 = true)
    (annotated : annotateCore .verified env fuel 0 raw = .ok type)
    (inferred : inferTypeCore .verified env fuel 0 type = .ok st)
    (sorted : ensureSortCore .verified env fuel 0 st = .ok u)
    (zero : u.isZero = true) : False := by
  have typeShape := annotation_pin_shape shape rfl closed bounded annotated
  obtain rfl := erasePwNames_sort_invS typeShape
  cases fuel with
  | zero => rw [inferTypeCore_zero] at inferred; cases inferred
  | succ fuel =>
    obtain rfl := inferTypeCore_sort_inv inferred
    obtain rfl := ensureSortCore_sort_eq sorted
    cases zero

private theorem and_type_not_prop {env : Env .anon} {fuel : Nat} {raw type st : Expr .anon}
    {u : Level} (shape : raw.erasePw = (andSpecTy : Expr .anon).erasePw)
    (closed : raw.hasFvar = false) (bounded : raw.looseBVarsBounded 0 = true)
    (annotated : annotateCore .verified env fuel 0 raw = .ok type)
    (inferred : inferTypeCore .verified env fuel 0 type = .ok st)
    (sorted : ensureSortCore .verified env fuel 0 st = .ok u)
    (zero : u.isZero = true) : False := by
  have typeShape := annotation_pin_shape shape rfl closed bounded annotated
  change type.erasePw = .forallE (.sort .zero)
    (.forallE (.sort .zero) (.sort .zero) _) _ at typeShape
  obtain ⟨outerDomain, outerBody, outerMeta, rfl, outerDomainShape, outerBodyShape⟩ :=
    erasePwNames_forallE_invS typeShape
  obtain rfl := erasePwNames_sort_invS outerDomainShape
  obtain ⟨innerDomain, innerBody, innerMeta, rfl, innerDomainShape, innerBodyShape⟩ :=
    erasePwNames_forallE_invS outerBodyShape
  obtain rfl := erasePwNames_sort_invS innerDomainShape
  obtain rfl := erasePwNames_sort_invS innerBodyShape
  match fuel, inferred with
  | 0, inferred => rw [inferTypeCore_zero] at inferred; cases inferred
  | firstFuel + 1, inferred =>
    obtain ⟨tty, outerLevel, bt, bodyLevel, _, _, bodyInferred, bodySorted, _, rfl⟩ :=
      inferTypeCore_forall_inv inferred
    change inferTypeCore .verified env firstFuel 1
      (.forallE (.sort .zero) (.sort .zero) innerMeta) = .ok bt at bodyInferred
    match firstFuel, bodyInferred with
    | 0, bodyInferred => rw [inferTypeCore_zero] at bodyInferred; cases bodyInferred
    | innerFuel + 1, bodyInferred =>
      obtain ⟨tty, innerLevel, bt, innerSort, _, _, lastInferred, lastSorted, _, rfl⟩ :=
        inferTypeCore_forall_inv bodyInferred
      change inferTypeCore .verified env innerFuel 2 (.sort .zero) = .ok bt at lastInferred
      match innerFuel, lastInferred with
      | 0, lastInferred => rw [inferTypeCore_zero] at lastInferred; cases lastInferred
      | lastFuel + 1, lastInferred =>
        obtain rfl := inferTypeCore_sort_inv lastInferred
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

/-- A theorem cannot occupy any of the head keys used to select the prepared prelude. -/
theorem ReferenceReplay.theorem_not_prelude_head
    {fuel : Nat} {ev : Evidences .anon} {sourceOut targetOut : Env .anon}
    {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty
      (ds.map IxVM.Refinement.thmToOpaqueDefn) sourceOut targetOut)
    (propositions : IxVM.Refinement.TheoremsInProp sourceOut ds)
    (anchors : IxVM.Refinement.AnchorsTyped ds)
    {cv : ConstantVal .anon} {value : Expr .anon}
    (member : Declaration.thmDecl cv value ∈ ds) :
    cv.name ∉ [eqName, natName, punitName, emptyName, falseName,
      quotName, quotMkName, quotLiftName, quotIndName, quotSoundName, andName, boolName] := by
  intro head
  have publicName : cv.name.isAux = false := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at head
    rcases head with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl
  have mapped : IxVM.Refinement.thmToOpaqueDefn (.thmDecl cv value) = .defnDecl cv value .opaque := by
    cases h : cv.name with
    | id _ | role _ => simp only [IxVM.Refinement.thmToOpaqueDefn, h]
    | aux _ _ => rw [h] at publicName; cases publicName
  have checkedMember : Declaration.defnDecl cv value .opaque ∈ ds.map IxVM.Refinement.thmToOpaqueDefn := by
    rw [← mapped]
    exact List.mem_map_of_mem member
  obtain ⟨_, _, _, _, _, _, _, _, _, checked, _⟩ := replay.declarationStep checkedMember
  obtain ⟨type, value', header, _, _, _, _⟩ := checked.definition
  obtain ⟨_, reserved, _, _, bounded, closed, _, _, _, _⟩ := header
  obtain ⟨propFuel, propType, propSt, propU, annotated, inferred, sorted, zero⟩ :=
    propositions cv value member
  have pinned (pin : ConstantVal .anon) (atHead : IxVM.Refinement.anchorPin? cv.name = some pin) :
      cv.type.erasePw = pin.type.erasePw := by
    have pinCheck := anchors _ member cv List.mem_cons_self pin atHead
    simp only [ConstantVal.matchesPin, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at pinCheck
    exact pinCheck.2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at head
  rcases head with h | h | h | h | h | h | h | h | h | h | h | h
  any_goals rw [h] at reserved; cases reserved
  · have shape := pinned ⟨andName, [], andSpecTy⟩ (by rw [h]; rfl)
    exact and_type_not_prop shape closed bounded annotated inferred sorted zero
  · have shape := pinned ⟨boolName, [], .sort (.succ .zero)⟩ (by rw [h]; rfl)
    exact sort_type_not_prop shape closed bounded annotated inferred sorted zero

end IxVM.Refinement.Decl
