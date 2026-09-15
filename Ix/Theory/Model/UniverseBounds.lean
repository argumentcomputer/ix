/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Checking

/-!
Universe bounds for inferred result types. An inhabited dependent product
in a Grothendieck universe has all its fibres in that universe: any fibre
element can replace the corresponding value in an existing function graph.
This avoids inverting universe membership of an empty product.
-/

namespace Ix.Theory.Model

open SetTheory SetModel Certified

universe u v
variable {V : Type v} [SetTheory V]

/-- Varying one value of an existing function puts every fibre element in
the third union of the product. No choice of inhabitants for the remaining
fibres is needed. -/
theorem piSet_fibre_subset {A f a : V} {B : V → V}
    (member : f ∈ˢ piSet A B) (argument : a ∈ˢ A) :
    B a ⊆ˢ sUnion (sUnion (sUnion (piSet A B))) := by
  classical
  intro y hy
  let updated := fun x => if x = a then y else app f x
  have updatedMember : graph updated A ∈ˢ piSet A B := by
    apply graph_mem_piSet
    intro x hx
    dsimp [updated]
    split
    · next same => subst x; exact hy
    · exact app_mem_of_mem_piSet member hx
  have pairMember : kpair a y ∈ˢ graph updated A := by
    apply mem_graph.mpr
    exact ⟨a, argument, by simp [updated]⟩
  exact mem_sUnion.mpr ⟨upair a y,
    mem_sUnion.mpr ⟨kpair a y,
      mem_sUnion.mpr ⟨graph updated A, updatedMember, pairMember⟩,
      mem_upair_right _ _⟩, mem_upair_right _ _⟩

/-- Inhabitation is essential: an empty product alone cannot bound all of
its fibres. The bound here follows from an actual function member. -/
theorem IsTGUniverse.piSet_fibre_mem {U A f a : V} {B : V → V}
    (grothendieck : IsTGUniverse (Mem (V := V)) U)
    (formed : piSet A B ∈ˢ U) (member : f ∈ˢ piSet A B) (argument : a ∈ˢ A) :
    B a ∈ˢ U :=
  grothendieck.mem_of_subset_mem
    (grothendieck.sUnion_mem (grothendieck.sUnion_mem (grothendieck.sUnion_mem formed)))
    (piSet_fibre_subset member argument)

/-- A level with exactly the supplied binder's zero condition. Its positive
values serve only to preserve the Prop/data distinction in an upper bound. -/
def conditionLevel : PropWhen → VLevel
  | .never => .succ .zero
  | .allZero parameters _ => parameters.foldr (fun i level => .max (.param i) level) .zero

theorem zeroCondition_conditionLevel (condition : PropWhen) :
    zeroCondition (conditionLevel condition) = condition := by
  apply PropWhen.eq_of_holds
  intro valuation
  cases condition with
  | never => rfl
  | allZero parameters sorted =>
    change (zeroCondition (parameters.foldr (fun i level => .max (.param i) level) .zero)).holds
      valuation = parameters.all (fun i => valuation i == 0)
    clear sorted
    induction parameters with
    | nil => rfl
    | cons index parameters ih =>
      simpa only [List.foldr_cons, zeroCondition, PropWhen.holds_inter,
        PropWhen.holds_param, List.all_cons] using congrArg (fun b => (valuation index == 0) && b) ih

/-- A positive upper bound in the graph regime and zero in the proof
regime. This is a semantic size bound, not a claimed exact inference result. -/
def applicationLevel (functionLevel : VLevel) (condition : PropWhen) : VLevel :=
  .imax (.succ functionLevel) (conditionLevel condition)

theorem zeroCondition_applicationLevel (functionLevel : VLevel) (condition : PropWhen) :
    zeroCondition (applicationLevel functionLevel condition) = condition :=
  zeroCondition_conditionLevel condition

theorem applicationLevel_zero (functionLevel : VLevel) (condition : PropWhen) (levels : List Nat) :
    (applicationLevel functionLevel condition).eval levels = 0 ↔ regime condition levels = 0 := by
  simpa only [zeroCondition_applicationLevel] using
    (regime_zeroCondition (applicationLevel functionLevel condition) levels).symm

theorem applicationLevel_ge {functionLevel : VLevel} {condition : PropWhen} {levels : List Nat}
    (positive : regime condition levels ≠ 0) :
    functionLevel.eval levels + 1 ≤ (applicationLevel functionLevel condition).eval levels := by
  have nonzero : (conditionLevel condition).eval levels ≠ 0 := by
    intro zero
    apply positive
    rw [← zeroCondition_conditionLevel condition]
    exact (regime_zeroCondition _ _).mpr zero
  simp only [applicationLevel, VLevel.eval, VLevel.natIMax, nonzero, ↓reduceIte]
  exact Nat.le_max_left _ _

/-- Application retains a uniform bound on its inferred type. In the data
regime the function inhabits the product, so the fibre inversion above
applies; in the proof regime hereditary validity gives the exact bound zero. -/
theorem TypingClaim.applicationType {β : Type u} {entries : Environment β} {context : Context β}
    {function argument domain body : AExpr β} {condition : PropWhen} {level : VLevel}
    (functionTyped : TypingClaim.{u,v} entries context function (.forallE condition domain body))
    (functionTypeFormed : TypingClaim.{u,v} entries context
      (.forallE condition domain body) (.sort level))
    (argumentChecked : CheckingClaim.{u,v} entries context argument domain) :
    TypingClaim.{u,v} entries context (body.inst argument) (.sort (applicationLevel level condition)) := by
  intro V _ constants realizes levels env valid
  have typed := functionTyped.appChecking argumentChecked V constants realizes levels env valid
  obtain ⟨_, productValid, functionMember⟩ := functionTyped V constants realizes levels env valid
  have argumentMember := (argumentChecked V constants realizes levels env valid productValid.1).2
  have productBound := (functionTypeFormed V constants realizes levels env valid).2.2
  refine ⟨typed.2.1, trivial, ?_⟩
  simp only [interp_inst, Valuation.skip_zero, Valuation.insert_zero, interp]
  by_cases proofRegime : regime condition levels = 0
  · have zero := (applicationLevel_zero level condition levels).mpr proofRegime
    obtain ⟨_, _, bodyLevel, agrees, bodyBound⟩ := productValid
    have bodyZero := agrees.mp proofRegime
    simpa only [zero, bodyZero] using bodyBound _ argumentMember
  · have upper := applicationLevel_ge (functionLevel := level) proofRegime
    have positive : (applicationLevel level condition).eval levels ≠ 0 := by omega
    apply (univ_isTGUniverse positive).piSet_fibre_mem
      (A := interp constants levels env domain)
      (f := interp constants levels env function)
      (a := interp constants levels env argument)
      (B := fun x => interp constants levels (Valuation.cons x env) body)
    · apply univ_mono (Nat.le_trans (Nat.le_succ _) upper)
      simpa only [interp, piR_pos proofRegime] using productBound
    · simpa only [interp, piR_pos proofRegime] using functionMember
    · exact argumentMember

end Ix.Theory.Model
