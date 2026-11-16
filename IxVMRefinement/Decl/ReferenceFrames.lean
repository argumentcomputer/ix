import IxVMRefinement.Decl.ReferenceMetadata
import IxVMRefinement.Decl.ReferenceGenerated
import IxC.Kernel.Verify.Rename.UnionUnits

/-! # Actual environment frames at checked unit boundaries

The executable unit check separates later bases from completed earlier units and from the
prelude. Paired source/target replay transfers that noninterference to the annotated store.
Generated prefixes add no role entries, so they can be traversed inside the same frame.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

universe u

theorem ReferenceReplay.split {fuel : Nat} {ev : Evidences .anon}
    {source target sourceOut targetOut : Env .anon} {left right : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev source target (left ++ right) sourceOut targetOut) :
    ∃ sourceMiddle targetMiddle,
      ReferenceReplay fuel ev source target left sourceMiddle targetMiddle ∧
      ReferenceReplay fuel ev sourceMiddle targetMiddle right sourceOut targetOut := by
  induction left generalizing source target with
  | nil => exact ⟨source, target, .nil replay.startAgreement, replay⟩
  | cons d left ih =>
    cases replay with
    | cons agreement sourceCheck targetCheck tail =>
      obtain ⟨sourceMiddle, targetMiddle, first, rest⟩ := ih tail
      exact ⟨sourceMiddle, targetMiddle, .cons agreement sourceCheck targetCheck first, rest⟩

/-- Actual checked units separate every later base from the completed prefix and prelude. -/
theorem checked_units_separation {ds : List (Declaration .anon)}
    {before after : List (List (Declaration .anon))}
    (checked : checkUnits ds.toArray = .ok ())
    (split : unitsOf ds = before ++ after)
    (pastPrelude : preludeSize ≤ before.flatten.length) :
    (∀ key ∈ basesOf before.flatten, key ∉ basesOf after.flatten) ∧
      (∀ key ∈ basesOf after.flatten, ¬ IsPre key) ∧
      (∀ d ∈ after.flatten, d.BasisFree) := by
  have run : checkUnitsGo {} (unitsOf ds) 0 = .ok () := by
    simpa only [checkUnits, List.toList_toArray] using checked
  obtain ⟨notBasis, _, _, disjoint, past⟩ := (checkUnitsGo_ok_iff {} (unitsOf ds) 0).mp run
  rw [split] at notBasis disjoint past
  have pastAfter := PastFront.append (xs := before) (ys := after) past
  have noPreBool := pastAfter.all (by simpa only [Nat.zero_add] using pastPrelude)
  have noPre : ∀ key ∈ basesOf after.flatten, ¬ IsPre key := by
    intro key member isPre
    obtain ⟨unit, inAfter, inUnit⟩ := mem_basesOf_flatten.mp member
    have zero := noPreBool unit inAfter key inUnit
    rw [Key.isPreludeRole_iff.mpr isPre] at zero
    cases zero
  rw [List.pairwise_append] at disjoint
  refine ⟨?_, noPre, ?_⟩
  · intro key inBefore inAfter
    obtain ⟨oldUnit, oldMember, oldBase⟩ := mem_basesOf_flatten.mp inBefore
    obtain ⟨newUnit, newMember, newBase⟩ := mem_basesOf_flatten.mp inAfter
    exact disjoint.2.2 oldUnit oldMember newUnit newMember key oldBase newBase
  · intro d member
    obtain ⟨unit, inAfter, inUnit⟩ := List.mem_flatten.mp member
    apply Declaration.basisFree_of
    · intro kind same
      have noBasis := notBasis unit (List.mem_append_right before inAfter) d inUnit
      rw [same] at noBasis
      cases noBasis
    · intro name named
      exact noPre name.base (mem_basesOf.mpr ⟨d, member, name, named, rfl⟩)

private theorem target_lookup_eq {source target sourceOut targetOut : Env .anon}
    (before : ThmBodyView.Agrees source target) (after : ThmBodyView.Agrees sourceOut targetOut)
    (extension : EnvExt target targetOut) {key : Key .anon}
    (same : sourceOut.find? key = source.find? key) :
    targetOut.find? key = target.find? key := by
  cases found : target.find? key with
  | some ci => exact (extension.find found).trans found.symm
  | none =>
    have sourceNone : source.find? key = none :=
      Option.isNone_iff_eq_none.mp (by rw [before.isNone, found]; rfl)
    have finalNone : sourceOut.find? key = none := same.trans sourceNone
    have targetNone : targetOut.find? key = none :=
      Option.isNone_iff_eq_none.mp (by rw [← after.isNone, finalNone]; rfl)
    exact targetNone.trans found.symm

/-- A complete-unit prefix produces its actual frame against the final checked environment. -/
theorem ReferenceReplay.unit_frame {V : Type u} [SetTheory V]
    {fuel : Nat} {ev : Evidences .anon} {sourceOut targetOut : Env .anon}
    {ds : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty ds sourceOut targetOut)
    (checked : checkUnits ds.toArray = .ok ())
    {before after : List (List (Declaration .anon))}
    (split : unitsOf ds = before ++ after)
    (pastPrelude : preludeSize ≤ before.flatten.length) :
    ∃ sourceMiddle targetMiddle,
      ReferenceReplay fuel ev Env.empty Env.empty before.flatten sourceMiddle targetMiddle ∧
      ReferenceReplay fuel ev sourceMiddle targetMiddle after.flatten sourceOut targetOut ∧
      EnvFrame (nameScope (namesOf before.flatten)) targetMiddle targetOut := by
  have declarations : ds = before.flatten ++ after.flatten := by
    rw [← unitsOf_flatten ds, split, List.flatten_append]
  rw [declarations] at replay
  obtain ⟨sourceMiddle, targetMiddle, prefixRun, suffixRun⟩ := replay.split
  obtain ⟨disjoint, noPre, free⟩ := checked_units_separation checked split pastPrelude
  have growth := run_free .verified (fueledOps .verified fuel) ev after.flatten free
    sourceMiddle sourceOut suffixRun.sourceRun
  refine ⟨sourceMiddle, targetMiddle, prefixRun, suffixRun, EnvFrame.mk ?_ ?_ ?_ (nameScope_pre _)⟩
  · intro key good
    apply target_lookup_eq prefixRun.endAgreement suffixRun.endAgreement suffixRun.checked.envExt
    apply growth.keep
    intro newBase
    rcases Key.good_nameScope.mp good with oldBase | preBase
    · exact disjoint key.base oldBase newBase
    · exact noPre key.base newBase preBase
  · intro name ci _ found
    exact prefixRun.findGood (V := V) name ci found
  · intro role outside
    exact prefixRun.declaredScope.absent outside

private theorem middle_lookup_eq {before middle after : Env .anon}
    (first : EnvExt before middle) (rest : EnvExt middle after)
    {key : Key .anon} (finalEq : after.find? key = before.find? key) :
    middle.find? key = before.find? key := by
  cases found : before.find? key with
  | some ci => exact (first.find found).trans found.symm
  | none =>
    cases current : middle.find? key with
    | none => exact current.trans found.symm
    | some ci =>
      have final := rest.find current
      rw [finalEq, found] at final
      cases final

/-- Traversing an actual generated prefix preserves a frame for the completed earlier units. -/
theorem ReferenceReplay.frame_after_generated {P : KeyScope .anon}
    {fuel : Nat} {ev : Evidences .anon} {source target sourceMiddle targetMiddle sourceOut targetOut : Env .anon}
    {generated rest : List (Declaration .anon)}
    (prefixRun : ReferenceReplay fuel ev source target generated sourceMiddle targetMiddle)
    (suffixRun : ReferenceReplay fuel ev sourceMiddle targetMiddle rest sourceOut targetOut)
    (allGenerated : ∀ d ∈ generated, d.isGenerated = true)
    (frame : EnvFrame P target targetOut) :
    EnvFrame P targetMiddle targetOut := by
  have middleEq : ∀ key, key.Good P → targetMiddle.find? key = target.find? key := by
    intro key good
    exact middle_lookup_eq prefixRun.checked.envExt suffixRun.checked.envExt (frame.find_eq good)
  apply EnvFrame.mk
  · intro key good
    exact (frame.find_eq good).trans (middleEq key good).symm
  · intro key ci good found
    exact frame.good key ci good (by rw [← middleEq key good]; exact found)
  · intro role outside
    rw [prefixRun.generated_nonAux allGenerated (by intro base derived same; cases same)]
    exact frame.absent role outside
  · exact frame.pre

end IxVM.Refinement.Decl
