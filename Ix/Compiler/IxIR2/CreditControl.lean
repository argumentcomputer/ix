import Ix.Compiler.IxIR2.CreditRelation

/-! Register resolution and linear credit transfer for the same CFG. -/

namespace Ix.Compiler.IxIR2.CreditRefinement

open Eval
open Ix.Compiler.IxIR1.Sim (RValIso RValsIso)
open CallReuse.Sim (MapRel HeapMap)

theorem values_size {mapping : Array Nat} {left right : Array RVal}
    (related : RValsIso (MapRel mapping) left.toList right.toList) :
    left.size = right.size := by simpa using related.lengths

theorem values_extract {mapping : Array Nat} {left right : Array RVal}
    (related : RValsIso (MapRel mapping) left.toList right.toList) (start stop : Nat) :
    RValsIso (MapRel mapping) (left.extract start stop).toList
      (right.extract start stop).toList := by
  simp only [Array.toList_extract, List.extract_eq_take_drop]
  exact (related.drop start).take (stop - start)

theorem values_scalar {mapping : Array Nat} {left right : Array RVal}
    (related : RValsIso (MapRel mapping) left.toList right.toList) :
    left.all RVal.isScalar = right.all RVal.isScalar := by
  rw [← Array.all_toList, ← Array.all_toList]
  generalize left.toList = leftList at related ⊢
  generalize right.toList = rightList at related ⊢
  induction related with
  | nil => rfl
  | cons head tail ih => cases head <;> simp only [List.all_cons, RVal.isScalar, ih]

theorem scalarOracle_related {context : Context} {mapping : Array Nat}
    {left right : Array RVal} {address : Ixon.Address} {value : RVal}
    (values : RValsIso (MapRel mapping) left.toList right.toList)
    (called : ScalarOracleCall context address left value) :
    ScalarOracleCall context address right value ∧ RValIso (MapRel mapping) value value := by
  obtain ⟨inputs, result⟩ := called.scalar
  have scalar : left.toList.all IxIR1.RVal.isScalar = true := by
    rw [Array.all_toList]
    apply Array.all_eq_true.mpr
    intro i bound
    have valid := Array.all_eq_true.mp inputs i bound
    cases valueAt : left[i] <;> simp_all only [RVal.isScalar, IxIR1.RVal.isScalar]
  have same : left = right := Array.toList_inj.mp (values.eq_of_allScalar scalar)
  subst right
  refine ⟨called, ?_⟩
  cases value <;> simp_all [RVal.isScalar] <;> constructor

theorem FrameRel.noCredits {mapping : Array Nat} {left right : Frame}
    (related : FrameRel mapping left right) (cleared : NoLiveCredits left) :
    NoLiveCredits right := by
  change right.credits.any Option.isSome = false
  change left.credits.any Option.isSome = false at cleared
  rw [← Array.any_toList] at cleared ⊢
  rw [← related.credits.any]
  exact cleared

theorem FrameRel.presentCredits {mapping : Array Nat} {left right : Frame}
    (related : FrameRel mapping left right) : left.presentCredits = right.presentCredits := by
  simp only [Frame.presentCredits, creditPresentCount_eq_countP, ← Array.countP_toList]
  exact related.credits.weight

theorem FrameRel.creditLookup {mapping : Array Nat} {left right : Frame}
    (related : FrameRel mapping left right) {index : Nat} {credit : Credit}
    (lookedUp : CreditLookup left index credit) :
    ∃ target, CreditLookup right index target ∧ CreditRel credit target := by
  have found := (CreditTake.of_lookup lookedUp).target_eq.2
  obtain ⟨target, targetAt, credits⟩ := related.credits.get? (by simpa using found)
  exact ⟨target, .of_getElem (by simpa using targetAt), credits⟩

theorem FrameRel.creditTake {mapping : Array Nat} {left right after : Frame}
    (related : FrameRel mapping left right) {index : Nat} {credit : Credit}
    (taken : CreditTake left index after credit) :
    ∃ target targetCredit, CreditTake right index target targetCredit ∧
      FrameRel mapping after target ∧ CreditRel credit targetCredit := by
  obtain ⟨rfl, found⟩ := taken.target_eq
  obtain ⟨targetCredit, targetAt, credits⟩ := related.credits.get? (by simpa using found)
  refine ⟨_, targetCredit, .of_lookup (.of_getElem (by simpa using targetAt)), ?_, credits⟩
  exact { related with
    credits := by
      simpa only [Array.toList_setIfInBounds] using related.credits.setNone index }

theorem FrameRel.creditSequence {mapping : Array Nat} {left right after : Frame}
    (related : FrameRel mapping left right) {indices : List Nat} {credits : List Credit}
    (taken : CreditTakeSequence left indices after credits) :
    ∃ target targetCredits, CreditTakeSequence right indices target targetCredits ∧
      FrameRel mapping after target ∧ CreditsRel (credits.map some) (targetCredits.map some) := by
  induction taken generalizing right with
  | nil => exact ⟨right, [], .nil _, related, .nil⟩
  | cons head tail ih =>
      obtain ⟨middle, targetCredit, first, frames, credit⟩ := related.creditTake head
      obtain ⟨target, targetCredits, rest, frames, credits⟩ := ih frames
      exact ⟨target, targetCredit :: targetCredits, .cons first rest, frames,
        .cons (.live credit) credits⟩

theorem FrameRel.creditMany {mapping : Array Nat} {left right after : Frame}
    (related : FrameRel mapping left right) {indices : Array Nat} {credits : Array Credit}
    (taken : CreditTakeMany left indices after credits) :
    ∃ target targetCredits, CreditTakeMany right indices target targetCredits ∧
      FrameRel mapping after target ∧
      CreditsRel (credits.map some).toList (targetCredits.map some).toList := by
  obtain ⟨target, targetCredits, steps, frames, credits⟩ := related.creditSequence taken.sequence
  exact ⟨target, targetCredits.toArray, by simpa using steps.toMany,
    frames, by simpa using credits⟩

theorem FrameRel.edge {mapping : Array Nat} {left right after : Frame}
    (related : FrameRel mapping left right) {edge : Edge} {leftImplicit rightImplicit : Array RVal}
    (implicitValues : RValsIso (MapRel mapping) leftImplicit.toList rightImplicit.toList)
    (transferred : EdgeTransfer left edge leftImplicit after) :
    ∃ target, EdgeTransfer right edge rightImplicit target ∧ FrameRel mapping after target := by
  obtain ⟨values, credits, middle, block, resolved, taken, cleared, blockAt,
    valueArity, creditArity, rfl⟩ := transferred.parts
  obtain ⟨targetValues, targetResolved, valueRel⟩ := ReuseSim.resolveAtoms_iso related.values resolved
  obtain ⟨targetMiddle, targetCredits, targetTaken, middleRel, creditsRel⟩ := related.creditMany taken
  have combined : RValsIso (MapRel mapping) (leftImplicit ++ values).toList
      (rightImplicit ++ targetValues).toList := by
    simpa only [Array.toList_append] using implicitValues.append valueRel
  refine ⟨_, .of_parts targetResolved targetTaken (middleRel.noCredits cleared)
    (by rw [← middleRel.definition]; exact blockAt)
    (by rw [← values_size combined]; exact valueArity) ?_, ?_⟩
  · have sizes := creditsRel.lengths
    simp only [Array.length_toList, Array.size_map] at sizes
    omega
  · exact ⟨middleRel.definition, rfl, rfl, combined, creditsRel⟩

theorem ContinuationRel.presentCredits {mapping : Array Nat} {left right : Continuation}
    (related : ContinuationRel mapping left right) : left.presentCredits = right.presentCredits := by
  cases related with
  | resume frames => exact frames.presentCredits
  | applyMore frames values => exact frames.presentCredits

theorem StackRel.presentCredits {mapping : Array Nat} {left right : List Continuation}
    (related : StackRel mapping left right) :
    (left.map Continuation.presentCredits).sum = (right.map Continuation.presentCredits).sum := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, List.sum_cons, head.presentCredits, ih]

theorem reservedCredit {store : Store} {frame after : Frame} {stack : List Continuation}
    {index location : Nat} {credit : Credit}
    (owned : (Machine.mk store 0 (.running frame stack)).ReservationOwnership)
    (taken : CreditTake frame index after credit)
    (present : credit.presence = .present (some location)) : Store.EmptySlot store location := by
  apply owned.empty
  change location ∈ frame.reservations ++ stack.flatMap Continuation.reservations
  apply List.mem_append_left
  apply taken.reservations.mem_iff.mpr
  simp [Credit.reservation?, present]

end Ix.Compiler.IxIR2.CreditRefinement
