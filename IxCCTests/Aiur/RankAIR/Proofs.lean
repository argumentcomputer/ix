import IxCCTests.Aiur.RankAIR.Fixtures
import IxCC.Aiur.AIR.Rank.Sound
import IxCC.Aiur.AIR.Rank.GraphProofs

namespace IxCCTests.Aiur.RankAIR

open _root_.Aiur (G gSize)
open IxCC.Aiur.AIR
open IxCC.Aiur.AIR.Rank

theorem first_checked : firstStep.check = true := by cbv
theorem limb_carry_checked : limbCarry.check = true := by cbv
theorem high_carry_checked : highCarry.check = true := by cbv
theorem last_checked : lastStep.check = true := by cbv
theorem long_gap_checked : longGap.check = true := by cbv

theorem overflow_rejected : overflow.check = false := by cbv
theorem wrong_binding_rejected : wrongBinding.check = false := by cbv
theorem aliased_limb_rejected : (⟨⟨65536, 0, 0⟩, limbs 0, limbs 65537⟩ : Edge).check = false := by cbv

theorem every_self_call_rejected (parent gap : Limbs) :
    ¬ Nonempty (Checked ⟨parent, gap, parent⟩) := checked_no_self parent gap

theorem every_two_cycle_rejected (left right leftGap rightGap : Limbs)
    (forward : Checked ⟨left, leftGap, right⟩) : ¬ Nonempty (Checked ⟨right, rightGap, left⟩) := by
  rintro ⟨backward⟩
  have first := forward.increases
  have second := backward.increases
  change left.value < right.value at first
  change right.value < left.value at second
  omega

theorem maximum_parent_rejected {entry : Edge} (maximum : entry.parent.value = rankBound - 1) :
    ¬ Nonempty (Checked entry) := by
  rintro ⟨checked⟩
  have small := checked.child_bound
  have grows := checked.increases
  omega

theorem range_maximum : RangeProvided (65535 : G) := (rangeProvided_iff _).mpr (by decide)
theorem range_overflow : ¬ RangeProvided (65536 : G) := by
  intro provided
  have small := (rangeProvided_iff _).mp provided
  exact (by decide : ¬ (65536 : G).n < limbBound) small

theorem field_negative_not_u16 : ¬ RangeProvided ((0 : G) - 1) := by
  intro provided
  have small := (rangeProvided_iff _).mp provided
  exact (by decide : ¬ ((0 : G) - 1).n < limbBound) small

theorem fixed_last_row : rangeValue 65535 = (65535 : G) := rangeValue_eq (by decide)

theorem scalar_channel_is_not_byte_pair : ([15, 7] : List G) ≠ [11, 0, 7] := by decide

theorem rank_survives_message : functionMessage 1 [7] [8] 0 ≠ functionMessage 1 [7] [8] 1 := by
  intro binding
  exact G.one_ne_zero (functionMessage_rank binding).symm

theorem public_zero_rank {rank : Limbs} (bounded : rank.Bounded)
    (binding : functionMessage 1 [7] [8] 0 = functionMessage 1 [7] [8] rank.packed) :
    rank.value = 0 := root_rank_zero bounded (functionMessage_rank binding).symm

theorem boundary_rank_may_decrease :
    callValue .bound (limbs 100) (limbs 0) (limbs 7).packed = (limbs 7).packed ∧
      (limbs 7).value < (limbs 100).value := by cbv

theorem balanced_overflow_impossible {demands : List (List G)} {providers : List RangeRow}
    (budget : demands.length < gSize.toNat) (requested : [15, (65536 : G)] ∈ demands) :
    ¬ RangeBalanced demands providers := by
  intro balanced
  exact range_overflow (rangeProvided_of_balance balanced budget requested)

theorem signed_provider_sum :
    rangeProviderSum [15, 7]
      [⟨⟨7, by decide⟩, 0 - 1⟩, ⟨⟨7, by decide⟩, 2⟩, ⟨⟨8, by decide⟩, 0 - 99⟩] = 1 := by cbv

theorem checked_ranked_obligation :
    IxCC.Aiur.Static.Advances ⟨0, 99, firstStep.parent.value⟩
      ⟨0, 42, firstStep.child.value⟩ :=
  (Checked.advances ⟨first_checked⟩ 0 (by decide) 99 42)

end IxCCTests.Aiur.RankAIR
