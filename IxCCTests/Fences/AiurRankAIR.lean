import IxCCTests.Aiur.RankAIR.Proofs

/-! Exact ordinary-logic axiom sets for range balance, rank extraction,
selected expression evaluation, checked edges, and kernel regressions. -/

/-- info: 'IxCC.Aiur.AIR.Rank.Checked.advances' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.Checked.advances

/-- info: 'IxCC.Aiur.AIR.Rank.Checked.child_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.Checked.child_bound

/-- info: 'IxCC.Aiur.AIR.Rank.Checked.equation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.Checked.equation

/-- info: 'IxCC.Aiur.AIR.Rank.Checked.facts' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.Checked.facts

/-- info: 'IxCC.Aiur.AIR.Rank.Checked.increases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.Checked.increases

/-- info: 'IxCC.Aiur.AIR.Rank.Limbs.packed_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.Limbs.packed_n

/-- info: 'IxCC.Aiur.AIR.Rank.Limbs.rangeProvided_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.Limbs.rangeProvided_iff

/-- info: 'IxCC.Aiur.AIR.Rank.Limbs.ranges_of_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.Limbs.ranges_of_balance

/-- info: 'IxCC.Aiur.AIR.Rank.Limbs.value_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.Limbs.value_lt

/-- info: 'IxCC.Aiur.AIR.Rank.bound_message_rank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.bound_message_rank

/-- info: 'IxCC.Aiur.AIR.Rank.callExpr_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.callExpr_eval

/-- info: 'IxCC.Aiur.AIR.Rank.checked_no_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.checked_no_self

/-- info: 'IxCC.Aiur.AIR.Rank.functionArguments_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.functionArguments_eval

/-- info: 'IxCC.Aiur.AIR.Rank.functionMessage_rank' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.functionMessage_rank

/-- info: 'IxCC.Aiur.AIR.Rank.functionPull_weight' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.functionPull_weight

/-- info: 'IxCC.Aiur.AIR.Rank.gate_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.gate_eval

/-- info: 'IxCC.Aiur.AIR.Rank.gate_list_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.gate_list_eval

/-- info: 'IxCC.Aiur.AIR.Rank.mul_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.mul_n

/-- info: 'IxCC.Aiur.AIR.Rank.ofNat_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.ofNat_n

/-- info: 'IxCC.Aiur.AIR.Rank.orderedExpr_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.orderedExpr_eval

/-- info: 'IxCC.Aiur.AIR.Rank.ordered_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.ordered_eq

/-- info: 'IxCC.Aiur.AIR.Rank.ordered_from_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.ordered_from_range

/-- info: 'IxCC.Aiur.AIR.Rank.ordered_increases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.ordered_increases

/-- info: 'IxCC.Aiur.AIR.Rank.ordered_message_increases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.ordered_message_increases

/-- info: 'IxCC.Aiur.AIR.Rank.ordered_message_of_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.ordered_message_of_balance

/-- info: 'IxCC.Aiur.AIR.Rank.ordered_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.ordered_n

/-- info: 'IxCC.Aiur.AIR.Rank.ordered_no_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.ordered_no_self

/-- info: 'IxCC.Aiur.AIR.Rank.ordered_of_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.ordered_of_balance

/-- info: 'IxCC.Aiur.AIR.Rank.pack_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.pack_eval

/-- info: 'IxCC.Aiur.AIR.Rank.rangeProvided_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.rangeProvided_iff

/-- info: 'IxCC.Aiur.AIR.Rank.rangeProvided_of_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.rangeProvided_of_balance

/-- info: 'IxCC.Aiur.AIR.Rank.rangeProviderSum_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.rangeProviderSum_ne_zero

/-- info: 'IxCC.Aiur.AIR.Rank.rangeProviderSum_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.rangeProviderSum_zero

/-- info: 'IxCC.Aiur.AIR.Rank.rangePull_arguments' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.rangePull_arguments

/-- info: 'IxCC.Aiur.AIR.Rank.rangePull_weight' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.rangePull_weight

/-- info: 'IxCC.Aiur.AIR.Rank.rangePush_arguments' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.rangePush_arguments

/-- info: 'IxCC.Aiur.AIR.Rank.rangePush_weight' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.rangePush_weight

/-- info: 'IxCC.Aiur.AIR.Rank.rangeValue_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.rangeValue_eq

/-- info: 'IxCC.Aiur.AIR.Rank.rangeValue_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.rangeValue_n

/-- info: 'IxCC.Aiur.AIR.Rank.range_bound_of_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.range_bound_of_balance

/-- info: 'IxCC.Aiur.AIR.Rank.root_rank_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Rank.root_rank_zero

/-- info: 'IxCCTests.Aiur.RankAIR.aliased_limb_rejected' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.aliased_limb_rejected

/-- info: 'IxCCTests.Aiur.RankAIR.balanced_overflow_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.balanced_overflow_impossible

/-- info: 'IxCCTests.Aiur.RankAIR.boundary_rank_may_decrease' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.boundary_rank_may_decrease

/-- info: 'IxCCTests.Aiur.RankAIR.checked_ranked_obligation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.checked_ranked_obligation

/-- info: 'IxCCTests.Aiur.RankAIR.every_self_call_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.every_self_call_rejected

/-- info: 'IxCCTests.Aiur.RankAIR.every_two_cycle_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.every_two_cycle_rejected

/-- info: 'IxCCTests.Aiur.RankAIR.field_negative_not_u16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.field_negative_not_u16

/-- info: 'IxCCTests.Aiur.RankAIR.first_checked' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.first_checked

/-- info: 'IxCCTests.Aiur.RankAIR.fixed_last_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.fixed_last_row

/-- info: 'IxCCTests.Aiur.RankAIR.high_carry_checked' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.high_carry_checked

/-- info: 'IxCCTests.Aiur.RankAIR.last_checked' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.last_checked

/-- info: 'IxCCTests.Aiur.RankAIR.limb_carry_checked' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.limb_carry_checked

/-- info: 'IxCCTests.Aiur.RankAIR.long_gap_checked' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.long_gap_checked

/-- info: 'IxCCTests.Aiur.RankAIR.maximum_parent_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.maximum_parent_rejected

/-- info: 'IxCCTests.Aiur.RankAIR.overflow_rejected' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.overflow_rejected

/-- info: 'IxCCTests.Aiur.RankAIR.public_zero_rank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.public_zero_rank

/-- info: 'IxCCTests.Aiur.RankAIR.range_maximum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.range_maximum

/-- info: 'IxCCTests.Aiur.RankAIR.range_overflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.range_overflow

/-- info: 'IxCCTests.Aiur.RankAIR.rank_survives_message' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.rank_survives_message

/-- info: 'IxCCTests.Aiur.RankAIR.scalar_channel_is_not_byte_pair' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.scalar_channel_is_not_byte_pair

/-- info: 'IxCCTests.Aiur.RankAIR.signed_provider_sum' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.signed_provider_sum

/-- info: 'IxCCTests.Aiur.RankAIR.wrong_binding_rejected' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.RankAIR.wrong_binding_rejected
