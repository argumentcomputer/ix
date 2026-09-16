import CompilatrixTests.Aiur.RankAIR.Proofs

/-! Exact ordinary-logic axiom sets for range balance, rank extraction,
selected expression evaluation, checked edges, and kernel regressions. -/

/-- info: 'Compilatrix.Aiur.AIR.Rank.Checked.advances' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.Checked.advances

/-- info: 'Compilatrix.Aiur.AIR.Rank.Checked.child_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.Checked.child_bound

/-- info: 'Compilatrix.Aiur.AIR.Rank.Checked.equation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.Checked.equation

/-- info: 'Compilatrix.Aiur.AIR.Rank.Checked.facts' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.Checked.facts

/-- info: 'Compilatrix.Aiur.AIR.Rank.Checked.increases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.Checked.increases

/-- info: 'Compilatrix.Aiur.AIR.Rank.Limbs.packed_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.Limbs.packed_n

/-- info: 'Compilatrix.Aiur.AIR.Rank.Limbs.rangeProvided_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.Limbs.rangeProvided_iff

/-- info: 'Compilatrix.Aiur.AIR.Rank.Limbs.ranges_of_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.Limbs.ranges_of_balance

/-- info: 'Compilatrix.Aiur.AIR.Rank.Limbs.value_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.Limbs.value_lt

/-- info: 'Compilatrix.Aiur.AIR.Rank.bound_message_rank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.bound_message_rank

/-- info: 'Compilatrix.Aiur.AIR.Rank.callExpr_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.callExpr_eval

/-- info: 'Compilatrix.Aiur.AIR.Rank.checked_no_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.checked_no_self

/-- info: 'Compilatrix.Aiur.AIR.Rank.functionArguments_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.functionArguments_eval

/-- info: 'Compilatrix.Aiur.AIR.Rank.functionMessage_rank' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.functionMessage_rank

/-- info: 'Compilatrix.Aiur.AIR.Rank.functionPull_weight' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.functionPull_weight

/-- info: 'Compilatrix.Aiur.AIR.Rank.gate_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.gate_eval

/-- info: 'Compilatrix.Aiur.AIR.Rank.gate_list_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.gate_list_eval

/-- info: 'Compilatrix.Aiur.AIR.Rank.mul_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.mul_n

/-- info: 'Compilatrix.Aiur.AIR.Rank.ofNat_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.ofNat_n

/-- info: 'Compilatrix.Aiur.AIR.Rank.orderedExpr_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.orderedExpr_eval

/-- info: 'Compilatrix.Aiur.AIR.Rank.ordered_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.ordered_eq

/-- info: 'Compilatrix.Aiur.AIR.Rank.ordered_from_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.ordered_from_range

/-- info: 'Compilatrix.Aiur.AIR.Rank.ordered_increases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.ordered_increases

/-- info: 'Compilatrix.Aiur.AIR.Rank.ordered_message_increases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.ordered_message_increases

/-- info: 'Compilatrix.Aiur.AIR.Rank.ordered_message_of_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.ordered_message_of_balance

/-- info: 'Compilatrix.Aiur.AIR.Rank.ordered_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.ordered_n

/-- info: 'Compilatrix.Aiur.AIR.Rank.ordered_no_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.ordered_no_self

/-- info: 'Compilatrix.Aiur.AIR.Rank.ordered_of_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.ordered_of_balance

/-- info: 'Compilatrix.Aiur.AIR.Rank.pack_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.pack_eval

/-- info: 'Compilatrix.Aiur.AIR.Rank.rangeProvided_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.rangeProvided_iff

/-- info: 'Compilatrix.Aiur.AIR.Rank.rangeProvided_of_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.rangeProvided_of_balance

/-- info: 'Compilatrix.Aiur.AIR.Rank.rangeProviderSum_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.rangeProviderSum_ne_zero

/-- info: 'Compilatrix.Aiur.AIR.Rank.rangeProviderSum_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.rangeProviderSum_zero

/-- info: 'Compilatrix.Aiur.AIR.Rank.rangePull_arguments' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.rangePull_arguments

/-- info: 'Compilatrix.Aiur.AIR.Rank.rangePull_weight' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.rangePull_weight

/-- info: 'Compilatrix.Aiur.AIR.Rank.rangePush_arguments' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.rangePush_arguments

/-- info: 'Compilatrix.Aiur.AIR.Rank.rangePush_weight' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.rangePush_weight

/-- info: 'Compilatrix.Aiur.AIR.Rank.rangeValue_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.rangeValue_eq

/-- info: 'Compilatrix.Aiur.AIR.Rank.rangeValue_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.rangeValue_n

/-- info: 'Compilatrix.Aiur.AIR.Rank.range_bound_of_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.range_bound_of_balance

/-- info: 'Compilatrix.Aiur.AIR.Rank.root_rank_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Rank.root_rank_zero

/-- info: 'CompilatrixTests.Aiur.RankAIR.aliased_limb_rejected' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.aliased_limb_rejected

/-- info: 'CompilatrixTests.Aiur.RankAIR.balanced_overflow_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.balanced_overflow_impossible

/-- info: 'CompilatrixTests.Aiur.RankAIR.boundary_rank_may_decrease' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.boundary_rank_may_decrease

/-- info: 'CompilatrixTests.Aiur.RankAIR.checked_ranked_obligation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.checked_ranked_obligation

/-- info: 'CompilatrixTests.Aiur.RankAIR.every_self_call_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.every_self_call_rejected

/-- info: 'CompilatrixTests.Aiur.RankAIR.every_two_cycle_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.every_two_cycle_rejected

/-- info: 'CompilatrixTests.Aiur.RankAIR.field_negative_not_u16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.field_negative_not_u16

/-- info: 'CompilatrixTests.Aiur.RankAIR.first_checked' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.first_checked

/-- info: 'CompilatrixTests.Aiur.RankAIR.fixed_last_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.fixed_last_row

/-- info: 'CompilatrixTests.Aiur.RankAIR.high_carry_checked' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.high_carry_checked

/-- info: 'CompilatrixTests.Aiur.RankAIR.last_checked' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.last_checked

/-- info: 'CompilatrixTests.Aiur.RankAIR.limb_carry_checked' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.limb_carry_checked

/-- info: 'CompilatrixTests.Aiur.RankAIR.long_gap_checked' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.long_gap_checked

/-- info: 'CompilatrixTests.Aiur.RankAIR.maximum_parent_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.maximum_parent_rejected

/-- info: 'CompilatrixTests.Aiur.RankAIR.overflow_rejected' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.overflow_rejected

/-- info: 'CompilatrixTests.Aiur.RankAIR.public_zero_rank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.public_zero_rank

/-- info: 'CompilatrixTests.Aiur.RankAIR.range_maximum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.range_maximum

/-- info: 'CompilatrixTests.Aiur.RankAIR.range_overflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.range_overflow

/-- info: 'CompilatrixTests.Aiur.RankAIR.rank_survives_message' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.rank_survives_message

/-- info: 'CompilatrixTests.Aiur.RankAIR.scalar_channel_is_not_byte_pair' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.scalar_channel_is_not_byte_pair

/-- info: 'CompilatrixTests.Aiur.RankAIR.signed_provider_sum' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.signed_provider_sum

/-- info: 'CompilatrixTests.Aiur.RankAIR.wrong_binding_rejected' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.RankAIR.wrong_binding_rejected
