import IxCC.Lir.Proof.Run
import IxCC.Lir.Proof.Steps
import IxCC.Lir.Proof.Eval
import IxCC.Lir.Proof.Relabel
import IxCC.Lir.Proof.Split

/-! Required axiom fences for Lir's run loop and step lemmas (M2.5):
`Lir.run` is `Sem.runClocked` of its step, the fuel of `Lir.eval` outlasts
its clock (`runs_eval`, `eval_mono`), the width-64 evaluation equations,
the steps of a frame, and relabelled programs running in lock step
(`ProgSim.lockStep`) with edge splitting one such relabelling
(`split_sim`). Generated from the proof modules' public theorems; expected
messages are preserved verbatim. -/

/-- info: 'IxCC.Lir.semStep_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.semStep_next

/-- info: 'IxCC.Lir.semStep_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.semStep_fail

/-- info: 'IxCC.Lir.semStep_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.semStep_trap

/-- info: 'IxCC.Lir.semStep_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.semStep_done

/-- info: 'IxCC.Lir.run_eq_runClocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.run_eq_runClocked

/-- info: 'IxCC.Lir.eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.eval_eq

/-- info: 'IxCC.Lir.foldl_add_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lir.foldl_add_eq

/-- info: 'IxCC.Lir.Func.size_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Func.size_eq

/-- info: 'IxCC.Lir.Program.size_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Program.size_eq

/-- info: 'IxCC.Lir.sum_take_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.sum_take_le

/-- info: 'IxCC.Lir.le_sum_of_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.le_sum_of_getElem?

/-- info: 'IxCC.Lir.Func.before_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Func.before_le

/-- info: 'IxCC.Lir.Func.before_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lir.Func.before_succ

/-- info: 'IxCC.Lir.Func.before_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Func.before_mono

/-- info: 'IxCC.Lir.Func.bodyAt_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lir.Func.bodyAt_eq

/-- info: 'IxCC.Lir.Func.at_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Func.at_lt

/-- info: 'IxCC.Lir.Func.left_le' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Lir.Func.left_le

/-- info: 'IxCC.Lir.Func.left_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Func.left_succ

/-- info: 'IxCC.Lir.Func.left_fwd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Func.left_fwd

/-- info: 'IxCC.Lir.Func.left_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Func.left_pos

/-- info: 'IxCC.Lir.Program.left_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Program.left_le

/-- info: 'IxCC.Lir.Program.left_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lir.Program.left_of

/-- info: 'IxCC.Lir.Move.potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Move.potential

/-- info: 'IxCC.Lir.fuel_enough' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.fuel_enough

/-- info: 'IxCC.Lir.takeEdge_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.takeEdge_next

/-- info: 'IxCC.Lir.edge_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.edge_move

/-- info: 'IxCC.Lir.step_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_move

/-- info: 'IxCC.Lir.potential_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.potential_step

/-- info: 'IxCC.Lir.potential_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.potential_single

/-- info: 'IxCC.Lir.runs_of_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.runs_of_potential

/-- info: 'IxCC.Lir.runs_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.runs_eval

/-- info: 'IxCC.Lir.eval_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.eval_mono

/-- info: 'IxCC.Lir.env_insert_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.env_insert_self

/-- info: 'IxCC.Lir.env_insert_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.env_insert_ne

/-- info: 'IxCC.Lir.env_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.env_empty

/-- info: 'IxCC.Lir.env_insert_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.env_insert_get

/-- info: 'IxCC.Lir.step_stmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_stmt

/-- info: 'IxCC.Lir.step_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_call

/-- info: 'IxCC.Lir.star_stmts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.star_stmts

/-- info: 'IxCC.Lir.takeEdge_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.takeEdge_ok

/-- info: 'IxCC.Lir.step_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_term

/-- info: 'IxCC.Lir.step_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_jump

/-- info: 'IxCC.Lir.step_br' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_br

/-- info: 'IxCC.Lir.step_brOvf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_brOvf

/-- info: 'IxCC.Lir.step_ret_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_ret_done

/-- info: 'IxCC.Lir.step_ret_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_ret_caller

/-- info: 'IxCC.Lir.step_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_tail

/-- info: 'IxCC.Lir.step_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_fail

/-- info: 'IxCC.Lir.step_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_trap

/-- info: 'IxCC.Lir.fails_of_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.fails_of_star

/-- info: 'IxCC.Lir.jump_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.jump_at

/-- info: 'IxCC.Lir.br_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.br_at

/-- info: 'IxCC.Lir.brOvf_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.brOvf_at

/-- info: 'IxCC.Lir.fail_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.fail_at

/-- info: 'IxCC.Lir.trap_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.trap_at

/-- info: 'IxCC.Lir.stmts_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.stmts_at

/-- info: 'IxCC.Lir.star_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.star_of_step

/-- info: 'IxCC.Lir.evalArgs_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.evalArgs_nil

/-- info: 'IxCC.Lir.evalArgs_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.evalArgs_cons

/-- info: 'IxCC.Lir.Arg.eval_imm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Arg.eval_imm

/-- info: 'IxCC.Lir.Arg.eval_v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Arg.eval_v

/-- info: 'IxCC.Lir.option_pure' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Lir.option_pure

/-- info: 'IxCC.Lir.trunc64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.trunc64

/-- info: 'IxCC.Lir.bin_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.bin_add

/-- info: 'IxCC.Lir.bin_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.bin_sub

/-- info: 'IxCC.Lir.bin_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.bin_and

/-- info: 'IxCC.Lir.bin_or' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.bin_or

/-- info: 'IxCC.Lir.bin_xor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.bin_xor

/-- info: 'IxCC.Lir.bin_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.bin_mul

/-- info: 'IxCC.Lir.bin_shl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.bin_shl

/-- info: 'IxCC.Lir.bin_shr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.bin_shr

/-- info: 'IxCC.Lir.bin_udiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.bin_udiv

/-- info: 'IxCC.Lir.bin_urem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.bin_urem

/-- info: 'IxCC.Lir.holds_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.holds_eq

/-- info: 'IxCC.Lir.holds_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.holds_ne

/-- info: 'IxCC.Lir.holds_ult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.holds_ult

/-- info: 'IxCC.Lir.holds_ule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.holds_ule

/-- info: 'IxCC.Lir.holds_ugt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.holds_ugt

/-- info: 'IxCC.Lir.holds_uge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.holds_uge

/-- info: 'IxCC.Lir.holds_tz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.holds_tz

/-- info: 'IxCC.Lir.holds_tnz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.holds_tnz

/-- info: 'IxCC.Lir.holds_slt_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.holds_slt_zero

/-- info: 'IxCC.Lir.and63_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.and63_one

/-- info: 'IxCC.Lir.ofNat_one_word' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Lir.ofNat_one_word

/-- info: 'IxCC.Lir.ofNat_zero_word' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Lir.ofNat_zero_word

/-- info: 'IxCC.Lir.one_and63' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.one_and63

/-- info: 'IxCC.Lir.dispWord_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lir.dispWord_one

/-- info: 'IxCC.Lir.dispWord_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lir.dispWord_zero

/-- info: 'IxCC.Lir.scale_one' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Lir.scale_one

/-- info: 'IxCC.Lir.dispWord_ofNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.dispWord_ofNat

/-- info: 'IxCC.Lir.dispWord_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.dispWord_neg

/-- info: 'IxCC.Lir.takeEdge_next_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.takeEdge_next_full

/-- info: 'IxCC.Lir.step_next_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_next_cases

/-- info: 'IxCC.Lir.takeEdge_not_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.takeEdge_not_final

/-- info: 'IxCC.Lir.step_final_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_final_cases

/-- info: 'IxCC.Lir.ProgSim.enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.ProgSim.enter

/-- info: 'IxCC.Lir.step_term_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.step_term_ge

/-- info: 'IxCC.Lir.edgeSim_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.edgeSim_step

/-- info: 'IxCC.Lir.frameRel_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.frameRel_eq

/-- info: 'IxCC.Lir.ProgSim.lockStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.ProgSim.lockStep

/-- info: 'IxCC.Lir.funcSim_refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lir.funcSim_refl

/-- info: 'IxCC.Lir.newLabels_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.newLabels_get

/-- info: 'IxCC.Lir.newLabels_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lir.newLabels_length

/-- info: 'IxCC.Lir.newLabel_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.newLabel_succ

/-- info: 'IxCC.Lir.newLabel_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.newLabel_mono

/-- info: 'IxCC.Lir.newLabel_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.newLabel_le_iff

/-- info: 'IxCC.Lir.splitEdges_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.splitEdges_spec

/-- info: 'IxCC.Lir.filter_getElem_count' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lir.filter_getElem_count

/-- info: 'IxCC.Lir.emit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.emit_spec

/-- info: 'IxCC.Lir.split_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.split_core

/-- info: 'IxCC.Lir.split_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.split_sim
