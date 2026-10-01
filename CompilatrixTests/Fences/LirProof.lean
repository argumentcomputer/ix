import Compilatrix.Lir.Proof.Run
import Compilatrix.Lir.Proof.Steps
import Compilatrix.Lir.Proof.Eval
import Compilatrix.Lir.Proof.Relabel
import Compilatrix.Lir.Proof.Split

/-! Required axiom fences for Lir's run loop and step lemmas (M2.5):
`Lir.run` is `Sem.runClocked` of its step, the fuel of `Lir.eval` outlasts
its clock (`runs_eval`, `eval_mono`), the width-64 evaluation equations,
the steps of a frame, and relabelled programs running in lock step
(`ProgSim.lockStep`) with edge splitting one such relabelling
(`split_sim`). Generated from the proof modules' public theorems; expected
messages are preserved verbatim. -/

/-- info: 'Compilatrix.Lir.semStep_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.semStep_next

/-- info: 'Compilatrix.Lir.semStep_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.semStep_fail

/-- info: 'Compilatrix.Lir.semStep_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.semStep_trap

/-- info: 'Compilatrix.Lir.semStep_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.semStep_done

/-- info: 'Compilatrix.Lir.run_eq_runClocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.run_eq_runClocked

/-- info: 'Compilatrix.Lir.eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.eval_eq

/-- info: 'Compilatrix.Lir.foldl_add_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Lir.foldl_add_eq

/-- info: 'Compilatrix.Lir.Func.size_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Func.size_eq

/-- info: 'Compilatrix.Lir.Program.size_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Program.size_eq

/-- info: 'Compilatrix.Lir.sum_take_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.sum_take_le

/-- info: 'Compilatrix.Lir.le_sum_of_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.le_sum_of_getElem?

/-- info: 'Compilatrix.Lir.Func.before_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Func.before_le

/-- info: 'Compilatrix.Lir.Func.before_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Lir.Func.before_succ

/-- info: 'Compilatrix.Lir.Func.before_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Func.before_mono

/-- info: 'Compilatrix.Lir.Func.bodyAt_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Lir.Func.bodyAt_eq

/-- info: 'Compilatrix.Lir.Func.at_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Func.at_lt

/-- info: 'Compilatrix.Lir.Func.left_le' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Lir.Func.left_le

/-- info: 'Compilatrix.Lir.Func.left_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Func.left_succ

/-- info: 'Compilatrix.Lir.Func.left_fwd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Func.left_fwd

/-- info: 'Compilatrix.Lir.Func.left_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Func.left_pos

/-- info: 'Compilatrix.Lir.Program.left_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Program.left_le

/-- info: 'Compilatrix.Lir.Program.left_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Lir.Program.left_of

/-- info: 'Compilatrix.Lir.Move.potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Move.potential

/-- info: 'Compilatrix.Lir.fuel_enough' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.fuel_enough

/-- info: 'Compilatrix.Lir.takeEdge_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.takeEdge_next

/-- info: 'Compilatrix.Lir.edge_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.edge_move

/-- info: 'Compilatrix.Lir.step_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_move

/-- info: 'Compilatrix.Lir.potential_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.potential_step

/-- info: 'Compilatrix.Lir.potential_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.potential_single

/-- info: 'Compilatrix.Lir.runs_of_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.runs_of_potential

/-- info: 'Compilatrix.Lir.runs_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.runs_eval

/-- info: 'Compilatrix.Lir.eval_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.eval_mono

/-- info: 'Compilatrix.Lir.env_insert_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.env_insert_self

/-- info: 'Compilatrix.Lir.env_insert_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.env_insert_ne

/-- info: 'Compilatrix.Lir.env_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.env_empty

/-- info: 'Compilatrix.Lir.env_insert_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.env_insert_get

/-- info: 'Compilatrix.Lir.step_stmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_stmt

/-- info: 'Compilatrix.Lir.step_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_call

/-- info: 'Compilatrix.Lir.star_stmts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.star_stmts

/-- info: 'Compilatrix.Lir.takeEdge_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.takeEdge_ok

/-- info: 'Compilatrix.Lir.step_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_term

/-- info: 'Compilatrix.Lir.step_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_jump

/-- info: 'Compilatrix.Lir.step_br' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_br

/-- info: 'Compilatrix.Lir.step_brOvf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_brOvf

/-- info: 'Compilatrix.Lir.step_ret_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_ret_done

/-- info: 'Compilatrix.Lir.step_ret_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_ret_caller

/-- info: 'Compilatrix.Lir.step_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_tail

/-- info: 'Compilatrix.Lir.step_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_fail

/-- info: 'Compilatrix.Lir.step_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_trap

/-- info: 'Compilatrix.Lir.fails_of_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.fails_of_star

/-- info: 'Compilatrix.Lir.jump_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.jump_at

/-- info: 'Compilatrix.Lir.br_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.br_at

/-- info: 'Compilatrix.Lir.brOvf_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.brOvf_at

/-- info: 'Compilatrix.Lir.fail_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.fail_at

/-- info: 'Compilatrix.Lir.trap_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.trap_at

/-- info: 'Compilatrix.Lir.stmts_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.stmts_at

/-- info: 'Compilatrix.Lir.star_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.star_of_step

/-- info: 'Compilatrix.Lir.evalArgs_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.evalArgs_nil

/-- info: 'Compilatrix.Lir.evalArgs_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.evalArgs_cons

/-- info: 'Compilatrix.Lir.Arg.eval_imm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Arg.eval_imm

/-- info: 'Compilatrix.Lir.Arg.eval_v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Arg.eval_v

/-- info: 'Compilatrix.Lir.option_pure' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Lir.option_pure

/-- info: 'Compilatrix.Lir.trunc64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.trunc64

/-- info: 'Compilatrix.Lir.bin_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.bin_add

/-- info: 'Compilatrix.Lir.bin_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.bin_sub

/-- info: 'Compilatrix.Lir.bin_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.bin_and

/-- info: 'Compilatrix.Lir.bin_or' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.bin_or

/-- info: 'Compilatrix.Lir.bin_xor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.bin_xor

/-- info: 'Compilatrix.Lir.bin_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.bin_mul

/-- info: 'Compilatrix.Lir.bin_shl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.bin_shl

/-- info: 'Compilatrix.Lir.bin_shr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.bin_shr

/-- info: 'Compilatrix.Lir.bin_udiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.bin_udiv

/-- info: 'Compilatrix.Lir.bin_urem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.bin_urem

/-- info: 'Compilatrix.Lir.holds_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.holds_eq

/-- info: 'Compilatrix.Lir.holds_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.holds_ne

/-- info: 'Compilatrix.Lir.holds_ult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.holds_ult

/-- info: 'Compilatrix.Lir.holds_ule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.holds_ule

/-- info: 'Compilatrix.Lir.holds_ugt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.holds_ugt

/-- info: 'Compilatrix.Lir.holds_uge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.holds_uge

/-- info: 'Compilatrix.Lir.holds_tz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.holds_tz

/-- info: 'Compilatrix.Lir.holds_tnz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.holds_tnz

/-- info: 'Compilatrix.Lir.holds_slt_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.holds_slt_zero

/-- info: 'Compilatrix.Lir.and63_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.and63_one

/-- info: 'Compilatrix.Lir.ofNat_one_word' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Lir.ofNat_one_word

/-- info: 'Compilatrix.Lir.ofNat_zero_word' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Lir.ofNat_zero_word

/-- info: 'Compilatrix.Lir.one_and63' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.one_and63

/-- info: 'Compilatrix.Lir.dispWord_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Lir.dispWord_one

/-- info: 'Compilatrix.Lir.dispWord_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Lir.dispWord_zero

/-- info: 'Compilatrix.Lir.scale_one' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Lir.scale_one

/-- info: 'Compilatrix.Lir.dispWord_ofNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.dispWord_ofNat

/-- info: 'Compilatrix.Lir.dispWord_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.dispWord_neg

/-- info: 'Compilatrix.Lir.takeEdge_next_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.takeEdge_next_full

/-- info: 'Compilatrix.Lir.step_next_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_next_cases

/-- info: 'Compilatrix.Lir.takeEdge_not_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.takeEdge_not_final

/-- info: 'Compilatrix.Lir.step_final_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_final_cases

/-- info: 'Compilatrix.Lir.ProgSim.enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.ProgSim.enter

/-- info: 'Compilatrix.Lir.step_term_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.step_term_ge

/-- info: 'Compilatrix.Lir.edgeSim_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.edgeSim_step

/-- info: 'Compilatrix.Lir.frameRel_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.frameRel_eq

/-- info: 'Compilatrix.Lir.ProgSim.lockStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.ProgSim.lockStep

/-- info: 'Compilatrix.Lir.funcSim_refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Lir.funcSim_refl

/-- info: 'Compilatrix.Lir.newLabels_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.newLabels_get

/-- info: 'Compilatrix.Lir.newLabels_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Lir.newLabels_length

/-- info: 'Compilatrix.Lir.newLabel_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.newLabel_succ

/-- info: 'Compilatrix.Lir.newLabel_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.newLabel_mono

/-- info: 'Compilatrix.Lir.newLabel_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.newLabel_le_iff

/-- info: 'Compilatrix.Lir.splitEdges_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.splitEdges_spec

/-- info: 'Compilatrix.Lir.filter_getElem_count' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Lir.filter_getElem_count

/-- info: 'Compilatrix.Lir.emit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.emit_spec

/-- info: 'Compilatrix.Lir.split_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.split_core

/-- info: 'Compilatrix.Lir.split_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.split_sim
