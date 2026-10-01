import Compilatrix.Xv.Select.Proof.Place
import Compilatrix.Xv.Select.Proof.Exec
import Compilatrix.Xv.Select.Proof.Words
import Compilatrix.Xv.Select.Proof.Lin
import Compilatrix.Xv.Select.Proof.Monad
import Compilatrix.Xv.Select.Proof.Helpers
import Compilatrix.Xv.Select.Proof.Producer
import Compilatrix.Xv.Select.Proof.Assign
import Compilatrix.Xv.Select.Proof.Arith
import Compilatrix.Xv.Select.Proof.Shift
import Compilatrix.Xv.Select.Proof.Stmt
import Compilatrix.Xv.Select.Proof.Term
import Compilatrix.Xv.Select.Proof.Pending
import Compilatrix.Xv.Select.Proof.Block
import Compilatrix.Xv.Select.Proof.Program
import Compilatrix.Xv.Select.Proof.XvSteps
import Compilatrix.Xv.Select.Proof.Correct

/-! Required axiom fences for instruction selection's proof (M2.6b item 1):
placed Xv rows run on their operands' values (`execBound_run`) and each
row family computes its result (`exec_*`); word, sum and address lemmas;
selection's monad and folds (`foldLin_spec`, `buildAmode_spec`,
`sinkLoad?_spec`); the helpers, flag producers (`compareProducer_spec`),
assignment, arithmetic, shift, division, store, statement and terminator
rules (`selectAssign_ok`, `selectStmt_ok`, `selectTerm_ok`); pending
values of folded statements (`PendInv`); selected blocks, functions and
programs (`selectBlock_spec`, `select_spec`, `run_spec`); the lock-step
diagram (`select_lockstep`) and `Select.correct`, `Select.eval_eq`,
`Select.sim`, `Select.tsim` and their `Select.run` forms. Generated from the
proof modules' public theorems; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.Xv.Amode.map_id'' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Amode.map_id'

/-- info: 'Compilatrix.Xv.Bound.map_id'' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.map_id'

/-- info: 'Compilatrix.Xv.Placer.take_some' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Placer.take_some

/-- info: 'Compilatrix.Xv.Placer.use_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Placer.use_some

/-- info: 'Compilatrix.Xv.Placer.amode_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Placer.amode_some

/-- info: 'Compilatrix.Xv.Placer.bound_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Placer.bound_free

/-- info: 'Compilatrix.Xv.Placer.bound_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Placer.bound_some

/-- info: 'Compilatrix.Xv.Placer.bounds_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Placer.bounds_some

/-- info: 'Compilatrix.Xv.placeParts_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.placeParts_some

/-- info: 'Compilatrix.Xv.loadValues_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.loadValues_some

/-- info: 'Compilatrix.Xv.loadValues_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.loadValues_map

/-- info: 'Compilatrix.Xv.mem_eq_of_nodup_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.mem_eq_of_nodup_fst

/-- info: 'Compilatrix.Xv.guard_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.guard_vals

/-- info: 'Compilatrix.Xv.Bound.uses_regs_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.uses_regs_mem

/-- info: 'Compilatrix.Xv.Bound.fixedUse?_fixed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.fixedUse?_fixed

/-- info: 'Compilatrix.Xv.Bound.uses_regs_nodup' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.uses_regs_nodup

/-- info: 'Compilatrix.Xv.uses_regs_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.uses_regs_nodup

/-- info: 'Compilatrix.Xv.scratch_no_rsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.scratch_no_rsp

/-- info: 'Compilatrix.Xv.parts_map_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.parts_map_id

/-- info: 'Compilatrix.Xv.execBound_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.execBound_run

/-- info: 'Compilatrix.Xv.execSeq_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.execSeq_nil

/-- info: 'Compilatrix.Xv.execSeq_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.execSeq_cons

/-- info: 'Compilatrix.Xv.execSeq_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.execSeq_append

/-- info: 'Compilatrix.Xv.execSeq_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.execSeq_singleton

/-- info: 'Compilatrix.Xv.Amode.regs_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Amode.regs_length_le

/-- info: 'Compilatrix.Xv.Amode.evalV_toMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Amode.evalV_toMem

/-- info: 'Compilatrix.Xv.Bound.map_fst_eq_input_r' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.map_fst_eq_input_r

/-- info: 'Compilatrix.Xv.Bound.map_fst_eq_input_i' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.map_fst_eq_input_i

/-- info: 'Compilatrix.Xv.Bound.map_fst_eq_input_m' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.map_fst_eq_input_m

/-- info: 'Compilatrix.Xv.Bound.map_fst_eq_output' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.map_fst_eq_output

/-- info: 'Compilatrix.Xv.Bound.map_fst_eq_tied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.map_fst_eq_tied

/-- info: 'Compilatrix.Xv.Bound.map_fst_eq_memory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.map_fst_eq_memory

/-- info: 'Compilatrix.Xv.Bound.map_fst_eq_fixedUse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.map_fst_eq_fixedUse

/-- info: 'Compilatrix.Xv.Bound.map_fst_eq_fixedDef' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.map_fst_eq_fixedDef

/-- info: 'Compilatrix.Xv.Bound.map_fst_eq_fixedTied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.map_fst_eq_fixedTied

/-- info: 'Compilatrix.Xv.bound_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.bound_run

/-- info: 'Compilatrix.Xv.exec_op' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_op

/-- info: 'Compilatrix.Xv.op_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.op_run

/-- info: 'Compilatrix.Xv.execJcc_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.execJcc_of

/-- info: 'Compilatrix.Xv.Amode.evalV_defined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Amode.evalV_defined

/-- info: 'Compilatrix.Xv.XArg.valIn_defined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.XArg.valIn_defined

/-- info: 'Compilatrix.Xv.load_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.load_r

/-- info: 'Compilatrix.Xv.load_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.load_m

/-- info: 'Compilatrix.Xv.merge_allSet' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.merge_allSet

/-- info: 'Compilatrix.Xv.exec_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_zero

/-- info: 'Compilatrix.Xv.exec_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_move

/-- info: 'Compilatrix.Xv.exec_movImm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_movImm

/-- info: 'Compilatrix.Xv.aluBind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.aluBind

/-- info: 'Compilatrix.Xv.exec_aluR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_aluR

/-- info: 'Compilatrix.Xv.exec_aluI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_aluI

/-- info: 'Compilatrix.Xv.exec_aluM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_aluM

/-- info: 'Compilatrix.Xv.out_in_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.out_in_reg

/-- info: 'Compilatrix.Xv.out_in_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.out_in_mem

/-- info: 'Compilatrix.Xv.exec_movzxR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_movzxR

/-- info: 'Compilatrix.Xv.exec_mov32R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_mov32R

/-- info: 'Compilatrix.Xv.exec_movLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_movLoad

/-- info: 'Compilatrix.Xv.exec_movzxLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_movzxLoad

/-- info: 'Compilatrix.Xv.exec_lea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_lea

/-- info: 'Compilatrix.Xv.tied_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.tied_in

/-- info: 'Compilatrix.Xv.tied_in_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.tied_in_mem

/-- info: 'Compilatrix.Xv.exec_imulR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_imulR

/-- info: 'Compilatrix.Xv.exec_imulM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_imulM

/-- info: 'Compilatrix.Xv.exec_imulI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_imulI

/-- info: 'Compilatrix.Xv.exec_shiftI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_shiftI

/-- info: 'Compilatrix.Xv.exec_shiftC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_shiftC

/-- info: 'Compilatrix.Xv.exec_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_div

/-- info: 'Compilatrix.Xv.mem_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.mem_store

/-- info: 'Compilatrix.Xv.exec_storeR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_storeR

/-- info: 'Compilatrix.Xv.exec_storeI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_storeI

/-- info: 'Compilatrix.Xv.test_restrict' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.test_restrict

/-- info: 'Compilatrix.Xv.jccTaken_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.jccTaken_eq

/-- info: 'Compilatrix.Xv.Prod.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Prod.bind

/-- info: 'Compilatrix.Xv.Prod.exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Prod.exec

/-- info: 'Compilatrix.Xv.input_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.input_loads

/-- info: 'Compilatrix.Xv.need_input_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.need_input_le

/-- info: 'Compilatrix.Xv.parts2_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.parts2_run

/-- info: 'Compilatrix.Xv.slotArgs_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.slotArgs_two

/-- info: 'Compilatrix.Xv.bound_alu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.bound_alu

/-- info: 'Compilatrix.Xv.execJcc_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.execJcc_prod

/-- info: 'Compilatrix.Xv.input_isSlot' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.input_isSlot

/-- info: 'Compilatrix.Xv.input_defs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.input_defs

/-- info: 'Compilatrix.Xv.fused_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.fused_prod

/-- info: 'Compilatrix.Xv.exec_fusedCmov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_fusedCmov

/-- info: 'Compilatrix.Xv.exec_fusedSetcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.exec_fusedSetcc

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_lt

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_eq_self

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_truncate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_truncate_le

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_truncate_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_truncate_ge

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_mergeWrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_mergeWrite

/-- info: 'Compilatrix.Xv.Select.Proof.mergeWrite_wide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.mergeWrite_wide

/-- info: 'Compilatrix.Xv.Select.Proof.shiftCount_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.shiftCount_eq

/-- info: 'Compilatrix.Xv.Select.Proof.masked_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.masked_lt

/-- info: 'Compilatrix.Xv.Select.Proof.mod64_of_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.mod64_of_lt

/-- info: 'Compilatrix.Xv.Select.Proof.shl_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.shl_eq

/-- info: 'Compilatrix.Xv.Select.Proof.shr_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.shr_eq

/-- info: 'Compilatrix.Xv.Select.Proof.sext_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.sext_bits

/-- info: 'Compilatrix.Xv.Select.Proof.sar_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.sar_eq

/-- info: 'Compilatrix.Xv.Select.Proof.shiftResult_wide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.shiftResult_wide

/-- info: 'Compilatrix.Xv.Select.Proof.xor_two_pow_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.xor_two_pow_of_lt

/-- info: 'Compilatrix.Xv.Select.Proof.sext_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.sext_toNat

/-- info: 'Compilatrix.Xv.Select.Proof.sext_xor_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.sext_xor_add

/-- info: 'Compilatrix.Xv.Select.Proof.divQuot_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.divQuot_eq

/-- info: 'Compilatrix.Xv.Select.Proof.divRem_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.divRem_eq

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_zero

/-- info: 'Compilatrix.Xv.Select.Proof.readLittle_bit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.readLittle_bit

/-- info: 'Compilatrix.Xv.Select.Proof.rangeAllowed_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.rangeAllowed_le

/-- info: 'Compilatrix.Xv.Select.Proof.width_bytes_bits' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.width_bytes_bits

/-- info: 'Compilatrix.Xv.Select.Proof.read_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.read_prefix

/-- info: 'Compilatrix.Xv.Select.Proof.loadWord_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.loadWord_read

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_and

/-- info: 'Compilatrix.Xv.Select.Proof.holds_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.holds_congr

/-- info: 'Compilatrix.Xv.Select.Proof.holds_trunc_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.holds_trunc_right

/-- info: 'Compilatrix.Xv.Select.Proof.holds_trunc_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.holds_trunc_left

/-- info: 'Compilatrix.Xv.Select.Proof.cmp_swap_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.cmp_swap_test

/-- info: 'Compilatrix.Xv.Select.Proof.tz_narrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.tz_narrow

/-- info: 'Compilatrix.Xv.Select.Proof.tnz_narrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.tnz_narrow

/-- info: 'Compilatrix.Xv.Select.Proof.mov32_imm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.mov32_imm

/-- info: 'Compilatrix.Xv.Select.Proof.termsVal_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.termsVal_append

/-- info: 'Compilatrix.Xv.Select.Proof.termVal_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.termVal_scale

/-- info: 'Compilatrix.Xv.Select.Proof.termsVal_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.termsVal_scale

/-- info: 'Compilatrix.Xv.Select.Proof.dispWord_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.dispWord_add

/-- info: 'Compilatrix.Xv.Select.Proof.dispWord_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.dispWord_mul

/-- info: 'Compilatrix.Xv.Select.Proof.dispWord_negWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.dispWord_negWord

/-- info: 'Compilatrix.Xv.Select.Proof.linVal_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.linVal_add

/-- info: 'Compilatrix.Xv.Select.Proof.linVal_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.linVal_scale

/-- info: 'Compilatrix.Xv.Select.Proof.linVal_ofArg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.linVal_ofArg

/-- info: 'Compilatrix.Xv.Select.Proof.linVal_ofAddr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.linVal_ofAddr

/-- info: 'Compilatrix.Xv.Select.Proof.shl_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.shl_mul

/-- info: 'Compilatrix.Xv.Select.Proof.rhsLin_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.rhsLin_val

/-- info: 'Compilatrix.Xv.Select.Proof.termsVal_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.termsVal_split

/-- info: 'Compilatrix.Xv.Select.Proof.fold_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.fold_val

/-- info: 'Compilatrix.Xv.Select.Proof.termsVal_filter_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.termsVal_filter_nonzero

/-- info: 'Compilatrix.Xv.Select.Proof.dispWord_signed64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.dispWord_signed64

/-- info: 'Compilatrix.Xv.Select.Proof.disp32_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.disp32_eq

/-- info: 'Compilatrix.Xv.Select.Proof.scaleOf_word' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.scaleOf_word

/-- info: 'Compilatrix.Xv.Select.Proof.termVal_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.termVal_r

/-- info: 'Compilatrix.Xv.Select.Proof.baseVal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.baseVal_eq

/-- info: 'Compilatrix.Xv.Select.Proof.regIndex_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.regIndex_eq

/-- info: 'Compilatrix.Xv.Select.Proof.evalV_base_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.evalV_base_index

/-- info: 'Compilatrix.Xv.Select.Proof.encodeTerms_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.encodeTerms_val

/-- info: 'Compilatrix.Xv.Select.Proof.mergeTerms_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.mergeTerms_eq

/-- info: 'Compilatrix.Xv.Select.Proof.termVal_add_mult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.termVal_add_mult

/-- info: 'Compilatrix.Xv.Select.Proof.termVal_mult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.termVal_mult

/-- info: 'Compilatrix.Xv.Select.Proof.termsVal_map_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.termsVal_map_add

/-- info: 'Compilatrix.Xv.Select.Proof.mergeStep_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.mergeStep_val

/-- info: 'Compilatrix.Xv.Select.Proof.foldl_merge_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.foldl_merge_val

/-- info: 'Compilatrix.Xv.Select.Proof.mergeTerms_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.mergeTerms_val

/-- info: 'Compilatrix.Xv.Select.Proof.encode_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.encode_val

/-- info: 'Compilatrix.Xv.Select.Proof.linLow_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.linLow_add

/-- info: 'Compilatrix.Xv.Select.Proof.linLow_scale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.linLow_scale

/-- info: 'Compilatrix.Xv.Select.Proof.linLow_ofArg' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.linLow_ofArg

/-- info: 'Compilatrix.Xv.Select.Proof.linLow_ofAddr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.linLow_ofAddr

/-- info: 'Compilatrix.Xv.Select.Proof.linLow_rhsLin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.linLow_rhsLin

/-- info: 'Compilatrix.Xv.Select.Proof.linLow_fold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.linLow_fold

/-- info: 'Compilatrix.Xv.Select.Proof.base_mem_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.base_mem_regs

/-- info: 'Compilatrix.Xv.Select.Proof.encodeTerms_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.encodeTerms_regs

/-- info: 'Compilatrix.Xv.Select.Proof.mergeStep_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.mergeStep_regs

/-- info: 'Compilatrix.Xv.Select.Proof.foldl_merge_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.foldl_merge_regs

/-- info: 'Compilatrix.Xv.Select.Proof.encode_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.encode_regs

/-- info: 'Compilatrix.Xv.Select.Proof.encode_low' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.encode_low

/-- info: 'Compilatrix.Xv.Select.Proof.evalV_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.evalV_congr

/-- info: 'Compilatrix.Xv.Select.Proof.bind_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.bind_ok

/-- info: 'Compilatrix.Xv.Select.Proof.pure_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.pure_ok

/-- info: 'Compilatrix.Xv.Select.Proof.fireSt_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.fireSt_next

/-- info: 'Compilatrix.Xv.Select.Proof.fireSt_consumed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.fireSt_consumed

/-- info: 'Compilatrix.Xv.Select.Proof.fire_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.fire_run

/-- info: 'Compilatrix.Xv.Select.Proof.fresh_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.fresh_run

/-- info: 'Compilatrix.Xv.Select.Proof.consume_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.consume_run

/-- info: 'Compilatrix.Xv.Select.Proof.useCount_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.useCount_run

/-- info: 'Compilatrix.Xv.Select.Proof.read_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.read_run

/-- info: 'Compilatrix.Xv.Select.Proof.get_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.get_run

/-- info: 'Compilatrix.Xv.Select.Proof.singleUse_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.singleUse_run

/-- info: 'Compilatrix.Xv.Select.Proof.sitePos_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.sitePos_run

/-- info: 'Compilatrix.Xv.Select.Proof.pureBetween_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.pureBetween_run

/-- info: 'Compilatrix.Xv.Select.Proof.read_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.read_bind

/-- info: 'Compilatrix.Xv.Select.Proof.get_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.get_bind

/-- info: 'Compilatrix.Xv.Select.Proof.sitePos_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.sitePos_bind

/-- info: 'Compilatrix.Xv.Select.Proof.fire_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.fire_bind

/-- info: 'Compilatrix.Xv.Select.Proof.fresh_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.fresh_bind

/-- info: 'Compilatrix.Xv.Select.Proof.consume_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.consume_bind

/-- info: 'Compilatrix.Xv.Select.Proof.useCount_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.useCount_bind

/-- info: 'Compilatrix.Xv.Select.Proof.singleUse_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.singleUse_bind

/-- info: 'Compilatrix.Xv.Select.Proof.pureBetween_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.pureBetween_bind

/-- info: 'Compilatrix.Xv.Select.Proof.pure_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.pure_run

/-- info: 'Compilatrix.Xv.Select.Proof.pure_bind'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.pure_bind'

/-- info: 'Compilatrix.Xv.Select.Proof.unsupported_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.unsupported_ne

/-- info: 'Compilatrix.Xv.Select.Proof.Ext.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Ext.refl

/-- info: 'Compilatrix.Xv.Select.Proof.Ext.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Ext.trans

/-- info: 'Compilatrix.Xv.Select.Proof.Ext.of_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Ext.of_same

/-- info: 'Compilatrix.Xv.Select.Proof.Ext.of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Ext.of_le

/-- info: 'Compilatrix.Xv.Select.Proof.Ext.fire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Ext.fire

/-- info: 'Compilatrix.Xv.Select.Proof.Ext.fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Ext.fresh

/-- info: 'Compilatrix.Xv.Select.Proof.Ext.consumed_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Ext.consumed_sub

/-- info: 'Compilatrix.Xv.Select.Proof.Pend.left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Pend.left

/-- info: 'Compilatrix.Xv.Select.Proof.Pend.right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Pend.right

/-- info: 'Compilatrix.Xv.Select.Proof.Pend.same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Pend.same

/-- info: 'Compilatrix.Xv.Select.Proof.defStmt?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.defStmt?_spec

/-- info: 'Compilatrix.Xv.Select.Proof.FoldOk.folded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.FoldOk.folded

/-- info: 'Compilatrix.Xv.Select.Proof.foldOne_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.foldOne_spec

/-- info: 'Compilatrix.Xv.Select.Proof.FoldsTo.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.FoldsTo.refl

/-- info: 'Compilatrix.Xv.Select.Proof.foldLinFuel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.foldLinFuel_spec

/-- info: 'Compilatrix.Xv.Select.Proof.foldLin_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.foldLin_spec

/-- info: 'Compilatrix.Xv.Select.Proof.commitFold_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.commitFold_spec

/-- info: 'Compilatrix.Xv.Select.Proof.FoldsTo.ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.FoldsTo.ext

/-- info: 'Compilatrix.Xv.Select.Proof.FoldsTo.pend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.FoldsTo.pend

/-- info: 'Compilatrix.Xv.Select.Proof.buildAmode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.buildAmode_spec

/-- info: 'Compilatrix.Xv.Select.Proof.sinkLoad?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.sinkLoad?_spec

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_add

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_sub

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_mul

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_and'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_and'

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_or

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_xor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_xor

/-- info: 'Compilatrix.Xv.Select.Proof.alu_trunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.alu_trunc

/-- info: 'Compilatrix.Xv.Select.Proof.alu_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.alu_congr

/-- info: 'Compilatrix.Xv.Select.Proof.mul_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.mul_congr

/-- info: 'Compilatrix.Xv.Select.Proof.alu_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.alu_comm

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_low

/-- info: 'Compilatrix.Xv.Select.Proof.bits_opWidth' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.bits_opWidth

/-- info: 'Compilatrix.Xv.Select.Proof.opWidth_wide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.opWidth_wide

/-- info: 'Compilatrix.Xv.Select.Proof.opWidth_of_not_narrow' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.opWidth_of_not_narrow

/-- info: 'Compilatrix.Xv.Select.Proof.narrow_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.narrow_cases

/-- info: 'Compilatrix.Xv.Select.Proof.aluOf_mnemonic' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.aluOf_mnemonic

/-- info: 'Compilatrix.Xv.Select.Proof.aluOf_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.aluOf_eval

/-- info: 'Compilatrix.Xv.Select.Proof.aluOf_sub' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.aluOf_sub

/-- info: 'Compilatrix.Xv.Select.Proof.readsOf_nil' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.readsOf_nil

/-- info: 'Compilatrix.Xv.Select.Proof.readsOf_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.readsOf_cons

/-- info: 'Compilatrix.Xv.Select.Proof.readsOf_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.readsOf_append

/-- info: 'Compilatrix.Xv.Select.Proof.Agree.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Agree.mono

/-- info: 'Compilatrix.Xv.Select.Proof.Agree.get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Agree.get

/-- info: 'Compilatrix.Xv.Select.Proof.Agree.arg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Agree.arg

/-- info: 'Compilatrix.Xv.Select.Proof.Agree.args' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Agree.args

/-- info: 'Compilatrix.Xv.Select.Proof.Computes.single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Computes.single

/-- info: 'Compilatrix.Xv.Select.Proof.Computes.append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Computes.append

/-- info: 'Compilatrix.Xv.Select.Proof.Computes.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Computes.mono

/-- info: 'Compilatrix.Xv.Select.Proof.Computes.congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Computes.congr

/-- info: 'Compilatrix.Xv.Select.Proof.insert_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.insert_below

/-- info: 'Compilatrix.Xv.Select.Proof.insert_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.insert_ne

/-- info: 'Compilatrix.Xv.Select.Proof.valIn_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.valIn_above

/-- info: 'Compilatrix.Xv.Select.Proof.eval_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.eval_above

/-- info: 'Compilatrix.Xv.Select.Proof.evalArgs_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.evalArgs_above

/-- info: 'Compilatrix.Xv.Select.Proof.movImm_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.movImm_spec

/-- info: 'Compilatrix.Xv.Select.Proof.materialize_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.materialize_spec

/-- info: 'Compilatrix.Xv.Select.Proof.argReg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.argReg_spec

/-- info: 'Compilatrix.Xv.Select.Proof.argRegs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.argRegs_spec

/-- info: 'Compilatrix.Xv.Select.Proof.exec_truncTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.exec_truncTo

/-- info: 'Compilatrix.Xv.Select.Proof.readsOf_truncTo' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.readsOf_truncTo

/-- info: 'Compilatrix.Xv.Select.Proof.argTrunc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.argTrunc_spec

/-- info: 'Compilatrix.Xv.Select.Proof.aluImm_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.aluImm_spec

/-- info: 'Compilatrix.Xv.Select.Proof.mulImm_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.mulImm_spec

/-- info: 'Compilatrix.Xv.Select.Proof.tieOrder_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.tieOrder_spec

/-- info: 'Compilatrix.Xv.Select.Proof.narrowed_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.narrowed_spec

/-- info: 'Compilatrix.Xv.Select.Proof.narrow_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.narrow_val

/-- info: 'Compilatrix.Xv.Select.Proof.Decides.jcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Decides.jcc

/-- info: 'Compilatrix.Xv.Select.Proof.Decides.cmov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Decides.cmov

/-- info: 'Compilatrix.Xv.Select.Proof.Decides.setcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Decides.setcc

/-- info: 'Compilatrix.Xv.Select.Proof.valIn_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.valIn_m

/-- info: 'Compilatrix.Xv.Select.Proof.Agree.amode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Agree.amode

/-- info: 'Compilatrix.Xv.Select.Proof.producerArgs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.producerArgs_spec

/-- info: 'Compilatrix.Xv.Select.Proof.cmpArgs_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.cmpArgs_run

/-- info: 'Compilatrix.Xv.Select.Proof.v_uses' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.v_uses

/-- info: 'Compilatrix.Xv.Select.Proof.imm_uses' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.imm_uses

/-- info: 'Compilatrix.Xv.Select.Proof.cmp_sunk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.cmp_sunk

/-- info: 'Compilatrix.Xv.Select.Proof.cmp_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.cmp_reg

/-- info: 'Compilatrix.Xv.Select.Proof.test_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.test_self

/-- info: 'Compilatrix.Xv.Select.Proof.test_self_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.test_self_swap

/-- info: 'Compilatrix.Xv.Select.Proof.truncate_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.truncate_idem

/-- info: 'Compilatrix.Xv.Select.Proof.cmpProducer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.cmpProducer_spec

/-- info: 'Compilatrix.Xv.Select.Proof.tz_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.tz_flags

/-- info: 'Compilatrix.Xv.Select.Proof.tz_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.tz_comm

/-- info: 'Compilatrix.Xv.Select.Proof.tz_trunc_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.tz_trunc_left

/-- info: 'Compilatrix.Xv.Select.Proof.tz_narrow'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.tz_narrow'

/-- info: 'Compilatrix.Xv.Select.Proof.immFull?_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.immFull?_some

/-- info: 'Compilatrix.Xv.Select.Proof.testWidth_w64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.testWidth_w64

/-- info: 'Compilatrix.Xv.Select.Proof.testImm_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.testImm_spec

/-- info: 'Compilatrix.Xv.Select.Proof.testProducer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.testProducer_spec

/-- info: 'Compilatrix.Xv.Select.Proof.compareProducer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.compareProducer_spec

/-- info: 'Compilatrix.Xv.Select.Proof.Decides.above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Decides.above

/-- info: 'Compilatrix.Xv.Select.Proof.uses_v' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.uses_v

/-- info: 'Compilatrix.Xv.Select.Proof.Rhs.uses_select' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Rhs.uses_select

/-- info: 'Compilatrix.Xv.Select.Proof.move_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.move_ok

/-- info: 'Compilatrix.Xv.Select.Proof.movImm_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.movImm_ok

/-- info: 'Compilatrix.Xv.Select.Proof.lea_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.lea_ok

/-- info: 'Compilatrix.Xv.Select.Proof.loadWord_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.loadWord_inv

/-- info: 'Compilatrix.Xv.Select.Proof.signBit_lt' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.signBit_lt

/-- info: 'Compilatrix.Xv.Select.Proof.norm_signBit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.norm_signBit

/-- info: 'Compilatrix.Xv.Select.Proof.xor_signBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.xor_signBit

/-- info: 'Compilatrix.Xv.Select.Proof.sext_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.sext_tail

/-- info: 'Compilatrix.Xv.Select.Proof.selectLoad_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectLoad_ok

/-- info: 'Compilatrix.Xv.Select.Proof.Agree.above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Agree.above

/-- info: 'Compilatrix.Xv.Select.Proof.above_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.above_trans

/-- info: 'Compilatrix.Xv.Select.Proof.selectTest_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectTest_ok

/-- info: 'Compilatrix.Xv.Select.Proof.selectSelect_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectSelect_ok

/-- info: 'Compilatrix.Xv.Select.Proof.leaAdd?_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.leaAdd?_eq

/-- info: 'Compilatrix.Xv.Select.Proof.allM_useCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.allM_useCount

/-- info: 'Compilatrix.Xv.Select.Proof.leaTail_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.leaTail_spec

/-- info: 'Compilatrix.Xv.Select.Proof.linVal_disp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.linVal_disp

/-- info: 'Compilatrix.Xv.Select.Proof.leaAdd_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.leaAdd_ok

/-- info: 'Compilatrix.Xv.Select.Proof.leaAdd?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.leaAdd?_spec

/-- info: 'Compilatrix.Xv.Select.Proof.selectAlu_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectAlu_eq

/-- info: 'Compilatrix.Xv.Select.Proof.trunc_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.trunc_low

/-- info: 'Compilatrix.Xv.Select.Proof.alu_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.alu_close

/-- info: 'Compilatrix.Xv.Select.Proof.low_trunc_wo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.low_trunc_wo

/-- info: 'Compilatrix.Xv.Select.Proof.alu_lir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.alu_lir

/-- info: 'Compilatrix.Xv.Select.Proof.bin_uses_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.bin_uses_left

/-- info: 'Compilatrix.Xv.Select.Proof.bin_uses_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.bin_uses_right

/-- info: 'Compilatrix.Xv.Select.Proof.aluBody_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.aluBody_ok

/-- info: 'Compilatrix.Xv.Select.Proof.selectAlu_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectAlu_ok

/-- info: 'Compilatrix.Xv.Select.Proof.selectMul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectMul_eq

/-- info: 'Compilatrix.Xv.Select.Proof.mul_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.mul_close

/-- info: 'Compilatrix.Xv.Select.Proof.mul_lir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.mul_lir

/-- info: 'Compilatrix.Xv.Select.Proof.mulBody_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.mulBody_ok

/-- info: 'Compilatrix.Xv.Select.Proof.selectMul_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectMul_ok

/-- info: 'Compilatrix.Xv.Select.Proof.shiftOf_mnemonic' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.shiftOf_mnemonic

/-- info: 'Compilatrix.Xv.Select.Proof.shift_lir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.shift_lir

/-- info: 'Compilatrix.Xv.Select.Proof.shiftResult_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.shiftResult_count

/-- info: 'Compilatrix.Xv.Select.Proof.shiftCount_masked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.shiftCount_masked

/-- info: 'Compilatrix.Xv.Select.Proof.shiftResult_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.shiftResult_zero

/-- info: 'Compilatrix.Xv.Select.Proof.shift_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.shift_close

/-- info: 'Compilatrix.Xv.Select.Proof.selectShift_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectShift_eq

/-- info: 'Compilatrix.Xv.Select.Proof.shiftRow_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.shiftRow_ok

/-- info: 'Compilatrix.Xv.Select.Proof.shiftBody_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.shiftBody_ok

/-- info: 'Compilatrix.Xv.Select.Proof.selectShift_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectShift_ok

/-- info: 'Compilatrix.Xv.Select.Proof.divLo_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.divLo_spec

/-- info: 'Compilatrix.Xv.Select.Proof.divDivisor_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.divDivisor_spec

/-- info: 'Compilatrix.Xv.Select.Proof.div_lir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.div_lir

/-- info: 'Compilatrix.Xv.Select.Proof.div_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.div_ok

/-- info: 'Compilatrix.Xv.Select.Proof.selectDiv_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectDiv_ok

/-- info: 'Compilatrix.Xv.Select.Proof.byte_trunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.byte_trunc

/-- info: 'Compilatrix.Xv.Select.Proof.writeLittle_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.writeLittle_congr

/-- info: 'Compilatrix.Xv.Select.Proof.write?_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.write?_congr

/-- info: 'Compilatrix.Xv.Select.Proof.selectBin_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectBin_ok

/-- info: 'Compilatrix.Xv.Select.Proof.selectAssign_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectAssign_ok

/-- info: 'Compilatrix.Xv.Select.Proof.storeTail_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.storeTail_ok

/-- info: 'Compilatrix.Xv.Select.Proof.AssignOk.stmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.AssignOk.stmt

/-- info: 'Compilatrix.Xv.Select.Proof.selectStore_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectStore_ok

/-- info: 'Compilatrix.Xv.Select.Proof.selectStmt_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectStmt_ok

/-- info: 'Compilatrix.Xv.Select.Proof.selectCall_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectCall_spec

/-- info: 'Compilatrix.Xv.Select.Proof.argReg_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.argReg_gen

/-- info: 'Compilatrix.Xv.Select.Proof.argRegs_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.argRegs_gen

/-- info: 'Compilatrix.Xv.Select.Proof.edgeArgs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.edgeArgs_spec

/-- info: 'Compilatrix.Xv.Select.Proof.ovf_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.ovf_eval

/-- info: 'Compilatrix.Xv.Select.Proof.ovf_carry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.ovf_carry

/-- info: 'Compilatrix.Xv.Select.Proof.carry_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.carry_comm

/-- info: 'Compilatrix.Xv.Select.Proof.execJcc_alu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.execJcc_alu

/-- info: 'Compilatrix.Xv.Select.Proof.brOvf_jcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.brOvf_jcc

/-- info: 'Compilatrix.Xv.Select.Proof.ovf_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.ovf_general

/-- info: 'Compilatrix.Xv.Select.Proof.ovf_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.ovf_reg

/-- info: 'Compilatrix.Xv.Select.Proof.ovf_mat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.ovf_mat

/-- info: 'Compilatrix.Xv.Select.Proof.ovf_sunk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.ovf_sunk

/-- info: 'Compilatrix.Xv.Select.Proof.selectBrOvf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectBrOvf_spec

/-- info: 'Compilatrix.Xv.Select.Proof.edge_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.edge_rel

/-- info: 'Compilatrix.Xv.Select.Proof.Agree.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Agree.insert

/-- info: 'Compilatrix.Xv.Select.Proof.selectTerm_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectTerm_ok

/-- info: 'Compilatrix.Xv.Select.Proof.defSites_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.defSites_eq

/-- info: 'Compilatrix.Xv.Select.Proof.foldl_defStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.foldl_defStep

/-- info: 'Compilatrix.Xv.Select.Proof.defSites_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.defSites_spec

/-- info: 'Compilatrix.Xv.Select.Proof.defSites_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.defSites_unique

/-- info: 'Compilatrix.Xv.Select.Proof.mem_effectSites' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.mem_effectSites

/-- info: 'Compilatrix.Xv.Select.Proof.exec_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.exec_other

/-- info: 'Compilatrix.Xv.Select.Proof.Arg.eval_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Arg.eval_congr

/-- info: 'Compilatrix.Xv.Select.Proof.Addr.eval_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Addr.eval_congr

/-- info: 'Compilatrix.Xv.Select.Proof.Rhs.eval_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.Rhs.eval_congr

/-- info: 'Compilatrix.Xv.Select.Proof.window_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.window_succ

/-- info: 'Compilatrix.Xv.Select.Proof.window_ne_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.window_ne_nil

/-- info: 'Compilatrix.Xv.Select.Proof.stableFrom_snoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.stableFrom_snoc

/-- info: 'Compilatrix.Xv.Select.Proof.all_avoid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.all_avoid

/-- info: 'Compilatrix.Xv.Select.Proof.stableFrom_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.stableFrom_single

/-- info: 'Compilatrix.Xv.Select.Proof.PendInv.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.PendInv.zero

/-- info: 'Compilatrix.Xv.Select.Proof.pure_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.pure_succ

/-- info: 'Compilatrix.Xv.Select.Proof.pure_not_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.pure_not_effect

/-- info: 'Compilatrix.Xv.Select.Proof.PendInv.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.PendInv.step

/-- info: 'Compilatrix.Xv.Select.Proof.PendInv.call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.PendInv.call

/-- info: 'Compilatrix.Xv.Select.Proof.PendInv.pend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.PendInv.pend

/-- info: 'Compilatrix.Xv.Select.Proof.sbind_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.sbind_ok

/-- info: 'Compilatrix.Xv.Select.Proof.sget_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.sget_bind

/-- info: 'Compilatrix.Xv.Select.Proof.smodify_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.smodify_bind

/-- info: 'Compilatrix.Xv.Select.Proof.spure_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.spure_run

/-- info: 'Compilatrix.Xv.Select.Proof.blockCtx_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.blockCtx_ok

/-- info: 'Compilatrix.Xv.Select.Proof.selectStmt_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectStmt_ext

/-- info: 'Compilatrix.Xv.Select.Proof.zipIdx_take_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.zipIdx_take_succ

/-- info: 'Compilatrix.Xv.Select.Proof.selectStmts_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectStmts_spec

/-- info: 'Compilatrix.Xv.Select.Proof.selectBlock_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectBlock_spec

/-- info: 'Compilatrix.Xv.Select.Proof.tbind_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.tbind_ok

/-- info: 'Compilatrix.Xv.Select.Proof.foldl_max_ge' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.foldl_max_ge

/-- info: 'Compilatrix.Xv.Select.Proof.foldl_max_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.foldl_max_mem

/-- info: 'Compilatrix.Xv.Select.Proof.foldl_blocks_ge' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.foldl_blocks_ge

/-- info: 'Compilatrix.Xv.Select.Proof.foldl_blocks_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.foldl_blocks_mem

/-- info: 'Compilatrix.Xv.Select.Proof.maxVReg_params' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.maxVReg_params

/-- info: 'Compilatrix.Xv.Select.Proof.maxVReg_block' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.maxVReg_block

/-- info: 'Compilatrix.Xv.Select.Proof.ctxLow_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.ctxLow_block

/-- info: 'Compilatrix.Xv.Select.Proof.selectBlocks_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectBlocks_spec

/-- info: 'Compilatrix.Xv.Select.Proof.BlockSel.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.BlockSel.mono

/-- info: 'Compilatrix.Xv.Select.Proof.selectFunc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectFunc_spec

/-- info: 'Compilatrix.Xv.Select.Proof.selectFuncs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.selectFuncs_spec

/-- info: 'Compilatrix.Xv.Select.Proof.progSel_of_funcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.progSel_of_funcs

/-- info: 'Compilatrix.Xv.Select.Proof.select_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.select_spec

/-- info: 'Compilatrix.Xv.Select.Proof.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.run_spec

/-- info: 'Compilatrix.Xv.Select.Proof.xv_step_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.xv_step_inst

/-- info: 'Compilatrix.Xv.Select.Proof.xv_star_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.xv_star_seq

/-- info: 'Compilatrix.Xv.Select.Proof.xv_step_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.xv_step_call

/-- info: 'Compilatrix.Xv.Select.Proof.xv_step_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.xv_step_term

/-- info: 'Compilatrix.Xv.Select.Proof.off_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.off_succ

/-- info: 'Compilatrix.Xv.Select.Proof.body_split' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.body_split

/-- info: 'Compilatrix.Xv.Select.Proof.off_len' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.off_len

/-- info: 'Compilatrix.Xv.Select.Proof.avoids_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.avoids_body

/-- info: 'Compilatrix.Xv.Select.Proof.avoids_term' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.avoids_term

/-- info: 'Compilatrix.Xv.Select.Proof.EnvRel.agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.EnvRel.agree

/-- info: 'Compilatrix.Xv.Select.Proof.readsOf_avoid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.readsOf_avoid

/-- info: 'Compilatrix.Xv.Select.Proof.bindParams_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.bindParams_rel

/-- info: 'Compilatrix.Xv.Select.Proof.EnvRel.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.EnvRel.bind

/-- info: 'Compilatrix.Xv.Select.Proof.EnvRel.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.EnvRel.insert

/-- info: 'Compilatrix.Xv.Select.Proof.EnvRel.above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.EnvRel.above

/-- info: 'Compilatrix.Xv.Select.Proof.takeEdge_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.takeEdge_inv

/-- info: 'Compilatrix.Xv.Select.Proof.xv_takeEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.xv_takeEdge

/-- info: 'Compilatrix.Xv.Select.Proof.enter_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.enter_rel

/-- info: 'Compilatrix.Xv.Select.Proof.FrameRel.susp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.FrameRel.susp

/-- info: 'Compilatrix.Xv.Select.Proof.forall₂_susp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.forall₂_susp

/-- info: 'Compilatrix.Xv.Select.Proof.entry_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.entry_rel

/-- info: 'Compilatrix.Xv.Select.Proof.stmt_low' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.stmt_low

/-- info: 'Compilatrix.Xv.Select.Proof.term_low' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.term_low

/-- info: 'Compilatrix.Xv.Select.Proof.params_low' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.params_low

/-- info: 'Compilatrix.Xv.Select.Proof.consumed_dead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.consumed_dead

/-- info: 'Compilatrix.Xv.Select.Proof.stmt_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.stmt_next

/-- info: 'Compilatrix.Xv.Select.Proof.call_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.call_next

/-- info: 'Compilatrix.Xv.Select.Proof.term_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.term_setup

/-- info: 'Compilatrix.Xv.Select.Proof.pre_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.pre_star

/-- info: 'Compilatrix.Xv.Select.Proof.enter_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.enter_block

/-- info: 'Compilatrix.Xv.Select.Proof.edge_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.edge_next

/-- info: 'Compilatrix.Xv.Select.Proof.xv_term_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.xv_term_eq

/-- info: 'Compilatrix.Xv.Select.Proof.select_lockstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.select_lockstep

/-- info: 'Compilatrix.Xv.Select.Proof.initial_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.initial_rel

/-- info: 'Compilatrix.Xv.Select.Proof.prog_eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.prog_eval_eq

/-- info: 'Compilatrix.Xv.Select.Proof.prog_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.Proof.prog_sim

/-- info: 'Compilatrix.Xv.Select.eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.eval_eq

/-- info: 'Compilatrix.Xv.Select.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.sim

/-- info: 'Compilatrix.Xv.Select.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.correct

/-- info: 'Compilatrix.Xv.Select.tsim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.tsim

/-- info: 'Compilatrix.Xv.Select.run_eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.run_eval_eq

/-- info: 'Compilatrix.Xv.Select.run_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.run_sim

/-- info: 'Compilatrix.Xv.Select.run_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.run_correct
