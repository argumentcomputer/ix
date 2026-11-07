import IxCC.Xv.Select.Proof.Place
import IxCC.Xv.Select.Proof.Exec
import IxCC.Xv.Select.Proof.Words
import IxCC.Xv.Select.Proof.Lin
import IxCC.Xv.Select.Proof.Monad
import IxCC.Xv.Select.Proof.Helpers
import IxCC.Xv.Select.Proof.Producer
import IxCC.Xv.Select.Proof.Assign
import IxCC.Xv.Select.Proof.Arith
import IxCC.Xv.Select.Proof.Shift
import IxCC.Xv.Select.Proof.Stmt
import IxCC.Xv.Select.Proof.Term
import IxCC.Xv.Select.Proof.Pending
import IxCC.Xv.Select.Proof.Block
import IxCC.Xv.Select.Proof.Program
import IxCC.Xv.Select.Proof.XvSteps
import IxCC.Xv.Select.Proof.Correct

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

/-- info: 'IxCC.Xv.Amode.map_id'' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Amode.map_id'

/-- info: 'IxCC.Xv.Bound.map_id'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.map_id'

/-- info: 'IxCC.Xv.Placer.take_some' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Placer.take_some

/-- info: 'IxCC.Xv.Placer.use_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Placer.use_some

/-- info: 'IxCC.Xv.Placer.amode_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Placer.amode_some

/-- info: 'IxCC.Xv.Placer.bound_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Placer.bound_free

/-- info: 'IxCC.Xv.Placer.bound_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Placer.bound_some

/-- info: 'IxCC.Xv.Placer.bounds_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Placer.bounds_some

/-- info: 'IxCC.Xv.placeParts_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.placeParts_some

/-- info: 'IxCC.Xv.loadValues_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.loadValues_some

/-- info: 'IxCC.Xv.loadValues_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.loadValues_map

/-- info: 'IxCC.Xv.mem_eq_of_nodup_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.mem_eq_of_nodup_fst

/-- info: 'IxCC.Xv.guard_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.guard_vals

/-- info: 'IxCC.Xv.Bound.uses_regs_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.uses_regs_mem

/-- info: 'IxCC.Xv.Bound.fixedUse?_fixed' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.fixedUse?_fixed

/-- info: 'IxCC.Xv.Bound.uses_regs_nodup' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.uses_regs_nodup

/-- info: 'IxCC.Xv.uses_regs_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.uses_regs_nodup

/-- info: 'IxCC.Xv.scratch_no_rsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.scratch_no_rsp

/-- info: 'IxCC.Xv.parts_map_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.parts_map_id

/-- info: 'IxCC.Xv.execBound_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.execBound_run

/-- info: 'IxCC.Xv.execSeq_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.execSeq_nil

/-- info: 'IxCC.Xv.execSeq_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.execSeq_cons

/-- info: 'IxCC.Xv.execSeq_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.execSeq_append

/-- info: 'IxCC.Xv.execSeq_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.execSeq_singleton

/-- info: 'IxCC.Xv.Amode.regs_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Amode.regs_length_le

/-- info: 'IxCC.Xv.Amode.evalV_toMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Amode.evalV_toMem

/-- info: 'IxCC.Xv.Bound.map_fst_eq_input_r' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.map_fst_eq_input_r

/-- info: 'IxCC.Xv.Bound.map_fst_eq_input_i' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.map_fst_eq_input_i

/-- info: 'IxCC.Xv.Bound.map_fst_eq_input_m' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.map_fst_eq_input_m

/-- info: 'IxCC.Xv.Bound.map_fst_eq_output' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.map_fst_eq_output

/-- info: 'IxCC.Xv.Bound.map_fst_eq_tied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.map_fst_eq_tied

/-- info: 'IxCC.Xv.Bound.map_fst_eq_memory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.map_fst_eq_memory

/-- info: 'IxCC.Xv.Bound.map_fst_eq_fixedUse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.map_fst_eq_fixedUse

/-- info: 'IxCC.Xv.Bound.map_fst_eq_fixedDef' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.map_fst_eq_fixedDef

/-- info: 'IxCC.Xv.Bound.map_fst_eq_fixedTied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.map_fst_eq_fixedTied

/-- info: 'IxCC.Xv.bound_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.bound_run

/-- info: 'IxCC.Xv.exec_op' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_op

/-- info: 'IxCC.Xv.op_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.op_run

/-- info: 'IxCC.Xv.execJcc_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.execJcc_of

/-- info: 'IxCC.Xv.Amode.evalV_defined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Amode.evalV_defined

/-- info: 'IxCC.Xv.XArg.valIn_defined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.XArg.valIn_defined

/-- info: 'IxCC.Xv.load_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.load_r

/-- info: 'IxCC.Xv.load_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.load_m

/-- info: 'IxCC.Xv.merge_allSet' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.merge_allSet

/-- info: 'IxCC.Xv.exec_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_zero

/-- info: 'IxCC.Xv.exec_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_move

/-- info: 'IxCC.Xv.exec_movImm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_movImm

/-- info: 'IxCC.Xv.aluBind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.aluBind

/-- info: 'IxCC.Xv.exec_aluR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_aluR

/-- info: 'IxCC.Xv.exec_aluI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_aluI

/-- info: 'IxCC.Xv.exec_aluM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_aluM

/-- info: 'IxCC.Xv.out_in_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.out_in_reg

/-- info: 'IxCC.Xv.out_in_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.out_in_mem

/-- info: 'IxCC.Xv.exec_movzxR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_movzxR

/-- info: 'IxCC.Xv.exec_mov32R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_mov32R

/-- info: 'IxCC.Xv.exec_movLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_movLoad

/-- info: 'IxCC.Xv.exec_movzxLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_movzxLoad

/-- info: 'IxCC.Xv.exec_lea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_lea

/-- info: 'IxCC.Xv.tied_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.tied_in

/-- info: 'IxCC.Xv.tied_in_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.tied_in_mem

/-- info: 'IxCC.Xv.exec_imulR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_imulR

/-- info: 'IxCC.Xv.exec_imulM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_imulM

/-- info: 'IxCC.Xv.exec_imulI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_imulI

/-- info: 'IxCC.Xv.exec_shiftI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_shiftI

/-- info: 'IxCC.Xv.exec_shiftC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_shiftC

/-- info: 'IxCC.Xv.exec_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_div

/-- info: 'IxCC.Xv.mem_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.mem_store

/-- info: 'IxCC.Xv.exec_storeR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_storeR

/-- info: 'IxCC.Xv.exec_storeI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_storeI

/-- info: 'IxCC.Xv.test_restrict' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.test_restrict

/-- info: 'IxCC.Xv.jccTaken_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.jccTaken_eq

/-- info: 'IxCC.Xv.Prod.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Prod.bind

/-- info: 'IxCC.Xv.Prod.exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Prod.exec

/-- info: 'IxCC.Xv.input_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.input_loads

/-- info: 'IxCC.Xv.need_input_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.need_input_le

/-- info: 'IxCC.Xv.parts2_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.parts2_run

/-- info: 'IxCC.Xv.slotArgs_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.slotArgs_two

/-- info: 'IxCC.Xv.bound_alu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.bound_alu

/-- info: 'IxCC.Xv.execJcc_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.execJcc_prod

/-- info: 'IxCC.Xv.input_isSlot' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.input_isSlot

/-- info: 'IxCC.Xv.input_defs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.input_defs

/-- info: 'IxCC.Xv.fused_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.fused_prod

/-- info: 'IxCC.Xv.exec_fusedCmov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_fusedCmov

/-- info: 'IxCC.Xv.exec_fusedSetcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.exec_fusedSetcc

/-- info: 'IxCC.Xv.Select.Proof.truncate_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_lt

/-- info: 'IxCC.Xv.Select.Proof.truncate_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_eq_self

/-- info: 'IxCC.Xv.Select.Proof.truncate_truncate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_truncate_le

/-- info: 'IxCC.Xv.Select.Proof.truncate_truncate_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_truncate_ge

/-- info: 'IxCC.Xv.Select.Proof.truncate_mergeWrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_mergeWrite

/-- info: 'IxCC.Xv.Select.Proof.mergeWrite_wide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.mergeWrite_wide

/-- info: 'IxCC.Xv.Select.Proof.shiftCount_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.shiftCount_eq

/-- info: 'IxCC.Xv.Select.Proof.masked_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.masked_lt

/-- info: 'IxCC.Xv.Select.Proof.mod64_of_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.mod64_of_lt

/-- info: 'IxCC.Xv.Select.Proof.shl_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.shl_eq

/-- info: 'IxCC.Xv.Select.Proof.shr_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.shr_eq

/-- info: 'IxCC.Xv.Select.Proof.sext_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.sext_bits

/-- info: 'IxCC.Xv.Select.Proof.sar_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.sar_eq

/-- info: 'IxCC.Xv.Select.Proof.shiftResult_wide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.shiftResult_wide

/-- info: 'IxCC.Xv.Select.Proof.xor_two_pow_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.xor_two_pow_of_lt

/-- info: 'IxCC.Xv.Select.Proof.sext_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.sext_toNat

/-- info: 'IxCC.Xv.Select.Proof.sext_xor_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.sext_xor_add

/-- info: 'IxCC.Xv.Select.Proof.divQuot_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.divQuot_eq

/-- info: 'IxCC.Xv.Select.Proof.divRem_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.divRem_eq

/-- info: 'IxCC.Xv.Select.Proof.truncate_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_zero

/-- info: 'IxCC.Xv.Select.Proof.readLittle_bit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.readLittle_bit

/-- info: 'IxCC.Xv.Select.Proof.rangeAllowed_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.rangeAllowed_le

/-- info: 'IxCC.Xv.Select.Proof.width_bytes_bits' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.width_bytes_bits

/-- info: 'IxCC.Xv.Select.Proof.read_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.read_prefix

/-- info: 'IxCC.Xv.Select.Proof.loadWord_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.loadWord_read

/-- info: 'IxCC.Xv.Select.Proof.truncate_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_and

/-- info: 'IxCC.Xv.Select.Proof.holds_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.holds_congr

/-- info: 'IxCC.Xv.Select.Proof.holds_trunc_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.holds_trunc_right

/-- info: 'IxCC.Xv.Select.Proof.holds_trunc_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.holds_trunc_left

/-- info: 'IxCC.Xv.Select.Proof.cmp_swap_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.cmp_swap_test

/-- info: 'IxCC.Xv.Select.Proof.tz_narrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.tz_narrow

/-- info: 'IxCC.Xv.Select.Proof.tnz_narrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.tnz_narrow

/-- info: 'IxCC.Xv.Select.Proof.mov32_imm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.mov32_imm

/-- info: 'IxCC.Xv.Select.Proof.termsVal_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.termsVal_append

/-- info: 'IxCC.Xv.Select.Proof.termVal_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.termVal_scale

/-- info: 'IxCC.Xv.Select.Proof.termsVal_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.termsVal_scale

/-- info: 'IxCC.Xv.Select.Proof.dispWord_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.dispWord_add

/-- info: 'IxCC.Xv.Select.Proof.dispWord_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.dispWord_mul

/-- info: 'IxCC.Xv.Select.Proof.dispWord_negWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.dispWord_negWord

/-- info: 'IxCC.Xv.Select.Proof.linVal_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.linVal_add

/-- info: 'IxCC.Xv.Select.Proof.linVal_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.linVal_scale

/-- info: 'IxCC.Xv.Select.Proof.linVal_ofArg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.linVal_ofArg

/-- info: 'IxCC.Xv.Select.Proof.linVal_ofAddr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.linVal_ofAddr

/-- info: 'IxCC.Xv.Select.Proof.shl_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.shl_mul

/-- info: 'IxCC.Xv.Select.Proof.rhsLin_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.rhsLin_val

/-- info: 'IxCC.Xv.Select.Proof.termsVal_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.termsVal_split

/-- info: 'IxCC.Xv.Select.Proof.fold_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.fold_val

/-- info: 'IxCC.Xv.Select.Proof.termsVal_filter_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.termsVal_filter_nonzero

/-- info: 'IxCC.Xv.Select.Proof.dispWord_signed64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.dispWord_signed64

/-- info: 'IxCC.Xv.Select.Proof.disp32_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.disp32_eq

/-- info: 'IxCC.Xv.Select.Proof.scaleOf_word' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.scaleOf_word

/-- info: 'IxCC.Xv.Select.Proof.termVal_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.termVal_r

/-- info: 'IxCC.Xv.Select.Proof.baseVal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.baseVal_eq

/-- info: 'IxCC.Xv.Select.Proof.regIndex_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.regIndex_eq

/-- info: 'IxCC.Xv.Select.Proof.evalV_base_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.evalV_base_index

/-- info: 'IxCC.Xv.Select.Proof.encodeTerms_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.encodeTerms_val

/-- info: 'IxCC.Xv.Select.Proof.mergeTerms_eq' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.mergeTerms_eq

/-- info: 'IxCC.Xv.Select.Proof.termVal_add_mult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.termVal_add_mult

/-- info: 'IxCC.Xv.Select.Proof.termVal_mult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.termVal_mult

/-- info: 'IxCC.Xv.Select.Proof.termsVal_map_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.termsVal_map_add

/-- info: 'IxCC.Xv.Select.Proof.mergeStep_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.mergeStep_val

/-- info: 'IxCC.Xv.Select.Proof.foldl_merge_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.foldl_merge_val

/-- info: 'IxCC.Xv.Select.Proof.mergeTerms_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.mergeTerms_val

/-- info: 'IxCC.Xv.Select.Proof.encode_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.encode_val

/-- info: 'IxCC.Xv.Select.Proof.linLow_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.linLow_add

/-- info: 'IxCC.Xv.Select.Proof.linLow_scale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.linLow_scale

/-- info: 'IxCC.Xv.Select.Proof.linLow_ofArg' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.linLow_ofArg

/-- info: 'IxCC.Xv.Select.Proof.linLow_ofAddr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.linLow_ofAddr

/-- info: 'IxCC.Xv.Select.Proof.linLow_rhsLin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.linLow_rhsLin

/-- info: 'IxCC.Xv.Select.Proof.linLow_fold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.linLow_fold

/-- info: 'IxCC.Xv.Select.Proof.base_mem_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.base_mem_regs

/-- info: 'IxCC.Xv.Select.Proof.encodeTerms_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.encodeTerms_regs

/-- info: 'IxCC.Xv.Select.Proof.mergeStep_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.mergeStep_regs

/-- info: 'IxCC.Xv.Select.Proof.foldl_merge_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.foldl_merge_regs

/-- info: 'IxCC.Xv.Select.Proof.encode_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.encode_regs

/-- info: 'IxCC.Xv.Select.Proof.encode_low' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.encode_low

/-- info: 'IxCC.Xv.Select.Proof.evalV_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.evalV_congr

/-- info: 'IxCC.Xv.Select.Proof.bind_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.bind_ok

/-- info: 'IxCC.Xv.Select.Proof.pure_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.pure_ok

/-- info: 'IxCC.Xv.Select.Proof.fireSt_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.fireSt_next

/-- info: 'IxCC.Xv.Select.Proof.fireSt_consumed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.fireSt_consumed

/-- info: 'IxCC.Xv.Select.Proof.fire_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.fire_run

/-- info: 'IxCC.Xv.Select.Proof.fresh_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.fresh_run

/-- info: 'IxCC.Xv.Select.Proof.consume_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.consume_run

/-- info: 'IxCC.Xv.Select.Proof.useCount_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.useCount_run

/-- info: 'IxCC.Xv.Select.Proof.read_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.read_run

/-- info: 'IxCC.Xv.Select.Proof.get_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.get_run

/-- info: 'IxCC.Xv.Select.Proof.singleUse_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.singleUse_run

/-- info: 'IxCC.Xv.Select.Proof.sitePos_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.sitePos_run

/-- info: 'IxCC.Xv.Select.Proof.pureBetween_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.pureBetween_run

/-- info: 'IxCC.Xv.Select.Proof.read_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.read_bind

/-- info: 'IxCC.Xv.Select.Proof.get_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.get_bind

/-- info: 'IxCC.Xv.Select.Proof.sitePos_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.sitePos_bind

/-- info: 'IxCC.Xv.Select.Proof.fire_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.fire_bind

/-- info: 'IxCC.Xv.Select.Proof.fresh_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.fresh_bind

/-- info: 'IxCC.Xv.Select.Proof.consume_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.consume_bind

/-- info: 'IxCC.Xv.Select.Proof.useCount_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.useCount_bind

/-- info: 'IxCC.Xv.Select.Proof.singleUse_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.singleUse_bind

/-- info: 'IxCC.Xv.Select.Proof.pureBetween_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.pureBetween_bind

/-- info: 'IxCC.Xv.Select.Proof.pure_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.pure_run

/-- info: 'IxCC.Xv.Select.Proof.pure_bind'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.pure_bind'

/-- info: 'IxCC.Xv.Select.Proof.unsupported_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.unsupported_ne

/-- info: 'IxCC.Xv.Select.Proof.Ext.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Ext.refl

/-- info: 'IxCC.Xv.Select.Proof.Ext.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Ext.trans

/-- info: 'IxCC.Xv.Select.Proof.Ext.of_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Ext.of_same

/-- info: 'IxCC.Xv.Select.Proof.Ext.of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Ext.of_le

/-- info: 'IxCC.Xv.Select.Proof.Ext.fire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Ext.fire

/-- info: 'IxCC.Xv.Select.Proof.Ext.fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Ext.fresh

/-- info: 'IxCC.Xv.Select.Proof.Ext.consumed_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Ext.consumed_sub

/-- info: 'IxCC.Xv.Select.Proof.Pend.left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Pend.left

/-- info: 'IxCC.Xv.Select.Proof.Pend.right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Pend.right

/-- info: 'IxCC.Xv.Select.Proof.Pend.same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Pend.same

/-- info: 'IxCC.Xv.Select.Proof.defStmt?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.defStmt?_spec

/-- info: 'IxCC.Xv.Select.Proof.FoldOk.folded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.FoldOk.folded

/-- info: 'IxCC.Xv.Select.Proof.foldOne_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.foldOne_spec

/-- info: 'IxCC.Xv.Select.Proof.FoldsTo.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.FoldsTo.refl

/-- info: 'IxCC.Xv.Select.Proof.foldLinFuel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.foldLinFuel_spec

/-- info: 'IxCC.Xv.Select.Proof.foldLin_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.foldLin_spec

/-- info: 'IxCC.Xv.Select.Proof.commitFold_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.commitFold_spec

/-- info: 'IxCC.Xv.Select.Proof.FoldsTo.ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.FoldsTo.ext

/-- info: 'IxCC.Xv.Select.Proof.FoldsTo.pend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.FoldsTo.pend

/-- info: 'IxCC.Xv.Select.Proof.buildAmode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.buildAmode_spec

/-- info: 'IxCC.Xv.Select.Proof.sinkLoad?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.sinkLoad?_spec

/-- info: 'IxCC.Xv.Select.Proof.truncate_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_add

/-- info: 'IxCC.Xv.Select.Proof.truncate_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_sub

/-- info: 'IxCC.Xv.Select.Proof.truncate_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_mul

/-- info: 'IxCC.Xv.Select.Proof.truncate_and'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_and'

/-- info: 'IxCC.Xv.Select.Proof.truncate_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_or

/-- info: 'IxCC.Xv.Select.Proof.truncate_xor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_xor

/-- info: 'IxCC.Xv.Select.Proof.alu_trunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.alu_trunc

/-- info: 'IxCC.Xv.Select.Proof.alu_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.alu_congr

/-- info: 'IxCC.Xv.Select.Proof.mul_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.mul_congr

/-- info: 'IxCC.Xv.Select.Proof.alu_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.alu_comm

/-- info: 'IxCC.Xv.Select.Proof.truncate_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_low

/-- info: 'IxCC.Xv.Select.Proof.bits_opWidth' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.bits_opWidth

/-- info: 'IxCC.Xv.Select.Proof.opWidth_wide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.opWidth_wide

/-- info: 'IxCC.Xv.Select.Proof.opWidth_of_not_narrow' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.opWidth_of_not_narrow

/-- info: 'IxCC.Xv.Select.Proof.narrow_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.narrow_cases

/-- info: 'IxCC.Xv.Select.Proof.aluOf_mnemonic' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.aluOf_mnemonic

/-- info: 'IxCC.Xv.Select.Proof.aluOf_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.aluOf_eval

/-- info: 'IxCC.Xv.Select.Proof.aluOf_sub' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.aluOf_sub

/-- info: 'IxCC.Xv.Select.Proof.readsOf_nil' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.readsOf_nil

/-- info: 'IxCC.Xv.Select.Proof.readsOf_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.readsOf_cons

/-- info: 'IxCC.Xv.Select.Proof.readsOf_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.readsOf_append

/-- info: 'IxCC.Xv.Select.Proof.Agree.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Agree.mono

/-- info: 'IxCC.Xv.Select.Proof.Agree.get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Agree.get

/-- info: 'IxCC.Xv.Select.Proof.Agree.arg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Agree.arg

/-- info: 'IxCC.Xv.Select.Proof.Agree.args' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Agree.args

/-- info: 'IxCC.Xv.Select.Proof.Computes.single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Computes.single

/-- info: 'IxCC.Xv.Select.Proof.Computes.append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Computes.append

/-- info: 'IxCC.Xv.Select.Proof.Computes.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Computes.mono

/-- info: 'IxCC.Xv.Select.Proof.Computes.congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Computes.congr

/-- info: 'IxCC.Xv.Select.Proof.insert_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.insert_below

/-- info: 'IxCC.Xv.Select.Proof.insert_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.insert_ne

/-- info: 'IxCC.Xv.Select.Proof.valIn_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.valIn_above

/-- info: 'IxCC.Xv.Select.Proof.eval_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.eval_above

/-- info: 'IxCC.Xv.Select.Proof.evalArgs_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.evalArgs_above

/-- info: 'IxCC.Xv.Select.Proof.movImm_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.movImm_spec

/-- info: 'IxCC.Xv.Select.Proof.materialize_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.materialize_spec

/-- info: 'IxCC.Xv.Select.Proof.argReg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.argReg_spec

/-- info: 'IxCC.Xv.Select.Proof.argRegs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.argRegs_spec

/-- info: 'IxCC.Xv.Select.Proof.exec_truncTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.exec_truncTo

/-- info: 'IxCC.Xv.Select.Proof.readsOf_truncTo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.readsOf_truncTo

/-- info: 'IxCC.Xv.Select.Proof.argTrunc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.argTrunc_spec

/-- info: 'IxCC.Xv.Select.Proof.aluImm_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.aluImm_spec

/-- info: 'IxCC.Xv.Select.Proof.mulImm_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.mulImm_spec

/-- info: 'IxCC.Xv.Select.Proof.tieOrder_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.tieOrder_spec

/-- info: 'IxCC.Xv.Select.Proof.narrowed_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.narrowed_spec

/-- info: 'IxCC.Xv.Select.Proof.narrow_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.narrow_val

/-- info: 'IxCC.Xv.Select.Proof.Decides.jcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Decides.jcc

/-- info: 'IxCC.Xv.Select.Proof.Decides.cmov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Decides.cmov

/-- info: 'IxCC.Xv.Select.Proof.Decides.setcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Decides.setcc

/-- info: 'IxCC.Xv.Select.Proof.valIn_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.valIn_m

/-- info: 'IxCC.Xv.Select.Proof.Agree.amode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Agree.amode

/-- info: 'IxCC.Xv.Select.Proof.producerArgs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.producerArgs_spec

/-- info: 'IxCC.Xv.Select.Proof.cmpArgs_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.cmpArgs_run

/-- info: 'IxCC.Xv.Select.Proof.v_uses' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.v_uses

/-- info: 'IxCC.Xv.Select.Proof.imm_uses' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.imm_uses

/-- info: 'IxCC.Xv.Select.Proof.cmp_sunk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.cmp_sunk

/-- info: 'IxCC.Xv.Select.Proof.cmp_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.cmp_reg

/-- info: 'IxCC.Xv.Select.Proof.test_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.test_self

/-- info: 'IxCC.Xv.Select.Proof.test_self_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.test_self_swap

/-- info: 'IxCC.Xv.Select.Proof.truncate_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.truncate_idem

/-- info: 'IxCC.Xv.Select.Proof.cmpProducer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.cmpProducer_spec

/-- info: 'IxCC.Xv.Select.Proof.tz_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.tz_flags

/-- info: 'IxCC.Xv.Select.Proof.tz_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.tz_comm

/-- info: 'IxCC.Xv.Select.Proof.tz_trunc_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.tz_trunc_left

/-- info: 'IxCC.Xv.Select.Proof.tz_narrow'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.tz_narrow'

/-- info: 'IxCC.Xv.Select.Proof.immFull?_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.immFull?_some

/-- info: 'IxCC.Xv.Select.Proof.testWidth_w64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.testWidth_w64

/-- info: 'IxCC.Xv.Select.Proof.testImm_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.testImm_spec

/-- info: 'IxCC.Xv.Select.Proof.testProducer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.testProducer_spec

/-- info: 'IxCC.Xv.Select.Proof.compareProducer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.compareProducer_spec

/-- info: 'IxCC.Xv.Select.Proof.Decides.above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Decides.above

/-- info: 'IxCC.Xv.Select.Proof.uses_v' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.uses_v

/-- info: 'IxCC.Xv.Select.Proof.Rhs.uses_select' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Rhs.uses_select

/-- info: 'IxCC.Xv.Select.Proof.move_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.move_ok

/-- info: 'IxCC.Xv.Select.Proof.movImm_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.movImm_ok

/-- info: 'IxCC.Xv.Select.Proof.lea_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.lea_ok

/-- info: 'IxCC.Xv.Select.Proof.loadWord_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.loadWord_inv

/-- info: 'IxCC.Xv.Select.Proof.signBit_lt' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.signBit_lt

/-- info: 'IxCC.Xv.Select.Proof.norm_signBit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.norm_signBit

/-- info: 'IxCC.Xv.Select.Proof.xor_signBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.xor_signBit

/-- info: 'IxCC.Xv.Select.Proof.sext_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.sext_tail

/-- info: 'IxCC.Xv.Select.Proof.selectLoad_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectLoad_ok

/-- info: 'IxCC.Xv.Select.Proof.Agree.above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Agree.above

/-- info: 'IxCC.Xv.Select.Proof.above_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.above_trans

/-- info: 'IxCC.Xv.Select.Proof.selectTest_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectTest_ok

/-- info: 'IxCC.Xv.Select.Proof.selectSelect_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectSelect_ok

/-- info: 'IxCC.Xv.Select.Proof.leaAdd?_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.leaAdd?_eq

/-- info: 'IxCC.Xv.Select.Proof.allM_useCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.allM_useCount

/-- info: 'IxCC.Xv.Select.Proof.leaTail_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.leaTail_spec

/-- info: 'IxCC.Xv.Select.Proof.linVal_disp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.linVal_disp

/-- info: 'IxCC.Xv.Select.Proof.leaAdd_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.leaAdd_ok

/-- info: 'IxCC.Xv.Select.Proof.leaAdd?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.leaAdd?_spec

/-- info: 'IxCC.Xv.Select.Proof.selectAlu_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectAlu_eq

/-- info: 'IxCC.Xv.Select.Proof.trunc_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.trunc_low

/-- info: 'IxCC.Xv.Select.Proof.alu_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.alu_close

/-- info: 'IxCC.Xv.Select.Proof.low_trunc_wo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.low_trunc_wo

/-- info: 'IxCC.Xv.Select.Proof.alu_lir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.alu_lir

/-- info: 'IxCC.Xv.Select.Proof.bin_uses_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.bin_uses_left

/-- info: 'IxCC.Xv.Select.Proof.bin_uses_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.bin_uses_right

/-- info: 'IxCC.Xv.Select.Proof.aluBody_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.aluBody_ok

/-- info: 'IxCC.Xv.Select.Proof.selectAlu_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectAlu_ok

/-- info: 'IxCC.Xv.Select.Proof.selectMul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectMul_eq

/-- info: 'IxCC.Xv.Select.Proof.mul_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.mul_close

/-- info: 'IxCC.Xv.Select.Proof.mul_lir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.mul_lir

/-- info: 'IxCC.Xv.Select.Proof.mulBody_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.mulBody_ok

/-- info: 'IxCC.Xv.Select.Proof.selectMul_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectMul_ok

/-- info: 'IxCC.Xv.Select.Proof.shiftOf_mnemonic' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.shiftOf_mnemonic

/-- info: 'IxCC.Xv.Select.Proof.shift_lir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.shift_lir

/-- info: 'IxCC.Xv.Select.Proof.shiftResult_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.shiftResult_count

/-- info: 'IxCC.Xv.Select.Proof.shiftCount_masked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.shiftCount_masked

/-- info: 'IxCC.Xv.Select.Proof.shiftResult_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.shiftResult_zero

/-- info: 'IxCC.Xv.Select.Proof.shift_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.shift_close

/-- info: 'IxCC.Xv.Select.Proof.selectShift_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectShift_eq

/-- info: 'IxCC.Xv.Select.Proof.shiftRow_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.shiftRow_ok

/-- info: 'IxCC.Xv.Select.Proof.shiftBody_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.shiftBody_ok

/-- info: 'IxCC.Xv.Select.Proof.selectShift_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectShift_ok

/-- info: 'IxCC.Xv.Select.Proof.divLo_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.divLo_spec

/-- info: 'IxCC.Xv.Select.Proof.divDivisor_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.divDivisor_spec

/-- info: 'IxCC.Xv.Select.Proof.div_lir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.div_lir

/-- info: 'IxCC.Xv.Select.Proof.div_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.div_ok

/-- info: 'IxCC.Xv.Select.Proof.selectDiv_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectDiv_ok

/-- info: 'IxCC.Xv.Select.Proof.byte_trunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.byte_trunc

/-- info: 'IxCC.Xv.Select.Proof.writeLittle_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.writeLittle_congr

/-- info: 'IxCC.Xv.Select.Proof.write?_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.write?_congr

/-- info: 'IxCC.Xv.Select.Proof.selectBin_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectBin_ok

/-- info: 'IxCC.Xv.Select.Proof.selectAssign_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectAssign_ok

/-- info: 'IxCC.Xv.Select.Proof.storeTail_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.storeTail_ok

/-- info: 'IxCC.Xv.Select.Proof.AssignOk.stmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.AssignOk.stmt

/-- info: 'IxCC.Xv.Select.Proof.selectStore_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectStore_ok

/-- info: 'IxCC.Xv.Select.Proof.selectStmt_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectStmt_ok

/-- info: 'IxCC.Xv.Select.Proof.selectCall_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectCall_spec

/-- info: 'IxCC.Xv.Select.Proof.argReg_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.argReg_gen

/-- info: 'IxCC.Xv.Select.Proof.argRegs_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.argRegs_gen

/-- info: 'IxCC.Xv.Select.Proof.edgeArgs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.edgeArgs_spec

/-- info: 'IxCC.Xv.Select.Proof.ovf_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.ovf_eval

/-- info: 'IxCC.Xv.Select.Proof.ovf_carry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.ovf_carry

/-- info: 'IxCC.Xv.Select.Proof.carry_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.carry_comm

/-- info: 'IxCC.Xv.Select.Proof.execJcc_alu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.execJcc_alu

/-- info: 'IxCC.Xv.Select.Proof.brOvf_jcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.brOvf_jcc

/-- info: 'IxCC.Xv.Select.Proof.ovf_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.ovf_general

/-- info: 'IxCC.Xv.Select.Proof.ovf_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.ovf_reg

/-- info: 'IxCC.Xv.Select.Proof.ovf_mat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.ovf_mat

/-- info: 'IxCC.Xv.Select.Proof.ovf_sunk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.ovf_sunk

/-- info: 'IxCC.Xv.Select.Proof.selectBrOvf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectBrOvf_spec

/-- info: 'IxCC.Xv.Select.Proof.edge_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.edge_rel

/-- info: 'IxCC.Xv.Select.Proof.Agree.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Agree.insert

/-- info: 'IxCC.Xv.Select.Proof.selectTerm_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectTerm_ok

/-- info: 'IxCC.Xv.Select.Proof.defSites_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.defSites_eq

/-- info: 'IxCC.Xv.Select.Proof.foldl_defStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.foldl_defStep

/-- info: 'IxCC.Xv.Select.Proof.defSites_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.defSites_spec

/-- info: 'IxCC.Xv.Select.Proof.defSites_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.defSites_unique

/-- info: 'IxCC.Xv.Select.Proof.mem_effectSites' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.mem_effectSites

/-- info: 'IxCC.Xv.Select.Proof.exec_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.exec_other

/-- info: 'IxCC.Xv.Select.Proof.Arg.eval_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Arg.eval_congr

/-- info: 'IxCC.Xv.Select.Proof.Addr.eval_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Addr.eval_congr

/-- info: 'IxCC.Xv.Select.Proof.Rhs.eval_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.Rhs.eval_congr

/-- info: 'IxCC.Xv.Select.Proof.window_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.window_succ

/-- info: 'IxCC.Xv.Select.Proof.window_ne_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.window_ne_nil

/-- info: 'IxCC.Xv.Select.Proof.stableFrom_snoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.stableFrom_snoc

/-- info: 'IxCC.Xv.Select.Proof.all_avoid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.all_avoid

/-- info: 'IxCC.Xv.Select.Proof.stableFrom_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.stableFrom_single

/-- info: 'IxCC.Xv.Select.Proof.PendInv.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.PendInv.zero

/-- info: 'IxCC.Xv.Select.Proof.pure_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.pure_succ

/-- info: 'IxCC.Xv.Select.Proof.pure_not_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.pure_not_effect

/-- info: 'IxCC.Xv.Select.Proof.PendInv.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.PendInv.step

/-- info: 'IxCC.Xv.Select.Proof.PendInv.call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.PendInv.call

/-- info: 'IxCC.Xv.Select.Proof.PendInv.pend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.PendInv.pend

/-- info: 'IxCC.Xv.Select.Proof.sbind_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.sbind_ok

/-- info: 'IxCC.Xv.Select.Proof.sget_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.sget_bind

/-- info: 'IxCC.Xv.Select.Proof.smodify_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.smodify_bind

/-- info: 'IxCC.Xv.Select.Proof.spure_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.spure_run

/-- info: 'IxCC.Xv.Select.Proof.blockCtx_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.blockCtx_ok

/-- info: 'IxCC.Xv.Select.Proof.selectStmt_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectStmt_ext

/-- info: 'IxCC.Xv.Select.Proof.zipIdx_take_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.zipIdx_take_succ

/-- info: 'IxCC.Xv.Select.Proof.selectStmts_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectStmts_spec

/-- info: 'IxCC.Xv.Select.Proof.selectBlock_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectBlock_spec

/-- info: 'IxCC.Xv.Select.Proof.tbind_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.tbind_ok

/-- info: 'IxCC.Xv.Select.Proof.foldl_max_ge' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.foldl_max_ge

/-- info: 'IxCC.Xv.Select.Proof.foldl_max_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.foldl_max_mem

/-- info: 'IxCC.Xv.Select.Proof.foldl_blocks_ge' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.foldl_blocks_ge

/-- info: 'IxCC.Xv.Select.Proof.foldl_blocks_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.foldl_blocks_mem

/-- info: 'IxCC.Xv.Select.Proof.maxVReg_params' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.maxVReg_params

/-- info: 'IxCC.Xv.Select.Proof.maxVReg_block' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.maxVReg_block

/-- info: 'IxCC.Xv.Select.Proof.ctxLow_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.ctxLow_block

/-- info: 'IxCC.Xv.Select.Proof.selectBlocks_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectBlocks_spec

/-- info: 'IxCC.Xv.Select.Proof.BlockSel.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.BlockSel.mono

/-- info: 'IxCC.Xv.Select.Proof.selectFunc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectFunc_spec

/-- info: 'IxCC.Xv.Select.Proof.selectFuncs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.selectFuncs_spec

/-- info: 'IxCC.Xv.Select.Proof.progSel_of_funcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.progSel_of_funcs

/-- info: 'IxCC.Xv.Select.Proof.select_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.select_spec

/-- info: 'IxCC.Xv.Select.Proof.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.run_spec

/-- info: 'IxCC.Xv.Select.Proof.xv_step_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.xv_step_inst

/-- info: 'IxCC.Xv.Select.Proof.xv_star_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.xv_star_seq

/-- info: 'IxCC.Xv.Select.Proof.xv_step_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.xv_step_call

/-- info: 'IxCC.Xv.Select.Proof.xv_step_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.xv_step_term

/-- info: 'IxCC.Xv.Select.Proof.off_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.off_succ

/-- info: 'IxCC.Xv.Select.Proof.body_split' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.body_split

/-- info: 'IxCC.Xv.Select.Proof.off_len' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.off_len

/-- info: 'IxCC.Xv.Select.Proof.avoids_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.avoids_body

/-- info: 'IxCC.Xv.Select.Proof.avoids_term' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.avoids_term

/-- info: 'IxCC.Xv.Select.Proof.EnvRel.agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.EnvRel.agree

/-- info: 'IxCC.Xv.Select.Proof.readsOf_avoid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.readsOf_avoid

/-- info: 'IxCC.Xv.Select.Proof.bindParams_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.bindParams_rel

/-- info: 'IxCC.Xv.Select.Proof.EnvRel.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.EnvRel.bind

/-- info: 'IxCC.Xv.Select.Proof.EnvRel.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.EnvRel.insert

/-- info: 'IxCC.Xv.Select.Proof.EnvRel.above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.EnvRel.above

/-- info: 'IxCC.Xv.Select.Proof.takeEdge_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.takeEdge_inv

/-- info: 'IxCC.Xv.Select.Proof.xv_takeEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.xv_takeEdge

/-- info: 'IxCC.Xv.Select.Proof.enter_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.enter_rel

/-- info: 'IxCC.Xv.Select.Proof.FrameRel.susp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.FrameRel.susp

/-- info: 'IxCC.Xv.Select.Proof.forall₂_susp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.forall₂_susp

/-- info: 'IxCC.Xv.Select.Proof.entry_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.entry_rel

/-- info: 'IxCC.Xv.Select.Proof.stmt_low' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.stmt_low

/-- info: 'IxCC.Xv.Select.Proof.term_low' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.term_low

/-- info: 'IxCC.Xv.Select.Proof.params_low' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.params_low

/-- info: 'IxCC.Xv.Select.Proof.consumed_dead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.consumed_dead

/-- info: 'IxCC.Xv.Select.Proof.stmt_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.stmt_next

/-- info: 'IxCC.Xv.Select.Proof.call_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.call_next

/-- info: 'IxCC.Xv.Select.Proof.term_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.term_setup

/-- info: 'IxCC.Xv.Select.Proof.pre_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.pre_star

/-- info: 'IxCC.Xv.Select.Proof.enter_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.enter_block

/-- info: 'IxCC.Xv.Select.Proof.edge_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.edge_next

/-- info: 'IxCC.Xv.Select.Proof.xv_term_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.xv_term_eq

/-- info: 'IxCC.Xv.Select.Proof.select_lockstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.select_lockstep

/-- info: 'IxCC.Xv.Select.Proof.initial_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.initial_rel

/-- info: 'IxCC.Xv.Select.Proof.prog_eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.prog_eval_eq

/-- info: 'IxCC.Xv.Select.Proof.prog_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.Proof.prog_sim

/-- info: 'IxCC.Xv.Select.eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.eval_eq

/-- info: 'IxCC.Xv.Select.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.sim

/-- info: 'IxCC.Xv.Select.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.correct

/-- info: 'IxCC.Xv.Select.tsim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.tsim

/-- info: 'IxCC.Xv.Select.run_eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.run_eval_eq

/-- info: 'IxCC.Xv.Select.run_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.run_sim

/-- info: 'IxCC.Xv.Select.run_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.run_correct
