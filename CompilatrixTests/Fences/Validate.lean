import Compilatrix.Xv.Validate.Proof.Program

/-! Required axiom fences for register-allocation validation (M2.6): the
validator's abstract states and checks, the row-level correspondence of Xv
and Xl, the transfer of each instruction, edit and terminator, the
simulation relation and the per-step simulation `Validate.sound`, fuel for
Xv and Xl runs, and the whole-program results `Validate.program_eval_eq`,
`Validate.program_sim` and `Validate.program_sound`. Generated from the
proof modules' public theorems; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.Xv.Xl.read_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.read_reg

/-- info: 'Compilatrix.Xv.Xl.Frame.SameCtl.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.Frame.SameCtl.trans

/-- info: 'Compilatrix.Xv.Xl.write_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.write_spec

/-- info: 'Compilatrix.Xv.Xl.Regs.get_empty' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.Regs.get_empty

/-- info: 'Compilatrix.Xv.Xl.Frame.SameCtl.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.Frame.SameCtl.refl

/-- info: 'Compilatrix.Xv.Xl.write_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.write_ok

/-- info: 'Compilatrix.Xv.Xl.Regs.empty_size' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.Regs.empty_size

/-- info: 'Compilatrix.Xv.Xl.Regs.get_set' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.Regs.get_set

/-- info: 'Compilatrix.Xv.Xl.Regs.size_set' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.Regs.size_set

/-- info: 'Compilatrix.Xv.bindSlots_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.bindSlots_regs

/-- info: 'Compilatrix.Xv.Inst.substitute_consumed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Inst.substitute_consumed

/-- info: 'Compilatrix.Xv.boundOperands_v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.boundOperands_v

/-- info: 'Compilatrix.Xv.bindImplicits_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.bindImplicits_map

/-- info: 'Compilatrix.Xv.boundUses_length_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.boundUses_length_map

/-- info: 'Compilatrix.Xv.Amode.regs_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Amode.regs_map

/-- info: 'Compilatrix.Xv.Bound.map_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.map_map

/-- info: 'Compilatrix.Xv.boundUses_v' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.boundUses_v

/-- info: 'Compilatrix.Xv.Inst.substitute_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Inst.substitute_self

/-- info: 'Compilatrix.Xv.conUses_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.conUses_map

/-- info: 'Compilatrix.Xv.Amode.substitute_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Amode.substitute_eq

/-- info: 'Compilatrix.Xv.XArg.map_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.XArg.map_map

/-- info: 'Compilatrix.Xv.Amode.map_map' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Amode.map_map

/-- info: 'Compilatrix.Xv.XArg.substitute_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.XArg.substitute_eq

/-- info: 'Compilatrix.Xv.Bound.narrowOutput_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.narrowOutput_map

/-- info: 'Compilatrix.Xv.substituteArgs_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.substituteArgs_map

/-- info: 'Compilatrix.Xv.Inst.operands_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Inst.operands_map

/-- info: 'Compilatrix.Xv.bindRow_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.bindRow_regs

/-- info: 'Compilatrix.Xv.Amode.substitute_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Amode.substitute_map

/-- info: 'Compilatrix.Xv.Amode.map_id' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Amode.map_id

/-- info: 'Compilatrix.Xv.bindRow_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.bindRow_map

/-- info: 'Compilatrix.Xv.Inst.substitute_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Inst.substitute_map

/-- info: 'Compilatrix.Xv.substituteArgs_self' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.substituteArgs_self

/-- info: 'Compilatrix.Xv.boundOperands_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.boundOperands_map

/-- info: 'Compilatrix.Xv.opMap_pos' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.opMap_pos

/-- info: 'Compilatrix.Xv.boundDefs_v' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.boundDefs_v

/-- info: 'Compilatrix.Xv.opMap_con' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.opMap_con

/-- info: 'Compilatrix.Xv.Inst.map_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Inst.map_map

/-- info: 'Compilatrix.Xv.XArg.substitute_self' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.XArg.substitute_self

/-- info: 'Compilatrix.Xv.substituteArgs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.substituteArgs_eq

/-- info: 'Compilatrix.Xv.XArg.substitute_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.XArg.substitute_map

/-- info: 'Compilatrix.Xv.xargsRegs_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.xargsRegs_map

/-- info: 'Compilatrix.Xv.bindImplicits_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.bindImplicits_regs

/-- info: 'Compilatrix.Xv.opMap_kind' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.opMap_kind

/-- info: 'Compilatrix.Xv.boundDefs_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.boundDefs_map

/-- info: 'Compilatrix.Xv.boundUses_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.boundUses_map

/-- info: 'Compilatrix.Xv.opMap_v' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.opMap_v

/-- info: 'Compilatrix.Xv.XArg.regs_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.XArg.regs_map

/-- info: 'Compilatrix.Xv.Amode.substitute_self' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Amode.substitute_self

/-- info: 'Compilatrix.Xv.bindSlots_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.bindSlots_map

/-- info: 'Compilatrix.Xv.conDefs_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.conDefs_map

/-- info: 'Compilatrix.Xv.Inst.pair_of_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Inst.pair_of_substitute

/-- info: 'Compilatrix.Xv.slotArgs_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.slotArgs_cons

/-- info: 'Compilatrix.Xv.Placer.use_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Placer.use_spec

/-- info: 'Compilatrix.Xv.Placer.bounds_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Placer.bounds_spec

/-- info: 'Compilatrix.Xv.Bound.uses_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.uses_map

/-- info: 'Compilatrix.Xv.Bound.defs_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.defs_map

/-- info: 'Compilatrix.Xv.Placer.take_spec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Placer.take_spec

/-- info: 'Compilatrix.Xv.Placer.bound_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Placer.bound_spec

/-- info: 'Compilatrix.Xv.Bound.isSlot_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.isSlot_map

/-- info: 'Compilatrix.Xv.Placer.amode_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Placer.amode_spec

/-- info: 'Compilatrix.Xv.Validate.run_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.run_eq

/-- info: 'Compilatrix.Xv.Validate.slotWrites_nodup_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.slotWrites_nodup_tail

/-- info: 'Compilatrix.Xv.Validate.op_run_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.op_run_corr

/-- info: 'Compilatrix.Xv.Validate.readSlots_corr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.readSlots_corr

/-- info: 'Compilatrix.Xv.Validate.readReg_writeReg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.readReg_writeReg

/-- info: 'Compilatrix.Xv.Validate.SlotsCorr.write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.SlotsCorr.write

/-- info: 'Compilatrix.Xv.Validate.readReg_setReg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.readReg_setReg

/-- info: 'Compilatrix.Xv.Validate.WrittenCorr.frame' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.WrittenCorr.frame

/-- info: 'Compilatrix.Xv.Validate.readImplicits_corr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.readImplicits_corr

/-- info: 'Compilatrix.Xv.Validate.WriteCorr.update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.WriteCorr.update

/-- info: 'Compilatrix.Xv.Validate.mergeWrite_wide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.mergeWrite_wide

/-- info: 'Compilatrix.Xv.Validate.writeImplicits_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.writeImplicits_frame

/-- info: 'Compilatrix.Xv.Validate.writeImplicits_memory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.writeImplicits_memory

/-- info: 'Compilatrix.Xv.Validate.writeImplicits_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.writeImplicits_corr

/-- info: 'Compilatrix.Xv.Validate.memory_writeReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.memory_writeReg

/-- info: 'Compilatrix.Xv.Validate.op_exec_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.op_exec_corr

/-- info: 'Compilatrix.Xv.Validate.writeSlots_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.writeSlots_frame

/-- info: 'Compilatrix.Xv.Validate.writeSlots_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.writeSlots_corr

/-- info: 'Compilatrix.Xv.bindRow_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.bindRow_shape

/-- info: 'Compilatrix.Xv.Amode.eval_toMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Amode.eval_toMem

/-- info: 'Compilatrix.Xv.Bound.reassign_fst' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.reassign_fst

/-- info: 'Compilatrix.Xv.implicit_defs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.implicit_defs

/-- info: 'Compilatrix.Xv.bindImplicits_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.bindImplicits_shape

/-- info: 'Compilatrix.Xv.written_defs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.written_defs

/-- info: 'Compilatrix.Xv.isSlot_of_slot?' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.isSlot_of_slot?

/-- info: 'Compilatrix.Xv.slotsCorr_of_assign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.slotsCorr_of_assign

/-- info: 'Compilatrix.Xv.not_isSlot_of_implicit?' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.not_isSlot_of_implicit?

/-- info: 'Compilatrix.Xv.Bound.implicit?_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.implicit?_map

/-- info: 'Compilatrix.Xv.Bound.roleOk_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.roleOk_map

/-- info: 'Compilatrix.Xv.indexReg_gpr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.indexReg_gpr

/-- info: 'Compilatrix.Xv.Bound.reassign_snd' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.reassign_snd

/-- info: 'Compilatrix.Xv.slotArgs_append_implicits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.slotArgs_append_implicits

/-- info: 'Compilatrix.Xv.bindSlots_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.bindSlots_shape

/-- info: 'Compilatrix.Xv.Bound.slot?_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.slot?_map

/-- info: 'Compilatrix.Xv.amode_eval_corr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.amode_eval_corr

/-- info: 'Compilatrix.Xv.Bound.map_fst_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.map_fst_eq

/-- info: 'Compilatrix.Xv.loadRegisters_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.loadRegisters_none

/-- info: 'Compilatrix.Xv.readBack_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.readBack_other

/-- info: 'Compilatrix.Xv.scratch_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.scratch_nodup

/-- info: 'Compilatrix.Xv.loadRegisters_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.loadRegisters_mem

/-- info: 'Compilatrix.Xv.outputs_not_freeUses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.outputs_not_freeUses

/-- info: 'Compilatrix.Xv.Bound.fixed?_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.fixed?_map

/-- info: 'Compilatrix.Xv.loadRegisters_r15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.loadRegisters_r15

/-- info: 'Compilatrix.Xv.execBound_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.execBound_spec

/-- info: 'Compilatrix.Xv.loadValues_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.loadValues_spec

/-- info: 'Compilatrix.Xv.placeParts_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.placeParts_spec

/-- info: 'Compilatrix.Xv.r15_not_mem_scratch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.r15_not_mem_scratch

/-- info: 'Compilatrix.Xv.Bound.uses_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.uses_fixed

/-- info: 'Compilatrix.Xv.readBack_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.readBack_mem

/-- info: 'Compilatrix.Xv.Bound.taken_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.taken_eq

/-- info: 'Compilatrix.Xv.Bound.taken_not_fixed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.taken_not_fixed

/-- info: 'Compilatrix.Xv.rowWrites_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.rowWrites_eq

/-- info: 'Compilatrix.Xv.PartShape.reassign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.PartShape.reassign

/-- info: 'Compilatrix.Xv.Bound.uses_reassign' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.uses_reassign

/-- info: 'Compilatrix.Xv.slotWrites_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.slotWrites_eq

/-- info: 'Compilatrix.Xv.Bound.defs_reassign' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.defs_reassign

/-- info: 'Compilatrix.Xv.execRow_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.execRow_eq

/-- info: 'Compilatrix.Xv.part_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.part_corr

/-- info: 'Compilatrix.Xv.implicitWrites_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.implicitWrites_eq

/-- info: 'Compilatrix.Xv.Xl.placeL_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.placeL_cell

/-- info: 'Compilatrix.Xv.Xl.Bound.machine_rename' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.Bound.machine_rename

/-- info: 'Compilatrix.Xv.Xl.lookup_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.lookup_mem

/-- info: 'Compilatrix.Xv.Xl.Bound.placed_sub' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.Bound.placed_sub

/-- info: 'Compilatrix.Xv.Xl.r15_not_scratch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.r15_not_scratch

/-- info: 'Compilatrix.Xv.Xl.exists_mem_zip' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.exists_mem_zip

/-- info: 'Compilatrix.Xv.Xl.rowRegisters_zeroed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.rowRegisters_zeroed

/-- info: 'Compilatrix.Xv.Xl.Amode.toMem_rename' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.Amode.toMem_rename

/-- info: 'Compilatrix.Xv.Xl.placeIn_locs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.placeIn_locs

/-- info: 'Compilatrix.Xv.Xl.lookup_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.lookup_of_mem

/-- info: 'Compilatrix.Xv.Xl.mem_dedup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.mem_dedup

/-- info: 'Compilatrix.Xv.Xl.Bound.mem_locs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.Bound.mem_locs

/-- info: 'Compilatrix.Xv.Xl.rowRegisters_r15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.rowRegisters_r15

/-- info: 'Compilatrix.Xv.Xl.find?_snd_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.find?_snd_none

/-- info: 'Compilatrix.Xv.Xl.scratch_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.scratch_nodup

/-- info: 'Compilatrix.Xv.Xl.xlFree_not_named' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.xlFree_not_named

/-- info: 'Compilatrix.Xv.Xl.nodup_dedup' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.nodup_dedup

/-- info: 'Compilatrix.Xv.Xl.xlTable_snd_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.xlTable_snd_free

/-- info: 'Compilatrix.Xv.Xl.xlTable_fst_nodup' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.xlTable_fst_nodup

/-- info: 'Compilatrix.Xv.Xl.Bound.addrRegs_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.Bound.addrRegs_map

/-- info: 'Compilatrix.Xv.Xl.find?_snd_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.find?_snd_of_mem

/-- info: 'Compilatrix.Xv.Xl.zip_snd_sublist' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.zip_snd_sublist

/-- info: 'Compilatrix.Xv.Xl.xlFree_scratch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.xlFree_scratch

/-- info: 'Compilatrix.Xv.Xl.mem_xlNamed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.mem_xlNamed

/-- info: 'Compilatrix.Xv.Xl.Bound.placed_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.Bound.placed_map

/-- info: 'Compilatrix.Xv.Xl.slotArgs_rename' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.slotArgs_rename

/-- info: 'Compilatrix.Xv.Xl.placeL_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.placeL_inj

/-- info: 'Compilatrix.Xv.Xl.rowRegisters_use' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.rowRegisters_use

/-- info: 'Compilatrix.Xv.Xl.Bound.addrRegs_sub' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.Bound.addrRegs_sub

/-- info: 'Compilatrix.Xv.Xl.placeL_reg' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.placeL_reg

/-- info: 'Compilatrix.Xv.Xl.xlTable_snd_nodup' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.xlTable_snd_nodup

/-- info: 'Compilatrix.Xv.flatMap_sublist_flatMap' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.flatMap_sublist_flatMap

/-- info: 'Compilatrix.Xv.Bound.fixedDefRegs_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.fixedDefRegs_eq

/-- info: 'Compilatrix.Xv.rows_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.rows_corr

/-- info: 'Compilatrix.Xv.nodup_flatMap_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.nodup_flatMap_split

/-- info: 'Compilatrix.Xv.Bound.defs_regs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.defs_regs

/-- info: 'Compilatrix.Xv.flatMap_congr'' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.flatMap_congr'

/-- info: 'Compilatrix.Xv.Bound.fixedDefRegs_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.fixedDefRegs_fixed

/-- info: 'Compilatrix.Xv.Bound.slotDefRegs_sublist' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.slotDefRegs_sublist

/-- info: 'Compilatrix.Xv.defRegs_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.defRegs_nodup

/-- info: 'Compilatrix.Xv.APart.reassign_args' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.APart.reassign_args

/-- info: 'Compilatrix.Xv.execRows_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.execRows_eq

/-- info: 'Compilatrix.Xv.Xl.WriteOk.of_sameCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.WriteOk.of_sameCtl

/-- info: 'Compilatrix.Xv.writeBacks_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.writeBacks_spec

/-- info: 'Compilatrix.Xv.Xl.execBound_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.execBound_eq

/-- info: 'Compilatrix.Xv.readback_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.readback_eq

/-- info: 'Compilatrix.Xv.execBound_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.execBound_sim

/-- info: 'Compilatrix.Xv.Bound.narrowOutput_defs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.narrowOutput_defs

/-- info: 'Compilatrix.Xv.optGuard_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.optGuard_eq

/-- info: 'Compilatrix.Xv.defs_map_flat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.defs_map_flat

/-- info: 'Compilatrix.Xv.mem_xlLocs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.mem_xlLocs

/-- info: 'Compilatrix.Xv.slotArgs_isSome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.slotArgs_isSome

/-- info: 'Compilatrix.Xv.narrow_loc_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.narrow_loc_reg

/-- info: 'Compilatrix.Xv.fixed_use_loc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.fixed_use_loc

/-- info: 'Compilatrix.Xv.use_mem_xlLocs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.use_mem_xlLocs

/-- info: 'Compilatrix.Xv.PartShape.of_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.PartShape.of_map

/-- info: 'Compilatrix.Xv.Bound.machine_isSome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Bound.machine_isSome

/-- info: 'Compilatrix.Xv.uses_map_flat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.uses_map_flat

/-- info: 'Compilatrix.Xv.mapM_isSome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.mapM_isSome

/-- info: 'Compilatrix.Xv.reassign_assigned' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.reassign_assigned

/-- info: 'Compilatrix.Xv.mapM_map_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.mapM_map_congr

/-- info: 'Compilatrix.Xv.nodup_map_on' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.nodup_map_on

/-- info: 'Compilatrix.Xv.partArgs_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.partArgs_eq

/-- info: 'Compilatrix.Xv.def_mem_xlLocs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.def_mem_xlLocs

/-- info: 'Compilatrix.Xv.Validate.NatMap.allAux_find?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.NatMap.allAux_find?

/-- info: 'Compilatrix.Xv.Validate.NatMap.find?_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.NatMap.find?_erase

/-- info: 'Compilatrix.Xv.Validate.NatMap.find?_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.NatMap.find?_eq

/-- info: 'Compilatrix.Xv.Validate.NatMap.find?_mk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.NatMap.find?_mk

/-- info: 'Compilatrix.Xv.Validate.NatMap.find?_filterMapAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.NatMap.find?_filterMapAux

/-- info: 'Compilatrix.Xv.Validate.NatMap.find?_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.NatMap.find?_insert

/-- info: 'Compilatrix.Xv.Validate.NatMap.all_find?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.NatMap.all_find?

/-- info: 'Compilatrix.Xv.Validate.NatMap.find?_alterAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.NatMap.find?_alterAux

/-- info: 'Compilatrix.Xv.Validate.NatMap.alterAux_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.NatMap.alterAux_succ

/-- info: 'Compilatrix.Xv.Validate.NatMap.find?_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.NatMap.find?_node

/-- info: 'Compilatrix.Xv.Validate.NatMap.find?_filterMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.NatMap.find?_filterMap

/-- info: 'Compilatrix.Xv.Validate.NatMap.find?_leaf' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.NatMap.find?_leaf

/-- info: 'Compilatrix.Xv.Validate.NatMap.find?_alter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.NatMap.find?_alter

/-- info: 'Compilatrix.Xv.Validate.VSet.mem_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.VSet.mem_erase

/-- info: 'Compilatrix.Xv.Validate.VSet.mem_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.VSet.mem_sound

/-- info: 'Compilatrix.Xv.Validate.AState.Agree.holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.Agree.holds

/-- info: 'Compilatrix.Xv.Validate.AState.get_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.get_clear

/-- info: 'Compilatrix.Xv.Validate.AState.get_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.get_forget

/-- info: 'Compilatrix.Xv.Validate.AState.get_stepMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.get_stepMove

/-- info: 'Compilatrix.Xv.Validate.AState.mem_get_setFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.mem_get_setFold

/-- info: 'Compilatrix.Xv.Validate.AState.mem_get_of_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.mem_get_of_holds

/-- info: 'Compilatrix.Xv.Validate.isOutArgKey_locKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.isOutArgKey_locKey

/-- info: 'Compilatrix.Xv.Validate.AState.mem_gainFold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.mem_gainFold

/-- info: 'Compilatrix.Xv.Validate.gprIndex_inj' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.gprIndex_inj

/-- info: 'Compilatrix.Xv.Validate.AState.Agree.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.Agree.empty

/-- info: 'Compilatrix.Xv.Validate.bindParams_zip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.bindParams_zip

/-- info: 'Compilatrix.Xv.Validate.AState.mem_get_forgetFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.mem_get_forgetFold

/-- info: 'Compilatrix.Xv.Validate.gprOfIndex_gprIndex' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.gprOfIndex_gprIndex

/-- info: 'Compilatrix.Xv.Validate.AState.mem_get_bindParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.mem_get_bindParams

/-- info: 'Compilatrix.Xv.Validate.AState.Agree.antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.Agree.antitone

/-- info: 'Compilatrix.Xv.Validate.AState.get_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.get_set

/-- info: 'Compilatrix.Xv.Validate.VSet.mem_insert' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.VSet.mem_insert

/-- info: 'Compilatrix.Xv.Validate.locKey_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.locKey_inj

/-- info: 'Compilatrix.Xv.Validate.AState.mem_get_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.mem_get_le

/-- info: 'Compilatrix.Xv.Validate.AState.Agree.bindParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.Agree.bindParams

/-- info: 'Compilatrix.Xv.Validate.AState.get_clearOutArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.get_clearOutArgs

/-- info: 'Compilatrix.Xv.Validate.bindParams_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.bindParams_other

/-- info: 'Compilatrix.Xv.Validate.bindParams_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.bindParams_length

/-- info: 'Compilatrix.Xv.Validate.AState.mem_get_clearFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.mem_get_clearFold

/-- info: 'Compilatrix.Xv.Validate.VSet.subset_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.VSet.subset_sound

/-- info: 'Compilatrix.Xv.Validate.gprIndex_lt' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.gprIndex_lt

/-- info: 'Compilatrix.Xv.Validate.AState.Agree.clearOutArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.Agree.clearOutArgs

/-- info: 'Compilatrix.Xv.Validate.locKey_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.locKey_eq_iff

/-- info: 'Compilatrix.Xv.Validate.mapM_zip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.mapM_zip

/-- info: 'Compilatrix.Xv.Validate.AState.Agree.stepMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.Agree.stepMove

/-- info: 'Compilatrix.Xv.Validate.AState.mem_get_define' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.mem_get_define

/-- info: 'Compilatrix.Xv.Validate.isOutArgKey_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.isOutArgKey_iff

/-- info: 'Compilatrix.Xv.Validate.AState.Agree.define' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.Agree.define

/-- info: 'Compilatrix.Xv.Validate.AState.Agree.set_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.AState.Agree.set_single

/-- info: 'Compilatrix.Xv.Validate.nodup_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.nodup_iff

/-- info: 'Compilatrix.Xv.Validate.operandCode_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.operandCode_none

/-- info: 'Compilatrix.Xv.Validate.tied_reuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.tied_reuse

/-- info: 'Compilatrix.Xv.Validate.boundDefs_kind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.boundDefs_kind

/-- info: 'Compilatrix.Xv.Validate.firstCode_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.firstCode_none

/-- info: 'Compilatrix.Xv.Validate.conOk_reg' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.conOk_reg

/-- info: 'Compilatrix.Xv.Validate.mem_boundUses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.mem_boundUses

/-- info: 'Compilatrix.Xv.Validate.conOk_fixed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.conOk_fixed

/-- info: 'Compilatrix.Xv.Validate.mem_pairsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.mem_pairsOf

/-- info: 'Compilatrix.Xv.Validate.tie_loc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.tie_loc

/-- info: 'Compilatrix.Xv.Validate.usesOf_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.usesOf_pairs

/-- info: 'Compilatrix.Xv.Validate.conOk_readCon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.conOk_readCon

/-- info: 'Compilatrix.Xv.Validate.boundUses_flat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.boundUses_flat

/-- info: 'Compilatrix.Xv.Validate.defsOf_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.defsOf_pairs

/-- info: 'Compilatrix.Xv.Validate.allDistinct_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.allDistinct_iff

/-- info: 'Compilatrix.Xv.Validate.boundUses_kind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.boundUses_kind

/-- info: 'Compilatrix.Xv.Validate.conOk_writeCon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.conOk_writeCon

/-- info: 'Compilatrix.Xv.Validate.mem_boundDefs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.mem_boundDefs

/-- info: 'Compilatrix.Xv.Validate.use_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.use_pair

/-- info: 'Compilatrix.Xv.Validate.def_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.def_pair

/-- info: 'Compilatrix.Xv.Validate.pairs_snd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.pairs_snd

/-- info: 'Compilatrix.Xv.Validate.con_of_use' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.con_of_use

/-- info: 'Compilatrix.Xv.Validate.defAt_con' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.defAt_con

/-- info: 'Compilatrix.Xv.Validate.defAt_v' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.defAt_v

/-- info: 'Compilatrix.Xv.Validate.length_filter_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.length_filter_add

/-- info: 'Compilatrix.Xv.Validate.length_filterMap_reg' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.length_filterMap_reg

/-- info: 'Compilatrix.Xv.Validate.nodup_filterMap_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.nodup_filterMap_reg

/-- info: 'Compilatrix.Xv.Validate.usesOf_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.usesOf_mem

/-- info: 'Compilatrix.Xv.Validate.useAt_v' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.useAt_v

/-- info: 'Compilatrix.Xv.Validate.con_of_def' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.con_of_def

/-- info: 'Compilatrix.Xv.Validate.cells_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.cells_fit

/-- info: 'Compilatrix.Xv.Validate.earlyDefAt_v' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.earlyDefAt_v

/-- info: 'Compilatrix.Xv.Validate.perm_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.perm_length

/-- info: 'Compilatrix.Xv.Validate.useAt_con' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.useAt_con

/-- info: 'Compilatrix.Xv.Validate.earlyDefAt_con' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.earlyDefAt_con

/-- info: 'Compilatrix.Xv.Validate.mem_scratch_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.mem_scratch_iff

/-- info: 'Compilatrix.Xv.Validate.rowFacts_of_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.rowFacts_of_checks

/-- info: 'Compilatrix.Xv.Validate.defsOf_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.defsOf_mem

/-- info: 'Compilatrix.Xv.Validate.rows_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.rows_sound

/-- info: 'Compilatrix.Xv.Validate.kind_use_beq_use' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.kind_use_beq_use

/-- info: 'Compilatrix.Xv.Validate.Inst.map_eq_fused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.Inst.map_eq_fused

/-- info: 'Compilatrix.Xv.Validate.move_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.move_sound

/-- info: 'Compilatrix.Xv.Validate.kind_define_beq_define' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.kind_define_beq_define

/-- info: 'Compilatrix.Xv.Validate.fused_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.fused_sound

/-- info: 'Compilatrix.Xv.Validate.zero_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.zero_sound

/-- info: 'Compilatrix.Xv.Validate.single_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.single_sound

/-- info: 'Compilatrix.Xv.Validate.Inst.map_eq_op' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.Inst.map_eq_op

/-- info: 'Compilatrix.Xv.Validate.unless_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.unless_ok

/-- info: 'Compilatrix.Xv.Validate.jcc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.jcc_sound

/-- info: 'Compilatrix.Xv.Validate.rowShape_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.rowShape_facts

/-- info: 'Compilatrix.Xv.Validate.jcc_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.jcc_substitute

/-- info: 'Compilatrix.Xv.Validate.stepOperands_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.stepOperands_ok

/-- info: 'Compilatrix.Xv.Validate.zeroRow_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.zeroRow_run

/-- info: 'Compilatrix.Xv.Validate.locs_of_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.locs_of_pair

/-- info: 'Compilatrix.Xv.Validate.zip_pairs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.zip_pairs

/-- info: 'Compilatrix.Xv.Validate.bindRow_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.bindRow_pair

/-- info: 'Compilatrix.Xv.Validate.kind_define_beq_use' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.kind_define_beq_use

/-- info: 'Compilatrix.Xv.Validate.op_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.op_sound

/-- info: 'Compilatrix.Xv.Validate.defsOfPairs_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.defsOfPairs_pairs

/-- info: 'Compilatrix.Xv.Validate.stepEdit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.stepEdit_sound

/-- info: 'Compilatrix.Xv.Validate.kind_use_beq_define' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.kind_use_beq_define

/-- info: 'Compilatrix.Xv.Validate.checkBlock_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.checkBlock_ok

/-- info: 'Compilatrix.Xv.Validate.walk_interleave' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.walk_interleave

/-- info: 'Compilatrix.Xv.Validate.BlockRest.start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.BlockRest.start

/-- info: 'Compilatrix.Xv.Validate.applyBlocks_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.applyBlocks_ok

/-- info: 'Compilatrix.Xv.Validate.BlockRest.atTerm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.BlockRest.atTerm

/-- info: 'Compilatrix.Xv.Validate.apply_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.apply_ok

/-- info: 'Compilatrix.Xv.Validate.BlockRest.inst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.BlockRest.inst

/-- info: 'Compilatrix.Xv.Validate.checkBlocks_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.checkBlocks_ok

/-- info: 'Compilatrix.Xv.Validate.program_go_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.program_go_ok

/-- info: 'Compilatrix.Xv.Validate.applyBlock_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.applyBlock_ok

/-- info: 'Compilatrix.Xv.Validate.applyProgram_go_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.applyProgram_go_ok

/-- info: 'Compilatrix.Xv.Validate.accepted_of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.accepted_of_run

/-- info: 'Compilatrix.Xv.Validate.blockInfo_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.blockInfo_find

/-- info: 'Compilatrix.Xv.Validate.mapError_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.mapError_ok

/-- info: 'Compilatrix.Xv.Validate.func_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.func_ok

/-- info: 'Compilatrix.Xv.Validate.clearFold_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.clearFold_get

/-- info: 'Compilatrix.Xv.Validate.drop_nil_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.drop_nil_size

/-- info: 'Compilatrix.Xv.Validate.entryRegs_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.entryRegs_get

/-- info: 'Compilatrix.Xv.Validate.argRegs_not_reserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.argRegs_not_reserved

/-- info: 'Compilatrix.Xv.Validate.argRegs_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.argRegs_nodup

/-- info: 'Compilatrix.Xv.Validate.entry_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.entry_read

/-- info: 'Compilatrix.Xv.Validate.xl_edits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.xl_edits

/-- info: 'Compilatrix.Xv.Validate.call_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.call_agree

/-- info: 'Compilatrix.Xv.Validate.find?_zip_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.find?_zip_nodup

/-- info: 'Compilatrix.Xv.Validate.xl_step_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.xl_step_inst

/-- info: 'Compilatrix.Xv.Validate.returnRegs_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.returnRegs_result

/-- info: 'Compilatrix.Xv.Validate.paramLoc_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.paramLoc_eq

/-- info: 'Compilatrix.Xv.Validate.get_foldl_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.get_foldl_set

/-- info: 'Compilatrix.Xv.Validate.drop_succ_of_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.drop_succ_of_cons

/-- info: 'Compilatrix.Xv.Validate.returnRegs_size' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.returnRegs_size

/-- info: 'Compilatrix.Xv.Validate.returnRegs_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.returnRegs_other

/-- info: 'Compilatrix.Xv.Validate.read_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.read_pos

/-- info: 'Compilatrix.Xv.Validate.entry_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.entry_agree

/-- info: 'Compilatrix.Xv.Validate.regs_size_foldl_set' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.regs_size_foldl_set

/-- info: 'Compilatrix.Xv.Validate.resultLocs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.resultLocs_eq

/-- info: 'Compilatrix.Xv.Validate.resultRegs_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.resultRegs_nodup

/-- info: 'Compilatrix.Xv.Validate.argLoc_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.argLoc_eq

/-- info: 'Compilatrix.Xv.Validate.entryRegs_size' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.entryRegs_size

/-- info: 'Compilatrix.Xv.Validate.allGPRs_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.allGPRs_mem

/-- info: 'Compilatrix.Xv.Validate.drop_getElem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.drop_getElem

/-- info: 'Compilatrix.Xv.Validate.callee_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.callee_match

/-- info: 'Compilatrix.Xv.Validate.func_block0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.func_block0

/-- info: 'Compilatrix.Xv.Validate.argLocs_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.argLocs_length

/-- info: 'Compilatrix.Xv.Validate.call_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.call_check

/-- info: 'Compilatrix.Xv.Validate.conventionArgs_argLocs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.conventionArgs_argLocs

/-- info: 'Compilatrix.Xv.Validate.readAll_of_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.readAll_of_holds

/-- info: 'Compilatrix.Xv.Validate.inst_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.inst_sound

/-- info: 'Compilatrix.Xv.Validate.conventionResults_resultLocs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.conventionResults_resultLocs

/-- info: 'Compilatrix.Xv.Validate.resultLocs_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.resultLocs_length

/-- info: 'Compilatrix.Xv.Validate.call_substitute' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.call_substitute

/-- info: 'Compilatrix.Xv.Validate.checkEdges_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.checkEdges_mem

/-- info: 'Compilatrix.Xv.Validate.takeEdge_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.takeEdge_next

/-- info: 'Compilatrix.Xv.Validate.ret_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.ret_check

/-- info: 'Compilatrix.Xv.Validate.jmp_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.jmp_check

/-- info: 'Compilatrix.Xv.Validate.read_goto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.read_goto

/-- info: 'Compilatrix.Xv.Validate.xl_takeEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.xl_takeEdge

/-- info: 'Compilatrix.Xv.Validate.fail_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.fail_substitute

/-- info: 'Compilatrix.Xv.Validate.ret_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.ret_substitute

/-- info: 'Compilatrix.Xv.Validate.jmp_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.jmp_substitute

/-- info: 'Compilatrix.Xv.Validate.tail_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.tail_substitute

/-- info: 'Compilatrix.Xv.Validate.tail_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.tail_check

/-- info: 'Compilatrix.Xv.Validate.trap_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.trap_substitute

/-- info: 'Compilatrix.Xv.Validate.RunMatch.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.RunMatch.running

/-- info: 'Compilatrix.Xv.Validate.xl_step_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.xl_step_ret

/-- info: 'Compilatrix.Xv.Validate.edge_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.edge_sound

/-- info: 'Compilatrix.Xv.Validate.xl_step_ret_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.xl_step_ret_done

/-- info: 'Compilatrix.Xv.Validate.xl_step_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.xl_step_fail

/-- info: 'Compilatrix.Xv.Validate.xv_step_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.xv_step_final

/-- info: 'Compilatrix.Xv.Validate.Running.runMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.Running.runMatch

/-- info: 'Compilatrix.Xv.Validate.xl_step_jmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.xl_step_jmp

/-- info: 'Compilatrix.Xv.Validate.xl_step_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.xl_step_tail

/-- info: 'Compilatrix.Xv.Validate.xl_step_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.xl_step_trap

/-- info: 'Compilatrix.Xv.Validate.xl_step_jcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.xl_step_jcc

/-- info: 'Compilatrix.Xv.Validate.xl_step_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.xl_step_call

/-- info: 'Compilatrix.Xv.Validate.LockStep.eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.LockStep.eq

/-- info: 'Compilatrix.Xv.Validate.star_zero_step' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.star_zero_step

/-- info: 'Compilatrix.Xv.Validate.LockStep.reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.LockStep.reaches

/-- info: 'Compilatrix.Xv.Validate.LockStep.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.LockStep.sim

/-- info: 'Compilatrix.Xv.Validate.inst_case' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.inst_case

/-- info: 'Compilatrix.Xv.Validate.diagram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.diagram

/-- info: 'Compilatrix.Xv.Validate.sound_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.sound_final

/-- info: 'Compilatrix.Xv.Validate.call_case' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.call_case

/-- info: 'Compilatrix.Xv.Validate.drop_getElem_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.drop_getElem_cons

/-- info: 'Compilatrix.Xv.Validate.term_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.term_next

/-- info: 'Compilatrix.Xv.Validate.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.sound

/-- info: 'Compilatrix.Xv.Move.potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Move.potential

/-- info: 'Compilatrix.Xv.Xl.writeBacks_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.writeBacks_ctl

/-- info: 'Compilatrix.Xv.Func.bodyAt_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Func.bodyAt_eq

/-- info: 'Compilatrix.Xv.Xl.xl_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.xl_move

/-- info: 'Compilatrix.Xv.Func.left_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Func.left_succ

/-- info: 'Compilatrix.Xv.Func.left_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Func.left_pos

/-- info: 'Compilatrix.Xv.Program.left_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Program.left_le

/-- info: 'Compilatrix.Xv.Xl.potential_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.potential_step

/-- info: 'Compilatrix.Xv.Xl.execBound_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.execBound_ctl

/-- info: 'Compilatrix.Xv.Func.before_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Func.before_le

/-- info: 'Compilatrix.Xv.foldl_add_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.foldl_add_eq

/-- info: 'Compilatrix.Xv.Xl.execInst_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.execInst_ctl

/-- info: 'Compilatrix.Xv.Xl.eval_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.eval_mono

/-- info: 'Compilatrix.Xv.Func.left_le' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Func.left_le

/-- info: 'Compilatrix.Xv.Xl.xl_edge_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.xl_edge_move

/-- info: 'Compilatrix.Xv.eval_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.eval_mono

/-- info: 'Compilatrix.Xv.Func.at_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Func.at_lt

/-- info: 'Compilatrix.Xv.xv_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.xv_move

/-- info: 'Compilatrix.Xv.Xl.write_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.write_ctl

/-- info: 'Compilatrix.Xv.Xl.runs_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.runs_eval

/-- info: 'Compilatrix.Xv.Func.before_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Func.before_succ

/-- info: 'Compilatrix.Xv.Func.before_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Func.before_mono

/-- info: 'Compilatrix.Xv.Func.size_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Func.size_eq

/-- info: 'Compilatrix.Xv.fuel_enough' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.fuel_enough

/-- info: 'Compilatrix.Xv.runs_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.runs_eval

/-- info: 'Compilatrix.Xv.xv_edge_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.xv_edge_move

/-- info: 'Compilatrix.Xv.Program.left_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Program.left_of

/-- info: 'Compilatrix.Xv.Xl.writeAll_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Xl.writeAll_ctl

/-- info: 'Compilatrix.Xv.sum_take_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.sum_take_le

/-- info: 'Compilatrix.Xv.le_sum_of_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.le_sum_of_getElem?

/-- info: 'Compilatrix.Xv.potential_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.potential_step

/-- info: 'Compilatrix.Xv.Program.size_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Program.size_eq

/-- info: 'Compilatrix.Xv.Func.left_fwd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Func.left_fwd

/-- info: 'Compilatrix.Xv.Validate.initial_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.initial_match

/-- info: 'Compilatrix.Xv.Validate.program_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.program_sound

/-- info: 'Compilatrix.Xv.Validate.program_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.program_sim

/-- info: 'Compilatrix.Xv.Validate.program_eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.program_eval_eq
