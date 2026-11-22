import IxCC.Xv.Validate.Proof.Program

/-! Required axiom fences for register-allocation validation: the
validator's abstract states and checks, the row-level correspondence of Xv
and Xl, the transfer of each instruction, edit and terminator, the
simulation relation and the per-step simulation `Validate.sound`, fuel for
Xv and Xl runs, and the whole-program results `Validate.program_eval_eq`,
`Validate.program_sim` and `Validate.program_sound`. Generated from the
proof modules' public theorems; expected messages are preserved verbatim. -/

/-- info: 'IxCC.Xv.Xl.read_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.read_reg

/-- info: 'IxCC.Xv.Xl.Frame.SameCtl.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.Frame.SameCtl.trans

/-- info: 'IxCC.Xv.Xl.write_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.write_spec

/-- info: 'IxCC.Xv.Xl.Regs.get_empty' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Xl.Regs.get_empty

/-- info: 'IxCC.Xv.Xl.Frame.SameCtl.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.Frame.SameCtl.refl

/-- info: 'IxCC.Xv.Xl.write_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.write_ok

/-- info: 'IxCC.Xv.Xl.Regs.empty_size' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Xl.Regs.empty_size

/-- info: 'IxCC.Xv.Xl.Regs.get_set' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.Regs.get_set

/-- info: 'IxCC.Xv.Xl.Regs.size_set' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.Regs.size_set

/-- info: 'IxCC.Xv.bindSlots_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.bindSlots_regs

/-- info: 'IxCC.Xv.Inst.substitute_consumed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Inst.substitute_consumed

/-- info: 'IxCC.Xv.boundOperands_v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.boundOperands_v

/-- info: 'IxCC.Xv.bindImplicits_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.bindImplicits_map

/-- info: 'IxCC.Xv.boundUses_length_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.boundUses_length_map

/-- info: 'IxCC.Xv.Amode.regs_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Amode.regs_map

/-- info: 'IxCC.Xv.Bound.map_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.map_map

/-- info: 'IxCC.Xv.boundUses_v' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.boundUses_v

/-- info: 'IxCC.Xv.Inst.substitute_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Inst.substitute_self

/-- info: 'IxCC.Xv.conUses_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.conUses_map

/-- info: 'IxCC.Xv.Amode.substitute_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Amode.substitute_eq

/-- info: 'IxCC.Xv.XArg.map_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.XArg.map_map

/-- info: 'IxCC.Xv.Amode.map_map' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Amode.map_map

/-- info: 'IxCC.Xv.XArg.substitute_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.XArg.substitute_eq

/-- info: 'IxCC.Xv.Bound.narrowOutput_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.narrowOutput_map

/-- info: 'IxCC.Xv.substituteArgs_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.substituteArgs_map

/-- info: 'IxCC.Xv.Inst.operands_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Inst.operands_map

/-- info: 'IxCC.Xv.bindRow_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.bindRow_regs

/-- info: 'IxCC.Xv.Amode.substitute_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Amode.substitute_map

/-- info: 'IxCC.Xv.Amode.map_id' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Amode.map_id

/-- info: 'IxCC.Xv.bindRow_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.bindRow_map

/-- info: 'IxCC.Xv.Inst.substitute_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Inst.substitute_map

/-- info: 'IxCC.Xv.substituteArgs_self' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.substituteArgs_self

/-- info: 'IxCC.Xv.boundOperands_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.boundOperands_map

/-- info: 'IxCC.Xv.opMap_pos' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.opMap_pos

/-- info: 'IxCC.Xv.boundDefs_v' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.boundDefs_v

/-- info: 'IxCC.Xv.opMap_con' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.opMap_con

/-- info: 'IxCC.Xv.Inst.map_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Inst.map_map

/-- info: 'IxCC.Xv.XArg.substitute_self' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.XArg.substitute_self

/-- info: 'IxCC.Xv.substituteArgs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.substituteArgs_eq

/-- info: 'IxCC.Xv.XArg.substitute_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.XArg.substitute_map

/-- info: 'IxCC.Xv.xargsRegs_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.xargsRegs_map

/-- info: 'IxCC.Xv.bindImplicits_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.bindImplicits_regs

/-- info: 'IxCC.Xv.opMap_kind' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.opMap_kind

/-- info: 'IxCC.Xv.boundDefs_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.boundDefs_map

/-- info: 'IxCC.Xv.boundUses_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.boundUses_map

/-- info: 'IxCC.Xv.opMap_v' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.opMap_v

/-- info: 'IxCC.Xv.XArg.regs_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.XArg.regs_map

/-- info: 'IxCC.Xv.Amode.substitute_self' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Amode.substitute_self

/-- info: 'IxCC.Xv.bindSlots_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.bindSlots_map

/-- info: 'IxCC.Xv.conDefs_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.conDefs_map

/-- info: 'IxCC.Xv.Inst.pair_of_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Inst.pair_of_substitute

/-- info: 'IxCC.Xv.slotArgs_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.slotArgs_cons

/-- info: 'IxCC.Xv.Placer.use_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Placer.use_spec

/-- info: 'IxCC.Xv.Placer.bounds_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Placer.bounds_spec

/-- info: 'IxCC.Xv.Bound.uses_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.uses_map

/-- info: 'IxCC.Xv.Bound.defs_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.defs_map

/-- info: 'IxCC.Xv.Placer.take_spec' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Placer.take_spec

/-- info: 'IxCC.Xv.Placer.bound_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Placer.bound_spec

/-- info: 'IxCC.Xv.Bound.isSlot_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.isSlot_map

/-- info: 'IxCC.Xv.Placer.amode_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Placer.amode_spec

/-- info: 'IxCC.Xv.Validate.run_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.run_eq

/-- info: 'IxCC.Xv.Validate.slotWrites_nodup_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.slotWrites_nodup_tail

/-- info: 'IxCC.Xv.Validate.op_run_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.op_run_corr

/-- info: 'IxCC.Xv.Validate.readSlots_corr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.readSlots_corr

/-- info: 'IxCC.Xv.Validate.readReg_writeReg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.readReg_writeReg

/-- info: 'IxCC.Xv.Validate.SlotsCorr.write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.SlotsCorr.write

/-- info: 'IxCC.Xv.Validate.readReg_setReg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.readReg_setReg

/-- info: 'IxCC.Xv.Validate.WrittenCorr.frame' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.WrittenCorr.frame

/-- info: 'IxCC.Xv.Validate.readImplicits_corr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.readImplicits_corr

/-- info: 'IxCC.Xv.Validate.WriteCorr.update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.WriteCorr.update

/-- info: 'IxCC.Xv.Validate.mergeWrite_wide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.mergeWrite_wide

/-- info: 'IxCC.Xv.Validate.writeImplicits_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.writeImplicits_frame

/-- info: 'IxCC.Xv.Validate.writeImplicits_memory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.writeImplicits_memory

/-- info: 'IxCC.Xv.Validate.writeImplicits_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.writeImplicits_corr

/-- info: 'IxCC.Xv.Validate.memory_writeReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.memory_writeReg

/-- info: 'IxCC.Xv.Validate.op_exec_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.op_exec_corr

/-- info: 'IxCC.Xv.Validate.writeSlots_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.writeSlots_frame

/-- info: 'IxCC.Xv.Validate.writeSlots_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.writeSlots_corr

/-- info: 'IxCC.Xv.bindRow_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.bindRow_shape

/-- info: 'IxCC.Xv.Amode.eval_toMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Amode.eval_toMem

/-- info: 'IxCC.Xv.Bound.reassign_fst' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.reassign_fst

/-- info: 'IxCC.Xv.implicit_defs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.implicit_defs

/-- info: 'IxCC.Xv.bindImplicits_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.bindImplicits_shape

/-- info: 'IxCC.Xv.written_defs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.written_defs

/-- info: 'IxCC.Xv.isSlot_of_slot?' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.isSlot_of_slot?

/-- info: 'IxCC.Xv.slotsCorr_of_assign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.slotsCorr_of_assign

/-- info: 'IxCC.Xv.not_isSlot_of_implicit?' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.not_isSlot_of_implicit?

/-- info: 'IxCC.Xv.Bound.implicit?_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.implicit?_map

/-- info: 'IxCC.Xv.Bound.roleOk_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.roleOk_map

/-- info: 'IxCC.Xv.indexReg_gpr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.indexReg_gpr

/-- info: 'IxCC.Xv.Bound.reassign_snd' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.reassign_snd

/-- info: 'IxCC.Xv.slotArgs_append_implicits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.slotArgs_append_implicits

/-- info: 'IxCC.Xv.bindSlots_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.bindSlots_shape

/-- info: 'IxCC.Xv.Bound.slot?_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.slot?_map

/-- info: 'IxCC.Xv.amode_eval_corr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.amode_eval_corr

/-- info: 'IxCC.Xv.Bound.map_fst_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.map_fst_eq

/-- info: 'IxCC.Xv.loadRegisters_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.loadRegisters_none

/-- info: 'IxCC.Xv.readBack_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.readBack_other

/-- info: 'IxCC.Xv.scratch_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.scratch_nodup

/-- info: 'IxCC.Xv.loadRegisters_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.loadRegisters_mem

/-- info: 'IxCC.Xv.outputs_not_freeUses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.outputs_not_freeUses

/-- info: 'IxCC.Xv.Bound.fixed?_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.fixed?_map

/-- info: 'IxCC.Xv.loadRegisters_r15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.loadRegisters_r15

/-- info: 'IxCC.Xv.execBound_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.execBound_spec

/-- info: 'IxCC.Xv.loadValues_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.loadValues_spec

/-- info: 'IxCC.Xv.placeParts_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.placeParts_spec

/-- info: 'IxCC.Xv.r15_not_mem_scratch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.r15_not_mem_scratch

/-- info: 'IxCC.Xv.Bound.uses_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.uses_fixed

/-- info: 'IxCC.Xv.readBack_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.readBack_mem

/-- info: 'IxCC.Xv.Bound.taken_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.taken_eq

/-- info: 'IxCC.Xv.Bound.taken_not_fixed' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.taken_not_fixed

/-- info: 'IxCC.Xv.rowWrites_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.rowWrites_eq

/-- info: 'IxCC.Xv.PartShape.reassign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.PartShape.reassign

/-- info: 'IxCC.Xv.Bound.uses_reassign' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.uses_reassign

/-- info: 'IxCC.Xv.slotWrites_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.slotWrites_eq

/-- info: 'IxCC.Xv.Bound.defs_reassign' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.defs_reassign

/-- info: 'IxCC.Xv.execRow_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.execRow_eq

/-- info: 'IxCC.Xv.part_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.part_corr

/-- info: 'IxCC.Xv.implicitWrites_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.implicitWrites_eq

/-- info: 'IxCC.Xv.Xl.placeL_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.placeL_cell

/-- info: 'IxCC.Xv.Xl.Bound.machine_rename' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.Bound.machine_rename

/-- info: 'IxCC.Xv.Xl.lookup_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.lookup_mem

/-- info: 'IxCC.Xv.Xl.Bound.placed_sub' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.Bound.placed_sub

/-- info: 'IxCC.Xv.Xl.r15_not_scratch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.r15_not_scratch

/-- info: 'IxCC.Xv.Xl.exists_mem_zip' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.exists_mem_zip

/-- info: 'IxCC.Xv.Xl.rowRegisters_zeroed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.rowRegisters_zeroed

/-- info: 'IxCC.Xv.Xl.Amode.toMem_rename' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.Amode.toMem_rename

/-- info: 'IxCC.Xv.Xl.placeIn_locs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.placeIn_locs

/-- info: 'IxCC.Xv.Xl.lookup_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.lookup_of_mem

/-- info: 'IxCC.Xv.Xl.mem_dedup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.mem_dedup

/-- info: 'IxCC.Xv.Xl.Bound.mem_locs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.Bound.mem_locs

/-- info: 'IxCC.Xv.Xl.rowRegisters_r15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.rowRegisters_r15

/-- info: 'IxCC.Xv.Xl.find?_snd_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.find?_snd_none

/-- info: 'IxCC.Xv.Xl.scratch_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Xl.scratch_nodup

/-- info: 'IxCC.Xv.Xl.xlFree_not_named' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.xlFree_not_named

/-- info: 'IxCC.Xv.Xl.nodup_dedup' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.nodup_dedup

/-- info: 'IxCC.Xv.Xl.xlTable_snd_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.xlTable_snd_free

/-- info: 'IxCC.Xv.Xl.xlTable_fst_nodup' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.xlTable_fst_nodup

/-- info: 'IxCC.Xv.Xl.Bound.addrRegs_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.Bound.addrRegs_map

/-- info: 'IxCC.Xv.Xl.find?_snd_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.find?_snd_of_mem

/-- info: 'IxCC.Xv.Xl.zip_snd_sublist' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.zip_snd_sublist

/-- info: 'IxCC.Xv.Xl.xlFree_scratch' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.xlFree_scratch

/-- info: 'IxCC.Xv.Xl.mem_xlNamed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.mem_xlNamed

/-- info: 'IxCC.Xv.Xl.Bound.placed_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.Bound.placed_map

/-- info: 'IxCC.Xv.Xl.slotArgs_rename' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.slotArgs_rename

/-- info: 'IxCC.Xv.Xl.placeL_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.placeL_inj

/-- info: 'IxCC.Xv.Xl.rowRegisters_use' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.rowRegisters_use

/-- info: 'IxCC.Xv.Xl.Bound.addrRegs_sub' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.Bound.addrRegs_sub

/-- info: 'IxCC.Xv.Xl.placeL_reg' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.placeL_reg

/-- info: 'IxCC.Xv.Xl.xlTable_snd_nodup' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.xlTable_snd_nodup

/-- info: 'IxCC.Xv.flatMap_sublist_flatMap' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.flatMap_sublist_flatMap

/-- info: 'IxCC.Xv.Bound.fixedDefRegs_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.fixedDefRegs_eq

/-- info: 'IxCC.Xv.rows_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.rows_corr

/-- info: 'IxCC.Xv.nodup_flatMap_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.nodup_flatMap_split

/-- info: 'IxCC.Xv.Bound.defs_regs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.defs_regs

/-- info: 'IxCC.Xv.flatMap_congr'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.flatMap_congr'

/-- info: 'IxCC.Xv.Bound.fixedDefRegs_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.fixedDefRegs_fixed

/-- info: 'IxCC.Xv.Bound.slotDefRegs_sublist' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.slotDefRegs_sublist

/-- info: 'IxCC.Xv.defRegs_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.defRegs_nodup

/-- info: 'IxCC.Xv.APart.reassign_args' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.APart.reassign_args

/-- info: 'IxCC.Xv.execRows_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.execRows_eq

/-- info: 'IxCC.Xv.Xl.WriteOk.of_sameCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.WriteOk.of_sameCtl

/-- info: 'IxCC.Xv.writeBacks_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.writeBacks_spec

/-- info: 'IxCC.Xv.Xl.execBound_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.execBound_eq

/-- info: 'IxCC.Xv.readback_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.readback_eq

/-- info: 'IxCC.Xv.execBound_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.execBound_sim

/-- info: 'IxCC.Xv.Bound.narrowOutput_defs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.narrowOutput_defs

/-- info: 'IxCC.Xv.optGuard_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.optGuard_eq

/-- info: 'IxCC.Xv.defs_map_flat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.defs_map_flat

/-- info: 'IxCC.Xv.mem_xlLocs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.mem_xlLocs

/-- info: 'IxCC.Xv.slotArgs_isSome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.slotArgs_isSome

/-- info: 'IxCC.Xv.narrow_loc_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.narrow_loc_reg

/-- info: 'IxCC.Xv.fixed_use_loc' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.fixed_use_loc

/-- info: 'IxCC.Xv.use_mem_xlLocs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.use_mem_xlLocs

/-- info: 'IxCC.Xv.PartShape.of_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.PartShape.of_map

/-- info: 'IxCC.Xv.Bound.machine_isSome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Bound.machine_isSome

/-- info: 'IxCC.Xv.uses_map_flat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.uses_map_flat

/-- info: 'IxCC.Xv.mapM_isSome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.mapM_isSome

/-- info: 'IxCC.Xv.reassign_assigned' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.reassign_assigned

/-- info: 'IxCC.Xv.mapM_map_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.mapM_map_congr

/-- info: 'IxCC.Xv.nodup_map_on' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.nodup_map_on

/-- info: 'IxCC.Xv.partArgs_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.partArgs_eq

/-- info: 'IxCC.Xv.def_mem_xlLocs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.def_mem_xlLocs

/-- info: 'IxCC.Xv.Validate.NatMap.allAux_find?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.allAux_find?

/-- info: 'IxCC.Xv.Validate.NatMap.find?_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_erase

/-- info: 'IxCC.Xv.Validate.NatMap.find?_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_eq

/-- info: 'IxCC.Xv.Validate.NatMap.find?_mk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_mk

/-- info: 'IxCC.Xv.Validate.NatMap.find?_filterMapAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_filterMapAux

/-- info: 'IxCC.Xv.Validate.NatMap.find?_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_insert

/-- info: 'IxCC.Xv.Validate.NatMap.all_find?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.all_find?

/-- info: 'IxCC.Xv.Validate.NatMap.find?_alterAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_alterAux

/-- info: 'IxCC.Xv.Validate.NatMap.alterAux_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.alterAux_succ

/-- info: 'IxCC.Xv.Validate.NatMap.find?_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_node

/-- info: 'IxCC.Xv.Validate.NatMap.find?_filterMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_filterMap

/-- info: 'IxCC.Xv.Validate.NatMap.find?_leaf' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_leaf

/-- info: 'IxCC.Xv.Validate.NatMap.find?_alter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_alter

/-- info: 'IxCC.Xv.Validate.VSet.mem_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.VSet.mem_erase

/-- info: 'IxCC.Xv.Validate.VSet.mem_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.VSet.mem_sound

/-- info: 'IxCC.Xv.Validate.AState.Agree.holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.Agree.holds

/-- info: 'IxCC.Xv.Validate.AState.get_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.get_clear

/-- info: 'IxCC.Xv.Validate.AState.get_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.get_forget

/-- info: 'IxCC.Xv.Validate.AState.get_stepMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.get_stepMove

/-- info: 'IxCC.Xv.Validate.AState.mem_get_setFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.mem_get_setFold

/-- info: 'IxCC.Xv.Validate.AState.mem_get_of_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.mem_get_of_holds

/-- info: 'IxCC.Xv.Validate.isOutArgKey_locKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.isOutArgKey_locKey

/-- info: 'IxCC.Xv.Validate.AState.mem_gainFold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.mem_gainFold

/-- info: 'IxCC.Xv.Validate.gprIndex_inj' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.gprIndex_inj

/-- info: 'IxCC.Xv.Validate.AState.Agree.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.Agree.empty

/-- info: 'IxCC.Xv.Validate.bindParams_zip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.bindParams_zip

/-- info: 'IxCC.Xv.Validate.AState.mem_get_forgetFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.mem_get_forgetFold

/-- info: 'IxCC.Xv.Validate.gprOfIndex_gprIndex' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.gprOfIndex_gprIndex

/-- info: 'IxCC.Xv.Validate.AState.mem_get_bindParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.mem_get_bindParams

/-- info: 'IxCC.Xv.Validate.AState.Agree.antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.Agree.antitone

/-- info: 'IxCC.Xv.Validate.AState.get_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.get_set

/-- info: 'IxCC.Xv.Validate.VSet.mem_insert' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.VSet.mem_insert

/-- info: 'IxCC.Xv.Validate.locKey_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.locKey_inj

/-- info: 'IxCC.Xv.Validate.AState.mem_get_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.mem_get_le

/-- info: 'IxCC.Xv.Validate.AState.Agree.bindParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.Agree.bindParams

/-- info: 'IxCC.Xv.Validate.AState.get_clearOutArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.get_clearOutArgs

/-- info: 'IxCC.Xv.Validate.bindParams_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.bindParams_other

/-- info: 'IxCC.Xv.Validate.bindParams_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.bindParams_length

/-- info: 'IxCC.Xv.Validate.AState.mem_get_clearFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.mem_get_clearFold

/-- info: 'IxCC.Xv.Validate.VSet.subset_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.VSet.subset_sound

/-- info: 'IxCC.Xv.Validate.gprIndex_lt' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.gprIndex_lt

/-- info: 'IxCC.Xv.Validate.AState.Agree.clearOutArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.Agree.clearOutArgs

/-- info: 'IxCC.Xv.Validate.locKey_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.locKey_eq_iff

/-- info: 'IxCC.Xv.Validate.mapM_zip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.mapM_zip

/-- info: 'IxCC.Xv.Validate.AState.Agree.stepMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.Agree.stepMove

/-- info: 'IxCC.Xv.Validate.AState.mem_get_define' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.mem_get_define

/-- info: 'IxCC.Xv.Validate.isOutArgKey_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.isOutArgKey_iff

/-- info: 'IxCC.Xv.Validate.AState.Agree.define' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.Agree.define

/-- info: 'IxCC.Xv.Validate.AState.Agree.set_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.Agree.set_single

/-- info: 'IxCC.Xv.Validate.nodup_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.nodup_iff

/-- info: 'IxCC.Xv.Validate.operandCode_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.operandCode_none

/-- info: 'IxCC.Xv.Validate.tied_reuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.tied_reuse

/-- info: 'IxCC.Xv.Validate.boundDefs_kind' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.boundDefs_kind

/-- info: 'IxCC.Xv.Validate.firstCode_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.firstCode_none

/-- info: 'IxCC.Xv.Validate.conOk_reg' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.conOk_reg

/-- info: 'IxCC.Xv.Validate.mem_boundUses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.mem_boundUses

/-- info: 'IxCC.Xv.Validate.conOk_fixed' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.conOk_fixed

/-- info: 'IxCC.Xv.Validate.mem_pairsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.mem_pairsOf

/-- info: 'IxCC.Xv.Validate.tie_loc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.tie_loc

/-- info: 'IxCC.Xv.Validate.usesOf_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.usesOf_pairs

/-- info: 'IxCC.Xv.Validate.conOk_readCon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.conOk_readCon

/-- info: 'IxCC.Xv.Validate.boundUses_flat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.boundUses_flat

/-- info: 'IxCC.Xv.Validate.defsOf_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.defsOf_pairs

/-- info: 'IxCC.Xv.Validate.allDistinct_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.allDistinct_iff

/-- info: 'IxCC.Xv.Validate.boundUses_kind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.boundUses_kind

/-- info: 'IxCC.Xv.Validate.conOk_writeCon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.conOk_writeCon

/-- info: 'IxCC.Xv.Validate.mem_boundDefs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.mem_boundDefs

/-- info: 'IxCC.Xv.Validate.use_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.use_pair

/-- info: 'IxCC.Xv.Validate.def_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.def_pair

/-- info: 'IxCC.Xv.Validate.pairs_snd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.pairs_snd

/-- info: 'IxCC.Xv.Validate.con_of_use' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.con_of_use

/-- info: 'IxCC.Xv.Validate.defAt_con' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.defAt_con

/-- info: 'IxCC.Xv.Validate.defAt_v' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.defAt_v

/-- info: 'IxCC.Xv.Validate.length_filter_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.length_filter_add

/-- info: 'IxCC.Xv.Validate.length_filterMap_reg' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.length_filterMap_reg

/-- info: 'IxCC.Xv.Validate.nodup_filterMap_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.nodup_filterMap_reg

/-- info: 'IxCC.Xv.Validate.usesOf_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.usesOf_mem

/-- info: 'IxCC.Xv.Validate.useAt_v' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.useAt_v

/-- info: 'IxCC.Xv.Validate.con_of_def' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.con_of_def

/-- info: 'IxCC.Xv.Validate.cells_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.cells_fit

/-- info: 'IxCC.Xv.Validate.earlyDefAt_v' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.earlyDefAt_v

/-- info: 'IxCC.Xv.Validate.perm_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.perm_length

/-- info: 'IxCC.Xv.Validate.useAt_con' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.useAt_con

/-- info: 'IxCC.Xv.Validate.earlyDefAt_con' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.earlyDefAt_con

/-- info: 'IxCC.Xv.Validate.mem_scratch_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.mem_scratch_iff

/-- info: 'IxCC.Xv.Validate.rowFacts_of_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.rowFacts_of_checks

/-- info: 'IxCC.Xv.Validate.defsOf_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.defsOf_mem

/-- info: 'IxCC.Xv.Validate.rows_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.rows_sound

/-- info: 'IxCC.Xv.Validate.kind_use_beq_use' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.kind_use_beq_use

/-- info: 'IxCC.Xv.Validate.Inst.map_eq_fused' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.Inst.map_eq_fused

/-- info: 'IxCC.Xv.Validate.move_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.move_sound

/-- info: 'IxCC.Xv.Validate.kind_define_beq_define' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.kind_define_beq_define

/-- info: 'IxCC.Xv.Validate.fused_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.fused_sound

/-- info: 'IxCC.Xv.Validate.zero_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.zero_sound

/-- info: 'IxCC.Xv.Validate.single_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.single_sound

/-- info: 'IxCC.Xv.Validate.Inst.map_eq_op' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.Inst.map_eq_op

/-- info: 'IxCC.Xv.Validate.unless_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.unless_ok

/-- info: 'IxCC.Xv.Validate.jcc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.jcc_sound

/-- info: 'IxCC.Xv.Validate.rowShape_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.rowShape_facts

/-- info: 'IxCC.Xv.Validate.jcc_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.jcc_substitute

/-- info: 'IxCC.Xv.Validate.stepOperands_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.stepOperands_ok

/-- info: 'IxCC.Xv.Validate.zeroRow_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.zeroRow_run

/-- info: 'IxCC.Xv.Validate.locs_of_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.locs_of_pair

/-- info: 'IxCC.Xv.Validate.zip_pairs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.zip_pairs

/-- info: 'IxCC.Xv.Validate.bindRow_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.bindRow_pair

/-- info: 'IxCC.Xv.Validate.kind_define_beq_use' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.kind_define_beq_use

/-- info: 'IxCC.Xv.Validate.op_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.op_sound

/-- info: 'IxCC.Xv.Validate.defsOfPairs_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.defsOfPairs_pairs

/-- info: 'IxCC.Xv.Validate.stepEdit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.stepEdit_sound

/-- info: 'IxCC.Xv.Validate.kind_use_beq_define' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.kind_use_beq_define

/-- info: 'IxCC.Xv.Validate.checkBlock_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.checkBlock_ok

/-- info: 'IxCC.Xv.Validate.walk_interleave' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.walk_interleave

/-- info: 'IxCC.Xv.Validate.BlockRest.start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.BlockRest.start

/-- info: 'IxCC.Xv.Validate.applyBlocks_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.applyBlocks_ok

/-- info: 'IxCC.Xv.Validate.BlockRest.atTerm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.BlockRest.atTerm

/-- info: 'IxCC.Xv.Validate.apply_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.apply_ok

/-- info: 'IxCC.Xv.Validate.BlockRest.inst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.BlockRest.inst

/-- info: 'IxCC.Xv.Validate.checkBlocks_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.checkBlocks_ok

/-- info: 'IxCC.Xv.Validate.program_go_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.program_go_ok

/-- info: 'IxCC.Xv.Validate.applyBlock_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.applyBlock_ok

/-- info: 'IxCC.Xv.Validate.applyProgram_go_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.applyProgram_go_ok

/-- info: 'IxCC.Xv.Validate.accepted_of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.accepted_of_run

/-- info: 'IxCC.Xv.Validate.blockInfo_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.blockInfo_find

/-- info: 'IxCC.Xv.Validate.mapError_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.mapError_ok

/-- info: 'IxCC.Xv.Validate.func_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.func_ok

/-- info: 'IxCC.Xv.Validate.clearFold_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.clearFold_get

/-- info: 'IxCC.Xv.Validate.drop_nil_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.drop_nil_size

/-- info: 'IxCC.Xv.Validate.entryRegs_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.entryRegs_get

/-- info: 'IxCC.Xv.Validate.argRegs_not_reserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.argRegs_not_reserved

/-- info: 'IxCC.Xv.Validate.argRegs_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.argRegs_nodup

/-- info: 'IxCC.Xv.Validate.entry_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.entry_read

/-- info: 'IxCC.Xv.Validate.xl_edits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.xl_edits

/-- info: 'IxCC.Xv.Validate.call_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.call_agree

/-- info: 'IxCC.Xv.Validate.find?_zip_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.find?_zip_nodup

/-- info: 'IxCC.Xv.Validate.xl_step_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.xl_step_inst

/-- info: 'IxCC.Xv.Validate.returnRegs_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.returnRegs_result

/-- info: 'IxCC.Xv.Validate.paramLoc_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.paramLoc_eq

/-- info: 'IxCC.Xv.Validate.get_foldl_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.get_foldl_set

/-- info: 'IxCC.Xv.Validate.drop_succ_of_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.drop_succ_of_cons

/-- info: 'IxCC.Xv.Validate.returnRegs_size' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.returnRegs_size

/-- info: 'IxCC.Xv.Validate.returnRegs_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.returnRegs_other

/-- info: 'IxCC.Xv.Validate.read_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.read_pos

/-- info: 'IxCC.Xv.Validate.entry_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.entry_agree

/-- info: 'IxCC.Xv.Validate.regs_size_foldl_set' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.regs_size_foldl_set

/-- info: 'IxCC.Xv.Validate.resultLocs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.resultLocs_eq

/-- info: 'IxCC.Xv.Validate.resultRegs_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.resultRegs_nodup

/-- info: 'IxCC.Xv.Validate.argLoc_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.argLoc_eq

/-- info: 'IxCC.Xv.Validate.entryRegs_size' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.entryRegs_size

/-- info: 'IxCC.Xv.Validate.allGPRs_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.allGPRs_mem

/-- info: 'IxCC.Xv.Validate.drop_getElem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.drop_getElem

/-- info: 'IxCC.Xv.Validate.callee_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.callee_match

/-- info: 'IxCC.Xv.Validate.func_block0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.func_block0

/-- info: 'IxCC.Xv.Validate.argLocs_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.argLocs_length

/-- info: 'IxCC.Xv.Validate.call_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.call_check

/-- info: 'IxCC.Xv.Validate.conventionArgs_argLocs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.conventionArgs_argLocs

/-- info: 'IxCC.Xv.Validate.readAll_of_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.readAll_of_holds

/-- info: 'IxCC.Xv.Validate.inst_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.inst_sound

/-- info: 'IxCC.Xv.Validate.conventionResults_resultLocs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.conventionResults_resultLocs

/-- info: 'IxCC.Xv.Validate.resultLocs_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.resultLocs_length

/-- info: 'IxCC.Xv.Validate.call_substitute' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.call_substitute

/-- info: 'IxCC.Xv.Validate.checkEdges_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.checkEdges_mem

/-- info: 'IxCC.Xv.Validate.takeEdge_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.takeEdge_next

/-- info: 'IxCC.Xv.Validate.ret_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.ret_check

/-- info: 'IxCC.Xv.Validate.jmp_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.jmp_check

/-- info: 'IxCC.Xv.Validate.read_goto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.read_goto

/-- info: 'IxCC.Xv.Validate.xl_takeEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.xl_takeEdge

/-- info: 'IxCC.Xv.Validate.fail_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.fail_substitute

/-- info: 'IxCC.Xv.Validate.ret_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.ret_substitute

/-- info: 'IxCC.Xv.Validate.jmp_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.jmp_substitute

/-- info: 'IxCC.Xv.Validate.tail_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.tail_substitute

/-- info: 'IxCC.Xv.Validate.tail_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.tail_check

/-- info: 'IxCC.Xv.Validate.trap_substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.trap_substitute

/-- info: 'IxCC.Xv.Validate.RunMatch.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.RunMatch.running

/-- info: 'IxCC.Xv.Validate.xl_step_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.xl_step_ret

/-- info: 'IxCC.Xv.Validate.edge_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.edge_sound

/-- info: 'IxCC.Xv.Validate.xl_step_ret_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.xl_step_ret_done

/-- info: 'IxCC.Xv.Validate.xl_step_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.xl_step_fail

/-- info: 'IxCC.Xv.Validate.xv_step_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.xv_step_final

/-- info: 'IxCC.Xv.Validate.Running.runMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.Running.runMatch

/-- info: 'IxCC.Xv.Validate.xl_step_jmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.xl_step_jmp

/-- info: 'IxCC.Xv.Validate.xl_step_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.xl_step_tail

/-- info: 'IxCC.Xv.Validate.xl_step_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.xl_step_trap

/-- info: 'IxCC.Xv.Validate.xl_step_jcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.xl_step_jcc

/-- info: 'IxCC.Xv.Validate.xl_step_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.xl_step_call

/-- info: 'IxCC.Xv.Validate.LockStep.eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.LockStep.eq

/-- info: 'IxCC.Xv.Validate.star_zero_step' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.star_zero_step

/-- info: 'IxCC.Xv.Validate.LockStep.reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.LockStep.reaches

/-- info: 'IxCC.Xv.Validate.LockStep.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.LockStep.sim

/-- info: 'IxCC.Xv.Validate.inst_case' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.inst_case

/-- info: 'IxCC.Xv.Validate.diagram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.diagram

/-- info: 'IxCC.Xv.Validate.sound_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.sound_final

/-- info: 'IxCC.Xv.Validate.call_case' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.call_case

/-- info: 'IxCC.Xv.Validate.drop_getElem_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.drop_getElem_cons

/-- info: 'IxCC.Xv.Validate.term_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.term_next

/-- info: 'IxCC.Xv.Validate.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.sound

/-- info: 'IxCC.Xv.Move.potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Move.potential

/-- info: 'IxCC.Xv.Xl.writeBacks_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.writeBacks_ctl

/-- info: 'IxCC.Xv.Func.bodyAt_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Func.bodyAt_eq

/-- info: 'IxCC.Xv.Xl.xl_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.xl_move

/-- info: 'IxCC.Xv.Func.left_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Func.left_succ

/-- info: 'IxCC.Xv.Func.left_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Func.left_pos

/-- info: 'IxCC.Xv.Program.left_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Program.left_le

/-- info: 'IxCC.Xv.Xl.potential_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.potential_step

/-- info: 'IxCC.Xv.Xl.execBound_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.execBound_ctl

/-- info: 'IxCC.Xv.Func.before_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Func.before_le

/-- info: 'IxCC.Xv.foldl_add_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.foldl_add_eq

/-- info: 'IxCC.Xv.Xl.execInst_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.execInst_ctl

/-- info: 'IxCC.Xv.Xl.eval_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.eval_mono

/-- info: 'IxCC.Xv.Func.left_le' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Func.left_le

/-- info: 'IxCC.Xv.Xl.xl_edge_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.xl_edge_move

/-- info: 'IxCC.Xv.eval_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.eval_mono

/-- info: 'IxCC.Xv.Func.at_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Func.at_lt

/-- info: 'IxCC.Xv.xv_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.xv_move

/-- info: 'IxCC.Xv.Xl.write_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.write_ctl

/-- info: 'IxCC.Xv.Xl.runs_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.runs_eval

/-- info: 'IxCC.Xv.Func.before_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Func.before_succ

/-- info: 'IxCC.Xv.Func.before_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Func.before_mono

/-- info: 'IxCC.Xv.Func.size_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Func.size_eq

/-- info: 'IxCC.Xv.fuel_enough' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.fuel_enough

/-- info: 'IxCC.Xv.runs_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.runs_eval

/-- info: 'IxCC.Xv.xv_edge_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.xv_edge_move

/-- info: 'IxCC.Xv.Program.left_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Program.left_of

/-- info: 'IxCC.Xv.Xl.writeAll_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Xl.writeAll_ctl

/-- info: 'IxCC.Xv.sum_take_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.sum_take_le

/-- info: 'IxCC.Xv.le_sum_of_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.le_sum_of_getElem?

/-- info: 'IxCC.Xv.potential_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.potential_step

/-- info: 'IxCC.Xv.Program.size_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Program.size_eq

/-- info: 'IxCC.Xv.Func.left_fwd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Func.left_fwd

/-- info: 'IxCC.Xv.Validate.initial_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.initial_match

/-- info: 'IxCC.Xv.Validate.program_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.program_sound

/-- info: 'IxCC.Xv.Validate.program_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.program_sim

/-- info: 'IxCC.Xv.Validate.program_eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.program_eval_eq

/-! ## The tracked walk (2026-11-13): `NatMap` canonical form, choice-free lookups, `checkBlock_eq_list` -/

/-- info: 'IxCC.Xv.Validate.NatMap.Canon.mk' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.Canon.mk

/-- info: 'IxCC.Xv.Validate.NatMap.Canon.leftChild' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.Canon.leftChild

/-- info: 'IxCC.Xv.Validate.NatMap.Canon.rightChild' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.Canon.rightChild

/-- info: 'IxCC.Xv.Validate.NatMap.Canon.alterAux' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.Canon.alterAux

/-- info: 'IxCC.Xv.Validate.NatMap.Canon.alter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.Canon.alter

/-- info: 'IxCC.Xv.Validate.NatMap.Canon.insert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.Canon.insert

/-- info: 'IxCC.Xv.Validate.NatMap.Canon.erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.Canon.erase

/-- info: 'IxCC.Xv.Validate.NatMap.Canon.filterMapAux' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.Canon.filterMapAux

/-- info: 'IxCC.Xv.Validate.NatMap.Canon.filterMap' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.Canon.filterMap

/-- info: 'IxCC.Xv.Validate.NatMap.find?_node_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_node_left

/-- info: 'IxCC.Xv.Validate.NatMap.find?_node_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_node_right

/-- info: 'IxCC.Xv.Validate.NatMap.Canon.eq_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.Canon.eq_leaf

/-- info: 'IxCC.Xv.Validate.NatMap.ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.ext

/-- info: 'IxCC.Xv.Validate.NatMap.key_cases'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.key_cases'

/-- info: 'IxCC.Xv.Validate.NatMap.find?_alterAux'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_alterAux'

/-- info: 'IxCC.Xv.Validate.NatMap.find?_alter'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_alter'

/-- info: 'IxCC.Xv.Validate.NatMap.find?_insert'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_insert'

/-- info: 'IxCC.Xv.Validate.NatMap.find?_erase'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_erase'

/-- info: 'IxCC.Xv.Validate.NatMap.find?_filterMapAux'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_filterMapAux'

/-- info: 'IxCC.Xv.Validate.NatMap.find?_filterMap'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.NatMap.find?_filterMap'

/-- info: 'IxCC.Xv.Validate.find?_addRegs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.find?_addRegs

/-- info: 'IxCC.Xv.Validate.AState.find?_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.find?_set

/-- info: 'IxCC.Xv.Validate.AState.canon_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.canon_set

/-- info: 'IxCC.Xv.Validate.find?_foldl_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.find?_foldl_erase

/-- info: 'IxCC.Xv.Validate.canon_foldl_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.canon_foldl_erase

/-- info: 'IxCC.Xv.Validate.Tracked.Inv.empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.Tracked.Inv.empty

/-- info: 'IxCC.Xv.Validate.mem_noteOut' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.mem_noteOut

/-- info: 'IxCC.Xv.Validate.Tracked.Inv.setRow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.Tracked.Inv.setRow

/-- info: 'IxCC.Xv.Validate.Tracked.ofList_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.Tracked.ofList_inv

/-- info: 'IxCC.Xv.Validate.AState.forget_unlisted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.forget_unlisted

/-- info: 'IxCC.Xv.Validate.AState.find?_forget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.AState.find?_forget

/-- info: 'IxCC.Xv.Validate.Tracked.Inv.forget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.Tracked.Inv.forget

/-- info: 'IxCC.Xv.Validate.Tracked.Inv.clearOutArgs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.Tracked.Inv.clearOutArgs

/-- info: 'IxCC.Xv.Validate.Tracked.Inv.clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.Tracked.Inv.clear

/-- info: 'IxCC.Xv.Validate.Tracked.Inv.define' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.Tracked.Inv.define

/-- info: 'IxCC.Xv.Validate.Tracked.Inv.stepMove' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.Tracked.Inv.stepMove

/-- info: 'IxCC.Xv.Validate.tracks_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.tracks_ok

/-- info: 'IxCC.Xv.Validate.Tracked.Inv.callState' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.Tracked.Inv.callState

/-- info: 'IxCC.Xv.Validate.stepOperandsT_tracks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.stepOperandsT_tracks

/-- info: 'IxCC.Xv.Validate.stepInstT_tracks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.stepInstT_tracks

/-- info: 'IxCC.Xv.Validate.stepTermT_tracks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.stepTermT_tracks

/-- info: 'IxCC.Xv.Validate.stepEditT_tracks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.stepEditT_tracks

/-- info: 'IxCC.Xv.Validate.stepEditsT_tracks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.stepEditsT_tracks

/-- info: 'IxCC.Xv.Validate.Tracks.bind' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.Tracks.bind

/-- info: 'IxCC.Xv.Validate.tracks2_err' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.tracks2_err

/-- info: 'IxCC.Xv.Validate.walkBodyT_tracks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.walkBodyT_tracks

/-- info: 'IxCC.Xv.Validate.checkBlock_eq_list' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.checkBlock_eq_list
