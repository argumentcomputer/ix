import IxCC.Rt.Proof.Mono
import IxCC.Cfg.Rc.Proof.Native.RawFacts
import IxCC.Cfg.Rc.Proof.Native.CodeContract
import IxCC.Cfg.Rc.Proof.Owned.Admission

/-! Required axiom fences for raw 64-bit words on the reference-counted route (lane
`rc-raw-words`, `plans/ONE-PIPELINE.md` sections 2.4 and 7.3): the lowering's operand and
instruction facts over raw positions (`Rt.Proof`), the layout's flow check and gate
(`Cfg.Rc.Raw`, `Cfg.Rc.Native.Spec`), and the raw register relation the physical proofs will
carry (`Cfg.Rc.Proof.Physical.Bridge.RawWords`, `RawSlots`). Expected messages are preserved
verbatim. -/

/-- info: 'IxCC.Rt.Proof.withOperandsAt_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.withOperandsAt_run

/-- info: 'IxCC.Rt.Proof.operandAt_false' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.operandAt_false

/-- info: 'IxCC.Rt.Proof.operandsAt_tagged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.operandsAt_tagged

/-- info: 'IxCC.Rt.Proof.operandsAt_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.operandsAt_one

/-- info: 'IxCC.Rt.Proof.operandsAt_noRaw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.operandsAt_noRaw

/-- info: 'IxCC.Rt.Proof.operandAt_noRaw' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.operandAt_noRaw

/-- info: 'IxCC.Rt.Proof.noRaw_tables' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.noRaw_tables

/-- info: 'IxCC.Rt.Proof.NoRaw.tagged' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.NoRaw.tagged

/-- info: 'IxCC.Rt.Proof.Tagged.operandsAt_params' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Tagged.operandsAt_params

/-- info: 'IxCC.Rt.Proof.Tagged.operandsAt_var' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Tagged.operandsAt_var

/-- info: 'IxCC.Rt.Proof.Tagged.operandAt_ret' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Tagged.operandAt_ret

/-- info: 'IxCC.Rt.Proof.Tagged.rawPrim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Tagged.rawPrim

/-- info: 'IxCC.Rt.Proof.Tagged.instr_prim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Tagged.instr_prim

/-- info: 'IxCC.Rt.Proof.rawPrim_noRaw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.rawPrim_noRaw

/-- info: 'IxCC.Rt.Proof.instr_prim_noRaw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.instr_prim_noRaw

/-- info: 'IxCC.Rt.Proof.instr_prim_tagged' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.instr_prim_tagged

/-- info: 'IxCC.Rt.Proof.instr_prim_raw' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.instr_prim_raw

/-- info: 'IxCC.Rt.Proof.rawPrimCode_false' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.rawPrimCode_false

/-- info: 'IxCC.Rt.Proof.Mono.divModRaw64'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Mono.divModRaw64'

/-- info: 'IxCC.Rt.Proof.Mono.checked64'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Mono.checked64'

/-- info: 'IxCC.Rt.Proof.Mono.wordRaw64'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Mono.wordRaw64'

/-- info: 'IxCC.Rt.Proof.Mono.untagAt'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Mono.untagAt'

/-- info: 'IxCC.Rt.Proof.withOperandsAt_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.withOperandsAt_mono

/-- info: 'IxCC.Rt.Proof.rawPrimCode_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.rawPrimCode_mono

/-- info: 'IxCC.Cfg.Rc.generate_raw' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.generate_raw

/-- info: 'IxCC.Cfg.Rc.rawEq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.rawEq_iff

/-- info: 'IxCC.Cfg.Rc.Raw.emptyLayout_isRaw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Raw.emptyLayout_isRaw

/-- info: 'IxCC.Cfg.Rc.Raw.emptyLayout_retRaw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Raw.emptyLayout_retRaw

/-- info: 'IxCC.Cfg.Rc.Raw.rawFnInstr_heap' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Raw.rawFnInstr_heap

/-- info: 'IxCC.Cfg.Rc.Native.Spec.tablesOf_tagged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.tablesOf_tagged

/-- info: 'IxCC.Cfg.Rc.Native.Spec.CodeAdmission.tagged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.CodeAdmission.tagged

/-- info: 'IxCC.Cfg.Rc.Native.Spec.tablesOf_rawVar' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.tablesOf_rawVar

/-- info: 'IxCC.Cfg.Rc.Native.Spec.tablesOf_rawRet' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.tablesOf_rawRet

/-- info: 'IxCC.Cfg.Rc.Native.Spec.consumed_size' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.consumed_size

/-- info: 'IxCC.Cfg.Rc.Native.Spec.consumed_lookup_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.consumed_lookup_lt

/-- info: 'IxCC.Cfg.Rc.Native.Spec.rawParams_consumed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.rawParams_consumed

/-- info: 'IxCC.Cfg.Rc.Native.Spec.rawOk_funOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.rawOk_funOk

/-- info: 'IxCC.Cfg.Rc.Native.Spec.rawOk_exportOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.rawOk_exportOk

/-- info: 'IxCC.Cfg.Rc.Native.Spec.rawOk_retRaw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.rawOk_retRaw

/-- info: 'IxCC.Cfg.Rc.Native.Spec.funOk_blockOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.funOk_blockOk

/-- info: 'IxCC.Cfg.Rc.Native.Spec.blockOk_instrOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.blockOk_instrOk

/-- info: 'IxCC.Cfg.Rc.Native.Spec.blockOk_termOk' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.blockOk_termOk

/-- info: 'IxCC.Cfg.Rc.Native.Spec.funOk_heap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.funOk_heap

/-- info: 'IxCC.Cfg.Rc.Native.Spec.Cursor.instrOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.Cursor.instrOk

/-- info: 'IxCC.Cfg.Rc.Native.Spec.Cursor.termOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.Cursor.termOk

/-- info: 'IxCC.Cfg.Rc.Native.Spec.Cursor.noRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.Cursor.noRaw

/-- info: 'IxCC.Cfg.Rc.Native.Spec.ConsumedCursor.instrOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.ConsumedCursor.instrOk

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.RawVal.lit' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.RawVal.lit

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.RawVal.toNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.RawVal.toNat

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.empty

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.of_noRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.of_noRaw

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.agree

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.restrict

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.insert_tagged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.insert_tagged

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.insert_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.insert_raw

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.temp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.temp

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.insert_dead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords.insert_dead

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.omit_of_fused' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.omit_of_fused

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedWords.ofFused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedWords.ofFused

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedWords.toFused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedWords.toFused

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.SlotVal.tagged' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.SlotVal.tagged

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.SlotVal.raw' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.SlotVal.raw

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.SlotsRel.length_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.SlotsRel.length_eq

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.SlotsRel.of_tagged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.SlotsRel.of_tagged

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.SlotsRel.to_tagged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.SlotsRel.to_tagged

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.slot_operand_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.slot_operand_word

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.slot_operands_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.slot_operands_words

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedWords.bind_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedWords.bind_raw

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.slots_bindParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.slots_bindParams

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.slots_boundParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.slots_boundParams

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.live_omit' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.live_omit

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.live_omit_of_noRaw' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.live_omit_of_noRaw
