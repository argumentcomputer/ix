import IxCC.Rt.Proof.Words
import IxCC.Rt.Proof.Procs
import IxCC.Rt.Proof.Pow
import IxCC.Rt.Proof.Mem
import IxCC.Rt.Proof.Heap
import IxCC.Rt.Proof.Alloc
import IxCC.Rt.Proof.Chunk
import IxCC.Rt.Proof.Env
import IxCC.Rt.Proof.Ops
import IxCC.Rt.Proof.OpsDiv
import IxCC.Rt.Proof.Check
import IxCC.Rt.Proof.OpsCheck
import IxCC.Rt.Proof.OpsAlloc
import IxCC.Rt.Proof.OpsProj
import IxCC.Rt.Proof.OpsCall
import IxCC.Rt.Proof.Instr
import IxCC.Rt.Proof.Edge
import IxCC.Rt.Proof.Chain
import IxCC.Rt.Proof.Switch
import IxCC.Rt.Proof.SwitchTag
import IxCC.Rt.Proof.SwitchLink
import IxCC.Rt.Proof.SwitchSim
import IxCC.Rt.Proof.Term
import IxCC.Rt.Proof.Mono
import IxCC.Rt.Proof.Block
import IxCC.Rt.Proof.Layout
import IxCC.Rt.Proof.LayoutFun
import IxCC.Rt.Proof.Rel
import IxCC.Rt.Proof.StepFrame
import IxCC.Rt.Proof.StepInstr
import IxCC.Rt.Proof.StepEdge
import IxCC.Rt.Proof.StepTerm
import IxCC.Rt.Proof.Diagram
import IxCC.Rt.Proof.Prune
import IxCC.Rt.Proof.Program
import IxCC.Rt.Proof.Correct
import IxCC.Rt.Proof.Readback
import IxCC.Rt.Proof.CxInit
import IxCC.Rt.Proof.Publish

/-! Required axiom fences for the runtime lowering's proof (M2.5): the
value relation and the immortal heap invariant, every primitive's
expansion, allocation, projection, the procedures and their calls, the
switch shapes, chunk and function layout, the state relation and the
forward diagram from Cfg to the lowered Lir, pruning and edge splitting as
relabellings, the whole-program `Rt.lower_correct` and its traced form,
`Rt.readback_sound`, `cx_init` (`cxInit_ok`, `cxInit_fail`) and
`Rt.init_correct`: the theorems `IxCCTests.Fences.Rt` announced.
Generated from the proof modules' public theorems; expected messages are
preserved verbatim. -/

/-- info: 'IxCC.Rt.Proof.two64' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.two64

/-- info: 'IxCC.Rt.Proof.two63' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.two63

/-- info: 'IxCC.Rt.Proof.natLimit_eq' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natLimit_eq

/-- info: 'IxCC.Rt.Proof.natWord_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natWord_iff

/-- info: 'IxCC.Rt.Proof.natWord_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natWord_lt

/-- info: 'IxCC.Rt.Proof.natWord_of_lt' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natWord_of_lt

/-- info: 'IxCC.Rt.Proof.toNat_ofNat_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.toNat_ofNat_lt

/-- info: 'IxCC.Rt.Proof.word_lt' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.word_lt

/-- info: 'IxCC.Rt.Proof.sub_toNat_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.sub_toNat_of_le

/-- info: 'IxCC.Rt.Proof.sub_one_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.sub_one_toNat

/-- info: 'IxCC.Rt.Proof.truncate_w64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.truncate_w64

/-- info: 'IxCC.Rt.Proof.shiftMask_w64' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.shiftMask_w64

/-- info: 'IxCC.Rt.Proof.toNat_and63' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.toNat_and63

/-- info: 'IxCC.Rt.Proof.testBit_two_mul_add_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.testBit_two_mul_add_one

/-- info: 'IxCC.Rt.Proof.testBit_two_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.testBit_two_mul

/-- info: 'IxCC.Rt.Proof.tag_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.tag_and

/-- info: 'IxCC.Rt.Proof.tag_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.tag_or

/-- info: 'IxCC.Rt.Proof.tag_xor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.tag_xor

/-- info: 'IxCC.Rt.Proof.or_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.or_one

/-- info: 'IxCC.Rt.Proof.even_or_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.even_or_one

/-- info: 'IxCC.Rt.Proof.tagged_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.tagged_toNat

/-- info: 'IxCC.Rt.Proof.natWord_tagged' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natWord_tagged

/-- info: 'IxCC.Rt.Proof.add_carry_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.add_carry_iff

/-- info: 'IxCC.Rt.Proof.add_toNat_of_not_carry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.add_toNat_of_not_carry

/-- info: 'IxCC.Rt.Proof.natAdd_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natAdd_word

/-- info: 'IxCC.Rt.Proof.natAdd_operands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natAdd_operands

/-- info: 'IxCC.Rt.Proof.natSub_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natSub_word

/-- info: 'IxCC.Rt.Proof.natPred_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPred_word

/-- info: 'IxCC.Rt.Proof.mul_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.mul_check

/-- info: 'IxCC.Rt.Proof.natMul_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natMul_word

/-- info: 'IxCC.Rt.Proof.untag_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.untag_toNat

/-- info: 'IxCC.Rt.Proof.retag_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.retag_toNat

/-- info: 'IxCC.Rt.Proof.natDiv_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natDiv_word

/-- info: 'IxCC.Rt.Proof.natMod_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natMod_word

/-- info: 'IxCC.Rt.Proof.natWord_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natWord_eq_one

/-- info: 'IxCC.Rt.Proof.natWord_lt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natWord_lt_iff

/-- info: 'IxCC.Rt.Proof.natWord_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natWord_le_iff

/-- info: 'IxCC.Rt.Proof.natWord_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natWord_eq_iff

/-- info: 'IxCC.Rt.Proof.natLand_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natLand_word

/-- info: 'IxCC.Rt.Proof.natLor_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natLor_word

/-- info: 'IxCC.Rt.Proof.natXor_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natXor_word

/-- info: 'IxCC.Rt.Proof.shiftRight_eval' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.shiftRight_eval

/-- info: 'IxCC.Rt.Proof.shr_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.shr_tag

/-- info: 'IxCC.Rt.Proof.natShr_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natShr_word

/-- info: 'IxCC.Rt.Proof.shl_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.shl_check

/-- info: 'IxCC.Rt.Proof.natShl_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natShl_word

/-- info: 'IxCC.Rt.Proof.dispWord_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.dispWord_one

/-- info: 'IxCC.Rt.Proof.Scale.word_one' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Scale.word_one

/-- info: 'IxCC.Rt.Proof.retag_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.retag_eval

/-- info: 'IxCC.Rt.Proof.call_proc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.call_proc

/-- info: 'IxCC.Rt.Proof.natGcd_b0' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natGcd_b0

/-- info: 'IxCC.Rt.Proof.natGcd_b1' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natGcd_b1

/-- info: 'IxCC.Rt.Proof.natGcd_b2' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natGcd_b2

/-- info: 'IxCC.Rt.Proof.natGcd_b3' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natGcd_b3

/-- info: 'IxCC.Rt.Proof.gcd_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.gcd_step

/-- info: 'IxCC.Rt.Proof.natGcd_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natGcd_loop

/-- info: 'IxCC.Rt.Proof.natGcd_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natGcd_spec

/-- info: 'IxCC.Rt.Proof.natPow_b0' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_b0

/-- info: 'IxCC.Rt.Proof.natPow_b1' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_b1

/-- info: 'IxCC.Rt.Proof.natPow_b2' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_b2

/-- info: 'IxCC.Rt.Proof.natPow_b3' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_b3

/-- info: 'IxCC.Rt.Proof.natPow_b4' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_b4

/-- info: 'IxCC.Rt.Proof.natPow_b5' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_b5

/-- info: 'IxCC.Rt.Proof.natPow_b6' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_b6

/-- info: 'IxCC.Rt.Proof.natPow_b7' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_b7

/-- info: 'IxCC.Rt.Proof.natPow_b8' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_b8

/-- info: 'IxCC.Rt.Proof.natPow_b9' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_b9

/-- info: 'IxCC.Rt.Proof.natPow_b10' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_b10

/-- info: 'IxCC.Rt.Proof.natPow_b11' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_b11

/-- info: 'IxCC.Rt.Proof.natPow_b12' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_b12

/-- info: 'IxCC.Rt.Proof.natPow_b13' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_b13

/-- info: 'IxCC.Rt.Proof.pow_round' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.pow_round

/-- info: 'IxCC.Rt.Proof.checked_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.checked_mul

/-- info: 'IxCC.Rt.Proof.word_ne_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.word_ne_zero

/-- info: 'IxCC.Rt.Proof.round_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.round_flag

/-- info: 'IxCC.Rt.Proof.square_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.square_flag

/-- info: 'IxCC.Rt.Proof.bit_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.bit_toNat

/-- info: 'IxCC.Rt.Proof.bit_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.bit_cases

/-- info: 'IxCC.Rt.Proof.half_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.half_toNat

/-- info: 'IxCC.Rt.Proof.fails_prepend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fails_prepend

/-- info: 'IxCC.Rt.Proof.natPow_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_loop

/-- info: 'IxCC.Rt.Proof.natPow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_spec

/-- info: 'IxCC.Rt.Proof.natGcd_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natGcd_returns

/-- info: 'IxCC.Rt.Proof.addr_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.addr_toNat

/-- info: 'IxCC.Rt.Proof.addr_ne' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.addr_ne

/-- info: 'IxCC.Rt.Proof.rangeAllowed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.rangeAllowed_iff

/-- info: 'IxCC.Rt.Proof.writeLittle_readable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.writeLittle_readable

/-- info: 'IxCC.Rt.Proof.writeLittle_writable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.writeLittle_writable

/-- info: 'IxCC.Rt.Proof.write?_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.write?_ok

/-- info: 'IxCC.Rt.Proof.read?_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.read?_ok

/-- info: 'IxCC.Rt.Proof.WordAt.read64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.WordAt.read64

/-- info: 'IxCC.Rt.Proof.wordAt_write64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.wordAt_write64

/-- info: 'IxCC.Rt.Proof.writeLittle_bytes_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.writeLittle_bytes_out

/-- info: 'IxCC.Rt.Proof.WordAt.write_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.WordAt.write_disjoint

/-- info: 'IxCC.Rt.Proof.toUInt8_toNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.toUInt8_toNat

/-- info: 'IxCC.Rt.Proof.byte_of_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.byte_of_shift

/-- info: 'IxCC.Rt.Proof.wordAt_write32_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.wordAt_write32_pair

/-- info: 'IxCC.Rt.Proof.wordAt_write32_pair.toNat_ofNat_lt'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.wordAt_write32_pair.toNat_ofNat_lt'

/-- info: 'IxCC.Rt.Proof.add_two_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.add_two_toNat

/-- info: 'IxCC.Rt.Proof.WordAt.read16_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.WordAt.read16_tag

/-- info: 'IxCC.Rt.Proof.ValRel.mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ValRel.mono

/-- info: 'IxCC.Rt.Proof.ValRel.mono.List.lt_length_of_getElem?' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ValRel.mono.List.lt_length_of_getElem?

/-- info: 'IxCC.Rt.Proof.ListRel.length_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ListRel.length_eq

/-- info: 'IxCC.Rt.Proof.ListRel.get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ListRel.get

/-- info: 'IxCC.Rt.Proof.ListRel.mono' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ListRel.mono

/-- info: 'IxCC.Rt.Proof.HeapAt.cell' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.HeapAt.cell

/-- info: 'IxCC.Rt.Proof.cell_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cell_even

/-- info: 'IxCC.Rt.Proof.proj_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.proj_mem

/-- info: 'IxCC.Rt.Proof.immortalHeader_tag_half' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.immortalHeader_tag_half

/-- info: 'IxCC.Rt.Proof.tag_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.tag_mem

/-- info: 'IxCC.Rt.Proof.storeFields_readable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.storeFields_readable

/-- info: 'IxCC.Rt.Proof.storeFields_writable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.storeFields_writable

/-- info: 'IxCC.Rt.Proof.storeFields_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.storeFields_keeps

/-- info: 'IxCC.Rt.Proof.storeFields_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.storeFields_word

/-- info: 'IxCC.Rt.Proof.ctx_sub_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ctx_sub_toNat

/-- info: 'IxCC.Rt.Proof.ctx40_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ctx40_toNat

/-- info: 'IxCC.Rt.Proof.ctx32_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ctx32_toNat

/-- info: 'IxCC.Rt.Proof.immortalHeader_halves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.immortalHeader_halves

/-- info: 'IxCC.Rt.Proof.allocStores_readable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.allocStores_readable

/-- info: 'IxCC.Rt.Proof.allocStores_writable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.allocStores_writable

/-- info: 'IxCC.Rt.Proof.add4_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.add4_toNat

/-- info: 'IxCC.Rt.Proof.allocStores_keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.allocStores_keep

/-- info: 'IxCC.Rt.Proof.allocStores_bump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.allocStores_bump

/-- info: 'IxCC.Rt.Proof.allocStores_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.allocStores_header

/-- info: 'IxCC.Rt.Proof.allocStores_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.allocStores_field

/-- info: 'IxCC.Rt.Proof.alloc_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.alloc_mem

/-- info: 'IxCC.Rt.Proof.Grows.refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Grows.refl

/-- info: 'IxCC.Rt.Proof.Grows.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Grows.trans

/-- info: 'IxCC.Rt.Proof.Grows.ext' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Grows.ext

/-- info: 'IxCC.Rt.Proof.emit_run' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.emit_run

/-- info: 'IxCC.Rt.Proof.assign_run' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.assign_run

/-- info: 'IxCC.Rt.Proof.temp_run' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.temp_run

/-- info: 'IxCC.Rt.Proof.bin_run' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.bin_run

/-- info: 'IxCC.Rt.Proof.untag_imm_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.untag_imm_run

/-- info: 'IxCC.Rt.Proof.untag_v_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.untag_v_run

/-- info: 'IxCC.Rt.Proof.close_run' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.close_run

/-- info: 'IxCC.Rt.Proof.openAt_run' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.openAt_run

/-- info: 'IxCC.Rt.Proof.newLabel_run' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.newLabel_run

/-- info: 'IxCC.Rt.Proof.coldBlock_run' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.coldBlock_run

/-- info: 'IxCC.Rt.Proof.check_run' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.check_run

/-- info: 'IxCC.Rt.Proof.grows_acc' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.grows_acc

/-- info: 'IxCC.Rt.Proof.labels_acc' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.labels_acc

/-- info: 'IxCC.Rt.Proof.open_acc' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.open_acc

/-- info: 'IxCC.Rt.Proof.grows_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.grows_check

/-- info: 'IxCC.Rt.Proof.labels_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.labels_check

/-- info: 'IxCC.Rt.Proof.open_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.open_check

/-- info: 'IxCC.Rt.Proof.ext_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ext_check

/-- info: 'IxCC.Rt.Proof.resolveBlock_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.resolveBlock_ok

/-- info: 'IxCC.Rt.Proof.holds_open' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.holds_open

/-- info: 'IxCC.Rt.Proof.EnvRel.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.EnvRel.mono

/-- info: 'IxCC.Rt.Proof.EnvRel.temp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.EnvRel.temp

/-- info: 'IxCC.Rt.Proof.EnvRel.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.EnvRel.insert

/-- info: 'IxCC.Rt.Proof.EnvRel.insert_dead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.EnvRel.insert_dead

/-- info: 'IxCC.Rt.Proof.ArgReads.imm' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ArgReads.imm

/-- info: 'IxCC.Rt.Proof.arg_eval_temp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.arg_eval_temp

/-- info: 'IxCC.Rt.Proof.operand_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.operand_rel

/-- info: 'IxCC.Rt.Proof.operands_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.operands_rel

/-- info: 'IxCC.Rt.Proof.except_pure' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.except_pure

/-- info: 'IxCC.Rt.Proof.natArgs_two' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natArgs_two

/-- info: 'IxCC.Rt.Proof.natArgs_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natArgs_one

/-- info: 'IxCC.Rt.Proof.evalRhs_prim' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.evalRhs_prim

/-- info: 'IxCC.Rt.Proof.primResult_nat2' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.primResult_nat2

/-- info: 'IxCC.Rt.Proof.straight_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.straight_star

/-- info: 'IxCC.Rt.Proof.straight_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.straight_sim

/-- info: 'IxCC.Rt.Proof.bin2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.bin2_of

/-- info: 'IxCC.Rt.Proof.sem_not_bool_sub' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.sem_not_bool_sub

/-- info: 'IxCC.Rt.Proof.prim_natSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim_natSub

/-- info: 'IxCC.Rt.Proof.sem_nat2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.sem_nat2

/-- info: 'IxCC.Rt.Proof.sem_not_bool' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.sem_not_bool

/-- info: 'IxCC.Rt.Proof.prim2_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim2_sim

/-- info: 'IxCC.Rt.Proof.prim_natLand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim_natLand

/-- info: 'IxCC.Rt.Proof.prim_natLor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim_natLor

/-- info: 'IxCC.Rt.Proof.prim_natXor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim_natXor

/-- info: 'IxCC.Rt.Proof.ofKey_key' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ofKey_key

/-- info: 'IxCC.Rt.Proof.tables_boolsOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.tables_boolsOk

/-- info: 'IxCC.Rt.Proof.compareOf_cases' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.compareOf_cases

/-- info: 'IxCC.Rt.Proof.cmp_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cmp_sem

/-- info: 'IxCC.Rt.Proof.bool_rel' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.bool_rel

/-- info: 'IxCC.Rt.Proof.prim_cmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim_cmp

/-- info: 'IxCC.Rt.Proof.prim_natPred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim_natPred

/-- info: 'IxCC.Rt.Proof.prim_natShr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim_natShr

/-- info: 'IxCC.Rt.Proof.untag_ne_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.untag_ne_zero

/-- info: 'IxCC.Rt.Proof.word_one_ne_zero' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.word_one_ne_zero

/-- info: 'IxCC.Rt.Proof.mod_word0' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.mod_word0

/-- info: 'IxCC.Rt.Proof.div_word0' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.div_word0

/-- info: 'IxCC.Rt.Proof.div_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.div_word

/-- info: 'IxCC.Rt.Proof.mod_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.mod_word

/-- info: 'IxCC.Rt.Proof.prim_natDiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim_natDiv

/-- info: 'IxCC.Rt.Proof.prim_natMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim_natMod

/-- info: 'IxCC.Rt.Proof.check_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.check_code

/-- info: 'IxCC.Rt.Proof.check_br_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.check_br_sim

/-- info: 'IxCC.Rt.Proof.check_ovf_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.check_ovf_sim

/-- info: 'IxCC.Rt.Proof.prim_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim_natAdd

/-- info: 'IxCC.Rt.Proof.mul_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.mul_flag

/-- info: 'IxCC.Rt.Proof.prim_natMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim_natMul

/-- info: 'IxCC.Rt.Proof.shl_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.shl_flag

/-- info: 'IxCC.Rt.Proof.prim_natShl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim_natShl

/-- info: 'IxCC.Rt.Proof.fieldStmts_cons' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fieldStmts_cons

/-- info: 'IxCC.Rt.Proof.forM_stores_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.forM_stores_run

/-- info: 'IxCC.Rt.Proof.fieldStmts_noCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fieldStmts_noCall

/-- info: 'IxCC.Rt.Proof.stbind_run' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.stbind_run

/-- info: 'IxCC.Rt.Proof.freshReg_run' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.freshReg_run

/-- info: 'IxCC.Rt.Proof.alloc_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.alloc_run

/-- info: 'IxCC.Rt.Proof.execList_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.execList_append

/-- info: 'IxCC.Rt.Proof.ctx_disp_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ctx_disp_neg

/-- info: 'IxCC.Rt.Proof.eval_bumpOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.eval_bumpOff

/-- info: 'IxCC.Rt.Proof.eval_limitOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.eval_limitOff

/-- info: 'IxCC.Rt.Proof.eval_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.eval_mem

/-- info: 'IxCC.Rt.Proof.fieldOffset_nat' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fieldOffset_nat

/-- info: 'IxCC.Rt.Proof.load_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.load_word

/-- info: 'IxCC.Rt.Proof.exec_fieldStmts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.exec_fieldStmts

/-- info: 'IxCC.Rt.Proof.evalArgs_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.evalArgs_agree

/-- info: 'IxCC.Rt.Proof.evalRhs_alloc' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.evalRhs_alloc

/-- info: 'IxCC.Rt.Proof.add_ofNat_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.add_ofNat_zero

/-- info: 'IxCC.Rt.Proof.ofNat_four' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ofNat_four

/-- info: 'IxCC.Rt.Proof.exec_allocStores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.exec_allocStores

/-- info: 'IxCC.Rt.Proof.alloc_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.alloc_sim

/-- info: 'IxCC.Rt.Proof.evalRhs_proj' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.evalRhs_proj

/-- info: 'IxCC.Rt.Proof.evalRhs_arg' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.evalRhs_arg

/-- info: 'IxCC.Rt.Proof.cell_notNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cell_notNat

/-- info: 'IxCC.Rt.Proof.proj_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.proj_run

/-- info: 'IxCC.Rt.Proof.proj_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.proj_sim

/-- info: 'IxCC.Rt.Proof.arg_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.arg_sim

/-- info: 'IxCC.Rt.Proof.enter_proc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.enter_proc

/-- info: 'IxCC.Rt.Proof.procCall_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.procCall_sim

/-- info: 'IxCC.Rt.Proof.natPow_params' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natPow_params

/-- info: 'IxCC.Rt.Proof.natGcd_params' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natGcd_params

/-- info: 'IxCC.Rt.Proof.prim_natPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim_natPow

/-- info: 'IxCC.Rt.Proof.prim_natGcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prim_natGcd

/-- info: 'IxCC.Rt.Proof.withOperands_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.withOperands_run

/-- info: 'IxCC.Rt.Proof.operands_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.operands_one

/-- info: 'IxCC.Rt.Proof.liveArgs_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.liveArgs_of

/-- info: 'IxCC.Rt.Proof.primitive_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.primitive_sim

/-- info: 'IxCC.Rt.Proof.instr_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.instr_sim

/-- info: 'IxCC.Rt.Proof.instr_false' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.instr_false

/-- info: 'IxCC.Rt.Proof.instr_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.instr_fails

/-- info: 'IxCC.Rt.Proof.bind_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.bind_rel

/-- info: 'IxCC.Rt.Proof.edge_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.edge_run

/-- info: 'IxCC.Rt.Proof.grows_cold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.grows_cold

/-- info: 'IxCC.Rt.Proof.labels_cold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.labels_cold

/-- info: 'IxCC.Rt.Proof.edge_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.edge_facts

/-- info: 'IxCC.Rt.Proof.closed_block' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.closed_block

/-- info: 'IxCC.Rt.Proof.close_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.close_ext

/-- info: 'IxCC.Rt.Proof.reachesEdge_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.reachesEdge_jump

/-- info: 'IxCC.Rt.Proof.reachesEdge_br' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.reachesEdge_br

/-- info: 'IxCC.Rt.Proof.ReachesEdge.prepend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ReachesEdge.prepend

/-- info: 'IxCC.Rt.Proof.edge_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.edge_complete

/-- info: 'IxCC.Rt.Proof.chain_nil_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chain_nil_run

/-- info: 'IxCC.Rt.Proof.chain_one_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chain_one_run

/-- info: 'IxCC.Rt.Proof.chain_cons_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chain_cons_run

/-- info: 'IxCC.Rt.Proof.grows_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.grows_close

/-- info: 'IxCC.Rt.Proof.labels_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.labels_close

/-- info: 'IxCC.Rt.Proof.not_open_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.not_open_close

/-- info: 'IxCC.Rt.Proof.grows_chainSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.grows_chainSt

/-- info: 'IxCC.Rt.Proof.labels_chainSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.labels_chainSt

/-- info: 'IxCC.Rt.Proof.open_chainSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.open_chainSt

/-- info: 'IxCC.Rt.Proof.chain_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chain_grows

/-- info: 'IxCC.Rt.Proof.chain_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chain_keys

/-- info: 'IxCC.Rt.Proof.chainOr_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chainOr_keys

/-- info: 'IxCC.Rt.Proof.chain_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chain_reaches

/-- info: 'IxCC.Rt.Proof.unsnoc_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.unsnoc_eq

/-- info: 'IxCC.Rt.Proof.unsnoc_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.unsnoc_none

/-- info: 'IxCC.Rt.Proof.chainOr_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chainOr_grows

/-- info: 'IxCC.Rt.Proof.chainOr_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chainOr_reaches

/-- info: 'IxCC.Rt.Proof.mapM_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.mapM_run

/-- info: 'IxCC.Rt.Proof.switchAlt_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.switchAlt_run

/-- info: 'IxCC.Rt.Proof.alts_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.alts_run

/-- info: 'IxCC.Rt.Proof.dflt_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.dflt_run

/-- info: 'IxCC.Rt.Proof.closed_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.closed_jump

/-- info: 'IxCC.Rt.Proof.closed_br' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.closed_br

/-- info: 'IxCC.Rt.Proof.natSwitch_grows' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natSwitch_grows

/-- info: 'IxCC.Rt.Proof.natSwitch_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natSwitch_reaches

/-- info: 'IxCC.Rt.Proof.run_bind' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.run_bind

/-- info: 'IxCC.Rt.Proof.mixed_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.mixed_run

/-- info: 'IxCC.Rt.Proof.cellsOnly_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cellsOnly_run

/-- info: 'IxCC.Rt.Proof.labels_mixSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.labels_mixSt

/-- info: 'IxCC.Rt.Proof.open_mixSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.open_mixSt

/-- info: 'IxCC.Rt.Proof.grows_mixSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.grows_mixSt

/-- info: 'IxCC.Rt.Proof.mixed_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.mixed_facts

/-- info: 'IxCC.Rt.Proof.tagSwitch_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.tagSwitch_grows

/-- info: 'IxCC.Rt.Proof.tagSwitch_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.tagSwitch_odd

/-- info: 'IxCC.Rt.Proof.exec_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.exec_tag

/-- info: 'IxCC.Rt.Proof.mixed_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.mixed_even

/-- info: 'IxCC.Rt.Proof.tagSwitch_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.tagSwitch_even

/-- info: 'IxCC.Rt.Proof.and_one_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.and_one_toNat

/-- info: 'IxCC.Rt.Proof.odd_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.odd_and

/-- info: 'IxCC.Rt.Proof.even_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.even_and

/-- info: 'IxCC.Rt.Proof.ctor0Word_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ctor0Word_odd

/-- info: 'IxCC.Rt.Proof.erasedWord_odd' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.erasedWord_odd

/-- info: 'IxCC.Rt.Proof.natWord_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.natWord_odd

/-- info: 'IxCC.Rt.Proof.valWord_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.valWord_rel

/-- info: 'IxCC.Rt.Proof.keyKind_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.keyKind_zero

/-- info: 'IxCC.Rt.Proof.keyKind_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.keyKind_succ

/-- info: 'IxCC.Rt.Proof.keyKind_succ_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.keyKind_succ_of

/-- info: 'IxCC.Rt.Proof.keyKind_imm' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.keyKind_imm

/-- info: 'IxCC.Rt.Proof.keyKind_notNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.keyKind_notNat

/-- info: 'IxCC.Rt.Proof.chainPick_eq' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chainPick_eq

/-- info: 'IxCC.Rt.Proof.firstMatch_append' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.firstMatch_append

/-- info: 'IxCC.Rt.Proof.chainOrPick_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chainOrPick_of_match

/-- info: 'IxCC.Rt.Proof.chainOrPick_dflt' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chainOrPick_dflt

/-- info: 'IxCC.Rt.Proof.selectEdge_dflt' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.selectEdge_dflt

/-- info: 'IxCC.Rt.Proof.link_tests' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.link_tests

/-- info: 'IxCC.Rt.Proof.link_find' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.link_find

/-- info: 'IxCC.Rt.Proof.ListRel.with_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ListRel.with_mem

/-- info: 'IxCC.Rt.Proof.pick_tests' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.pick_tests

/-- info: 'IxCC.Rt.Proof.pick_nat' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.pick_nat

/-- info: 'IxCC.Rt.Proof.selectEdge_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.selectEdge_none

/-- info: 'IxCC.Rt.Proof.unless_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.unless_run

/-- info: 'IxCC.Rt.Proof.throw_not_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.throw_not_ok

/-- info: 'IxCC.Rt.Proof.ListRel.exists_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.ListRel.exists_left

/-- info: 'IxCC.Rt.Proof.immTest_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.immTest_some

/-- info: 'IxCC.Rt.Proof.cellTest_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cellTest_some

/-- info: 'IxCC.Rt.Proof.immTest_snd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.immTest_snd

/-- info: 'IxCC.Rt.Proof.cellTest_snd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cellTest_snd

/-- info: 'IxCC.Rt.Proof.switch_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.switch_sim

/-- info: 'IxCC.Rt.Proof.closedAt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.closedAt_of

/-- info: 'IxCC.Rt.Proof.fails_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fails_closed

/-- info: 'IxCC.Rt.Proof.term_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.term_jump

/-- info: 'IxCC.Rt.Proof.term_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.term_ret

/-- info: 'IxCC.Rt.Proof.term_tcall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.term_tcall

/-- info: 'IxCC.Rt.Proof.term_trap' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.term_trap

/-- info: 'IxCC.Rt.Proof.boolEdge_some' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.boolEdge_some

/-- info: 'IxCC.Rt.Proof.fusedClose_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fusedClose_run

/-- info: 'IxCC.Rt.Proof.fused_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fused_sim

/-- info: 'IxCC.Rt.Proof.Mono.pure'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Mono.pure'

/-- info: 'IxCC.Rt.Proof.Mono.bind'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Mono.bind'

/-- info: 'IxCC.Rt.Proof.Mono.emit'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Mono.emit'

/-- info: 'IxCC.Rt.Proof.Mono.freshReg'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Mono.freshReg'

/-- info: 'IxCC.Rt.Proof.Mono.check'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Mono.check'

/-- info: 'IxCC.Rt.Proof.Mono.throw'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Mono.throw'

/-- info: 'IxCC.Rt.Proof.Mono.lift'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Mono.lift'

/-- info: 'IxCC.Rt.Proof.Mono.untag'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Mono.untag'

/-- info: 'IxCC.Rt.Proof.Mono.divMod'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Mono.divMod'

/-- info: 'IxCC.Rt.Proof.primitive_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.primitive_mono

/-- info: 'IxCC.Rt.Proof.Mono.forM'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.Mono.forM'

/-- info: 'IxCC.Rt.Proof.alloc_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.alloc_mono

/-- info: 'IxCC.Rt.Proof.withOperands_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.withOperands_mono

/-- info: 'IxCC.Rt.Proof.instr_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.instr_mono

/-- info: 'IxCC.Rt.Proof.instrs_cons_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.instrs_cons_run

/-- info: 'IxCC.Rt.Proof.instrs_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.instrs_grows

/-- info: 'IxCC.Rt.Proof.switch_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.switch_grows

/-- info: 'IxCC.Rt.Proof.fusedSwitch_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fusedSwitch_grows

/-- info: 'IxCC.Rt.Proof.term_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.term_grows

/-- info: 'IxCC.Rt.Proof.unsnoc_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.unsnoc_some

/-- info: 'IxCC.Rt.Proof.fusable_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fusable_some

/-- info: 'IxCC.Rt.Proof.restAct_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.restAct_body

/-- info: 'IxCC.Rt.Proof.run_bind_of' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.run_bind_of

/-- info: 'IxCC.Rt.Proof.instrs_then' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.instrs_then

/-- info: 'IxCC.Rt.Proof.rest_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.rest_cons

/-- info: 'IxCC.Rt.Proof.fusedEnd_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fusedEnd_grows

/-- info: 'IxCC.Rt.Proof.rest_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.rest_grows

/-- info: 'IxCC.Rt.Proof.getD_foldl_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.getD_foldl_count

/-- info: 'IxCC.Rt.Proof.useCounts_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.useCounts_getD

/-- info: 'IxCC.Rt.Proof.le_sum_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.le_sum_map

/-- info: 'IxCC.Rt.Proof.two_le_sum_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.two_le_sum_map

/-- info: 'IxCC.Rt.Proof.count_flatMap_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.count_flatMap_ge

/-- info: 'IxCC.Rt.Proof.count_blockUses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.count_blockUses

/-- info: 'IxCC.Rt.Proof.fused_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fused_once

/-- info: 'IxCC.Rt.Proof.except_mapM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.except_mapM

/-- info: 'IxCC.Rt.Proof.chunkBlocks_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chunkBlocks_ok

/-- info: 'IxCC.Rt.Proof.labels_openSt' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.labels_openSt

/-- info: 'IxCC.Rt.Proof.open_openSt' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.open_openSt

/-- info: 'IxCC.Rt.Proof.block_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.block_run

/-- info: 'IxCC.Rt.Proof.blockCode_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.blockCode_grows

/-- info: 'IxCC.Rt.Proof.chunks_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chunks_spec

/-- info: 'IxCC.Rt.Proof.chunkStarts_foldl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chunkStarts_foldl

/-- info: 'IxCC.Rt.Proof.chunkStarts_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chunkStarts_get

/-- info: 'IxCC.Rt.Proof.chunkOff_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chunkOff_mono

/-- info: 'IxCC.Rt.Proof.resolveChunks_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.resolveChunks_spec

/-- info: 'IxCC.Rt.Proof.misordered_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.misordered_none

/-- info: 'IxCC.Rt.Proof.chunk_head' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.chunk_head

/-- info: 'IxCC.Rt.Proof.lowered_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.lowered_of

/-- info: 'IxCC.Rt.Proof.functionRaw_lowered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.functionRaw_lowered

/-- info: 'IxCC.Rt.Proof.foldl_max_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.foldl_max_ge

/-- info: 'IxCC.Rt.Proof.defs_lt_sup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.defs_lt_sup

/-- info: 'IxCC.Rt.Proof.SuspAt.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.SuspAt.mono

/-- info: 'IxCC.Rt.Proof.stack_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.stack_mono

/-- info: 'IxCC.Rt.Proof.fun_unique' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fun_unique

/-- info: 'IxCC.Rt.Proof.bindParams_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.bindParams_some

/-- info: 'IxCC.Rt.Proof.bindParams_get_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.bindParams_get_not_mem

/-- info: 'IxCC.Rt.Proof.evalArgs_bindParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.evalArgs_bindParams

/-- info: 'IxCC.Rt.Proof.envRel_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.envRel_leaf

/-- info: 'IxCC.Rt.Proof.params_lt_sup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.params_lt_sup

/-- info: 'IxCC.Rt.Proof.fusable_body_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fusable_body_ne

/-- info: 'IxCC.Rt.Proof.runAt_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.runAt_head

/-- info: 'IxCC.Rt.Proof.entry_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.entry_rel

/-- info: 'IxCC.Rt.Proof.step_enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.step_enter

/-- info: 'IxCC.Rt.Proof.step_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.step_return

/-- info: 'IxCC.Rt.Proof.final_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.final_return

/-- info: 'IxCC.Rt.Proof.state_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.state_eq

/-- info: 'IxCC.Rt.Proof.instr_def_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.instr_def_lt

/-- info: 'IxCC.Rt.Proof.instr_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.instr_live

/-- info: 'IxCC.Rt.Proof.fused_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fused_last

/-- info: 'IxCC.Rt.Proof.evalArg_insert_irrel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.evalArg_insert_irrel

/-- info: 'IxCC.Rt.Proof.evalArgs_insert_irrel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.evalArgs_insert_irrel

/-- info: 'IxCC.Rt.Proof.evalArgs_two' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.evalArgs_two

/-- info: 'IxCC.Rt.Proof.step_instr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.step_instr

/-- info: 'IxCC.Rt.Proof.step_call_instr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.step_call_instr

/-- info: 'IxCC.Rt.Proof.edge_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.edge_live

/-- info: 'IxCC.Rt.Proof.edge_live.argVars_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.edge_live.argVars_mem

/-- info: 'IxCC.Rt.Proof.merged_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.merged_target

/-- info: 'IxCC.Rt.Proof.take_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.take_edge

/-- info: 'IxCC.Rt.Proof.rest_nil' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.rest_nil

/-- info: 'IxCC.Rt.Proof.takeEdge_charge' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.takeEdge_charge

/-- info: 'IxCC.Rt.Proof.term_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.term_live

/-- info: 'IxCC.Rt.Proof.argVars_of_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.argVars_of_mem

/-- info: 'IxCC.Rt.Proof.lir_evalArgs_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.lir_evalArgs_two

/-- info: 'IxCC.Rt.Proof.key_of_bool' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.key_of_bool

/-- info: 'IxCC.Rt.Proof.selectEdge_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.selectEdge_mem

/-- info: 'IxCC.Rt.Proof.step_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.step_term

/-- info: 'IxCC.Rt.Proof.takeEdge_ne_trap' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.takeEdge_ne_trap

/-- info: 'IxCC.Rt.Proof.final_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.final_trap

/-- info: 'IxCC.Rt.Proof.evalRhs_ok_or_stuck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.evalRhs_ok_or_stuck

/-- info: 'IxCC.Rt.Proof.step_bind' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.step_bind

/-- info: 'IxCC.Rt.Proof.diagram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.diagram

/-- info: 'IxCC.Rt.Proof.contains_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.contains_insert

/-- info: 'IxCC.Rt.Proof.foldl_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.foldl_contains

/-- info: 'IxCC.Rt.Proof.reach_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.reach_mono

/-- info: 'IxCC.Rt.Proof.reachable_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.reachable_zero

/-- info: 'IxCC.Rt.Proof.kept_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.kept_spec

/-- info: 'IxCC.Rt.Proof.kept_le_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.kept_le_iff

/-- info: 'IxCC.Rt.Proof.rank_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.rank_get

/-- info: 'IxCC.Rt.Proof.kept_of_seen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.kept_of_seen

/-- info: 'IxCC.Rt.Proof.prune_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.prune_sim

/-- info: 'IxCC.Rt.Proof.function_spec' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.function_spec

/-- info: 'IxCC.Rt.Proof.functions_spec' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.functions_spec

/-- info: 'IxCC.Rt.Proof.lower_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.lower_spec

/-- info: 'IxCC.Rt.Proof.stageProg_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.stageProg_get

/-- info: 'IxCC.Rt.Proof.lower_lowers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.lower_lowers

/-- info: 'IxCC.Rt.Proof.target_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.target_raw

/-- info: 'IxCC.Rt.Proof.raw_ne_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.raw_ne_nil

/-- info: 'IxCC.Rt.Proof.raw_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.raw_pruned

/-- info: 'IxCC.Rt.Proof.pruned_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.pruned_split

/-- info: 'IxCC.Rt.Proof.lower_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.lower_ordered

/-- info: 'IxCC.Rt.Proof.call_step_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.call_step_cases

/-- info: 'IxCC.Rt.Proof.lower_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.lower_correct

/-- info: 'IxCC.Rt.Proof.toFirList_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.toFirList_length

/-- info: 'IxCC.Rt.Proof.fields_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.fields_readback

/-- info: 'IxCC.Rt.Proof.readback_toFir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.readback_toFir

/-- info: 'IxCC.Rt.Proof.readback_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.readback_sound

/-- info: 'IxCC.Rt.Proof.and_alignDown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.and_alignDown

/-- info: 'IxCC.Rt.Proof.word_alignDown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.word_alignDown

/-- info: 'IxCC.Rt.Proof.zeros_readable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.zeros_readable

/-- info: 'IxCC.Rt.Proof.zeros_writable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.zeros_writable

/-- info: 'IxCC.Rt.Proof.execList_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.execList_zeros

/-- info: 'IxCC.Rt.Proof.zeros_keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.zeros_keep

/-- info: 'IxCC.Rt.Proof.cxInit_b0' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cxInit_b0

/-- info: 'IxCC.Rt.Proof.cxInit_b1' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cxInit_b1

/-- info: 'IxCC.Rt.Proof.cxInit_b2' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cxInit_b2

/-- info: 'IxCC.Rt.Proof.cxInit_b3' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cxInit_b3

/-- info: 'IxCC.Rt.Proof.cxInit_b4' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cxInit_b4

/-- info: 'IxCC.Rt.Proof.cxInit_b5' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cxInit_b5

/-- info: 'IxCC.Rt.Proof.cxInit_b6' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cxInit_b6

/-- info: 'IxCC.Rt.Proof.cxInit_b7' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cxInit_b7

/-- info: 'IxCC.Rt.Proof.cxInit_b8' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cxInit_b8

/-- info: 'IxCC.Rt.Proof.cxInit_params' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cxInit_params

/-- info: 'IxCC.Rt.Proof.body8_noCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.body8_noCall

/-- info: 'IxCC.Rt.Proof.execList_cons_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.execList_cons_of

/-- info: 'IxCC.Rt.Proof.exec_assign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.exec_assign

/-- info: 'IxCC.Rt.Proof.exec_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.exec_store

/-- info: 'IxCC.Rt.Proof.eval_fail_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.eval_fail_of

/-- info: 'IxCC.Rt.Proof.eval_done_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.eval_done_of

/-- info: 'IxCC.Rt.Proof.and7_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.and7_toNat

/-- info: 'IxCC.Rt.Proof.base_toNat' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.base_toNat

/-- info: 'IxCC.Rt.Proof.add_word_toNat' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Proof.add_word_toNat

/-- info: 'IxCC.Rt.Proof.zeroOff_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.zeroOff_mem

/-- info: 'IxCC.Rt.Proof.zeroAddr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.zeroAddr

/-- info: 'IxCC.Rt.Proof.region_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.region_at

/-- info: 'IxCC.Rt.Proof.bumpOf_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.bumpOf_toNat

/-- info: 'IxCC.Rt.Proof.cxInit_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cxInit_cases

/-- info: 'IxCC.Rt.Proof.cxInit_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cxInit_fail

/-- info: 'IxCC.Rt.Proof.cxInit_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.cxInit_ok

/-- info: 'IxCC.Rt.lower_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.lower_correct

/-- info: 'IxCC.Rt.lower_correct_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.lower_correct_traced

/-- info: 'IxCC.Rt.readback_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.readback_sound

/-- info: 'IxCC.Rt.result_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.result_readback

/-- info: 'IxCC.Rt.lower_cxInit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.lower_cxInit

/-- info: 'IxCC.Rt.init_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.init_correct
