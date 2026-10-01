import Compilatrix.Rt.Proof.Words
import Compilatrix.Rt.Proof.Procs
import Compilatrix.Rt.Proof.Pow
import Compilatrix.Rt.Proof.Mem
import Compilatrix.Rt.Proof.Heap
import Compilatrix.Rt.Proof.Alloc
import Compilatrix.Rt.Proof.Chunk
import Compilatrix.Rt.Proof.Env
import Compilatrix.Rt.Proof.Ops
import Compilatrix.Rt.Proof.OpsDiv
import Compilatrix.Rt.Proof.Check
import Compilatrix.Rt.Proof.OpsCheck
import Compilatrix.Rt.Proof.OpsAlloc
import Compilatrix.Rt.Proof.OpsProj
import Compilatrix.Rt.Proof.OpsCall
import Compilatrix.Rt.Proof.Instr
import Compilatrix.Rt.Proof.Edge
import Compilatrix.Rt.Proof.Chain
import Compilatrix.Rt.Proof.Switch
import Compilatrix.Rt.Proof.SwitchTag
import Compilatrix.Rt.Proof.SwitchLink
import Compilatrix.Rt.Proof.SwitchSim
import Compilatrix.Rt.Proof.Term
import Compilatrix.Rt.Proof.Mono
import Compilatrix.Rt.Proof.Block
import Compilatrix.Rt.Proof.Layout
import Compilatrix.Rt.Proof.LayoutFun
import Compilatrix.Rt.Proof.Rel
import Compilatrix.Rt.Proof.StepFrame
import Compilatrix.Rt.Proof.StepInstr
import Compilatrix.Rt.Proof.StepEdge
import Compilatrix.Rt.Proof.StepTerm
import Compilatrix.Rt.Proof.Diagram
import Compilatrix.Rt.Proof.Prune
import Compilatrix.Rt.Proof.Program
import Compilatrix.Rt.Proof.Correct
import Compilatrix.Rt.Proof.Readback
import Compilatrix.Rt.Proof.CxInit
import Compilatrix.Rt.Proof.Publish

/-! Required axiom fences for the runtime lowering's proof (M2.5): the
value relation and the immortal heap invariant, every primitive's
expansion, allocation, projection, the procedures and their calls, the
switch shapes, chunk and function layout, the state relation and the
forward diagram from Cfg to the lowered Lir, pruning and edge splitting as
relabellings, the whole-program `Rt.lower_correct` and its traced form,
`Rt.readback_sound`, `cx_init` (`cxInit_ok`, `cxInit_fail`) and
`Rt.init_correct`: the theorems `CompilatrixTests.Fences.Rt` announced.
Generated from the proof modules' public theorems; expected messages are
preserved verbatim. -/

/-- info: 'Compilatrix.Rt.Proof.two64' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.two64

/-- info: 'Compilatrix.Rt.Proof.two63' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.two63

/-- info: 'Compilatrix.Rt.Proof.natLimit_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natLimit_eq

/-- info: 'Compilatrix.Rt.Proof.natWord_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natWord_iff

/-- info: 'Compilatrix.Rt.Proof.natWord_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natWord_lt

/-- info: 'Compilatrix.Rt.Proof.natWord_of_lt' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natWord_of_lt

/-- info: 'Compilatrix.Rt.Proof.toNat_ofNat_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.toNat_ofNat_lt

/-- info: 'Compilatrix.Rt.Proof.word_lt' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.word_lt

/-- info: 'Compilatrix.Rt.Proof.sub_toNat_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.sub_toNat_of_le

/-- info: 'Compilatrix.Rt.Proof.sub_one_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.sub_one_toNat

/-- info: 'Compilatrix.Rt.Proof.truncate_w64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.truncate_w64

/-- info: 'Compilatrix.Rt.Proof.shiftMask_w64' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.shiftMask_w64

/-- info: 'Compilatrix.Rt.Proof.toNat_and63' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.toNat_and63

/-- info: 'Compilatrix.Rt.Proof.testBit_two_mul_add_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.testBit_two_mul_add_one

/-- info: 'Compilatrix.Rt.Proof.testBit_two_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.testBit_two_mul

/-- info: 'Compilatrix.Rt.Proof.tag_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.tag_and

/-- info: 'Compilatrix.Rt.Proof.tag_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.tag_or

/-- info: 'Compilatrix.Rt.Proof.tag_xor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.tag_xor

/-- info: 'Compilatrix.Rt.Proof.or_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.or_one

/-- info: 'Compilatrix.Rt.Proof.even_or_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.even_or_one

/-- info: 'Compilatrix.Rt.Proof.tagged_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.tagged_toNat

/-- info: 'Compilatrix.Rt.Proof.natWord_tagged' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natWord_tagged

/-- info: 'Compilatrix.Rt.Proof.add_carry_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.add_carry_iff

/-- info: 'Compilatrix.Rt.Proof.add_toNat_of_not_carry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.add_toNat_of_not_carry

/-- info: 'Compilatrix.Rt.Proof.natAdd_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natAdd_word

/-- info: 'Compilatrix.Rt.Proof.natAdd_operands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natAdd_operands

/-- info: 'Compilatrix.Rt.Proof.natSub_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natSub_word

/-- info: 'Compilatrix.Rt.Proof.natPred_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPred_word

/-- info: 'Compilatrix.Rt.Proof.mul_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.mul_check

/-- info: 'Compilatrix.Rt.Proof.natMul_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natMul_word

/-- info: 'Compilatrix.Rt.Proof.untag_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.untag_toNat

/-- info: 'Compilatrix.Rt.Proof.retag_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.retag_toNat

/-- info: 'Compilatrix.Rt.Proof.natDiv_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natDiv_word

/-- info: 'Compilatrix.Rt.Proof.natMod_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natMod_word

/-- info: 'Compilatrix.Rt.Proof.natWord_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natWord_eq_one

/-- info: 'Compilatrix.Rt.Proof.natWord_lt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natWord_lt_iff

/-- info: 'Compilatrix.Rt.Proof.natWord_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natWord_le_iff

/-- info: 'Compilatrix.Rt.Proof.natWord_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natWord_eq_iff

/-- info: 'Compilatrix.Rt.Proof.natLand_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natLand_word

/-- info: 'Compilatrix.Rt.Proof.natLor_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natLor_word

/-- info: 'Compilatrix.Rt.Proof.natXor_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natXor_word

/-- info: 'Compilatrix.Rt.Proof.shiftRight_eval' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.shiftRight_eval

/-- info: 'Compilatrix.Rt.Proof.shr_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.shr_tag

/-- info: 'Compilatrix.Rt.Proof.natShr_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natShr_word

/-- info: 'Compilatrix.Rt.Proof.shl_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.shl_check

/-- info: 'Compilatrix.Rt.Proof.natShl_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natShl_word

/-- info: 'Compilatrix.Rt.Proof.dispWord_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.dispWord_one

/-- info: 'Compilatrix.Rt.Proof.Scale.word_one' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.Scale.word_one

/-- info: 'Compilatrix.Rt.Proof.retag_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.retag_eval

/-- info: 'Compilatrix.Rt.Proof.call_proc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.call_proc

/-- info: 'Compilatrix.Rt.Proof.natGcd_b0' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natGcd_b0

/-- info: 'Compilatrix.Rt.Proof.natGcd_b1' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natGcd_b1

/-- info: 'Compilatrix.Rt.Proof.natGcd_b2' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natGcd_b2

/-- info: 'Compilatrix.Rt.Proof.natGcd_b3' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natGcd_b3

/-- info: 'Compilatrix.Rt.Proof.gcd_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.gcd_step

/-- info: 'Compilatrix.Rt.Proof.natGcd_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natGcd_loop

/-- info: 'Compilatrix.Rt.Proof.natGcd_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natGcd_spec

/-- info: 'Compilatrix.Rt.Proof.natPow_b0' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_b0

/-- info: 'Compilatrix.Rt.Proof.natPow_b1' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_b1

/-- info: 'Compilatrix.Rt.Proof.natPow_b2' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_b2

/-- info: 'Compilatrix.Rt.Proof.natPow_b3' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_b3

/-- info: 'Compilatrix.Rt.Proof.natPow_b4' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_b4

/-- info: 'Compilatrix.Rt.Proof.natPow_b5' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_b5

/-- info: 'Compilatrix.Rt.Proof.natPow_b6' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_b6

/-- info: 'Compilatrix.Rt.Proof.natPow_b7' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_b7

/-- info: 'Compilatrix.Rt.Proof.natPow_b8' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_b8

/-- info: 'Compilatrix.Rt.Proof.natPow_b9' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_b9

/-- info: 'Compilatrix.Rt.Proof.natPow_b10' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_b10

/-- info: 'Compilatrix.Rt.Proof.natPow_b11' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_b11

/-- info: 'Compilatrix.Rt.Proof.natPow_b12' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_b12

/-- info: 'Compilatrix.Rt.Proof.natPow_b13' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_b13

/-- info: 'Compilatrix.Rt.Proof.pow_round' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.pow_round

/-- info: 'Compilatrix.Rt.Proof.checked_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.checked_mul

/-- info: 'Compilatrix.Rt.Proof.word_ne_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.word_ne_zero

/-- info: 'Compilatrix.Rt.Proof.round_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.round_flag

/-- info: 'Compilatrix.Rt.Proof.square_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.square_flag

/-- info: 'Compilatrix.Rt.Proof.bit_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.bit_toNat

/-- info: 'Compilatrix.Rt.Proof.bit_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.bit_cases

/-- info: 'Compilatrix.Rt.Proof.half_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.half_toNat

/-- info: 'Compilatrix.Rt.Proof.fails_prepend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fails_prepend

/-- info: 'Compilatrix.Rt.Proof.natPow_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_loop

/-- info: 'Compilatrix.Rt.Proof.natPow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_spec

/-- info: 'Compilatrix.Rt.Proof.natGcd_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natGcd_returns

/-- info: 'Compilatrix.Rt.Proof.addr_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.addr_toNat

/-- info: 'Compilatrix.Rt.Proof.addr_ne' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.addr_ne

/-- info: 'Compilatrix.Rt.Proof.rangeAllowed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.rangeAllowed_iff

/-- info: 'Compilatrix.Rt.Proof.writeLittle_readable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.writeLittle_readable

/-- info: 'Compilatrix.Rt.Proof.writeLittle_writable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.writeLittle_writable

/-- info: 'Compilatrix.Rt.Proof.write?_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.write?_ok

/-- info: 'Compilatrix.Rt.Proof.read?_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.read?_ok

/-- info: 'Compilatrix.Rt.Proof.WordAt.read64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.WordAt.read64

/-- info: 'Compilatrix.Rt.Proof.wordAt_write64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.wordAt_write64

/-- info: 'Compilatrix.Rt.Proof.writeLittle_bytes_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.writeLittle_bytes_out

/-- info: 'Compilatrix.Rt.Proof.WordAt.write_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.WordAt.write_disjoint

/-- info: 'Compilatrix.Rt.Proof.toUInt8_toNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.toUInt8_toNat

/-- info: 'Compilatrix.Rt.Proof.byte_of_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.byte_of_shift

/-- info: 'Compilatrix.Rt.Proof.wordAt_write32_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.wordAt_write32_pair

/-- info: 'Compilatrix.Rt.Proof.wordAt_write32_pair.toNat_ofNat_lt'' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.wordAt_write32_pair.toNat_ofNat_lt'

/-- info: 'Compilatrix.Rt.Proof.add_two_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.add_two_toNat

/-- info: 'Compilatrix.Rt.Proof.WordAt.read16_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.WordAt.read16_tag

/-- info: 'Compilatrix.Rt.Proof.ValRel.mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ValRel.mono

/-- info: 'Compilatrix.Rt.Proof.ValRel.mono.List.lt_length_of_getElem?' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ValRel.mono.List.lt_length_of_getElem?

/-- info: 'Compilatrix.Rt.Proof.ListRel.length_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ListRel.length_eq

/-- info: 'Compilatrix.Rt.Proof.ListRel.get' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ListRel.get

/-- info: 'Compilatrix.Rt.Proof.ListRel.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ListRel.mono

/-- info: 'Compilatrix.Rt.Proof.HeapAt.cell' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.HeapAt.cell

/-- info: 'Compilatrix.Rt.Proof.cell_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cell_even

/-- info: 'Compilatrix.Rt.Proof.proj_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.proj_mem

/-- info: 'Compilatrix.Rt.Proof.immortalHeader_tag_half' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.immortalHeader_tag_half

/-- info: 'Compilatrix.Rt.Proof.tag_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.tag_mem

/-- info: 'Compilatrix.Rt.Proof.storeFields_readable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.storeFields_readable

/-- info: 'Compilatrix.Rt.Proof.storeFields_writable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.storeFields_writable

/-- info: 'Compilatrix.Rt.Proof.storeFields_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.storeFields_keeps

/-- info: 'Compilatrix.Rt.Proof.storeFields_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.storeFields_word

/-- info: 'Compilatrix.Rt.Proof.ctx_sub_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ctx_sub_toNat

/-- info: 'Compilatrix.Rt.Proof.ctx40_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ctx40_toNat

/-- info: 'Compilatrix.Rt.Proof.ctx32_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ctx32_toNat

/-- info: 'Compilatrix.Rt.Proof.immortalHeader_halves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.immortalHeader_halves

/-- info: 'Compilatrix.Rt.Proof.allocStores_readable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.allocStores_readable

/-- info: 'Compilatrix.Rt.Proof.allocStores_writable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.allocStores_writable

/-- info: 'Compilatrix.Rt.Proof.add4_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.add4_toNat

/-- info: 'Compilatrix.Rt.Proof.allocStores_keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.allocStores_keep

/-- info: 'Compilatrix.Rt.Proof.allocStores_bump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.allocStores_bump

/-- info: 'Compilatrix.Rt.Proof.allocStores_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.allocStores_header

/-- info: 'Compilatrix.Rt.Proof.allocStores_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.allocStores_field

/-- info: 'Compilatrix.Rt.Proof.alloc_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.alloc_mem

/-- info: 'Compilatrix.Rt.Proof.Grows.refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.Grows.refl

/-- info: 'Compilatrix.Rt.Proof.Grows.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.Grows.trans

/-- info: 'Compilatrix.Rt.Proof.Grows.ext' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.Grows.ext

/-- info: 'Compilatrix.Rt.Proof.emit_run' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.emit_run

/-- info: 'Compilatrix.Rt.Proof.assign_run' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.assign_run

/-- info: 'Compilatrix.Rt.Proof.temp_run' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.temp_run

/-- info: 'Compilatrix.Rt.Proof.bin_run' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.bin_run

/-- info: 'Compilatrix.Rt.Proof.untag_imm_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.untag_imm_run

/-- info: 'Compilatrix.Rt.Proof.untag_v_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.untag_v_run

/-- info: 'Compilatrix.Rt.Proof.close_run' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.close_run

/-- info: 'Compilatrix.Rt.Proof.openAt_run' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.openAt_run

/-- info: 'Compilatrix.Rt.Proof.newLabel_run' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.newLabel_run

/-- info: 'Compilatrix.Rt.Proof.coldBlock_run' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.coldBlock_run

/-- info: 'Compilatrix.Rt.Proof.check_run' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.check_run

/-- info: 'Compilatrix.Rt.Proof.grows_acc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.grows_acc

/-- info: 'Compilatrix.Rt.Proof.labels_acc' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.labels_acc

/-- info: 'Compilatrix.Rt.Proof.open_acc' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.open_acc

/-- info: 'Compilatrix.Rt.Proof.grows_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.grows_check

/-- info: 'Compilatrix.Rt.Proof.labels_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.labels_check

/-- info: 'Compilatrix.Rt.Proof.open_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.open_check

/-- info: 'Compilatrix.Rt.Proof.ext_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ext_check

/-- info: 'Compilatrix.Rt.Proof.resolveBlock_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.resolveBlock_ok

/-- info: 'Compilatrix.Rt.Proof.holds_open' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.holds_open

/-- info: 'Compilatrix.Rt.Proof.EnvRel.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.EnvRel.mono

/-- info: 'Compilatrix.Rt.Proof.EnvRel.temp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.EnvRel.temp

/-- info: 'Compilatrix.Rt.Proof.EnvRel.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.EnvRel.insert

/-- info: 'Compilatrix.Rt.Proof.EnvRel.insert_dead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.EnvRel.insert_dead

/-- info: 'Compilatrix.Rt.Proof.ArgReads.imm' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ArgReads.imm

/-- info: 'Compilatrix.Rt.Proof.arg_eval_temp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.arg_eval_temp

/-- info: 'Compilatrix.Rt.Proof.operand_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.operand_rel

/-- info: 'Compilatrix.Rt.Proof.operands_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.operands_rel

/-- info: 'Compilatrix.Rt.Proof.except_pure' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.except_pure

/-- info: 'Compilatrix.Rt.Proof.natArgs_two' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natArgs_two

/-- info: 'Compilatrix.Rt.Proof.natArgs_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natArgs_one

/-- info: 'Compilatrix.Rt.Proof.evalRhs_prim' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.evalRhs_prim

/-- info: 'Compilatrix.Rt.Proof.primResult_nat2' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.primResult_nat2

/-- info: 'Compilatrix.Rt.Proof.straight_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.straight_star

/-- info: 'Compilatrix.Rt.Proof.straight_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.straight_sim

/-- info: 'Compilatrix.Rt.Proof.bin2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.bin2_of

/-- info: 'Compilatrix.Rt.Proof.sem_not_bool_sub' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.sem_not_bool_sub

/-- info: 'Compilatrix.Rt.Proof.prim_natSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim_natSub

/-- info: 'Compilatrix.Rt.Proof.sem_nat2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.sem_nat2

/-- info: 'Compilatrix.Rt.Proof.sem_not_bool' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.sem_not_bool

/-- info: 'Compilatrix.Rt.Proof.prim2_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim2_sim

/-- info: 'Compilatrix.Rt.Proof.prim_natLand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim_natLand

/-- info: 'Compilatrix.Rt.Proof.prim_natLor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim_natLor

/-- info: 'Compilatrix.Rt.Proof.prim_natXor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim_natXor

/-- info: 'Compilatrix.Rt.Proof.ofKey_key' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ofKey_key

/-- info: 'Compilatrix.Rt.Proof.tables_boolsOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.tables_boolsOk

/-- info: 'Compilatrix.Rt.Proof.compareOf_cases' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.compareOf_cases

/-- info: 'Compilatrix.Rt.Proof.cmp_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cmp_sem

/-- info: 'Compilatrix.Rt.Proof.bool_rel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.bool_rel

/-- info: 'Compilatrix.Rt.Proof.prim_cmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim_cmp

/-- info: 'Compilatrix.Rt.Proof.prim_natPred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim_natPred

/-- info: 'Compilatrix.Rt.Proof.prim_natShr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim_natShr

/-- info: 'Compilatrix.Rt.Proof.untag_ne_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.untag_ne_zero

/-- info: 'Compilatrix.Rt.Proof.word_one_ne_zero' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.word_one_ne_zero

/-- info: 'Compilatrix.Rt.Proof.mod_word0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.mod_word0

/-- info: 'Compilatrix.Rt.Proof.div_word0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.div_word0

/-- info: 'Compilatrix.Rt.Proof.div_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.div_word

/-- info: 'Compilatrix.Rt.Proof.mod_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.mod_word

/-- info: 'Compilatrix.Rt.Proof.prim_natDiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim_natDiv

/-- info: 'Compilatrix.Rt.Proof.prim_natMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim_natMod

/-- info: 'Compilatrix.Rt.Proof.check_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.check_code

/-- info: 'Compilatrix.Rt.Proof.check_br_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.check_br_sim

/-- info: 'Compilatrix.Rt.Proof.check_ovf_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.check_ovf_sim

/-- info: 'Compilatrix.Rt.Proof.prim_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim_natAdd

/-- info: 'Compilatrix.Rt.Proof.mul_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.mul_flag

/-- info: 'Compilatrix.Rt.Proof.prim_natMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim_natMul

/-- info: 'Compilatrix.Rt.Proof.shl_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.shl_flag

/-- info: 'Compilatrix.Rt.Proof.prim_natShl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim_natShl

/-- info: 'Compilatrix.Rt.Proof.fieldStmts_cons' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fieldStmts_cons

/-- info: 'Compilatrix.Rt.Proof.forM_stores_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.forM_stores_run

/-- info: 'Compilatrix.Rt.Proof.fieldStmts_noCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fieldStmts_noCall

/-- info: 'Compilatrix.Rt.Proof.stbind_run' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.stbind_run

/-- info: 'Compilatrix.Rt.Proof.freshReg_run' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.freshReg_run

/-- info: 'Compilatrix.Rt.Proof.alloc_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.alloc_run

/-- info: 'Compilatrix.Rt.Proof.execList_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.execList_append

/-- info: 'Compilatrix.Rt.Proof.ctx_disp_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ctx_disp_neg

/-- info: 'Compilatrix.Rt.Proof.eval_bumpOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.eval_bumpOff

/-- info: 'Compilatrix.Rt.Proof.eval_limitOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.eval_limitOff

/-- info: 'Compilatrix.Rt.Proof.eval_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.eval_mem

/-- info: 'Compilatrix.Rt.Proof.fieldOffset_nat' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fieldOffset_nat

/-- info: 'Compilatrix.Rt.Proof.load_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.load_word

/-- info: 'Compilatrix.Rt.Proof.exec_fieldStmts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.exec_fieldStmts

/-- info: 'Compilatrix.Rt.Proof.evalArgs_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.evalArgs_agree

/-- info: 'Compilatrix.Rt.Proof.evalRhs_alloc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.evalRhs_alloc

/-- info: 'Compilatrix.Rt.Proof.add_ofNat_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.add_ofNat_zero

/-- info: 'Compilatrix.Rt.Proof.ofNat_four' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ofNat_four

/-- info: 'Compilatrix.Rt.Proof.exec_allocStores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.exec_allocStores

/-- info: 'Compilatrix.Rt.Proof.alloc_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.alloc_sim

/-- info: 'Compilatrix.Rt.Proof.evalRhs_proj' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.evalRhs_proj

/-- info: 'Compilatrix.Rt.Proof.evalRhs_arg' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.evalRhs_arg

/-- info: 'Compilatrix.Rt.Proof.cell_notNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cell_notNat

/-- info: 'Compilatrix.Rt.Proof.proj_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.proj_run

/-- info: 'Compilatrix.Rt.Proof.proj_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.proj_sim

/-- info: 'Compilatrix.Rt.Proof.arg_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.arg_sim

/-- info: 'Compilatrix.Rt.Proof.enter_proc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.enter_proc

/-- info: 'Compilatrix.Rt.Proof.procCall_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.procCall_sim

/-- info: 'Compilatrix.Rt.Proof.natPow_params' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natPow_params

/-- info: 'Compilatrix.Rt.Proof.natGcd_params' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natGcd_params

/-- info: 'Compilatrix.Rt.Proof.prim_natPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim_natPow

/-- info: 'Compilatrix.Rt.Proof.prim_natGcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prim_natGcd

/-- info: 'Compilatrix.Rt.Proof.withOperands_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.withOperands_run

/-- info: 'Compilatrix.Rt.Proof.operands_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.operands_one

/-- info: 'Compilatrix.Rt.Proof.liveArgs_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.liveArgs_of

/-- info: 'Compilatrix.Rt.Proof.primitive_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.primitive_sim

/-- info: 'Compilatrix.Rt.Proof.instr_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.instr_sim

/-- info: 'Compilatrix.Rt.Proof.instr_false' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.instr_false

/-- info: 'Compilatrix.Rt.Proof.instr_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.instr_fails

/-- info: 'Compilatrix.Rt.Proof.bind_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.bind_rel

/-- info: 'Compilatrix.Rt.Proof.edge_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.edge_run

/-- info: 'Compilatrix.Rt.Proof.grows_cold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.grows_cold

/-- info: 'Compilatrix.Rt.Proof.labels_cold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.labels_cold

/-- info: 'Compilatrix.Rt.Proof.edge_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.edge_facts

/-- info: 'Compilatrix.Rt.Proof.closed_block' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.closed_block

/-- info: 'Compilatrix.Rt.Proof.close_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.close_ext

/-- info: 'Compilatrix.Rt.Proof.reachesEdge_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.reachesEdge_jump

/-- info: 'Compilatrix.Rt.Proof.reachesEdge_br' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.reachesEdge_br

/-- info: 'Compilatrix.Rt.Proof.ReachesEdge.prepend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ReachesEdge.prepend

/-- info: 'Compilatrix.Rt.Proof.edge_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.edge_complete

/-- info: 'Compilatrix.Rt.Proof.chain_nil_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chain_nil_run

/-- info: 'Compilatrix.Rt.Proof.chain_one_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chain_one_run

/-- info: 'Compilatrix.Rt.Proof.chain_cons_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chain_cons_run

/-- info: 'Compilatrix.Rt.Proof.grows_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.grows_close

/-- info: 'Compilatrix.Rt.Proof.labels_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.labels_close

/-- info: 'Compilatrix.Rt.Proof.not_open_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.not_open_close

/-- info: 'Compilatrix.Rt.Proof.grows_chainSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.grows_chainSt

/-- info: 'Compilatrix.Rt.Proof.labels_chainSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.labels_chainSt

/-- info: 'Compilatrix.Rt.Proof.open_chainSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.open_chainSt

/-- info: 'Compilatrix.Rt.Proof.chain_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chain_grows

/-- info: 'Compilatrix.Rt.Proof.chain_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chain_keys

/-- info: 'Compilatrix.Rt.Proof.chainOr_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chainOr_keys

/-- info: 'Compilatrix.Rt.Proof.chain_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chain_reaches

/-- info: 'Compilatrix.Rt.Proof.unsnoc_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.unsnoc_eq

/-- info: 'Compilatrix.Rt.Proof.unsnoc_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.unsnoc_none

/-- info: 'Compilatrix.Rt.Proof.chainOr_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chainOr_grows

/-- info: 'Compilatrix.Rt.Proof.chainOr_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chainOr_reaches

/-- info: 'Compilatrix.Rt.Proof.mapM_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.mapM_run

/-- info: 'Compilatrix.Rt.Proof.switchAlt_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.switchAlt_run

/-- info: 'Compilatrix.Rt.Proof.alts_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.alts_run

/-- info: 'Compilatrix.Rt.Proof.dflt_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.dflt_run

/-- info: 'Compilatrix.Rt.Proof.closed_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.closed_jump

/-- info: 'Compilatrix.Rt.Proof.closed_br' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.closed_br

/-- info: 'Compilatrix.Rt.Proof.natSwitch_grows' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natSwitch_grows

/-- info: 'Compilatrix.Rt.Proof.natSwitch_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natSwitch_reaches

/-- info: 'Compilatrix.Rt.Proof.run_bind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.run_bind

/-- info: 'Compilatrix.Rt.Proof.mixed_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.mixed_run

/-- info: 'Compilatrix.Rt.Proof.cellsOnly_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cellsOnly_run

/-- info: 'Compilatrix.Rt.Proof.labels_mixSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.labels_mixSt

/-- info: 'Compilatrix.Rt.Proof.open_mixSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.open_mixSt

/-- info: 'Compilatrix.Rt.Proof.grows_mixSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.grows_mixSt

/-- info: 'Compilatrix.Rt.Proof.mixed_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.mixed_facts

/-- info: 'Compilatrix.Rt.Proof.tagSwitch_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.tagSwitch_grows

/-- info: 'Compilatrix.Rt.Proof.tagSwitch_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.tagSwitch_odd

/-- info: 'Compilatrix.Rt.Proof.exec_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.exec_tag

/-- info: 'Compilatrix.Rt.Proof.mixed_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.mixed_even

/-- info: 'Compilatrix.Rt.Proof.tagSwitch_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.tagSwitch_even

/-- info: 'Compilatrix.Rt.Proof.and_one_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.and_one_toNat

/-- info: 'Compilatrix.Rt.Proof.odd_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.odd_and

/-- info: 'Compilatrix.Rt.Proof.even_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.even_and

/-- info: 'Compilatrix.Rt.Proof.ctor0Word_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ctor0Word_odd

/-- info: 'Compilatrix.Rt.Proof.erasedWord_odd' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.erasedWord_odd

/-- info: 'Compilatrix.Rt.Proof.natWord_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.natWord_odd

/-- info: 'Compilatrix.Rt.Proof.valWord_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.valWord_rel

/-- info: 'Compilatrix.Rt.Proof.keyKind_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.keyKind_zero

/-- info: 'Compilatrix.Rt.Proof.keyKind_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.keyKind_succ

/-- info: 'Compilatrix.Rt.Proof.keyKind_succ_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.keyKind_succ_of

/-- info: 'Compilatrix.Rt.Proof.keyKind_imm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.keyKind_imm

/-- info: 'Compilatrix.Rt.Proof.keyKind_notNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.keyKind_notNat

/-- info: 'Compilatrix.Rt.Proof.chainPick_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chainPick_eq

/-- info: 'Compilatrix.Rt.Proof.firstMatch_append' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.firstMatch_append

/-- info: 'Compilatrix.Rt.Proof.chainOrPick_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chainOrPick_of_match

/-- info: 'Compilatrix.Rt.Proof.chainOrPick_dflt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chainOrPick_dflt

/-- info: 'Compilatrix.Rt.Proof.selectEdge_dflt' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.selectEdge_dflt

/-- info: 'Compilatrix.Rt.Proof.link_tests' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.link_tests

/-- info: 'Compilatrix.Rt.Proof.link_find' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.link_find

/-- info: 'Compilatrix.Rt.Proof.ListRel.with_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ListRel.with_mem

/-- info: 'Compilatrix.Rt.Proof.pick_tests' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.pick_tests

/-- info: 'Compilatrix.Rt.Proof.pick_nat' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.pick_nat

/-- info: 'Compilatrix.Rt.Proof.selectEdge_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.selectEdge_none

/-- info: 'Compilatrix.Rt.Proof.unless_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.unless_run

/-- info: 'Compilatrix.Rt.Proof.throw_not_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.throw_not_ok

/-- info: 'Compilatrix.Rt.Proof.ListRel.exists_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.ListRel.exists_left

/-- info: 'Compilatrix.Rt.Proof.immTest_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.immTest_some

/-- info: 'Compilatrix.Rt.Proof.cellTest_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cellTest_some

/-- info: 'Compilatrix.Rt.Proof.immTest_snd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.immTest_snd

/-- info: 'Compilatrix.Rt.Proof.cellTest_snd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cellTest_snd

/-- info: 'Compilatrix.Rt.Proof.switch_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.switch_sim

/-- info: 'Compilatrix.Rt.Proof.closedAt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.closedAt_of

/-- info: 'Compilatrix.Rt.Proof.fails_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fails_closed

/-- info: 'Compilatrix.Rt.Proof.term_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.term_jump

/-- info: 'Compilatrix.Rt.Proof.term_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.term_ret

/-- info: 'Compilatrix.Rt.Proof.term_tcall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.term_tcall

/-- info: 'Compilatrix.Rt.Proof.term_trap' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.term_trap

/-- info: 'Compilatrix.Rt.Proof.boolEdge_some' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.boolEdge_some

/-- info: 'Compilatrix.Rt.Proof.fusedClose_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fusedClose_run

/-- info: 'Compilatrix.Rt.Proof.fused_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fused_sim

/-- info: 'Compilatrix.Rt.Proof.Mono.pure'' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.Mono.pure'

/-- info: 'Compilatrix.Rt.Proof.Mono.bind'' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.Mono.bind'

/-- info: 'Compilatrix.Rt.Proof.Mono.emit'' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.Mono.emit'

/-- info: 'Compilatrix.Rt.Proof.Mono.freshReg'' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.Mono.freshReg'

/-- info: 'Compilatrix.Rt.Proof.Mono.check'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.Mono.check'

/-- info: 'Compilatrix.Rt.Proof.Mono.throw'' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.Mono.throw'

/-- info: 'Compilatrix.Rt.Proof.Mono.lift'' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.Mono.lift'

/-- info: 'Compilatrix.Rt.Proof.Mono.untag'' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.Mono.untag'

/-- info: 'Compilatrix.Rt.Proof.Mono.divMod'' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.Mono.divMod'

/-- info: 'Compilatrix.Rt.Proof.primitive_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.primitive_mono

/-- info: 'Compilatrix.Rt.Proof.Mono.forM'' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.Mono.forM'

/-- info: 'Compilatrix.Rt.Proof.alloc_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.alloc_mono

/-- info: 'Compilatrix.Rt.Proof.withOperands_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.withOperands_mono

/-- info: 'Compilatrix.Rt.Proof.instr_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.instr_mono

/-- info: 'Compilatrix.Rt.Proof.instrs_cons_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.instrs_cons_run

/-- info: 'Compilatrix.Rt.Proof.instrs_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.instrs_grows

/-- info: 'Compilatrix.Rt.Proof.switch_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.switch_grows

/-- info: 'Compilatrix.Rt.Proof.fusedSwitch_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fusedSwitch_grows

/-- info: 'Compilatrix.Rt.Proof.term_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.term_grows

/-- info: 'Compilatrix.Rt.Proof.unsnoc_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.unsnoc_some

/-- info: 'Compilatrix.Rt.Proof.fusable_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fusable_some

/-- info: 'Compilatrix.Rt.Proof.restAct_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.restAct_body

/-- info: 'Compilatrix.Rt.Proof.run_bind_of' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.run_bind_of

/-- info: 'Compilatrix.Rt.Proof.instrs_then' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.instrs_then

/-- info: 'Compilatrix.Rt.Proof.rest_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.rest_cons

/-- info: 'Compilatrix.Rt.Proof.fusedEnd_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fusedEnd_grows

/-- info: 'Compilatrix.Rt.Proof.rest_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.rest_grows

/-- info: 'Compilatrix.Rt.Proof.getD_foldl_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.getD_foldl_count

/-- info: 'Compilatrix.Rt.Proof.useCounts_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.useCounts_getD

/-- info: 'Compilatrix.Rt.Proof.le_sum_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.le_sum_map

/-- info: 'Compilatrix.Rt.Proof.two_le_sum_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.two_le_sum_map

/-- info: 'Compilatrix.Rt.Proof.count_flatMap_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.count_flatMap_ge

/-- info: 'Compilatrix.Rt.Proof.count_blockUses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.count_blockUses

/-- info: 'Compilatrix.Rt.Proof.fused_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fused_once

/-- info: 'Compilatrix.Rt.Proof.except_mapM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.except_mapM

/-- info: 'Compilatrix.Rt.Proof.chunkBlocks_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chunkBlocks_ok

/-- info: 'Compilatrix.Rt.Proof.labels_openSt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.labels_openSt

/-- info: 'Compilatrix.Rt.Proof.open_openSt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.open_openSt

/-- info: 'Compilatrix.Rt.Proof.block_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.block_run

/-- info: 'Compilatrix.Rt.Proof.blockCode_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.blockCode_grows

/-- info: 'Compilatrix.Rt.Proof.chunks_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chunks_spec

/-- info: 'Compilatrix.Rt.Proof.chunkStarts_foldl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chunkStarts_foldl

/-- info: 'Compilatrix.Rt.Proof.chunkStarts_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chunkStarts_get

/-- info: 'Compilatrix.Rt.Proof.chunkOff_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chunkOff_mono

/-- info: 'Compilatrix.Rt.Proof.resolveChunks_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.resolveChunks_spec

/-- info: 'Compilatrix.Rt.Proof.misordered_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.misordered_none

/-- info: 'Compilatrix.Rt.Proof.chunk_head' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.chunk_head

/-- info: 'Compilatrix.Rt.Proof.lowered_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.lowered_of

/-- info: 'Compilatrix.Rt.Proof.functionRaw_lowered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.functionRaw_lowered

/-- info: 'Compilatrix.Rt.Proof.foldl_max_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.foldl_max_ge

/-- info: 'Compilatrix.Rt.Proof.defs_lt_sup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.defs_lt_sup

/-- info: 'Compilatrix.Rt.Proof.SuspAt.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.SuspAt.mono

/-- info: 'Compilatrix.Rt.Proof.stack_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.stack_mono

/-- info: 'Compilatrix.Rt.Proof.fun_unique' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fun_unique

/-- info: 'Compilatrix.Rt.Proof.bindParams_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.bindParams_some

/-- info: 'Compilatrix.Rt.Proof.bindParams_get_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.bindParams_get_not_mem

/-- info: 'Compilatrix.Rt.Proof.evalArgs_bindParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.evalArgs_bindParams

/-- info: 'Compilatrix.Rt.Proof.envRel_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.envRel_leaf

/-- info: 'Compilatrix.Rt.Proof.params_lt_sup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.params_lt_sup

/-- info: 'Compilatrix.Rt.Proof.fusable_body_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fusable_body_ne

/-- info: 'Compilatrix.Rt.Proof.runAt_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.runAt_head

/-- info: 'Compilatrix.Rt.Proof.entry_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.entry_rel

/-- info: 'Compilatrix.Rt.Proof.step_enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.step_enter

/-- info: 'Compilatrix.Rt.Proof.step_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.step_return

/-- info: 'Compilatrix.Rt.Proof.final_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.final_return

/-- info: 'Compilatrix.Rt.Proof.state_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.state_eq

/-- info: 'Compilatrix.Rt.Proof.instr_def_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.instr_def_lt

/-- info: 'Compilatrix.Rt.Proof.instr_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.instr_live

/-- info: 'Compilatrix.Rt.Proof.fused_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fused_last

/-- info: 'Compilatrix.Rt.Proof.evalArg_insert_irrel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.evalArg_insert_irrel

/-- info: 'Compilatrix.Rt.Proof.evalArgs_insert_irrel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.evalArgs_insert_irrel

/-- info: 'Compilatrix.Rt.Proof.evalArgs_two' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.evalArgs_two

/-- info: 'Compilatrix.Rt.Proof.step_instr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.step_instr

/-- info: 'Compilatrix.Rt.Proof.step_call_instr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.step_call_instr

/-- info: 'Compilatrix.Rt.Proof.edge_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.edge_live

/-- info: 'Compilatrix.Rt.Proof.edge_live.argVars_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.edge_live.argVars_mem

/-- info: 'Compilatrix.Rt.Proof.merged_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.merged_target

/-- info: 'Compilatrix.Rt.Proof.take_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.take_edge

/-- info: 'Compilatrix.Rt.Proof.rest_nil' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.rest_nil

/-- info: 'Compilatrix.Rt.Proof.takeEdge_charge' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.takeEdge_charge

/-- info: 'Compilatrix.Rt.Proof.term_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.term_live

/-- info: 'Compilatrix.Rt.Proof.argVars_of_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.argVars_of_mem

/-- info: 'Compilatrix.Rt.Proof.lir_evalArgs_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.lir_evalArgs_two

/-- info: 'Compilatrix.Rt.Proof.key_of_bool' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.key_of_bool

/-- info: 'Compilatrix.Rt.Proof.selectEdge_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.selectEdge_mem

/-- info: 'Compilatrix.Rt.Proof.step_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.step_term

/-- info: 'Compilatrix.Rt.Proof.takeEdge_ne_trap' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.takeEdge_ne_trap

/-- info: 'Compilatrix.Rt.Proof.final_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.final_trap

/-- info: 'Compilatrix.Rt.Proof.evalRhs_ok_or_stuck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.evalRhs_ok_or_stuck

/-- info: 'Compilatrix.Rt.Proof.step_bind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.step_bind

/-- info: 'Compilatrix.Rt.Proof.diagram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.diagram

/-- info: 'Compilatrix.Rt.Proof.contains_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.contains_insert

/-- info: 'Compilatrix.Rt.Proof.foldl_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.foldl_contains

/-- info: 'Compilatrix.Rt.Proof.reach_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.reach_mono

/-- info: 'Compilatrix.Rt.Proof.reachable_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.reachable_zero

/-- info: 'Compilatrix.Rt.Proof.kept_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.kept_spec

/-- info: 'Compilatrix.Rt.Proof.kept_le_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.kept_le_iff

/-- info: 'Compilatrix.Rt.Proof.rank_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.rank_get

/-- info: 'Compilatrix.Rt.Proof.kept_of_seen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.kept_of_seen

/-- info: 'Compilatrix.Rt.Proof.prune_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.prune_sim

/-- info: 'Compilatrix.Rt.Proof.function_spec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.function_spec

/-- info: 'Compilatrix.Rt.Proof.functions_spec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.functions_spec

/-- info: 'Compilatrix.Rt.Proof.lower_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.lower_spec

/-- info: 'Compilatrix.Rt.Proof.stageProg_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.stageProg_get

/-- info: 'Compilatrix.Rt.Proof.lower_lowers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.lower_lowers

/-- info: 'Compilatrix.Rt.Proof.target_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.target_raw

/-- info: 'Compilatrix.Rt.Proof.raw_ne_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.raw_ne_nil

/-- info: 'Compilatrix.Rt.Proof.raw_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.raw_pruned

/-- info: 'Compilatrix.Rt.Proof.pruned_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.pruned_split

/-- info: 'Compilatrix.Rt.Proof.lower_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.lower_ordered

/-- info: 'Compilatrix.Rt.Proof.call_step_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.call_step_cases

/-- info: 'Compilatrix.Rt.Proof.lower_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.lower_correct

/-- info: 'Compilatrix.Rt.Proof.toFirList_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.toFirList_length

/-- info: 'Compilatrix.Rt.Proof.fields_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.fields_readback

/-- info: 'Compilatrix.Rt.Proof.readback_toFir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.readback_toFir

/-- info: 'Compilatrix.Rt.Proof.readback_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.readback_sound

/-- info: 'Compilatrix.Rt.Proof.and_alignDown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.and_alignDown

/-- info: 'Compilatrix.Rt.Proof.word_alignDown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.word_alignDown

/-- info: 'Compilatrix.Rt.Proof.zeros_readable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.zeros_readable

/-- info: 'Compilatrix.Rt.Proof.zeros_writable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.zeros_writable

/-- info: 'Compilatrix.Rt.Proof.execList_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.execList_zeros

/-- info: 'Compilatrix.Rt.Proof.zeros_keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.zeros_keep

/-- info: 'Compilatrix.Rt.Proof.cxInit_b0' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cxInit_b0

/-- info: 'Compilatrix.Rt.Proof.cxInit_b1' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cxInit_b1

/-- info: 'Compilatrix.Rt.Proof.cxInit_b2' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cxInit_b2

/-- info: 'Compilatrix.Rt.Proof.cxInit_b3' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cxInit_b3

/-- info: 'Compilatrix.Rt.Proof.cxInit_b4' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cxInit_b4

/-- info: 'Compilatrix.Rt.Proof.cxInit_b5' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cxInit_b5

/-- info: 'Compilatrix.Rt.Proof.cxInit_b6' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cxInit_b6

/-- info: 'Compilatrix.Rt.Proof.cxInit_b7' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cxInit_b7

/-- info: 'Compilatrix.Rt.Proof.cxInit_b8' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cxInit_b8

/-- info: 'Compilatrix.Rt.Proof.cxInit_params' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cxInit_params

/-- info: 'Compilatrix.Rt.Proof.body8_noCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.body8_noCall

/-- info: 'Compilatrix.Rt.Proof.execList_cons_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.execList_cons_of

/-- info: 'Compilatrix.Rt.Proof.exec_assign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.exec_assign

/-- info: 'Compilatrix.Rt.Proof.exec_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.exec_store

/-- info: 'Compilatrix.Rt.Proof.eval_fail_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.eval_fail_of

/-- info: 'Compilatrix.Rt.Proof.eval_done_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.eval_done_of

/-- info: 'Compilatrix.Rt.Proof.and7_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.and7_toNat

/-- info: 'Compilatrix.Rt.Proof.base_toNat' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.base_toNat

/-- info: 'Compilatrix.Rt.Proof.add_word_toNat' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.add_word_toNat

/-- info: 'Compilatrix.Rt.Proof.zeroOff_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.zeroOff_mem

/-- info: 'Compilatrix.Rt.Proof.zeroAddr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.zeroAddr

/-- info: 'Compilatrix.Rt.Proof.region_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.region_at

/-- info: 'Compilatrix.Rt.Proof.bumpOf_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.bumpOf_toNat

/-- info: 'Compilatrix.Rt.Proof.cxInit_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cxInit_cases

/-- info: 'Compilatrix.Rt.Proof.cxInit_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cxInit_fail

/-- info: 'Compilatrix.Rt.Proof.cxInit_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Proof.cxInit_ok

/-- info: 'Compilatrix.Rt.lower_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.lower_correct

/-- info: 'Compilatrix.Rt.lower_correct_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.lower_correct_traced

/-- info: 'Compilatrix.Rt.readback_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.readback_sound

/-- info: 'Compilatrix.Rt.result_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.result_readback

/-- info: 'Compilatrix.Rt.lower_cxInit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.lower_cxInit

/-- info: 'Compilatrix.Rt.init_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.init_correct
