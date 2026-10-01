import Compilatrix.X86.Layout.Proof.Tunnel
import Compilatrix.X86.Layout.Proof.Order
import Compilatrix.X86.Layout.Proof.Rows
import Compilatrix.X86.Layout.Proof.Linearize
import Compilatrix.X86.Layout.Proof.Transport

/-! Required axiom fences for the layout proofs (M2.6b): tunnelling keeps
programs well formed and is a measured simulation (`tunnel_wellFormed`,
`tunnel_step`, `tunnel_safeSteps`, `tunnel_run`), `Order.check` is sound
(`Order.check_sound`: duplicate free, in range, entry, reachable blocks,
closure under targets, groups), rows on related cores and what they leave
alone (`exec_pair`, `run_bytes_outside`, `TokensAt.exec`), linearisation is
a lock-step simulation (`lin_safe`, `lin_step`, `lin_safeSteps`,
`linearize_run`, `LRel.exit`), and the composed `transport` from the
stacked program to the laid-out one. Generated from the proof modules'
public theorems; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.X86.Layout.Proof.wellFormed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.wellFormed_iff

/-- info: 'Compilatrix.X86.Layout.Proof.wellFormed_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.wellFormed_block

/-- info: 'Compilatrix.X86.Layout.Proof.hasBlock_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.hasBlock_iff

/-- info: 'Compilatrix.X86.Layout.Proof.jump_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.jump_valid

/-- info: 'Compilatrix.X86.Layout.Proof.ChainN.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.ChainN.zero

/-- info: 'Compilatrix.X86.Layout.Proof.ChainN.chainTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.ChainN.chainTo

/-- info: 'Compilatrix.X86.Layout.Proof.chase_chainN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.chase_chainN

/-- info: 'Compilatrix.X86.Layout.Proof.chainTo_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.chainTo_valid

/-- info: 'Compilatrix.X86.Layout.Proof.chase_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.chase_valid

/-- info: 'Compilatrix.X86.Layout.Proof.tunnel_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.tunnel_entry

/-- info: 'Compilatrix.X86.Layout.Proof.tunnel_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.tunnel_size

/-- info: 'Compilatrix.X86.Layout.Proof.tunnel_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.tunnel_get

/-- info: 'Compilatrix.X86.Layout.Proof.tunnel_hasBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.tunnel_hasBlock

/-- info: 'Compilatrix.X86.Layout.Proof.instr_targetsValid_congr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.instr_targetsValid_congr

/-- info: 'Compilatrix.X86.Layout.Proof.tunnel_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.tunnel_wellFormed

/-- info: 'Compilatrix.X86.Layout.Proof.goto_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.goto_congr

/-- info: 'Compilatrix.X86.Layout.Proof.executeInstr_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.executeInstr_congr

/-- info: 'Compilatrix.X86.Layout.Proof.executeTerminator_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.executeTerminator_congr

/-- info: 'Compilatrix.X86.Layout.Proof.goto_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.goto_valid

/-- info: 'Compilatrix.X86.Layout.Proof.TRel.eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.TRel.eq

/-- info: 'Compilatrix.X86.Layout.Proof.TRel.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.TRel.refl

/-- info: 'Compilatrix.X86.Layout.Proof.tunnel_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.tunnel_step

/-- info: 'Compilatrix.X86.Layout.Proof.tunnel_safeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.tunnel_safeAt

/-- info: 'Compilatrix.X86.Layout.Proof.tunnel_holeStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.tunnel_holeStep

/-- info: 'Compilatrix.X86.Layout.Proof.chain_head_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.chain_head_step

/-- info: 'Compilatrix.X86.Layout.Proof.tunnel_safeSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.tunnel_safeSteps

/-- info: 'Compilatrix.X86.Layout.Proof.tunnel_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.tunnel_initial

/-- info: 'Compilatrix.X86.Layout.Proof.tunnel_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.tunnel_run

/-- info: 'Compilatrix.X86.Layout.Proof.TRel.exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.TRel.exit

/-- info: 'Compilatrix.X86.Layout.Proof.TRel.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.TRel.running

/-- info: 'Compilatrix.X86.Layout.Proof.contains_foldl_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.contains_foldl_insert

/-- info: 'Compilatrix.X86.Layout.Proof.contains_setOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.contains_setOf

/-- info: 'Compilatrix.X86.Layout.Proof.size_foldl_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.size_foldl_insert

/-- info: 'Compilatrix.X86.Layout.Proof.nodup_of_setOf_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.nodup_of_setOf_size

/-- info: 'Compilatrix.X86.Layout.Proof.Order.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.Order.check_sound

/-- info: 'Compilatrix.X86.Layout.Proof.OperationSafe.noFrames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.OperationSafe.noFrames

/-- info: 'Compilatrix.X86.Layout.Proof.exec_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.exec_pair

/-- info: 'Compilatrix.X86.Layout.Proof.write?_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.write?_bytes

/-- info: 'Compilatrix.X86.Layout.Proof.store_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.store_bytes

/-- info: 'Compilatrix.X86.Layout.Proof.writeSlots_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.writeSlots_bytes

/-- info: 'Compilatrix.X86.Layout.Proof.writeImplicits_memory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.writeImplicits_memory

/-- info: 'Compilatrix.X86.Layout.Proof.stage_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.stage_bytes

/-- info: 'Compilatrix.X86.Layout.Proof.run_bytes_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.run_bytes_outside

/-- info: 'Compilatrix.X86.Layout.Proof.exec_bytes_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.exec_bytes_outside

/-- info: 'Compilatrix.X86.Layout.Proof.TokensAt.bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.TokensAt.bytes

/-- info: 'Compilatrix.X86.Layout.Proof.TokensAt.suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.TokensAt.suffix

/-- info: 'Compilatrix.X86.Layout.Proof.TokensAt.exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.TokensAt.exec

/-- info: 'Compilatrix.X86.Layout.Proof.linearize_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.linearize_eq

/-- info: 'Compilatrix.X86.Layout.Proof.run_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.run_eq

/-- info: 'Compilatrix.X86.Layout.Proof.blockMap_get_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.blockMap_get_complete

/-- info: 'Compilatrix.X86.Layout.Proof.posOf_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.posOf_get

/-- info: 'Compilatrix.X86.Layout.Proof.Setup.index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.Setup.index

/-- info: 'Compilatrix.X86.Layout.Proof.Setup.block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.Setup.block

/-- info: 'Compilatrix.X86.Layout.Proof.Setup.hasBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.Setup.hasBlock

/-- info: 'Compilatrix.X86.Layout.Proof.Setup.hasBlock_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.Setup.hasBlock_source

/-- info: 'Compilatrix.X86.Layout.Proof.Setup.target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.Setup.target

/-- info: 'Compilatrix.X86.Layout.Proof.linBlk_instr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.linBlk_instr

/-- info: 'Compilatrix.X86.Layout.Proof.linBlk_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.linBlk_size

/-- info: 'Compilatrix.X86.Layout.Proof.linBlk_terminator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.linBlk_terminator

/-- info: 'Compilatrix.X86.Layout.Proof.call_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.call_target

/-- info: 'Compilatrix.X86.Layout.Proof.FramesRel.slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.FramesRel.slots

/-- info: 'Compilatrix.X86.Layout.Proof.FramesRel.drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.FramesRel.drop

/-- info: 'Compilatrix.X86.Layout.Proof.FramesRel.findIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.FramesRel.findIdx

/-- info: 'Compilatrix.X86.Layout.Proof.FramesRel.cutAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.FramesRel.cutAt

/-- info: 'Compilatrix.X86.Layout.Proof.FramesRel.disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.FramesRel.disjoint

/-- info: 'Compilatrix.X86.Layout.Proof.FramesRel.nil_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.FramesRel.nil_iff

/-- info: 'Compilatrix.X86.Layout.Proof.FramesRel.cons_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.FramesRel.cons_inv

/-- info: 'Compilatrix.X86.Layout.Proof.FramesRel.nil_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.FramesRel.nil_inv

/-- info: 'Compilatrix.X86.Layout.Proof.LRel.memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.LRel.memory

/-- info: 'Compilatrix.X86.Layout.Proof.LRel.readReg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.LRel.readReg

/-- info: 'Compilatrix.X86.Layout.Proof.LRel.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.LRel.running

/-- info: 'Compilatrix.X86.Layout.Proof.LRel.trapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.LRel.trapped

/-- info: 'Compilatrix.X86.Layout.Proof.LRel.halted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.LRel.halted

/-- info: 'Compilatrix.X86.Layout.Proof.slots_eq_of_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.slots_eq_of_rel

/-- info: 'Compilatrix.X86.Layout.Proof.OperationSafe.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.OperationSafe.transfer

/-- info: 'Compilatrix.X86.Layout.Proof.nextHoles_registers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.nextHoles_registers

/-- info: 'Compilatrix.X86.Layout.Proof.calleeSavedSnapshot_registers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.calleeSavedSnapshot_registers

/-- info: 'Compilatrix.X86.Layout.Proof.calleeSavedMatch_registers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.calleeSavedMatch_registers

/-- info: 'Compilatrix.X86.Layout.Proof.read64?_tokens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.read64?_tokens

/-- info: 'Compilatrix.X86.Layout.Proof.linTerm_branch' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.linTerm_branch

/-- info: 'Compilatrix.X86.Layout.Proof.lin_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.lin_safe

/-- info: 'Compilatrix.X86.Layout.Proof.PC.next?_rename' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.PC.next?_rename

/-- info: 'Compilatrix.X86.Layout.Proof.PC.next?_block' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.PC.next?_block

/-- info: 'Compilatrix.X86.Layout.Proof.LRel.ofTrapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.LRel.ofTrapped

/-- info: 'Compilatrix.X86.Layout.Proof.LRel.trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.LRel.trap

/-- info: 'Compilatrix.X86.Layout.Proof.afterRow_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.afterRow_rel

/-- info: 'Compilatrix.X86.Layout.Proof.exec_flagsOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.exec_flagsOnly

/-- info: 'Compilatrix.X86.Layout.Proof.fused_flagsOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.fused_flagsOnly

/-- info: 'Compilatrix.X86.Layout.Proof.write64_bytes_outside'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.write64_bytes_outside'

/-- info: 'Compilatrix.X86.Layout.Proof.lin_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.lin_step

/-- info: 'Compilatrix.X86.Layout.Proof.lin_safeSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.lin_safeSteps

/-- info: 'Compilatrix.X86.Layout.Proof.lin_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.lin_initial

/-- info: 'Compilatrix.X86.Layout.Proof.setup_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.setup_of_run

/-- info: 'Compilatrix.X86.Layout.Proof.linearize_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.linearize_run

/-- info: 'Compilatrix.X86.Layout.Proof.LRel.exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.LRel.exit

/-- info: 'Compilatrix.X86.Layout.Proof.LRel.status_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.LRel.status_running

/-- info: 'Compilatrix.X86.Layout.Proof.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.transport

/-- info: 'Compilatrix.X86.Layout.Proof.transport_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.Proof.transport_end
