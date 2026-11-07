import IxCC.X86.Layout.Proof.Tunnel
import IxCC.X86.Layout.Proof.Order
import IxCC.X86.Layout.Proof.Rows
import IxCC.X86.Layout.Proof.Linearize
import IxCC.X86.Layout.Proof.Transport

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

/-- info: 'IxCC.X86.Layout.Proof.wellFormed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.wellFormed_iff

/-- info: 'IxCC.X86.Layout.Proof.wellFormed_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.wellFormed_block

/-- info: 'IxCC.X86.Layout.Proof.hasBlock_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.hasBlock_iff

/-- info: 'IxCC.X86.Layout.Proof.jump_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.jump_valid

/-- info: 'IxCC.X86.Layout.Proof.ChainN.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.ChainN.zero

/-- info: 'IxCC.X86.Layout.Proof.ChainN.chainTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.ChainN.chainTo

/-- info: 'IxCC.X86.Layout.Proof.chase_chainN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.chase_chainN

/-- info: 'IxCC.X86.Layout.Proof.chainTo_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.chainTo_valid

/-- info: 'IxCC.X86.Layout.Proof.chase_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.chase_valid

/-- info: 'IxCC.X86.Layout.Proof.tunnel_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.tunnel_entry

/-- info: 'IxCC.X86.Layout.Proof.tunnel_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.tunnel_size

/-- info: 'IxCC.X86.Layout.Proof.tunnel_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.tunnel_get

/-- info: 'IxCC.X86.Layout.Proof.tunnel_hasBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.tunnel_hasBlock

/-- info: 'IxCC.X86.Layout.Proof.instr_targetsValid_congr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.instr_targetsValid_congr

/-- info: 'IxCC.X86.Layout.Proof.tunnel_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.tunnel_wellFormed

/-- info: 'IxCC.X86.Layout.Proof.goto_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.goto_congr

/-- info: 'IxCC.X86.Layout.Proof.executeInstr_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.executeInstr_congr

/-- info: 'IxCC.X86.Layout.Proof.executeTerminator_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.executeTerminator_congr

/-- info: 'IxCC.X86.Layout.Proof.goto_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.goto_valid

/-- info: 'IxCC.X86.Layout.Proof.TRel.eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.TRel.eq

/-- info: 'IxCC.X86.Layout.Proof.TRel.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.TRel.refl

/-- info: 'IxCC.X86.Layout.Proof.tunnel_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.tunnel_step

/-- info: 'IxCC.X86.Layout.Proof.tunnel_safeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.tunnel_safeAt

/-- info: 'IxCC.X86.Layout.Proof.tunnel_holeStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.tunnel_holeStep

/-- info: 'IxCC.X86.Layout.Proof.chain_head_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.chain_head_step

/-- info: 'IxCC.X86.Layout.Proof.tunnel_safeSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.tunnel_safeSteps

/-- info: 'IxCC.X86.Layout.Proof.tunnel_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.tunnel_initial

/-- info: 'IxCC.X86.Layout.Proof.tunnel_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.tunnel_run

/-- info: 'IxCC.X86.Layout.Proof.TRel.exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.TRel.exit

/-- info: 'IxCC.X86.Layout.Proof.TRel.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.TRel.running

/-- info: 'IxCC.X86.Layout.Proof.contains_foldl_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.contains_foldl_insert

/-- info: 'IxCC.X86.Layout.Proof.contains_setOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.contains_setOf

/-- info: 'IxCC.X86.Layout.Proof.size_foldl_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.size_foldl_insert

/-- info: 'IxCC.X86.Layout.Proof.nodup_of_setOf_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.nodup_of_setOf_size

/-- info: 'IxCC.X86.Layout.Proof.Order.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.Order.check_sound

/-- info: 'IxCC.X86.Layout.Proof.OperationSafe.noFrames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.OperationSafe.noFrames

/-- info: 'IxCC.X86.Layout.Proof.exec_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.exec_pair

/-- info: 'IxCC.X86.Layout.Proof.write?_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.write?_bytes

/-- info: 'IxCC.X86.Layout.Proof.store_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.store_bytes

/-- info: 'IxCC.X86.Layout.Proof.writeSlots_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.writeSlots_bytes

/-- info: 'IxCC.X86.Layout.Proof.writeImplicits_memory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.writeImplicits_memory

/-- info: 'IxCC.X86.Layout.Proof.stage_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.stage_bytes

/-- info: 'IxCC.X86.Layout.Proof.run_bytes_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.run_bytes_outside

/-- info: 'IxCC.X86.Layout.Proof.exec_bytes_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.exec_bytes_outside

/-- info: 'IxCC.X86.Layout.Proof.TokensAt.bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.TokensAt.bytes

/-- info: 'IxCC.X86.Layout.Proof.TokensAt.suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.TokensAt.suffix

/-- info: 'IxCC.X86.Layout.Proof.TokensAt.exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.TokensAt.exec

/-- info: 'IxCC.X86.Layout.Proof.linearize_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.linearize_eq

/-- info: 'IxCC.X86.Layout.Proof.run_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.run_eq

/-- info: 'IxCC.X86.Layout.Proof.blockMap_get_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.blockMap_get_complete

/-- info: 'IxCC.X86.Layout.Proof.posOf_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.posOf_get

/-- info: 'IxCC.X86.Layout.Proof.Setup.index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.Setup.index

/-- info: 'IxCC.X86.Layout.Proof.Setup.block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.Setup.block

/-- info: 'IxCC.X86.Layout.Proof.Setup.hasBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.Setup.hasBlock

/-- info: 'IxCC.X86.Layout.Proof.Setup.hasBlock_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.Setup.hasBlock_source

/-- info: 'IxCC.X86.Layout.Proof.Setup.target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.Setup.target

/-- info: 'IxCC.X86.Layout.Proof.linBlk_instr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.linBlk_instr

/-- info: 'IxCC.X86.Layout.Proof.linBlk_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.linBlk_size

/-- info: 'IxCC.X86.Layout.Proof.linBlk_terminator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.linBlk_terminator

/-- info: 'IxCC.X86.Layout.Proof.call_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.call_target

/-- info: 'IxCC.X86.Layout.Proof.FramesRel.slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.FramesRel.slots

/-- info: 'IxCC.X86.Layout.Proof.FramesRel.drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.FramesRel.drop

/-- info: 'IxCC.X86.Layout.Proof.FramesRel.findIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.FramesRel.findIdx

/-- info: 'IxCC.X86.Layout.Proof.FramesRel.cutAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.FramesRel.cutAt

/-- info: 'IxCC.X86.Layout.Proof.FramesRel.disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.FramesRel.disjoint

/-- info: 'IxCC.X86.Layout.Proof.FramesRel.nil_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.FramesRel.nil_iff

/-- info: 'IxCC.X86.Layout.Proof.FramesRel.cons_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.FramesRel.cons_inv

/-- info: 'IxCC.X86.Layout.Proof.FramesRel.nil_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.FramesRel.nil_inv

/-- info: 'IxCC.X86.Layout.Proof.LRel.memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.LRel.memory

/-- info: 'IxCC.X86.Layout.Proof.LRel.readReg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.LRel.readReg

/-- info: 'IxCC.X86.Layout.Proof.LRel.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.LRel.running

/-- info: 'IxCC.X86.Layout.Proof.LRel.trapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.LRel.trapped

/-- info: 'IxCC.X86.Layout.Proof.LRel.halted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.LRel.halted

/-- info: 'IxCC.X86.Layout.Proof.slots_eq_of_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.slots_eq_of_rel

/-- info: 'IxCC.X86.Layout.Proof.OperationSafe.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.OperationSafe.transfer

/-- info: 'IxCC.X86.Layout.Proof.nextHoles_registers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.nextHoles_registers

/-- info: 'IxCC.X86.Layout.Proof.calleeSavedSnapshot_registers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.calleeSavedSnapshot_registers

/-- info: 'IxCC.X86.Layout.Proof.calleeSavedMatch_registers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.calleeSavedMatch_registers

/-- info: 'IxCC.X86.Layout.Proof.read64?_tokens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.read64?_tokens

/-- info: 'IxCC.X86.Layout.Proof.linTerm_branch' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.linTerm_branch

/-- info: 'IxCC.X86.Layout.Proof.lin_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.lin_safe

/-- info: 'IxCC.X86.Layout.Proof.PC.next?_rename' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.PC.next?_rename

/-- info: 'IxCC.X86.Layout.Proof.PC.next?_block' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.PC.next?_block

/-- info: 'IxCC.X86.Layout.Proof.LRel.ofTrapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.LRel.ofTrapped

/-- info: 'IxCC.X86.Layout.Proof.LRel.trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.LRel.trap

/-- info: 'IxCC.X86.Layout.Proof.afterRow_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.afterRow_rel

/-- info: 'IxCC.X86.Layout.Proof.exec_flagsOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.exec_flagsOnly

/-- info: 'IxCC.X86.Layout.Proof.fused_flagsOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.fused_flagsOnly

/-- info: 'IxCC.X86.Layout.Proof.write64_bytes_outside'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.write64_bytes_outside'

/-- info: 'IxCC.X86.Layout.Proof.lin_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.lin_step

/-- info: 'IxCC.X86.Layout.Proof.lin_safeSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.lin_safeSteps

/-- info: 'IxCC.X86.Layout.Proof.lin_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.lin_initial

/-- info: 'IxCC.X86.Layout.Proof.setup_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.setup_of_run

/-- info: 'IxCC.X86.Layout.Proof.linearize_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.linearize_run

/-- info: 'IxCC.X86.Layout.Proof.LRel.exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.LRel.exit

/-- info: 'IxCC.X86.Layout.Proof.LRel.status_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.LRel.status_running

/-- info: 'IxCC.X86.Layout.Proof.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.transport

/-- info: 'IxCC.X86.Layout.Proof.transport_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.Proof.transport_end
