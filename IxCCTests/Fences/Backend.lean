import IxCC.Xv.Stacking.Frame
import IxCC.X86.Layout.Tunnel
import IxCC.X86.Layout.Linearize

/-! Required axiom fences for stacking and layout (M1.B5): what the frame
layout check guarantees, that tunnelled targets are reached by executing
empty jumps, that an inverted branch goes where the original goes, and
that a branch's `Reach` mark (fall-through) is invisible to the typed
semantics.
Expected messages are preserved verbatim. -/

/-- info: 'IxCC.Xv.Stacking.FrameLayout.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.FrameLayout.check_sound

/-- info: 'IxCC.Xv.Stacking.FrameLayout.Sound.separated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.FrameLayout.Sound.separated

/-- info: 'IxCC.Xv.Stacking.FrameLayout.Sound.frameless' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.FrameLayout.Sound.frameless

/-- info: 'IxCC.X86.Layout.chase_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.chase_chain

/-- info: 'IxCC.X86.Layout.step_emptyJump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.step_emptyJump

/-- info: 'IxCC.X86.Layout.run_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Layout.run_chain

/-- info: 'IxCC.X86.Condition.negate_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Condition.negate_holds

/-- info: 'IxCC.X86.ByteEval.Flags.test_negate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ByteEval.Flags.test_negate

/-- info: 'IxCC.X86.Terminator.wellFormed_negate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Terminator.wellFormed_negate

/-- info: 'IxCC.X86.executeTerminator_negate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.executeTerminator_negate

/-- info: 'IxCC.X86.executeTerminator_reach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.executeTerminator_reach

/-- info: 'IxCC.X86.Terminator.wellFormed_reach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Terminator.wellFormed_reach
