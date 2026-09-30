import Compilatrix.Xv.Stacking.Frame
import Compilatrix.X86.Layout.Tunnel
import Compilatrix.X86.Layout.Linearize

/-! Required axiom fences for stacking and layout (M1.B5): what the frame
layout check guarantees, that tunnelled targets are reached by executing
empty jumps, and that an inverted branch goes where the original goes.
Expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.Xv.Stacking.FrameLayout.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.FrameLayout.check_sound

/-- info: 'Compilatrix.Xv.Stacking.FrameLayout.Sound.separated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.FrameLayout.Sound.separated

/-- info: 'Compilatrix.Xv.Stacking.FrameLayout.Sound.frameless' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.FrameLayout.Sound.frameless

/-- info: 'Compilatrix.X86.Layout.chase_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.chase_chain

/-- info: 'Compilatrix.X86.Layout.step_emptyJump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.step_emptyJump

/-- info: 'Compilatrix.X86.Layout.run_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Layout.run_chain

/-- info: 'Compilatrix.X86.Condition.negate_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Condition.negate_holds

/-- info: 'Compilatrix.X86.ByteEval.Flags.test_negate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ByteEval.Flags.test_negate

/-- info: 'Compilatrix.X86.Terminator.wellFormed_negate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Terminator.wellFormed_negate

/-- info: 'Compilatrix.X86.executeTerminator_negate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.executeTerminator_negate
