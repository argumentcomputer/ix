import Ix.Cert.ReaderStreamsTrace
import Ix.Cert.LayoutsHold

/-! # The certified compiler's correctness, proved

`ReaderStreamsTrace.compileCorrect_of` proves `CompileCorrect` from three statements about the
compile: the closure's record layout (`ReaderStreamsTrace.LayoutsHold`) and the definitions'
hints (`ReaderStreamsTrace.SingletonsHinted`, `ReaderStreamsTrace.BlocksHinted`). This module
discharges them: the layout by `LayoutsHold.layouts_hold`, a singleton definition's hint, read at
its lone record, by `TraceFold.definition_needs`, and the hint of a member of a block of several
definitions, read at its projection record, by `TraceFold.block_compiled`. So `compileCorrect`
proves `CompileCorrect` with no premises, on the standard three axioms. -/

namespace Ix.Cert.ReaderStreamsTrace

universe w

/-- **Every accepted closure's compiled records lie as quotient Source's graph says**
(`LayoutsHold.layouts_hold`). -/
theorem layoutsHold : LayoutsHold :=
  @Ix.Cert.LayoutsHold.layouts_hold

/-- **Every singleton definition compiles alone at the hint quotient Source reads it at**: the
reader reads it at the lone record (`TraceFold.definition_needs`). -/
theorem singletonsHinted : SingletonsHinted := by
  intro _ _ _ _ _ _ _ P scheduled idx _ _ hgr
  exact TraceFold.definition_needs P scheduled idx hgr

/-- **Every block of several definitions compiles with each member at the hint quotient Source
reads it at**: the reader reads it at the member's projection record
(`TraceFold.block_compiled`). -/
theorem blocksHinted : BlocksHinted := by
  intro _ _ _ _ _ _ _ P scheduled idx _ _ hgr two _ order
  exact TraceFold.block_compiled P scheduled idx hgr two order

/-- **The certified compiler is correct** (`CompileCorrect`), with no premises:
`compileCorrect_of` at the closure's record layout and the definitions' hints. -/
theorem compileCorrect : CompileCorrect.{w} :=
  compileCorrect_of layoutsHold singletonsHinted blocksHinted

end Ix.Cert.ReaderStreamsTrace

/--
info: 'Ix.Cert.ReaderStreamsTrace.layoutsHold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.ReaderStreamsTrace.layoutsHold

/--
info: 'Ix.Cert.ReaderStreamsTrace.singletonsHinted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.ReaderStreamsTrace.singletonsHinted

/--
info: 'Ix.Cert.ReaderStreamsTrace.blocksHinted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.ReaderStreamsTrace.blocksHinted

/--
info: 'Ix.Cert.ReaderStreamsTrace.compileCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.ReaderStreamsTrace.compileCorrect
