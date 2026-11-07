import IxCC.X86.ObjectRun
import IxCC.X86.ObjectRunSafe
import IxCC.Backend.Proof.Xl
import IxCC.Backend.Proof.Emit
import IxCC.Backend.Proof.Object

/-! Required axiom fences for the backend composition (M2.6b item 5): the
object's clocked execution (`ObjectEval.exec`, `exec_mono`), the bridge
from checked typed runs to it (`exec_exit`, `exec_running`,
`sim_of_ends`), and the composed backend (`Backend.xl_sim` and the
allocation and driver decompositions). Generated from the modules' public
theorems; expected messages are preserved verbatim. -/

/-- info: 'IxCC.X86.ObjectEval.runTo_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.runTo_stop

/-- info: 'IxCC.X86.ObjectEval.runTo_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.runTo_add

/-- info: 'IxCC.X86.ObjectEval.finish_timeout' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.finish_timeout

/-- info: 'IxCC.X86.ObjectEval.exec_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.exec_mono

/-- info: 'IxCC.X86.ObjectEval.step_inText' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.step_inText

/-- info: 'IxCC.X86.ObjectEval.runTo_of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.runTo_of_run

/-- info: 'IxCC.X86.ObjectEval.safeSteps_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.safeSteps_bytes

/-- info: 'IxCC.X86.ObjectEval.exec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.exec_eq

/-- info: 'IxCC.X86.ObjectEval.exec_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.exec_exit

/-- info: 'IxCC.X86.ObjectEval.exec_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.exec_running

/-- info: 'IxCC.X86.ObjectEval.statusResult_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.statusResult_zero

/-- info: 'IxCC.X86.ObjectEval.statusResult_code' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.statusResult_code

/-- info: 'IxCC.X86.ObjectEval.statusResult_four' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.statusResult_four

/-- info: 'IxCC.X86.ObjectEval.statusResult_two' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.statusResult_two

/-- info: 'IxCC.X86.ObjectEval.sim_of_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.sim_of_ends

/-- info: 'IxCC.X86.ObjectEval.sim_of_ends_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.sim_of_ends_succ

/-- info: 'IxCC.Backend.alloc_validated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.alloc_validated

/-- info: 'IxCC.Backend.compileWith_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.compileWith_parts

/-- info: 'IxCC.Backend.compile_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.compile_parts

/-- info: 'IxCC.Backend.xl_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.xl_sim

/-- info: 'IxCC.Backend.xl_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.xl_refines

/-- info: 'IxCC.Backend.xl_tsim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.xl_tsim

/-- info: 'IxCC.Backend.emit_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.emit_parts

/-- info: 'IxCC.Backend.object_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.object_sim

/-- info: 'IxCC.Backend.compile_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.compile_sim

/-- info: 'IxCC.Backend.object_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.object_refines

/-- info: 'IxCC.Backend.object_tsim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.object_tsim
