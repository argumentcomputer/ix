import Compilatrix.X86.ObjectRun
import Compilatrix.X86.ObjectRunSafe
import Compilatrix.Backend.Proof.Xl

/-! Required axiom fences for the backend composition (M2.6b item 5): the
object's clocked execution (`ObjectEval.exec`, `exec_mono`), the bridge
from checked typed runs to it (`exec_exit`, `exec_running`,
`sim_of_ends`), and the composed backend (`Backend.xl_sim` and the
allocation and driver decompositions). Generated from the modules' public
theorems; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.X86.ObjectEval.runTo_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.runTo_stop

/-- info: 'Compilatrix.X86.ObjectEval.runTo_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.runTo_add

/-- info: 'Compilatrix.X86.ObjectEval.finish_timeout' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.finish_timeout

/-- info: 'Compilatrix.X86.ObjectEval.exec_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.exec_mono

/-- info: 'Compilatrix.X86.ObjectEval.step_inText' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.step_inText

/-- info: 'Compilatrix.X86.ObjectEval.runTo_of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.runTo_of_run

/-- info: 'Compilatrix.X86.ObjectEval.safeSteps_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.safeSteps_bytes

/-- info: 'Compilatrix.X86.ObjectEval.exec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.exec_eq

/-- info: 'Compilatrix.X86.ObjectEval.exec_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.exec_exit

/-- info: 'Compilatrix.X86.ObjectEval.exec_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.exec_running

/-- info: 'Compilatrix.X86.ObjectEval.statusResult_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.statusResult_zero

/-- info: 'Compilatrix.X86.ObjectEval.statusResult_code' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.statusResult_code

/-- info: 'Compilatrix.X86.ObjectEval.statusResult_four' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.statusResult_four

/-- info: 'Compilatrix.X86.ObjectEval.statusResult_two' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.statusResult_two

/-- info: 'Compilatrix.X86.ObjectEval.sim_of_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.sim_of_ends

/-- info: 'Compilatrix.Backend.alloc_validated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Backend.alloc_validated

/-- info: 'Compilatrix.Backend.compileWith_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Backend.compileWith_parts

/-- info: 'Compilatrix.Backend.compile_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Backend.compile_parts

/-- info: 'Compilatrix.Backend.xl_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Backend.xl_sim

/-- info: 'Compilatrix.Backend.xl_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Backend.xl_refines

/-- info: 'Compilatrix.Backend.xl_tsim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Backend.xl_tsim
