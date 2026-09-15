import Compilatrix.UniqueReuse.AllocatingNative
import Compilatrix.UniqueReuse.AllocatingObjectSim
import Compilatrix.UniqueReuse.AllocatingObjectSpace
import Compilatrix.UniqueReuse.AllocatingSourceSim
import Compilatrix.UniqueReuse.Heap
import Compilatrix.UniqueReuse.LowerSim
import Compilatrix.UniqueReuse.NativeSim
import Compilatrix.UniqueReuse.PipelineSim
import Compilatrix.UniqueReuse.Reclamation
import Compilatrix.UniqueReuse.RuntimeNative
import Compilatrix.UniqueReuse.RuntimeNativeSim
import Compilatrix.UniqueReuse.RuntimeObjectSim
import Compilatrix.UniqueReuse.RuntimeObjectSpace
import Compilatrix.UniqueReuse.RuntimeSourceSim
import Compilatrix.UniqueReuse.RuntimeTarget
import Compilatrix.UniqueReuse.SourceSim
import Compilatrix.UniqueReuse.TargetHeap
import Compilatrix.UniqueReuse.TargetLoop
import Compilatrix.UniqueReuse.TargetMain
import Compilatrix.UniqueReuse.TargetResources
import Compilatrix.UniqueReuse.TargetSim

/-! Required axiom fences for UniqueReuse; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.UniqueReuse.CheckedSource.sourceValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.CheckedSource.sourceValue

/-- info: 'Compilatrix.UniqueReuse.ListAt.hasWorld' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.ListAt.hasWorld

/-- info: 'Compilatrix.UniqueReuse.ListAt.graph' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.ListAt.graph

/-- info: 'Compilatrix.UniqueReuse.consumingLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.consumingLoop

/-- info: 'Compilatrix.UniqueReuse.mainExists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.mainExists

/-- info: 'Compilatrix.UniqueReuse.consumingMainResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.consumingMainResult

/-- info: 'Compilatrix.UniqueReuse.release1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.release1

/-- info: 'Compilatrix.UniqueReuse.release2_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.release2_complete

/-- info: 'Compilatrix.UniqueReuse.Target.reserveReuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.reserveReuse

/-- info: 'Compilatrix.UniqueReuse.Target.reuseAt_peak' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.reuseAt_peak

/-- info: 'Compilatrix.UniqueReuse.Target.loopSteps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.loopSteps

/-- info: 'Compilatrix.UniqueReuse.Target.mainSteps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.mainSteps

/-- info: 'Compilatrix.UniqueReuse.Target.mainRuns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.mainRuns

/-- info: 'Compilatrix.UniqueReuse.Target.MainResult.reclaims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.MainResult.reclaims

/-- info: 'Compilatrix.UniqueReuse.Target.prefixResources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.prefixResources

/-- info: 'Compilatrix.UniqueReuse.Target.costLaws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.costLaws

/-- info: 'Compilatrix.IxIR2.UniqueLower.Translation.forwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.UniqueLower.Translation.forwardSimulation

/-- info: 'Compilatrix.UniqueReuse.ownedSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.ownedSemantics

/-- info: 'Compilatrix.UniqueReuse.backendSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.backendSemantics

/-- info: 'Compilatrix.UniqueReuse.Compilation.sourceRefinesWithCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Compilation.sourceRefinesWithCostLaws

/-- info: 'Compilatrix.UniqueReuse.Native.Output.executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Native.Output.executes

/-- info: 'Compilatrix.UniqueReuse.Native.Output.costsAgree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Native.Output.costsAgree

/-- info: 'Compilatrix.UniqueReuse.Native.Output.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Native.Output.sourceRefines

/-- info: 'Compilatrix.UniqueReuse.Native.SourceNativeResult.witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Native.SourceNativeResult.witness

/-- info: 'Compilatrix.UniqueReuse.Native.Execution.mainSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Native.Execution.mainSafe

/-- info: 'Compilatrix.UniqueReuse.Native.Execution.releaseSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Native.Execution.releaseSafe

/-- info: 'Compilatrix.UniqueReuse.Runtime.Compilation.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Compilation.sourceRefines

/-- info: 'Compilatrix.UniqueReuse.Runtime.Compilation.targetRuns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Compilation.targetRuns

/-- info: 'Compilatrix.UniqueReuse.Runtime.Target.makeInput_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Target.makeInput_valid

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.ArgumentRel.graph' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.ArgumentRel.graph

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.Output.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.Output.sourceRefines

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.costsAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.costsAgree

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.ofNats_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.ofNats_exact

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.Output.emit_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.Output.emit_spec

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.role_callFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.role_callFree

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.Object.provenance_parsed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.Object.provenance_parsed

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.Output.sourceRefinesObjects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.Output.sourceRefinesObjects

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.Output.sourceRefinesObjects_of_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.Output.sourceRefinesObjects_of_bytes

/-- info: 'Compilatrix.UniqueReuse.Runtime.AllocatingNative.Output.emit_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.AllocatingNative.Output.emit_spec

/-- info: 'Compilatrix.UniqueReuse.Runtime.AllocatingNative.byte_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.AllocatingNative.byte_execution

/-- info: 'Compilatrix.UniqueReuse.Runtime.AllocatingNative.ByteExecution.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.AllocatingNative.ByteExecution.frame

/-- info: 'Compilatrix.UniqueReuse.Runtime.AllocatingNative.Object.capacityRejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.AllocatingNative.Object.capacityRejects

/-- info: 'Compilatrix.UniqueReuse.Runtime.AllocatingNative.Output.sourceRefinesObjects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.AllocatingNative.Output.sourceRefinesObjects
