import Ix.Compiler.UniqueReuse.RuntimeNativeSim
import Ix.Compiler.X86.ObjectExecution
import Ix.Compiler.X86.StreamPermissions

/-! The runtime-input source theorem reaches actual emitted ELF text.
Every admitted Word list uses the same compiled object pair. -/

namespace Ix.Compiler.UniqueReuse.Runtime.Native

open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.X86
open Ix.Compiler.X86.UniqueABI
open Ix.Compiler.X86.UniqueExecution
open Ix.Compiler.X86.UniqueTarget (releaseCost)

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

variable {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
  {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}
  {foldCounters : Bool}

theorem Output.emit_spec {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (role : Role) {object : Object} (emitted : output.emit role = .ok object) :
    object.role = role ∧ object.provenance = .ixir1Policy output.graph loweringVersion (role.policyVersion output.foldCounters) ∧
      object.policyBytes = output.policyBytes role ∧ object.policyIdentity = output.identity role ∧
      object.foldCounters = output.foldCounters := by
  unfold Output.emit at emitted
  cases stream : Stream.encode (role.checked output.foldCounters) with
  | error error => simp [stream, Except.mapError] at emitted
  | ok streamValue =>
      simp only [stream, Except.mapError, bind, Except.bind] at emitted
      cases written : ELF.writeChecked {
          encoded := streamValue.output, entryBlock := (role.checked output.foldCounters).program.entry, exportName := role.symbol
          provenance := .ixir1Policy output.graph loweringVersion (role.policyVersion output.foldCounters) } with
      | error error => simp [written] at emitted
      | ok objectValue =>
          simp only [written, pure, Except.pure] at emitted
          cases Except.ok.inj emitted
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem role_callFree (role : Role) (foldCounters : Bool := false) : Stream.CallFree (role.checked foldCounters).program := by
  apply Stream.callFree_sound
  cases role <;> cases foldCounters <;> decide +kernel

theorem Object.run_from_typed (object : Object) (runtime : X86.Runtime) (base : Word)
    (fuel : Nat) (core : Core) (flags : ByteEval.Flags) {after : Machine} {result returnAddress : Word}
    (execution : X86.runFrom runtime (object.role.checked object.foldCounters) fuel core = after) (halted : after.status = .halted result)
    (slot : after.core.memory.read64? (after.core.readReg .rsp) = .ok returnAddress) :
    ∃ count finalState, 0 < count ∧ count ≤ 3 * fuel ∧
      ObjectEval.run object.bytes object.role.symbol base count core flags = .ok finalState ∧
      Stream.Returned after.core returnAddress finalState :=
  ObjectEval.run_from_typed object.streamValid object.objectValid rfl (role_callFree object.role object.foldCounters)
    runtime base fuel core flags execution halted slot

theorem Object.provenance_parsed (object : Object) :
    (ELFRead.parse object.bytes).map ELFRead.View.provenance = some (ELF.expectedProvenance object.provenance) := by
  obtain ⟨view, parsed, fields⟩ := object.objectValid
  simp [parsed, fields.provenance]

structure CallerSlot (layout : Layout) (stack : Word) (memory : Memory) (returnAddress : Word) : Prop where
  outside : ∀ offset < 8, layout.allowed (stack + UInt64.ofNat offset) = false
  read : memory.read64? stack = .ok returnAddress

theorem caller_read_preserved {layout : Layout} {outside before after : Memory} {beforeWords afterWords : Words}
    {stack returnAddress : Word} (caller : CallerSlot layout stack before returnAddress)
    (beforeView : Realizes layout outside beforeWords before) (afterView : Realizes layout outside afterWords after)
    (permissions : after.readable = before.readable) : after.read64? stack = .ok returnAddress := by
  have bytes : after.read64 stack = before.read64 stack := by
    apply Memory.readLittle_congr
    intro offset bound
    rw [afterView.frame _ (caller.outside offset bound), beforeView.frame _ (caller.outside offset bound)]
  change (if Memory.rangeAllowed after.readable stack 8 then Except.ok (after.read64 stack)
    else Except.error (⟨.read, stack, 8⟩ : MemoryFault)) = Except.ok returnAddress
  rw [permissions, bytes]
  exact caller.read

theorem return_slots {layout : Layout} {values : List Word} {before returned reclaimed : State}
    {memory outside returnedMemory reclaimedMemory : Memory} {runtime : X86.Runtime} {returnAddress : Word}
    (execution : RuntimeExecution.Execution layout values before memory outside runtime returned returnedMemory reclaimed reclaimedMemory foldCounters)
    (initial : Realizes layout outside before.words memory)
    (caller : CallerSlot layout (before.registers .rsp) memory returnAddress) :
    returnedMemory.read64? (returned.registers .rsp) = .ok returnAddress ∧
      reclaimedMemory.read64? (reclaimed.registers .rsp) = .ok returnAddress := by
  have mainPermissions := Stream.run_permissions runtime (RuntimeTarget.checked foldCounters) (role_callFree .main foldCounters)
    (RuntimeTarget.controlCost values.length foldCounters) (Machine.initial (RuntimeTarget.checked foldCounters) (before.core memory))
  have releasePermissions := Stream.run_permissions runtime RuntimeTarget.releaseChecked (role_callFree .release)
    (releaseCost values.length) (Machine.initial RuntimeTarget.releaseChecked (returned.core returnedMemory))
  change Stream.Permissions _ (runFrom runtime (RuntimeTarget.checked foldCounters) _ _).core at mainPermissions
  change Stream.Permissions _ (runFrom runtime RuntimeTarget.releaseChecked _ _).core at releasePermissions
  rw [execution.mainRun] at mainPermissions
  rw [execution.releaseRun] at releasePermissions
  have mainRead : returnedMemory.readable = memory.readable := mainPermissions.1
  have releaseRead : reclaimedMemory.readable = memory.readable := releasePermissions.1.trans mainRead
  rw [execution.returnedResult.saved .rsp rfl, execution.reclaimedResult.saved .rsp rfl]
  exact ⟨caller_read_preserved caller initial execution.returnedView mainRead,
    caller_read_preserved caller initial execution.reclaimedView releaseRead⟩

structure ByteExecution (main release : Object) (layout : Layout) (values : List Word) (before : State)
    (memory outside : Memory) (runtime : X86.Runtime) (returned : State) (returnedMemory : Memory)
    (reclaimed : State) (reclaimedMemory : Memory) (base returnAddress : Word) (flags : ByteEval.Flags)
    (mainCount releaseCount : Nat) (byteReturned byteReclaimed : ByteEval.State) : Prop where
  typed : RuntimeExecution.Execution layout values before memory outside runtime returned returnedMemory reclaimed reclaimedMemory main.foldCounters
  mainPositive : 0 < mainCount
  mainBound : mainCount ≤ 3 * RuntimeTarget.controlCost values.length main.foldCounters
  releasePositive : 0 < releaseCount
  releaseBound : releaseCount ≤ 3 * releaseCost values.length
  mainRun : ObjectEval.run main.bytes Role.main.symbol base mainCount (before.core memory) flags = .ok byteReturned
  releaseRun : ObjectEval.run release.bytes Role.release.symbol base releaseCount (returned.core returnedMemory) flags = .ok byteReclaimed
  mainReturn : Stream.Returned (returned.core returnedMemory) returnAddress byteReturned
  releaseReturn : Stream.Returned (reclaimed.core reclaimedMemory) returnAddress byteReclaimed
  graph : NativeList byteReturned.core.memory ((values.map UInt64.toNat).reverse) (byteReturned.core.readReg .rax)
    (chainNodes layout 1 values.length)
  releasedMemory : byteReclaimed.core.memory = reclaimedMemory
  releasedValue : byteReclaimed.core.readReg .rax = 0

theorem byte_execution {layout : Layout} {values : List Word} {before returned reclaimed : State}
    {memory outside returnedMemory reclaimedMemory : Memory} {runtime : X86.Runtime} {returnAddress : Word}
    (execution : RuntimeExecution.Execution layout values before memory outside runtime returned returnedMemory reclaimed reclaimedMemory foldCounters)
    (initial : Realizes layout outside before.words memory)
    (caller : CallerSlot layout (before.registers .rsp) memory returnAddress)
    (main release : Object) (mainRole : main.role = .main) (releaseRole : release.role = .release)
    (mainMode : main.foldCounters = foldCounters)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ mainCount releaseCount byteReturned byteReclaimed,
      ByteExecution main release layout values before memory outside runtime returned returnedMemory reclaimed reclaimedMemory
        base returnAddress flags mainCount releaseCount byteReturned byteReclaimed := by
  subst foldCounters
  have slots := return_slots execution initial caller
  have mainRun : runFrom runtime (main.role.checked main.foldCounters) (RuntimeTarget.controlCost values.length main.foldCounters) (before.core memory) =
      haltedLeaf (returned.core returnedMemory) 4 13 := by simpa [mainRole, Role.checked] using execution.mainRun
  have releaseRun : runFrom runtime (release.role.checked release.foldCounters) (releaseCost values.length) (returned.core returnedMemory) =
      haltedLeaf (reclaimed.core reclaimedMemory) 2 13 := by simpa [releaseRole, Role.checked] using execution.releaseRun
  obtain ⟨mainCount, byteReturned, mainPositive, mainBound, mainExecuted, mainReturned⟩ :=
    main.run_from_typed runtime base _ _ flags mainRun rfl slots.1
  obtain ⟨releaseCount, byteReclaimed, releasePositive, releaseBound, releaseExecuted, releaseReturned⟩ :=
    release.run_from_typed runtime base _ _ flags releaseRun rfl slots.2
  refine ⟨mainCount, releaseCount, byteReturned, byteReclaimed, execution, mainPositive, mainBound, releasePositive,
    releaseBound, by simpa [mainRole] using mainExecuted, by simpa [releaseRole] using releaseExecuted,
    mainReturned, releaseReturned, ?_, ?_, ?_⟩
  · rw [mainReturned.1]
    simpa [Core.setReg, Core.readReg, State.core, haltedLeaf, leaf] using execution.graph
  · rw [releaseReturned.1]
    rfl
  · rw [releaseReturned.1]
    simpa [Core.setReg, Core.readReg, State.core, haltedLeaf, leaf] using execution.reclaimedResult.result

structure ObjectResult {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (sourceResult : Ixon.Eval.Value) (values : List Word)
    (layout : Layout) (before : State) (outside memory : Memory) (runtime : X86.Runtime)
    (main release : Object) (base returnAddress : Word) (flags : ByteEval.Flags) : Prop where
  source : Result output sourceResult values layout before outside memory runtime
  mainProvenance : (ELFRead.parse main.bytes).map ELFRead.View.provenance =
    some (ELF.expectedProvenance (.ixir1Policy output.graph loweringVersion (Role.main.policyVersion output.foldCounters)))
  releaseProvenance : (ELFRead.parse release.bytes).map ELFRead.View.provenance =
    some (ELF.expectedProvenance (.ixir1Policy output.graph loweringVersion (Role.release.policyVersion output.foldCounters)))
  native : ∃ returned returnedMemory reclaimed reclaimedMemory mainCount releaseCount byteReturned byteReclaimed,
    ByteExecution main release layout values before memory outside runtime returned returnedMemory reclaimed reclaimedMemory
      base returnAddress flags mainCount releaseCount byteReturned byteReclaimed

/-- The actual compiler's emitted object pair executes on every admitted
runtime argument and preserves the source result, native graph and complete
reclamation observations. Emission success carries the concrete certificates. -/
theorem Output.sourceRefinesObjects {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) {functionFuel applyFuel : Nat} {function argument sourceResult : Ixon.Eval.Value}
    {values : List Word} {layout : Layout} {state : State} {outside memory : Memory}
    (relation : ArgumentRel compilation argument values layout state outside memory)
    (oracles : @Sim.OracleRel compilation.erased.memberScope (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.erased.erasure.result.raw })
    (contextWF : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (evaluated : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) functionFuel entry.frame [] entry.source = .ok function)
    (applied : Ixon.Eval.apply (Pipeline.validatedEvalCtx constants config) applyFuel function argument = .ok sourceResult)
    (runtime : X86.Runtime) (main release : Object)
    (mainEmitted : output.emit .main = .ok main) (releaseEmitted : output.emit .release = .ok release)
    (base returnAddress : Word) (flags : ByteEval.Flags)
    (caller : CallerSlot layout (state.registers .rsp) memory returnAddress) :
    ObjectResult output sourceResult values layout state outside memory runtime main release base returnAddress flags := by
  have source := output.sourceRefines relation oracles contextWF evaluated applied runtime
  have mainSpec := output.emit_spec .main mainEmitted
  have releaseSpec := output.emit_spec .release releaseEmitted
  refine ⟨source, ?_, ?_, ?_⟩
  · simpa [mainSpec.2.1] using main.provenance_parsed
  · simpa [releaseSpec.2.1] using release.provenance_parsed
  · obtain ⟨returned, returnedMemory, reclaimed, reclaimedMemory, execution⟩ := source.native
    obtain ⟨mainCount, releaseCount, byteReturned, byteReclaimed, bytes⟩ :=
      byte_execution execution relation.represented caller main release mainSpec.1 releaseSpec.1 mainSpec.2.2.2.2 base flags
    exact ⟨returned, returnedMemory, reclaimed, reclaimedMemory, mainCount, releaseCount, byteReturned, byteReclaimed, bytes⟩

end Ix.Compiler.UniqueReuse.Runtime.Native
