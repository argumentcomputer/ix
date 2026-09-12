import Benchmark.ScalingVerify

/-! Fixed-input comparison of baseline and shared native emission. The timer
covers one invocation of each named stage; execution, mutation checks, JSON,
and file writes occur outside those intervals. Neither selector limits nor
fixture provenance depend on the chosen emitter. -/
namespace Benchmark.NativeSharing
open Lean System Compilatrix Compilatrix.X86 Compilatrix.Tools.Check

private def timed (measurements : IO.Ref (Array Json)) (label stage : String)
    (operation : Unit → Except String α) : IO α := do
  let start ← IO.monoNanosNow
  let result := operation ()
  let value ← checked result
  let stop ← IO.monoNanosNow
  measurements.modify (·.push (Json.mkObj [("case", toJson label), ("stage", toJson stage), ("ns", toJson (stop - start))]))
  return value

private def targets : Terminator → Array BlockId
  | .jump entry | .tailCall entry => #[entry]
  | .branch _ _ zero successor => #[zero, successor]
  | .ret => #[]

private def joinedBlocks (program : X86.Program) : Nat := Id.run do
  let mut incoming := Array.replicate program.blocks.size (0 : Nat)
  for block in program.blocks do
    for entry in targets block.terminator do
      incoming := incoming.modify entry.toNat (· + 1)
  return (incoming.filter (· > 1)).size

private def mutations {schemas program root baseline}
    (selected : PhysicalHeap.Selected schemas program root) (candidate : HeapTarget.Candidate)
    (_output : HeapTarget.Output selected baseline) : IO Nat := do
  let mut count := 0
  for index in [:candidate.blocks.size] do
    let block := candidate.blocks[index]!
    let altered := { block with instructions := block.instructions.push (.mov .w64 .rax (.imm 0)) }
    let control := { block with terminator := if block.terminator == .ret then .jump index.toUInt32 else .ret }
    for changed in [altered, control] do
      match HeapTarget.checkCandidate selected baseline { candidate with blocks := candidate.blocks.set! index changed } with
      | .ok _ => throw (IO.userError "shared certificate accepted a changed instruction/control block")
      | .error _ => count := count + 1
  match HeapTarget.checkCandidate selected baseline { candidate with plans := #[] } with
  | .ok _ => throw (IO.userError "shared certificate accepted missing function coverage")
  | .error _ => return count + 1

private def observe {schemas program root}
    (selected : PhysicalHeap.Selected schemas program root) (native : HeapTarget.Output selected true)
    (object : ByteArray) (count : Nat) : IO (Array Json) := do
  let text ← present (ELFRead.text? object) "join ELF has no text"
  let entry ← present (ELF.entry? object "compilatrix_scaling") "join ELF has no entry"
  let inputs := #[0, 1, count - 1, count, count + 1, UInt64.size - 1]
  inputs.mapM fun argument => do
    let physical ← checked ((IxIR2.Eval.runFunction (IxIR2.Eval.Context.ofProgram program schemas) .physical
      selected.entryInterface.definition #[PhysicalScalar.rval argument.toUInt64] 100000 100000
      (PhysicalHeap.initialStore true)).mapError reprStr)
    need (physical.value == .lit (.nat (argument - count)) && physical.store.live == 0 &&
      physical.store.heap.allocs == 1 && physical.store.heap.frees == 1 && physical.store.heap.rcops == 1 &&
      physical.store.heap.nodes.all Option.isNone) "join physical result/reclamation disagrees"
    let initial := Scaling.core (selected.entry + 1) argument
    let typed := X86.runFrom Runtime.rejecting native.target 100000 initial
    need (typed.status == .halted (argument - count).toUInt64 && typed.core.readReg .rdx == 0 &&
      typed.core.readReg .rsp == initial.readReg .rsp && typed.core.calleeSavedMatch initial.calleeSavedSnapshot)
      "join typed execution disagrees"
    let mut state : ByteEval.State := ⟨initial, 0x400000 + entry.toUInt64, {}⟩
    let mut steps := 0
    for _ in [:100000] do
      if state.rip == 0x12345678 then break
      state ← checked ((ByteEval.step text 0x400000 state).mapError reprStr)
      steps := steps + 1
    let parsed ← checked ((ObjectEval.run object "compilatrix_scaling" 0x400000 steps initial).mapError reprStr)
    need (state.rip == 0x12345678 && parsed.rip == state.rip &&
      state.core.readReg .rax == (argument - count).toUInt64 && parsed.core.readReg .rax == state.core.readReg .rax &&
      state.core.readReg .rdx == 0 && parsed.core.readReg .rdx == 0 &&
      state.core.readReg .rsp == initial.readReg .rsp + 8 && parsed.core.calleeSavedMatch initial.calleeSavedSnapshot)
      "join complete ELF execution disagrees"
    for index in [:272] do
      let address := (0x10000 : Word) + (8 * index).toUInt64
      need (parsed.core.memory.read64 address == typed.core.memory.read64 address &&
        state.core.memory.read64 address == typed.core.memory.read64 address) "join arena words disagree"
      if index ≥ 10 then
        need (parsed.core.memory.read64 address == initial.memory.read64 address) "join touched unused arena words"
    for field in [0, 2, 3, 4, 5, 6, 7, 8, 9] do
      need (parsed.core.memory.read64 (0x10000 + (8 * field).toUInt64) ==
        (if [2, 3, 5].contains field then 1 else 0)) "join exact counters disagree"
    for address in [(0xffff : Word), 0xfff8, initial.readReg .rsp + 8, initial.readReg .rsp + 16] do
      need (parsed.core.memory.bytes address == initial.memory.bytes address) "join changed an outside canary"
    return Json.mkObj [("argument", toJson argument), ("value", toJson (argument - count)), ("byte_steps", toJson steps)]

private def row (directory : FilePath) (measurements : IO.Ref (Array Json))
    (count : Nat) (emission : HeapTarget.Emission) : IO Json := do
  let mode := if emission == .shared then "shared" else "tree"
  let label := s!"joins-{count}-{mode}"
  let artifact := Scaling.joinArtifact count
  let wire ← timed measurements label "snapshot-encode-check" fun _ => artifact.encodeChecked {}
  let loaded ← timed measurements label "snapshot-decode-check" fun _ =>
    IxIR2.Wire.Artifact.ingest {} IxIR2.Validate.defaultLimits wire.bytes artifact.address
  need (loaded.artifact == artifact) "join snapshot replay changed"
  let exported ← timed measurements label "native-export" fun _ => PhysicalScalar.resolveExport loaded.artifact.program
  let selected ← timed measurements label "native-select" fun _ =>
    PhysicalHeap.select loaded.artifact.context.schemas loaded.artifact.program exported.address
  let candidate ← timed measurements label "native-emit" fun _ => HeapTarget.emitCandidate selected true emission
  let native ← timed measurements label "native-certificate-check" fun _ => HeapTarget.checkCandidate selected true candidate
  let stream ← timed measurements label "x86-encode-check" fun _ => (Stream.encode native.target).mapError reprStr
  let input : ELF.Input := {
    encoded := stream.output, entryBlock := native.target.program.entry
    exportName := "compilatrix_scaling", provenance := .ixir2 artifact.address }
  let object ← timed measurements label "elf-write-check" fun _ => (ELF.writeChecked input).mapError reprStr
  let changed ← if emission == .shared then do
      need (decide native.target.program.blocks.toList.Nodup) "shared emission contains identical blocks"
      need (joinedBlocks native.target.program ≥ count) "shared joins disappeared"
      let replay ← checked (PhysicalHeap.compileSnapshotExport loaded.artifact loaded.checked "compilatrix_scaling")
      need (replay.compiled.object.bytes == object.bytes) "default object API differs from shared emission"
      mutations selected candidate native
    else pure 0
  let observations ← observe selected native object.bytes count
  let record := Json.mkObj [
    ("case", toJson label), ("joins", toJson count), ("mode", toJson mode), ("emission", toJson emission.policy),
    ("origin", toJson "checked-ixir2"), ("snapshot_root", toJson artifact.address), ("snapshot_bytes", toJson wire.bytes.size),
    ("entry", toJson exported.address), ("entry_offset", toJson (ELF.entry? object.bytes "compilatrix_scaling")),
    ("input_blocks", toJson exported.target.blocks.size), ("control_bound", toJson selected.entryInterface.controls),
    ("allocation_bound", toJson selected.entryInterface.allocations), ("function_count", toJson selected.entries.size),
    ("x86_blocks", toJson native.target.program.blocks.size),
    ("x86_instructions", toJson (native.target.program.blocks.foldl (fun n block => n + block.instructions.size) 0)),
    ("joined_blocks", toJson (joinedBlocks native.target.program)),
    ("text_bytes", toJson stream.output.text.size), ("text_root", toJson (Ixon.Address.blake3 stream.output.text)),
    ("elf_bytes", toJson object.bytes.size), ("elf_root", toJson (Ixon.Address.blake3 object.bytes)),
    ("mutation_rejections", toJson changed), ("observations", toJson observations)]
  IO.FS.writeBinFile (directory / s!"{label}.ixir2") wire.bytes
  IO.FS.writeBinFile (directory / s!"{label}.o") object.bytes
  Scaling.writeJson (directory / s!"{label}.json") record
  IO.println s!"{label}: {native.target.program.blocks.size} blocks, {object.bytes.size} ELF bytes"
  return record

def produce (directory : FilePath) (profile : String) : IO Unit := do
  need (profile == "smoke" || profile == "reference") "unknown native sharing profile"
  Scaling.fresh directory
  let measurements ← IO.mkRef #[]
  let mut rows := #[]
  let sizes := if profile == "smoke" then #[2, 4, 8] else #[2, 3, 4, 5, 6, 7, 8]
  for count in sizes do
    let baseline ← row directory measurements count .tree
    let shared ← row directory measurements count .shared
    for key in ["snapshot_root", "snapshot_bytes", "input_blocks", "control_bound", "allocation_bound", "observations"] do
      need ((← field baseline key) == (← field shared key)) s!"join baseline/shared {key} changed"
    need ((← nat (← field shared "x86_blocks")) < (← nat (← field baseline "x86_blocks"))) "join sharing did not reduce blocks"
    rows := rows ++ #[baseline, shared]
  -- The historical reference stopped baseline ELF emission at eight joins.
  -- Nine joins adds a shared-only endpoint without inventing baseline data.
  rows := rows.push (← row directory measurements 9 .shared)
  let rejected := Scaling.joinArtifact 10
  let _ ← checked (rejected.check IxIR2.Validate.defaultLimits)
  let rejection ← match PhysicalHeap.select rejected.context.schemas rejected.program Scaling.joinRoot with
    | .error reason => pure reason
    | .ok _ => throw (IO.userError "fixed ten-join selection limit changed")
  Scaling.writeJson (directory / "report.json") (Json.mkObj [
    ("format", toJson "compilatrix/native-sharing/1"), ("profile", toJson profile),
    ("selection_limits", Json.mkObj [("depth", toJson PhysicalHeap.maxDepth), ("work", toJson PhysicalHeap.maxWork),
      ("functions", toJson PhysicalHeap.maxFunctions), ("allocations", toJson PhysicalHeap.maxAllocations),
      ("values", toJson PhysicalHeap.maxValues), ("credits", toJson PhysicalHeap.maxCredits), ("copies", toJson PhysicalHeap.maxEdge)]),
    ("rejected_joins", toJson (10 : Nat)), ("rejection", toJson rejection), ("cases", toJson rows)])
  Scaling.writeJson (directory / "measurements.json") (Json.mkObj [
    ("format", toJson "compilatrix/native-sharing-measurements/1"),
    ("clock", toJson "IO.monoNanosNow; one invocation per stage, fixed tree/shared order"),
    ("excluded", toJson "fixture construction, default-API replay, semantic execution, mutations, JSON, hashing reported artifacts, file writes"),
    ("stages", toJson (← measurements.get))])
  IO.println s!"native sharing ok: {rows.size} objects, fixed ten-join rejection"

end Benchmark.NativeSharing
