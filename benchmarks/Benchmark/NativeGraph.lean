import Benchmark.NativeSharing
import Compilatrix.X86.HeapGraphTests

namespace Benchmark.NativeGraph
open Lean System Compilatrix Compilatrix.X86 Compilatrix.Tools.Check

private def graphDescription (selection : PhysicalHeap.Graph.Selected schemas program root) : Json :=
  Json.mkObj [("format", toJson "compilatrix/selected-graph-inspection/1"),
    ("functions", toJson (selection.graphs.map fun row => Json.mkObj [
      ("index", toJson row.row.index), ("entry", toJson row.graph.entry),
      ("nodes", toJson (row.graph.body.cells.map fun cell => Json.mkObj [
        ("point", toJson (reprStr cell.node.point)), ("shape", toJson (reprStr cell.node.shape)),
        ("result", toJson (reprStr cell.summary.result)), ("allocations", toJson cell.summary.allocations),
        ("controls", toJson cell.summary.controls), ("depth", toJson cell.summary.depth)]))]))]

private def graphCertificate (candidate : HeapGraph.Candidate) : Json :=
  Json.mkObj [("format", toJson "compilatrix/native-graph-plan-inspection/1"),
    ("entry", toJson (reprStr candidate.entry)),
    ("functions", toJson (candidate.functions.map fun row => Json.mkObj [
      ("entry", toJson row.entry.toNat), ("exit", toJson row.exit.toNat),
      ("nodes", toJson (row.nodes.map fun node => Json.mkObj [
        ("entry", toJson node.entry.toNat), ("zero_edge", toJson node.zeroEdge.toNat), ("succ_edge", toJson node.succEdge.toNat)]))]))]

private structure Representation where
  selectedNodes : Nat
  selectedEdges : Nat
  depth : Nat
  nativeRows : Nat
  sourceMutations : Nat
  nativeMutations : Nat
  selection : Json
  certificate : Json

private def row (directory : FilePath) (measurements : IO.Ref (Array Json)) (count : Nat)
    (graphMode : Bool) : IO Json := do
  let mode := if graphMode then "graph" else "shared"
  let label := s!"joins-{count}-{mode}"
  let artifact := Scaling.joinArtifact count
  let wire ← NativeSharing.timed measurements label "snapshot-encode-check" fun _ => artifact.encodeChecked {}
  let loaded ← NativeSharing.timed measurements label "snapshot-decode-check" fun _ =>
    IxIR2.Wire.Artifact.ingest {} IxIR2.Validate.defaultLimits wire.bytes artifact.address
  need (loaded.artifact == artifact) "graph join snapshot replay changed"
  let exported ← NativeSharing.timed measurements label "native-export" fun _ => PhysicalScalar.resolveExport loaded.artifact.program
  let result : ((selected : PhysicalHeap.Selected loaded.artifact.context.schemas loaded.artifact.program exported.address) ×
      HeapTarget.Output selected true) × (Unit → IO Representation) ← if graphMode then do
      let selection ← NativeSharing.timed measurements label "native-select" fun _ =>
        PhysicalHeap.Graph.select loaded.artifact.context.schemas loaded.artifact.program exported.address
      let candidate ← NativeSharing.timed measurements label "native-emit" fun _ => HeapGraph.emitCandidate selection true
      let native ← NativeSharing.timed measurements label "native-certificate-check" fun _ => HeapGraph.checkCandidate selection true candidate
      pure (⟨selection.selected, native⟩, fun _ => do
        let (sourceMutations, nativeMutations) ← HeapGraphTests.mutations selection candidate true
        let cells := selection.graphs.flatMap (·.graph.body.cells)
        return {
          selectedNodes := cells.size, selectedEdges := cells.foldl (fun total cell => total + cell.node.shape.children.length) 0
          depth := cells.foldl (fun depth cell => max depth cell.summary.depth) 0
          nativeRows := candidate.functions.foldl (fun total row => total + row.nodes.size) 0
          sourceMutations, nativeMutations, selection := graphDescription selection, certificate := graphCertificate candidate })
    else do
      let selected ← NativeSharing.timed measurements label "native-select" fun _ =>
        PhysicalHeap.select loaded.artifact.context.schemas loaded.artifact.program exported.address
      let candidate ← NativeSharing.timed measurements label "native-emit" fun _ => HeapTarget.emitCandidate selected true .shared
      let native ← NativeSharing.timed measurements label "native-certificate-check" fun _ => HeapTarget.checkCandidate selected true candidate
      pure (⟨selected, native⟩, fun _ => do
        let changed ← NativeSharing.mutations selected candidate native
        let nodes := selected.rows.foldl (fun total row => total + row.source.tree.nodes) 0
        return {
          selectedNodes := nodes, selectedEdges := nodes - selected.rows.size, depth := selected.entryInterface.controls
          nativeRows := nodes, sourceMutations := 0, nativeMutations := changed
          selection := Json.mkObj [("format", toJson "compilatrix/selected-tree-inspection/1"),
            ("functions", toJson (selected.rows.map (fun row => reprStr row.source.tree)))]
          certificate := Json.mkObj [("format", toJson "compilatrix/native-tree-plan-inspection/1"),
            ("entry", toJson (reprStr candidate.entry)), ("functions", toJson (candidate.plans.map reprStr))] })
  let selected := result.1.1
  let native := result.1.2
  let stream ← NativeSharing.timed measurements label "x86-encode-check" fun _ => (Stream.encode native.target).mapError reprStr
  let input : ELF.Input := {
    encoded := stream.output, entryBlock := native.target.program.entry
    exportName := "compilatrix_scaling", provenance := .ixir2 artifact.address }
  let object ← NativeSharing.timed measurements label "elf-write-check" fun _ => (ELF.writeChecked input).mapError reprStr
  let representation ← result.2 ()
  let replay ← checked (if graphMode then
      PhysicalHeap.compileSnapshotExport loaded.artifact loaded.checked "compilatrix_scaling"
    else PhysicalHeap.compileSnapshotExport loaded.artifact loaded.checked "compilatrix_scaling" (emission := .shared))
  need (replay.compiled.object.bytes == object.bytes) "graph object API replay changed bytes"
  need (decide native.target.program.blocks.toList.Nodup) "graph/shared emission contains identical native blocks"
  need (NativeSharing.joinedBlocks native.target.program ≥ count) "graph native joins disappeared"
  let observations ← NativeSharing.observe selected native object.bytes count
  let selectionText := representation.selection.compress ++ "\n"
  let certificateText := representation.certificate.compress ++ "\n"
  let record := Json.mkObj [
    ("case", toJson label), ("joins", toJson count), ("mode", toJson mode),
    ("emission", toJson (if graphMode then HeapTarget.Emission.graph.policy else HeapTarget.Emission.shared.policy)),
    ("origin", toJson "checked-ixir2"), ("snapshot_root", toJson artifact.address), ("snapshot_bytes", toJson wire.bytes.size),
    ("entry", toJson exported.address), ("entry_offset", toJson (ELF.entry? object.bytes "compilatrix_scaling")),
    ("input_blocks", toJson exported.target.blocks.size), ("control_bound", toJson selected.entryInterface.controls),
    ("allocation_bound", toJson selected.entryInterface.allocations), ("function_count", toJson selected.entries.size),
    ("selected_nodes", toJson representation.selectedNodes), ("selected_edges", toJson representation.selectedEdges),
    ("selected_depth", toJson representation.depth), ("native_certificate_rows", toJson representation.nativeRows),
    ("selection_inspection_bytes", toJson selectionText.toUTF8.size), ("native_certificate_inspection_bytes", toJson certificateText.toUTF8.size),
    ("selection_inspection_root", toJson (Ixon.Address.blake3 selectionText.toUTF8)),
    ("native_certificate_inspection_root", toJson (Ixon.Address.blake3 certificateText.toUTF8)),
    ("x86_blocks", toJson native.target.program.blocks.size),
    ("x86_instructions", toJson (native.target.program.blocks.foldl (fun total block => total + block.instructions.size) 0)),
    ("joined_blocks", toJson (NativeSharing.joinedBlocks native.target.program)),
    ("text_bytes", toJson stream.output.text.size), ("text_root", toJson (Ixon.Address.blake3 stream.output.text)),
    ("elf_bytes", toJson object.bytes.size), ("elf_root", toJson (Ixon.Address.blake3 object.bytes)),
    ("source_mutation_rejections", toJson representation.sourceMutations),
    ("mutation_rejections", toJson representation.nativeMutations), ("observations", toJson observations)]
  IO.FS.writeBinFile (directory / s!"{label}.ixir2") wire.bytes
  IO.FS.writeBinFile (directory / s!"{label}.o") object.bytes
  IO.FS.writeFile (directory / s!"{label}.selection.json") selectionText
  IO.FS.writeFile (directory / s!"{label}.plan.json") certificateText
  Scaling.writeJson (directory / s!"{label}.json") record
  IO.println s!"{label}: {representation.selectedNodes} selected nodes, {native.target.program.blocks.size} blocks"
  return record

private def rejection (name : String) (value : Except String α) : IO String :=
  match value with
  | .ok _ => throw (IO.userError s!"graph unexpectedly accepted {name}")
  | .error error => pure error

private def budgetTests : IO Json := do
  let artifact := Scaling.joinArtifact 42
  let limits : PhysicalHeap.Graph.Limits := ⟨169, 210, 127⟩
  let selected ← checked (PhysicalHeap.Graph.select artifact.context.schemas artifact.program Scaling.joinRoot limits)
  let row ← present selected.graphs[0]? "graph budget root is missing"
  let candidate : PhysicalHeap.Graph.Candidate := ⟨row.graph.body.cells.map (·.node), row.graph.entry⟩
  let check := fun limits => PhysicalHeap.Graph.checkFunction artifact.context.schemas selected.selected.constructors #[]
    Scaling.joinRoot row.row.interface.definition row.row.interface.parameters candidate limits
  let _ ← checked (check limits)
  let mut checks := #[]
  for (name, limit) in [("nodes", { limits with nodes := 168 }), ("edges", { limits with edges := 209 }),
      ("depth", { limits with depth := 126 })] do
    let reason ← rejection name (check limit)
    let _ ← rejection s!"builder {name}" (PhysicalHeap.Graph.select artifact.context.schemas artifact.program Scaling.joinRoot limit)
    checks := checks.push (Json.mkObj [("resource", toJson name), ("reason", toJson reason)])
  let shallow := Scaling.joinArtifact 8
  let some (.fn definition) := PhysicalScalar.lookup shallow.program Scaling.joinRoot
    | throw (IO.userError "graph depth fixture is missing")
  let shallowLimits : PhysicalHeap.Graph.Limits := { depth := 17 }
  let proposal ← checked (PhysicalHeap.Graph.propose shallow.context.schemas #[] #[] 0 definition
    ⟨0, 0, PhysicalHeap.Scope.initial #[.scalar]⟩ shallowLimits)
  let cachedDepth ← rejection "cached longer path" (PhysicalHeap.Graph.checkFunction shallow.context.schemas #[] #[]
    Scaling.joinRoot definition #[.scalar] proposal shallowLimits)
  return Json.mkObj [("exact_joins", toJson (42 : Nat)), ("nodes", toJson limits.nodes), ("edges", toJson limits.edges),
    ("depth", toJson limits.depth), ("smaller_limits", toJson checks), ("cached_longer_path", toJson cachedDepth),
    ("rejections", toJson (7 : Nat))]

def produce (directory : FilePath) (profile : String) : IO Unit := do
  need (profile == "smoke" || profile == "reference") "unknown native graph profile"
  Scaling.fresh directory
  let measurements ← IO.mkRef #[]
  let mut rows := #[]
  let sharedSizes := if profile == "smoke" then #[2, 8, 9] else #[2, 3, 4, 5, 6, 7, 8, 9]
  for count in sharedSizes do
    let baseline ← row directory measurements count false
    let graph ← row directory measurements count true
    for key in ["snapshot_root", "snapshot_bytes", "input_blocks", "control_bound", "allocation_bound", "observations",
        "x86_blocks", "x86_instructions", "text_bytes", "text_root", "elf_bytes", "elf_root"] do
      need ((← field baseline key) == (← field graph key)) s!"graph/shared {key} changed"
    rows := rows ++ #[baseline, graph]
  let largerSizes := if profile == "smoke" then #[10, 16, 32, 42] else #[10, 12, 16, 24, 32, 40, 42]
  for count in largerSizes do rows := rows.push (← row directory measurements count true)
  let old := Scaling.joinArtifact 10
  let _ ← checked (old.check IxIR2.Validate.defaultLimits)
  let oldRejection ← rejection "legacy ten-join selector" (PhysicalHeap.select old.context.schemas old.program Scaling.joinRoot)
  let larger := Scaling.joinArtifact 43
  let _ ← checked (larger.check IxIR2.Validate.defaultLimits)
  let graphRejection ← rejection "source block bound" (PhysicalHeap.Graph.select larger.context.schemas larger.program Scaling.joinRoot)
  let budgets ← budgetTests
  let (contextSource, contextNative) ← HeapGraphTests.contextTest
  Scaling.writeJson (directory / "report.json") (Json.mkObj [
    ("format", toJson "compilatrix/native-graph/1"), ("profile", toJson profile),
    ("graph_limits", Json.mkObj [("nodes", toJson (4096 : Nat)), ("edges", toJson (8192 : Nat)),
      ("depth", toJson PhysicalHeap.maxDepth), ("source_blocks", toJson PhysicalHeap.maxDepth),
      ("source_instructions_per_block", toJson PhysicalHeap.maxDepth), ("functions", toJson PhysicalHeap.maxFunctions),
      ("allocations", toJson PhysicalHeap.maxAllocations), ("controls", toJson PhysicalHeap.maxControls)]),
    ("legacy_rejected_joins", toJson (10 : Nat)), ("legacy_rejection", toJson oldRejection),
    ("graph_rejected_joins", toJson (43 : Nat)), ("graph_rejection", toJson graphRejection),
    ("budget_checks", budgets), ("typed_join_contexts", toJson (2 : Nat)), ("typed_join_executions", toJson (4 : Nat)),
    ("typed_join_source_rejections", toJson contextSource), ("typed_join_native_rejections", toJson contextNative),
    ("cases", toJson rows)])
  Scaling.writeJson (directory / "measurements.json") (Json.mkObj [
    ("format", toJson "compilatrix/native-graph-measurements/1"),
    ("clock", toJson "IO.monoNanosNow; one invocation per stage, fixed shared/graph order"),
    ("excluded", toJson "fixture construction, API replay, semantic execution, mutations, budget/context tests, inspection formatting, hashing reported artifacts, file writes"),
    ("stages", toJson (← measurements.get))])
  IO.println s!"native graph ok: {rows.size} objects through 42 joins, fixed resource rejections"

end Benchmark.NativeGraph
