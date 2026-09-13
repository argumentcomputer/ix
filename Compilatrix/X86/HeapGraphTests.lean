import Compilatrix.X86.PhysicalHeapExamples
import Compilatrix.Tools.Check

namespace Compilatrix.X86.HeapGraphTests
open PhysicalHeap PhysicalHeap.Graph Compilatrix.Tools.Check

private def reject (name : String) (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"heap graph accepted {name}")

/-- Corrupt every selected source point and every native block/node. These
are checker calls on changed proposals, independent of hash-table behavior. -/
def mutations (selection : Graph.Selected schemas program root) (candidate : HeapGraph.Candidate)
    (baseline : Bool) : IO (Nat × Nat) := do
  let mut sourceCount := 0
  for row in selection.graphs do
    let graph := row.graph
    let original : Graph.Candidate := ⟨graph.body.cells.map (·.node), graph.entry⟩
    let prior := selection.selected.entries.extract 0 row.row.index
    let check := fun proposed => Graph.checkFunction schemas selection.selected.constructors prior
      row.row.interface.address row.row.interface.definition row.row.interface.parameters proposed
    let _ ← checked (check original)
    for index in [:original.nodes.size] do
      let node := original.nodes[index]!
      let changed : Graph.Node := { node with point := { node.point with pc := 129 } }
      reject "changed source instruction position" (check { original with nodes := original.nodes.set! index changed })
      sourceCount := sourceCount + 1
      if !node.shape.children.isEmpty then
        for child in [index, original.nodes.size] do
          let changed : Graph.Node := { node with shape := node.shape.map (fun _ => child) }
          reject "cyclic or missing source child" (check { original with nodes := original.nodes.set! index changed })
          sourceCount := sourceCount + 1
    reject "missing source root" (check { original with entry := original.nodes.size })
    reject "duplicate source context" (check { original with nodes := original.nodes.push original.nodes[0]! })
    let first := original.nodes[0]!
    let changed := { first with point := { first.point with scope := ⟨Array.replicate 17 (some .scalar), #[]⟩ } }
    reject "oversized source scope" (check { original with nodes := original.nodes.set! 0 changed })
    sourceCount := sourceCount + 3
  let check := fun proposed => HeapGraph.checkCandidate selection baseline proposed
  let mut nativeCount := 0
  for index in [:candidate.blocks.size] do
    let block := candidate.blocks[index]!
    let instructions := { block with instructions := block.instructions.push (.mov .w64 .rax (.imm 0)) }
    let control := { block with terminator := if block.terminator == .ret then .jump index.toUInt32 else .ret }
    for changed in [instructions, control] do
      reject "changed native instruction/control" (check { candidate with blocks := candidate.blocks.set! index changed })
      nativeCount := nativeCount + 1
  for index in [:candidate.functions.size] do
    let function := candidate.functions[index]!
    for nodeIndex in [:function.nodes.size] do
      let node := function.nodes[nodeIndex]!
      let changed := { function with nodes := function.nodes.set! nodeIndex { node with entry := node.entry + 1 } }
      reject "changed native node reference" (check { candidate with functions := candidate.functions.set! index changed })
      nativeCount := nativeCount + 1
    for changed in [{ function with entry := function.entry + 1 }, { function with exit := function.exit + 1 },
        { function with nodes := #[] }] do
      reject "changed native function boundary/coverage" (check { candidate with functions := candidate.functions.set! index changed })
      nativeCount := nativeCount + 1
  reject "missing native function coverage" (check { candidate with functions := #[] })
  return (sourceCount, nativeCount + 1)

/-- The same source block is entered with a scalar or an owning leaf. Their
release operations differ, so caching just the block/pc would be unsound. -/
def typedJoin : IxIR2.Wire.Artifact :=
  let base := Examples.artifact "leaf-switch"
  let definition := Examples.function #[.shared] #[
    Examples.block #[.owned .shared] #[] (.switchValue (.reg 0) #[]
      (some ⟨Examples.edge 1 #[.reg 0], Examples.edge 2 #[.reg 0]⟩)),
    Examples.block #[.owned .shared] #[.releaseShared (.reg 0)] (.jump (Examples.edge 3 #[.lit (.nat 7)])),
    Examples.block #[.scalar, .owned .shared] #[.releaseShared (.reg 1), .alloc .shared Examples.cid #[.lit (.nat 19)]]
      (.jump (Examples.edge 3 #[.reg 2])),
    Examples.block #[.owned .shared] #[.releaseShared (.reg 0)] (.ret (.lit (.nat 99)))]
  { base with program := { base.program with declarations := [(Examples.root, .fn definition)] } }

private def core (value : Nat) : Core :=
  let low : Word := 0x10000
  let top := low + 8 * 307
  let allowed := fun address : Word => decide (low ≤ address ∧ address < top + 8)
  let memory : Memory := { bytes := fun address => (address ^^^ 0xa7).toUInt8, readable := allowed, writable := allowed }
  let registers : Registers := fun register => 0x1020304050607080 + (SysV.calleeSaved.toList.idxOf register + 1).toUInt64
  { registers := (((registers.set .rsp top).set .rdi value.toUInt64).set .rsi 0).set .rdx low
    memory := (memory.write64 (low + 8) 1).write64 top 0x12345678 }

def contextTest : IO (Nat × Nat) := do
  let artifact := typedJoin
  let checkedWire ← checked (artifact.check IxIR2.Validate.defaultLimits)
  let selected ← checked (Graph.select artifact.context.schemas artifact.program Examples.root)
  let row ← present selected.graphs[0]? "typed join profile is missing"
  let joined := row.graph.body.cells.filter (fun cell => cell.node.point.block == 3 && cell.node.point.pc == 0)
  need (joined.size == 2 && joined.any (fun cell => cell.node.point.scope.values == #[some .scalar]) &&
    joined.any (fun cell => cell.node.point.scope.values == #[some .node])) "typed join contexts were merged"
  let native ← checked (HeapGraph.emitCandidate selected false)
  let mutations ← mutations selected native false
  let compiled ← checked (PhysicalHeap.compileSnapshot artifact checkedWire Examples.root)
  let baseline ← checked (PhysicalHeap.compileSnapshot artifact checkedWire Examples.root (emission := .shared))
  need (compiled.object.bytes == baseline.object.bytes) "typed join changed the retained shared artifact"
  for value in [0, 1, 2, UInt64.size - 1] do
    let physical ← checked ((IxIR2.Eval.runFunction (IxIR2.Eval.Context.ofProgram artifact.program artifact.context.schemas)
      .physical compiled.selected.entryInterface.definition #[PhysicalScalar.rval value.toUInt64] 10000 10000
      (PhysicalHeap.initialStore false)).mapError reprStr)
    let allocations := if value == 0 then 0 else 1
    need (physical.value == .lit (.nat 99) && physical.store.live == 0 &&
      physical.store.heap.allocs == allocations && physical.store.heap.frees == allocations &&
      physical.store.heap.rcops == allocations) "typed join physical ownership result changed"
    let initial := core value
    let typed := X86.runFrom Runtime.rejecting compiled.native.target 20000 initial
    need (typed.status == .halted 99 && typed.core.readReg .rdx == 0 &&
      typed.core.readReg .rsp == initial.readReg .rsp && typed.core.calleeSavedMatch initial.calleeSavedSnapshot)
      "typed join native result/caller state changed"
    let text ← present (ELFRead.text? compiled.object.bytes) "typed join text is missing"
    let entry ← present (ELF.entry? compiled.object.bytes compiled.input.exportName) "typed join entry is missing"
    let mut state : ByteEval.State := ⟨initial, 0x400000 + entry.toUInt64, {}⟩
    let mut steps := 0
    for _ in [:20000] do
      if state.rip == 0x12345678 then break
      state ← checked ((ByteEval.step text 0x400000 state).mapError reprStr)
      steps := steps + 1
    let parsed ← checked ((ObjectEval.run compiled.object.bytes compiled.input.exportName 0x400000 steps initial).mapError reprStr)
    need (parsed.rip == 0x12345678 && parsed.core.readReg .rax == 99 && parsed.core.readReg .rdx == 0 &&
      parsed.core.readReg .rsp == initial.readReg .rsp + 8 && parsed.core.calleeSavedMatch initial.calleeSavedSnapshot)
      "typed join parsed ELF result/caller state changed"
    for (field, expected) in [(2, allocations), (3, allocations), (5, allocations), (9, 0)] do
      need (parsed.core.memory.read64 (0x10000 + (8 * field).toUInt64) == expected.toUInt64)
        "typed join native counters or reservations changed"
  return mutations

end Compilatrix.X86.HeapGraphTests
