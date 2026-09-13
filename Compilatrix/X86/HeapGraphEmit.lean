import Compilatrix.X86.HeapGraphPlan

namespace Compilatrix.X86.HeapGraph
open PhysicalHeap PhysicalHeap.Graph

structure Candidate where
  blocks : Array Block
  functions : Array FunctionPlan
  entry : HeapTarget.EntryPlan

def Candidate.program (candidate : Candidate) : X86.Program :=
  { blocks := candidate.blocks, entry := candidate.entry.entry }

def Candidate.entries (candidate : Candidate) : Array BlockId := candidate.functions.map (·.entry)

private def emitNode (entries : Array BlockId) (exit : BlockId) (prior : Array NodePlan) :
    Shape Nat → BlockSharing.Emit NodePlan
  | .ret _ value => do
    return ⟨← BlockSharing.emit [Scalar.load .rax value] (.jump exit), 0, 0⟩
  | .primitive operation next => do
    let some child := prior[next]? | throw "heap graph emission child is missing"
    return ⟨← BlockSharing.emit (HeapTarget.primitive operation) (.jump child.entry), 0, 0⟩
  | .jump copies next => do
    let some child := prior[next]? | throw "heap graph emission child is missing"
    return ⟨← BlockSharing.emit (HeapTarget.transfer copies) (.jump child.entry), 0, 0⟩
  | .branch value zt zeroIndex st succIndex => do
    let some left := prior[zeroIndex]? | throw "heap graph emission zero child is missing"
    let some right := prior[succIndex]? | throw "heap graph emission successor child is missing"
    let zeroEdge ← BlockSharing.emit (HeapTarget.transfer zt) (.jump left.entry)
    let succEdge ← BlockSharing.emit (HeapTarget.transfer st) (.jump right.entry)
    let entry ← BlockSharing.emit [Scalar.load .rax value] (.branch Scalar.zeroCompare .eq zeroEdge succEdge)
    return ⟨entry, zeroEdge, succEdge⟩
  | .call function operands destination next => do
    let some target := entries[function]? | throw "heap graph emission callee is missing"
    let some child := prior[next]? | throw "heap graph emission child is missing"
    let entry ← BlockSharing.emit (HeapTarget.arguments target operands ++ [.spill (Scalar.slot destination) .rax]) (.jump child.entry)
    return ⟨entry, 0, 0⟩
  | .tailCall _ function operands => do
    let some target := entries[function]? | throw "heap graph emission tail callee is missing"
    return ⟨← BlockSharing.emit (HeapTarget.arguments target operands) (.jump exit), 0, 0⟩

private def emitFunction (entries : Array BlockId) (parameters : Nat) (graph : Root tree) :
    BlockSharing.Emit FunctionPlan := do
  let exit ← BlockSharing.emit Scalar.successInstructions .ret
  let mut nodes : Array NodePlan := #[]
  for cell in graph.body.cells do
    nodes := nodes.push (← emitNode entries exit nodes cell.node.shape)
  let some body := nodes[graph.entry]? | throw "heap graph emission root is missing"
  return ⟨← BlockSharing.emit (Scalar.prologue parameters) (.jump body.entry), exit, nodes⟩

/-- Emit each selected node once, retaining complete native block interning. -/
def emitCandidate (selection : Graph.Selected schemas program root) (baseline : Bool := false) :
    Except String Candidate := do
  let ((functions, entry), state) ← (do
    let mut functions : Array FunctionPlan := #[]
    for row in selection.graphs do
      functions := functions.push (← emitFunction (functions.map (·.entry)) row.row.interface.parameters.size row.graph)
    let entry ← HeapTarget.emitEntry baseline ((functions.map (·.entry))[selection.selected.entry]?.getD 0)
      selection.selected.entryInterface.allocations
    return (functions, entry) : BlockSharing.Emit (Array FunctionPlan × HeapTarget.EntryPlan)).run { sharing := true }
  return { blocks := state.blocks, functions, entry }

end Compilatrix.X86.HeapGraph
