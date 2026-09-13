import Compilatrix.X86.PhysicalHeapGraphCheck

namespace Compilatrix.X86.PhysicalHeap

namespace Graph

private inductive Visit where
  | active
  | done (index : Nat)

private structure BuildState where
  nodes : Array Node := #[]
  known : Std.HashMap Point Visit := {}
  visited : Nat := 0
  edges : Nat := 0

private abbrev Build := StateT BuildState (Except String)

/-- The hash table is an untrusted proposal aid. The consumer checks every
node's complete context, source operation, and backward child reference. -/
private def visit (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (entries : Interfaces) (current : Nat) (definition : IxIR2.Function) (limits : Limits) :
    Nat → Point → Build Nat
  | fuel, point => do
    let state ← get
    match state.known[point]? with
    | some (.done index) => return index
    | some .active => throw "heap graph contains a cycle through the same typed context"
    | none =>
      match fuel with
      | 0 => throw "heap graph exploration exceeds the depth limit"
      | fuel + 1 =>
        if state.visited >= limits.nodes then throw "heap graph distinct context count exceeds the consumer limit"
        set { state with known := state.known.insert point .active, visited := state.visited + 1 }
        let step ← selectStep schemas constructors entries current definition point
        let shape : Shape Nat ← match step.shape with
          | .ret kind value => pure (.ret kind value)
          | .primitive operation next => do
            pure (.primitive operation (← visit schemas constructors entries current definition limits fuel next))
          | .jump transfer next => do
            pure (.jump transfer (← visit schemas constructors entries current definition limits fuel next))
          | .branch value zt zero st succ => do
            let left ← visit schemas constructors entries current definition limits fuel zero
            let right ← visit schemas constructors entries current definition limits fuel succ
            pure (.branch value zt left st right)
          | .call function arguments destination next => do
            pure (.call function arguments destination (← visit schemas constructors entries current definition limits fuel next))
          | .tailCall kind function arguments => pure (.tailCall kind function arguments)
        let state ← get
        let edges := state.edges + shape.children.length
        if edges > limits.edges then throw "heap graph edge count exceeds the consumer limit"
        let index := state.nodes.size
        set { state with
          nodes := state.nodes.push ⟨point, shape⟩
          known := state.known.insert point (.done index)
          edges }
        return index

def propose (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (entries : Interfaces) (current : Nat) (definition : IxIR2.Function) (point : Point)
    (limits : Limits := {}) : Except String Candidate := do
  let (entry, state) ← (visit schemas constructors entries current definition limits limits.depth point).run {}
  return ⟨state.nodes, entry⟩

end Graph
end Compilatrix.X86.PhysicalHeap
