import Compilatrix.X86.PhysicalHeapGraphStep

namespace Compilatrix.X86.PhysicalHeap.Graph

/-- These count distinct contexts and graph edges, independently of paths.
The depth and physical resource checks remain separate. -/
structure Limits where
  nodes : Nat := 4096
  edges : Nat := 8192
  depth : Nat := 128
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Candidate where
  nodes : Array Node
  entry : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure CheckedBody (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (entries : Interfaces) (current : Nat) (definition : IxIR2.Function) where
  body : Body
  typed : ∀ cell ∈ body.cells, CodeAt schemas constructors entries current definition cell.node.point cell.tree
  summaries : ∀ cell ∈ body.cells, cell.summary.Valid entries cell.tree

def CheckedBody.empty : CheckedBody schemas constructors entries current definition :=
  ⟨Body.empty, by simp [Body.empty], by simp [Body.empty]⟩

theorem CheckedBody.child {schemas constructors entries current definition}
    (checked : CheckedBody schemas constructors entries current definition) {index : Nat}
    (bound : index < checked.body.cells.size) :
    CodeAt schemas constructors entries current definition (points checked.body.cells index) (trees checked.body.cells index) ∧
      (Graph.summaries checked.body.cells index).Valid entries (trees checked.body.cells index) := by
  have found : checked.body.cells[index]? = some checked.body.cells[index] := by simp
  have member := Array.getElem_mem bound
  simpa [points, trees, Graph.summaries, found] using
    And.intro (checked.typed _ member) (checked.summaries _ member)

def CheckedBody.push (checked : CheckedBody schemas constructors entries current definition)
    (cell : Cell) (ordered : ∀ child ∈ cell.node.shape.children, child < checked.body.cells.size)
    (model : cell.node.shape.tree (trees checked.body.cells) = cell.tree)
    (typed : CodeAt schemas constructors entries current definition cell.node.point cell.tree)
    (summary : cell.summary.Valid entries cell.tree) : CheckedBody schemas constructors entries current definition :=
  { body := checked.body.push cell ordered model
    typed := by
      intro found member
      rcases Array.mem_push.mp member with old | rfl
      · exact checked.typed found old
      · exact typed
    summaries := by
      intro found member
      rcases Array.mem_push.mp member with old | rfl
      · exact checked.summaries found old
      · exact summary }

/-- Recheck a proposed node against actual source syntax and earlier typed
contexts. All executable equality checks are local; no tree is compared. -/
def checkNode (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (entries : Interfaces) (current : Nat) (definition : IxIR2.Function) (limits : Limits)
    (checked : CheckedBody schemas constructors entries current definition) (node : Node) :
    Except String (CheckedBody schemas constructors entries current definition) := do
  if !node.point.scope.bounded then throw "heap graph point exceeds the value/credit scope bounds"
  if ordered : ∀ child ∈ node.shape.children, child < checked.body.cells.size then
    let step ← selectStep schemas constructors entries current definition node.point
    if matching : node.shape.map (points checked.body.cells) = step.shape then
      if compatible : node.shape.compatible (fun child => (Graph.summaries checked.body.cells child).result) = true then
        let tree := node.shape.tree (trees checked.body.cells)
        let summary := node.shape.summary entries (Graph.summaries checked.body.cells)
        if summary.depth > limits.depth then throw "heap graph depth exceeds the consumer limit"
        let cell : Cell := ⟨node, tree, summary⟩
        have children := fun child member => checked.child (ordered child member)
        have sound : CodeAt schemas constructors entries current definition node.point tree := by
          apply step.sound
          rw [← matching]
          apply Shape.realizes
          · exact fun child member => (children child member).1
          · rw [Shape.compatible_congr node.shape (fun child member => (children child member).2.1)]
            exact compatible
        have resources : summary.Valid entries tree :=
          node.shape.summary_valid entries _ _ (fun child member => (children child member).2)
        return checked.push cell ordered rfl sound resources
      else throw "heap graph branch result kinds disagree"
    else throw "heap graph node differs from its source instruction or child contexts"
  else throw "heap graph child is missing, forward, or cyclic"

def checkBody (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (entries : Interfaces) (current : Nat) (definition : IxIR2.Function) (candidate : Candidate)
    (limits : Limits := {}) : Except String (CheckedBody schemas constructors entries current definition) := do
  if candidate.nodes.size > limits.nodes then throw "heap graph node count exceeds the consumer limit"
  let mut edges := 0
  let mut seen : Std.HashSet Point := {}
  let mut checked := CheckedBody.empty (schemas := schemas) (constructors := constructors)
    (entries := entries) (current := current) (definition := definition)
  for node in candidate.nodes do
    if !node.point.scope.bounded then throw "heap graph point exceeds the value/credit scope bounds"
    if seen.contains node.point then throw "heap graph contains a duplicate typed context"
    seen := seen.insert node.point
    edges := edges + node.shape.children.length
    if edges > limits.edges then throw "heap graph edge count exceeds the consumer limit"
    checked ← checkNode schemas constructors entries current definition limits checked node
  return checked

end Compilatrix.X86.PhysicalHeap.Graph
