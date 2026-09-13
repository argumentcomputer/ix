import Compilatrix.X86.HeapTarget
import Compilatrix.X86.PhysicalHeapGraphSelect

namespace Compilatrix.X86.HeapGraph
open PhysicalHeap PhysicalHeap.Graph

/-- One native certificate row per selected graph node. Child plans are
referenced through the checked source graph, rather than copied into rows. -/
structure NodePlan where
  entry : BlockId
  zeroEdge : BlockId := 0
  succEdge : BlockId := 0
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def NodePlan.plan (node : NodePlan) (get : Nat → HeapTarget.Plan) : Shape Nat → HeapTarget.Plan
  | .ret kind value => .ret node.entry kind value
  | .primitive operation next => .primitive node.entry operation (get next)
  | .jump transfer next => .jump node.entry transfer (get next)
  | .branch value zt left st right => .branch node.entry node.zeroEdge node.succEdge value zt (get left) st (get right)
  | .call function arguments destination next => .call node.entry function arguments destination (get next)
  | .tailCall kind function arguments => .tailCall node.entry kind function arguments

def NodePlan.matches (node : NodePlan) (program : X86.Program) (entries : Array BlockId)
    (exit : BlockId) (get : Nat → BlockId) : Shape Nat → Bool
  | .ret _ value => value.valid maxValues && Scalar.blockMatches program node.entry [Scalar.load .rax value] (.jump exit)
  | .primitive operation next =>
      HeapTarget.primitiveValid operation &&
        Scalar.blockMatches program node.entry (HeapTarget.primitive operation) (.jump (get next))
  | .jump copies next =>
      HeapTarget.transferValid copies &&
        Scalar.blockMatches program node.entry (HeapTarget.transfer copies) (.jump (get next))
  | .branch value zt left st right =>
      value.valid maxValues && HeapTarget.transferValid zt && HeapTarget.transferValid st &&
      Scalar.blockMatches program node.entry [Scalar.load .rax value] (.branch Scalar.zeroCompare .eq node.zeroEdge node.succEdge) &&
      Scalar.blockMatches program node.zeroEdge (HeapTarget.transfer zt) (.jump (get left)) &&
      Scalar.blockMatches program node.succEdge (HeapTarget.transfer st) (.jump (get right))
  | .call function operands destination next =>
      operands.size ≤ 2 && operands.all (·.valid maxValues) && destination < maxValues &&
      match entries[function]? with
      | none => false
      | some target => Scalar.blockMatches program node.entry
          (HeapTarget.arguments target operands ++ [.spill (Scalar.slot destination) .rax]) (.jump (get next))
  | .tailCall _ function operands =>
      operands.size ≤ 2 && operands.all (·.valid maxValues) &&
      match entries[function]? with
      | none => false
      | some target => Scalar.blockMatches program node.entry (HeapTarget.arguments target operands) (.jump exit)

theorem NodePlan.tree (node : NodePlan) (shape : Shape Nat) (get : Nat → HeapTarget.Plan) :
    (node.plan get shape).tree = shape.tree (fun child => (get child).tree) := by
  cases shape <;> rfl

theorem NodePlan.sound (node : NodePlan) (shape : Shape Nat) (program : X86.Program)
    (entries : Array BlockId) (exit : BlockId) (get : Nat → HeapTarget.Plan)
    (children : ∀ child ∈ shape.children, (get child).matches program entries exit = true)
    (checked : node.matches program entries exit (fun child => (get child).entry) shape = true) :
    (node.plan get shape).matches program entries exit = true := by
  cases shape <;>
    simp_all [Shape.children, NodePlan.plan, NodePlan.matches, HeapTarget.Plan.matches]
  all_goals exact checked.2

def plans (pool : Array HeapTarget.Plan) (index : Nat) : HeapTarget.Plan := pool[index]?.getD default

structure CheckedPlans (graph : Body) (program : X86.Program) (entries : Array BlockId) (exit : BlockId) where
  pool : Array HeapTarget.Plan
  size : pool.size ≤ graph.cells.size
  trees : ∀ (index : Nat) (plan : HeapTarget.Plan) (cell : Cell),
    pool[index]? = some plan → graph.cells[index]? = some cell → plan.tree = cell.tree
  verified : ∀ plan ∈ pool, plan.matches program entries exit = true

def CheckedPlans.empty (graph : Body) : CheckedPlans graph program entries exit :=
  ⟨#[], by simp, by simp, by simp⟩

theorem CheckedPlans.child (checked : CheckedPlans graph program entries exit) {index : Nat}
    (bound : index < checked.pool.size) :
    (plans checked.pool index).tree = Graph.trees graph.cells index ∧
      (plans checked.pool index).matches program entries exit = true := by
  have sourceBound : index < graph.cells.size := Nat.lt_of_lt_of_le bound checked.size
  have planAt : checked.pool[index]? = some checked.pool[index] := by simp
  have cellAt : graph.cells[index]? = some graph.cells[index] := by simp
  simpa [plans, Graph.trees, planAt, cellAt] using
    And.intro (checked.trees index _ _ planAt cellAt) (checked.verified _ (Array.getElem_mem bound))

def CheckedPlans.push (checked : CheckedPlans graph program entries exit) (plan : HeapTarget.Plan) (cell : Cell)
    (found : graph.cells[checked.pool.size]? = some cell) (tree : plan.tree = cell.tree)
    (verified : plan.matches program entries exit = true) : CheckedPlans graph program entries exit :=
  { pool := checked.pool.push plan
    size := by
      obtain ⟨bound, _⟩ := Array.getElem?_eq_some_iff.mp found
      simp only [Array.size_push]
      omega
    trees := by
      intro index actual source present sourceAt
      by_cases last : index = checked.pool.size
      · subst index
        have same : actual = plan := by simpa using present.symm
        have sameSource : source = cell := Option.some.inj (sourceAt.symm.trans found)
        subst actual
        subst source
        exact tree
      · exact checked.trees index actual source (by simpa [Array.getElem?_push, last] using present) sourceAt
    verified := by
      intro actual member
      rcases Array.mem_push.mp member with old | rfl
      · exact checked.verified actual old
      · exact verified }

def checkNode (graph : Body) (program : X86.Program) (entries : Array BlockId) (exit : BlockId)
    (checked : CheckedPlans graph program entries exit) (node : NodePlan) :
    Except String (CheckedPlans graph program entries exit) := do
  match found : graph.cells[checked.pool.size]? with
  | none => throw "heap graph native certificate has extra nodes"
  | some cell =>
    if matching : node.matches program entries exit (fun child => (plans checked.pool child).entry) cell.node.shape = true then
      let plan := node.plan (plans checked.pool) cell.node.shape
      have children := fun child member => checked.child (graph.ordered _ _ found child member)
      have tree : plan.tree = cell.tree := by
        rw [NodePlan.tree]
        rw [Shape.tree_congr cell.node.shape (fun child member => (children child member).1)]
        exact graph.model _ _ found
      have verified := node.sound cell.node.shape program entries exit (plans checked.pool)
        (fun child member => (children child member).2) matching
      return checked.push plan cell found tree verified
    else throw "heap graph native instruction, slot, or control certificate failed"

structure FunctionPlan where
  entry : BlockId
  exit : BlockId
  nodes : Array NodePlan
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def checkFunction (graph : Root tree) (program : X86.Program) (entries : Array BlockId)
    (parameters : Nat) (candidate : FunctionPlan) :
    Except String { plan : HeapTarget.FunctionPlan // plan.entry = candidate.entry ∧
      plan.matches program entries parameters tree = true } := do
  if candidate.nodes.size != graph.body.cells.size then throw "heap graph native node coverage is incomplete"
  let mut checked := CheckedPlans.empty (program := program) (entries := entries) (exit := candidate.exit) graph.body
  for node in candidate.nodes do
    checked ← checkNode graph.body program entries candidate.exit checked node
  if _size : checked.pool.size = graph.body.cells.size then
    match found : checked.pool[graph.entry]? with
    | none => throw "heap graph native root plan is missing"
    | some body =>
      let plan : HeapTarget.FunctionPlan := ⟨candidate.entry, candidate.exit, body⟩
      if small : parameters ≤ 2 then
        if prologue : Scalar.blockMatches program candidate.entry (Scalar.prologue parameters) (.jump body.entry) = true then
          if epilogue : Scalar.blockMatches program candidate.exit Scalar.successInstructions .ret = true then
            have tree : body.tree = tree := (checked.trees _ _ _ found graph.found).trans graph.same
            have verified := checked.verified body (Array.mem_of_getElem? found)
            return ⟨plan, rfl, by
              simp only [HeapTarget.FunctionPlan.matches, plan, tree, beq_self_eq_true,
                decide_eq_true small, prologue, epilogue, verified, Bool.and_self]⟩
          else throw "heap graph native epilogue certificate failed"
        else throw "heap graph native prologue certificate failed"
      else throw "heap graph native parameter count exceeds two"
  else throw "heap graph native node coverage changed during checking"

end Compilatrix.X86.HeapGraph
