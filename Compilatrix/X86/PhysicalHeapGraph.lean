import Compilatrix.X86.PhysicalHeapCode

/-! Acyclic physical control flow with explicit node references. The tree
fields are constructed once per node, sharing their children. They connect
the graph to the existing simulation; graph consumers never traverse them. -/
namespace Compilatrix.X86.PhysicalHeap.Graph

structure Point where
  block : Nat
  pc : Nat
  scope : Scope
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

deriving instance Hashable for Kind, Scope, Point

inductive Shape (α : Type) where
  | ret (kind : Kind) (value : Scalar.Atom)
  | primitive (operation : Primitive) (next : α)
  | jump (transfer : Transfer) (next : α)
  | branch (value : Scalar.Atom) (zeroTransfer : Transfer) (zero : α)
      (succTransfer : Transfer) (successor : α)
  | call (function : Nat) (arguments : Array Scalar.Atom) (destination : Nat) (next : α)
  | tailCall (kind : Kind) (function : Nat) (arguments : Array Scalar.Atom)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Shape.map (f : α → β) : Shape α → Shape β
  | .ret kind value => .ret kind value
  | .primitive operation next => .primitive operation (f next)
  | .jump transfer next => .jump transfer (f next)
  | .branch value zt zero st succ => .branch value zt (f zero) st (f succ)
  | .call function arguments destination next => .call function arguments destination (f next)
  | .tailCall kind function arguments => .tailCall kind function arguments

def Shape.children : Shape α → List α
  | .ret .. | .tailCall .. => []
  | .primitive _ next | .jump _ next | .call _ _ _ next => [next]
  | .branch _ _ zero _ succ => [zero, succ]

def Shape.tree (get : α → Tree) : Shape α → Tree
  | .ret kind value => .ret kind value
  | .primitive operation next => .primitive operation (get next)
  | .jump transfer next => .jump transfer (get next)
  | .branch value zt zero st succ => .branch value zt (get zero) st (get succ)
  | .call function arguments destination next => .call function arguments destination (get next)
  | .tailCall kind function arguments => .tailCall kind function arguments

def Shape.compatible (get : α → Kind) : Shape α → Bool
  | .branch _ _ zero _ succ => get zero == get succ
  | _ => true

theorem Shape.tree_congr (shape : Shape α) {left right : α → Tree}
    (same : ∀ child ∈ shape.children, left child = right child) :
    shape.tree left = shape.tree right := by
  cases shape <;> simp_all [Shape.tree, Shape.children]

theorem Shape.compatible_congr (shape : Shape α) {left right : α → Kind}
    (same : ∀ child ∈ shape.children, left child = right child) :
    shape.compatible left = shape.compatible right := by
  cases shape <;> simp_all [Shape.compatible, Shape.children]

/-- Local source obligations, with already checked child continuations. -/
inductive Realizes (code : α → Tree → Prop) : Shape α → Tree → Prop where
  | ret {kind value} : Realizes code (.ret kind value) (.ret kind value)
  | primitive {operation next tree} (rest : code next tree) :
      Realizes code (.primitive operation next) (.primitive operation tree)
  | jump {transfer next tree} (rest : code next tree) :
      Realizes code (.jump transfer next) (.jump transfer tree)
  | branch {value zt zero st succ zeroTree succTree}
      (same : zeroTree.result = succTree.result) (left : code zero zeroTree) (right : code succ succTree) :
      Realizes code (.branch value zt zero st succ) (.branch value zt zeroTree st succTree)
  | call {function arguments destination next tree} (rest : code next tree) :
      Realizes code (.call function arguments destination next) (.call function arguments destination tree)
  | tailCall {kind function arguments} :
      Realizes code (.tailCall kind function arguments) (.tailCall kind function arguments)

theorem Shape.realizes (shape : Shape α) (point : α → β) (get : α → Tree)
    {code : β → Tree → Prop} (children : ∀ child ∈ shape.children, code (point child) (get child))
    (compatible : shape.compatible (fun child => (get child).result) = true) :
    Realizes code (shape.map point) (shape.tree get) := by
  cases shape with
  | ret => exact .ret
  | primitive operation next => exact .primitive (children next (by simp [Shape.children]))
  | jump transfer next => exact .jump (children next (by simp [Shape.children]))
  | branch value zt zero st succ =>
      exact .branch (beq_iff_eq.mp compatible)
        (children zero (by simp [Shape.children])) (children succ (by simp [Shape.children]))
  | call function arguments destination next => exact .call (children next (by simp [Shape.children]))
  | tailCall => exact .tailCall

structure Node where
  point : Point
  shape : Shape Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Summary where
  result : Kind
  allocations : Nat
  controls : Nat
  depth : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Shape.summary (callees : Interfaces) (get : α → Summary) : Shape α → Summary
  | .ret kind _ => ⟨kind, 0, 1, 1⟩
  | .primitive operation next =>
      let child := get next
      ⟨child.result, operation.allocations + child.allocations, 1 + child.controls, 1 + child.depth⟩
  | .jump _ next =>
      let child := get next
      ⟨child.result, child.allocations, 1 + child.controls, 1 + child.depth⟩
  | .branch _ _ zero _ succ =>
      let left := get zero
      let right := get succ
      ⟨left.result, max left.allocations right.allocations, 1 + max left.controls right.controls,
        1 + max left.depth right.depth⟩
  | .call function _ _ next =>
      let child := get next
      ⟨child.result, (callees[function]?.map (·.allocations)).getD 0 + child.allocations,
        1 + (callees[function]?.map (·.controls)).getD 0 + child.controls, 1 + child.depth⟩
  | .tailCall kind function _ =>
      ⟨kind, (callees[function]?.map (·.allocations)).getD 0,
        1 + (callees[function]?.map (·.controls)).getD 0, 1⟩

def Summary.Valid (callees : Interfaces) (tree : Tree) (summary : Summary) : Prop :=
  tree.result = summary.result ∧
  tree.allocations (callees.map (·.allocations)) = summary.allocations ∧
  tree.controls (callees.map (·.controls)) = summary.controls

theorem Shape.summary_valid (shape : Shape α) (callees : Interfaces)
    (trees : α → Tree) (summaries : α → Summary)
    (valid : ∀ child ∈ shape.children, (summaries child).Valid callees (trees child)) :
    (shape.summary callees summaries).Valid callees (shape.tree trees) := by
  cases shape <;>
    simp_all [Shape.children, Summary.Valid, Shape.summary, Shape.tree,
      Tree.result, Tree.allocations, Tree.controls, Array.getElem?_map]

structure Cell where
  node : Node
  tree : Tree
  summary : Summary
  deriving Inhabited

def trees (cells : Array Cell) (index : Nat) : Tree := (cells[index]?.getD default).tree
def points (cells : Array Cell) (index : Nat) : Point := (cells[index]?.getD default).node.point
def summaries (cells : Array Cell) (index : Nat) : Summary := (cells[index]?.getD default).summary

structure Body where
  cells : Array Cell
  ordered : ∀ (index : Nat) (cell : Cell), cells[index]? = some cell → ∀ child ∈ cell.node.shape.children, child < index
  model : ∀ (index : Nat) (cell : Cell), cells[index]? = some cell → cell.node.shape.tree (trees cells) = cell.tree

def Body.empty : Body := ⟨#[], by simp, by simp⟩

def Body.push (body : Body) (cell : Cell)
    (ordered : ∀ child ∈ cell.node.shape.children, child < body.cells.size)
    (model : cell.node.shape.tree (trees body.cells) = cell.tree) : Body := by
  refine ⟨body.cells.push cell, ?_, ?_⟩
  · intro index found present child member
    by_cases earlier : index < body.cells.size
    · exact body.ordered index found (by simpa [Array.getElem?_push, earlier, Nat.ne_of_lt earlier] using present) child member
    · have equal : index = body.cells.size := by
        obtain ⟨bound, _⟩ := Array.getElem?_eq_some_iff.mp present
        simp only [Array.size_push] at bound
        omega
      subst index
      have equal : found = cell := by simpa using present.symm
      subst found
      exact ordered child member
  · intro index found present
    by_cases earlier : index < body.cells.size
    · have old : body.cells[index]? = some found := by
        simpa [Array.getElem?_push, earlier, Nat.ne_of_lt earlier] using present
      rw [← body.model index found old]
      apply Shape.tree_congr
      intro child member
      have bound := body.ordered index found old child member
      have small : child < body.cells.size := by omega
      simp [trees, Array.getElem?_push, small, Nat.ne_of_lt small]
    · have equal : index = body.cells.size := by
        obtain ⟨bound, _⟩ := Array.getElem?_eq_some_iff.mp present
        simp only [Array.size_push] at bound
        omega
      subst index
      have equal : found = cell := by simpa using present.symm
      subst found
      rw [← model]
      apply Shape.tree_congr
      intro child member
      have small := ordered child member
      simp [trees, Array.getElem?_push, small, Nat.ne_of_lt small]

structure Root (tree : Tree) where
  body : Body
  entry : Nat
  root : Cell
  found : body.cells[entry]? = some root
  same : root.tree = tree

end Compilatrix.X86.PhysicalHeap.Graph
