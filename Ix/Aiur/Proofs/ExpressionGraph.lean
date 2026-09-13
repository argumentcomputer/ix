/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Field

/-!
The native base-node graph, its checked read layout, and forward evaluation.
The layout checker requires children before parents, bounded roots and leaf
indices, and no stage-two columns in the lookup prefix. Valid inputs admit
both sweeps. Their results agree with unfolded expressions for arbitrary
working operations, and their lookup values agree on the shared prefix.

These are total Lean definitions. The native comparison evaluates actual
Rust graphs and the guard on malformed layouts. Refinement of Rust execution,
frontend compilation, key decoding and cryptographic acceptance remains open.
-/

namespace Aiur.NativeAIR

inductive Source where
  | preprocessed | main | stage2
  deriving DecidableEq, Repr

inductive RowOffset where
  | current | next
  deriving DecidableEq, Repr

structure ColRef where
  source : Source
  offset : RowOffset
  index : Nat
  deriving DecidableEq, Repr

inductive Node where
  | konst (value : G)
  | var (column : ColRef)
  | publicInput (index : Nat)
  | isFirstRow | isLastRow | isTransition
  | add (left right : Nat)
  | sub (left right : Nat)
  | mul (left right : Nat)
  | neg (child : Nat)
  deriving DecidableEq, Repr

structure GraphWidths where
  preprocessed : Nat
  main : Nat
  stage2 : Nat
  publics : Nat
  deriving DecidableEq, Repr

def GraphWidths.width (widths : GraphWidths) : Source → Nat
  | .preprocessed => widths.preprocessed
  | .main => widths.main
  | .stage2 => widths.stage2

structure Lookup where
  multiplicity : Nat
  args : List Nat
  deriving DecidableEq, Repr

structure Graph where
  nodes : List Node
  zeros : List Nat
  lookups : List Lookup
  deriving DecidableEq, Repr

def Lookup.roots (lookup : Lookup) : List Nat := lookup.multiplicity :: lookup.args
def Graph.lookupRoots (graph : Graph) : List Nat := graph.lookups.flatMap Lookup.roots
/-- The dense prefix reconstructed by the native codec. Compilation can
intern extra nodes before folding its last lookup, so its stored prefix can
be longer. Children before parents make this root-derived prefix sufficient. -/
def Graph.lookupPrefix (graph : Graph) : Nat :=
  graph.lookupRoots.foldr (fun index rest => max (index + 1) rest) 0

def Node.Valid (widths : GraphWidths) (lookupEnd index : Nat) : Node → Prop
  | .konst _ | .isFirstRow | .isLastRow | .isTransition => True
  | .var column => column.index < widths.width column.source ∧
      (column.source = .stage2 → lookupEnd ≤ index)
  | .publicInput input => input < widths.publics
  | .add a b | .sub a b | .mul a b => a < index ∧ b < index
  | .neg a => a < index

def Node.check (widths : GraphWidths) (lookupEnd index : Nat) : Node → Bool
  | .konst _ | .isFirstRow | .isLastRow | .isTransition => true
  | .var column => column.index < widths.width column.source &&
      (column.source != .stage2 || lookupEnd ≤ index)
  | .publicInput input => input < widths.publics
  | .add a b | .sub a b | .mul a b => a < index && b < index
  | .neg a => a < index

theorem Node.check_iff (widths : GraphWidths) (lookupEnd index : Nat) (node : Node) :
    node.check widths lookupEnd index = true ↔ node.Valid widths lookupEnd index := by
  cases node <;> simp only [Node.check, Node.Valid, Bool.and_eq_true,
    Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, iff_self]
  case var column =>
    cases column.source <;> simp

def checkNodes (widths : GraphWidths) (lookupEnd : Nat) : Nat → List Node → Bool
  | _, [] => true
  | index, node :: nodes => node.check widths lookupEnd index && checkNodes widths lookupEnd (index + 1) nodes

inductive ValidNodes (widths : GraphWidths) (lookupEnd : Nat) : Nat → List Node → Prop where
  | nil (index : Nat) : ValidNodes widths lookupEnd index []
  | cons {index : Nat} {node : Node} {nodes : List Node}
      (valid : node.Valid widths lookupEnd index)
      (rest : ValidNodes widths lookupEnd (index + 1) nodes) :
      ValidNodes widths lookupEnd index (node :: nodes)

theorem checkNodes_iff (widths : GraphWidths) (lookupEnd index : Nat) (nodes : List Node) :
    checkNodes widths lookupEnd index nodes = true ↔ ValidNodes widths lookupEnd index nodes := by
  induction nodes generalizing index with
  | nil => exact ⟨fun _ => .nil _, fun _ => rfl⟩
  | cons node nodes ih =>
    simp only [checkNodes, Bool.and_eq_true, Node.check_iff, ih]
    exact ⟨fun ⟨valid, rest⟩ => .cons valid rest, fun valid => by cases valid; exact ⟨‹_›, ‹_›⟩⟩

def checkedGraphPrefix (widths : GraphWidths) (graph : Graph) : Option Nat :=
  if graph.zeros.all (· < graph.nodes.length) && graph.lookupRoots.all (· < graph.nodes.length) &&
      checkNodes widths graph.lookupPrefix 0 graph.nodes then
    some graph.lookupPrefix
  else none

structure Graph.Valid (widths : GraphWidths) (graph : Graph) : Prop where
  nodes : ValidNodes widths graph.lookupPrefix 0 graph.nodes
  zeros : ∀ index ∈ graph.zeros, index < graph.nodes.length
  lookups : ∀ index ∈ graph.lookupRoots, index < graph.nodes.length

theorem checkedGraphPrefix_iff (widths : GraphWidths) (graph : Graph) (lookupEnd : Nat) :
    checkedGraphPrefix widths graph = some lookupEnd ↔ graph.Valid widths ∧ lookupEnd = graph.lookupPrefix := by
  simp only [checkedGraphPrefix]
  split
  next accepted =>
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, checkNodes_iff] at accepted
    obtain ⟨⟨zeros, lookups⟩, nodes⟩ := accepted
    exact ⟨fun equal => ⟨⟨nodes, zeros, lookups⟩, (Option.some.inj equal).symm⟩,
      fun ⟨_, equal⟩ => congrArg some equal.symm⟩
  next rejected =>
    constructor
    · intro equal; cases equal
    · rintro ⟨valid, _⟩
      apply False.elim
      apply rejected
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, checkNodes_iff]
      exact ⟨⟨valid.zeros, valid.lookups⟩, valid.nodes⟩

theorem roots_below_prefix (roots : List Nat) (index : Nat) (member : index ∈ roots) :
    index < roots.foldr (fun root rest => max (root + 1) rest) 0 := by
  induction roots with
  | nil => simp only [List.not_mem_nil] at member
  | cons root roots ih =>
    simp only [List.mem_cons] at member
    simp only [List.foldr_cons]
    rcases member with rfl | member
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih member) (Nat.le_max_right _ _)

theorem prefix_bounded (roots : List Nat) (bound : Nat) (bounded : ∀ index ∈ roots, index < bound) :
    roots.foldr (fun root rest => max (root + 1) rest) 0 ≤ bound := by
  induction roots with
  | nil => exact Nat.zero_le _
  | cons root roots ih =>
    simp only [List.foldr_cons, Nat.max_le]
    exact ⟨bounded root (by simp), ih (fun index member => bounded index (by simp [member]))⟩

theorem Graph.Valid.prefix_bounded {widths : GraphWidths} {graph : Graph} (valid : graph.Valid widths) :
    graph.lookupPrefix ≤ graph.nodes.length := Aiur.NativeAIR.prefix_bounded _ _ valid.lookups

structure EvalOps (W : Type u) where
  konst : G → W
  add : W → W → W
  sub : W → W → W
  mul : W → W → W
  neg : W → W

structure Values (W : Type u) where
  columns : Source → RowOffset → Array W
  publics : Array W
  isFirstRow : W
  isLastRow : W
  isTransition : W

def Values.Fits (values : Values W) (widths : GraphWidths) : Prop :=
  (∀ source offset, (values.columns source offset).size = widths.width source) ∧
    values.publics.size = widths.publics

def Node.eval (ops : EvalOps W) (values : Values W) (buffer : Array W) : Node → Option W
  | .konst value => some (ops.konst value)
  | .var column => (values.columns column.source column.offset)[column.index]?
  | .publicInput index => values.publics[index]?
  | .isFirstRow => some values.isFirstRow
  | .isLastRow => some values.isLastRow
  | .isTransition => some values.isTransition
  | .add a b => return ops.add (← buffer[a]?) (← buffer[b]?)
  | .sub a b => return ops.sub (← buffer[a]?) (← buffer[b]?)
  | .mul a b => return ops.mul (← buffer[a]?) (← buffer[b]?)
  | .neg a => return ops.neg (← buffer[a]?)

theorem Node.eval_defined (ops : EvalOps W) (values : Values W) (buffer : Array W)
    {widths : GraphWidths} {lookupEnd : Nat} {node : Node}
    (fits : values.Fits widths) (valid : node.Valid widths lookupEnd buffer.size) :
    ∃ value, node.eval ops values buffer = some value := by
  cases node <;> simp only [Node.Valid] at valid
  all_goals try exact ⟨_, rfl⟩
  case var column =>
    have bounded : column.index < (values.columns column.source column.offset).size := by
      rw [fits.1]; exact valid.1
    exact ⟨_, Array.getElem?_eq_getElem bounded⟩
  case publicInput input =>
    have bounded : input < values.publics.size := by rw [fits.2]; exact valid
    exact ⟨_, Array.getElem?_eq_getElem bounded⟩
  case add a b => simp [Node.eval, Array.getElem?_eq_getElem valid.1, Array.getElem?_eq_getElem valid.2]
  case sub a b => simp [Node.eval, Array.getElem?_eq_getElem valid.1, Array.getElem?_eq_getElem valid.2]
  case mul a b => simp [Node.eval, Array.getElem?_eq_getElem valid.1, Array.getElem?_eq_getElem valid.2]
  case neg a => simp [Node.eval, Array.getElem?_eq_getElem valid]

def sweepFrom (ops : EvalOps W) (values : Values W) : List Node → Array W → Option (Array W)
  | [], buffer => some buffer
  | node :: nodes, buffer => do
    let value ← node.eval ops values buffer
    sweepFrom ops values nodes (buffer.push value)

def Graph.sweep (graph : Graph) (ops : EvalOps W) (values : Values W) : Option (Array W) :=
  sweepFrom ops values graph.nodes #[]

theorem sweepFrom_defined (ops : EvalOps W) (values : Values W) (nodes : List Node) (buffer : Array W)
    {widths : GraphWidths} {lookupEnd : Nat} (fits : values.Fits widths)
    (valid : ValidNodes widths lookupEnd buffer.size nodes) :
    ∃ result, sweepFrom ops values nodes buffer = some result ∧ result.size = buffer.size + nodes.length := by
  induction nodes generalizing buffer with
  | nil => exact ⟨buffer, rfl, by simp⟩
  | cons node nodes ih =>
    cases valid with
    | cons valid rest =>
      obtain ⟨value, evaluated⟩ := Node.eval_defined ops values buffer fits valid
      obtain ⟨result, swept, length⟩ := ih (buffer.push value) (by simpa only [Array.size_push] using rest)
      refine ⟨result, ?_, ?_⟩
      · simp only [sweepFrom, evaluated, bind, Option.bind, swept]
      · simp only [Array.size_push, List.length_cons] at length ⊢; omega

theorem Graph.Valid.sweep_defined {widths : GraphWidths} {graph : Graph} (valid : graph.Valid widths)
    (ops : EvalOps W) (values : Values W) (fits : values.Fits widths) :
    ∃ result, graph.sweep ops values = some result ∧ result.size = graph.nodes.length := by
  simpa only [Graph.sweep, Array.size_empty, Nat.zero_add] using
    sweepFrom_defined ops values graph.nodes #[] fits valid.nodes

theorem ValidNodes.take {widths : GraphWidths} {lookupEnd index : Nat} {nodes : List Node}
    (valid : ValidNodes widths lookupEnd index nodes) (count : Nat) :
    ValidNodes widths lookupEnd index (nodes.take count) := by
  induction valid generalizing count with
  | nil index => simpa using ValidNodes.nil (widths := widths) (lookupEnd := lookupEnd) index
  | cons valid rest ih =>
    cases count with
    | zero => exact .nil _
    | succ count => exact .cons valid (ih count)

def Values.withoutStage2 (values : Values W) : Values W :=
  { values with columns := fun source offset =>
      match source with
      | .stage2 => #[]
      | _ => values.columns source offset }

theorem Node.eval_withoutStage2 (ops : EvalOps W) (values : Values W) (buffer : Array W)
    {widths : GraphWidths} {lookupEnd : Nat} {node : Node}
    (valid : node.Valid widths lookupEnd buffer.size) (inside : buffer.size < lookupEnd) :
    node.eval ops values.withoutStage2 buffer = node.eval ops values buffer := by
  cases node <;> try rfl
  case var column =>
    cases source : column.source <;> simp only [Node.eval, Values.withoutStage2, source]
    exact False.elim (Nat.not_lt_of_ge (valid.2 source) inside)

theorem sweepFrom_withoutStage2 (ops : EvalOps W) (values : Values W) (nodes : List Node) (buffer : Array W)
    {widths : GraphWidths} {lookupEnd : Nat} (valid : ValidNodes widths lookupEnd buffer.size nodes)
    (inside : buffer.size + nodes.length ≤ lookupEnd) :
    sweepFrom ops values.withoutStage2 nodes buffer = sweepFrom ops values nodes buffer := by
  induction nodes generalizing buffer with
  | nil => rfl
  | cons node nodes ih =>
    cases valid with
    | cons valid rest =>
      have lt : buffer.size < lookupEnd := by simp only [List.length_cons] at inside; omega
      simp only [sweepFrom, Node.eval_withoutStage2 ops values buffer valid lt]
      cases evaluated : node.eval ops values buffer with
      | none => rfl
      | some value =>
        simp only [bind, Option.bind]
        exact ih (buffer.push value) (by simpa only [Array.size_push] using rest)
          (by simp only [Array.size_push, List.length_cons] at inside ⊢; omega)

theorem sweepFrom_append (ops : EvalOps W) (values : Values W) (left right : List Node) (buffer : Array W) :
    sweepFrom ops values (left ++ right) buffer =
      (sweepFrom ops values left buffer).bind (sweepFrom ops values right) := by
  induction left generalizing buffer with
  | nil => rfl
  | cons node nodes ih =>
    simp only [List.cons_append, sweepFrom]
    cases node.eval ops values buffer with
    | none => rfl
    | some value => exact ih (buffer.push value)

theorem sweepFrom_preserves (ops : EvalOps W) (values : Values W) (nodes : List Node)
    {buffer result : Array W} (swept : sweepFrom ops values nodes buffer = some result)
    (index : Nat) (bound : index < buffer.size) : result[index]? = buffer[index]? := by
  induction nodes generalizing buffer with
  | nil => cases swept; rfl
  | cons node nodes ih =>
    simp only [sweepFrom] at swept
    cases evaluated : node.eval ops values buffer with
    | none => simp only [evaluated, bind, Option.bind, reduceCtorEq] at swept
    | some value =>
      simp only [evaluated, bind, Option.bind] at swept
      exact (ih swept (by simp only [Array.size_push]; omega)).trans
        ((Array.getElem?_push_lt bound).trans (Array.getElem?_eq_getElem bound).symm)

def Graph.sweepLookupPrefix (graph : Graph) (ops : EvalOps W) (values : Values W) : Option (Array W) :=
  sweepFrom ops values.withoutStage2 (graph.nodes.take graph.lookupPrefix) #[]

theorem Graph.Valid.lookup_sweep_defined {widths : GraphWidths} {graph : Graph} (valid : graph.Valid widths)
    (ops : EvalOps W) (values : Values W) (fits : values.Fits widths) :
    ∃ result, graph.sweepLookupPrefix ops values = some result ∧ result.size = graph.lookupPrefix := by
  have nodes := valid.nodes.take graph.lookupPrefix
  have length : (graph.nodes.take graph.lookupPrefix).length = graph.lookupPrefix :=
    List.length_take_of_le valid.prefix_bounded
  unfold Graph.sweepLookupPrefix
  rw [sweepFrom_withoutStage2 ops values _ #[] nodes (by simp only [Array.size_empty, Nat.zero_add, length, Nat.le_refl])]
  simpa only [Array.size_empty, Nat.zero_add, length] using sweepFrom_defined ops values _ #[] fits nodes

theorem Graph.Valid.lookup_sweep_agrees {widths : GraphWidths} {graph : Graph} (valid : graph.Valid widths)
    (ops : EvalOps W) (values : Values W) {full prefixValues : Array W}
    (fullSweep : graph.sweep ops values = some full)
    (partialSweep : graph.sweepLookupPrefix ops values = some prefixValues)
    (index : Nat) (bound : index < prefixValues.size) : full[index]? = prefixValues[index]? := by
  have nodes := valid.nodes.take graph.lookupPrefix
  have length : (graph.nodes.take graph.lookupPrefix).length = graph.lookupPrefix :=
    List.length_take_of_le valid.prefix_bounded
  unfold Graph.sweepLookupPrefix at partialSweep
  rw [sweepFrom_withoutStage2 ops values _ #[] nodes (by simp only [Array.size_empty, Nat.zero_add, length, Nat.le_refl])]
    at partialSweep
  unfold Graph.sweep at fullSweep
  rw [← List.take_append_drop graph.lookupPrefix graph.nodes, sweepFrom_append, partialSweep] at fullSweep
  exact sweepFrom_preserves ops values _ fullSweep index bound

inductive Expr where
  | konst (value : G)
  | var (column : ColRef)
  | publicInput (index : Nat)
  | isFirstRow | isLastRow | isTransition
  | add (left right : Expr)
  | sub (left right : Expr)
  | mul (left right : Expr)
  | neg (child : Expr)
  deriving DecidableEq, Repr

def Expr.eval (ops : EvalOps W) (values : Values W) : Expr → Option W
  | .konst value => some (ops.konst value)
  | .var column => (values.columns column.source column.offset)[column.index]?
  | .publicInput index => values.publics[index]?
  | .isFirstRow => some values.isFirstRow
  | .isLastRow => some values.isLastRow
  | .isTransition => some values.isTransition
  | .add a b => return ops.add (← a.eval ops values) (← b.eval ops values)
  | .sub a b => return ops.sub (← a.eval ops values) (← b.eval ops values)
  | .mul a b => return ops.mul (← a.eval ops values) (← b.eval ops values)
  | .neg a => return ops.neg (← a.eval ops values)

def Node.unfold (trees : Array Expr) : Node → Option Expr
  | .konst value => some (.konst value)
  | .var column => some (.var column)
  | .publicInput index => some (.publicInput index)
  | .isFirstRow => some .isFirstRow
  | .isLastRow => some .isLastRow
  | .isTransition => some .isTransition
  | .add a b => return .add (← trees[a]?) (← trees[b]?)
  | .sub a b => return .sub (← trees[a]?) (← trees[b]?)
  | .mul a b => return .mul (← trees[a]?) (← trees[b]?)
  | .neg a => return .neg (← trees[a]?)

def Reflects (ops : EvalOps W) (values : Values W) (trees : Array Expr) (buffer : Array W) : Prop :=
  buffer.size = trees.size ∧ ∀ index : Nat, buffer[index]? = (trees[index]?).bind (Expr.eval ops values)

theorem Node.unfold_eval (ops : EvalOps W) (values : Values W) {trees : Array Expr} {buffer : Array W}
    (reflects : Reflects ops values trees buffer) (node : Node) {expr : Expr}
    (unfolded : node.unfold trees = some expr) : node.eval ops values buffer = expr.eval ops values := by
  cases node <;> simp only [Node.unfold] at unfolded
  all_goals first
    | (cases unfolded; rfl)
    | skip
  all_goals simp only [Node.eval, reflects.2]
  all_goals
    repeat first
      | (split at unfolded)
      | (rename_i a b; cases ha : trees[a]? <;> cases hb : trees[b]? <;>
          simp only [ha, hb, bind, Option.bind, pure, reduceCtorEq] at unfolded ⊢)
      | (rename_i a; cases ha : trees[a]? <;>
          simp only [ha, bind, Option.bind, pure, reduceCtorEq] at unfolded ⊢)
  all_goals cases unfolded; rfl

theorem Reflects.push {ops : EvalOps W} {values : Values W} {trees : Array Expr} {buffer : Array W}
    (reflects : Reflects ops values trees buffer) (expr : Expr) (value : W)
    (evaluated : expr.eval ops values = some value) :
    Reflects ops values (trees.push expr) (buffer.push value) := by
  refine ⟨by simpa only [Array.size_push] using congrArg (· + 1) reflects.1, ?_⟩
  intro index
  simp only [Array.getElem?_push, reflects.1]
  split
  · simpa only [Option.bind_some] using evaluated.symm
  · exact reflects.2 index

def unfoldFrom : List Node → Array Expr → Option (Array Expr)
  | [], trees => some trees
  | node :: nodes, trees => do
    let expr ← node.unfold trees
    unfoldFrom nodes (trees.push expr)

def Graph.unfold (graph : Graph) : Option (Array Expr) := unfoldFrom graph.nodes #[]

theorem Node.unfold_defined {trees : Array Expr} {widths : GraphWidths} {lookupEnd : Nat} {node : Node}
    (valid : node.Valid widths lookupEnd trees.size) : ∃ expr, node.unfold trees = some expr := by
  cases node <;> simp only [Node.Valid] at valid
  all_goals try exact ⟨_, rfl⟩
  case add a b => simp [Node.unfold, Array.getElem?_eq_getElem valid.1, Array.getElem?_eq_getElem valid.2]
  case sub a b => simp [Node.unfold, Array.getElem?_eq_getElem valid.1, Array.getElem?_eq_getElem valid.2]
  case mul a b => simp [Node.unfold, Array.getElem?_eq_getElem valid.1, Array.getElem?_eq_getElem valid.2]
  case neg a => simp [Node.unfold, Array.getElem?_eq_getElem valid]

theorem unfoldFrom_defined {nodes : List Node} {trees : Array Expr} {widths : GraphWidths} {lookupEnd : Nat}
    (valid : ValidNodes widths lookupEnd trees.size nodes) :
    ∃ result, unfoldFrom nodes trees = some result ∧ result.size = trees.size + nodes.length := by
  induction nodes generalizing trees with
  | nil => exact ⟨trees, rfl, by simp⟩
  | cons node nodes ih =>
    cases valid with
    | cons valid rest =>
      obtain ⟨expr, unfolded⟩ := Node.unfold_defined valid
      obtain ⟨result, extended, length⟩ := ih (trees := trees.push expr) (by simpa only [Array.size_push] using rest)
      refine ⟨result, ?_, ?_⟩
      · simp only [unfoldFrom, unfolded, bind, Option.bind, extended]
      · simp only [Array.size_push, List.length_cons] at length ⊢; omega

theorem unfoldFrom_reflects (ops : EvalOps W) (values : Values W) (nodes : List Node)
    {trees resultTrees : Array Expr} {buffer resultBuffer : Array W}
    (reflects : Reflects ops values trees buffer)
    (unfolded : unfoldFrom nodes trees = some resultTrees)
    (swept : sweepFrom ops values nodes buffer = some resultBuffer) :
    Reflects ops values resultTrees resultBuffer := by
  induction nodes generalizing trees buffer with
  | nil => cases unfolded; cases swept; exact reflects
  | cons node nodes ih =>
    simp only [unfoldFrom] at unfolded
    cases tree : node.unfold trees with
    | none => simp only [tree, bind, Option.bind, reduceCtorEq] at unfolded
    | some expr =>
      simp only [tree, bind, Option.bind] at unfolded
      simp only [sweepFrom] at swept
      cases evaluated : node.eval ops values buffer with
      | none => simp only [evaluated, bind, Option.bind, reduceCtorEq] at swept
      | some value =>
        simp only [evaluated, bind, Option.bind] at swept
        have exprEval : expr.eval ops values = some value :=
          (Node.unfold_eval ops values reflects node tree).symm.trans evaluated
        exact ih (reflects.push expr value exprEval) unfolded swept

theorem Graph.Valid.unfold_defined {widths : GraphWidths} {graph : Graph} (valid : graph.Valid widths) :
    ∃ trees, graph.unfold = some trees ∧ trees.size = graph.nodes.length := by
  simpa only [Graph.unfold, Array.size_empty, Nat.zero_add] using unfoldFrom_defined (trees := #[]) valid.nodes

theorem Graph.sweep_reflects (graph : Graph) (ops : EvalOps W) (values : Values W)
    {trees : Array Expr} {buffer : Array W}
    (unfolded : graph.unfold = some trees) (swept : graph.sweep ops values = some buffer) :
    Reflects ops values trees buffer :=
  unfoldFrom_reflects ops values graph.nodes ⟨rfl, fun _ => rfl⟩ unfolded swept

def readNodes (buffer : Array W) (roots : List Nat) : Option (List W) :=
  roots.mapM fun index => buffer[index]?

def evalRoots (ops : EvalOps W) (values : Values W) (trees : Array Expr) (roots : List Nat) : Option (List W) :=
  roots.mapM fun index => (trees[index]?).bind (Expr.eval ops values)

def readLookup (buffer : Array W) (lookup : Lookup) : Option (W × List W) := do
  let multiplicity ← buffer[lookup.multiplicity]?
  let args ← readNodes buffer lookup.args
  return (multiplicity, args)

def evalLookup (ops : EvalOps W) (values : Values W) (trees : Array Expr)
    (lookup : Lookup) : Option (W × List W) := do
  let multiplicity ← (trees[lookup.multiplicity]?).bind (Expr.eval ops values)
  let args ← evalRoots ops values trees lookup.args
  return (multiplicity, args)

theorem Reflects.readNodes {ops : EvalOps W} {values : Values W} {trees : Array Expr} {buffer : Array W}
    (reflects : Reflects ops values trees buffer) (roots : List Nat) :
    readNodes buffer roots = evalRoots ops values trees roots := by
  simp only [Aiur.NativeAIR.readNodes, evalRoots, reflects.2]

theorem Reflects.readLookup {ops : EvalOps W} {values : Values W} {trees : Array Expr} {buffer : Array W}
    (reflects : Reflects ops values trees buffer) (lookup : Lookup) :
    readLookup buffer lookup = evalLookup ops values trees lookup := by
  simp only [Aiur.NativeAIR.readLookup, evalLookup, reflects.2, reflects.readNodes]

theorem readNodes_congr (left right : Array W) (roots : List Nat)
    (agree : ∀ index ∈ roots, left[index]? = right[index]?) : readNodes left roots = readNodes right roots := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
    simp only [readNodes, List.mapM_cons, agree root (by simp)]
    rw [show roots.mapM (fun index => left[index]?) = roots.mapM (fun index => right[index]?) from
      ih (fun index member => agree index (by simp [member]))]

theorem readNodes_defined (buffer : Array W) (roots : List Nat)
    (bound : ∀ index ∈ roots, index < buffer.size) :
    ∃ values, readNodes buffer roots = some values ∧ values.length = roots.length := by
  induction roots with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons root roots ih =>
    obtain ⟨values, read, size⟩ := ih (fun index member => bound index (by simp [member]))
    have rootBound := bound root (by simp)
    refine ⟨buffer[root] :: values, ?_, congrArg (· + 1) size⟩
    simp only [readNodes, List.mapM_cons, Array.getElem?_eq_getElem rootBound, bind, Option.bind]
    change (readNodes buffer roots).bind (fun values => some (buffer[root] :: values)) = _
    rw [read]; rfl

theorem readLookup_defined (buffer : Array W) (lookup : Lookup)
    (bound : ∀ index ∈ lookup.roots, index < buffer.size) :
    ∃ value, readLookup buffer lookup = some value ∧ value.2.length = lookup.args.length := by
  have rootBound := bound lookup.multiplicity (by simp [Lookup.roots])
  obtain ⟨args, read, length⟩ := readNodes_defined buffer lookup.args
    (fun index member => bound index (by simp [Lookup.roots, member]))
  exact ⟨(buffer[lookup.multiplicity], args), by
    simp only [readLookup, Array.getElem?_eq_getElem rootBound, read, bind, Option.bind, pure], length⟩

theorem Graph.Valid.lookup_values_agree {widths : GraphWidths} {graph : Graph} (valid : graph.Valid widths)
    (ops : EvalOps W) (values : Values W) {full prefixValues : Array W}
    (fullSweep : graph.sweep ops values = some full)
    (partialSweep : graph.sweepLookupPrefix ops values = some prefixValues)
    (size : prefixValues.size = graph.lookupPrefix) (lookup : Lookup) (member : lookup ∈ graph.lookups) :
    readLookup full lookup = readLookup prefixValues lookup := by
  have bound : ∀ index ∈ lookup.roots, index < prefixValues.size := by
    intro index root
    rw [size]
    exact roots_below_prefix graph.lookupRoots index (List.mem_flatMap.mpr ⟨lookup, member, root⟩)
  have agree : ∀ index ∈ lookup.roots, full[index]? = prefixValues[index]? :=
    fun index root => valid.lookup_sweep_agrees ops values fullSweep partialSweep index (bound index root)
  simp only [readLookup, agree lookup.multiplicity (by simp [Lookup.roots])]
  rw [readNodes_congr full prefixValues lookup.args
    (fun index root => agree index (by simp [Lookup.roots, root]))]

theorem Graph.Valid.lookup_values_reflect {widths : GraphWidths} {graph : Graph} (valid : graph.Valid widths)
    (ops : EvalOps W) (values : Values W) {trees : Array Expr} {full prefixValues : Array W}
    (unfolded : graph.unfold = some trees)
    (fullSweep : graph.sweep ops values = some full)
    (partialSweep : graph.sweepLookupPrefix ops values = some prefixValues)
    (size : prefixValues.size = graph.lookupPrefix) (lookup : Lookup) (member : lookup ∈ graph.lookups) :
    readLookup prefixValues lookup = evalLookup ops values trees lookup :=
  (valid.lookup_values_agree ops values fullSweep partialSweep size lookup member).symm.trans
    ((graph.sweep_reflects ops values unfolded fullSweep).readLookup lookup)

def goldilocksOps : EvalOps G := ⟨id, (· + ·), (· - ·), (· * ·), (0 - ·)⟩

end Aiur.NativeAIR
