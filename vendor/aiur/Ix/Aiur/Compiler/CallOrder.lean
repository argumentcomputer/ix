module
public import Ix.Aiur.Compiler.Layout
public import Ix.Aiur.Compiler.UnitCounter

public section
@[expose] section
namespace Aiur

/-- Termination helper for the `Block`/`Ctrl` traversal below. -/
private theorem Bytecode.Block.sizeOf_ctrl_lt'' (b : Bytecode.Block) :
    sizeOf b.ctrl < sizeOf b := by
  rcases b with ⟨ops, ctrl⟩
  show sizeOf ctrl < 1 + sizeOf ops + sizeOf ctrl
  omega

mutual
/-- Collect all callee `FunIdx` values from constrained `Op.call` nodes in a
block tree. Unconstrained calls are skipped because cascading into unconstrained
mode removes the need for the callee's own circuit. -/
def Bytecode.Ctrl.collectConstrainedCallees (c : Bytecode.Ctrl) :
    Array Bytecode.FunIdx := match c with
  | .match _ cases default? =>
    let branchCallees := cases.attach.foldl (init := #[]) fun acc ⟨(_, block), _⟩ =>
      acc ++ block.collectConstrainedCallees
    match default? with
    | some block => branchCallees ++ block.collectConstrainedCallees
    | none => branchCallees
  | .matchContinue _ cases default? _ _ _ continuation =>
    let branchCallees := cases.attach.foldl (init := #[]) fun acc ⟨(_, block), _⟩ =>
      acc ++ block.collectConstrainedCallees
    let withDefault := match default? with
      | some block => branchCallees ++ block.collectConstrainedCallees
      | none => branchCallees
    withDefault ++ continuation.collectConstrainedCallees
  | .return _ _ | .yield _ _ => #[]
termination_by (sizeOf c, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind

def Bytecode.Block.collectConstrainedCallees (b : Bytecode.Block) :
    Array Bytecode.FunIdx :=
  let opCallees := b.ops.foldl (init := #[]) fun acc op =>
    match op with
    | .call idx _ _ false => acc.push idx
    | _ => acc
  opCallees ++ b.ctrl.collectConstrainedCallees
termination_by (sizeOf b, 1)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.left; exact Bytecode.Block.sizeOf_ctrl_lt'' _)
end

namespace Bytecode

/-- Every cross-component edge advances the static order. An internal edge
must retain the existing dynamic rank relation at both endpoints. Counter
self-edges are checked separately against their bytecode. -/
def CallComponent.permits (parent child : CallComponent) : Bool :=
  parent.order < child.order ||
    (parent.order == child.order && parent.ranked && child.ranked)

/-- The accepted call relation is well founded once every row has a bounded
component order and rank, and same-component calls strictly increase rank.
Cross-component calls need no comparison between their endpoint ranks.

This is the order argument used by the specialization, independent of how
the candidate components are produced. Relating AIR lookups to these row
premises still requires activity, exact lookup balance, and rank-limb bounds. -/
theorem CallComponent.wellFounded_calls {α : Type} (component : α → CallComponent)
    (rank : α → Nat) (componentCount rankBound : Nat)
    (hc : ∀ row, (component row).order < componentCount)
    (hr : ∀ row, rank row < rankBound) :
    WellFounded (fun child parent =>
      (component parent).permits (component child) = true ∧
      ((component parent).order = (component child).order → rank parent < rank child)) := by
  let measure := fun row => (componentCount - (component row).order, rankBound - rank row)
  apply Subrelation.wf (r := InvImage (Prod.Lex Nat.lt Nat.lt) measure)
  · intro child parent h
    rcases h with ⟨horder, hrank⟩
    simp only [CallComponent.permits, Bool.or_eq_true, decide_eq_true_eq,
      Bool.and_eq_true, beq_iff_eq] at horder
    rcases horder with horder | ⟨⟨horder, _⟩, _⟩
    · apply Prod.Lex.left
      have := hc child
      change componentCount - (component child).order < componentCount - (component parent).order
      omega
    · have h := hrank horder
      have := hr child
      change Prod.Lex Nat.lt Nat.lt
        (componentCount - (component child).order, rankBound - rank child)
        (componentCount - (component parent).order, rankBound - rank parent)
      rw [horder]
      apply Prod.Lex.right
      change rankBound - rank child < rankBound - rank parent
      omega
  · exact InvImage.wf measure (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- A candidate certificate is checked independently of the SCC algorithm.
The native constructor repeats this check before using it to omit constraints. -/
def Toplevel.validCallComponents (t : Toplevel) : Bool :=
  t.callComponents.size == t.functions.size &&
  t.callComponents.all (fun c => c.order < t.functions.size) &&
  (t.functions.mapIdx fun i f => !f.constrained ||
    f.body.collectConstrainedCallees.all (fun j =>
      match t.callComponents[i]?, t.callComponents[j]? with
      | some parent, some child => parent.permits child ||
        (i == j && !parent.ranked && (UnitCounter.find? i f).isSome)
      | _, _ => false)).all id

def callOrderFinishDfs (graph : Array (Array Nat)) :
    Nat → Nat → (Array Bool × Array Nat) → (Array Bool × Array Nat)
  | 0, _, state => state
  | fuel + 1, node, state =>
    if state.1[node]! then state else
      let state := (state.1.set! node true, state.2)
      let state := graph[node]!.foldl
        (fun state child => callOrderFinishDfs graph fuel child state) state
      (state.1, state.2.push node)

def callOrderComponentDfs (graph : Array (Array Nat)) (component : Nat) :
    Nat → Nat → Array Nat → Array Nat
  | 0, _, labels => labels
  | fuel + 1, node, labels =>
    if labels[node]! < graph.size then labels else
      graph[node]!.foldl
        (fun labels child => callOrderComponentDfs graph component fuel child labels)
        (labels.set! node component)

/-- Kosaraju traversal with an explicit depth bound. Graph construction uses
only constrained call edges of constrained functions. The result is checked
before it can affect a compiled layout, so correctness of this producer is
not a premise for omitting rank constraints. -/
def Toplevel.findCallComponents (t : Toplevel) : Array CallComponent := Id.run do
  let n := t.functions.size
  let graph := t.functions.map fun f =>
    if f.constrained then f.body.collectConstrainedCallees else #[]
  let mut reverse := Array.replicate n #[]
  for i in [:n] do
    for j in graph[i]! do
      reverse := reverse.set! j (reverse[j]!.push i)
  let mut visited := (Array.replicate n false, (#[] : Array Nat))
  for i in [:n] do
    visited := callOrderFinishDfs graph n i visited
  let mut labels := Array.replicate n n
  let mut count := 0
  for i in visited.2.reverse do
    if labels[i]! == n then
      labels := callOrderComponentDfs reverse count n i labels
      count := count + 1
  let mut sizes := Array.replicate count 0
  for label in labels do
    sizes := sizes.set! label (sizes[label]! + 1)
  return labels.mapIdx fun i label =>
    { order := label, ranked := sizes[label]! > 1 || graph[i]!.contains i }

/-- Native and compiler layout selection agree on these three cases. -/
def Toplevel.callRanksFor (t : Toplevel) (parent : Nat) : Array CallRank :=
  t.callComponents.map fun child =>
    if !child.ranked then .zero
    else if t.callComponents[parent]!.order == child.order then .ordered
    else .bound

/-- Recompute every function and continuation layout after selecting ranks.
Run before constructing the circuit partition. The instruction stream,
value indices and function indices are preserved. -/
def Toplevel.withCallComponents (t : Toplevel) (useCounters : Bool := false) : Toplevel :=
  let components := t.findCallComponents
  let callComponents := if useCounters then components.mapIdx fun i component =>
    if component.ranked &&
        (components.filter (·.order == component.order)).size == 1 &&
        (UnitCounter.find? i t.functions[i]!).isSome then
      { component with ranked := false }
    else component
    else components
  let candidate := { t with callComponents }
  if !candidate.validCallComponents then t else
    let functions := t.functions.mapIdx fun i function =>
      let initial := Concrete.Bytecode.LayoutMState.withCallRanks
        function.layout.inputSize callComponents[i]!.ranked (candidate.callRanksFor i)
      let (body, state) := Concrete.Bytecode.relayoutBlock function.body |>.run initial
      { function with body, layout := { state.functionLayout with
          lookups := state.functionLayout.lookups + 1 } }
    { candidate with functions }

end Bytecode

end Aiur
end
end
