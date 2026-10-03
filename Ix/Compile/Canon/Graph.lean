/-
  Ix.Compile.Canon.Graph: the reference graph and its strongly connected
  components, as total functions.

  **Edges** (exactly today's, `Ix/GraphM.lean:47-71`, which mirrors Rust
  `get_constant_info_references`):
  * axioms, quotients: the type;
  * definitions, theorems, opaques: the type and the value;
  * inductives: the type and the constructor *names* (not the constructor
    types);
  * constructors: the type and the inductive;
  * recursors: the type, each rule's constructor and right-hand side.
  An expression references every constant it names and every projection's
  structure name (`graphExpr`); `mdata` is looked through.

  So an inductive and its constructors are one component with the other
  members of their cycle, through constructor types: the split of a Lean
  block is the components of its members and constructors.

  **Components** (`tarjan`): Tarjan's algorithm with an explicit call stack
  and fuel `|E| + |V| + 1` (each step either advances one edge or finishes
  one node, so the fuel is never exhausted; exhaustion is reported, not
  hidden). Today's `Ix/CondenseM.lean:52` is the same algorithm as a
  `partial` recursion over hash-map order; the partition into components does
  not depend on the traversal order, only the representatives do (and Pass 1
  has none: a component is the set of its members, listed in node order).
-/
module
public import Ix.Environment
public import Ix.Common
public section

namespace Ix.Compile.Canon

open Ix (Name Expr ConstantInfo)

/-! ## References -/

/-- Constants and projection structure names `e` mentions, added to `acc`;
each distinct subterm (by hash) is visited once. `Ix.graphExpr`. -/
def refsExpr (e : Expr) (acc : Std.HashSet Name := {}) : Std.HashSet Name :=
  (go e (acc, {})).1
where
  go (e : Expr) (st : Std.HashSet Name × Std.HashSet Address) :
      Std.HashSet Name × Std.HashSet Address :=
    if st.2.contains e.getHash then st
    else
      let st := (st.1, st.2.insert e.getHash)
      match e with
      | .const nm _ _ => (st.1.insert nm, st.2)
      | .app f a _ => go a (go f st)
      | .lam _ t b _ _ => go b (go t st)
      | .forallE _ t b _ _ => go b (go t st)
      | .letE _ t v b _ _ => go b (go v (go t st))
      | .proj nm _ s _ => let st := go s st; (st.1.insert nm, st.2)
      | .mdata _ x _ => go x st
      | _ => st

/-- The out-edges of a constant (`Ix.graphConst`). -/
def refsConst : ConstantInfo → Std.HashSet Name
  | .axiomInfo v => refsExpr v.cnst.type
  | .defnInfo v => refsExpr v.value (refsExpr v.cnst.type)
  | .thmInfo v => refsExpr v.value (refsExpr v.cnst.type)
  | .opaqueInfo v => refsExpr v.value (refsExpr v.cnst.type)
  | .quotInfo v => refsExpr v.cnst.type
  | .inductInfo v => v.ctors.foldl (init := refsExpr v.cnst.type) (·.insert ·)
  | .ctorInfo v => (refsExpr v.cnst.type).insert v.induct
  | .recInfo v => v.rules.foldl (init := refsExpr v.cnst.type) fun acc r =>
      refsExpr r.rhs (acc.insert r.ctor)

/-! ## Tarjan, total -/

/-- Tarjan's working state over nodes `0 … n-1`. `index[v] = 0` means not yet
visited; otherwise it is the discovery number plus one. -/
structure TarjanState where
  index : Array Nat
  low : Array Nat
  onStack : Array Bool
  stack : List Nat := []
  /-- The DFS call stack: node and the position of its next out-edge. -/
  calls : List (Nat × Nat) := []
  next : Nat := 1
  comps : Array (Array Nat) := #[]
  exhausted : Bool := false

namespace TarjanState

def visit (st : TarjanState) (v : Nat) : TarjanState :=
  { st with
    index := st.index.set! v st.next
    low := st.low.set! v st.next
    onStack := st.onStack.set! v true
    stack := v :: st.stack
    calls := (v, 0) :: st.calls
    next := st.next + 1 }

/-- Pop the component rooted at `v` off the Tarjan stack. -/
def popComponent (st : TarjanState) (v : Nat) : TarjanState :=
  let rec go : List Nat → Array Nat → Array Bool → List Nat × Array Nat × Array Bool
    | [], comp, on => ([], comp, on)
    | w :: ws, comp, on =>
      let comp := comp.push w
      let on := on.set! w false
      if w == v then (ws, comp, on) else go ws comp on
  let (stack, comp, onStack) := go st.stack #[] st.onStack
  { st with stack, onStack, comps := st.comps.push (comp.qsort (· < ·)) }

end TarjanState

/-- Run the DFS until the call stack is empty or the fuel is spent. -/
def tarjanLoop (adj : Array (Array Nat)) : Nat → TarjanState → TarjanState
  | 0, st => if st.calls.isEmpty then st else { st with exhausted := true }
  | fuel + 1, st =>
    match st.calls with
    | [] => st
    | (v, i) :: rest =>
      let succs := adj[v]?.getD #[]
      if h : i < succs.size then
        let w := succs[i]
        let st := { st with calls := (v, i + 1) :: rest }
        let iw := st.index[w]?.getD 0
        if iw == 0 then
          tarjanLoop adj fuel (st.visit w)
        else if st.onStack[w]?.getD false then
          let lv := st.low[v]?.getD 0
          tarjanLoop adj fuel { st with low := st.low.set! v (min lv iw) }
        else tarjanLoop adj fuel st
      else
        let lv := st.low[v]?.getD 0
        let iv := st.index[v]?.getD 0
        let st := { st with calls := rest }
        let st := if lv == iv then st.popComponent v else st
        let st := match rest with
          | (u, _) :: _ =>
            let lu := st.low[u]?.getD 0
            { st with low := st.low.set! u (min lu lv) }
          | [] => st
        tarjanLoop adj fuel st

/-- Strongly connected components of the graph `adj` on `0 … n-1` (with
`n = adj.size`; out-of-range successors are ignored), each sorted, in
Tarjan's completion order (successors before predecessors). `none` only if
the fuel bound were wrong. -/
def tarjan (adj : Array (Array Nat)) : Option (Array (Array Nat)) :=
  let n := adj.size
  let adj := adj.map (·.filter (· < n))
  let edges := adj.foldl (init := 0) (· + ·.size)
  let init : TarjanState :=
    { index := Array.replicate n 0, low := Array.replicate n 0,
      onStack := Array.replicate n false }
  let (st, _) := (List.range n).foldl (init := (init, edges + n + 1))
    fun (st, fuel) r =>
      if st.exhausted || st.index[r]?.getD 0 != 0 then (st, fuel)
      else
        -- the whole run takes at most |E| + |V| steps, so one budget
        -- of that size suffices for every root
        (tarjanLoop adj fuel (st.visit r), fuel)
  if st.exhausted then none else some st.comps

/-- Components of the subgraph induced on `names` by `refs`, as name arrays
(members in the order of `names`). Edges leaving `names` are dropped. -/
def sccsOf (names : Array Name) (refs : Name → Std.HashSet Name) :
    Option (Array (Array Name)) := do
  let idx : Std.HashMap Name Nat :=
    names.zipIdx.foldl (init := {}) fun m (nm, i) => m.insert nm i
  let adj := names.map fun nm =>
    ((refs nm).toArray.filterMap idx.get?).qsort (· < ·)
  let comps ← tarjan adj
  return comps.map fun c => c.map (names[·]!)

end Ix.Compile.Canon

end
