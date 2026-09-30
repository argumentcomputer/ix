/-
  Exact minimum sharing (W1): fixed-dictionary optimizer (§5).

  For a dictionary `M` (available term IDs with their Share widths),
  `dictCosts` computes `C_M(t)`, the minimum byte length of a standalone
  expression expanding to `t`, for every term in increasing ID order
  (children first). Leaves, `Prj` and `Let` add their fixed header to optimal
  children. `App`, `Lam` and `All` walk their maximal same-family spine
  `t = t₀, t₁, …, t_l` (tail `t_l` of another family) and consider every
  inline prefix length `j ∈ 1..l`:

  * Tag4 header for `j`, plus every emitted contract byte and every side
    child's optimal standalone cost along the prefix;
  * for `j < l` the prefix ends at the same-family node `t_j`, which can only
    be written as a Share (an inline tail would be merged back by the
    canonical writer), so the cut is legal only if `t_j` is available;
  * for `j = l` the natural tail is written at its optimal standalone cost.

  Whole-term sharing is another option when `t` itself is available.

  `materialize` rebuilds, for a dictionary with actual table indices, the
  byte-lexicographically least encoding among the minimum-length ones. At
  every node the competing options (Share, or inline with a different spine
  length) have distinct Tag4 headers that differ inside the header, so the
  header alone decides their byte order; children are independent,
  fixed-length parts, so choosing each child's least encoding yields the
  least concatenation.
-/
module

public import Ix.Sharing.Exact.Dag

public section

namespace Ix.Sharing.Exact

open Ixon

/-! ## Telescope structure -/

/-- Telescope family of a node. -/
inductive Family where
  | app
  | lam
  | all
  | none
  deriving BEq, Repr, Inhabited

/-- Family of a head. -/
def Head.family : Head → Family
  | .app => .app
  | .lam _ => .lam
  | .all .. => .all
  | _ => .none

/-- Next node on a telescope spine: the function of an `App`, the body of a
`Lam`/`All`. -/
@[inline] def Node.spineNext (n : Node) : Nat :=
  match n.head with
  | .app => n.child 0
  | _ => n.child 1

/-- Side child of a telescope node: the argument of an `App`, the binder type
of a `Lam`/`All`. -/
@[inline] def Node.sideChild (n : Node) : Nat :=
  match n.head with
  | .app => n.child 1
  | _ => n.child 0

/-- Bytes a telescope node emits besides its side child: the contract byte of
a `Lam`/`All` binder. -/
@[inline] def Node.sideExtra (n : Node) : Nat :=
  match n.head with
  | .app => 0
  | _ => 1

/-- Per-DAG tables shared by every dictionary evaluation. -/
structure Prep where
  dag : Dag
  family : Array Family
  /-- For a telescope node, the number of nodes in its maximal same-family
  spine (at least 1); 0 for other nodes. -/
  spineLen : Array Nat
  /-- `C_∅`: the standalone unshared length of every term. -/
  base : Array Nat
  deriving Inhabited

/-- Spine lengths, children before parents. -/
def spineLengths (dag : Dag) (family : Array Family) : Array Nat := Id.run do
  let mut len : Array Nat := Array.replicate dag.size 0
  for t in [0:dag.size] do
    let fam := family[t]!
    if fam != .none then
      let nxt := (dag.node t).spineNext
      let rest := if family[nxt]! == fam then len[nxt]! else 0
      len := len.set! t (rest + 1)
  return len

/-- Width of term `t` in a dictionary (`none` when unavailable). -/
@[inline] def widthOf (width : Array (Option Nat)) (t : Nat) : Option Nat :=
  width[t]?.getD none

/-- `C_M(t)` given `cost[c] = C_M(c)` for every `c < t`. Returns the cost and
the number of telescope spine steps taken. -/
def termCost (dag : Dag) (family : Array Family) (spineLen : Array Nat)
    (cost : Array Nat) (width : Array (Option Nat)) (t : Nat) : Nat × Nat := Id.run do
  let node := dag.node t
  let mut steps := 0
  let inl ← match family[t]! with
    | .none => pure (node.children.foldl (fun acc c => acc + cost[c]!) node.head.ownBytes)
    | _ =>
      let l := spineLen[t]!
      let mut cur := t
      let mut sides := 0
      let mut best := 0
      for j in [1:l + 1] do
        let cn := dag.node cur
        sides := sides + cn.sideExtra + cost[cn.sideChild]!
        let nxt := cn.spineNext
        if j < l then
          if let some w := widthOf width nxt then
            let cand := tag4Size j + sides + w
            if best == 0 || cand < best then best := cand
        else
          let cand := tag4Size j + sides + cost[nxt]!
          if best == 0 || cand < best then best := cand
        cur := nxt
      steps := l
      pure best
  let c := match widthOf width t with
    | some w => min inl w
    | none => inl
  return (c, steps)

/-- `C_M` for every term. Terms with `affected[t] = false` keep `init[t]`
(sound when no available term occurs inside them). Returns the costs and the
work performed (terms evaluated plus spine steps). -/
def dictCostsFrom (dag : Dag) (family : Array Family) (spineLen : Array Nat)
    (init : Array Nat) (width : Array (Option Nat)) (affected : Array Bool) :
    Array Nat × Nat := Id.run do
  let mut cost := init
  let mut work := 0
  for t in [0:dag.size] do
    if affected[t]! then
      let (c, steps) := termCost dag family spineLen cost width t
      cost := cost.set! t c
      work := work + 1 + steps
  return (cost, work)

/-- Build the per-DAG tables, including the unshared costs `C_∅`. -/
def Prep.ofDag (dag : Dag) : Prep :=
  let family := dag.nodes.map (·.head.family)
  let spineLen := spineLengths dag family
  let (base, _) := dictCostsFrom dag family spineLen (Array.replicate dag.size 0)
    (Array.replicate dag.size none) (Array.replicate dag.size true)
  { dag, family, spineLen, base }

/-- `C_M` for every term under `width`, recomputing only `affected` terms. -/
def Prep.costs (p : Prep) (width : Array (Option Nat)) (affected : Array Bool) :
    Array Nat × Nat :=
  dictCostsFrom p.dag p.family p.spineLen p.base width affected

/-- `C_M` for every term, recomputing everything. -/
def Prep.costsAll (p : Prep) (width : Array (Option Nat)) : Array Nat × Nat :=
  p.costs width (Array.replicate p.dag.size true)

/-! ## Materialization with the byte-least tie-break -/

/-- One way to write a term at the top of a standalone expression. -/
inductive Choice where
  /-- `Share(index)`. -/
  | share
  /-- The inline node of a non-telescope head. -/
  | inline
  /-- An inline telescope of `j` spine nodes; if `j` is less than the spine
  length the tail is a Share. -/
  | cut (j : Nat)
  deriving BEq, Repr, Inhabited

/-- Widths of a dictionary given by table indices. -/
def widthsOfIndex (index : Array (Option Nat)) : Array (Option Nat) :=
  index.map (·.map shareWidth)

/-- Tag4 header bytes from the production encoder. -/
def tag4Bytes (flag : UInt8) (n : Nat) : ByteArray := runPut (putTag4 ⟨flag, n.toUInt64⟩)

/-- Every legal option at `t` with its exact cost and header bytes. -/
def Prep.options (p : Prep) (cost : Array Nat) (index : Array (Option Nat)) (t : Nat) :
    Array (Choice × Nat × ByteArray) := Id.run do
  let node := p.dag.node t
  let mut opts : Array (Choice × Nat × ByteArray) := #[]
  if let some i := index[t]?.getD none then
    opts := opts.push (.share, shareWidth i, tag4Bytes Ixon.Expr.FLAG_SHARE i)
  match p.family[t]! with
  | .none =>
    let c := node.children.foldl (fun acc c => acc + cost[c]!) node.head.ownBytes
    opts := opts.push (.inline, c,
      runPut (putTag4 ⟨node.head.flag, node.head.tag4Field⟩))
  | _ =>
    let l := p.spineLen[t]!
    let mut cur := t
    let mut sides := 0
    for j in [1:l + 1] do
      let cn := p.dag.node cur
      sides := sides + cn.sideExtra + cost[cn.sideChild]!
      let nxt := cn.spineNext
      if j < l then
        if let some i := index[nxt]?.getD none then
          opts := opts.push (.cut j, tag4Size j + sides + shareWidth i,
            tag4Bytes node.head.flag j)
      else
        opts := opts.push (.cut j, tag4Size j + sides + cost[nxt]!,
          tag4Bytes node.head.flag j)
      cur := nxt
  return opts

/-- The minimum-cost option whose header is byte-least. -/
def pickOption (opts : Array (Choice × Nat × ByteArray)) : Option (Choice × Nat) :=
  let best := opts.foldl (init := none) fun best o =>
    match best with
    | none => some o
    | some b =>
      if o.2.1 < b.2.1 then some o
      else if o.2.1 == b.2.1 && compareBytes o.2.2 b.2.2 == .lt then some o
      else best
  best.map fun o => (o.1, o.2.1)

/-- Materialization state: built standalone expressions and work. -/
structure MatState where
  memo : Std.HashMap Nat Ixon.Expr := {}
  nodes : Nat := 0
  deriving Inhabited

abbrev MatM := StateT MatState (Except SharingError)

/-- Build the chosen encoding of `t`. `fuel` bounds the recursion depth; every
recursive call descends to a strictly smaller term ID, so `dag.size + 1`
suffices. -/
def Prep.build (p : Prep) (cost : Array Nat) (index : Array (Option Nat))
    (limits : Limits) : Nat → Nat → MatM Ixon.Expr
  | 0, _ => throw (.internal "materialization fuel exhausted")
  | fuel + 1, t => do
    if let some e := (← get).memo.get? t then return e
    let some (choice, c) := pickOption (p.options cost index t)
      | throw (.internal s!"no option for term {t}")
    unless c == cost[t]! do
      throw (.internal s!"option cost {c} differs from C_M = {cost[t]!} at term {t}")
    let node := p.dag.node t
    let e ← match choice with
      | .share =>
        match index[t]?.getD none with
        | some i => pure (Ixon.Expr.share i.toUInt64)
        | none => throw (.internal "share choice without index")
      | .inline =>
        match node.head with
        | .prj ti f => do
          let v ← p.build cost index limits fuel (node.child 0)
          pure (Ixon.Expr.prj ti f v)
        | .letE lc => do
          let ty ← p.build cost index limits fuel (node.child 0)
          let v ← p.build cost index limits fuel (node.child 1)
          let b ← p.build cost index limits fuel (node.child 2)
          pure (Ixon.Expr.letE lc ty v b)
        | _ => pure (node.toExpr fun _ => default)
      | .cut j => do
        let l := p.spineLen[t]!
        let mut cur := t
        let mut spine : Array Node := #[]
        for _ in [0:j] do
          let cn := p.dag.node cur
          spine := spine.push cn
          cur := cn.spineNext
        let mut acc ← if j < l then
            match index[cur]?.getD none with
            | some i => pure (Ixon.Expr.share i.toUInt64)
            | none => throw (.internal "telescope cut at unavailable term")
          else p.build cost index limits fuel cur
        for k in [0:j] do
          let sn := spine[j - 1 - k]!
          let side ← p.build cost index limits fuel sn.sideChild
          acc := match sn.head with
            | .app => .app acc side
            | .lam bc => .lam bc side acc
            | .all bc r => .all bc r side acc
            | _ => acc
        pure acc
    let s ← get
    let nodes := s.nodes + 1
    if nodes > limits.maxMaterialize then
      throw (.resourceExhausted .materialize limits.maxMaterialize)
    set { s with memo := s.memo.insert t e, nodes }
    return e

/-- Materialize the byte-least minimum-length standalone encodings of
`targets` under the dictionary `index` (term ID ↦ table index). Returns the
expressions, the costs `C_M` used, and the work performed. -/
def Prep.materialize (p : Prep) (index : Array (Option Nat)) (targets : Array Nat)
    (limits : Limits) : Except SharingError (Array Ixon.Expr × Array Nat × Nat) := do
  for i in index do
    if let some i := i then
      if i ≥ wordBound then throw (.formatBound "share index" i)
  let (cost, work) := p.costsAll (widthsOfIndex index)
  let (out, st) ← (targets.mapM fun t => p.build cost index limits (p.dag.size + 1) t).run {}
  return (out, cost, work + st.nodes)

/-- A dictionary index from `(term, table index)` pairs. -/
def indexOfPairs (size : Nat) (pairs : List (Nat × Nat)) : Array (Option Nat) :=
  pairs.foldl (fun acc (t, i) => acc.set! t (some i)) (Array.replicate size none)

/-- The dictionary of the first `k` entries of a table sequence. -/
def indexOfPrefix (size : Nat) (table : Array Nat) (k : Nat) : Array (Option Nat) :=
  indexOfPairs size ((table.toList.take k).zipIdx)

end Ix.Sharing.Exact

end
