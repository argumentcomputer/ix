/-
  Exact minimum sharing (W1): fixed-dictionary optimizer (§5).

  For a dictionary `M` (available term IDs with their Share widths),
  `Prep.eval` computes `C_M(t)`, the minimum byte length of a standalone
  expression expanding to `t`, for every term in increasing ID order
  (children first). Leaves, `Prj` and `Let` add their fixed header to optimal
  children. `App`, `Lam` and `All` have a maximal same-family spine
  `t = t₀, t₁, …, t_{l-1}` with natural tail `t_l` of another family, and every
  inline prefix length `j ∈ 1..l` is a candidate:

  * Tag4 header for `j`, plus every emitted contract byte and every side
    child's optimal standalone cost along the prefix;
  * for `j < l` the prefix ends at the same-family node `t_j`, which can only
    be written as a Share (an inline tail would be merged back by the
    canonical writer), so the cut is legal only if `t_j` is available;
  * for `j = l` the natural tail is written at its optimal standalone cost.

  Whole-term sharing is another option when `t` itself is available.

  Evaluation is O(1 + number of available spine descendants) per term: the
  per-dictionary suffix sum `sides[t]` of spine bytes gives every prefix sum
  as `sides[t] - sides[t_j]`, and `below[t]` links each telescope node to its
  nearest available spine descendant, so only legal cuts are visited. This is
  the same recurrence as a walk over all `j` (the tests compare it with that
  walk and with exhaustive enumeration).

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

/-- One dictionary evaluation. `cost[t] = C_M(t)`. For a telescope node `t`,
`sides[t]` is the byte sum of the contract bytes and side-child costs along
its maximal spine, and `below[t]` is the nearest available node strictly
below `t` on that spine. Non-telescope nodes have `sides = 0`,
`below = none`. -/
structure DictEval where
  cost : Array Nat
  sides : Array Nat
  below : Array (Option Nat)
  /-- Terms evaluated plus available spine descendants visited. -/
  work : Nat := 0
  deriving Inhabited

/-- Per-DAG tables shared by every dictionary evaluation. -/
structure Prep where
  dag : Dag
  family : Array Family
  /-- For a telescope node, the number of nodes in its maximal same-family
  spine (at least 1); 0 for other nodes. -/
  spineLen : Array Nat
  /-- For a telescope node, the natural tail below its maximal spine. -/
  tail : Array Nat
  /-- Evaluation under the empty dictionary (`empty.cost = C_∅`). -/
  empty : DictEval
  deriving Inhabited

/-- `C_∅`: the standalone unshared length of every term. -/
@[inline] def Prep.base (p : Prep) : Array Nat := p.empty.cost

/-- Spine lengths and natural tails, children before parents. -/
def spineTables (dag : Dag) (family : Array Family) : Array Nat × Array Nat := Id.run do
  let mut len : Array Nat := Array.replicate dag.size 0
  let mut tail : Array Nat := Array.replicate dag.size 0
  for t in [0:dag.size] do
    let fam := family[t]!
    if fam != .none then
      let nxt := (dag.node t).spineNext
      if family[nxt]! == fam then
        len := len.set! t (len[nxt]! + 1)
        tail := tail.set! t tail[nxt]!
      else
        len := len.set! t 1
        tail := tail.set! t nxt
  return (len, tail)

/-- Width of term `t` in a dictionary (`none` when unavailable). -/
@[inline] def widthOf (width : Array (Option Nat)) (t : Nat) : Option Nat :=
  width[t]?.getD none

/-- Evaluate a dictionary. Terms with `affected[t] = false` keep their `init`
entries (sound when no available term occurs inside them, since then their
cost, spine sums and descendant links are those of the empty dictionary). -/
def evalFrom (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (init : DictEval) (width : Array (Option Nat)) (affected : Array Bool) :
    DictEval := Id.run do
  let mut cost := init.cost
  let mut sides := init.sides
  let mut below := init.below
  let mut work := 0
  for t in [0:dag.size] do
    if affected[t]! then
      let node := dag.node t
      let fam := family[t]!
      let mut inl := 0
      if fam == .none then
        inl := node.children.foldl (fun acc c => acc + cost[c]!) node.head.ownBytes
      else
        let nxt := node.spineNext
        let same := family[nxt]! == fam
        let s := node.sideExtra + cost[node.sideChild]! + (if same then sides[nxt]! else 0)
        let bl : Option Nat :=
          if same then (if (widthOf width nxt).isSome then some nxt else below[nxt]!)
          else none
        sides := sides.set! t s
        below := below.set! t bl
        let l := spineLen[t]!
        -- Natural end: all `l` spine nodes inline, then the tail.
        let mut best := tag4Size l + s + cost[tail[t]!]!
        -- Internal cuts: only at available spine descendants.
        let mut cur := bl
        for _ in [0:l] do
          match cur with
          | none => break
          | some u =>
            work := work + 1
            let cand := tag4Size (l - spineLen[u]!) + (s - sides[u]!) +
              (widthOf width u).getD 0
            if cand < best then best := cand
            cur := below[u]!
        inl := best
      let c := match widthOf width t with
        | some w => min inl w
        | none => inl
      cost := cost.set! t c
      work := work + 1
  return { cost, sides, below, work }

/-- Build the per-DAG tables, including the empty-dictionary evaluation. -/
def Prep.ofDag (dag : Dag) : Prep :=
  let family := dag.nodes.map (·.head.family)
  let (spineLen, tail) := spineTables dag family
  let n := dag.size
  let zero : DictEval :=
    { cost := Array.replicate n 0, sides := Array.replicate n 0,
      below := Array.replicate n none }
  let empty := evalFrom dag family spineLen tail zero (Array.replicate n none)
    (Array.replicate n true)
  { dag, family, spineLen, tail, empty := { empty with work := 0 } }

/-- Evaluate `width`, recomputing only `affected` terms. -/
def Prep.eval (p : Prep) (width : Array (Option Nat)) (affected : Array Bool) : DictEval :=
  evalFrom p.dag p.family p.spineLen p.tail p.empty width affected

/-- Evaluate `width`, recomputing every term. -/
def Prep.evalAll (p : Prep) (width : Array (Option Nat)) : DictEval :=
  p.eval width (Array.replicate p.dag.size true)

/-- `C_M` for every term under `width` (recomputing `affected` terms) and the
work performed. -/
def Prep.costs (p : Prep) (width : Array (Option Nat)) (affected : Array Bool) :
    Array Nat × Nat :=
  let ev := p.eval width affected
  (ev.cost, ev.work)

/-- `C_M` for every term, recomputing everything. -/
def Prep.costsAll (p : Prep) (width : Array (Option Nat)) : Array Nat × Nat :=
  let ev := p.evalAll width
  (ev.cost, ev.work)

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

/-- Every legal option at `t` with its exact cost and header bytes, given the
evaluation `ev` of the dictionary with Share widths `width`; headers use the
actual table indices `index`. -/
def Prep.options (p : Prep) (ev : DictEval) (index : Array (Option Nat))
    (width : Array (Option Nat)) (t : Nat) :
    Array (Choice × Nat × ByteArray) := Id.run do
  let node := p.dag.node t
  let mut opts : Array (Choice × Nat × ByteArray) := #[]
  if let some i := index[t]?.getD none then
    opts := opts.push (.share, (widthOf width t).getD 0, tag4Bytes Ixon.Expr.FLAG_SHARE i)
  if p.family[t]! == .none then
    let c := node.children.foldl (fun acc c => acc + ev.cost[c]!) node.head.ownBytes
    opts := opts.push (.inline, c, runPut (putTag4 ⟨node.head.flag, node.head.tag4Field⟩))
  else
    let l := p.spineLen[t]!
    let s := ev.sides[t]!
    opts := opts.push (.cut l, tag4Size l + s + ev.cost[p.tail[t]!]!, tag4Bytes node.head.flag l)
    let mut cur := ev.below[t]!
    for _ in [0:l] do
      match cur with
      | none => break
      | some u =>
        let j := l - p.spineLen[u]!
        if (index[u]?.getD none).isSome then
          opts := opts.push (.cut j, tag4Size j + (s - ev.sides[u]!) + (widthOf width u).getD 0,
            tag4Bytes node.head.flag j)
        cur := ev.below[u]!
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

/-- The first `j` nodes of the telescope spine from `t`, outermost first,
and the term after them. -/
def Prep.spineWalk (p : Prep) : Nat → Nat → List Node × Nat
  | 0, t => ([], t)
  | j + 1, t =>
    let n := p.dag.node t
    let (ns, e) := p.spineWalk j n.spineNext
    (n :: ns, e)

/-- Rebuild one telescope node around its rebuilt continuation (`inner`)
and side child. -/
def rebuildSpineNode (n : Node) (inner side : Ixon.Expr) : Except SharingError Ixon.Expr :=
  match n.head with
  | .app => .ok (.app inner side)
  | .lam bc => .ok (.lam bc side inner)
  | .all bc r => .ok (.all bc r side inner)
  | _ => .error (.internal "spine node is not a telescope node")

/-- Build the chosen encoding of `t`. With `entry = true` the top may not be
`Share(t)` (the body of `t`'s own table entry); nested terms always use
their standalone choice. Pure and structurally recursive on `fuel`; every
recursive call descends to a strictly smaller term ID, so `dag.size + 1`
suffices. Each call emits one node of the output, so the work is bounded
by the output size. Every inconsistency is an internal error. -/
def Prep.build (p : Prep) (ev : DictEval) (index width : Array (Option Nat)) :
    Bool → Nat → Nat → Except SharingError Ixon.Expr
  | _, 0, _ => throw (.internal "materialization fuel exhausted")
  | entry, fuel + 1, t => do
    let opts := p.options ev index width t
    let opts := if entry then opts.filter (·.1 != .share) else opts
    let some (choice, c) := pickOption opts
      | throw (.internal s!"no option for term {t}")
    unless entry || c == ev.cost[t]! do
      throw (.internal s!"option cost {c} differs from C_M = {ev.cost[t]!} at term {t}")
    let node := p.dag.node t
    match choice with
    | .share =>
      match index[t]?.getD none with
      | some i => pure (Ixon.Expr.share i.toUInt64)
      | none => throw (.internal "share choice without index")
    | .inline =>
      match node.head with
      | .prj ti f => do
        let v ← p.build ev index width false fuel (node.child 0)
        pure (Ixon.Expr.prj ti f v)
      | .letE lc => do
        let ty ← p.build ev index width false fuel (node.child 0)
        let v ← p.build ev index width false fuel (node.child 1)
        let b ← p.build ev index width false fuel (node.child 2)
        pure (Ixon.Expr.letE lc ty v b)
      | .app | .lam _ | .all .. => throw (.internal "inline choice at a telescope head")
      | _ => pure (node.toExpr fun _ => default)
    | .cut j => do
      let (spine, cur) := p.spineWalk j t
      let tail ← if j < p.spineLen[t]! then
          match index[cur]?.getD none with
          | some i => pure (Ixon.Expr.share i.toUInt64)
          | none => throw (.internal "telescope cut at unavailable term")
        else p.build ev index width false fuel cur
      spine.foldrM (fun n acc => do
        let side ← p.build ev index width false fuel n.sideChild
        rebuildSpineNode n acc side) tail

/-- Materialize the byte-least minimum-cost standalone encodings of `targets`
under the dictionary `index` (term ID ↦ table index), pricing each Share by
`width` (which must be `some` exactly where `index` is). The predicted
output size, which bounds the nodes built, is checked against
`maxMaterialize` first. Returns the expressions, the costs used, and the
work performed. -/
def Prep.materializeWith (p : Prep) (index width : Array (Option Nat)) (targets : Array Nat)
    (limits : Limits) : Except SharingError (Array Ixon.Expr × Array Nat × Nat) := do
  for i in index do
    if let some i := i then
      if i ≥ wordBound then throw (.formatBound "share index" i)
  let ev := p.evalAll width
  let total := targets.foldl (fun acc t => acc + ev.cost[t]!) 0
  if total > limits.maxMaterialize then
    throw (.resourceExhausted .materialize limits.maxMaterialize)
  let out ← targets.mapM fun t => p.build ev index width false (p.dag.size + 1) t
  return (out, ev.cost, ev.work + total)

/-- Materialize the byte-least minimum-length standalone encodings of
`targets` under the dictionary `index` (term ID ↦ table index), with the
real Share widths. Returns the expressions, the costs `C_M` used, and the
work performed. -/
def Prep.materialize (p : Prep) (index : Array (Option Nat)) (targets : Array Nat)
    (limits : Limits) : Except SharingError (Array Ixon.Expr × Array Nat × Nat) :=
  p.materializeWith index (widthsOfIndex index) targets limits

/-- A dictionary index from `(term, table index)` pairs. -/
def indexOfPairs (size : Nat) (pairs : List (Nat × Nat)) : Array (Option Nat) :=
  pairs.foldl (fun acc (t, i) => acc.set! t (some i)) (Array.replicate size none)

/-- The dictionary of the first `k` entries of a table sequence. -/
def indexOfPrefix (size : Nat) (table : Array Nat) (k : Nat) : Array (Option Nat) :=
  indexOfPairs size ((table.toList.take k).zipIdx)

/-- Minimum cost of `t` written with an inline top (the body of its own table
entry) under the evaluation `ev`. -/
def Prep.inlineCost (p : Prep) (ev : DictEval) (index width : Array (Option Nat)) (t : Nat) :
    Nat :=
  ((pickOption ((p.options ev index width t).filter (·.1 != .share))).map (·.2)).getD 0

/-- Materialize a table given in dependency order (every stored descendant of
an entry precedes it) and the roots, from one evaluation of the whole
dictionary. In such an order the entry for `t` can use every stored term
that can occur inside `t`, and no other stored term can occur there, so the
full dictionary prices and builds its body exactly. Shares are priced by
`width` (`some` exactly on the table's terms). Returns entries, roots, the
total variable cost (table count, entry bodies, roots) and the work. The
caller must re-expand the output: a table that is not in dependency order
is rejected there as a non-backward reference. -/
def Prep.materializeDependent (p : Prep) (table roots : Array Nat)
    (width : Array (Option Nat)) (limits : Limits) :
    Except SharingError (Array Ixon.Expr × Array Ixon.Expr × Nat × Nat) := do
  if table.size ≥ wordBound then throw (.formatBound "share index" table.size)
  let index := indexOfPairs p.dag.size table.toList.zipIdx
  let ev := p.evalAll width
  let entryCost := table.foldl (fun acc t => acc + p.inlineCost ev index width t) 0
  let rootCost := roots.foldl (fun acc r => acc + ev.cost[r]!) 0
  let total := tag0Size table.size + entryCost + rootCost
  if total > limits.maxMaterialize then
    throw (.resourceExhausted .materialize limits.maxMaterialize)
  let es ← table.mapM fun t => p.build ev index width true (p.dag.size + 1) t
  let rs ← roots.mapM fun r => p.build ev index width false (p.dag.size + 1) r
  return (es, rs, total, ev.work + total)

end Ix.Sharing.Exact

end
