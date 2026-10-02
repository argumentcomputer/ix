/-
  Exact minimum sharing: expanded structural DAG.

  * `ingestTable` expands an existing sharing table and its roots into a
    hash-consed DAG without materializing the occurrence tree. Entry `i` may
    refer only to entries `< i` (the backward-reference class of
    `Ix.Compile.Verify.ExprTableWF`); forward/self references, out-of-range
    indices, excessive depth and excessive work are reported as errors.
  * `canonicalize` keeps the subterms reachable from the roots and assigns
    the §3.2 structural IDs: increasing height, then the
    `(tag, scalars, child IDs)` key order. Children always have smaller IDs.
  * `occurrences` counts logical occurrences through every DAG edge.
  * `constantInfoRoots` / `withRoots` extract and reassemble the ordered
    expression roots of a `ConstantInfo`, mirroring
    `Ix.CompileM.constantInfoRootExprs` (checked equal in the tests), with an
    exact root-count check instead of out-of-range fallbacks.

  Structural equality is decided by `Node` keys (`BEq`), never by a hash
  alone; the pointer cache only skips re-walking the same live object.
-/
module

public import Ix.Sharing.Exact.Basic

public section

namespace Ix.Sharing.Exact

open Ixon

/-! ## Hash-consing interner -/

/-- Hash-consed nodes. Children are interned before their parent, so every
child ID is smaller than its parent's ID. -/
structure Interner where
  nodes : Array Node := #[]
  index : Std.HashMap Node Nat := {}
  deriving Inhabited

/-- Return the ID of `n`, adding it if it is new. Lookup is by the full
structural key. -/
def Interner.intern (s : Interner) (n : Node) : Interner × Nat :=
  match s.index.get? n with
  | some i => (s, i)
  | none =>
    let i := s.nodes.size
    ({ nodes := s.nodes.push n, index := s.index.insert n i }, i)

/-- An interner whose IDs are exactly the given nodes' positions. -/
def Interner.ofNodes (nodes : Array Node) : Interner :=
  { nodes, index := nodes.zipIdx.foldl (fun m (n, i) => m.insert n i) {} }

/-- State of one expansion pass. -/
structure IngestState where
  interner : Interner := {}
  /-- Live input object address ↦ term ID. Every object walked in one pass
  was allocated before the pass and is alive while walked, so two walked
  objects with the same address are the same object. -/
  ptrCache : Std.HashMap USize Nat := {}
  visits : Nat := 0
  deriving Inhabited

abbrev IngestM := StateT IngestState (Except SharingError)

@[inline] def liftExcept {α} (x : Except SharingError α) : IngestM α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

/-- How `Share` leaves resolve during one walk. -/
structure ShareCtx where
  /-- Term IDs of the entries this walk may reference (a strict prefix of
  the table for an entry, the whole table for a root). -/
  resolved : Array Nat
  tableSize : Nat
  /-- The entry being expanded, or `none` for a root. -/
  entry : Option Nat
  /-- Index of the root being walked (error reporting). -/
  root : Nat
  /-- `false` when the input must already be expanded. -/
  allowShare : Bool

/-- Resolve `Share(j)` in context. -/
def resolveShare (ctx : ShareCtx) (j : UInt64) : Except SharingError Nat :=
  if !ctx.allowShare then .error (.shareInExpandedInput ctx.root j)
  else match ctx.resolved[j.toNat]? with
    | some id => .ok id
    | none =>
      match ctx.entry with
      | some i =>
        if j.toNat < ctx.tableSize then .error (.nonBackwardShare i j)
        else .error (.shareOutOfRange (some i) j ctx.tableSize)
      | none => .error (.shareOutOfRange none j ctx.tableSize)

/-- Intern one node, enforcing the node limit. -/
def internNode (limits : Limits) (n : Node) : IngestM Nat := do
  let s ← get
  let (interner, id) := s.interner.intern n
  if interner.nodes.size > limits.maxNodes then
    throw (.resourceExhausted .nodes limits.maxNodes)
  set { s with interner }
  return id

/-- Expand one expression into the interner and return its term ID. -/
def ingestExpr (limits : Limits) (ctx : ShareCtx) (depth : Nat) (e : Ixon.Expr) :
    IngestM Nat := do
  let ptr := exprPtr e
  match (← get).ptrCache.get? ptr with
  | some id => return id
  | none =>
    if depth > limits.maxDepth then
      throw (.resourceExhausted .depth limits.maxDepth)
    let s ← get
    let visits ← liftExcept (bump s.visits 1 limits.maxExprVisits .exprVisits)
    set { s with visits }
    let id ← match e with
      | .sort i => internNode limits ⟨.sort i, #[]⟩
      | .var i => internNode limits ⟨.var i, #[]⟩
      | .ref r us => internNode limits ⟨.ref r us, #[]⟩
      | .recur r us => internNode limits ⟨.recur r us, #[]⟩
      | .prj t f v => do
        let vi ← ingestExpr limits ctx (depth + 1) v
        internNode limits ⟨.prj t f, #[vi]⟩
      | .str i => internNode limits ⟨.str i, #[]⟩
      | .nat i => internNode limits ⟨.nat i, #[]⟩
      | .app f a => do
        let fi ← ingestExpr limits ctx (depth + 1) f
        let ai ← ingestExpr limits ctx (depth + 1) a
        internNode limits ⟨.app, #[fi, ai]⟩
      | .lam c ty body => do
        let ti ← ingestExpr limits ctx (depth + 1) ty
        let bi ← ingestExpr limits ctx (depth + 1) body
        internNode limits ⟨.lam c, #[ti, bi]⟩
      | .all c r ty body => do
        let ti ← ingestExpr limits ctx (depth + 1) ty
        let bi ← ingestExpr limits ctx (depth + 1) body
        internNode limits ⟨.all c r, #[ti, bi]⟩
      | .letE c ty v body => do
        let ti ← ingestExpr limits ctx (depth + 1) ty
        let vi ← ingestExpr limits ctx (depth + 1) v
        let bi ← ingestExpr limits ctx (depth + 1) body
        internNode limits ⟨.letE c, #[ti, vi, bi]⟩
      | .share j => liftExcept (resolveShare ctx j)
    modify fun s => { s with ptrCache := s.ptrCache.insert ptr id }
    return id

/-- Expand a sharing table and then the roots. Entry `i` is expanded
against entries `0..i-1` only; roots may use the whole table. Returns the
root term IDs. With `allowShare = false` the table must be empty and any
`Share` is an error. Returns the entry term IDs and the root term IDs. -/
def ingestTable (limits : Limits) (sharing roots : Array Ixon.Expr)
    (allowShare : Bool) : IngestM (Array Nat × Array Nat) := do
  if sharing.size ≥ wordBound then
    throw (.formatBound "sharing table size" sharing.size)
  let mut resolved : Array Nat := #[]
  for h : i in [0:sharing.size] do
    let ctx : ShareCtx :=
      { resolved, tableSize := sharing.size, entry := some i, root := 0, allowShare }
    let id ← ingestExpr limits ctx 0 sharing[i]
    resolved := resolved.push id
  let mut out : Array Nat := #[]
  for h : r in [0:roots.size] do
    let ctx : ShareCtx :=
      { resolved, tableSize := sharing.size, entry := none, root := r, allowShare }
    let id ← ingestExpr limits ctx 0 roots[r]
    out := out.push id
  return (resolved, out)

/-! ## Canonical structural IDs (§3.2) -/

/-- The canonical DAG: `nodes[i]` is the node with structural ID `i`; every
child ID is smaller than its parent's ID. -/
structure Dag where
  nodes : Array Node := #[]
  deriving Inhabited, Repr, BEq

/-- Number of distinct subterms. -/
@[inline] def Dag.size (d : Dag) : Nat := d.nodes.size

/-- Node with the given ID (default for an out-of-range ID). -/
@[inline] def Dag.node (d : Dag) (t : Nat) : Node := d.nodes[t]?.getD default

/-- Heights of the given nodes, which must have children before parents. -/
def nodeHeights (nodes : Array Node) : Array Nat :=
  (List.range nodes.size).foldl (fun height t =>
      height.set! t (nodes[t]!.children.foldl (fun acc c => max acc (height[c]! + 1)) 0))
    (Array.replicate nodes.size 0)

/-- Check that every child ID is smaller than its parent's ID. -/
def childrenPrecede (nodes : Array Node) : Bool :=
  nodes.zipIdx.all fun (n, t) => n.children.all (· < t)

/-- Mark the nodes reachable from `roots`: the roots, then the children of
every marked node, visiting parents before children (descending IDs, as
children precede parents). -/
def reachMarks (temp : Array Node) (roots : Array Nat) : Array Bool :=
  (List.range temp.size).foldr
    (fun t reach =>
      if reach[t]! then temp[t]!.children.foldl (fun r c => r.set! c true) reach else reach)
    (roots.foldl (fun r t => r.set! t true) (Array.replicate temp.size false))

/-- The marked nodes grouped by height, each group in increasing ID order. -/
def heightBuckets (reach : Array Bool) (height : Array Nat) (maxH n : Nat) :
    Array (Array Nat) :=
  (List.range n).foldl
    (fun buckets t => if reach[t]! then buckets.modify height[t]! (·.push t) else buckets)
    (Array.replicate (maxH + 1) #[])

/-- Assign the next IDs to a key-sorted group, checking that the keys
strictly increase. -/
def placeSorted : List (Nat × Node) → Option Node → Array Nat × Array Node →
    Except SharingError (Array Nat × Array Node)
  | [], _, st => pure st
  | (t, node) :: rest, prev, (canon, out) => do
    if let some p := prev then
      unless Node.compareKey p node == .lt do
        throw (.internal "structural keys not strictly increasing within a height")
    placeSorted rest (some node) (canon.set! t out.size, out.push node)

/-- Renumber one height group: key every node by its head and the canonical
IDs of its (lower) children, sort by key, and append. -/
def placeBucket (temp : Array Node) (st : Array Nat × Array Node) (bucket : Array Nat) :
    Except SharingError (Array Nat × Array Node) :=
  let keyed := bucket.toList.map fun t =>
    let node := temp[t]!
    (t, { node with children := node.children.map (st.1[·]!) })
  let sorted := keyed.mergeSort fun x y => Node.compareKey x.2 y.2 != .gt
  placeSorted sorted none st

/-- Keep the nodes reachable from `rootTemps` and renumber them by the §3.2
rule: increasing height, then increasing `(tag, scalars, child IDs)`.
Returns the canonical DAG and the canonical root IDs. -/
def canonicalize (temp : Array Node) (rootTemps : Array Nat) :
    Except SharingError (Dag × Array Nat) := do
  let n := temp.size
  unless childrenPrecede temp do
    throw (.internal "interner produced a child after its parent")
  unless rootTemps.all (· < n) do
    throw (.internal "root ID out of range")
  let reach := reachMarks temp rootTemps
  let height := nodeHeights temp
  let maxH := (List.range n).foldl
    (fun acc t => if reach[t]! then max acc height[t]! else acc) 0
  let buckets := heightBuckets reach height maxH n
  let (canon, out) ← (List.range (maxH + 1)).foldlM
    (fun st h => placeBucket temp st buckets[h]!) (Array.replicate n 0, #[])
  return (⟨out⟩, rootTemps.map (canon[·]!))

/-- Result of expanding input into a canonical DAG. -/
structure Expanded where
  dag : Dag
  roots : Array Nat
  visits : Nat
  internedNodes : Nat
  deriving Inhabited

/-- Expand `(sharing, roots)` into the canonical DAG of the roots' distinct
subterms. The DAG height (which bounds the nesting depth of every later
recursive walk, including of the optimizer's output) must not exceed
`limits.maxDepth`. -/
def expand (limits : Limits) (sharing roots : Array Ixon.Expr) (allowShare : Bool) :
    Except SharingError Expanded := do
  let ((_, rootTemps), st) ← (ingestTable limits sharing roots allowShare).run {}
  let (dag, rootIds) ← canonicalize st.interner.nodes rootTemps
  if (nodeHeights dag.nodes).any (· > limits.maxDepth) then
    throw (.resourceExhausted .depth limits.maxDepth)
  return { dag, roots := rootIds, visits := st.visits,
           internedNodes := st.interner.nodes.size }

/-- Re-expand an encoding against an existing canonical DAG and return its
entry term IDs, root term IDs and walk count. A term absent from `dag`
receives an ID `≥ dag.size`. -/
def reexpand (limits : Limits) (dag : Dag) (sharing roots : Array Ixon.Expr) :
    Except SharingError (Array Nat × Array Nat × Nat) := do
  let st : IngestState := { interner := .ofNodes dag.nodes }
  let ((entryIds, rootIds), st) ← (ingestTable limits sharing roots true).run st
  return (entryIds, rootIds, st.visits)

/-! ## Occurrences and materialized expressions -/

/-- Whether the edge from `parent` to its `i`-th child continues the parent's
telescope. -/
def continuationEdge (parent : Node) (i : Nat) (child : Node) : Bool :=
  match parent.head, child.head with
  | .app, .app => i == 0
  | .lam _, .lam _ => i == 1
  | .all .., .all .. => i == 1
  | _, _ => false

/-- Counts pushed from parents to children, the largest ID first: every root
occurrence counts 1, and each term `y`, whose own count `c` is final by then,
adds `weight y c` per edge into each child. The second array counts only the
head (non-continuation) edges. -/
def propagateCounts (dag : Dag) (roots : Array Nat) (weight : Nat → Nat → Nat) :
    Array Nat × Array Nat :=
  let n := dag.size
  let base := roots.foldl (fun acc r => acc.modify r (· + 1)) (Array.replicate n 0)
  foldRange (fun (st : Array Nat × Array Nat) k =>
      let y := n - 1 - k
      let wy := weight y st.1[y]!
      let node := dag.node y
      (List.range node.children.size).foldl (fun (st : Array Nat × Array Nat) i =>
        let c := node.child i
        (st.1.modify c (· + wy),
         if continuationEdge node i (dag.node c) then st.2 else st.2.modify c (· + wy)))
        st)
    0 n (base, base)

/-- `propagateCounts` with the pair of counts taken apart before it is
updated, so that both arrays are updated in place. -/
def propagateCountsFast (dag : Dag) (roots : Array Nat) (weight : Nat → Nat → Nat) :
    Array Nat × Array Nat :=
  let n := dag.size
  let base := roots.foldl (fun acc r => acc.modify r (· + 1)) (Array.replicate n 0)
  foldRange (fun (st : Array Nat × Array Nat) k =>
      match st with
      | (ds, hs) =>
        let y := n - 1 - k
        let wy := weight y ds[y]!
        let node := dag.node y
        (List.range node.children.size).foldl (fun (st : Array Nat × Array Nat) i =>
          match st with
          | (ds, hs) =>
            let c := node.child i
            (ds.modify c (· + wy),
             if continuationEdge node i (dag.node c) then hs else hs.modify c (· + wy)))
          (ds, hs))
    0 n (base, base)

@[csimp] theorem propagateCounts_eq_fast : @propagateCounts = @propagateCountsFast := by
  funext dag roots weight
  unfold propagateCounts propagateCountsFast
  rfl

/-- Logical occurrence count of every term in the expanded roots, counted
through every DAG edge with multiplicity and every root occurrence. -/
def occurrences (dag : Dag) (roots : Array Nat) : Array Nat :=
  (propagateCounts dag roots fun _ c => c).1

/-- One expanded expression per term, built bottom-up with maximal pointer
sharing (no occurrence-tree allocation). -/
def Dag.toExprs (dag : Dag) : Array Ixon.Expr := Id.run do
  let mut out : Array Ixon.Expr := Array.mkEmpty dag.size
  for node in dag.nodes do
    let e := node.toExpr fun c => out[c]!
    out := out.push e
  return out

/-! ## Ordered expression roots of a `ConstantInfo` -/

/-- Roots of one mutual member, in the order of
`Ix.CompileM.mutConstRootExprs`. -/
def mutConstRoots : Ixon.MutConst → List Ixon.Expr
  | .defn d => [d.typ, d.value]
  | .indc i => i.typ :: i.ctors.toList.map (·.typ)
  | .recr r => r.typ :: r.rules.toList.map (·.rhs)

/-- All ordered expression roots of a `ConstantInfo`, in the order of
`Ix.CompileM.constantInfoRootExprs`: definitions type/value, axioms and
quotients type, recursors type then rule bodies, mutual blocks each member
in member order (inductives type then constructor types), projections none. -/
def constantInfoRoots : Ixon.ConstantInfo → Array Ixon.Expr
  | .defn d => (mutConstRoots (.defn d)).toArray
  | .recr r => (mutConstRoots (.recr r)).toArray
  | .axio a => #[a.typ]
  | .quot q => #[q.typ]
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => #[]
  | .muts ms => (ms.toList.flatMap mutConstRoots).toArray

/-- Apply `f` to every root of a mutual member, in `mutConstRoots` order. -/
def mapMutConstRoots (f : Ixon.Expr → Ixon.Expr) : Ixon.MutConst → Ixon.MutConst
  | .defn d => .defn { d with typ := f d.typ, value := f d.value }
  | .indc i => .indc { i with typ := f i.typ, ctors := i.ctors.map fun c => { c with typ := f c.typ } }
  | .recr r => .recr { r with typ := f r.typ, rules := r.rules.map fun rl => { rl with rhs := f rl.rhs } }

/-- Apply `f` to every root of a `ConstantInfo`, in `constantInfoRoots` order,
leaving every other field unchanged (a pure, total form of
`withRoots info ((constantInfoRoots info).map f)`). -/
def mapRoots (f : Ixon.Expr → Ixon.Expr) : Ixon.ConstantInfo → Ixon.ConstantInfo
  | .defn d => .defn { d with typ := f d.typ, value := f d.value }
  | .recr r => .recr { r with typ := f r.typ, rules := r.rules.map fun rl => { rl with rhs := f rl.rhs } }
  | .axio a => .axio { a with typ := f a.typ }
  | .quot q => .quot { q with typ := f q.typ }
  | .cPrj p => .cPrj p
  | .rPrj p => .rPrj p
  | .iPrj p => .iPrj p
  | .dPrj p => .dPrj p
  | .muts ms => .muts (ms.map (mapMutConstRoots f))

private def takeRoot : List Ixon.Expr → Except SharingError (Ixon.Expr × List Ixon.Expr)
  | e :: rest => .ok (e, rest)
  | [] => .error (.internal "root cursor underflow")

private def takeRoots : Nat → List Ixon.Expr →
    Except SharingError (List Ixon.Expr × List Ixon.Expr)
  | 0, rest => .ok ([], rest)
  | k + 1, rest => do
    let (e, rest) ← takeRoot rest
    let (es, rest) ← takeRoots k rest
    return (e :: es, rest)

private def withMutConstRoots (m : Ixon.MutConst) (rs : List Ixon.Expr) :
    Except SharingError (Ixon.MutConst × List Ixon.Expr) :=
  match m with
  | .defn d => do
    let (typ, rs) ← takeRoot rs
    let (value, rs) ← takeRoot rs
    return (.defn { d with typ, value }, rs)
  | .indc i => do
    let (typ, rs) ← takeRoot rs
    let (tys, rs) ← takeRoots i.ctors.size rs
    let ctors := (i.ctors.toList.zip tys).toArray.map fun (c, t) => { c with typ := t }
    return (.indc { i with typ, ctors }, rs)
  | .recr r => do
    let (typ, rs) ← takeRoot rs
    let (rhss, rs) ← takeRoots r.rules.size rs
    let rules := (r.rules.toList.zip rhss).toArray.map fun (rule, rhs) => { rule with rhs }
    return (.recr { r with typ, rules }, rs)

/-- Replace the roots of `info` by `roots`, which must have exactly as many
entries as `constantInfoRoots info`, consumed in the same order. -/
def withRoots (info : Ixon.ConstantInfo) (roots : Array Ixon.Expr) :
    Except SharingError Ixon.ConstantInfo := do
  let expected := (constantInfoRoots info).size
  if roots.size != expected then
    throw (.rootCountMismatch expected roots.size)
  let rs := roots.toList
  let (info', rest) ← match info with
    | .defn d => do
      let (m, rest) ← withMutConstRoots (.defn d) rs
      match m with
      | .defn d' => pure (Ixon.ConstantInfo.defn d', rest)
      | _ => throw (.internal "member kind changed")
    | .recr r => do
      let (m, rest) ← withMutConstRoots (.recr r) rs
      match m with
      | .recr r' => pure (Ixon.ConstantInfo.recr r', rest)
      | _ => throw (.internal "member kind changed")
    | .axio a => do
      let (typ, rest) ← takeRoot rs
      pure (Ixon.ConstantInfo.axio { a with typ }, rest)
    | .quot q => do
      let (typ, rest) ← takeRoot rs
      pure (Ixon.ConstantInfo.quot { q with typ }, rest)
    | .cPrj p => pure (Ixon.ConstantInfo.cPrj p, rs)
    | .rPrj p => pure (Ixon.ConstantInfo.rPrj p, rs)
    | .iPrj p => pure (Ixon.ConstantInfo.iPrj p, rs)
    | .dPrj p => pure (Ixon.ConstantInfo.dPrj p, rs)
    | .muts ms => do
      let mut out : Array Ixon.MutConst := #[]
      let mut rest := rs
      for m in ms do
        let (m', rest') ← withMutConstRoots m rest
        out := out.push m'
        rest := rest'
      pure (Ixon.ConstantInfo.muts out, rest)
  unless rest.isEmpty do
    throw (.internal "root cursor not exhausted")
  return info'

end Ix.Sharing.Exact

end
