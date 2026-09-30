/-
  Exact minimum sharing (W1): table selection and ordering (§4.1, §6).

  Candidates. By R1 a term with a single logical occurrence is never stored,
  and by R2 neither is a term whose inline encoding is one byte. The search
  therefore appends only terms with `occ ≥ 2` and unshared length `≥ 2`.

  Width states (§6.1, §6.4). A state is the sorted vector of
  `(term ID, Share width)` pairs of the stored terms; `k` stored terms fix the
  next index `k` and its width. `F(M)` is the least accumulated table-body
  length of any history reaching `M`; among equal `F`, the least term-ID
  prefix is retained (§6.2). Layers are processed in increasing `k`, states
  within a layer in increasing key order, so work counters are
  deterministic. Appending `t` to `M` costs `C_M(t)` (the entry may use only
  the earlier entries). Stopping at `M` costs
  `F(M) + tag0Size k + Σ C_M(root)` variable bytes; the fixed Constant bytes
  are the same for every candidate and do not affect the argmin.

  Pruning (§4.1 LB). With `M⁺` granting every absent candidate a width-1
  reference, `F(M) + tag0Size k + Σ C_{M⁺}(root)` bounds every completion of
  `M` from below. A state or transition is pruned only when its bound is
  strictly greater than a length already achieved by a feasible encoding, so
  equal-length states are always kept. For `k ≤ 8` every stored term has
  width 1, so `M⁺` is the same for all such states and its root costs are
  computed once.

  The selected table is materialized with the byte-least tie-break, and the
  output is re-expanded and re-measured; any disagreement is an internal
  error rather than a result.
-/
module

public import Ix.Sharing.Exact.Dictionary
public import Ix.Sharing

public section

namespace Ix.Sharing.Exact

open Ixon

/-! ## Candidates and affected terms -/

/-- Candidate terms after R1 (`occ ≥ 2`) and R2 (unshared length `≥ 2`), in
increasing ID order. -/
def candidateTerms (p : Prep) (occ : Array Nat) : Array Nat :=
  (Array.range p.dag.size).filter fun t => occ[t]! ≥ 2 && p.base[t]! ≥ 2

/-- Terms whose cost can depend on the dictionary: candidates and every term
with a candidate below it. Other terms always cost `C_∅`. -/
def affectedTerms (dag : Dag) (isCand : Array Bool) : Array Bool := Id.run do
  let mut aff : Array Bool := Array.replicate dag.size false
  for t in [0:dag.size] do
    let below := (dag.node t).children.any (aff[·]!)
    aff := aff.set! t (isCand[t]! || below)
  return aff

/-- Sum of root costs, with multiplicity. -/
def rootsCost (cost : Array Nat) (roots : Array Nat) : Nat :=
  roots.foldl (fun acc r => acc + cost[r]!) 0

/-! ## Width states -/

/-- Stored terms with their Share widths, sorted by term ID. -/
abbrev StateKey := Array (Nat × Nat)

/-- Insert `(t, w)` keeping the key sorted by term ID. -/
def StateKey.insertSorted (key : StateKey) (t w : Nat) : StateKey :=
  let (lo, hi) := key.toList.span fun (u, _) => u < t
  (lo ++ (t, w) :: hi).toArray

/-- Total order on state keys (term, then width, lexicographically). -/
def StateKey.compare (a b : StateKey) : Ordering :=
  lexCompare (a.toList.flatMap fun (t, w) => [t, w]) (b.toList.flatMap fun (t, w) => [t, w])

/-- Dictionary widths of a state. -/
def StateKey.widths (n : Nat) (key : StateKey) : Array (Option Nat) :=
  key.foldl (fun acc (t, w) => acc.set! t (some w)) (Array.replicate n none)

/-- `M⁺`: every candidate gets width 1, stored terms keep their widths. -/
def optimisticWidths (n : Nat) (cands : Array Nat) (key : StateKey) : Array (Option Nat) :=
  let w := cands.foldl (fun acc t => acc.set! t (some 1)) (Array.replicate n none)
  key.foldl (fun acc (t, wt) => acc.set! t (some wt)) w

/-- `(cost, prefix)` strictly better, comparing cost then prefix. -/
def lexLess (c : Nat) (pre : Array Nat) (c' : Nat) (pre' : Array Nat) : Bool :=
  c < c' || (c == c' && compareNatArray pre pre' == .lt)

/-! ## Search -/

/-- Inputs of one exact search. -/
structure SearchInput where
  prep : Prep
  roots : Array Nat
  candidates : Array Nat
  affected : Array Bool
  deriving Inhabited

abbrev SearchM := StateT Stats (Except SharingError)

@[inline] def liftE {α} (x : Except SharingError α) : SearchM α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

def chargeCost (limits : Limits) (w : Nat) : SearchM Unit := do
  let s ← get
  let v ← liftE (bump s.costEvals w limits.maxCostEvals .costEvals)
  set { s with costEvals := v }

def chargeTransition (limits : Limits) : SearchM Unit := do
  let s ← get
  let v ← liftE (bump s.transitions 1 limits.maxTransitions .transitions)
  set { s with transitions := v }

def chargeState (limits : Limits) : SearchM Unit := do
  let s ← get
  let v ← liftE (bump s.statesReached 1 limits.maxStates .states)
  set { s with statesReached := v }

/-- The winning stopping state: variable length and table term IDs. -/
structure Best where
  total : Nat
  table : Array Nat
  deriving Repr, Inhabited

/-- Exact width-state search. `upper` must be the variable length of some
feasible encoding (it is only used for pruning). Returns the least
`(variable length, table term-ID vector)` over all stopping states. -/
def search (inp : SearchInput) (limits : Limits) (upper : Nat) : SearchM Best := do
  let n := inp.prep.dag.size
  let cands := inp.candidates
  let (optCost, w0) := inp.prep.costs (optimisticWidths n cands #[]) inp.affected
  chargeCost limits w0
  let rootLB0 := rootsCost optCost inp.roots
  let mut incumbent := upper
  let mut best : Option Best := none
  let mut layer : Array (StateKey × Nat × Array Nat) := #[(#[], 0, #[])]
  chargeState limits
  for k in [0:cands.size + 1] do
    if layer.isEmpty then break
    modify fun s => { s with layers := s.layers + 1 }
    let mut next : Std.HashMap StateKey (Nat × Array Nat) := {}
    for (key, f, pre) in layer do
      let rootLB ← if k ≤ 8 then pure rootLB0 else do
        let (c, w) := inp.prep.costs (optimisticWidths n cands key) inp.affected
        chargeCost limits w
        pure (rootsCost c inp.roots)
      if f + tag0Size k + rootLB > incumbent then
        modify fun s => { s with statesPruned := s.statesPruned + 1 }
        continue
      modify fun s => { s with statesExpanded := s.statesExpanded + 1 }
      let width := key.widths n
      let (cost, w) := inp.prep.costs width inp.affected
      chargeCost limits w
      let total := f + tag0Size k + rootsCost cost inp.roots
      let improves := match best with
        | none => true
        | some b => lexLess total pre b.total b.table
      if improves then best := some ⟨total, pre⟩
      if total < incumbent then incumbent := total
      let nw := shareWidth k
      let quickRest := tag0Size (k + 1) + rootLB
      for t in cands do
        if (width[t]!).isSome then continue
        chargeTransition limits
        let f' := f + cost[t]!
        if f' + quickRest > incumbent then
          modify fun s => { s with transitionsPruned := s.transitionsPruned + 1 }
          continue
        let key' := key.insertSorted t nw
        let pre' := pre.push t
        match next.get? key' with
        | none =>
          chargeState limits
          next := next.insert key' (f', pre')
        | some (f0, pre0) =>
          if lexLess f' pre' f0 pre0 then next := next.insert key' (f', pre')
    layer := (next.toArray.map fun (key, f, pre) => (key, f, pre)).qsort
      fun a b => StateKey.compare a.1 b.1 == .lt
  match best with
  | some b => return b
  | none => throw (.internal "search evaluated no stopping state")

/-! ## Materialization and verification -/

/-- Materialize a table sequence and the roots with the byte-least
minimum-length encodings. Returns entries, roots, and the variable length
predicted by `C_M`. -/
def materializeTable (p : Prep) (table roots : Array Nat) (limits : Limits) :
    Except SharingError (Array Ixon.Expr × Array Ixon.Expr × Nat × Nat) := do
  let n := p.dag.size
  let mut entries : Array Ixon.Expr := #[]
  let mut predicted := tag0Size table.size
  let mut work := 0
  for h : i in [0:table.size] do
    let t := table[i]
    let (es, cost, w) ← p.materialize (indexOfPrefix n table i) #[t] limits
    let some e := es[0]? | throw (.internal "missing materialized entry")
    entries := entries.push e
    predicted := predicted + cost[t]!
    work := work + w
    if work > limits.maxMaterialize then
      throw (.resourceExhausted .materialize limits.maxMaterialize)
  let (rs, cost, w) ← p.materialize (indexOfPrefix n table table.size) roots limits
  predicted := predicted + rootsCost cost roots
  work := work + w
  if work > limits.maxMaterialize then
    throw (.resourceExhausted .materialize limits.maxMaterialize)
  return (entries, rs, predicted, work)

/-- Result of an exact optimization. -/
structure ExactSharingResult where
  /-- Rewritten roots, in input order. -/
  roots : Array Ixon.Expr
  /-- The sharing table. -/
  sharing : Array Ixon.Expr
  /-- Structural term IDs of the table entries (the key component `Q`). -/
  tableTerms : Array Nat
  /-- Exact variable bytes: roots, table count, and table bodies. -/
  variableBytes : Nat
  /-- Variable bytes of the unshared encoding. -/
  unsharedBytes : Nat
  stats : Stats
  deriving Repr, Inhabited

/-- Variable length of the existing heuristic applied to the expanded
roots, if its output is a valid backward-reference encoding of exactly the
same roots. Only used as a pruning upper bound. -/
def heuristicVariableBytes (limits : Limits) (dag : Dag) (rootIds : Array Nat) :
    Option Nat :=
  let exprs := dag.toExprs
  let roots := rootIds.map (exprs[·]!)
  let (rw, tbl) := Ix.Sharing.applySharing roots
  match reexpand limits dag tbl rw with
  | .ok (_, ids, _) =>
    if ids == rootIds then some (tag0Size tbl.size + exprsSize tbl + exprsSize rw)
    else none
  | .error _ => none

/-- Optimize an expanded input. The result minimizes
`(variable length, table term IDs, bytes)`; since the fixed Constant bytes
are the same for every candidate, this is the §3.3 key of the complete
Constant. -/
def optimizeExpanded (limits : Limits) (ex : Expanded) :
    Except SharingError ExactSharingResult := do
  let p := Prep.ofDag ex.dag
  let n := ex.dag.size
  let occ := occurrences ex.dag ex.roots
  let cands := candidateTerms p occ
  let isCand := cands.foldl (fun acc t => acc.set! t true) (Array.replicate n false)
  let affected := affectedTerms ex.dag isCand
  let unshared := tag0Size 0 + rootsCost p.base ex.roots
  let heuristic :=
    if limits.useHeuristicBound && unshared ≤ limits.heuristicMaxUnsharedBytes then
      heuristicVariableBytes limits ex.dag ex.roots
    else none
  let upper := match heuristic with
    | some h => min h unshared
    | none => unshared
  let stats0 : Stats :=
    { exprVisits := ex.visits, internedNodes := ex.internedNodes,
      distinctSubterms := n, candidates := cands.size, heuristicBytes := heuristic }
  let inp : SearchInput := { prep := p, roots := ex.roots, candidates := cands, affected }
  let (best, stats) ← (search inp limits upper).run stats0
  if best.total > limits.maxOutputBytes then
    throw (.resourceExhausted .outputBytes limits.maxOutputBytes)
  let (entries, roots, predicted, work) ← materializeTable p best.table ex.roots limits
  unless predicted == best.total do
    throw (.internal s!"materialized cost {predicted} differs from search cost {best.total}")
  let measured := tag0Size entries.size + exprsSize entries + exprsSize roots
  unless measured == best.total do
    throw (.internal s!"measured length {measured} differs from search cost {best.total}")
  let (entryIds, rootIds, _) ← reexpand limits ex.dag entries roots
  unless entryIds == best.table do
    throw (.internal "materialized entries do not expand to the selected terms")
  unless rootIds == ex.roots do
    throw (.internal "materialized roots do not expand to the input roots")
  return { roots, sharing := entries, tableTerms := best.table,
           variableBytes := best.total, unsharedBytes := unshared,
           stats := { stats with materializedNodes := work, outputBytes := measured } }

end Ix.Sharing.Exact

end
