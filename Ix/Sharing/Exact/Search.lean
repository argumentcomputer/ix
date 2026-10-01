/-
  Exact minimum sharing: table selection and ordering (§4.1, §6).

  The width-state search below computes the global minimum of
  `docs/sharing-minimum.md` §3. It is exponential in the candidates and is a
  test oracle for small inputs, not the compiler path. The table
  materialization (`materializeTable`) and `ExactSharingResult` are shared
  with the canonical construction (`Exact.Uniform`, `Exact.Tiered`).

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
public import Ix.Sharing.Exact.Phase3
public import Ix.Sharing.Exact.Reexpand

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
def search (inp : SearchInput) (limits : Limits) (upper : Nat)
    (widthAt : Nat → Nat := shareWidth) : SearchM Best := do
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
      if limits.prune && f + tag0Size k + rootLB > incumbent then
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
      let nw := widthAt k
      let quickRest := tag0Size (k + 1) + rootLB
      for t in cands do
        if (width[t]!).isSome then continue
        chargeTransition limits
        let f' := f + cost[t]!
        if limits.prune && f' + quickRest > incumbent then
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

/-- State of the table materialization: the entries so far, the dictionary
of those entries (table indices and Share widths), its evaluation, the
predicted length and the work. -/
structure TableState where
  entries : Array Ixon.Expr
  index : Array (Option Nat)
  width : Array (Option Nat)
  ev : DictEval
  predicted : Nat
  work : Nat
  deriving Inhabited

/-- Materialize table entry `i` against the dictionary of the entries before
it, then add it to the dictionary, re-evaluating only the entry and the
terms above it. The work (the evaluation that priced the entry plus its
size) is checked against `maxMaterializeWork` after every entry. -/
def materializeStep (p : Prep) (table : Array Nat) (limits : Limits) (widthAt : Nat → Nat)
    (st : TableState) (i : Nat) : Except SharingError TableState := do
  let t := table[i]!
  let c := st.ev.cost[t]!
  if c > limits.maxMaterialize then
    throw (.resourceExhausted .materialize limits.maxMaterialize)
  let e ← p.build st.ev st.index st.width false (p.dag.size + 1) t
  let work := st.work + st.ev.work + c
  if work > limits.maxMaterializeWork then
    throw (.resourceExhausted .materializeWork limits.maxMaterializeWork)
  let index := st.index.set! t (some i)
  let width := st.width.set! t (some (widthAt i))
  return { entries := st.entries.push e, index, width, ev := p.evalUp st.ev width t,
           predicted := st.predicted + c, work }

/-- Materialize a table sequence and the roots with the byte-least
minimum-length encodings: entry `i` against the dictionary of the entries
before it, the roots against the whole table. Returns entries, roots, and
the variable length predicted by `C_M`. The Share at index `i` is priced
`widthAt i` (the real width by default, or a model width). The dictionary
is evaluated once and then updated incrementally (`Prep.evalUp`). -/
def materializeTable (p : Prep) (table roots : Array Nat) (limits : Limits)
    (widthAt : Nat → Nat := shareWidth) :
    Except SharingError (Array Ixon.Expr × Array Ixon.Expr × Nat × Nat) := do
  if table.size ≥ wordBound then throw (.formatBound "share index" table.size) else
  if !table.all (· < p.dag.size) then throw (.internal "table term out of range") else do
  let st ← (List.range table.size).foldlM (materializeStep p table limits widthAt)
    { entries := #[], index := Array.replicate p.dag.size none,
      width := Array.replicate p.dag.size none,
      ev := p.evalAll (Array.replicate p.dag.size none),
      predicted := tag0Size table.size, work := 0 }
  if roots.foldl (fun acc r => acc + st.ev.cost[r]!) 0 > limits.maxMaterialize then
    throw (.resourceExhausted .materialize limits.maxMaterialize) else do
  let rs ← roots.mapM fun r => p.build st.ev st.index st.width false (p.dag.size + 1) r
  let work := st.work + st.ev.work + roots.foldl (fun acc r => acc + st.ev.cost[r]!) 0
  if work > limits.maxMaterializeWork then
    throw (.resourceExhausted .materializeWork limits.maxMaterializeWork) else
  return (st.entries, rs, st.predicted + rootsCost st.ev.cost roots, work)

/-! ### The same materialization with the ancestors marked by a walk

`materializeStep` re-evaluates through `Prep.evalUp`, which tests every term
from the entry on for the entry below it, and updates the dictionary arrays
while the state that holds them is still live, so each entry copies them.
`materializeStepFast` takes the state apart first and marks the terms to
re-evaluate by a walk up the parent lists (`Prep.evalUpFast`);
`materializeTable_eq_fast` proves the result equal for every input (on a
DAG whose children do not precede their parents the specification runs). -/

/-- `materializeStep` with the state taken apart and `Prep.evalUpFast`
(parent lists `parents`, cleared marks `mark`, returned cleared). -/
def materializeStepFast (p : Prep) (parents : Array (Array Nat)) (table : Array Nat)
    (limits : Limits) (widthAt : Nat → Nat) (st : TableState) (mark : Array Bool) (i : Nat) :
    Except SharingError (TableState × Array Bool) :=
  match st with
  | ⟨entries, index, width, ev, predicted, work⟩ =>
    let t := table[i]!
    let c := ev.cost[t]!
    if c > limits.maxMaterialize then .error (.resourceExhausted .materialize limits.maxMaterialize)
    else match p.build ev index width false (p.dag.size + 1) t with
    | .error e => .error e
    | .ok e =>
      let work := work + ev.work + c
      if work > limits.maxMaterializeWork then
        .error (.resourceExhausted .materializeWork limits.maxMaterializeWork)
      else
        let index := index.set! t (some i)
        let width := width.set! t (some (widthAt i))
        match p.evalUpFast parents ev width t mark with
        | (ev, mark) => .ok (⟨entries.push e, index, width, ev, predicted + c, work⟩, mark)

/-- Entries `i, …, i + k - 1` by `materializeStepFast`. -/
def materializeLoopFast (p : Prep) (parents : Array (Array Nat)) (table : Array Nat)
    (limits : Limits) (widthAt : Nat → Nat) :
    Nat → Nat → TableState → Array Bool → Except SharingError TableState
  | 0, _, st, _ => .ok st
  | k + 1, i, st, mark =>
    match materializeStepFast p parents table limits widthAt st mark i with
    | .error e => .error e
    | .ok (st, mark) => materializeLoopFast p parents table limits widthAt k (i + 1) st mark

/-- `materializeTable` by `materializeLoopFast` (`materializeTable_eq_fast`). -/
def materializeTableFast (p : Prep) (table roots : Array Nat) (limits : Limits)
    (widthAt : Nat → Nat := shareWidth) :
    Except SharingError (Array Ixon.Expr × Array Ixon.Expr × Nat × Nat) := do
  if table.size ≥ wordBound then throw (.formatBound "share index" table.size) else
  if !table.all (· < p.dag.size) then throw (.internal "table term out of range") else
  if !childrenPrecede p.dag.nodes then materializeTable p table roots limits widthAt else do
  let st ← materializeLoopFast p (parentEdgeLists p.dag) table limits widthAt table.size 0
    { entries := #[], index := Array.replicate p.dag.size none,
      width := Array.replicate p.dag.size none,
      ev := p.evalAll (Array.replicate p.dag.size none),
      predicted := tag0Size table.size, work := 0 } (Array.replicate p.dag.size false)
  if roots.foldl (fun acc r => acc + st.ev.cost[r]!) 0 > limits.maxMaterialize then
    throw (.resourceExhausted .materialize limits.maxMaterialize) else do
  let rs ← roots.mapM fun r => p.build st.ev st.index st.width false (p.dag.size + 1) r
  let work := st.work + st.ev.work + roots.foldl (fun acc r => acc + st.ev.cost[r]!) 0
  if work > limits.maxMaterializeWork then
    throw (.resourceExhausted .materializeWork limits.maxMaterializeWork) else
  return (st.entries, rs, st.predicted + rootsCost st.ev.cost roots, work)

theorem materializeStepFast_eq (p : Prep) (table : Array Nat) (limits : Limits)
    (widthAt : Nat → Nat) (st : TableState) (i : Nat) (hcp : childrenPrecede p.dag.nodes = true)
    (ht : table[i]! < p.dag.size) :
    materializeStepFast p (parentEdgeLists p.dag) table limits widthAt st
        (Array.replicate p.dag.size false) i =
      (materializeStep p table limits widthAt st i).map
        fun st' => (st', Array.replicate p.dag.size false) := by
  obtain ⟨entries, index, width, ev, predicted, work⟩ := st
  unfold materializeStepFast materializeStep
  simp only [Prep.evalUpFast_eq _ _ _ _ ht hcp]
  by_cases h1 : ev.cost[table[i]!]! > limits.maxMaterialize
  · simp [h1, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Except.map]
  · cases hb : p.build ev index width false (p.dag.size + 1) table[i]! with
    | error e => simp [h1, bind, Except.bind, Except.map]
    | ok e =>
      by_cases h2 : work + ev.work + ev.cost[table[i]!]! > limits.maxMaterializeWork
      · simp [h1, h2, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Except.map]
      · simp [h1, h2, bind, Except.bind, pure, Except.pure, Except.map]

theorem materializeLoopFast_eq (p : Prep) (table : Array Nat) (limits : Limits)
    (widthAt : Nat → Nat) (hcp : childrenPrecede p.dag.nodes = true)
    (htab : ∀ i, i < table.size → table[i]! < p.dag.size) :
    ∀ (k i : Nat) (st : TableState), i + k ≤ table.size →
      materializeLoopFast p (parentEdgeLists p.dag) table limits widthAt k i st
          (Array.replicate p.dag.size false) =
        (List.range' i k).foldlM (materializeStep p table limits widthAt) st
  | 0, _, st, _ => rfl
  | k + 1, i, st, hk => by
    unfold materializeLoopFast
    rw [materializeStepFast_eq p table limits widthAt st i hcp (htab i (by omega)),
      List.range'_succ, List.foldlM_cons]
    cases materializeStep p table limits widthAt st i with
    | error e => rfl
    | ok st' =>
      exact materializeLoopFast_eq p table limits widthAt hcp htab k (i + 1) st' (by omega)

@[csimp] theorem materializeTable_eq_fast : @materializeTable = @materializeTableFast := by
  funext p table roots limits widthAt
  unfold materializeTableFast
  by_cases h1 : table.size ≥ wordBound
  · unfold materializeTable
    simp [h1]
  · by_cases h2 : table.all (· < p.dag.size) = true
    · by_cases h3 : childrenPrecede p.dag.nodes = true
      · have htab : ∀ i, i < table.size → table[i]! < p.dag.size := by
          intro i hi
          rw [Array.all_eq_true] at h2
          rw [getElem!_pos table i hi]
          simpa using h2 i hi
        have hl := materializeLoopFast_eq p table limits widthAt h3 htab table.size 0
          { entries := #[], index := Array.replicate p.dag.size none,
            width := Array.replicate p.dag.size none,
            ev := p.evalAll (Array.replicate p.dag.size none),
            predicted := tag0Size table.size, work := 0 } (by omega)
        rw [← List.range_eq_range'] at hl
        unfold materializeTable
        simp only [h1, h2, h3, hl, ite_false, Bool.not_true, Bool.false_eq_true]
      · simp [h1, h2, h3]
    · unfold materializeTable
      simp [h1, h2]

/-! ### One evaluation for an order closed under stored descendants

When every stored descendant of each entry comes before it in the table (and
the DAG is well formed), the entry for `t` written under the entries before
it is the entry written under the whole table with the Share of `t` itself
hidden: below `t` the two dictionaries agree. `materializeTableOnePass` then
evaluates the whole dictionary once, prices each entry with its own Share
hidden (`evalHidden`) and builds it with the top Share excluded
(`Prep.buildTop`), and the roots under the whole table. The work it reports
and checks is the work `materializeTable` counts entry by entry, computed
from a walk up the parent lists (`ancestorWork`) and the spine counts
(`spineAdd`) instead of re-evaluating. Any other order or DAG, or a walk out
of fuel, runs `materializeTable`. -/

/-- The DAG is well formed (children before parents, the arity of each
head), the roots are terms of it, and the table lists distinct terms (its
whole-table index `index` maps each to its own position), each after every
stored term below it. -/
def onePassOrder (dag : Dag) (table roots : Array Nat) (index : Array (Option Nat)) : Bool :=
  childrenPrecede dag.nodes && dag.nodes.all (fun node => node.children.size == node.head.arity) &&
    roots.all (· < dag.size) &&
    let pos := fun c => match index[c]?.getD none with
      | some i => i + 1
      | none => 0
    let maxBelow := foldRange (fun (mb : Array Nat) u =>
        mb.set! u ((dag.node u).children.foldl (fun m c => max m (max (pos c) mb[c]!)) 0))
      0 dag.size (Array.replicate dag.size 0)
    (List.range table.size).all fun i =>
      index[table[i]!]?.getD none == some i && decide (maxBelow[table[i]!]! ≤ i)

/-- Entries `i, …, i + k - 1` of `materializeTableOnePass`: the entries so
far, the work so far, the work of the evaluation that prices the next entry,
the predicted length, the spine counts, the walk's marks (all below `i + 1`)
and its queue; `none` if a walk runs out of fuel. -/
def onePassLoop (p : Prep) (table : Array Nat) (limits : Limits) (ev : DictEval)
    (index width : Array (Option Nat)) (allTrue : Array Bool) (parents sp : Array (Array Nat)) :
    Nat → Nat → Array Ixon.Expr → Nat → Nat → Nat → Array Nat → Array Nat → Array Nat →
      Option (Except SharingError (Array Ixon.Expr × Nat × Nat × Nat))
  | 0, _, entries, work, evWork, predicted, _, _, _ => some (.ok (entries, work, evWork, predicted))
  | k + 1, i, entries, work, evWork, predicted, sc, mark, queue =>
    let t := table[i]!
    let c := evalHidden p.dag p.family p.spineLen p.tail width allTrue ev t
    if c > limits.maxMaterialize then
      some (.error (.resourceExhausted .materialize limits.maxMaterialize))
    else match p.buildTop ev index width c (p.dag.size + 1) t with
    | .error e => some (.error e)
    | .ok e =>
      let work := work + evWork + c
      if work > limits.maxMaterializeWork then
        some (.error (.resourceExhausted .materializeWork limits.maxMaterializeWork))
      else match spineAdd sp sc t with
      | none => none
      | some sc =>
        match ancestorWork parents sc (i + 1) t (4 * p.dag.size + 2) mark queue with
        | none => none
        | some (w, mark, queue) =>
          onePassLoop p table limits ev index width allTrue parents sp k (i + 1) (entries.push e)
            work w (predicted + c) sc mark queue

/-- `materializeTable` with one evaluation of the whole dictionary when the
order is closed under stored descendants (`onePassOrder`). -/
def materializeTableOnePass (p : Prep) (table roots : Array Nat) (limits : Limits)
    (widthAt : Nat → Nat := shareWidth) :
    Except SharingError (Array Ixon.Expr × Array Ixon.Expr × Nat × Nat) :=
  if table.size ≥ wordBound then throw (.formatBound "share index" table.size) else
  if !table.all (· < p.dag.size) then throw (.internal "table term out of range") else
  let n := p.dag.size
  let index := indexOfPrefix n table table.size
  if !onePassOrder p.dag table roots index then materializeTable p table roots limits widthAt else
  let width := index.map (·.map widthAt)
  let ev := p.evalAll width
  -- the first entry is priced by the empty dictionary's evaluation, which counts one per
  -- term (`evalAll_none_work`)
  match onePassLoop p table limits ev index width (Array.replicate n true) (parentEdgeLists p.dag)
      (spineParentLists p.dag p.family) table.size 0 #[] 0 n (tag0Size table.size)
      (Array.replicate n 0) (Array.replicate n 0) #[] with
  | none => materializeTable p table roots limits widthAt
  | some (.error e) => .error e
  | some (.ok (entries, work, evWork, predicted)) =>
    if roots.foldl (fun acc r => acc + ev.cost[r]!) 0 > limits.maxMaterialize then
      throw (.resourceExhausted .materialize limits.maxMaterialize) else do
    let rs ← roots.mapM fun r => p.build ev index width false (p.dag.size + 1) r
    let work := work + evWork + roots.foldl (fun acc r => acc + ev.cost[r]!) 0
    if work > limits.maxMaterializeWork then
      throw (.resourceExhausted .materializeWork limits.maxMaterializeWork) else
    return (entries, rs, predicted + rootsCost ev.cost roots, work)

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
  /-- The optimized objective: `variableBytes` with the real Share widths,
  or the variable length in a uniform-width cost model. -/
  modelBytes : Nat
  /-- Variable bytes of the unshared encoding. -/
  unsharedBytes : Nat
  stats : Stats
  deriving Repr, Inhabited

/-- Optimize an expanded input. The result minimizes
`(variable length, table term IDs, bytes)`; since the fixed Constant bytes
are the same for every candidate, this is the §3.3 key of the complete
Constant.

With `minInDegree2` only terms of compact in-degree at least 2 are
candidates. With `uniform := some w` every Share is priced `w` bytes regardless of its
index (a cost model, used as the reference for the uniform-width
optimizer): the search minimizes the model length, and `modelBytes` reports
the model length while `variableBytes` reports the real serialized length of the
same output. -/
def optimizeExpanded (limits : Limits) (ex : Expanded) (uniform : Option Nat := none)
    (minInDegree2 : Bool := false) : Except SharingError ExactSharingResult := do
  if uniform == some 0 then throw (.formatBound "uniform Share width" 0)
  let widthAt : Nat → Nat := match uniform with
    | some w => fun _ => w
    | none => shareWidth
  let p := Prep.ofDag ex.dag
  let n := ex.dag.size
  let occ := occurrences ex.dag ex.roots
  let cands := candidateTerms p occ
  -- Optionally restrict to terms of compact in-degree ≥ 2 (the uniform
  -- optimizer's candidate space), for differential tests.
  let cands := if !minInDegree2 then cands else Id.run do
    let mut deg : Array Nat := Array.replicate n 0
    for r in ex.roots do deg := deg.modify r (· + 1)
    for node in ex.dag.nodes do
      for c in node.children do deg := deg.modify c (· + 1)
    return cands.filter (deg[·]! ≥ 2)
  let isCand := cands.foldl (fun acc t => acc.set! t true) (Array.replicate n false)
  let affected := affectedTerms ex.dag isCand
  let unshared := tag0Size 0 + rootsCost p.base ex.roots
  -- The unshared encoding is the initial upper bound.
  let upper := unshared
  let stats0 : Stats :=
    { exprVisits := ex.visits, internedNodes := ex.internedNodes,
      distinctSubterms := n, candidates := cands.size }
  let inp : SearchInput := { prep := p, roots := ex.roots, candidates := cands, affected }
  let (best, stats) ← (search inp limits upper widthAt).run stats0
  if best.total > limits.maxOutputBytes then
    throw (.resourceExhausted .outputBytes limits.maxOutputBytes)
  let (entries, roots, predicted, work) ← materializeTable p best.table ex.roots limits widthAt
  unless predicted == best.total do
    throw (.internal s!"materialized cost {predicted} differs from search cost {best.total}")
  let measured := tag0Size entries.size + exprsSize entries + exprsSize roots
  unless uniform.isSome || measured == best.total do
    throw (.internal s!"measured length {measured} differs from search cost {best.total}")
  let (entryIds, rootIds, _) ← reexpand limits ex.dag entries roots
  unless entryIds == best.table do
    throw (.internal "materialized entries do not expand to the selected terms")
  unless rootIds == ex.roots do
    throw (.internal "materialized roots do not expand to the input roots")
  return { roots, sharing := entries, tableTerms := best.table,
           variableBytes := measured, modelBytes := best.total, unsharedBytes := unshared,
           stats := { stats with materializedNodes := work, outputBytes := measured } }

end Ix.Sharing.Exact

end
