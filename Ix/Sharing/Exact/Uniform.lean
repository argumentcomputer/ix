/-
  Exact minimum sharing under a uniform reference width.

  Cost model: every `Share` costs exactly `w ≥ 1` bytes regardless of its
  index; the table count is an exact `Tag0`; telescopes and all other bytes
  are as written by `putExpr`. The variable length of a table set `S` is

    L(S) = tag0Size |S| + Σ_{t ∈ S} inl_S(t) + Σ_{roots r} C_S(r)

  where `C_S` is the fixed-dictionary optimum (`Exact.Dictionary`) with every
  term of `S` available at width `w`, and `inl_S(t)` is `t`'s cost with an
  inline top. Order is irrelevant to the model length: in any dependency
  order (stored descendants first) each entry already sees every stored term
  that can occur inside it, and a Share's price does not depend on its index.
  So only the set is chosen; the table order is then pinned (children before
  parents; among ready terms, larger in-degree first, then smaller structural
  ID).

  ## Facts about a term `t` of the compact DAG
  * `deg(t)`: in-degree, counting edge multiplicity and root occurrences.
  * `headDeg(t)`: the in-edges at head positions (roots are heads). The other
    edges are continuations: an App as the function of an App, a Lam as the
    body of a Lam, an All as the body of an All.
  * `occ(t)`: the fully expanded occurrence count.
  * `size(t)`: the unshared standalone length `C_∅(t)`.

  ## Classes
  * CERTAIN-EXCLUDED (in no minimum) when `(occ-1)·size < occ·w`.
    Take any minimum storing `t` and replace each of its `R` references by
    `t`'s entry body (at a telescope continuation the merged header is
    subadditive), then delete the entry; the table count cannot grow. The
    length changes by at most `(R-1)·body - R·w` with `body ≤ size` and, as a
    minimum has no unreachable entry, `R ≤ occ`. This is negative when the
    condition holds (for `size ≤ w` for every `R`), contradicting minimality.
    It subsumes R1 (`occ = 1`) and R2 (one-byte terms).
  * Search candidates: in-degree `≥ 2`, not certain-excluded. In-degree-1
    terms are left out by an exchange that does not increase the length (so
    some minimum avoids them, although ties can also store them): let `p` be
    the single parent of `t`; every reference to `t` sits in an inline write
    of `p`, and each such write costs more than `w`. If `t` is referenced at
    most once, inlining it (or dropping it) is strictly shorter. Otherwise,
    if `p` is stored, a write of `p` outside its entry becomes `Share(p)`
    (strictly shorter). If `p` is not stored, store `p` instead of `t`, built
    from the write `W₁` with the smallest inline spine prefix `j₁`, and turn
    the other writes into `Share(p)`: the new header `tag4Size(j₁) ≤ j₁` is
    covered by another write's surplus over `w`, which is at least its own
    prefix length `≥ j₁`. The count is unchanged. Each step removes an
    in-degree-1 term and adds only a strict ancestor, so it terminates.
  * CERTAIN-STORED (in every minimum whose table holds only candidates; such
    minima have the global minimum length by the in-degree-1 exchange) for a
    candidate when `g ≥ θ`, with `d`, `h` the visible counts (below) and `b`
    a lower bound on the bytes of `t` inside a telescope that runs through it
    (excluding the header):
      non-telescope:      g = (d-1)·inl⁻ - d·w
      telescope, h ≥ 1:   g = (d-1)·b + (h-1) - d·w
      telescope, h = 0:   g = (d-1)·b - tag4Size(spine length) - d·w
    Exchange: in a candidate-only minimum `E` not storing `t`, `t` has at
    least `d` inline occurrences, at least `h` of them at head positions. Add
    the entry `t` (its optimal body, which costs exactly what one head
    occurrence costs, or at most one continuation occurrence plus its header
    `≤ tag4Size(spine length)`), and replace every occurrence by `Share(t)`:
    descendants lose occurrences, ancestors get a `w`-byte leaf where the
    subtree was, telescopes only shorten. The length drops by at least `g`
    minus the growth of the table count's TagN, contradicting minimality.
    Threshold: with `n` candidates, one more entry grows the count by at most
    `tag0StepBound n` bytes (1 below 4311826560, the TagN `f = 0` rung-5 end), so
    `θ = θmax = tag0StepBound n + 1` always holds; `θ = 1` holds when
    `tag0Size(#candidates) = tag0Size(#terms with g ≥ θmax)`, since every
    candidate-only minimum contains the `g ≥ θmax` terms and only candidates,
    so its count and that count plus one share a TagN bracket.
    Visible counts, for a maybe-stored set `M` (here the candidates): lower
    bounds `d(t)`, `h(t)` on the inline occurrences of `t` in an encoding of
    any `S ⊆ M` with `t ∉ S`. One per root occurrence, plus per edge from `z`
    (for `h`: head edges only) the writes of `z`: at least 1 when `z ∈ M`
    (every reachable term is written somewhere) and at least `d(z)` otherwise
    (every occurrence of an unstored term is an inline write). So `d ≥ deg`.
    The bounds `inl⁻`, `b` are computed bottom-up with every child in `M`
    priced at `min(w, ·)` (it might be stored), every other child at its
    inline bound, and a header of at least 1 byte.
  * UNCERTAIN: the remaining candidates.

  ## Certain-stored terms are opaque
  `g ≥ 1` forces `b ≥ w` (and `inl⁻ > w`), so in every candidate encoding a
  certain-stored term costs exactly `w` wherever it occurs, and a telescope
  running into it is never shorter than one cut there. Costs above it are
  therefore computed with it as a `w`-byte leaf that ends the spine; this
  truncated evaluation equals the real one (checked on the output).

  ## Components
  Two uncertain terms are connected when a DAG path joins them whose
  intermediate terms are not certain-stored. Every cost is then a sum of
  functions of the chosen terms of one component each: children add; a
  telescope's minimum over cut options couples a cut node only with the
  terms below it; a term's own Share option couples it with the terms below
  it. The table-count prefix is the only coupling: each component search
  returns, per chosen count, its best change `Δ` within `slack` of its
  optimum, where `slack` is the largest `Tag0` difference between two
  candidate-only sets that contain the certain-stored terms. When the
  combined choice is in a higher count bracket than the certain-stored terms
  alone, a small knapsack over components checks whether a lower bracket is
  at least as short.

  ## Component search: reclassifying branch and bound
  A node is a partial assignment of the component's members (stored, not
  stored, undecided) within the decisions of the enclosing searches. At each
  node:
  1. Reclassify. With `M` = the candidates minus every member decided not
     stored, recompute `inl⁻`, `b` and the visible counts over the
     component's area and decide stored every undecided member with
     `g ≥ θ`. The exchange above holds for every minimum that respects the
     partial assignment, since such a minimum lies in `M`.
  2. Bound. The cost with every undecided member available and its entry
     free is a lower bound on every completion (costs only drop when more
     terms are available; entries cost ≥ 0). Prune when it exceeds the best
     completion of this search by more than `slack`; never on equality
     (ties are left to the tie order).
  3. Split. A member decided stored with `inl⁻ ≥ w` (non-telescope) or
     `b ≥ w` (telescope) under the node's bounds is opaque, like a
     certain-stored term. The undecided members are grouped by DAG paths
     whose intermediate terms are not opaque; the groups below a decided
     stored member that is not opaque are also joined (its `min(w, ·)`
     couples them). Each group is solved by a sub-search with the node's
     decisions as context and the per-count tables are combined. A single
     group is also handed to a sub-search when one of this search's
     decisions no longer reaches it. Sub-search tables are memoized under
     the group and the decisions that reach it: those joined to a group
     member by a directed DAG path (up or down) whose intermediate terms are
     not opaque, and those below (through non-opaque terms) a stored
     non-opaque ancestor reached that way, whose `min(w, ·)` couples its
     subterms. Any other decision is reached only through ancestors whose
     cost it enters additively, so it does not change the group's `Δ`.
  4. Branch on the undecided member with the largest `|g|` (then the smaller
     ID), "stored" first when `g > 0`.
  Each node and each sub-search counts as one search state. The plain subset
  enumeration of each component is kept as a test oracle
  (`Limits.uniformSubsetSearch`, off by default and excluded from the
  optimality theorems); it is not the compiler path.

  ## Tie-break
  Among minimum-length sets the least one in the order "the smaller
  structural ID in the symmetric difference is not stored". Components,
  groups, memoized tables and the bracket knapsack preserve this order
  exactly: the parts of a union are disjoint, so the order of unions is
  decided inside one part.
-/
module

public import Ix.Sharing.Exact.UniformSearchLocal

public section

namespace Ix.Sharing.Exact

open Ixon

/-! ## Result -/

/-- Uniform-width optimization result: the usual result (with `modelBytes`
the exact uniform-model length and `variableBytes` the real serialized
length of the same output) plus the classification and search statistics. -/
structure UniformSharingResult where
  result : ExactSharingResult
  /-- The stored set, ascending. -/
  stored : Array Nat
  certainStored : Array Nat
  certainExcluded : Array Nat
  uncertain : Array Nat
  lowDegree : Array Nat
  components : Array (Array Nat)
  /-- Search states (component subsets evaluated). -/
  statesVisited : Nat
  /-- Whether the table-count knapsack chose a lower count bracket. -/
  lowerBracket : Bool
  deriving Inhabited

/-- Telescope spines must be shorter than this. Below `Ixon.tagNEnd5 4` (the
start of the 9-byte TagN rung) the telescope headers are subadditive,
`tag4Size (a + b) ≤ tag4Size a + tag4Size b`, which the certain-excluded class
relies on (merging two telescopes when a Share is unshared).
`optimizeUniformExpanded` fails closed on a longer spine. -/
def teleSubaddEnd : Nat := Ixon.tagNEnd5 4

/-- First count with the same TagN (`f = 0`) width as `k` (`tag0Size`): the
start of `k`'s rung. -/
def tag0BracketStart (k : Nat) : Nat :=
  if k < Ixon.tagNEnd1 0 then 0
  else if k < Ixon.tagNEnd2 0 then Ixon.tagNEnd1 0
  else if k < Ixon.tagNEnd3 0 then Ixon.tagNEnd2 0
  else if k < Ixon.tagNEnd4 0 then Ixon.tagNEnd3 0
  else if k < Ixon.tagNEnd5 0 then Ixon.tagNEnd4 0
  else Ixon.tagNEnd5 0

/-- An upper bound on `tag0Size (k + 1) - tag0Size k` for every `k < n`: the
TagN (`f = 0`) width grows by one byte at 128, 16512, 82048 and 16859264, and
by four at 4311826560. -/
def tag0StepBound (n : Nat) : Nat :=
  if n < Ixon.tagNEnd5 0 then 1 else 4

/-- The next term of the pinned order: among the remaining terms whose
nearest stored descendants are all placed, the larger in-degree first, then
the smaller ID. -/
def pinnedPick (deg : Array Nat) (deps : Std.HashMap Nat (Array Nat))
    (placed : Std.HashSet Nat) (remaining : Array Nat) : Option Nat :=
  let ready := remaining.filter fun t => ((deps.getD t #[]).all placed.contains)
  ready.foldl (init := none) fun acc t =>
    match acc with
    | none => some t
    | some a => if deg[t]! > deg[a]! || (deg[t]! == deg[a]! && t < a) then some t else acc

/-- Place up to `fuel` terms in the pinned order; anything left unplaced (never
the case for a DAG) is appended as given. -/
def pinnedPlace (deg : Array Nat) (deps : Std.HashMap Nat (Array Nat)) :
    Nat → Array Nat → Array Nat → Std.HashSet Nat → Array Nat
  | 0, order, remaining, _ => order ++ remaining
  | fuel + 1, order, remaining, placed =>
    match pinnedPick deg deps placed remaining with
    | none => order ++ remaining
    | some pick =>
      pinnedPlace deg deps fuel (order.push pick) (remaining.erase pick) (placed.insert pick)

/-- Nearest stored descendants of each stored term. -/
def pinnedDeps (dag : Dag) (stored : Array Nat) : Std.HashMap Nat (Array Nat) := Id.run do
  let n := dag.size
  let isStored := stored.foldl (fun acc t => acc.set! t true) (Array.replicate n false)
  let mut deps : Std.HashMap Nat (Array Nat) := {}
  for t in stored do
    let mut seen : Std.HashSet Nat := {}
    let mut stack := (dag.node t).children
    let mut out : Array Nat := #[]
    for _ in [0:4 * n + 4] do
      match stack.back? with
      | none => break
      | some u =>
        stack := stack.pop
        if seen.contains u then continue
        seen := seen.insert u
        if isStored[u]! then
          out := out.push u
        else
          stack := stack ++ (dag.node u).children
    deps := deps.insert t out
  return deps

/-- Pinned table order of a stored set: stored descendants first; among
ready terms the larger in-degree first, then the smaller ID. -/
def pinnedOrder (dag : Dag) (deg : Array Nat) (stored : Array Nat) : Array Nat :=
  pinnedPlace deg (pinnedDeps dag stored) stored.size #[] stored {}

/-- The stored set chosen by the uniform-width search, before
materialization, with its model length and the search statistics. -/
structure UniformChoice where
  facts : GraphFacts
  certainStored : Array Nat
  certainExcluded : Array Nat
  uncertain : Array Nat
  lowDegree : Array Nat
  components : Array (Array Nat)
  /-- The stored set, ascending. -/
  stored : Array Nat
  /-- The uniform-model length of `stored`, from the truncated evaluation. -/
  model : Nat
  states : Nat
  costEvals : Nat
  lowerBracket : Bool

/-- One knapsack step: the best `(Δ, set)` per count up to `cap`, combining the
counts so far with a component's table. -/
def knapStep (cap : Nat) (dp : Array (Option (_root_.Int × Array Nat))) (bySize : CTable) :
    Array (Option (_root_.Int × Array Nat)) :=
  (List.range dp.size).foldl (fun ndp c =>
    match dp[c]! with
    | none => ndp
    | some (d, s) => (List.range bySize.size).foldl (fun ndp k =>
      match bySize[k]! with
      | none => ndp
      | some (dk, sk) =>
        if c + k > cap then ndp
        else
          let cand : _root_.Int × Array Nat := (d + dk, mergeSorted s sk)
          if betterEntry cand ndp[c + k]! then ndp.set! (c + k) (some cand) else ndp) ndp)
    (Array.replicate (cap + 1) none)

/-- Pick the shortest count bracket candidate (ties by `setPrec`). -/
def knapChoose (kCS : Nat) (dp : Array (Option (_root_.Int × Array Nat)))
    (init : _root_.Int × Array Nat × Bool) : _root_.Int × Array Nat × Bool :=
  (List.range dp.size).foldl (fun (acc : _root_.Int × Array Nat × Bool) c =>
    match dp[c]! with
    | none => acc
    | some (d, s) =>
      let l : _root_.Int := d + (tag0Size (kCS + c) : _root_.Int)
      let l0 : _root_.Int := acc.1 + (tag0Size (kCS + acc.2.1.size) : _root_.Int)
      if l < l0 || (l == l0 && setPrec s acc.2.1) then (d, s, true) else acc) init

/-- The classification stage of the uniform optimizer: the classes, the
certain-stored evaluation, the components and the shared search tables. -/
structure UStage where
  f : GraphFacts
  cand : Array Bool
  b0 : UBounds
  vis0 : Array Nat × Array Nat
  theta : _root_.Int
  cls : Array UClass
  cs : Array Nat
  ce : Array Nat
  unc : Array Nat
  low : Array Nat
  opaq : Array Bool
  up : UPrep
  widthCs : Array (Option Nat)
  allTrue : Array Bool
  baseEv : DictEval
  comps : Array (Array Nat)
  slack : Nat
  rootCount : Array Nat

/-- Classify the terms and prepare the component searches. -/
def uniformStage (w : Nat) (ex : Expanded) (p : Prep) : UStage :=
  let n := ex.dag.size
  let f := graphFacts ex.dag ex.roots
  let cand := searchCandidates p f w
  let b0 := uniformBounds p w cand
  let vis0 := visibleCounts ex.dag ex.roots cand
  -- The certain-stored threshold: `1 + tag0StepBound nCand` always holds (one
  -- more entry grows the table count by at most that many bytes; 2 below
  -- 4311826560 candidates); 1 holds when every minimum lies in one count bracket
  -- (it contains the certain-stored terms and only candidates).
  let nCand := (cand.filter id).size
  let thetaMax : _root_.Int := tag0StepBound nCand + 1
  let clsMax := classifyWith p f w b0 vis0 thetaMax
  let nCsMax := (clsMax.filter (· == .certainStored)).size
  let theta : _root_.Int := if tag0Size nCand == tag0Size nCsMax then 1 else thetaMax
  let cls := if theta == 1 then classifyWith p f w b0 vis0 1 else clsMax
  let pick (c : UClass) := (Array.range n).filter (cls[·]! == c)
  let cs := pick .certainStored
  let unc := pick .uncertain
  let opaq := cs.foldl (fun acc t => acc.set! t true) (Array.replicate n false)
  let widthCs : Array (Option Nat) :=
    cs.foldl (fun acc t => acc.set! t (some w)) (Array.replicate n none)
  let allTrue := Array.replicate n true
  { f, cand, b0, vis0, theta, cls, cs, ce := pick .certainExcluded, unc,
    low := pick .lowDegree, opaq, up := UPrep.mk' p w opaq, widthCs, allTrue,
    baseEv := p.eval widthCs allTrue, comps := uncertainComponents ex.dag cls,
    -- Largest table-count difference between two sets that contain the
    -- certain-stored terms and only candidates.
    slack := tag0Size (cs.size + unc.size) - tag0Size cs.size,
    rootCount := ex.roots.foldl (fun acc r => acc.modify r (· + 1)) (Array.replicate n 0) }

/-- Search every component. -/
def searchComponents (limits : Limits) (ex : Expanded) (sg : UStage) :
    Except SharingError (Array CompResult × Nat × Nat) :=
  sg.comps.foldlM (init := ((#[] : Array CompResult), 0, 0))
    fun (acc : Array CompResult × Nat × Nat) members => do
      let (results, states, costEvals) := acc
      if limits.uniformSubsetSearch then
        let (r, states, costEvals) ← searchComponentRef sg.up sg.f sg.opaq ex.roots sg.slack
          limits members states costEvals
        pure (results.push r, states, costEvals)
      else
        let cx := mkSCtx ex sg.f sg.up sg.cand sg.b0 sg.vis0 sg.rootCount sg.slack sg.theta
          sg.baseEv sg.widthCs sg.allTrue sg.unc members
        let (r, states, costEvals) ← searchComponent cx limits states costEvals
        pure (results.push r, states, costEvals)

/-- `searchComponents` as `searchComponentsWith` on the stage's tables (the
same loop), so that compiled code runs `searchComponentsWithFast`. -/
def searchComponentsVia (limits : Limits) (ex : Expanded) (sg : UStage) :
    Except SharingError (Array CompResult × Nat × Nat) :=
  searchComponentsWith limits ex sg.f sg.up sg.cand sg.b0 sg.vis0 sg.rootCount sg.slack sg.theta
    sg.baseEv sg.widthCs sg.allTrue sg.unc sg.opaq sg.comps

@[csimp] theorem searchComponents_eq_via : @searchComponents = @searchComponentsVia := by
  funext limits ex sg
  rfl

/-- The chosen `Δ` and set: the per-component optima, unless a lower count
bracket is shorter (and whether one was). -/
def uniformKnapsack (limits : Limits) (kCS : Nat) (results : Array CompResult) :
    Except SharingError (_root_.Int × Array Nat × Bool) := do
  let bestX := results.foldl (fun acc r => mergeSorted acc r.bestSet) #[]
  let bestDelta := results.foldl (fun acc r => acc + r.bestDelta) (0 : _root_.Int)
  let start := tag0BracketStart (kCS + bestX.size)
  if start > kCS then
    let cap := start - 1 - kCS
    if (results.size + 1) * (cap + 1) > limits.maxKnapsackCells then
      throw (.resourceExhausted .knapsackCells limits.maxKnapsackCells)
    -- dp[c]: best (Δ, set) with c chosen terms, over the components so far.
    let dp := results.foldl (fun dp r => knapStep cap dp r.bySize)
      (#[some (0, #[])] ++ Array.replicate cap none)
    pure (knapChoose kCS dp (bestDelta, bestX, false))
  else pure (bestDelta, bestX, false)

/-- The uniform-model length of the certain-stored terms without the count's
`Tag0`: the roots and the certain-stored entries, by the full evaluation. -/
def csBase (ex : Expanded) (p : Prep) (sg : UStage) : Nat :=
  ex.roots.foldl (fun acc r => acc + sg.baseEv.cost[r]!) 0 +
    sg.cs.foldl (fun acc c => acc +
      (evalStep p.dag p.family p.spineLen p.tail (sg.widthCs.set! c none) sg.allTrue sg.baseEv
        c).cost[c]!) 0

/-- `csBase` with each entry cost read in place (`evalHidden`). -/
def csBaseFast (ex : Expanded) (p : Prep) (sg : UStage) : Nat :=
  ex.roots.foldl (fun acc r => acc + sg.baseEv.cost[r]!) 0 +
    sg.cs.foldl (fun acc c => acc +
      evalHidden p.dag p.family p.spineLen p.tail sg.widthCs sg.allTrue sg.baseEv c) 0

@[csimp] theorem csBase_eq_fast : @csBase = @csBaseFast := by
  funext ex p sg
  simp only [csBase, csBaseFast, evalHidden_eq]

/-- Classify, search every component and combine: the stored set and its
model length. -/
def uniformChoose (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep) :
    Except SharingError UniformChoice := do
  let sg := uniformStage w ex p
  unless componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) do
    throw (.internal "uncertain components are not a separated partition")
  let (results, states, costEvals) ← searchComponents limits ex sg
  let (chosenDelta, chosenX, lowerBracket) ← uniformKnapsack limits sg.cs.size results
  let modelInt : _root_.Int := (csBase ex p sg : Nat) + chosenDelta +
    (tag0Size (sg.cs.size + chosenX.size) : _root_.Int)
  if modelInt < 0 then throw (.internal "negative model length")
  let model := modelInt.toNat
  if model > limits.maxOutputBytes then
    throw (.resourceExhausted .outputBytes limits.maxOutputBytes)
  return { facts := sg.f, certainStored := sg.cs, certainExcluded := sg.ce, uncertain := sg.unc,
           lowDegree := sg.low, components := sg.comps, stored := mergeSorted sg.cs chosenX, model,
           states, costEvals, lowerBracket }

/-- The stored set is strictly increasing and every term has in-degree at
least 2. -/
def inClassCheck (dag : Dag) (roots : Array Nat) (stored : Array Nat) : Bool :=
  let deg := edgeCounts dag roots false
  (List.range stored.size).all (fun i => decide (i + 1 < stored.size → stored[i]! < stored[i + 1]!)) &&
    stored.all (fun t => decide (2 ≤ deg[t]!))

/-- Materialize a chosen set in the pinned order with the real evaluation, and
check it against the model length and the input. -/
def uniformFinish (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep) (c : UniformChoice) :
    Except SharingError UniformSharingResult := do
  let n := ex.dag.size
  let stored := c.stored
  let model := c.model
  unless stored.all (· < n) do
    throw (.internal "stored term out of range")
  unless inClassCheck ex.dag ex.roots stored do
    throw (.internal "stored terms are not increasing terms of in-degree at least 2")
  let order := pinnedOrder ex.dag c.facts.deg stored
  let width := stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate n none)
  let (entries, roots, predicted, work) ← p.materializeDependent order ex.roots width limits
  unless predicted == model do
    throw (.internal s!"uniform model length {model} differs from the full evaluation {predicted}")
  let (entryIds, rootIds, _) ← reexpand limits ex.dag entries roots
  unless entryIds == order do
    throw (.internal "materialized entries do not expand to the stored terms")
  unless rootIds == ex.roots do
    throw (.internal "materialized roots do not expand to the input roots")
  let measured := tag0Size entries.size + exprsSize entries + exprsSize roots
  let unshared := tag0Size 0 + rootsCost p.base ex.roots
  let stats : Stats :=
    { exprVisits := ex.visits, internedNodes := ex.internedNodes, distinctSubterms := n,
      candidates := c.certainStored.size + c.uncertain.size, statesExpanded := c.states,
      costEvals := c.costEvals, materializedNodes := work, outputBytes := measured }
  return {
    result := { roots, sharing := entries, tableTerms := order, variableBytes := measured,
                modelBytes := model, unsharedBytes := unshared, stats }
    stored, certainStored := c.certainStored, certainExcluded := c.certainExcluded,
    uncertain := c.uncertain, lowDegree := c.lowDegree, components := c.components,
    statesVisited := c.states, lowerBracket := c.lowerBracket }

/-- Exact uniform-width optimization of an expanded input. Fails closed
(`formatBound "telescope spine length"`) when a telescope spine reaches
`teleSubaddEnd`. -/
def optimizeUniformExpanded (w : Nat) (limits : Limits) (ex : Expanded) :
    Except SharingError UniformSharingResult := do
  if w == 0 then throw (.formatBound "uniform Share width" 0)
  unless childrenPrecede ex.dag.nodes do
    throw (.internal "DAG children do not precede their parents")
  unless ex.dag.nodes.all (fun node => node.children.size == node.head.arity) do
    throw (.internal "DAG node arity")
  unless ex.roots.all (· < ex.dag.size) do
    throw (.internal "root ID out of range")
  unless (reachMarks ex.dag.nodes ex.roots).all id do
    throw (.internal "DAG term unreachable from the roots")
  let p := Prep.ofDag ex.dag
  unless (List.range ex.dag.size).all (fun t => p.spineLen[t]! < teleSubaddEnd) do
    throw (.formatBound "telescope spine length" teleSubaddEnd)
  let c ← uniformChoose w limits ex p
  uniformFinish w limits ex p c

end Ix.Sharing.Exact

end
