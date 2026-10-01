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
    minus the growth of the table count's `Tag0`, contradicting minimality.
    Threshold: the `Tag0` grows by at most 1 byte, so `θ = 2` always holds;
    `θ = 1` holds when `tag0Size(#candidates) = tag0Size(#terms with g ≥ 2)`,
    since every candidate-only minimum contains the `g ≥ 2` terms and only
    candidates, so its count and that count plus one share a `Tag0` bracket.
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
  enumeration of each component is kept as the reference
  (`Limits.uniformSubsetSearch`).

  ## Tie-break
  Among minimum-length sets the least one in the order "the smaller
  structural ID in the symmetric difference is not stored". Components,
  groups, memoized tables and the bracket knapsack preserve this order
  exactly: the parts of a union are disjoint, so the order of unions is
  decided inside one part.
-/
module

public import Ix.Sharing.Exact.Search

public section

namespace Ix.Sharing.Exact

open Ixon

/-! ## Graph facts -/

/-- In-degrees, head in-degrees, occurrences and parent lists. -/
structure GraphFacts where
  deg : Array Nat
  headDeg : Array Nat
  occ : Array Nat
  parents : Array (Array Nat)
  deriving Inhabited

/-- Edge counts per target: the root occurrences plus, over every node and
child index, one per child edge (only non-continuation edges if `headOnly`). -/
def edgeCounts (dag : Dag) (roots : Array Nat) (headOnly : Bool) : Array Nat :=
  let base := roots.foldl (fun acc r => acc.modify r (· + 1)) (Array.replicate dag.size 0)
  foldRange (fun acc t =>
      let node := dag.node t
      (List.range node.children.size).foldl (fun acc i =>
        let c := node.child i
        if headOnly && continuationEdge node i (dag.node c) then acc
        else acc.modify c (· + 1)) acc)
    0 dag.size base

/-- Distinct parents of every term. -/
def parentLists (dag : Dag) : Array (Array Nat) := Id.run do
  let n := dag.size
  let mut parents : Array (Array Nat) := Array.replicate n #[]
  for t in [0:n] do
    let node := dag.node t
    for c in node.children do
      unless (parents[c]!).contains t do parents := parents.modify c (·.push t)
  return parents

def graphFacts (dag : Dag) (roots : Array Nat) : GraphFacts :=
  { deg := edgeCounts dag roots false, headDeg := edgeCounts dag roots true,
    occ := occurrences dag roots, parents := parentLists dag }

/-! ## Classes -/

/-- Classification of a term for the uniform-width search. -/
inductive UClass where
  /-- Not certain-excluded, but in-degree `< 2`: never searched. -/
  | lowDegree
  | certainExcluded
  | certainStored
  | uncertain
  deriving BEq, Repr, Inhabited

/-- Lower bounds used by the certain-stored test. `inlineLB`: bytes of the
term written inline at a head position; `mergedLB`: bytes of a telescope
node inside a telescope running through it (no header); `headLB`/`contLB`:
the same at a head/continuation position when the term may be a Share. -/
structure UBounds where
  inlineLB : Array Nat
  mergedLB : Array Nat
  headLB : Array Nat
  contLB : Array Nat
  deriving Inhabited

/-- One step of `uniformBounds`: the bounds of `t` from those of its
children. -/
def boundsStep (p : Prep) (w : Nat) (maybeStored : Array Bool) (b : UBounds) (t : Nat) :
    UBounds :=
  let node := p.dag.node t
  let fam := p.family[t]!
  let (i, m) :=
    if fam == .none then
      let i := node.children.foldl (fun acc c => acc + b.headLB[c]!) node.head.ownBytes
      (i, i)
    else
      let nxt := node.spineNext
      let rest := if p.family[nxt]! == fam then b.contLB[nxt]! else b.headLB[nxt]!
      let m := node.sideExtra + b.headLB[node.sideChild]! + rest
      (1 + m, m)
  { inlineLB := b.inlineLB.set! t i, mergedLB := b.mergedLB.set! t m,
    headLB := b.headLB.set! t (if maybeStored[t]! then min w i else i),
    contLB := b.contLB.set! t (if maybeStored[t]! then min w m else m) }

def uniformBounds (p : Prep) (w : Nat) (maybeStored : Array Bool) : UBounds :=
  let n := p.dag.size
  foldRange (boundsStep p w maybeStored) 0 n
    { inlineLB := Array.replicate n 0, mergedLB := Array.replicate n 0,
      headLB := Array.replicate n 0, contLB := Array.replicate n 0 }

/-- The certain-stored gain bound with explicit occurrence lower bounds: `d`
inline occurrences in all, `h` of them at head positions (see the module
doc). -/
def storedGainC (p : Prep) (b : UBounds) (w t d h : Nat) : _root_.Int :=
  let deg := _root_.Int.ofNat d
  let wI := _root_.Int.ofNat w
  if p.family[t]! == .none then
    (deg - 1) * _root_.Int.ofNat b.inlineLB[t]! - deg * wI
  else if h ≥ 1 then
    (deg - 1) * _root_.Int.ofNat b.mergedLB[t]! + (_root_.Int.ofNat h - 1) - deg * wI
  else
    (deg - 1) * _root_.Int.ofNat b.mergedLB[t]! - _root_.Int.ofNat (tag4Size p.spineLen[t]!) - deg * wI

/-- The certain-stored gain bound `g` of a term with its in-degrees as the
occurrence counts. -/
def storedGain (p : Prep) (f : GraphFacts) (b : UBounds) (w t : Nat) : _root_.Int :=
  storedGainC p b w t f.deg[t]! f.headDeg[t]!

/-- Cap of the visible counts (any lower bound keeps the gain test sound). -/
def visibleCap : Nat := 1 <<< 20

/-- Visible occurrence counts: lower bounds on the inline occurrences of each
term `t` in every encoding of a set `S ⊆ maybeStored` with `t ∉ S`. Each root
occurrence counts 1, and each edge from `z` counts the writes of `z`: at least
1 when `z` may be stored (every reachable term is written somewhere), else at
least the visible count of `z` (every occurrence of an unstored term is an
inline write). The second array counts only head (non-continuation) edges.
Values are capped at `visibleCap` where they are passed on. -/
def visibleCounts (dag : Dag) (roots : Array Nat) (maybeStored : Array Bool) :
    Array Nat × Array Nat :=
  propagateCounts dag roots fun y c => if maybeStored[y]! then 1 else min c visibleCap

/-- Whether a term is certain-excluded: `(occ-1)·size < occ·w`. -/
def certainExcludedTest (p : Prep) (f : GraphFacts) (w t : Nat) : Bool :=
  (f.occ[t]! - 1) * p.base[t]! < f.occ[t]! * w

/-- The search candidates (in-degree ≥ 2, not certain-excluded): only these
can be stored in the encodings the search ranges over. -/
def searchCandidates (p : Prep) (f : GraphFacts) (w : Nat) : Array Bool :=
  (Array.range p.dag.size).map fun t => !certainExcludedTest p f w t && f.deg[t]! ≥ 2

/-- Classify every term under the root-level bounds `b`
(`uniformBounds p w (searchCandidates p f w)`). -/
def classifyWith (p : Prep) (f : GraphFacts) (w : Nat) (b : UBounds)
    (vis : Array Nat × Array Nat) (theta : _root_.Int := 2) : Array UClass :=
  (Array.range p.dag.size).map fun t =>
    if certainExcludedTest p f w t then .certainExcluded
    else if f.deg[t]! < 2 then .lowDegree
    else if storedGainC p b w t vis.1[t]! vis.2[t]! ≥ theta then .certainStored
    else .uncertain

/-- Classify every term. -/
def classify (p : Prep) (f : GraphFacts) (w : Nat) (roots : Array Nat) : Array UClass :=
  let cand := searchCandidates p f w
  classifyWith p f w (uniformBounds p w cand) (visibleCounts p.dag roots cand)

/-! ## Components -/

/-- Union-find root (fuel-bounded; `parent[x] ≤ x` is maintained). -/
def ufFind (parent : Array Nat) (x : Nat) : Nat := Id.run do
  let mut cur := x
  for _ in [0:parent.size + 1] do
    let q := parent[cur]!
    if q == cur then break
    cur := q
  return cur

/-- Components of the uncertain terms: joined by DAG paths that avoid
certain-stored terms. Each component is sorted; components are sorted by
their smallest term. -/
def uncertainComponents (dag : Dag) (cls : Array UClass) : Array (Array Nat) := Id.run do
  let n := dag.size
  let mut uf : Array Nat := Array.range n
  -- Component representatives reachable at or below each term.
  let mut reps : Array (Array Nat) := Array.replicate n #[]
  for t in [0:n] do
    if cls[t]! == .certainStored then continue
    let mut rs : Array Nat := #[]
    for c in (dag.node t).children do
      for r in reps[c]! do
        let fr := ufFind uf r
        unless rs.contains fr do rs := rs.push fr
    if cls[t]! == .uncertain then
      for r in rs do
        let a := ufFind uf t
        let b := ufFind uf r
        if a != b then
          if a < b then uf := uf.set! b a else uf := uf.set! a b
      reps := reps.set! t #[t]
    else
      reps := reps.set! t rs
  let mut groups : Std.HashMap Nat (Array Nat) := {}
  for t in [0:n] do
    if cls[t]! == .uncertain then
      let r := ufFind uf t
      groups := groups.insert r ((groups.getD r #[]).push t)
  let comps := groups.toArray.map (·.2)
  return comps.qsort fun a b => a[0]! < b[0]!

/-! ## Truncated evaluation (certain-stored terms opaque) -/

/-- Values of one term in the truncated evaluation. -/
structure UVal where
  cost : Nat := 0
  inl : Nat := 0
  sides : Nat := 0
  below : Option Nat := none
  deriving Inhabited, Repr

/-- Static data of the truncated evaluation. -/
structure UPrep where
  prep : Prep
  w : Nat
  opaq : Array Bool
  /-- Spine length and natural tail, with spines ending at opaque terms. -/
  tLen : Array Nat
  tTail : Array Nat
  /-- Values with no uncertain term available. -/
  base : Array UVal
  deriving Inhabited

/-- Evaluate one term given its children's values. Returns the value and the
number of available spine descendants visited. -/
def UPrep.node (up : UPrep) (get : Nat → UVal) (avail : Nat → Bool) (t : Nat) :
    UVal × Nat := Id.run do
  let p := up.prep
  let node := p.dag.node t
  let fam := p.family[t]!
  let mut steps := 0
  let mut v : UVal := {}
  if fam == .none then
    v := { v with inl := node.children.foldl (fun acc c => acc + (get c).cost) node.head.ownBytes }
  else
    let nxt := node.spineNext
    let same := p.family[nxt]! == fam && !up.opaq[nxt]!
    let s := node.sideExtra + (get node.sideChild).cost + (if same then (get nxt).sides else 0)
    let bl : Option Nat :=
      if same then (if avail nxt then some nxt else (get nxt).below) else none
    let l := up.tLen[t]!
    let mut best := tag4Size l + s + (get up.tTail[t]!).cost
    let mut cur := bl
    for _ in [0:l] do
      match cur with
      | none => break
      | some u =>
        steps := steps + 1
        let cand := tag4Size (l - up.tLen[u]!) + (s - (get u).sides) + up.w
        if cand < best then best := cand
        cur := (get u).below
    v := { v with inl := best, sides := s, below := bl }
  let cost :=
    if up.opaq[t]! then up.w
    else if avail t then min up.w v.inl
    else v.inl
  return ({ v with cost }, steps)

/-- Build the truncated evaluation with certain-stored terms opaque. -/
def UPrep.mk' (p : Prep) (w : Nat) (opaq : Array Bool) : UPrep := Id.run do
  let n := p.dag.size
  let mut tLen : Array Nat := Array.replicate n 0
  let mut tTail : Array Nat := Array.replicate n 0
  for t in [0:n] do
    let fam := p.family[t]!
    if fam != .none then
      let nxt := (p.dag.node t).spineNext
      if p.family[nxt]! == fam && !opaq[nxt]! then
        tLen := tLen.set! t (tLen[nxt]! + 1)
        tTail := tTail.set! t tTail[nxt]!
      else
        tLen := tLen.set! t 1
        tTail := tTail.set! t nxt
  let up0 : UPrep := { prep := p, w, opaq, tLen, tTail, base := #[] }
  let mut base : Array UVal := Array.mkEmpty n
  for t in [0:n] do
    let (v, _) := up0.node (fun c => base[c]!) (fun _ => false) t
    base := base.push v
  return { up0 with base }

/-! ## Per-component exact search -/

/-- Static context of one component search. -/
structure CompCtx where
  up : UPrep
  members : Array Nat
  /-- Terms whose truncated values can depend on the component, ascending. -/
  area : Array Nat
  /-- Roots in `area` with their multiplicities. -/
  rootMult : Array (Nat × Nat)
  /-- Certain-stored terms in `area` (their entry bodies may change). -/
  storedIn : Array Nat
  /-- The component's cost with nothing chosen. -/
  phi0 : Nat
  /-- Keep subsets within this much of the best (table-count coupling). -/
  slack : Nat

/-- Numeric order reversed: the element order under which `setPrec` is a
lexicographic order. -/
def compareDesc (x y : Nat) : Ordering := compare y x

/-- Tie order on sorted sets: `a` precedes `b` when the smallest term of their
symmetric difference is in `b` (so `a` leaves it out). On sorted arrays this
is the lexicographic order under `compareDesc`, a proper prefix first: at the
first position where they differ, the smaller term belongs to one set only. -/
def setPrec (a b : Array Nat) : Bool :=
  Array.compareLex compareDesc a b == .lt

/-- Union of two sorted arrays (sorted). -/
def mergeSorted (a b : Array Nat) : Array Nat :=
  (a ++ b).qsort (· < ·)

/-- Search state of one component. -/
structure CompState where
  best : Option (_root_.Int × Array Nat) := none
  /-- Best `(Δ, set)` per chosen-set size, within `slack` of the best. -/
  bySize : Array (Option (_root_.Int × Array Nat)) := #[]
  states : Nat := 0
  costEvals : Nat := 0

abbrev CompM := StateT CompState (Except SharingError)

/-- Cost of the component's parts with `avail` available and `chosen`
stored (the entries of undecided terms are omitted), and the evaluation
work. -/
def CompCtx.phi (cx : CompCtx) (avail : Nat → Bool) (chosen : Array Nat) : Nat × Nat := Id.run do
  let mut vals : Std.HashMap Nat UVal := {}
  let mut work := 0
  for t in cx.area do
    let get := fun c => (vals.get? c).getD cx.up.base[c]!
    let (v, s) := cx.up.node get avail t
    vals := vals.insert t v
    work := work + 1 + s
  let get := fun c => (vals.get? c).getD cx.up.base[c]!
  let roots := cx.rootMult.foldl (fun acc (r, m) => acc + m * (get r).cost) 0
  let stored := cx.storedIn.foldl (fun acc c => acc + (get c).inl) 0
  let entries := chosen.foldl (fun acc x => acc + (get x).inl) 0
  return (roots + stored + entries, work)

/-- Record a complete choice. -/
def CompState.record (st : CompState) (delta : _root_.Int) (set : Array Nat) : CompState :=
  let better (o : Option (_root_.Int × Array Nat)) : Bool :=
    match o with
    | none => true
    | some (d, s) => delta < d || (delta == d && setPrec set s)
  let best := if better st.best then some (delta, set) else st.best
  let k := set.size
  let bySize := if st.bySize.size ≤ k then
      st.bySize ++ Array.replicate (k + 1 - st.bySize.size) none
    else st.bySize
  let bySize := if better bySize[k]! then bySize.set! k (some (delta, set)) else bySize
  { st with best, bySize }

/-- Depth-first branch and bound over the members (ascending), trying
"not stored" first. -/
def CompCtx.dfs (cx : CompCtx) (limits : Limits) : Nat → Nat → Array Nat → CompM Unit
  | 0, _, _ => throw (.internal "component search fuel exhausted")
  | fuel + 1, i, chosen => do
    let st ← get
    if st.states + 1 > limits.maxStates then
      throw (.resourceExhausted .states limits.maxStates)
    let undecided := cx.members.extract i cx.members.size
    let avail := fun t => chosen.contains t || undecided.contains t
    let (phi, work) := cx.phi avail chosen
    if st.costEvals + work > limits.maxCostEvals then
      throw (.resourceExhausted .costEvals limits.maxCostEvals)
    set { st with states := st.states + 1, costEvals := st.costEvals + work }
    let delta : _root_.Int := (phi : _root_.Int) - (cx.phi0 : _root_.Int)
    if i ≥ cx.members.size then
      modify fun st => st.record delta chosen
    else
      match (← get).best with
      | some (b, _) => if delta > b + (cx.slack : _root_.Int) then return
      | none => pure ()
      let t := cx.members[i]!
      cx.dfs limits fuel (i + 1) chosen
      cx.dfs limits fuel (i + 1) (chosen.push t)

/-- Terms whose truncated values can change with the component: its members
and their ancestors, not continuing above an opaq term. -/
def componentArea (up : UPrep) (f : GraphFacts) (members : Array Nat) : Array Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut stack := members
  for t in members do seen := seen.insert t
  for _ in [0:up.prep.dag.size + 1] do
    match stack.back? with
    | none => break
    | some t =>
      stack := stack.pop
      if up.opaq[t]! then continue
      for q in f.parents[t]! do
        unless seen.contains q do
          seen := seen.insert q
          stack := stack.push q
  return seen.toArray.qsort (· < ·)

/-- The undecided member to branch on: the largest `|gain|`, then the smaller
ID. -/
def pickBranch (gains : Array (Nat × _root_.Int)) : Option (Nat × _root_.Int) :=
  gains.foldl (init := none) fun acc (t, g) =>
    match acc with
    | none => some (t, g)
    | some (a, ga) => if g.natAbs > ga.natAbs || (g.natAbs == ga.natAbs && t < a) then some (t, g) else acc

/-! ## Reclassifying branch and bound with splitting -/

/-- Best `(Δ, set)` per chosen count (index = set size). -/
abbrev CTable := Array (Option (_root_.Int × Array Nat))

/-- Whether `e` beats the entry `o` (smaller `Δ`, then `setPrec`). -/
def betterEntry (e : _root_.Int × Array Nat) (o : Option (_root_.Int × Array Nat)) : Bool :=
  match o with
  | none => true
  | some (d, s) => e.1 < d || (e.1 == d && setPrec e.2 s)

/-- The smallest `Δ` of a table. -/
def CTable.best (tb : CTable) : Option _root_.Int :=
  tb.foldl (init := none) fun acc o =>
    match o, acc with
    | none, _ => acc
    | some (d, _), none => some d
    | some (d, _), some b => some (min d b)

/-- Record an entry at its count. -/
def CTable.add (tb : CTable) (e : _root_.Int × Array Nat) : CTable :=
  let k := e.2.size
  let tb := if tb.size ≤ k then tb ++ Array.replicate (k + 1 - tb.size) none else tb
  if betterEntry e tb[k]! then tb.set! k (some e) else tb

/-- Drop the entries more than `slack` above the best. -/
def CTable.trim (tb : CTable) (slack : Nat) : CTable :=
  match tb.best with
  | none => tb
  | some b => tb.map fun o =>
    match o with
    | some (d, s) => if d > b + (slack : _root_.Int) then none else some (d, s)
    | none => none

/-- Combine the tables of disjoint groups: every pair of entries, summed. -/
def CTable.conv (a b : CTable) : CTable := Id.run do
  let mut out : CTable := #[]
  for oa in a do
    let some (da, sa) := oa | continue
    for ob in b do
      let some (db, sb) := ob | continue
      out := out.add (da + db, mergeSorted sa sb)
  return out

/-- Static context of one component's search. -/
structure SCtx where
  up : UPrep
  facts : GraphFacts
  /-- Root-level search candidates, bounds and visible counts. -/
  cand : Array Bool
  bounds0 : UBounds
  vis0 : Array Nat × Array Nat
  members : Array Nat
  memberIdx : Std.HashMap Nat Nat
  /-- Members and their ancestors, not continuing above a certain-stored
  term, ascending; and the index of each. -/
  area : Array Nat
  areaIdx : Std.HashMap Nat Nat
  /-- Per area node: `(parent, edges, head edges)` for every distinct parent,
  and its root occurrences. -/
  inEdges : Array (Array (Nat × Nat × Nat))
  rootOcc : Array Nat
  /-- Roots in the area with multiplicities, certain-stored terms in it. -/
  rootMult : Array (Nat × Nat)
  storedIn : Array Nat
  slack : Nat
  theta : _root_.Int

/-- Search state of one component. -/
structure SState where
  states : Nat := 0
  costEvals : Nat := 0
  memo : Std.HashMap (Array Nat) CTable := {}
  memoHits : Nat := 0

abbrev SM := StateT SState (Except SharingError)

/-- The component's cost with `avail` available and the entries of `stored`
(beyond the certain-stored ones), and the evaluation work. -/
def SCtx.phi (cx : SCtx) (avail : Nat → Bool) (stored : Array Nat) : Nat × Nat := Id.run do
  let mut vals : Std.HashMap Nat UVal := {}
  let mut work := 0
  for t in cx.area do
    let get := fun c => (vals.get? c).getD cx.up.base[c]!
    let (v, s) := cx.up.node get avail t
    vals := vals.insert t v
    work := work + 1 + s
  let get := fun c => (vals.get? c).getD cx.up.base[c]!
  let roots := cx.rootMult.foldl (fun acc (r, m) => acc + m * (get r).cost) 0
  let base := cx.storedIn.foldl (fun acc c => acc + (get c).inl) 0
  let entries := stored.foldl (fun acc x => acc + (get x).inl) 0
  return (roots + base + entries, work)

/-- Bounds under a decided-out set: the root-level bounds recomputed over the
area (ascending) with the decided-out members no longer maybe-stored. Every
value is at most the bounds of exactly that maybe-stored set (`boundsStep` is
monotone and the start is pointwise below). -/
def SCtx.rebound (cx : SCtx) (ms : Array Bool) : UBounds :=
  cx.area.foldl (boundsStep cx.up.prep cx.up.w ms) cx.bounds0

/-- Visible counts of the area nodes under a maybe-stored set, recomputed
from their parents (descending); other terms keep their root-level counts. -/
def SCtx.revisible (cx : SCtx) (ms : Array Bool) : Std.HashMap Nat (Nat × Nat) := Id.run do
  let mut vis : Std.HashMap Nat (Nat × Nat) := {}
  for k in [0:cx.area.size] do
    let j := cx.area.size - 1 - k
    let y := cx.area[j]!
    let r := cx.rootOcc[j]!
    let mut d := r
    let mut h := r
    for (q, mA, mH) in cx.inEdges[j]! do
      let wq :=
        if ms[q]! then 1
        else min ((vis.get? q).map (·.1) |>.getD cx.vis0.1[q]!) visibleCap
      d := d + mA * wq
      h := h + mH * wq
    vis := vis.insert y (d, h)
  return vis

/-- Whether a decided-stored term costs exactly `w` wherever it occurs and
ends every telescope running into it, under bounds `b`. -/
def SCtx.opaqueUnder (cx : SCtx) (b : UBounds) (t : Nat) : Bool :=
  if cx.up.prep.family[t]! == .none then b.inlineLB[t]! ≥ cx.up.w
  else b.mergedLB[t]! ≥ cx.up.w

/-- Groups of the undecided members: joined by DAG paths whose intermediate
terms are not opaque, and below a common non-opaque decided-stored term. -/
def SCtx.groups (cx : SCtx) (opq : Nat → Bool) (availFixed : Nat → Bool) (und : Array Nat) :
    Array (Array Nat) := Id.run do
  let undSet : Std.HashSet Nat := und.foldl (·.insert ·) {}
  let mut uf : Array Nat := Array.range cx.members.size
  let mut reps : Array (Array Nat) := Array.replicate cx.area.size #[]
  for j in [0:cx.area.size] do
    let y := cx.area[j]!
    if opq y then continue
    let mut rs : Array Nat := #[]
    for c in (cx.up.prep.dag.node y).children do
      match cx.areaIdx.get? c with
      | none => pure ()
      | some jc =>
        for r in reps[jc]! do
          let fr := ufFind uf r
          unless rs.contains fr do rs := rs.push fr
    if undSet.contains y then
      let iy := cx.memberIdx.getD y 0
      for r in rs do
        let a := ufFind uf iy
        let b := ufFind uf r
        if a != b then
          if a < b then uf := uf.set! b a else uf := uf.set! a b
      reps := reps.set! j #[ufFind uf iy]
    else if availFixed y && rs.size > 1 then
      for r in rs do
        let a := ufFind uf rs[0]!
        let b := ufFind uf r
        if a != b then
          if a < b then uf := uf.set! b a else uf := uf.set! a b
      reps := reps.set! j #[ufFind uf rs[0]!]
    else
      reps := reps.set! j rs
  let mut groups : Std.HashMap Nat (Array Nat) := {}
  for t in und do
    let r := ufFind uf (cx.memberIdx.getD t 0)
    groups := groups.insert r ((groups.getD r #[]).push t)
  let gs := groups.toArray.map fun (_, g) => g.qsort (· < ·)
  return gs.qsort fun a b => a[0]! < b[0]!

/-- Memo key of a group: its members and the decisions that can change the
group's `Δ`, each as `3·t + code` (code 0 not stored, 1 stored, 2 stored
and opaque). Those are the decided members joined to a group member by a
directed DAG path (up or down) whose intermediate terms are not opaque, and
the decided members below (through non-opaque terms) a stored, non-opaque
ancestor reached that way, whose `min(w, ·)` couples its subterms. Any other
decision is reached only through ancestors whose cost it enters additively.
Also returns the set of those decided members. -/
def SCtx.memoKey (cx : SCtx) (opq : Nat → Bool) (inSet outSet : Std.HashSet Nat)
    (g : Array Nat) : Array Nat × Std.HashSet Nat := Id.run do
  let n := cx.up.prep.dag.size
  let mut entries : Array Nat := #[]
  let mut rel : Std.HashSet Nat := {}
  -- Up from the group; stored non-opaque ancestors also start a down search.
  let mut downStart := g
  let mut seen : Std.HashSet Nat := g.foldl (·.insert ·) {}
  let mut stack := g
  for _ in [0:cx.area.size + 1] do
    match stack.back? with
    | none => break
    | some y =>
      stack := stack.pop
      for q in cx.facts.parents[y]! do
        if !cx.areaIdx.contains q || seen.contains q then continue
        seen := seen.insert q
        if outSet.contains q then
          entries := entries.push (3 * q)
          rel := rel.insert q
        else if inSet.contains q then
          entries := entries.push (3 * q + (if opq q then 2 else 1))
          rel := rel.insert q
          unless opq q do downStart := downStart.push q
        unless opq q do stack := stack.push q
  -- Down through non-opaque terms.
  seen := downStart.foldl (·.insert ·) {}
  stack := downStart
  for _ in [0:cx.area.size + 1] do
    match stack.back? with
    | none => break
    | some y =>
      stack := stack.pop
      for c in (cx.up.prep.dag.node y).children do
        if !cx.areaIdx.contains c || seen.contains c then continue
        seen := seen.insert c
        if !rel.contains c then
          if outSet.contains c then
            entries := entries.push (3 * c)
            rel := rel.insert c
          else if inSet.contains c then
            entries := entries.push (3 * c + (if opq c then 2 else 1))
            rel := rel.insert c
        unless opq c do stack := stack.push c
  return (g ++ #[3 * n + 3] ++ entries.qsort (· < ·), rel)

/-- One step of the search accounting. -/
def SCtx.charge (limits : Limits) (work : Nat) : SM Unit := do
  let st ← get
  if st.states + 1 > limits.maxStates then
    throw (.resourceExhausted .states limits.maxStates)
  if st.costEvals + work > limits.maxCostEvals then
    throw (.resourceExhausted .costEvals limits.maxCostEvals)
  set { st with states := st.states + 1, costEvals := st.costEvals + work }

mutual
/-- Exact table of a group under the decided sets `inAll`/`outAll` (members
of the component decided stored / not stored outside the group): for each
count, the best `Δ` within `slack` of the group's best, where `Δ` is the
change of the component cost from leaving the whole group unstored. -/
def SCtx.solve (cx : SCtx) (limits : Limits) :
    Nat → Array Nat → Array Nat → Array Nat → SM CTable
  | 0, _, _, _ => throw (.internal "component search fuel exhausted")
  | fuel + 1, g, inAll, outAll => do
    let ms := outAll.foldl (fun acc t => acc.set! t false) cx.cand
    let b := cx.rebound ms
    let inSet : Std.HashSet Nat := inAll.foldl (·.insert ·) {}
    let outSet : Std.HashSet Nat := outAll.foldl (·.insert ·) {}
    let opq := fun t => cx.up.opaq[t]! || (inSet.contains t && cx.opaqueUnder b t)
    let (key, _) := cx.memoKey opq inSet outSet g
    if let some tb := (← get).memo.get? key then
      modify fun st => { st with memoHits := st.memoHits + 1 }
      return tb
    let (phi0, work) := cx.phi (fun t => inSet.contains t) inAll
    SCtx.charge limits (work + cx.area.size)
    let tb ← cx.node limits fuel phi0 inAll outAll outAll.size #[] g #[]
    let tb := tb.trim cx.slack
    modify fun st => { st with memo := st.memo.insert key tb }
    return tb

/-- Branch-and-bound node of a group: `localIn` are the group's members
decided stored, `und` the undecided ones, `tb` the table so far. -/
def SCtx.node (cx : SCtx) (limits : Limits) :
    Nat → Nat → Array Nat → Array Nat → Nat → Array Nat → Array Nat → CTable → SM CTable
  | 0, _, _, _, _, _, _, _ => throw (.internal "component search fuel exhausted")
  | fuel + 1, phi0, inCtx, outAll, nOutCtx, localIn, und, tb => do
    -- Reclassify: an undecided member whose gain under this partial
    -- assignment reaches the threshold is stored in every minimum that
    -- respects it.
    let ms := outAll.foldl (fun acc t => acc.set! t false) cx.cand
    let b := cx.rebound ms
    let vis := cx.revisible ms
    let gains := und.map fun t =>
      let (d, h) := vis.getD t (cx.vis0.1[t]!, cx.vis0.2[t]!)
      (t, storedGainC cx.up.prep b cx.up.w t d h)
    let forced := (gains.filter (·.2 ≥ cx.theta)).map (·.1)
    let localIn := if forced.isEmpty then localIn else mergeSorted localIn forced
    let open_ := gains.filter (·.2 < cx.theta)
    let und := open_.map (·.1)
    let inAll := inCtx ++ localIn
    let inSet : Std.HashSet Nat := inAll.foldl (·.insert ·) {}
    let undSet : Std.HashSet Nat := und.foldl (·.insert ·) {}
    -- Lower bound: every undecided member available, its entry free.
    let (phi, work) := cx.phi (fun t => inSet.contains t || undSet.contains t) inAll
    SCtx.charge limits (work + 2 * cx.area.size)
    let delta : _root_.Int := (phi : _root_.Int) - (phi0 : _root_.Int)
    if und.isEmpty then return tb.add (delta, localIn)
    if let some bd := tb.best then
      if delta > bd + (cx.slack : _root_.Int) then return tb
    -- Split into independent groups.
    let opq := fun t => cx.up.opaq[t]! || (inSet.contains t && cx.opaqueUnder b t)
    let availFixed := fun t => inSet.contains t && !opq t
    let groups := cx.groups opq availFixed und
    -- Hand a single group to the memoized solver when a decision of this
    -- solve no longer reaches it.
    let route :=
      if groups.size > 1 then true
      else if groups.size == 1 then
        let outSet : Std.HashSet Nat := outAll.foldl (·.insert ·) {}
        let (_, rel) := cx.memoKey opq inSet outSet groups[0]!
        localIn.any (!rel.contains ·) || (outAll.extract nOutCtx outAll.size).any (!rel.contains ·)
      else false
    if route then
      let (phiNone, work) := cx.phi (fun t => inSet.contains t) inAll
      SCtx.charge limits work
      let base : _root_.Int := (phiNone : _root_.Int) - (phi0 : _root_.Int)
      let mut comb : CTable := #[some (base, localIn)]
      for grp in groups do
        let sub ← cx.solve limits fuel grp inAll outAll
        comb := (comb.conv sub).trim cx.slack
      return comb.foldl (fun acc o => match o with
        | some e => acc.add e
        | none => acc) tb
    -- Branch on the largest |gain|, "stored" first when it is positive.
    let some (t, gt) := pickBranch open_ | return tb
    let und' := und.erase t
    let inBranch := fun tb => cx.node limits fuel phi0 inCtx outAll nOutCtx (mergeSorted localIn #[t]) und' tb
    let outBranch := fun tb => cx.node limits fuel phi0 inCtx (outAll.push t) nOutCtx localIn und' tb
    if gt > 0 then
      let tb ← inBranch tb
      outBranch tb
    else
      let tb ← outBranch tb
      inBranch tb
end

/-- Result of one component search. -/
structure CompResult where
  members : Array Nat
  bestDelta : _root_.Int
  bestSet : Array Nat
  bySize : Array (Option (_root_.Int × Array Nat))
  deriving Inhabited

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

/-- First count with the same `Tag0` width as `k`. -/
def tag0BracketStart (k : Nat) : Nat :=
  if k < 128 then 0 else if k < 256 then 128 else 256 ^ (natByteCount k - 1)

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

/-- Classify, search every component and combine: the stored set and its
model length. -/
def uniformChoose (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep) :
    Except SharingError UniformChoice := do
  let n := ex.dag.size
  let f := graphFacts ex.dag ex.roots
  let cand := searchCandidates p f w
  let b0 := uniformBounds p w cand
  let vis0 := visibleCounts ex.dag ex.roots cand
  -- The certain-stored threshold: 2 always holds (the table count grows by at
  -- most one byte); 1 holds when every minimum lies in one count bracket
  -- (it contains the gain-2 terms and only candidates).
  let cls2 := classifyWith p f w b0 vis0 2
  let nCs2 := (cls2.filter (· == .certainStored)).size
  let nCand := (cand.filter id).size
  let theta : _root_.Int := if tag0Size nCand == tag0Size nCs2 then 1 else 2
  let cls := if theta == 1 then classifyWith p f w b0 vis0 1 else cls2
  let pick (c : UClass) := (Array.range n).filter (cls[·]! == c)
  let cs := pick .certainStored
  let ce := pick .certainExcluded
  let unc := pick .uncertain
  let low := pick .lowDegree
  let opaq := cs.foldl (fun acc t => acc.set! t true) (Array.replicate n false)
  let up := UPrep.mk' p w opaq
  let comps := uncertainComponents ex.dag cls
  -- Largest table-count difference between two sets that contain the
  -- certain-stored terms and only candidates.
  let slack := tag0Size (cs.size + unc.size) - tag0Size cs.size
  -- Search each component.
  let mut results : Array CompResult := #[]
  let mut states := 0
  let mut costEvals := 0
  for members in comps do
    let area := componentArea up f members
    let areaSet : Std.HashSet Nat := area.foldl (·.insert ·) {}
    let mut rootMult : Std.HashMap Nat Nat := {}
    for r in ex.roots do
      if areaSet.contains r then rootMult := rootMult.insert r (rootMult.getD r 0 + 1)
    let rootArr := rootMult.toArray.qsort (fun a b => a.1 < b.1)
    let storedIn := area.filter (opaq[·]!)
    if limits.uniformSubsetSearch then
      let cx0 : CompCtx :=
        { up := up, members := members, area := area, rootMult := rootArr,
          storedIn, phi0 := 0, slack := slack }
      let (phi0, _) := cx0.phi (fun _ => false) #[]
      let cx := { cx0 with phi0 }
      let st0 : CompState := { states, costEvals }
      let ((), st) ← (cx.dfs limits (members.size + 2) 0 #[]).run st0
      states := st.states
      costEvals := st.costEvals
      let some (bd, bs) := st.best | throw (.internal "component search found no choice")
      results := results.push { members, bestDelta := bd, bestSet := bs, bySize := st.bySize }
    else
      let areaIdx : Std.HashMap Nat Nat :=
        (Array.range area.size).foldl (fun acc j => acc.insert area[j]! j) {}
      let memberIdx : Std.HashMap Nat Nat :=
        (Array.range members.size).foldl (fun acc j => acc.insert members[j]! j) {}
      let inEdges := area.map fun y =>
        f.parents[y]!.map fun q =>
          let node := ex.dag.node q
          (List.range node.children.size).foldl (fun (acc : Nat × Nat × Nat) i =>
            if node.child i == y then
              (q, acc.2.1 + 1,
               acc.2.2 + (if continuationEdge node i (ex.dag.node y) then 0 else 1))
            else acc) (q, 0, 0)
      let rootOcc := area.map fun y => rootMult.getD y 0
      let cx : SCtx :=
        { up, facts := f, cand, bounds0 := b0, vis0, members, memberIdx, area, areaIdx,
          inEdges, rootOcc, rootMult := rootArr, storedIn, slack, theta }
      let st0 : SState := { states, costEvals }
      let (tb, st) ← (cx.solve limits (4 * members.size + 4) members #[] #[]).run st0
      states := st.states
      costEvals := st.costEvals
      let some bd := tb.best | throw (.internal "component search found no choice")
      let bestSet := tb.foldl (init := (none : Option (Array Nat))) fun acc o =>
        match o with
        | some (d, s) =>
          if d == bd then
            match acc with
            | none => some s
            | some a => if setPrec s a then some s else acc
          else acc
        | none => acc
      let some bs := bestSet | throw (.internal "component search found no choice")
      results := results.push { members, bestDelta := bd, bestSet := bs, bySize := tb }
  -- Combine: per-component optima, unless a lower count bracket is shorter.
  let kCS := cs.size
  let bestX := results.foldl (fun acc r => mergeSorted acc r.bestSet) #[]
  let bestDelta := results.foldl (fun acc r => acc + r.bestDelta) (0 : _root_.Int)
  let k0 := kCS + bestX.size
  let mut chosenX := bestX
  let mut chosenDelta := bestDelta
  let mut lowerBracket := false
  let start := tag0BracketStart k0
  if start > kCS then
    let cap := start - 1 - kCS
    if (results.size + 1) * (cap + 1) > limits.maxStates then
      throw (.resourceExhausted .states limits.maxStates)
    -- dp[c]: best (Δ, set) with c chosen terms, over the components so far.
    let mut dp : Array (Option (_root_.Int × Array Nat)) :=
      #[some (0, #[])] ++ Array.replicate cap none
    for r in results do
      let mut ndp : Array (Option (_root_.Int × Array Nat)) := Array.replicate (cap + 1) none
      for h : c in [0:dp.size] do
        let some (d, s) := dp[c] | continue
        for h2 : k in [0:r.bySize.size] do
          let some (dk, sk) := r.bySize[k] | continue
          if c + k > cap then continue
          let cand : _root_.Int × Array Nat := (d + dk, mergeSorted s sk)
          let better := match ndp[c + k]! with
            | none => true
            | some (d0, s0) => cand.1 < d0 || (cand.1 == d0 && setPrec cand.2 s0)
          if better then ndp := ndp.set! (c + k) (some cand)
      dp := ndp
    for h : c in [0:dp.size] do
      let some (d, s) := dp[c] | continue
      let l : _root_.Int := d + (tag0Size (kCS + c) : _root_.Int)
      let l0 : _root_.Int := chosenDelta + (tag0Size (kCS + chosenX.size) : _root_.Int)
      if l < l0 || (l == l0 && setPrec s chosenX) then
        chosenX := s
        chosenDelta := d
        lowerBracket := true
  -- Model length from the truncated evaluation.
  let baseRoots := ex.roots.foldl (fun acc r => acc + up.base[r]!.cost) 0
  let baseStored := cs.foldl (fun acc c => acc + up.base[c]!.inl) 0
  let modelInt : _root_.Int := (baseRoots + baseStored : Nat) + chosenDelta +
    (tag0Size (kCS + chosenX.size) : _root_.Int)
  if modelInt < 0 then throw (.internal "negative model length")
  let model := modelInt.toNat
  if model > limits.maxOutputBytes then
    throw (.resourceExhausted .outputBytes limits.maxOutputBytes)
  return { facts := f, certainStored := cs, certainExcluded := ce, uncertain := unc,
           lowDegree := low, components := comps, stored := mergeSorted cs chosenX, model,
           states, costEvals, lowerBracket }

/-- Materialize a chosen set in the pinned order with the real evaluation, and
check it against the model length and the input. -/
def uniformFinish (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep) (c : UniformChoice) :
    Except SharingError UniformSharingResult := do
  let n := ex.dag.size
  let stored := c.stored
  let model := c.model
  unless stored.all (· < n) do
    throw (.internal "stored term out of range")
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

/-- Exact uniform-width optimization of an expanded input. -/
def optimizeUniformExpanded (w : Nat) (limits : Limits) (ex : Expanded) :
    Except SharingError UniformSharingResult := do
  if w == 0 then throw (.formatBound "uniform Share width" 0)
  unless childrenPrecede ex.dag.nodes do
    throw (.internal "DAG children do not precede their parents")
  unless ex.dag.nodes.all (fun node => node.children.size == node.head.arity) do
    throw (.internal "DAG node arity")
  unless ex.roots.all (· < ex.dag.size) do
    throw (.internal "root ID out of range")
  let p := Prep.ofDag ex.dag
  let c ← uniformChoose w limits ex p
  uniformFinish w limits ex p c

end Ix.Sharing.Exact

end
