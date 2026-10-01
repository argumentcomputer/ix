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
    candidate when `g ≥ 2`, with
    `b` a lower bound on the bytes of `t` inside a telescope that runs
    through it (excluding the header):
      non-telescope:           g = (deg-1)·inl⁻ - deg·w
      telescope, headDeg ≥ 1:  g = (deg-1)·b + (headDeg-1) - deg·w
      telescope, headDeg = 0:  g = (deg-1)·b - tag4Size(spine length) - deg·w
    Exchange: in a candidate-only minimum `E` not storing `t`, every parent is written
    inline at least once, so `t` has at least `deg` inline occurrences, at
    least `headDeg` at head positions. Add the entry `t` (its optimal body,
    which costs exactly what one head occurrence costs, or at most one
    continuation occurrence plus its header `≤ tag4Size(spine length)`), and
    replace `deg` occurrences, including `headDeg` heads, by `Share(t)`:
    descendants lose occurrences, ancestors get a `w`-byte leaf where the
    subtree was, telescopes only shorten. The table count grows by at most 1
    byte. So the length drops by at least `g - 1 > 0`, contradicting
    minimality. The bounds `inl⁻`, `b` are computed bottom-up with every
    candidate child priced at `min(w, ·)` (it might be stored), every other
    child at its inline bound, and a header of at least 1 byte.
  * UNCERTAIN: the remaining candidates.

  ## Certain-stored terms are opaq
  `g ≥ 2` forces `b ≥ w` (and `inl⁻ > w`), so in every candidate encoding a
  certain-stored term costs exactly `w` wherever it occurs, and a telescope
  running into it is never shorter than one cut there. Costs above it are
  therefore computed with it as a `w`-byte leaf that ends the spine; this
  truncated evaluation equals the real one (checked on the output).

  ## Components
  Two uncertain terms are connected when a DAG path joins them without
  passing through a certain-stored term. Every cost is then a sum of
  functions of the chosen terms of one component each: children add; a
  telescope's minimum over cut options couples a cut node only with the
  terms below it; a term's own Share option couples it with the terms below
  it. So each component is searched independently (branch and bound over
  subsets with the lower bound "every undecided term available, its entry
  free"). The table-count prefix is the only coupling: when the combined
  choice reaches 128 entries or more, a small knapsack over components
  checks whether a lower count bracket is at least as short.

  ## Tie-break
  Among minimum-length sets the least one in the order "the smaller
  structural ID in the symmetric difference is not stored". Components and
  the bracket knapsack preserve this order exactly.
-/
module

public import Ix.Sharing.Exact.Search

public section

namespace Ix.Sharing.Exact

open Ixon

/-! ## Graph facts -/

/-- Whether the edge from `parent` to its `i`-th child continues the parent's
telescope. -/
def continuationEdge (parent : Node) (i : Nat) (child : Node) : Bool :=
  match parent.head, child.head with
  | .app, .app => i == 0
  | .lam _, .lam _ => i == 1
  | .all .., .all .. => i == 1
  | _, _ => false

/-- In-degrees, head in-degrees, occurrences and parent lists. -/
structure GraphFacts where
  deg : Array Nat
  headDeg : Array Nat
  occ : Array Nat
  parents : Array (Array Nat)
  deriving Inhabited

def graphFacts (dag : Dag) (roots : Array Nat) : GraphFacts := Id.run do
  let n := dag.size
  let mut deg : Array Nat := Array.replicate n 0
  let mut hd : Array Nat := Array.replicate n 0
  let mut parents : Array (Array Nat) := Array.replicate n #[]
  for r in roots do
    deg := deg.modify r (· + 1)
    hd := hd.modify r (· + 1)
  for t in [0:n] do
    let node := dag.node t
    for h : i in [0:node.children.size] do
      let c := node.children[i]
      deg := deg.modify c (· + 1)
      unless continuationEdge node i (dag.node c) do hd := hd.modify c (· + 1)
      unless (parents[c]!).contains t do parents := parents.modify c (·.push t)
  return { deg, headDeg := hd, occ := occurrences dag roots, parents }

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

def uniformBounds (p : Prep) (w : Nat) (maybeStored : Array Bool) : UBounds := Id.run do
  let n := p.dag.size
  let mut inl : Array Nat := Array.replicate n 0
  let mut merged : Array Nat := Array.replicate n 0
  let mut headLB : Array Nat := Array.replicate n 0
  let mut contLB : Array Nat := Array.replicate n 0
  for t in [0:n] do
    let node := p.dag.node t
    let fam := p.family[t]!
    let (i, m) :=
      if fam == .none then
        let i := node.children.foldl (fun acc c => acc + headLB[c]!) node.head.ownBytes
        (i, i)
      else
        let nxt := node.spineNext
        let rest := if p.family[nxt]! == fam then contLB[nxt]! else headLB[nxt]!
        let m := node.sideExtra + headLB[node.sideChild]! + rest
        (1 + m, m)
    inl := inl.set! t i
    merged := merged.set! t m
    headLB := headLB.set! t (if maybeStored[t]! then min w i else i)
    contLB := contLB.set! t (if maybeStored[t]! then min w m else m)
  return { inlineLB := inl, mergedLB := merged, headLB, contLB }

/-- The certain-stored gain bound `g` of a term (see the module doc). -/
def storedGain (p : Prep) (f : GraphFacts) (b : UBounds) (w t : Nat) : _root_.Int :=
  let deg := _root_.Int.ofNat f.deg[t]!
  let wI := _root_.Int.ofNat w
  if p.family[t]! == .none then
    (deg - 1) * _root_.Int.ofNat b.inlineLB[t]! - deg * wI
  else if f.headDeg[t]! ≥ 1 then
    (deg - 1) * _root_.Int.ofNat b.mergedLB[t]! + (_root_.Int.ofNat f.headDeg[t]! - 1) - deg * wI
  else
    (deg - 1) * _root_.Int.ofNat b.mergedLB[t]! - _root_.Int.ofNat (tag4Size p.spineLen[t]!) - deg * wI

/-- Classify every term. -/
def classify (p : Prep) (f : GraphFacts) (w : Nat) : Array UClass := Id.run do
  let n := p.dag.size
  let ce : Array Bool := (Array.range n).map fun t =>
    (f.occ[t]! - 1) * p.base[t]! < f.occ[t]! * w
  -- Only search candidates (in-degree ≥ 2, not certain-excluded) can be
  -- stored in the encodings the search ranges over.
  let cand : Array Bool := (Array.range n).map fun t => !ce[t]! && f.deg[t]! ≥ 2
  let b := uniformBounds p w cand
  return (Array.range n).map fun t =>
    if ce[t]! then .certainExcluded
    else if f.deg[t]! < 2 then .lowDegree
    else if storedGain p f b w t ≥ 2 then .certainStored
    else .uncertain

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

/-- Pinned table order of a stored set: stored descendants first; among
ready terms the larger in-degree first, then the smaller ID. -/
def pinnedOrder (dag : Dag) (deg : Array Nat) (stored : Array Nat) : Array Nat := Id.run do
  let n := dag.size
  let isStored := stored.foldl (fun acc t => acc.set! t true) (Array.replicate n false)
  -- Nearest stored descendants of each stored term.
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
  return pinnedPlace deg deps stored.size #[] stored {}

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
  let cls := classify p f w
  let pick (c : UClass) := (Array.range n).filter (cls[·]! == c)
  let cs := pick .certainStored
  let ce := pick .certainExcluded
  let unc := pick .uncertain
  let low := pick .lowDegree
  let opaq := cs.foldl (fun acc t => acc.set! t true) (Array.replicate n false)
  let up := UPrep.mk' p w opaq
  let comps := uncertainComponents ex.dag cls
  let slack := tag0Size (cs.size + unc.size) - 1
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
    let cx0 : CompCtx :=
      { up := up, members := members, area := area, rootMult := rootArr,
        storedIn := area.filter (opaq[·]!), phi0 := 0, slack := slack }
    let (phi0, _) := cx0.phi (fun _ => false) #[]
    let cx := { cx0 with phi0 }
    let st0 : CompState := { states, costEvals }
    let ((), st) ← (cx.dfs limits (members.size + 2) 0 #[]).run st0
    states := st.states
    costEvals := st.costEvals
    let some (bd, bs) := st.best | throw (.internal "component search found no choice")
    results := results.push { members, bestDelta := bd, bestSet := bs, bySize := st.bySize }
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
  let p := Prep.ofDag ex.dag
  let c ← uniformChoose w limits ex p
  uniformFinish w limits ex p c

end Ix.Sharing.Exact

end
