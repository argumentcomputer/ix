/-
  Exact minimum sharing under a uniform reference width: the compiled
  component search.

  `searchComponentsWith` (the component loop of `searchComponents`) is the
  specification; `searchComponentsWithFast` computes it with work bounded by
  the components' areas and closures instead of the DAG's size, and
  `searchComponentsWith_eq_fast` (`@[csimp]`) proves the two equal for every
  input, so compiled code runs the fast loop while every theorem about the
  search keeps talking about the specification.
-/
module

public import Ix.Sharing.Exact.UniformSearch
import all Ix.Sharing.Exact.Basic
import all Ix.Sharing.Exact.Dag
import all Ix.Sharing.Exact.Dictionary
import all Ix.Sharing.Exact.UniformSearch

public section

namespace Ix.Sharing.Exact

open Ixon

/-! ## Area- and closure-local values

The search of `Ix.Sharing.Exact.UniformSearch` recomputes, at every node,
tables of the DAG's size
(`SCtx.rebound`, `SCtx.revisible`, `SCtx.opaqueArr`, `SCtx.sepCheck`,
`SCtx.phiE`), each from an n-sized array held by the context, so each node
costs Θ(n); and `mkSCtx` scans the whole DAG for every component. The
versions below compute the same values over the component's area (or its
closure) only, read every other term from the root-level tables, and find the
closure by an upward walk; `searchComponentsWith_eq_fast` attaches them to the
specification `searchComponentsWith`.

Position tables: `pos[t]! = j + 1` when `t` is the `j`-th term of the area
(closure), `0` otherwise. -/

/-- The position recorded for `u` in a position table. -/
@[inline] def posOf (pos : Array Nat) (u : Nat) : Option Nat :=
  let p := pos[u]!
  if p == 0 then none else some (p - 1)

/-- A field of the local value at `u`: of the entry at `u`'s position when that
is below `L.size`, else `base u`. -/
@[inline] def readAtF {α β : Type} [Inhabited α] (posf : Nat → Option Nat) (L : Array α)
    (proj : α → β) (base : Nat → β) (u : Nat) : β :=
  match posf u with
  | some j => if j < L.size then proj L[j]! else base u
  | none => base u

/-- The local values of a fold over the terms `xsAt 0, …, xsAt (k - 1)`: entry
`i` is `G` of the entries before it. -/
@[inline] def localFold {α : Type} (k : Nat) (xsAt : Nat → Nat)
    (G : Array α → Nat → Nat → α) : Array α :=
  foldRange (fun L i => L.push (G L i (xsAt i))) 0 k (Array.mkEmpty k)

/-- `cutScan` with readers for the spine sums, the descendant links and the
widths. -/
@[specialize] def cutScanG (spineLen : Array Nat) (getS : Nat → Nat) (getB : Nat → Option Nat)
    (widthG : Nat → Option Nat) (l s : Nat) : Nat → Option Nat → Nat → Nat → Nat × Nat
  | 0, _, best, work => (best, work)
  | _ + 1, none, best, work => (best, work)
  | fuel + 1, some u, best, work =>
    let cand := tag4Size (l - spineLen[u]!) + (s - getS u) + (widthG u).getD 0
    cutScanG spineLen getS getB widthG l s fuel (getB u) (if cand < best then cand else best)
      (work + 1)

/-- The row (cost, spine sum, descendant link) that `evalStep` writes at an
affected term `t`, from readers of the evaluation before it. -/
@[inline] def evalRowG (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (widthG : Nat → Option Nat) (getC getS : Nat → Nat) (getB : Nat → Option Nat) (t : Nat) :
    Nat × Nat × Option Nat :=
  let node := dag.node t
  let fam := family[t]!
  if fam == .none then
    let inl := node.children.foldl (fun acc c => acc + getC c) node.head.ownBytes
    let c := match widthG t with
      | some w => min inl w
      | none => inl
    (c, getS t, getB t)
  else
    let nxt := node.spineNext
    let same := family[nxt]! == fam
    let s := node.sideExtra + getC node.sideChild + (if same then getS nxt else 0)
    let bl : Option Nat :=
      if same then (if (widthG nxt).isSome then some nxt else getB nxt) else none
    let l := spineLen[t]!
    let inl := (cutScanG spineLen (fun u => if u = t then s else getS u)
      (fun u => if u = t then bl else getB u) widthG l s l bl
      (tag4Size l + s + getC tail[t]!) 0).1
    let c := match widthG t with
      | some w => min inl w
      | none => inl
    (c, s, bl)

/-- `evalHidden` with readers (`inb`: the term is inside the tables). -/
@[inline] def evalHiddenG (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (widthG : Nat → Option Nat) (aff inb : Bool) (getC getS : Nat → Nat)
    (getB : Nat → Option Nat) (t : Nat) : Nat :=
  if aff then
    let node := dag.node t
    let fam := family[t]!
    if fam == .none then
      if inb then node.children.foldl (fun acc c => acc + getC c) node.head.ownBytes
      else getC t
    else
      let nxt := node.spineNext
      let same := family[nxt]! == fam
      let s := node.sideExtra + getC node.sideChild + (if same then getS nxt else 0)
      let bl : Option Nat :=
        if same then
          (if (if nxt = t then none else widthG nxt).isSome then some nxt else getB nxt)
        else none
      let l := spineLen[t]!
      if inb then
        (cutScanG spineLen (fun u => if u = t then s else getS u)
          (fun u => if u = t then bl else getB u) (fun u => if u = t then none else widthG u)
          l s l bl (tag4Size l + s + getC tail[t]!) 0).1
      else getC t
  else getC t

/-- The width of `u` when the members satisfying `avail` are added at width
`w` to `widthCs` (the dictionary of `SCtx.phiE`). -/
@[inline] def phiWidth (cx : SCtx) (avail : Nat → Bool) (u : Nat) : Option Nat :=
  if decide (u < cx.widthCs.size) && cx.members.contains u && avail u then some cx.up.w
  else widthOf cx.widthCs u

/-- The closure-local evaluation of `SCtx.phiE` (by closure position). -/
def phiTable (cx : SCtx) (posC : Array Nat) (avail : Nat → Bool) :
    Array (Nat × Nat × Option Nat) :=
  let p := cx.up.prep
  let base := cx.baseEv
  localFold cx.closure.size (cx.closure[·]!) fun L _ t =>
    if cx.allTrue[t]! then
      evalRowG p.dag p.family p.spineLen p.tail (phiWidth cx avail)
        (readAtF (posOf posC) L (·.1) (base.cost[·]!))
        (readAtF (posOf posC) L (·.2.1) (base.sides[·]!))
        (readAtF (posOf posC) L (·.2.2) (base.below[·]!)) t
    else (base.cost[t]!, base.sides[t]!, base.below[t]!)

/-- The component cost of `SCtx.phiE` from the closure-local evaluation. -/
def phiEL (cx : SCtx) (posC : Array Nat) (avail : Nat → Bool) (stored : Array Nat) :
    Nat × Nat :=
  let p := cx.up.prep
  let base := cx.baseEv
  let L := phiTable cx posC avail
  let getC := readAtF (posOf posC) L (·.1) (base.cost[·]!)
  let getS := readAtF (posOf posC) L (·.2.1) (base.sides[·]!)
  let getB := readAtF (posOf posC) L (·.2.2) (base.below[·]!)
  let inl := fun x => evalHiddenG p.dag p.family p.spineLen p.tail (phiWidth cx avail)
    cx.allTrue[x]! (decide (x < base.cost.size)) getC getS getB x
  let roots := cx.rootsC.foldl (fun acc r => acc + getC r) 0
  let baseSum := cx.storedInC.foldl (fun acc c => acc + inl c) 0
  let entries := stored.foldl (fun acc x => acc + inl x) 0
  (roots + baseSum + entries, cx.closure.size + stored.size)

/-! The search runs `phiEL2`, which computes `phiEL` (`phiEL2_eq`) without
allocating a row per closure term: three tables in place of one table of
triples, the scan's best cost without its work count (`cutScanBest`), and the
widths read through flags over the area positions (`memberFlags`) in place of
a scan of the members per read. -/

/-- The best cost of `cutScanG` (without the work count). -/
@[specialize] def cutScanBest (spineLen : Array Nat) (getS : Nat → Nat)
    (getB : Nat → Option Nat) (widthG : Nat → Option Nat) (l s : Nat) :
    Nat → Option Nat → Nat → Nat
  | 0, _, best => best
  | _ + 1, none, best => best
  | fuel + 1, some u, best =>
    let cand := tag4Size (l - spineLen[u]!) + (s - getS u) + (widthG u).getD 0
    cutScanBest spineLen getS getB widthG l s fuel (getB u) (if cand < best then cand else best)

/-- `evalRowG` with `cutScanBest`. -/
@[inline] def evalRowB (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (widthG : Nat → Option Nat) (getC getS : Nat → Nat) (getB : Nat → Option Nat) (t : Nat) :
    Nat × Nat × Option Nat :=
  let node := dag.node t
  let fam := family[t]!
  if fam == .none then
    let inl := node.children.foldl (fun acc c => acc + getC c) node.head.ownBytes
    let c := match widthG t with
      | some w => min inl w
      | none => inl
    (c, getS t, getB t)
  else
    let nxt := node.spineNext
    let same := family[nxt]! == fam
    let s := node.sideExtra + getC node.sideChild + (if same then getS nxt else 0)
    let bl : Option Nat :=
      if same then (if (widthG nxt).isSome then some nxt else getB nxt) else none
    let l := spineLen[t]!
    let inl := cutScanBest spineLen (fun u => if u = t then s else getS u)
      (fun u => if u = t then bl else getB u) widthG l s l bl (tag4Size l + s + getC tail[t]!)
    let c := match widthG t with
      | some w => min inl w
      | none => inl
    (c, s, bl)

/-- Flags over the area positions: the members satisfying `avail`. -/
def memberFlags (cx : SCtx) (posA : Array Nat) (avail : Nat → Bool) : Array Bool :=
  cx.members.foldl (fun fl m => match posOf posA m with
    | some j => if avail m then fl.set! j true else fl
    | none => fl) (Array.replicate cx.area.size false)

/-- The widths of `SCtx.phiE` read through member flags `fl`. -/
@[inline] def flagWidth (cx : SCtx) (posA : Array Nat) (fl : Array Bool) (u : Nat) :
    Option Nat :=
  match posOf posA u with
  | some j => if fl[j]! then some cx.up.w else widthOf cx.widthCs u
  | none => widthOf cx.widthCs u

/-- The row of `phiTable3` at `t`, from the three tables so far. -/
@[inline] def phiRow3 (cx : SCtx) (posA posC : Array Nat) (fl : Array Bool) (Lc Ls : Array Nat)
    (Lb : Array (Option Nat)) (t : Nat) : Nat × Nat × Option Nat :=
  let p := cx.up.prep
  let base := cx.baseEv
  if cx.allTrue[t]! then
    evalRowB p.dag p.family p.spineLen p.tail (flagWidth cx posA fl)
      (readAtF (posOf posC) Lc id (base.cost[·]!))
      (readAtF (posOf posC) Ls id (base.sides[·]!))
      (readAtF (posOf posC) Lb id (base.below[·]!)) t
  else (base.cost[t]!, base.sides[t]!, base.below[t]!)

/-- `phiTable` as three tables (costs, spine sums, descendant links). -/
def phiTable3 (cx : SCtx) (posA posC : Array Nat) (fl : Array Bool) :
    Array Nat × Array Nat × Array (Option Nat) :=
  let k := cx.closure.size
  foldRange (fun (st : Array Nat × Array Nat × Array (Option Nat)) i =>
    match st with
    | (Lc, Ls, Lb) =>
      match phiRow3 cx posA posC fl Lc Ls Lb cx.closure[i]! with
      | (c, s, b) => (Lc.push c, Ls.push s, Lb.push b))
    0 k (Array.mkEmpty k, Array.mkEmpty k, Array.mkEmpty k)

/-- `phiEL` on the three tables and the member flags. -/
def phiEL2 (cx : SCtx) (posA posC : Array Nat) (avail : Nat → Bool) (stored : Array Nat) :
    Nat × Nat :=
  let p := cx.up.prep
  let base := cx.baseEv
  let fl := memberFlags cx posA avail
  let L := phiTable3 cx posA posC fl
  let getC := readAtF (posOf posC) L.1 id (base.cost[·]!)
  let getS := readAtF (posOf posC) L.2.1 id (base.sides[·]!)
  let getB := readAtF (posOf posC) L.2.2 id (base.below[·]!)
  let inl := fun x => evalHiddenG p.dag p.family p.spineLen p.tail (flagWidth cx posA fl)
    cx.allTrue[x]! (decide (x < base.cost.size)) getC getS getB x
  let roots := cx.rootsC.foldl (fun acc r => acc + getC r) 0
  let baseSum := cx.storedInC.foldl (fun acc c => acc + inl c) 0
  let entries := stored.foldl (fun acc x => acc + inl x) 0
  (roots + baseSum + entries, cx.closure.size + stored.size)

/-- The four bounds `boundsStep` writes at `t`, from readers of the head and
continuation bounds. -/
@[inline] def boundsValsG (p : Prep) (w : Nat) (msT : Bool) (getH getC : Nat → Nat) (t : Nat) :
    Nat × Nat × Nat × Nat :=
  let node := p.dag.node t
  let fam := p.family[t]!
  let (i, m) :=
    if fam == .none then
      let i := node.children.foldl (fun acc c => acc + getH c) node.head.ownBytes
      (i, i)
    else
      let nxt := node.spineNext
      let rest := if p.family[nxt]! == fam then getC nxt else getH nxt
      let m := node.sideExtra + getH node.sideChild + rest
      (1 + m, m)
  (i, m, if msT then min w i else i, if msT then min w m else m)

/-- Whether `t` may be stored: a candidate not in `outAll` (the table
`outAll.foldl (·.set! · false) cand`). -/
@[inline] def maybeStoredAt (cx : SCtx) (outAll : Array Nat) (t : Nat) : Bool :=
  cx.cand[t]! && !outAll.contains t

/-- `SCtx.rebound` for the maybe-stored set `cand` minus `outAll`, by area
position: `(inline, merged, head, continuation)`. -/
def reboundL (cx : SCtx) (posA : Array Nat) (outAll : Array Nat) :
    Array (Nat × Nat × Nat × Nat) :=
  let b0 := cx.bounds0
  localFold cx.area.size (cx.area[·]!) fun L _ t =>
    boundsValsG cx.up.prep cx.up.w (maybeStoredAt cx outAll t)
      (readAtF (posOf posA) L (·.2.2.1) (b0.headLB[·]!))
      (readAtF (posOf posA) L (·.2.2.2) (b0.contLB[·]!)) t

/-- `SCtx.opaqueUnder` on the local bounds. -/
@[inline] def opaqueUnderL (cx : SCtx) (posA : Array Nat) (b : Array (Nat × Nat × Nat × Nat))
    (t : Nat) : Bool :=
  if cx.up.prep.family[t]! == .none then
    readAtF (posOf posA) b (·.1) (cx.bounds0.inlineLB[·]!) t ≥ cx.up.w
  else readAtF (posOf posA) b (·.2.1) (cx.bounds0.mergedLB[·]!) t ≥ cx.up.w

/-- The reader of `SCtx.opaqueArr inAll outAll`, given
`b = reboundL cx posA outAll`. -/
@[inline] def opqArrR (cx : SCtx) (posA : Array Nat) (b : Array (Nat × Nat × Nat × Nat))
    (inAll : Array Nat) (t : Nat) : Bool :=
  cx.up.opaq[t]! || (decide (t < cx.up.opaq.size) && inAll.contains t && opaqueUnderL cx posA b t)

/-- Area positions in descending order: position `i` of the reversed area. -/
@[inline] def posRev (k : Nat) (pos : Array Nat) (u : Nat) : Option Nat :=
  match posOf pos u with
  | some j => some (k - 1 - j)
  | none => none

/-- `SCtx.revisible` for the maybe-stored set `cand` minus `outAll`, by
position in the reversed area: `(all, head)`. -/
def revisibleL (cx : SCtx) (posA : Array Nat) (outAll : Array Nat) : Array (Nat × Nat) :=
  let k := cx.area.size
  localFold k (fun i => cx.area[k - 1 - i]!) fun L i _ =>
    let j := k - 1 - i
    let r := cx.rootOcc[j]!
    cx.inEdges[j]!.foldl (fun (dh : Nat × Nat) (e : Nat × Nat × Nat) =>
      let wq := if maybeStoredAt cx outAll e.1 then 1
        else min (readAtF (posRev k posA) L (·.1) (cx.vis0.1[·]!) e.1) visibleCap
      (dh.1 + e.2.1 * wq, dh.2 + e.2.2 * wq)) (r, r)

/-- `storedGainWith` with readers of the inline and merged bounds. -/
@[inline] def storedGainG (p : Prep) (inlR mrgR : Nat → Nat) (w t d h : Nat) : _root_.Int :=
  let deg := _root_.Int.ofNat d
  let wI := _root_.Int.ofNat w
  if p.family[t]! == .none then
    (deg - 1) * _root_.Int.ofNat (inlR t) - deg * wI
  else if h ≥ 1 then
    (deg - 1) * _root_.Int.ofNat (mrgR t) + (_root_.Int.ofNat h - 1) - deg * wI
  else
    (deg - 1) * _root_.Int.ofNat (mrgR t) - _root_.Int.ofNat (tag4Size p.spineLen[t]!) - deg * wI

/-- `SCtx.reclassify` on the local bounds and counts. -/
def reclassifyL (cx : SCtx) (posA : Array Nat) (outAll localIn und : Array Nat) :
    Array Nat × Array (Nat × _root_.Int) × Array (Nat × Nat × Nat × Nat) :=
  let b := reboundL cx posA outAll
  let vis := revisibleL cx posA outAll
  let k := cx.area.size
  let gains := und.map fun t =>
    let d := readAtF (posRev k posA) vis (·.1) (cx.vis0.1[·]!) t
    let h := readAtF (posRev k posA) vis (·.2) (cx.vis0.2[·]!) t
    (t, storedGainG cx.up.prep (readAtF (posOf posA) b (·.1) (cx.bounds0.inlineLB[·]!))
      (readAtF (posOf posA) b (·.2.1) (cx.bounds0.mergedLB[·]!)) cx.up.w t d h,
      1 ≤ d && h ≤ d)
  let isForced := fun (e : Nat × _root_.Int × Bool) => e.2.2 && e.2.1 ≥ cx.theta
  let forced := (gains.filter isForced).map (·.1)
  let localIn := if forced.isEmpty then localIn else mergeSorted localIn forced
  let open_ := (gains.filter (!isForced ·)).map fun e => (e.1, e.2.1)
  (localIn, open_, b)

/-- `reachLabelsOn` over the closure, by closure position. -/
def reachLabelsL (dag : Dag) (closure posC : Array Nat) (opq : Nat → Bool)
    (lab : Nat → Option Nat) : Array (Option (Option Nat)) :=
  localFold closure.size (closure[·]!) fun L _ t =>
    (dag.node t).children.foldl (fun v c =>
      labelJoin v (if opq c then (lab c).map some else readAtF (posOf posC) L id (fun _ => none) c))
      ((lab t).map some)

/-- The labels of `sepLabels n members g inRed outRed`. -/
@[inline] def sepLab (n : Nat) (members g inRed outRed : Array Nat) (u : Nat) : Option Nat :=
  if u < n then
    (if inRed.contains u || outRed.contains u then none
     else if g.contains u then some 1
     else if members.contains u then some 2
     else none)
  else none

/-- `SCtx.sepCheck` on the local tables. -/
def sepCheckL (cx : SCtx) (posA posC : Array Nat) (g inRed outRed : Array Nat) : Bool :=
  let n := cx.up.prep.dag.size
  let bR := reboundL cx posA outRed
  let opqR := fun t => opqArrR cx posA bR inRed t
  let lab := sepLab n cx.members g inRed outRed
  let rl := reachLabelsL cx.up.prep.dag cx.closure posC opqR lab
  g.all (fun t => (decide (t < n) && cx.members.contains t) && lab t == some 1) &&
    cx.members.all fun v => (decide (v < n) && outRed.contains v) || opqR v ||
      readAtF (posOf posC) rl id (fun _ => none) v != some none

mutual
/-- `SCtx.solveP` on the local tables. -/
def solvePL (cx : SCtx) (posA posC : Array Nat) (limits : Limits) :
    Nat → Array Nat → Array Nat → Array Nat → SState → Except SharingError (CTable × SState)
  | 0, _, _, _, _ => throw (.internal "component search fuel exhausted")
  | fuel + 1, g, inAll, outAll, st => do
    let bA := reboundL cx posA outAll
    let opqA := fun t => opqArrR cx posA bA inAll t
    let inSet : Std.HashSet Nat := inAll.foldl (·.insert ·) {}
    let outSet : Std.HashSet Nat := outAll.foldl (·.insert ·) {}
    let (entries, _) := cx.memoKey opqA inSet outSet g
    let (inRed, outRed) := keyContext entries
    unless strictInc g && strictInc inRed && strictInc outRed &&
        inRed.all inSet.contains && outRed.all outSet.contains do
      throw (.internal "memo key context is not part of the decided context")
    match st.memo.get? (g, entries) with
    | some tb => pure (tb, { st with memoHits := st.memoHits + 1 })
    | none =>
      unless sepCheckL cx posA posC g inRed outRed do
        throw (.internal "search group is not separated")
      let (tb, st) ← solveBodyL cx posA posC limits fuel g inRed outRed st
      pure (tb, { st with memo := st.memo.insert (g, entries) tb })

/-- `SCtx.solveBody` on the local tables. -/
def solveBodyL (cx : SCtx) (posA posC : Array Nat) (limits : Limits) :
    Nat → Array Nat → Array Nat → Array Nat → SState → Except SharingError (CTable × SState)
  | 0, _, _, _, _ => throw (.internal "component search fuel exhausted")
  | fuel + 1, g, inRed, outRed, st => do
    let inSet : Std.HashSet Nat := inRed.foldl (·.insert ·) {}
    let (phi0, work) := phiEL2 cx posA posC (fun t => inSet.contains t) inRed
    let st ← chargeP limits (work + cx.area.size) st
    let (tb, st) ← nodePL cx posA posC limits fuel phi0 inRed outRed outRed.size #[] g #[] st
    pure (tb.trim cx.slack, st)

/-- `SCtx.nodeP` on the local tables. -/
def nodePL (cx : SCtx) (posA posC : Array Nat) (limits : Limits) :
    Nat → Nat → Array Nat → Array Nat → Nat → Array Nat → Array Nat → CTable → SState →
      Except SharingError (CTable × SState)
  | 0, _, _, _, _, _, _, _, _ => throw (.internal "component search fuel exhausted")
  | fuel + 1, phi0, inCtx, outAll, nOutCtx, localIn, und, tb, st => do
    let (localIn, open_, b) := reclassifyL cx posA outAll localIn und
    let und := open_.map (·.1)
    let inAll := inCtx ++ localIn
    let inSet : Std.HashSet Nat := inAll.foldl (·.insert ·) {}
    let undSet : Std.HashSet Nat := und.foldl (·.insert ·) {}
    let (phi, work) := phiEL2 cx posA posC (fun t => inSet.contains t || undSet.contains t) inAll
    let st ← chargeP limits (work + 2 * cx.area.size) st
    let delta : _root_.Int := (phi : _root_.Int) - (phi0 : _root_.Int)
    if und.isEmpty then return (tb.add (delta, localIn), st)
    if tb.prunes delta cx.slack then return (tb, st)
    let opq := fun t => cx.up.opaq[t]! || (inSet.contains t && opaqueUnderL cx posA b t)
    let availFixed := fun t => inSet.contains t && !opq t
    let groups := cx.groups opq availFixed und
    unless partitionCheck und groups do
      throw (.internal "search groups do not partition the undecided members")
    let route :=
      if groups.size > 1 then true
      else if groups.size == 1 then
        let outSet : Std.HashSet Nat := outAll.foldl (·.insert ·) {}
        let (_, rel) := cx.memoKey opq inSet outSet groups[0]!
        localIn.any (!rel.contains ·) || (outAll.extract nOutCtx outAll.size).any (!rel.contains ·)
      else false
    if route then
      let (phiNone, work) := phiEL2 cx posA posC (fun t => inSet.contains t) inAll
      let st ← chargeP limits work st
      let base : _root_.Int := (phiNone : _root_.Int) - (phi0 : _root_.Int)
      let (comb, st) ← splitPL cx posA posC limits fuel inAll outAll groups.toList
        #[some (base, localIn)] st
      return (comb.foldl (fun acc o => match o with
        | some e => acc.add e
        | none => acc) tb, st)
    let some (t, gt) := pickBranch open_ | return (tb, st)
    let und' := und.erase t
    if gt > 0 then
      let (tb, st) ← nodePL cx posA posC limits fuel phi0 inCtx outAll nOutCtx
        (mergeSorted localIn #[t]) und' tb st
      nodePL cx posA posC limits fuel phi0 inCtx (outAll.push t) nOutCtx localIn und' tb st
    else
      let (tb, st) ← nodePL cx posA posC limits fuel phi0 inCtx (outAll.push t) nOutCtx localIn
        und' tb st
      nodePL cx posA posC limits fuel phi0 inCtx outAll nOutCtx (mergeSorted localIn #[t]) und'
        tb st

/-- `SCtx.splitP` on the local tables. -/
def splitPL (cx : SCtx) (posA posC : Array Nat) (limits : Limits) :
    Nat → Array Nat → Array Nat → List (Array Nat) → CTable → SState →
      Except SharingError (CTable × SState)
  | 0, _, _, _, _, _ => throw (.internal "component search fuel exhausted")
  | _ + 1, _, _, [], comb, st => pure (comb, st)
  | fuel + 1, inAll, outAll, grp :: grps, comb, st => do
    let (sub, st) ← solvePL cx posA posC limits fuel grp inAll outAll st
    splitPL cx posA posC limits fuel inAll outAll grps (comb.conv sub) st
end

/-- `searchComponent` on the local tables. Every member is in the area
(`componentArea` starts from the members), so the fallback to
`searchComponent` for a member outside it is defensive. -/
def searchComponentL (cx : SCtx) (posA posC : Array Nat) (limits : Limits) (states costEvals : Nat) :
    Except SharingError (CompResult × Nat × Nat) :=
  if cx.members.all (fun m => (posOf posA m).isSome) then do
    unless areaParentsOK cx.up.prep.dag.size cx do
      throw (.internal "component parents are not duplicate-free terms")
    let st0 : SState := { states, costEvals }
    let (tb, st) ← solvePL cx posA posC limits (8 * cx.members.size + 8) cx.members #[] #[] st0
    let some bd := tb.best | throw (.internal "component search found no choice")
    let some bs := bestSetOf tb bd | throw (.internal "component search found no choice")
    pure ({ members := cx.members, bestDelta := bd, bestSet := bs, bySize := tb },
      st.states, st.costEvals)
  else searchComponent cx limits states costEvals

/-- The conditions under which the local search reads the same values as the
specification: the tables have the DAG's size, and the area and the closure
are strictly increasing terms inside them. Every context that
`searchComponentsWithFast` builds satisfies them (the stage's tables are
built at the DAG's size, `componentArea` sorts its terms and the closure is
sorted and duplicate-free), so the fallback to `searchComponent` in
`fastStep` is defensive. -/
def localSearchOK (cx : SCtx) : Bool :=
  let n := cx.up.prep.dag.size
  cx.cand.size == n && cx.bounds0.inlineLB.size == n && cx.bounds0.mergedLB.size == n &&
    cx.bounds0.headLB.size == n && cx.bounds0.contLB.size == n &&
    cx.vis0.1.size == n && cx.vis0.2.size == n &&
    cx.baseEv.cost.size == n && cx.baseEv.sides.size == n && cx.baseEv.below.size == n &&
    cx.widthCs.size == n && cx.allTrue.size == n && cx.up.opaq.size == n &&
    strictInc cx.area && cx.area.all (· < n) && strictInc cx.closure && cx.closure.all (· < n)

/-! ### The component loop -/

/-- One component of the loop of `searchComponents`: search it and record its
table, threading the search counters. -/
@[expose] def specStep (limits : Limits) (ex : Expanded) (f : GraphFacts) (up : UPrep)
    (cand : Array Bool) (b0 : UBounds) (vis0 : Array Nat × Array Nat) (rootCount : Array Nat)
    (slack : Nat) (theta : _root_.Int) (baseEv : DictEval) (widthCs : Array (Option Nat))
    (allTrue : Array Bool) (unc : Array Nat) (opaq : Array Bool)
    (acc : Array CompResult × Nat × Nat) (members : Array Nat) :
    Except SharingError (Array CompResult × Nat × Nat) := do
  let (results, states, costEvals) := acc
  if limits.uniformSubsetSearch then
    let (r, states, costEvals) ← searchComponentRef up f opaq ex.roots slack
      limits members states costEvals
    pure (results.push r, states, costEvals)
  else
    let cx := mkSCtx ex f up cand b0 vis0 rootCount slack theta
      baseEv widthCs allTrue unc members
    let (r, states, costEvals) ← searchComponent cx limits states costEvals
    pure (results.push r, states, costEvals)

/-- The component loop of `searchComponents` (`Ix.Sharing.Exact.Uniform`),
with the stage's tables as arguments. -/
@[expose] def searchComponentsWith (limits : Limits) (ex : Expanded) (f : GraphFacts) (up : UPrep)
    (cand : Array Bool) (b0 : UBounds) (vis0 : Array Nat × Array Nat) (rootCount : Array Nat)
    (slack : Nat) (theta : _root_.Int) (baseEv : DictEval) (widthCs : Array (Option Nat))
    (allTrue : Array Bool) (unc : Array Nat) (opaq : Array Bool) (comps : Array (Array Nat)) :
    Except SharingError (Array CompResult × Nat × Nat) :=
  comps.foldlM (init := ((#[] : Array CompResult), 0, 0))
    (specStep limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc opaq)

/-- The parents of every term (`q` is listed under each child `c < n` of
`q`, once per edge). -/
def parentsOf (dag : Dag) : Array (Array Nat) :=
  foldRange (fun P q => (dag.node q).children.foldl (fun P c => P.modify c (·.push q)) P)
    0 dag.size (Array.replicate dag.size #[])

/-- One push of the closure walk: mark and record `q` if it is a new term
below `n`. State: marks, terms found, stack. -/
@[inline] def walkPush (n : Nat) (st : Array Nat × Array Nat × Array Nat) (q : Nat) :
    Array Nat × Array Nat × Array Nat :=
  match st with
  | (vis, out, stack) =>
    if q < n && vis[q]! == 0 then (vis.set! q 1, out.push q, stack.push q) else (vis, out, stack)

/-- The closure walk: pop a term and push its parents, at most `fuel` times. -/
def walkLoop (P : Array (Array Nat)) (n : Nat) :
    Nat → Array Nat × Array Nat × Array Nat → Array Nat × Array Nat × Array Nat
  | 0, st => st
  | fuel + 1, (vis, out, stack) =>
    match stack.back? with
    | none => (vis, out, stack)
    | some c => walkLoop P n fuel ((P[c]!).foldl (walkPush n) (vis, out, stack.pop))

/-- The members below `vis.size` and their ancestors through `P`, marked `1`
in `vis` (which must be `0` there), in the order found; the stack is empty
when the walk finished. -/
def upWalk (P : Array (Array Nat)) (members : Array Nat) (vis : Array Nat) :
    Array Nat × Array Nat × Array Nat :=
  let n := vis.size
  walkLoop P n (n + 1) (members.foldl (walkPush n) (vis, #[], #[]))


/-- Write the positions `j + 1` of the terms of `xs` into `pos`. -/
def setPositions (pos : Array Nat) (xs : Array Nat) : Array Nat :=
  foldRange (fun pos j => pos.set! xs[j]! (j + 1)) 0 xs.size pos

/-- Clear the entries of the terms of `xs` in `pos`. -/
def clearPositions (pos : Array Nat) (xs : Array Nat) : Array Nat :=
  xs.foldl (fun pos t => pos.set! t 0) pos

/-- `mkSCtx` with the closure found by an upward walk over the parent lists
`P` (valid when `P` lists the parents of every term and children precede
their parents), using `posC` (all `0`) as marks; returns the context and
`posC` holding the closure positions. The walk pushes every term at most
once, so its fuel (`n + 1` pops) always suffices and the fallback to
`upClosure` is defensive. -/
def mkSCtxL (ex : Expanded) (f : GraphFacts) (up : UPrep) (cand : Array Bool) (b0 : UBounds)
    (vis0 : Array Nat × Array Nat) (rootCount : Array Nat) (slack : Nat) (theta : _root_.Int)
    (baseEv : DictEval) (widthCs : Array (Option Nat)) (allTrue : Array Bool) (unc : Array Nat)
    (P : Array (Array Nat)) (posC : Array Nat) (members : Array Nat) : SCtx × Array Nat :=
  let area := componentArea up f members
  let areaIdx : Std.HashMap Nat Nat :=
    (Array.range area.size).foldl (fun acc j => acc.insert area[j]! j) {}
  let memberIdx : Std.HashMap Nat Nat :=
    (Array.range members.size).foldl (fun acc j => acc.insert members[j]! j) {}
  let inEdges := area.map fun y => f.parents[y]!.map fun q => edgeCount ex.dag q y
  let rootOcc := area.map (rootCount[·]!)
  let (vis, found, stack) := upWalk P members posC
  let (closure, posC) :=
    if stack.isEmpty then ((found.toList.mergeSort fun a b => decide (a ≤ b)).toArray, vis)
    else (upClosure ex.dag ((markTable ex.dag.size members)[·]!), clearPositions vis found)
  let posC := setPositions posC closure
  let rootsC := ex.roots.filter (posC[·]! != 0)
  let storedInC := closure.filter (up.opaq[·]!)
  ({ up, facts := f, cand, bounds0 := b0, vis0, members, memberIdx, area, areaIdx,
     inEdges, rootOcc, slack, theta, baseEv, widthCs, allTrue, closure, rootsC, storedInC,
     allUnc := unc }, posC)

/-- One component of the compiled loop: build its context with the closure
walk, run the local search when its conditions hold (else the specification's
search), and clear the two position tables again. -/
def fastStep (limits : Limits) (ex : Expanded) (f : GraphFacts) (up : UPrep)
    (cand : Array Bool) (b0 : UBounds) (vis0 : Array Nat × Array Nat) (rootCount : Array Nat)
    (slack : Nat) (theta : _root_.Int) (baseEv : DictEval) (widthCs : Array (Option Nat))
    (allTrue : Array Bool) (unc : Array Nat) (P : Array (Array Nat))
    (acc : (Array CompResult × Nat × Nat) × Array Nat × Array Nat) (members : Array Nat) :
    Except SharingError ((Array CompResult × Nat × Nat) × Array Nat × Array Nat) := do
  let ((results, states, costEvals), posA, posC) := acc
  let (cx, posC) := mkSCtxL ex f up cand b0 vis0 rootCount slack theta baseEv widthCs
    allTrue unc P posC members
  if localSearchOK cx then
    let posA := setPositions posA cx.area
    let (r, states, costEvals) ← searchComponentL cx posA posC limits states costEvals
    pure ((results.push r, states, costEvals), clearPositions posA cx.area,
      clearPositions posC cx.closure)
  else
    let (r, states, costEvals) ← searchComponent cx limits states costEvals
    pure ((results.push r, states, costEvals), posA, clearPositions posC cx.closure)

/-- `searchComponentsWith` with the closure walk and the local search, sharing
two position tables across the components. It runs the specification when
`uniformSubsetSearch` is set (the test oracle) or the DAG's children do not
precede their parents, which never happens for an expanded DAG (the interner
numbers children first), so that second fallback is defensive. -/
def searchComponentsWithFast (limits : Limits) (ex : Expanded) (f : GraphFacts) (up : UPrep)
    (cand : Array Bool) (b0 : UBounds) (vis0 : Array Nat × Array Nat) (rootCount : Array Nat)
    (slack : Nat) (theta : _root_.Int) (baseEv : DictEval) (widthCs : Array (Option Nat))
    (allTrue : Array Bool) (unc : Array Nat) (opaq : Array Bool) (comps : Array (Array Nat)) :
    Except SharingError (Array CompResult × Nat × Nat) :=
  if limits.uniformSubsetSearch || !childrenPrecede ex.dag.nodes then
    searchComponentsWith limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs
      allTrue unc opaq comps
  else
    (comps.foldlM (init := (((#[] : Array CompResult), 0, 0),
        Array.replicate up.prep.dag.size 0, Array.replicate ex.dag.size 0))
      (fastStep limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc
        (parentsOf ex.dag))).map (·.1)


/-! ### Equality with the specification -/

namespace LocalSearch

theorem foldRange_succ {σ : Type} (f : σ → Nat → σ) (k m : Nat) (s : σ) :
    foldRange f k (m + 1) s = f (foldRange f k m s) (k + m) := by
  induction m generalizing k s with
  | zero => rfl
  | succ m ih =>
    show foldRange f (k + 1) (m + 1) (f s k) = f (foldRange f (k + 1) m (f s k)) (k + (m + 1))
    rw [ih, show k + 1 + m = k + (m + 1) by omega]

theorem foldRange_zero {σ : Type} (f : σ → Nat → σ) (k : Nat) (s : σ) : foldRange f k 0 s = s := by
  rfl

theorem list_range_foldl {σ : Type} (g : σ → Nat → σ) (k : Nat) (s : σ) :
    (List.range k).foldl g s = foldRange g 0 k s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.foldl_append, ih, foldRange_succ]; simp

theorem array_foldl_eq {α σ : Type} [Inhabited α] (f : σ → α → σ) (xs : Array α) (s : σ) :
    xs.foldl f s = foldRange (fun s i => f s xs[i]!) 0 xs.size s := by
  have key : ∀ m, m ≤ xs.size →
      foldRange (fun s i => f s xs[i]!) 0 m s = (xs.toList.take m).foldl f s := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [foldRange_succ, ih (by omega), List.take_add_one, List.foldl_append]
      have hm' : m < xs.toList.length := by simp; omega
      simp [List.getElem?_eq_getElem hm', getElem!_pos xs m (by omega)]
  rw [key xs.size (Nat.le_refl _), List.take_of_length_le (by simp), Array.foldl_toList]

/-- `posf` lists the positions of the terms `xsAt 0, …, xsAt (k - 1)`. -/
def PosFn (k : Nat) (xsAt : Nat → Nat) (posf : Nat → Option Nat) : Prop :=
  ∀ u j, posf u = some j ↔ (j < k ∧ xsAt j = u)

theorem readAtF_proj {α β : Type} [Inhabited α] (posf : Nat → Option Nat) (L : Array α)
    (proj : α → β) (base : Nat → α) (u : Nat) :
    readAtF posf L proj (fun v => proj (base v)) u = proj (readAtF posf L id base u) := by
  unfold readAtF
  split
  · split <;> rfl
  · rfl

theorem readAtF_empty {α β : Type} [Inhabited α] (posf : Nat → Option Nat) (proj : α → β)
    (base : Nat → β) (u : Nat) : readAtF posf (#[] : Array α) proj base u = base u := by
  unfold readAtF
  split
  · simp
  · rfl

/-- **Local folds.** A fold that writes, at the terms `xsAt 0, …, xsAt (k-1)`
in order, values computed from the state before (`hstep`), reads at every
term what the local fold `localFold` computes from those values and the
initial state elsewhere. -/
theorem fold_local {S V : Type} [Inhabited V] (get : S → Nat → V) (step : S → Nat → Nat → S)
    (F : (Nat → V) → Nat → Nat → V) (Ok : S → Prop) (k : Nat) (xsAt : Nat → Nat)
    (posf : Nat → Option Nat) (hpos : PosFn k xsAt posf)
    (hstep : ∀ s i, Ok s → i < k → Ok (step s i (xsAt i)) ∧
      ∀ u, get (step s i (xsAt i)) u = if u = xsAt i then F (get s) i (xsAt i) else get s u)
    (s0 : S) (h0 : Ok s0) (G : Array V → Nat → Nat → V)
    (hG : ∀ L i, L.size = i → i < k →
      G L i (xsAt i) = F (readAtF posf L id (get s0)) i (xsAt i)) :
    Ok (foldRange (fun s i => step s i (xsAt i)) 0 k s0) ∧ ∀ u, get (foldRange (fun s i => step s i (xsAt i)) 0 k s0) u =
      readAtF posf (localFold k xsAt G) id (get s0) u := by
  have key : ∀ m, m ≤ k →
      Ok (foldRange (fun s i => step s i (xsAt i)) 0 m s0) ∧
      (foldRange (fun L i => L.push (G L i (xsAt i))) 0 m (Array.mkEmpty k)).size = m ∧
      ∀ u, get (foldRange (fun s i => step s i (xsAt i)) 0 m s0) u =
        readAtF posf (foldRange (fun L i => L.push (G L i (xsAt i))) 0 m (Array.mkEmpty k))
          id (get s0) u := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨h0, by simp [foldRange_zero], fun u => ?_⟩
      rw [foldRange_zero, foldRange_zero]
      exact (readAtF_empty posf id (get s0) u).symm
    | succ m ih =>
      intro hm
      obtain ⟨hok, hsz, hrd⟩ := ih (by omega)
      rw [foldRange_succ, foldRange_succ, Nat.zero_add]
      generalize foldRange (fun s i => step s i (xsAt i)) 0 m s0 = s at hok hrd
      generalize foldRange (fun L i => L.push (G L i (xsAt i))) 0 m (Array.mkEmpty k) = L
        at hsz hrd
      obtain ⟨hok', hget⟩ := hstep s m hok (by omega)
      have hrd' : get s = readAtF posf L id (get s0) := funext hrd
      refine ⟨hok', by simp [hsz], fun u => ?_⟩
      rw [hget u, hG L m hsz (by omega), ← hrd']
      have hxm : posf (xsAt m) = some m := (hpos _ m).mpr ⟨by omega, rfl⟩
      by_cases hu : u = xsAt m
      · subst hu
        simp only [if_true]
        unfold readAtF
        rw [hxm]
        subst hsz
        simp
      · simp only [hu, if_false]
        rw [hrd u]
        unfold readAtF
        cases hp : posf u with
        | none => rfl
        | some j =>
          have hjm : j ≠ m := by
            intro h
            subst h
            exact hu ((hpos u j).mp hp).2.symm
          simp only [Array.size_push, hsz]
          by_cases hj : j < m
          · simp only [hj, if_true, show j < m + 1 by omega]
            rw [getElem!_pos (L.push _) j (by simp [hsz]; omega), getElem!_pos L j (by omega)]
            simp [Array.getElem_push_lt (show j < L.size by omega)]
          · simp only [hj, if_false, show ¬ j < m + 1 by omega]
  obtain ⟨hok, _, h⟩ := key k (Nat.le_refl _)
  exact ⟨hok, h⟩

end LocalSearch

/-! ### Reading the tables of `set!` folds -/

namespace LocalSearch

theorem foldl_setFalse_read (l : List Nat) (a : Array Bool) (u : Nat) :
    (l.foldl (fun acc t => acc.set! t false) a)[u]! = (a[u]! && !l.contains u) := by
  induction l generalizing a with
  | nil => simp
  | cons t l ih =>
    rw [List.foldl_cons, ih, getElem!_setBang]
    by_cases hut : u = t
    · subst hut
      by_cases h : u < a.size
      · simp [h]
      · simp [h]
    · simp [hut]

/-- The maybe-stored table of `SCtx.reclassify` and `SCtx.opaqueArr`. -/
theorem ms_read (cand : Array Bool) (outAll : Array Nat) (u : Nat) :
    (outAll.foldl (fun acc t => acc.set! t false) cand)[u]! = (cand[u]! && !outAll.contains u) := by
  rw [← Array.foldl_toList, foldl_setFalse_read, Array.contains_toList]

theorem markTable_read (n : Nat) (ts : Array Nat) (u : Nat) :
    (markTable n ts)[u]! = (decide (u < n) && ts.contains u) := by
  unfold markTable
  rw [← Array.foldl_toList, ← Array.contains_toList]
  generalize ts.toList = l
  have key : ∀ (a : Array Bool), a.size = n →
      (l.foldl (fun acc t => acc.set! t true) a)[u]! = (a[u]! || (decide (u < n) && l.contains u)) := by
    induction l with
    | nil => intro a _; simp
    | cons t l ih =>
      intro a ha
      rw [List.foldl_cons, ih _ (by simp [ha]), getElem!_setBang]
      by_cases hut : u = t
      · subst hut
        by_cases h : u < n
        · simp [h, ha]
        · simp [h, ha]
      · simp [hut]
  rw [key _ (by simp)]
  by_cases h : u < n
  · simp [h]
  · simp [h]

theorem foldl_setConst_size {α : Type} (l : List Nat) (v : α) (a : Array α) :
    (l.foldl (fun acc t => acc.set! t v) a).size = a.size := by
  induction l generalizing a with
  | nil => rfl
  | cons t l ih => rw [List.foldl_cons, ih]; simp

theorem foldl_setConst_read {α : Type} [Inhabited α] (l : List Nat) (v : α) (a : Array α)
    (u : Nat) :
    (l.foldl (fun acc t => acc.set! t v) a)[u]! = if u < a.size ∧ u ∈ l then v else a[u]! := by
  induction l generalizing a with
  | nil => simp
  | cons t l ih =>
    rw [List.foldl_cons, ih, getElem!_setBang]
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, List.mem_cons]
    by_cases hut : u = t
    · subst hut
      by_cases h : u < a.size <;> simp [h]
    · by_cases h : u < a.size <;> simp [h, hut]

theorem sepLabels_read (n : Nat) (members g inRed outRed : Array Nat) (u : Nat) :
    (sepLabels n members g inRed outRed)[u]! = sepLab n members g inRed outRed u := by
  unfold sepLabels sepLab
  simp only [← Array.foldl_toList]
  rw [foldl_setConst_read, foldl_setConst_read, foldl_setConst_read, foldl_setConst_size,
    foldl_setConst_size]
  have hrep : (Array.replicate n (none : Option Nat))[u]! = none := by
    by_cases h : u < n
    · rw [getElem!_pos _ u (by simpa using h)]; simp
    · rw [getElem!_neg _ u (by simpa using h)]; rfl
  simp only [Array.size_replicate, Array.toList_append, List.mem_append, Array.mem_toList_iff,
    hrep]
  by_cases h : u < n <;> by_cases hi : u ∈ inRed <;> by_cases ho : u ∈ outRed <;>
    by_cases hg : u ∈ g <;> by_cases hm : u ∈ members <;> simp [h, hi, ho, hg, hm]


/-- The widths of `SCtx.phiE`. -/
theorem phiWidth_eq (cx : SCtx) (avail : Nat → Bool) (u : Nat) :
    widthOf (cx.members.foldl (fun acc t => if avail t then acc.set! t (some cx.up.w) else acc)
      cx.widthCs) u = phiWidth cx avail u := by
  unfold phiWidth
  rw [← Array.foldl_toList, ← Array.contains_toList]
  have key : ∀ (l : List Nat) (a : Array (Option Nat)), a.size = cx.widthCs.size →
      widthOf (l.foldl (fun acc t => if avail t then acc.set! t (some cx.up.w) else acc) a) u =
        if decide (u < cx.widthCs.size) && l.contains u && avail u then some cx.up.w
        else widthOf a u := by
    intro l
    induction l with
    | nil => intro a _; simp
    | cons t l ih =>
      intro a ha
      rw [List.foldl_cons]
      by_cases hat : avail t
      · simp only [hat, if_true]
        rw [ih _ (by simp [ha])]
        unfold widthOf
        simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        by_cases hut : u = t
        · subst hut
          by_cases h : u < a.size
          · simp [h, ha.symm ▸ h, hat]
          · simp [h, ha ▸ h, hat]
        · simp [hut, Ne.symm hut]
      · simp only [hat, Bool.false_eq_true, if_false]
        rw [ih _ ha]
        by_cases hut : u = t
        · subst hut; simp [hat]
        · simp [hut]
  rw [key _ _ rfl]

end LocalSearch

/-! ### Steps of the specification's folds -/

namespace LocalSearch

theorem cutScan_eq_G (spineLen sides : Array Nat) (below : Array (Option Nat))
    (width : Array (Option Nat)) (l s : Nat) :
    ∀ fuel cur best work, cutScan spineLen sides below width l s fuel cur best work =
      cutScanG spineLen (sides[·]!) (below[·]!) (widthOf width) l s fuel cur best work
  | 0, _, _, _ => by simp only [cutScan, cutScanG]
  | _ + 1, none, _, _ => by simp only [cutScan, cutScanG]
  | fuel + 1, some u, best, work => by
    simp only [cutScan, cutScanG]
    exact cutScan_eq_G spineLen sides below width l s fuel _ _ _

theorem cutScanAt_eq_G (spineLen sides : Array Nat) (below : Array (Option Nat))
    (width : Array (Option Nat)) (t s' : Nat) (bl' : Option Nat) (l s : Nat) :
    ∀ fuel cur best work, cutScanAt spineLen sides below width t s' bl' l s fuel cur best work =
      cutScanG spineLen (fun u => if u = t ∧ t < sides.size then s' else sides[u]!)
        (fun u => if u = t ∧ t < below.size then bl' else below[u]!)
        (fun u => if u = t then none else widthOf width u) l s fuel cur best work
  | 0, _, _, _ => by simp only [cutScanAt, cutScanG]
  | _ + 1, none, _, _ => by simp only [cutScanAt, cutScanG]
  | fuel + 1, some u, best, work => by
    simp only [cutScanAt, cutScanG]
    exact cutScanAt_eq_G spineLen sides below width t s' bl' l s fuel _ _ _

/-- The cheapest cut does not depend on the work counter. -/
theorem cutScanG_fst (spineLen : Array Nat) (getS : Nat → Nat) (getB : Nat → Option Nat)
    (widthG : Nat → Option Nat) (l s : Nat) :
    ∀ fuel cur best w1 w2, (cutScanG spineLen getS getB widthG l s fuel cur best w1).1 =
      (cutScanG spineLen getS getB widthG l s fuel cur best w2).1
  | 0, _, _, _, _ => by simp only [cutScanG]
  | _ + 1, none, _, _, _ => by simp only [cutScanG]
  | fuel + 1, some u, best, w1, w2 => by
    simp only [cutScanG]
    exact cutScanG_fst spineLen getS getB widthG l s fuel _ _ _ _

/-- The rows of an evaluation. -/
def eget (st : DictEval) (u : Nat) : Nat × Nat × Option Nat :=
  (st.cost[u]!, st.sides[u]!, st.below[u]!)

/-- Its three tables have size `n`. -/
def ESize (n : Nat) (st : DictEval) : Prop :=
  st.cost.size = n ∧ st.sides.size = n ∧ st.below.size = n

theorem setBang_read {α : Type} [Inhabited α] {n t : Nat} (ht : t < n) (a : Array α) (v : α)
    (ha : a.size = n) (x : Nat) : (a.set! t v)[x]! = if x = t then v else a[x]! := by
  rw [getElem!_setBang]
  by_cases hx : x = t <;> simp [hx, ha, ht]

theorem cutScan_set_fst (spineLen sides : Array Nat) (below : Array (Option Nat))
    (width : Array (Option Nat)) {t : Nat} (s' : Nat) (bl' : Option Nat) (l s : Nat)
    (hs : t < sides.size) (hb : t < below.size) (fuel : Nat) (cur : Option Nat) (best work : Nat) :
    (cutScan spineLen (sides.set! t s') (below.set! t bl') width l s fuel cur best work).1 =
      (cutScanG spineLen (fun x => if x = t then s' else sides[x]!)
        (fun x => if x = t then bl' else below[x]!) (widthOf width) l s fuel cur best 0).1 := by
  rw [cutScan_eq_G, cutScanG_fst _ _ _ _ _ _ _ _ _ _ 0]
  congr 2
  · funext x; rw [getElem!_setBang]; by_cases hx : x = t <;> simp [hx, hs]
  · funext x; rw [getElem!_setBang]; by_cases hx : x = t <;> simp [hx, hb]

theorem evalStep_get (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (width : Array (Option Nat)) (affected : Array Bool) {n : Nat} (st : DictEval)
    (hst : ESize n st) {t : Nat} (ht : t < n) :
    ESize n (evalStep dag family spineLen tail width affected st t) ∧
      ∀ u, eget (evalStep dag family spineLen tail width affected st t) u =
        if u = t then
          (if affected[t]! then
            evalRowG dag family spineLen tail (widthOf width) (st.cost[·]!) (st.sides[·]!)
              (st.below[·]!) t
           else eget st t)
        else eget st u := by
  obtain ⟨hc, hs, hb⟩ := hst
  unfold evalStep
  by_cases ha : affected[t]! = true
  · simp only [ha, if_true]
    by_cases hf : (family[t]! == Family.none) = true
    · simp only [hf, if_true]
      refine ⟨⟨by simp [hc], hs, hb⟩, fun u => ?_⟩
      unfold eget evalRowG
      simp only [hf, if_true]
      rw [setBang_read ht _ _ hc]
      by_cases hu : u = t
      · subst hu
        simp only [if_true]
        rcases widthOf width u with _ | w <;> rfl
      · simp [hu]
    · simp only [hf, Bool.false_eq_true, if_false]
      refine ⟨⟨by simp [hc], by simp [hs], by simp [hb]⟩, fun u => ?_⟩
      unfold eget evalRowG
      simp only [hf, Bool.false_eq_true, if_false]
      rw [setBang_read ht _ _ hc, setBang_read ht _ _ hs, setBang_read ht _ _ hb]
      by_cases hu : u = t
      · subst hu
        simp only [if_true]
        rw [cutScan_set_fst _ _ _ _ _ _ _ _ (by omega) (by omega)]
        rcases widthOf width u with _ | w <;> rfl
      · simp [hu]
  · simp only [ha, Bool.false_eq_true, if_false]
    refine ⟨⟨hc, hs, hb⟩, fun u => ?_⟩
    by_cases hu : u = t
    · subst hu; simp
    · simp [hu]


theorem evalHidden_eq_G (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (width : Array (Option Nat)) (affected : Array Bool) (st : DictEval) (t : Nat)
    (hs : st.sides.size = st.cost.size) (hb : st.below.size = st.cost.size) :
    evalHidden dag family spineLen tail width affected st t =
      evalHiddenG dag family spineLen tail (widthOf width) affected[t]!
        (decide (t < st.cost.size)) (st.cost[·]!) (st.sides[·]!) (st.below[·]!) t := by
  unfold evalHidden evalHiddenG
  by_cases ha : affected[t]! = true
  · simp only [ha, if_true]
    split
    · by_cases ht : t < st.cost.size <;> simp [ht]
    · by_cases ht : t < st.cost.size
      · simp only [ht, decide_true, if_true]
        rw [cutScanAt_eq_G, cutScanG_fst _ _ _ _ _ _ _ _ _ _ 0]
        congr 2
        · funext v; simp only [hs, ht, and_true]
        · funext v; simp only [hb, ht, and_true]
      · simp [ht]
  · simp only [ha, Bool.false_eq_true, if_false]

/-- The bounds of a term. -/
def bget (b : UBounds) (u : Nat) : Nat × Nat × Nat × Nat :=
  (b.inlineLB[u]!, b.mergedLB[u]!, b.headLB[u]!, b.contLB[u]!)

/-- Its four tables have size `n`. -/
def BSize (n : Nat) (b : UBounds) : Prop :=
  b.inlineLB.size = n ∧ b.mergedLB.size = n ∧ b.headLB.size = n ∧ b.contLB.size = n

theorem boundsStep_get (p : Prep) (w : Nat) (ms : Array Bool) {n : Nat} (b : UBounds)
    (hb : BSize n b) {t : Nat} (ht : t < n) :
    BSize n (boundsStep p w ms b t) ∧
      ∀ u, bget (boundsStep p w ms b t) u =
        if u = t then boundsValsG p w ms[t]! (b.headLB[·]!) (b.contLB[·]!) t else bget b u := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  unfold boundsStep
  refine ⟨⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4]⟩, fun u => ?_⟩
  unfold bget boundsValsG
  by_cases hu : u = t
  · subst hu
    simp only [getElem!_setBang, h1, h2, h3, h4, ht, and_self, if_true]
  · simp only [getElem!_setBang, hu, false_and, if_false]

end LocalSearch

/-! ### The local tables read as the specification's -/

namespace LocalSearch

/-- What the local search needs of a context: `localSearchOK` and the two
position tables. -/
structure Ready (cx : SCtx) (posA posC : Array Nat) : Prop where
  ok : localSearchOK cx = true
  area : PosFn cx.area.size (cx.area[·]!) (posOf posA)
  closure : PosFn cx.closure.size (cx.closure[·]!) (posOf posC)

theorem localSearchOK_spec {cx : SCtx} (h : localSearchOK cx = true) :
    cx.cand.size = cx.up.prep.dag.size ∧ BSize cx.up.prep.dag.size cx.bounds0 ∧
    cx.vis0.1.size = cx.up.prep.dag.size ∧ cx.vis0.2.size = cx.up.prep.dag.size ∧
    ESize cx.up.prep.dag.size cx.baseEv ∧
    cx.widthCs.size = cx.up.prep.dag.size ∧ cx.allTrue.size = cx.up.prep.dag.size ∧
    cx.up.opaq.size = cx.up.prep.dag.size ∧
    (∀ i, i < cx.area.size → cx.area[i]! < cx.up.prep.dag.size) ∧
    (∀ i, i < cx.closure.size → cx.closure[i]! < cx.up.prep.dag.size) := by
  unfold localSearchOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, _⟩,
    h15⟩, _⟩, h17⟩ := h
  refine ⟨h1, ⟨h2, h3, h4, h5⟩, h6, h7, ⟨h8, h9, h10⟩, h11, h12, h13, fun i hi => ?_,
    fun i hi => ?_⟩
  · rw [getElem!_pos cx.area i hi]; exact h15 i hi
  · rw [getElem!_pos cx.closure i hi]; exact h17 i hi

theorem readAtF_field {α β : Type} [Inhabited α] (posf : Nat → Option Nat) (L : Array α)
    (proj : α → β) (base : Nat → α) (base' : Nat → β) (h : ∀ v, base' v = proj (base v))
    (u : Nat) : readAtF posf L proj base' u = proj (readAtF posf L id base u) := by
  rw [show base' = fun v => proj (base v) from funext h]
  exact readAtF_proj posf L proj base u

theorem readAtF_field_fun {α β : Type} [Inhabited α] (posf : Nat → Option Nat) (L : Array α)
    (proj : α → β) (base : Nat → α) (base' : Nat → β) (h : ∀ v, base' v = proj (base v)) :
    readAtF posf L proj base' = fun u => proj (readAtF posf L id base u) :=
  funext (readAtF_field posf L proj base base' h)

theorem readAtF_at_new {α β : Type} [Inhabited α] {k : Nat} {xsAt : Nat → Nat}
    {posf : Nat → Option Nat} (hpos : PosFn k xsAt posf) (L : Array α) (proj : α → β)
    (base : Nat → β) {i : Nat} (hi : i < k) (hL : L.size = i) :
    readAtF posf L proj base (xsAt i) = base (xsAt i) := by
  unfold readAtF
  rw [(hpos _ i).mpr ⟨hi, rfl⟩]
  simp [hL]

/-- **Bounds.** `SCtx.rebound` read through the local bounds. -/
theorem rebound_read {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (outAll : Array Nat) (u : Nat) :
    bget (cx.rebound (outAll.foldl (fun acc t => acc.set! t false) cx.cand)) u =
      readAtF (posOf posA) (reboundL cx posA outAll) id (bget cx.bounds0) u := by
  obtain ⟨_, hb0, _, _, _, _, _, _, harea, _⟩ := localSearchOK_spec hr.ok
  unfold SCtx.rebound reboundL
  rw [array_foldl_eq]
  refine (fold_local bget (fun s _ t => boundsStep cx.up.prep cx.up.w
      (outAll.foldl (fun acc t => acc.set! t false) cx.cand) s t)
    (fun g _ t => boundsValsG cx.up.prep cx.up.w
      (outAll.foldl (fun acc t => acc.set! t false) cx.cand)[t]! (fun v => (g v).2.2.1)
      (fun v => (g v).2.2.2) t)
    (BSize cx.up.prep.dag.size) cx.area.size (cx.area[·]!) (posOf posA) hr.area ?_ cx.bounds0
    hb0 _ ?_).2 u
  · intro s i hs hi
    exact boundsStep_get _ _ _ s hs (harea i hi)
  · intro L i _ _
    simp only [ms_read, maybeStoredAt]
    have e1 : readAtF (posOf posA) L (·.2.2.1) (cx.bounds0.headLB[·]!) =
        fun v => (readAtF (posOf posA) L id (bget cx.bounds0) v).2.2.1 :=
      funext fun v => readAtF_proj (posOf posA) L (·.2.2.1) (bget cx.bounds0) v
    have e2 : readAtF (posOf posA) L (·.2.2.2) (cx.bounds0.contLB[·]!) =
        fun v => (readAtF (posOf posA) L id (bget cx.bounds0) v).2.2.2 :=
      funext fun v => readAtF_proj (posOf posA) L (·.2.2.2) (bget cx.bounds0) v
    rw [e1, e2]

theorem storedGainWith_eq_G (p : Prep) (b : UBounds) (w t d h : Nat) :
    storedGainWith p b w t d h = storedGainG p (b.inlineLB[·]!) (b.mergedLB[·]!) w t d h := by
  unfold storedGainWith storedGainG
  rfl

theorem opaqueUnder_read {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (outAll : Array Nat) (t : Nat) :
    cx.opaqueUnder (cx.rebound (outAll.foldl (fun acc t => acc.set! t false) cx.cand)) t =
      opaqueUnderL cx posA (reboundL cx posA outAll) t := by
  unfold SCtx.opaqueUnder opaqueUnderL
  have h := rebound_read hr outAll t
  unfold bget at h
  have h1 := congrArg (·.1) h
  have h2 := congrArg (·.2.1) h
  simp only at h1 h2
  rw [h1, h2, readAtF_field (posOf posA) _ (fun e : Nat × Nat × Nat × Nat => e.1)
      (bget cx.bounds0) (fun x => cx.bounds0.inlineLB[x]!) (fun _ => rfl),
    readAtF_field (posOf posA) _ (fun e : Nat × Nat × Nat × Nat => e.2.1)
      (bget cx.bounds0) (fun x => cx.bounds0.mergedLB[x]!) (fun _ => rfl)]
  rfl

theorem foldl_setOr_read (l : List Nat) (f : Nat → Bool) (a : Array Bool) (u : Nat) :
    (l.foldl (fun acc t => acc.set! t (acc[t]! || f t)) a)[u]! =
      (a[u]! || (decide (u < a.size) && l.contains u && f u)) := by
  induction l generalizing a with
  | nil => simp
  | cons t l ih =>
    rw [List.foldl_cons, ih, getElem!_setBang]
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, List.contains_cons]
    by_cases hut : u = t
    · subst hut
      by_cases h : u < a.size
      · simp only [h, and_self, if_true, decide_true, Bool.true_and]
        cases a[u]! <;> cases f u <;> simp
      · simp [h]
    · have hne : (u == t) = false := by simpa using hut
      simp [hut, hne]

/-- **Opaque terms.** `SCtx.opaqueArr` read through the local bounds. -/
theorem opaqueArr_read {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (inAll outAll : Array Nat) (t : Nat) :
    (cx.opaqueArr inAll outAll)[t]! = opqArrR cx posA (reboundL cx posA outAll) inAll t := by
  unfold SCtx.opaqueArr opqArrR
  rw [← Array.foldl_toList, foldl_setOr_read, Array.contains_toList, opaqueUnder_read hr]

end LocalSearch

/-! ### The component cost, the visible counts and the reach labels -/

namespace LocalSearch

/-- The closure evaluation of `SCtx.phiE` read through the closure-local table. -/
theorem phiFold_read {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (avail : Nat → Bool) (width : Array (Option Nat))
    (hW : cx.members.foldl (fun acc t => if avail t then acc.set! t (some cx.up.w) else acc)
      cx.widthCs = width) :
    ESize cx.up.prep.dag.size (cx.closure.foldl (evalStep cx.up.prep.dag cx.up.prep.family
      cx.up.prep.spineLen cx.up.prep.tail width cx.allTrue) cx.baseEv) ∧
      ∀ u, eget (cx.closure.foldl (evalStep cx.up.prep.dag cx.up.prep.family cx.up.prep.spineLen
        cx.up.prep.tail width cx.allTrue) cx.baseEv) u =
        readAtF (posOf posC) (phiTable cx posC avail) id (eget cx.baseEv) u := by
  obtain ⟨_, _, _, _, hev, _, _, _, _, hclo⟩ := localSearchOK_spec hr.ok
  have hwid : widthOf width = phiWidth cx avail := by rw [← hW]; exact funext (phiWidth_eq cx avail)
  rw [array_foldl_eq]
  unfold phiTable
  refine fold_local eget (fun s _ t => evalStep cx.up.prep.dag cx.up.prep.family
      cx.up.prep.spineLen cx.up.prep.tail width cx.allTrue s t)
    (fun g _ t => if cx.allTrue[t]! then
      evalRowG cx.up.prep.dag cx.up.prep.family cx.up.prep.spineLen cx.up.prep.tail (widthOf width)
        (fun v => (g v).1) (fun v => (g v).2.1) (fun v => (g v).2.2) t else g t)
    (ESize cx.up.prep.dag.size) cx.closure.size (cx.closure[·]!) (posOf posC) hr.closure ?_
    cx.baseEv hev _ ?_
  · intro s i hs hi
    exact evalStep_get _ _ _ _ _ _ s hs (hclo i hi)
  · intro L i hL hi
    by_cases ha : cx.allTrue[cx.closure[i]!]! = true
    · simp only [ha, if_true]
      rw [hwid,
        readAtF_field_fun (posOf posC) L (fun e : Nat × Nat × Option Nat => e.1) (eget cx.baseEv)
          (fun x => cx.baseEv.cost[x]!) (fun _ => rfl),
        readAtF_field_fun (posOf posC) L (fun e : Nat × Nat × Option Nat => e.2.1) (eget cx.baseEv)
          (fun x => cx.baseEv.sides[x]!) (fun _ => rfl),
        readAtF_field_fun (posOf posC) L (fun e : Nat × Nat × Option Nat => e.2.2) (eget cx.baseEv)
          (fun x => cx.baseEv.below[x]!) (fun _ => rfl)]
    · simp only [ha, Bool.false_eq_true, if_false]
      rw [readAtF_at_new hr.closure L id (eget cx.baseEv) hi hL]
      rfl

/-- **Component cost.** `SCtx.phiE` is the local evaluation's cost. -/
theorem phiE_eq_L {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (avail : Nat → Bool) (stored : Array Nat) :
    cx.phiE avail stored = phiEL cx posC avail stored := by
  obtain ⟨_, _, _, _, hev, _, _, _, _, _⟩ := localSearchOK_spec hr.ok
  unfold SCtx.phiE phiEL
  simp only [evalHidden_eq]
  generalize hW : cx.members.foldl (fun acc t => if avail t then acc.set! t (some cx.up.w) else acc)
    cx.widthCs = width
  obtain ⟨hsz, hrd⟩ := phiFold_read hr avail width hW
  have hwid : widthOf width = phiWidth cx avail := by rw [← hW]; exact funext (phiWidth_eq cx avail)
  generalize cx.closure.foldl (evalStep cx.up.prep.dag cx.up.prep.family cx.up.prep.spineLen
    cx.up.prep.tail width cx.allTrue) cx.baseEv = ev at hsz hrd
  obtain ⟨hc, hs, hb⟩ := hsz
  obtain ⟨hc0, _, _⟩ := hev
  have hC : (fun u => ev.cost[u]!) =
      readAtF (posOf posC) (phiTable cx posC avail) (·.1) (cx.baseEv.cost[·]!) := by
    funext u
    rw [readAtF_field (posOf posC) _ (fun e : Nat × Nat × Option Nat => e.1) (eget cx.baseEv)
      (fun x => cx.baseEv.cost[x]!) (fun _ => rfl), ← hrd u]
    rfl
  have hS : (fun u => ev.sides[u]!) =
      readAtF (posOf posC) (phiTable cx posC avail) (·.2.1) (cx.baseEv.sides[·]!) := by
    funext u
    rw [readAtF_field (posOf posC) _ (fun e : Nat × Nat × Option Nat => e.2.1) (eget cx.baseEv)
      (fun x => cx.baseEv.sides[x]!) (fun _ => rfl), ← hrd u]
    rfl
  have hB : (fun u => ev.below[u]!) =
      readAtF (posOf posC) (phiTable cx posC avail) (·.2.2) (cx.baseEv.below[·]!) := by
    funext u
    rw [readAtF_field (posOf posC) _ (fun e : Nat × Nat × Option Nat => e.2.2) (eget cx.baseEv)
      (fun x => cx.baseEv.below[x]!) (fun _ => rfl), ← hrd u]
    rfl
  have hEH : ∀ x, evalHidden cx.up.prep.dag cx.up.prep.family cx.up.prep.spineLen
      cx.up.prep.tail width cx.allTrue ev x =
      evalHiddenG cx.up.prep.dag cx.up.prep.family cx.up.prep.spineLen cx.up.prep.tail
        (phiWidth cx avail) cx.allTrue[x]! (decide (x < cx.baseEv.cost.size))
        (readAtF (posOf posC) (phiTable cx posC avail) (·.1) (cx.baseEv.cost[·]!))
        (readAtF (posOf posC) (phiTable cx posC avail) (·.2.1) (cx.baseEv.sides[·]!))
        (readAtF (posOf posC) (phiTable cx posC avail) (·.2.2) (cx.baseEv.below[·]!)) x := by
    intro x
    rw [evalHidden_eq_G _ _ _ _ _ _ _ _ (by omega) (by omega), hwid, ← hC, ← hS, ← hB, hc, hc0]
  simp only [hEH]
  have hCr : ∀ r, ev.cost[r]! =
      readAtF (posOf posC) (phiTable cx posC avail) (·.1) (cx.baseEv.cost[·]!) r :=
    fun r => congrFun hC r
  simp only [hCr]

theorem cutScanBest_eq (spineLen : Array Nat) (getS : Nat → Nat) (getB : Nat → Option Nat)
    (widthG : Nat → Option Nat) (l s : Nat) : ∀ fuel cur best work,
    cutScanBest spineLen getS getB widthG l s fuel cur best =
      (cutScanG spineLen getS getB widthG l s fuel cur best work).1
  | 0, _, _, _ => rfl
  | _ + 1, none, _, _ => rfl
  | fuel + 1, some u, best, work => by
    simp only [cutScanBest, cutScanG]
    exact cutScanBest_eq spineLen getS getB widthG l s fuel _ _ _

theorem evalRowB_eq (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (widthG : Nat → Option Nat) (getC getS : Nat → Nat) (getB : Nat → Option Nat) (t : Nat) :
    evalRowB dag family spineLen tail widthG getC getS getB t =
      evalRowG dag family spineLen tail widthG getC getS getB t := by
  unfold evalRowB evalRowG
  simp only [cutScanBest_eq _ _ _ _ _ _ _ _ _ 0]

theorem readAtF_map {α β : Type} [Inhabited α] [Inhabited β] (posf : Nat → Option Nat)
    (L : Array α) (proj : α → β) (base : Nat → β) (u : Nat) :
    readAtF posf (L.map proj) id base u = readAtF posf L proj base u := by
  unfold readAtF
  cases posf u with
  | none => rfl
  | some j =>
    simp only [Array.size_map, id]
    by_cases hj : j < L.size
    · simp only [hj, if_true]
      rw [getElem!_pos (L.map proj) j (by simpa using hj), getElem!_pos L j hj]
      simp
    · simp only [hj, if_false]

theorem readAtF_map_fun {α β : Type} [Inhabited α] [Inhabited β] (posf : Nat → Option Nat)
    (L : Array α) (proj : α → β) (base : Nat → β) :
    readAtF posf (L.map proj) id base = readAtF posf L proj base :=
  funext (readAtF_map posf L proj base)

/-- The member flags mark the area positions of the members satisfying
`avail`. -/
theorem memberFlags_spec {cx : SCtx} {posA : Array Nat}
    (hA : PosFn cx.area.size (cx.area[·]!) (posOf posA)) (avail : Nat → Bool) :
    (memberFlags cx posA avail).size = cx.area.size ∧
      ∀ j, j < cx.area.size → ((memberFlags cx posA avail)[j]! = true ↔
        (cx.members.contains cx.area[j]! = true ∧ avail cx.area[j]! = true)) := by
  unfold memberFlags
  rw [← Array.foldl_toList]
  have hc : ∀ x, cx.members.contains x = cx.members.toList.contains x := fun x => by
    rw [Array.contains_toList]
  simp only [hc]
  generalize cx.members.toList = l
  have key : ∀ (l : List Nat) (fl : Array Bool), fl.size = cx.area.size →
      (l.foldl (fun fl m => match posOf posA m with
        | some j => if avail m then fl.set! j true else fl
        | none => fl) fl).size = cx.area.size ∧
      ∀ j, j < cx.area.size → ((l.foldl (fun fl m => match posOf posA m with
        | some j => if avail m then fl.set! j true else fl
        | none => fl) fl)[j]! = true ↔
        (fl[j]! = true ∨ (l.contains cx.area[j]! = true ∧ avail cx.area[j]! = true))) := by
    intro l
    induction l with
    | nil => intro fl hfl; exact ⟨hfl, fun j _ => by simp⟩
    | cons m l ih =>
      intro fl hfl
      have hstep : ∀ j, j < cx.area.size →
          ((match posOf posA m with
            | some j => if avail m then fl.set! j true else fl
            | none => fl)[j]! = true ↔
            (fl[j]! = true ∨ (cx.area[j]! = m ∧ avail m = true))) := by
        intro j hj
        cases hp : posOf posA m with
        | none =>
          simp only
          have : cx.area[j]! ≠ m := fun h => by
            have := (hA m j).mpr ⟨hj, h⟩
            rw [hp] at this; cases this
          simp [this]
        | some j' =>
          simp only
          obtain ⟨hj', hm⟩ := (hA m j').mp hp
          by_cases ha : avail m = true
          · simp only [ha, if_true, and_true]
            rw [getElem!_setBang]
            by_cases hjj : j = j'
            · subst hjj
              have hm' : cx.area[j]! = m := hm
              have hT : (j = j ∧ j < fl.size) := ⟨rfl, by rw [hfl]; exact hj'⟩
              simp only [hT, and_self, if_true, true_iff]
              exact Or.inr hm'
            · have : cx.area[j]! ≠ m := fun h => by
                have := (hA m j).mpr ⟨hj, h⟩
                rw [hp] at this
                exact hjj (Option.some.inj this).symm
              simp [hjj, this]
          · simp [ha]
      have hsz : (match posOf posA m with
            | some j => if avail m then fl.set! j true else fl
            | none => fl).size = cx.area.size := by
        cases posOf posA m with
        | none => exact hfl
        | some j' =>
          simp only
          split
          · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hfl]
          · exact hfl
      obtain ⟨h1, h2⟩ := ih _ hsz
      refine ⟨h1, fun j hj => ?_⟩
      rw [List.foldl_cons, h2 j hj, hstep j hj]
      constructor
      · rintro ((h | ⟨h1, h2⟩) | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨by simp [h1], by rw [h1]; exact h2⟩
        · refine Or.inr ⟨?_, h2⟩
          simp only [List.contains_iff_mem] at h1 ⊢
          exact List.mem_cons_of_mem m h1
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl (Or.inl h)
        · by_cases hxm : cx.area[j]! = m
          · exact Or.inl (Or.inr ⟨hxm, by rw [← hxm]; exact h2⟩)
          · refine Or.inr ⟨?_, h2⟩
            simp only [List.contains_iff_mem, List.mem_cons] at h1 ⊢
            rcases h1 with h1 | h1
            · exact absurd h1 hxm
            · exact h1
  obtain ⟨h1, h2⟩ := key l (Array.replicate cx.area.size false) (by simp)
  refine ⟨h1, fun j hj => ?_⟩
  rw [h2 j hj]
  simp [getElem!_pos (Array.replicate cx.area.size false) j (by simpa using hj)]

/-- Every member has an area position. -/
def MembersIn (cx : SCtx) (posA : Array Nat) : Prop :=
  ∀ m, cx.members.contains m = true → (posOf posA m).isSome = true

/-- **Widths.** The member flags give the widths of `SCtx.phiE`. -/
theorem flagWidth_eq {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (hm : MembersIn cx posA) (avail : Nat → Bool) :
    flagWidth cx posA (memberFlags cx posA avail) = phiWidth cx avail := by
  funext u
  obtain ⟨_, _, _, _, _, hw, _, _, harea, _⟩ := localSearchOK_spec hr.ok
  obtain ⟨_, hfl⟩ := memberFlags_spec hr.area avail
  unfold flagWidth phiWidth
  cases hp : posOf posA u with
  | none =>
    have hc : cx.members.contains u = false := by
      cases hc : cx.members.contains u
      · rfl
      · have := hm u hc
        rw [hp] at this
        cases this
    simp only [hc, Bool.and_false, Bool.false_and, Bool.false_eq_true, if_false]
  | some j =>
    obtain ⟨hj, hu⟩ := (hr.area u j).mp hp
    have hu' : cx.area[j]! = u := hu
    have hlt : decide (u < cx.widthCs.size) = true := by
      rw [decide_eq_true_eq, hw, ← hu']; exact harea j hj
    have hfj := hfl j hj
    rw [hu'] at hfj
    simp only [hlt, Bool.true_and]
    cases hf : (memberFlags cx posA avail)[j]! with
    | true =>
      obtain ⟨h1, h2⟩ := hfj.mp hf
      simp only [h1, h2, Bool.and_self, if_true]
    | false =>
      have hn : ¬ (cx.members.contains u = true ∧ avail u = true) := fun h => by
        rw [hfj.mpr h] at hf; cases hf
      cases hc : cx.members.contains u with
      | false => simp only [Bool.false_and, Bool.false_eq_true, if_false]
      | true =>
        cases ha : avail u with
        | false => simp only [Bool.and_false, Bool.false_eq_true, if_false]
        | true => exact absurd ⟨hc, ha⟩ hn

/-- A fold that pushes one row per step, kept as three tables. -/
theorem fold3_eq (k : Nat) (xsAt : Nat → Nat)
    (G : Array (Nat × Nat × Option Nat) → Nat → Nat → Nat × Nat × Option Nat)
    (G3 : Array Nat → Array Nat → Array (Option Nat) → Nat → Nat × Nat × Option Nat)
    (hG : ∀ L i, G3 (L.map (·.1)) (L.map (·.2.1)) (L.map (·.2.2)) (xsAt i) = G L i (xsAt i)) :
    foldRange (fun (st : Array Nat × Array Nat × Array (Option Nat)) i =>
      match st with
      | (Lc, Ls, Lb) =>
        match G3 Lc Ls Lb (xsAt i) with
        | (c, s, b) => (Lc.push c, Ls.push s, Lb.push b))
      0 k (Array.mkEmpty k, Array.mkEmpty k, Array.mkEmpty k) =
      ((localFold k xsAt G).map (·.1), (localFold k xsAt G).map (·.2.1),
        (localFold k xsAt G).map (·.2.2)) := by
  unfold localFold
  have key : ∀ m,
      foldRange (fun (st : Array Nat × Array Nat × Array (Option Nat)) i =>
        match st with
        | (Lc, Ls, Lb) =>
          match G3 Lc Ls Lb (xsAt i) with
          | (c, s, b) => (Lc.push c, Ls.push s, Lb.push b))
        0 m (Array.mkEmpty k, Array.mkEmpty k, Array.mkEmpty k) =
      ((foldRange (fun L i => L.push (G L i (xsAt i))) 0 m (Array.mkEmpty k)).map (·.1),
        (foldRange (fun L i => L.push (G L i (xsAt i))) 0 m (Array.mkEmpty k)).map (·.2.1),
        (foldRange (fun L i => L.push (G L i (xsAt i))) 0 m (Array.mkEmpty k)).map (·.2.2)) := by
    intro m
    induction m with
    | zero => simp [foldRange_zero]
    | succ m ih =>
      rw [foldRange_succ, foldRange_succ, ih, Nat.zero_add]
      simp only
      rw [hG]
      rcases G (foldRange (fun L i => L.push (G L i (xsAt i))) 0 m (Array.mkEmpty k)) m (xsAt m)
        with ⟨c, s, b⟩
      simp [Array.map_push]
  exact key k

/-- `phiTable3` is `phiTable` split into its three columns. -/
theorem phiTable3_eq {cx : SCtx} {posA posC : Array Nat} (avail : Nat → Bool)
    (hW : flagWidth cx posA (memberFlags cx posA avail) = phiWidth cx avail) :
    phiTable3 cx posA posC (memberFlags cx posA avail) =
      ((phiTable cx posC avail).map (·.1), (phiTable cx posC avail).map (·.2.1),
        (phiTable cx posC avail).map (·.2.2)) := by
  unfold phiTable3 phiTable
  dsimp only
  refine fold3_eq _ _ _ _ (fun L i => ?_)
  unfold phiRow3
  simp only [readAtF_map_fun, evalRowB_eq, hW]

/-- **Component cost, compiled.** -/
theorem phiEL2_eq {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (hm : MembersIn cx posA) (avail : Nat → Bool) (stored : Array Nat) :
    phiEL cx posC avail stored = phiEL2 cx posA posC avail stored := by
  have hW := flagWidth_eq hr hm avail
  unfold phiEL phiEL2
  simp only [phiTable3_eq avail hW, readAtF_map_fun, hW]

theorem phiE_eq_L2 {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (hm : MembersIn cx posA) (avail : Nat → Bool) (stored : Array Nat) :
    cx.phiE avail stored = phiEL2 cx posA posC avail stored :=
  (phiE_eq_L hr avail stored).trans (phiEL2_eq hr hm avail stored)

/-- **Visible counts.** `SCtx.revisible` read through the local counts. -/
theorem revisible_read {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (outAll : Array Nat) (u : Nat) :
    ((cx.revisible (outAll.foldl (fun acc t => acc.set! t false) cx.cand)).1[u]!,
      (cx.revisible (outAll.foldl (fun acc t => acc.set! t false) cx.cand)).2[u]!) =
      readAtF (posRev cx.area.size posA) (revisibleL cx posA outAll) id
        (fun v => (cx.vis0.1[v]!, cx.vis0.2[v]!)) u := by
  obtain ⟨_, _, hv1, hv2, _, _, _, _, harea, _⟩ := localSearchOK_spec hr.ok
  have hrev : PosFn cx.area.size (fun i => cx.area[cx.area.size - 1 - i]!)
      (posRev cx.area.size posA) := by
    intro v j
    unfold posRev
    constructor
    · intro h
      cases hp : posOf posA v with
      | none => rw [hp] at h; cases h
      | some j0 =>
        rw [hp] at h
        injection h with h
        obtain ⟨hj0, hx⟩ := (hr.area v j0).mp hp
        subst h
        refine ⟨by omega, ?_⟩
        show cx.area[cx.area.size - 1 - (cx.area.size - 1 - j0)]! = v
        rw [show cx.area.size - 1 - (cx.area.size - 1 - j0) = j0 by omega]
        exact hx
    · rintro ⟨hj, hx⟩
      rw [(hr.area v (cx.area.size - 1 - j)).mpr ⟨by omega, hx⟩]
      simp only [Option.some.injEq]
      omega
  unfold SCtx.revisible revisibleL
  rw [list_range_foldl]
  refine (fold_local (S := Array Nat × Array Nat) (V := Nat × Nat)
    (fun s v => (s.1[v]!, s.2[v]!))
    (fun s i _ => match s with
      | (ds, hs) =>
        let j := cx.area.size - 1 - i
        let y := cx.area[j]!
        let r := cx.rootOcc[j]!
        let dh := cx.inEdges[j]!.foldl (fun (dh : Nat × Nat) (e : Nat × Nat × Nat) =>
          let wq := if (outAll.foldl (fun acc t => acc.set! t false) cx.cand)[e.1]! then 1
            else min ds[e.1]! visibleCap
          (dh.1 + e.2.1 * wq, dh.2 + e.2.2 * wq)) (r, r)
        (ds.set! y dh.1, hs.set! y dh.2))
    (fun g i _ =>
      cx.inEdges[cx.area.size - 1 - i]!.foldl (fun (dh : Nat × Nat) (e : Nat × Nat × Nat) =>
        let wq := if (outAll.foldl (fun acc t => acc.set! t false) cx.cand)[e.1]! then 1
          else min (g e.1).1 visibleCap
        (dh.1 + e.2.1 * wq, dh.2 + e.2.2 * wq))
        (cx.rootOcc[cx.area.size - 1 - i]!, cx.rootOcc[cx.area.size - 1 - i]!))
    (fun s => s.1.size = cx.up.prep.dag.size ∧ s.2.size = cx.up.prep.dag.size)
    cx.area.size (fun i => cx.area[cx.area.size - 1 - i]!) (posRev cx.area.size posA) hrev ?_
    cx.vis0 ⟨hv1, hv2⟩ _ ?_).2 u
  · intro s i hs hi
    obtain ⟨ds, hs'⟩ := s
    obtain ⟨h1, h2⟩ := hs
    have hy := harea (cx.area.size - 1 - i) (by omega)
    refine ⟨⟨by simp [h1], by simp [h2]⟩, fun v => ?_⟩
    simp only
    rw [setBang_read (by omega) _ _ h1, setBang_read (by omega) _ _ h2]
    by_cases hv : v = cx.area[cx.area.size - 1 - i]!
    · simp only [hv, if_true]
    · simp only [hv, if_false]
  · intro L i hL hi
    simp only [ms_read, maybeStoredAt]
    simp only [readAtF_field (posRev cx.area.size posA) L (fun e : Nat × Nat => e.1)
      (fun v => (cx.vis0.1[v]!, cx.vis0.2[v]!)) (fun x => cx.vis0.1[x]!) (fun _ => rfl)]

/-- **Reach labels.** `reachLabelsOn` over the closure read through the local labels. -/
theorem reachLabels_read {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (opq : Nat → Bool) (lab : Nat → Option Nat) (u : Nat) :
    (reachLabelsOn cx.up.prep.dag cx.closure opq lab)[u]! =
      readAtF (posOf posC) (reachLabelsL cx.up.prep.dag cx.closure posC opq lab) id
        (fun _ => none) u := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hclo⟩ := localSearchOK_spec hr.ok
  have hbase : (fun (v : Nat) => (Array.replicate cx.up.prep.dag.size
      (none : Option (Option Nat)))[v]!) = fun _ => none := by
    funext v
    by_cases h : v < cx.up.prep.dag.size
    · rw [getElem!_pos _ v (by simpa using h)]; simp
    · rw [getElem!_neg _ v (by simpa using h)]; rfl
  unfold reachLabelsOn reachLabelsL
  rw [array_foldl_eq, ← hbase]
  refine (fold_local (fun (A : Array (Option (Option Nat))) v => A[v]!)
    (fun (A : Array (Option (Option Nat))) _ t => A.set! t ((cx.up.prep.dag.node t).children.foldl (fun v c =>
      labelJoin v (if opq c then (lab c).map some else A[c]!)) ((lab t).map some)))
    (fun g _ t => (cx.up.prep.dag.node t).children.foldl (fun v c =>
      labelJoin v (if opq c then (lab c).map some else g c)) ((lab t).map some))
    (fun (A : Array (Option (Option Nat))) => A.size = cx.up.prep.dag.size) cx.closure.size (cx.closure[·]!) (posOf posC)
    hr.closure ?_ _ (by simp) _ ?_).2 u
  · intro A i hA hi
    refine ⟨by simp [hA], fun v => ?_⟩
    rw [setBang_read (hclo i hi) _ _ hA]
  · intro L i _ _
    rfl

end LocalSearch

/-! ### Reclassification and the separation check -/

namespace LocalSearch

theorem reclassify_eq_L {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (outAll localIn und : Array Nat) :
    (reclassifyL cx posA outAll localIn und).1 = (cx.reclassify outAll localIn und).1 ∧
    (reclassifyL cx posA outAll localIn und).2.1 = (cx.reclassify outAll localIn und).2.1 ∧
    ∀ t, opaqueUnderL cx posA (reclassifyL cx posA outAll localIn und).2.2 t =
      cx.opaqueUnder (cx.reclassify outAll localIn und).2.2 t := by
  have hgain : (und.map fun t =>
      (t, storedGainG cx.up.prep
        (readAtF (posOf posA) (reboundL cx posA outAll) (·.1) (cx.bounds0.inlineLB[·]!))
        (readAtF (posOf posA) (reboundL cx posA outAll) (·.2.1) (cx.bounds0.mergedLB[·]!))
        cx.up.w t (readAtF (posRev cx.area.size posA) (revisibleL cx posA outAll) (·.1)
          (cx.vis0.1[·]!) t)
        (readAtF (posRev cx.area.size posA) (revisibleL cx posA outAll) (·.2)
          (cx.vis0.2[·]!) t),
       1 ≤ readAtF (posRev cx.area.size posA) (revisibleL cx posA outAll) (·.1)
          (cx.vis0.1[·]!) t &&
        readAtF (posRev cx.area.size posA) (revisibleL cx posA outAll) (·.2)
          (cx.vis0.2[·]!) t ≤
        readAtF (posRev cx.area.size posA) (revisibleL cx posA outAll) (·.1)
          (cx.vis0.1[·]!) t)) =
      und.map fun t =>
        (t, storedGainWith cx.up.prep
          (cx.rebound (outAll.foldl (fun acc t => acc.set! t false) cx.cand)) cx.up.w t
          (cx.revisible (outAll.foldl (fun acc t => acc.set! t false) cx.cand)).1[t]!
          (cx.revisible (outAll.foldl (fun acc t => acc.set! t false) cx.cand)).2[t]!,
         1 ≤ (cx.revisible (outAll.foldl (fun acc t => acc.set! t false) cx.cand)).1[t]! &&
          (cx.revisible (outAll.foldl (fun acc t => acc.set! t false) cx.cand)).2[t]! ≤
          (cx.revisible (outAll.foldl (fun acc t => acc.set! t false) cx.cand)).1[t]!) := by
    congr 1
    funext t
    have hv := revisible_read hr outAll t
    have hv1 := congrArg (·.1) hv
    have hv2 := congrArg (·.2) hv
    simp only at hv1 hv2
    rw [storedGainWith_eq_G, hv1, hv2,
      readAtF_field (posRev cx.area.size posA) _ (fun e : Nat × Nat => e.1)
        (fun v => (cx.vis0.1[v]!, cx.vis0.2[v]!)) (fun x => cx.vis0.1[x]!) (fun _ => rfl),
      readAtF_field (posRev cx.area.size posA) _ (fun e : Nat × Nat => e.2)
        (fun v => (cx.vis0.1[v]!, cx.vis0.2[v]!)) (fun x => cx.vis0.2[x]!) (fun _ => rfl)]
    have hI : (fun v => (cx.rebound (outAll.foldl (fun acc t => acc.set! t false) cx.cand)).inlineLB[v]!) =
        readAtF (posOf posA) (reboundL cx posA outAll) (·.1) (cx.bounds0.inlineLB[·]!) := by
      funext v
      rw [readAtF_field (posOf posA) _ (fun e : Nat × Nat × Nat × Nat => e.1) (bget cx.bounds0)
        (fun x => cx.bounds0.inlineLB[x]!) (fun _ => rfl), ← rebound_read hr outAll v]
      rfl
    have hM : (fun v => (cx.rebound (outAll.foldl (fun acc t => acc.set! t false) cx.cand)).mergedLB[v]!) =
        readAtF (posOf posA) (reboundL cx posA outAll) (·.2.1) (cx.bounds0.mergedLB[·]!) := by
      funext v
      rw [readAtF_field (posOf posA) _ (fun e : Nat × Nat × Nat × Nat => e.2.1) (bget cx.bounds0)
        (fun x => cx.bounds0.mergedLB[x]!) (fun _ => rfl), ← rebound_read hr outAll v]
      rfl
    rw [hI, hM]
  unfold reclassifyL SCtx.reclassify
  simp only
  rw [hgain]
  refine ⟨rfl, rfl, fun t => ?_⟩
  exact (opaqueUnder_read hr outAll t).symm

theorem sepCheck_eq_L {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (g inRed outRed : Array Nat) :
    cx.sepCheck g inRed outRed = sepCheckL cx posA posC g inRed outRed := by
  unfold SCtx.sepCheck sepCheckL
  simp only
  have hO : (fun t => (cx.opaqueArr inRed outRed)[t]!) =
      fun t => opqArrR cx posA (reboundL cx posA outRed) inRed t :=
    funext (opaqueArr_read hr inRed outRed)
  have hL : (fun t => (sepLabels cx.up.prep.dag.size cx.members g inRed outRed)[t]!) =
      sepLab cx.up.prep.dag.size cx.members g inRed outRed :=
    funext (sepLabels_read _ _ _ _ _)
  rw [hO, hL]
  simp only [reachLabels_read hr, markTable_read, opaqueArr_read hr, sepLabels_read]

end LocalSearch

/-! ### The search -/

namespace LocalSearch

theorem search_eq_L {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (hm : MembersIn cx posA) (limits : Limits) : ∀ fuel,
    (∀ g inAll outAll st, solvePL cx posA posC limits fuel g inAll outAll st =
      cx.solveP limits fuel g inAll outAll st) ∧
    (∀ g inRed outRed st, solveBodyL cx posA posC limits fuel g inRed outRed st =
      cx.solveBody limits fuel g inRed outRed st) ∧
    (∀ phi0 inCtx outAll nOutCtx localIn und tb st,
      nodePL cx posA posC limits fuel phi0 inCtx outAll nOutCtx localIn und tb st =
        cx.nodeP limits fuel phi0 inCtx outAll nOutCtx localIn und tb st) ∧
    (∀ inAll outAll grps comb st, splitPL cx posA posC limits fuel inAll outAll grps comb st =
      cx.splitP limits fuel inAll outAll grps comb st)
  | 0 => by
    refine ⟨fun _ _ _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ _ _ _ _ _ => ?_,
      fun _ _ _ _ _ => ?_⟩
    · simp only [solvePL, SCtx.solveP]
    · simp only [solveBodyL, SCtx.solveBody]
    · simp only [nodePL, SCtx.nodeP]
    · simp only [splitPL, SCtx.splitP]
  | fuel + 1 => by
    obtain ⟨ihP, ihB, ihN, ihS⟩ := search_eq_L hr hm limits fuel
    refine ⟨fun g inAll outAll st => ?_, fun g inRed outRed st => ?_,
      fun phi0 inCtx outAll nOutCtx localIn und tb st => ?_,
      fun inAll outAll grps comb st => ?_⟩
    · simp only [solvePL, SCtx.solveP, opaqueArr_read hr, sepCheck_eq_L hr, ihB] <;> rfl
    · simp only [solveBodyL, SCtx.solveBody, phiE_eq_L2 hr hm, ihN] <;> rfl
    · obtain ⟨h1, h2, h3⟩ := reclassify_eq_L hr outAll localIn und
      simp only [nodePL, SCtx.nodeP]
      rcases hS : cx.reclassify outAll localIn und with ⟨li, op, b⟩
      rcases hF : reclassifyL cx posA outAll localIn und with ⟨li', op', b'⟩
      rw [hS, hF] at h1 h2
      rw [hS, hF] at h3
      simp only at h1 h2 h3
      subst h1 h2
      simp only [phiE_eq_L2 hr hm, h3, ihN, ihS] <;> rfl
    · cases grps with
      | nil => simp only [splitPL, SCtx.splitP]
      | cons grp grps => simp only [splitPL, SCtx.splitP, ihP, ihS]

/-- **Component search.** -/
theorem searchComponentL_eq {cx : SCtx} {posA posC : Array Nat} (hr : Ready cx posA posC)
    (limits : Limits) (states costEvals : Nat) :
    searchComponentL cx posA posC limits states costEvals =
      searchComponent cx limits states costEvals := by
  unfold searchComponentL
  split
  · rename_i hall
    have hm : MembersIn cx posA := fun m hc => by
      rw [Array.all_eq_true'] at hall
      exact hall m (Array.contains_iff_mem.mp hc)
    unfold searchComponent
    simp only [(search_eq_L hr hm limits _).1] <;> rfl
  · rfl

end LocalSearch

/-! ### Position tables -/

namespace LocalSearch

theorem strictInc_lt {a : Array Nat} (h : strictInc a = true) :
    ∀ i j, i < j → j < a.size → a[i]! < a[j]! := by
  unfold strictInc at h
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    have hs := h j (by omega) hj
    by_cases hij' : i = j
    · subst hij'; exact hs
    · exact Nat.lt_trans (ih (by omega) (by omega)) hs

theorem strictInc_inj {a : Array Nat} (h : strictInc a = true) {i j : Nat} (hi : i < a.size)
    (hj : j < a.size) (he : a[i]! = a[j]!) : i = j := by
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · have := strictInc_lt h i j hlt hj; omega
  · exact heq
  · have := strictInc_lt h j i hgt hi; omega

/-- The entries `setPositions` writes (`xs` distinct, inside `pos`). -/
theorem setPositions_read (pos xs : Array Nat) (hd : strictInc xs = true)
    (hin : ∀ i, i < xs.size → xs[i]! < pos.size) :
    (setPositions pos xs).size = pos.size ∧
      ∀ u, (setPositions pos xs)[u]! =
        if h : ∃ j, j < xs.size ∧ xs[j]! = u then Classical.choose h + 1 else pos[u]! := by
  unfold setPositions
  have key : ∀ m, m ≤ xs.size →
      (foldRange (fun pos j => pos.set! xs[j]! (j + 1)) 0 m pos).size = pos.size ∧
      ∀ u, (foldRange (fun pos j => pos.set! xs[j]! (j + 1)) 0 m pos)[u]! =
        if h : ∃ j, j < m ∧ xs[j]! = u then Classical.choose h + 1 else pos[u]! := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨rfl, fun u => ?_⟩
      have : ¬ ∃ j, j < 0 ∧ xs[j]! = u := by omega
      simp only [foldRange_zero, this, dif_neg, not_false_eq_true]
    | succ m ih =>
      intro hm
      obtain ⟨hsz, hrd⟩ := ih (by omega)
      rw [foldRange_succ, Nat.zero_add]
      refine ⟨by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hsz], fun u => ?_⟩
      rw [getElem!_setBang, hrd u]
      by_cases hu : u = xs[m]!
      · have hex : ∃ j, j < m + 1 ∧ xs[j]! = u := ⟨m, by omega, hu.symm⟩
        have hlt : xs[m]! < pos.size := hin m (by omega)
        simp only [hu, hsz, hlt, and_self, if_true]
        rw [dif_pos (hu ▸ hex)]
        have hc := Classical.choose_spec (hu ▸ hex)
        have := strictInc_inj hd (i := Classical.choose (hu ▸ hex)) (j := m) (by omega) (by omega)
          hc.2
        omega
      · simp only [hu, false_and, if_false]
        by_cases hex : ∃ j, j < m ∧ xs[j]! = u
        · have hex' : ∃ j, j < m + 1 ∧ xs[j]! = u := by
            obtain ⟨j, hj, hx⟩ := hex; exact ⟨j, by omega, hx⟩
          rw [dif_pos hex, dif_pos hex']
          have h1 := Classical.choose_spec hex
          have h2 := Classical.choose_spec hex'
          have : Classical.choose hex = Classical.choose hex' :=
            strictInc_inj hd (by omega) (by omega) (h1.2.trans h2.2.symm)
          rw [this]
        · have hex' : ¬ ∃ j, j < m + 1 ∧ xs[j]! = u := by
            rintro ⟨j, hj, hx⟩
            by_cases hjm : j = m
            · subst hjm; exact hu hx.symm
            · exact hex ⟨j, by omega, hx⟩
          rw [dif_neg hex, dif_neg hex']
  exact key xs.size (Nat.le_refl _)

theorem posOf_some (pos : Array Nat) (u j : Nat) : posOf pos u = some j ↔ pos[u]! = j + 1 := by
  unfold posOf
  by_cases h : pos[u]! = 0
  · simp [h]
  · simp only [h, beq_iff_eq, if_false, Option.some.injEq]
    omega

/-- `setPositions` of an all-`0` table is a position table. -/
theorem setPositions_posFn (xs : Array Nat) (n : Nat) (hd : strictInc xs = true)
    (hin : ∀ i, i < xs.size → xs[i]! < n) :
    PosFn xs.size (xs[·]!) (posOf (setPositions (Array.replicate n 0) xs)) := by
  obtain ⟨_, hrd⟩ := setPositions_read (Array.replicate n 0) xs hd (by simpa using hin)
  intro u j
  rw [posOf_some, hrd u]
  by_cases hex : ∃ j, j < xs.size ∧ xs[j]! = u
  · rw [dif_pos hex]
    have hc := Classical.choose_spec hex
    constructor
    · intro h
      have : Classical.choose hex = j := by omega
      subst this
      exact hc
    · rintro ⟨hj, hx⟩
      have := strictInc_inj hd hc.1 hj (hc.2.trans hx.symm)
      omega
  · rw [dif_neg hex]
    have h0 : (Array.replicate n 0)[u]! = 0 := by
      by_cases h : u < n
      · rw [getElem!_pos _ u (by simpa using h)]; simp
      · rw [getElem!_neg _ u (by simpa using h)]; rfl
    rw [h0]
    constructor
    · intro h; omega
    · intro h; exact absurd ⟨j, h⟩ hex

/-- Clearing the entries of `xs` in a table that is `0` elsewhere gives the
all-`0` table. -/
theorem clearPositions_zero (pos xs : Array Nat) (n : Nat) (hsz : pos.size = n)
    (h0 : ∀ u, (∀ i, i < xs.size → xs[i]! ≠ u) → pos[u]! = 0) :
    clearPositions pos xs = Array.replicate n 0 := by
  unfold clearPositions
  rw [← Array.foldl_toList]
  have key : ∀ (l : List Nat) (a : Array Nat), a.size = n →
      ((l.foldl (fun pos t => pos.set! t 0) a).size = n ∧
        ∀ u, (l.foldl (fun pos t => pos.set! t 0) a)[u]! = if u ∈ l then 0 else a[u]!) := by
    intro l
    induction l with
    | nil => intro a ha; exact ⟨ha, fun u => by simp⟩
    | cons t l ih =>
      intro a ha
      obtain ⟨h1, h2⟩ := ih (a.set! t 0) (by simp [ha])
      refine ⟨by rw [List.foldl_cons]; exact h1, fun u => ?_⟩
      rw [List.foldl_cons, h2 u, getElem!_setBang]
      by_cases hu : u ∈ l
      · simp [hu]
      · by_cases hut : u = t
        · subst hut
          by_cases hlt : u < a.size
          · simp [hu, hlt]
          · simp [hu, hlt]
        · simp [hu, hut]
  obtain ⟨h1, h2⟩ := key xs.toList pos hsz
  apply Array.ext
  · rw [Array.size_replicate]; exact h1
  · intro i hi1 hi2
    have := h2 i
    rw [getElem!_pos _ i hi1] at this
    rw [this]
    by_cases hm : i ∈ xs.toList
    · simp [hm]
    · simp only [hm, if_false, Array.getElem_replicate]
      have hne : ∀ j, j < xs.size → xs[j]! ≠ i := by
        intro j hj hx
        apply hm
        rw [Array.mem_toList_iff, Array.mem_iff_getElem]
        exact ⟨j, hj, by rw [getElem!_pos xs j hj] at hx; exact hx⟩
      exact h0 i hne

end LocalSearch

/-! ### The closure walk -/

namespace LocalSearch

theorem node_children_lt {dag : Dag} (h : childrenPrecede dag.nodes = true) {t : Nat}
    (ht : t < dag.size) {c : Nat} (hc : c ∈ (dag.node t).children) : c < t := by
  unfold childrenPrecede at h
  rw [Array.all_eq_true] at h
  have := h t (by simpa [Dag.size] using ht)
  simp only [Array.getElem_zipIdx, Nat.zero_add] at this
  rw [Array.all_eq_true] at this
  have hn : dag.node t = dag.nodes[t] := by
    unfold Dag.node; simp only [Dag.size] at ht; simp [ht]
  rw [hn] at hc
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hc
  have := this k hk
  simp only [decide_eq_true_eq] at this
  exact this

theorem modify_read {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (f : α → α) :
    (a.modify i f)[j]! = if i = j ∧ i < a.size then f a[j]! else a[j]! := by
  simp only [getElem!_def, Array.getElem?_modify]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size <;> simp [hi]
  · simp [hij]

/-- **Parents.** `q` is listed under `c` iff `c` is a child of `q`, both in
the DAG. -/
theorem mem_parentsOf (dag : Dag) (c q : Nat) :
    q ∈ (parentsOf dag)[c]! ↔ c < dag.size ∧ q < dag.size ∧ c ∈ (dag.node q).children := by
  unfold parentsOf
  have inner : ∀ (m : Nat) (l : List Nat) (P : Array (Array Nat)), P.size = dag.size →
      (l.foldl (fun P c => P.modify c (·.push m)) P).size = dag.size ∧
      ∀ c q, q ∈ (l.foldl (fun P c => P.modify c (·.push m)) P)[c]! ↔
        q ∈ P[c]! ∨ (q = m ∧ c < dag.size ∧ c ∈ l) := by
    intro m l
    induction l with
    | nil => intro P hP; exact ⟨hP, fun c q => by simp⟩
    | cons c0 l ih =>
      intro P hP
      obtain ⟨h1, h2⟩ := ih (P.modify c0 (·.push m)) (by simp [hP])
      refine ⟨h1, fun c q => ?_⟩
      rw [List.foldl_cons, h2, modify_read]
      by_cases hc : c0 = c
      · subst hc
        by_cases hlt : c0 < P.size
        · simp only [hlt, and_self, if_true, Array.mem_push, List.mem_cons, true_or, and_true]
          rw [hP] at hlt
          simp only [hlt, true_and]
          constructor
          · rintro ((h | h) | ⟨h1, _, _⟩) <;> simp_all
          · rintro (h | h) <;> simp_all
        · have : ¬ c0 < dag.size := by omega
          simp [hlt, this]
      · simp only [hc, false_and, if_false, List.mem_cons]
        constructor
        · rintro (h | ⟨h1, h2, h3⟩)
          · exact Or.inl h
          · exact Or.inr ⟨h1, h2, Or.inr h3⟩
        · rintro (h | ⟨h1, h2, h3 | h3⟩)
          · exact Or.inl h
          · exact absurd h3.symm hc
          · exact Or.inr ⟨h1, h2, h3⟩
  have key : ∀ m, m ≤ dag.size →
      (foldRange (fun P q => (dag.node q).children.foldl (fun P c => P.modify c (·.push q)) P)
        0 m (Array.replicate dag.size #[])).size = dag.size ∧
      ∀ c q, q ∈ (foldRange (fun P q => (dag.node q).children.foldl
        (fun P c => P.modify c (·.push q)) P) 0 m (Array.replicate dag.size #[]))[c]! ↔
        c < dag.size ∧ q < m ∧ c ∈ (dag.node q).children := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨by simp [foldRange_zero], fun c q => ?_⟩
      rw [foldRange_zero]
      constructor
      · intro h
        by_cases hc : c < dag.size
        · rw [getElem!_pos _ c (by simpa using hc)] at h; simp at h
        · rw [getElem!_neg _ c (by simpa using hc)] at h
          exact absurd h (by simp [show (default : Array Nat) = #[] from rfl])
      · rintro ⟨_, h, _⟩; omega
    | succ m ih =>
      intro hm
      obtain ⟨hs, hr⟩ := ih (by omega)
      rw [foldRange_succ, Nat.zero_add, ← Array.foldl_toList]
      obtain ⟨h1, h2⟩ := inner m (dag.node m).children.toList _ hs
      refine ⟨h1, fun c q => ?_⟩
      rw [h2, hr, Array.mem_toList_iff]
      constructor
      · rintro (⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩)
        · exact ⟨a1, by omega, a3⟩
        · rw [a1]; exact ⟨a2, by omega, a3⟩
      · rintro ⟨a1, a2, a3⟩
        by_cases hqm : q = m
        · rw [hqm] at a3; exact Or.inr ⟨hqm, a1, a3⟩
        · exact Or.inl ⟨a1, by omega, a3⟩
  obtain ⟨_, h⟩ := key dag.size (Nat.le_refl _)
  rw [h]

/-- Members (by `isMember`) and their ancestors. -/
inductive Up (dag : Dag) (isMember : Nat → Bool) : Nat → Prop
  | mem {t : Nat} : t < dag.size → isMember t = true → Up dag isMember t
  | par {t c : Nat} : t < dag.size → c ∈ (dag.node t).children → Up dag isMember c →
      Up dag isMember t

theorem Up.lt {dag : Dag} {isMember : Nat → Bool} {t : Nat} (h : Up dag isMember t) :
    t < dag.size := by
  cases h with
  | mem h _ => exact h
  | par h _ _ => exact h

/-- **Closure.** With children before their parents, `upClosure` lists the
members and their ancestors, ascending. -/
theorem mem_upClosure {dag : Dag} (hcp : childrenPrecede dag.nodes = true)
    (isMember : Nat → Bool) (t : Nat) :
    t ∈ (upClosure dag isMember).toList ↔ Up dag isMember t := by
  unfold upClosure
  have key : ∀ m, m ≤ dag.size →
      (foldRange (fun (acc : Array Bool) t =>
        acc.set! t (isMember t || (dag.node t).children.any (acc[·]!))) 0 m
        (Array.replicate dag.size false)).size = dag.size ∧
      ∀ t, (foldRange (fun (acc : Array Bool) t =>
        acc.set! t (isMember t || (dag.node t).children.any (acc[·]!))) 0 m
        (Array.replicate dag.size false))[t]! = true ↔ t < m ∧ Up dag isMember t := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨by simp [foldRange_zero], fun t => ?_⟩
      rw [foldRange_zero]
      constructor
      · intro h
        by_cases ht : t < dag.size
        · rw [getElem!_pos _ t (by simpa using ht)] at h; simp at h
        · rw [getElem!_neg _ t (by simpa using ht)] at h; exact absurd h (by decide)
      · rintro ⟨h, _⟩; omega
    | succ m ih =>
      intro hm
      obtain ⟨hs, hr⟩ := ih (by omega)
      rw [foldRange_succ, Nat.zero_add]
      refine ⟨by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hs], fun t => ?_⟩
      rw [getElem!_setBang]
      by_cases htm : t = m
      · subst htm
        simp only [hs, show t < dag.size by omega, and_self, if_true, Bool.or_eq_true,
          Array.any_eq_true]
        constructor
        · rintro (h | ⟨k, hk, hc⟩)
          · exact ⟨by omega, .mem (by omega) h⟩
          · have hcm := (hr _).mp hc
            exact ⟨by omega, .par (by omega) (Array.getElem_mem hk) hcm.2⟩
        · rintro ⟨_, hu⟩
          cases hu with
          | mem _ h => exact Or.inl h
          | par _ hc hu' =>
            right
            obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hc
            exact ⟨k, hk, (hr _).mpr ⟨node_children_lt hcp (by omega) hc, hu'⟩⟩
      · simp only [htm, false_and, if_false]
        rw [hr t]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  obtain ⟨hs, hr⟩ := key dag.size (Nat.le_refl _)
  rw [Array.toList_filter, List.mem_filter, Array.mem_toList_iff, Array.mem_range, hr t]
  constructor
  · rintro ⟨_, _, h⟩; exact h
  · intro h; exact ⟨h.lt, h.lt, h⟩

theorem upClosure_sorted (dag : Dag) (isMember : Nat → Bool) :
    (upClosure dag isMember).toList.Pairwise (· < ·) := by
  unfold upClosure
  rw [Array.toList_filter, Array.toList_range]
  exact List.pairwise_lt_range.filter _

end LocalSearch

namespace LocalSearch

/-- The closure walk's invariant over `(marks, found, stack)`. -/
structure WalkInv (dag : Dag) (isMember : Nat → Bool) (P : Array (Array Nat)) (n : Nat)
    (st : Array Nat × Array Nat × Array Nat) : Prop where
  size : st.1.size = n
  marks : ∀ t, st.1[t]! = if t ∈ st.2.1.toList then 1 else 0
  nodup : st.2.1.toList.Nodup
  up : ∀ t ∈ st.2.1.toList, Up dag isMember t
  stackIn : ∀ t ∈ st.2.2.toList, t ∈ st.2.1.toList
  stackNodup : st.2.2.toList.Nodup
  done : ∀ t ∈ st.2.1.toList, t ∉ st.2.2.toList → ∀ q ∈ (P[t]!).toList, q < n →
    q ∈ st.2.1.toList

theorem walkPush_spec {dag : Dag} {isMember : Nat → Bool} {P : Array (Array Nat)} {n : Nat}
    (vis out stack : Array Nat) (except : Nat → Prop)
    (hsz : vis.size = n) (hmk : ∀ t, vis[t]! = if t ∈ out.toList then 1 else 0)
    (hnd : out.toList.Nodup) (hup : ∀ t ∈ out.toList, Up dag isMember t)
    (hsi : ∀ t ∈ stack.toList, t ∈ out.toList) (hsn : stack.toList.Nodup)
    (hdn : ∀ t ∈ out.toList, t ∉ stack.toList → ¬ except t → ∀ q ∈ (P[t]!).toList, q < n →
      q ∈ out.toList)
    (q : Nat) (hq : q < n → Up dag isMember q) :
    let r := walkPush n (vis, out, stack) q
    r.1.size = n ∧ (∀ t, r.1[t]! = if t ∈ r.2.1.toList then 1 else 0) ∧ r.2.1.toList.Nodup ∧
    (∀ t ∈ r.2.1.toList, Up dag isMember t) ∧ (∀ t ∈ r.2.2.toList, t ∈ r.2.1.toList) ∧
    r.2.2.toList.Nodup ∧
    (∀ t ∈ r.2.1.toList, t ∉ r.2.2.toList → ¬ except t → ∀ q ∈ (P[t]!).toList, q < n →
      q ∈ r.2.1.toList) ∧
    (∀ t ∈ out.toList, t ∈ r.2.1.toList) ∧ (q < n → q ∈ r.2.1.toList) := by
  intro r
  unfold r walkPush
  by_cases hnew : q < n ∧ vis[q]! = 0
  · have hc : (decide (q < n) && vis[q]! == 0) = true := by simp [hnew.1, hnew.2]
    simp only [hc, if_true]
    have hqo : q ∉ out.toList := by
      intro h; have := hmk q; rw [if_pos h] at this; omega
    refine ⟨by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hsz], fun t => ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [setBang_read (n := n) hnew.1 _ _ hsz, hmk t]
      simp only [Array.toList_push, List.mem_append, List.mem_singleton]
      by_cases htq : t = q
      · simp [htq]
      · simp [htq]
    · rw [Array.toList_push, List.nodup_append]
      refine ⟨hnd, by simp, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb
      exact fun h => hqo (h ▸ ha)
    · intro t ht
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact hup t ht
      · exact hq hnew.1
    · intro t ht
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at ht ⊢
      rcases ht with ht | rfl
      · exact Or.inl (hsi t ht)
      · exact Or.inr rfl
    · rw [Array.toList_push, List.nodup_append]
      refine ⟨hsn, by simp, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb
      exact fun h => hqo (h ▸ hsi a ha)
    · intro t ht hts hex q' hq' hq'n
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at ht hts ⊢
      rcases ht with ht | rfl
      · exact Or.inl (hdn t ht (fun h => hts (Or.inl h)) hex q' hq' hq'n)
      · exact absurd (Or.inr rfl) hts
    · intro t ht
      rw [Array.toList_push, List.mem_append]
      exact Or.inl ht
    · intro _
      rw [Array.toList_push, List.mem_append, List.mem_singleton]
      exact Or.inr rfl
  · have hc : (decide (q < n) && vis[q]! == 0) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
      by_cases h1 : q < n
      · exact Or.inr (fun h2 => hnew ⟨h1, h2⟩)
      · exact Or.inl h1
    simp only [hc, Bool.false_eq_true, if_false]
    refine ⟨hsz, hmk, hnd, hup, hsi, hsn, hdn, fun t ht => ht, fun hqn => ?_⟩
    have h0 : vis[q]! ≠ 0 := fun h => hnew ⟨hqn, h⟩
    have := hmk q
    by_cases hm : q ∈ out.toList
    · exact hm
    · rw [if_neg hm] at this; exact absurd this h0

end LocalSearch

namespace LocalSearch

theorem walkFold_spec {dag : Dag} {isMember : Nat → Bool} {P : Array (Array Nat)} {n : Nat}
    (except : Nat → Prop) : ∀ (qs : List Nat) (vis out stack : Array Nat),
    vis.size = n → (∀ t, vis[t]! = if t ∈ out.toList then 1 else 0) → out.toList.Nodup →
    (∀ t ∈ out.toList, Up dag isMember t) → (∀ t ∈ stack.toList, t ∈ out.toList) →
    stack.toList.Nodup →
    (∀ t ∈ out.toList, t ∉ stack.toList → ¬ except t → ∀ q ∈ (P[t]!).toList, q < n →
      q ∈ out.toList) →
    (∀ q ∈ qs, q < n → Up dag isMember q) →
    let r := qs.foldl (walkPush n) (vis, out, stack)
    r.1.size = n ∧ (∀ t, r.1[t]! = if t ∈ r.2.1.toList then 1 else 0) ∧ r.2.1.toList.Nodup ∧
    (∀ t ∈ r.2.1.toList, Up dag isMember t) ∧ (∀ t ∈ r.2.2.toList, t ∈ r.2.1.toList) ∧
    r.2.2.toList.Nodup ∧
    (∀ t ∈ r.2.1.toList, t ∉ r.2.2.toList → ¬ except t → ∀ q ∈ (P[t]!).toList, q < n →
      q ∈ r.2.1.toList) ∧
    (∀ t ∈ out.toList, t ∈ r.2.1.toList) ∧ (∀ q ∈ qs, q < n → q ∈ r.2.1.toList)
  | [], vis, out, stack, h1, h2, h3, h4, h5, h6, h7, _ =>
    ⟨h1, h2, h3, h4, h5, h6, h7, fun _ h => h, fun _ h => absurd h (by simp)⟩
  | q :: qs, vis, out, stack, h1, h2, h3, h4, h5, h6, h7, hqs => by
    intro r
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ :=
      walkPush_spec (dag := dag) (isMember := isMember) (P := P) vis out stack except h1 h2 h3
        h4 h5 h6 h7 q (hqs q List.mem_cons_self)
    unfold r
    rw [List.foldl_cons]
    generalize hw : walkPush n (vis, out, stack) q = w at a1 a2 a3 a4 a5 a6 a7 a8 a9
    obtain ⟨vis', out', stack'⟩ := w
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := walkFold_spec except qs vis' out' stack' a1 a2
      a3 a4 a5 a6 a7 (fun q' hq' => hqs q' (List.mem_cons_of_mem _ hq'))
    refine ⟨b1, b2, b3, b4, b5, b6, b7, fun t ht => b8 t (a8 t ht), fun q' hq' hq'n => ?_⟩
    rcases List.mem_cons.mp hq' with rfl | hq'
    · exact b8 _ (a9 hq'n)
    · exact b9 q' hq' hq'n

theorem walkLoop_spec {dag : Dag} {isMember : Nat → Bool} {n : Nat} (hn : n = dag.size) :
    ∀ (fuel : Nat) (st : Array Nat × Array Nat × Array Nat),
    WalkInv dag isMember (parentsOf dag) n st →
    WalkInv dag isMember (parentsOf dag) n (walkLoop (parentsOf dag) n fuel st) ∧
      ∀ t ∈ st.2.1.toList, t ∈ (walkLoop (parentsOf dag) n fuel st).2.1.toList
  | 0, st, h => ⟨h, fun _ ht => ht⟩
  | fuel + 1, (vis, out, stack), h => by
    unfold walkLoop
    cases hb : stack.back? with
    | none => exact ⟨h, fun _ ht => ht⟩
    | some c =>
      simp only
      obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.mp hb
      have hcin : c ∈ out.toList := h.stackIn c (by simp)
      have hcup : Up dag isMember c := h.up c hcin
      rw [Array.pop_push, ← Array.foldl_toList]
      have hstk : ∀ t, t ∈ ys.toList → t ∈ (ys.push c).toList := by
        intro t ht; simp [ht]
      have hnd' : ys.toList.Nodup := by
        have := h.stackNodup
        rw [Array.toList_push, List.nodup_append] at this
        exact this.1
      have hcys : c ∉ ys.toList := by
        have := h.stackNodup
        rw [Array.toList_push, List.nodup_append] at this
        exact fun hc => this.2.2 c hc c (by simp) rfl
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ :=
        walkFold_spec (dag := dag) (isMember := isMember) (P := parentsOf dag) (n := n)
          (fun t => t = c) ((parentsOf dag)[c]!).toList vis out ys h.size h.marks h.nodup h.up
          (fun t ht => h.stackIn t (hstk t ht)) hnd'
          (fun t ht hts hne q hq hqn => h.done t ht (by
            intro hts'
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hts'
            rcases hts' with hts' | rfl
            · exact hts hts'
            · exact hne rfl) q hq hqn)
          (fun q hq hqn => by
            rw [Array.mem_toList_iff, mem_parentsOf] at hq
            exact .par (by omega) hq.2.2 hcup)
      generalize hw : ((parentsOf dag)[c]!).toList.foldl (walkPush n) (vis, out, ys) = w
        at a1 a2 a3 a4 a5 a6 a7 a8 a9
      have hinv : WalkInv dag isMember (parentsOf dag) n w := by
        refine ⟨a1, a2, a3, a4, a5, a6, fun t ht hts q hq hqn => ?_⟩
        by_cases htc : t = c
        · subst htc; exact a9 q (by simpa using hq) hqn
        · exact a7 t ht hts htc q hq hqn
      obtain ⟨b1, b2⟩ := walkLoop_spec hn fuel w hinv
      exact ⟨b1, fun t ht => b2 t (a8 t ht)⟩

/-- **Closure walk.** From all-`0` marks, the walk keeps its invariant, and
when its stack is empty it has found exactly the members and their
ancestors. -/
theorem upWalk_spec (dag : Dag) (members : Array Nat) :
    let isMem := fun t => (markTable dag.size members)[t]!
    let r := upWalk (parentsOf dag) members (Array.replicate dag.size 0)
    WalkInv dag isMem (parentsOf dag) dag.size r ∧
      (r.2.2.toList = [] → ∀ t, t ∈ r.2.1.toList ↔ Up dag isMem t) := by
  intro isMem r
  have hm0 : ∀ t, (Array.replicate dag.size 0)[t]! = if t ∈ (#[] : Array Nat).toList then 1 else 0 := by
    intro t
    by_cases h : t < dag.size
    · rw [getElem!_pos _ t (by simpa using h)]; simp
    · rw [getElem!_neg _ t (by simpa using h)]; simp
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ :=
    walkFold_spec (dag := dag) (isMember := isMem) (P := parentsOf dag) (n := dag.size)
      (fun _ => False) members.toList (Array.replicate dag.size 0) #[] #[] (by simp) hm0
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (fun q hq hqn => .mem hqn (by
        show (markTable dag.size members)[q]! = true
        rw [markTable_read]; simp [hqn, Array.mem_toList_iff.mp hq]))
  have hinv0 : WalkInv dag isMem (parentsOf dag) dag.size
      (members.toList.foldl (walkPush dag.size) (Array.replicate dag.size 0, #[], #[])) :=
    ⟨a1, a2, a3, a4, a5, a6, fun t ht hts q hq hqn => a7 t ht hts (fun h => h) q hq hqn⟩
  unfold r upWalk
  simp only [Array.size_replicate]
  rw [← Array.foldl_toList]
  obtain ⟨b1, b2⟩ := walkLoop_spec (isMember := isMem) rfl (dag.size + 1) _ hinv0
  refine ⟨b1, fun hempty t => ⟨fun ht => b1.up t ht, fun hup => ?_⟩⟩
  induction hup with
  | mem hlt hm =>
    apply b2
    apply a9 _ _ hlt
    have : (markTable dag.size members)[_]! = true := hm
    rw [markTable_read] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    simpa using this.2
  | @par t c hlt hc hu ih =>
    exact b1.done c ih (by rw [hempty]; simp) t
      (by rw [Array.mem_toList_iff, mem_parentsOf]; exact ⟨hu.lt, hlt, hc⟩) hlt

end LocalSearch

/-! ### The context -/

namespace LocalSearch

theorem strictInc_of_sorted {a : Array Nat} (h : a.toList.Pairwise (· < ·)) : strictInc a = true := by
  unfold strictInc
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
  intro i _ hi
  rw [List.pairwise_iff_getElem] at h
  have := h i (i + 1) (by simpa using (show i < a.size by omega)) (by simpa using hi) (by omega)
  rw [getElem!_pos a i (by omega), getElem!_pos a (i + 1) hi]
  simpa using this

theorem mem_of_getElem! {a : Array Nat} {i : Nat} (hi : i < a.size) : a[i]! ∈ a.toList := by
  rw [getElem!_pos a i hi, Array.mem_toList_iff]
  exact Array.getElem_mem hi

theorem mergeSort_eq_of_mem {l : List Nat} {C : Array Nat} (hnd : l.Nodup)
    (hmem : ∀ t, t ∈ l ↔ t ∈ C.toList) (hs : C.toList.Pairwise (· < ·)) :
    (l.mergeSort fun a b => decide (a ≤ b)).toArray = C := by
  apply Array.ext'
  rw [List.toList_toArray]
  have hp : List.Perm (l.mergeSort fun a b => decide (a ≤ b)) C.toList := by
    refine (List.mergeSort_perm l _).trans ?_
    rw [List.perm_ext_iff_of_nodup hnd (hs.imp Nat.ne_of_lt)]
    exact hmem
  refine List.Perm.eq_of_pairwise (le := fun a b => a ≤ b) (fun a b _ _ h1 h2 => by omega) ?_
    (hs.imp Nat.le_of_lt) hp
  have := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  exact this.imp (fun h => by simpa using h)

theorem setPositions_congr (a b xs : Array Nat) (hs : strictInc xs = true)
    (hab : a.size = b.size) (hin : ∀ i, i < xs.size → xs[i]! < a.size)
    (h : ∀ u, (∀ i, i < xs.size → xs[i]! ≠ u) → a[u]! = b[u]!) :
    setPositions a xs = setPositions b xs := by
  obtain ⟨ha1, ha2⟩ := setPositions_read a xs hs hin
  obtain ⟨hb1, hb2⟩ := setPositions_read b xs hs (fun i hi => hab ▸ hin i hi)
  apply Array.ext
  · rw [ha1, hb1, hab]
  · intro i hi1 hi2
    have e1 := ha2 i
    have e2 := hb2 i
    rw [getElem!_pos _ i hi1] at e1
    rw [getElem!_pos _ i hi2] at e2
    rw [e1, e2]
    by_cases hex : ∃ j, j < xs.size ∧ xs[j]! = i
    · rw [dif_pos hex, dif_pos hex]
    · rw [dif_neg hex, dif_neg hex]
      exact h i (fun j hj hx => hex ⟨j, hj, hx⟩)

/-- **Context.** With children before their parents, `mkSCtxL` builds the
context of `mkSCtx` and the closure's position table. -/
theorem mkSCtxL_eq (ex : Expanded) (f : GraphFacts) (up : UPrep) (cand : Array Bool)
    (b0 : UBounds) (vis0 : Array Nat × Array Nat) (rootCount : Array Nat) (slack : Nat)
    (theta : _root_.Int) (baseEv : DictEval) (widthCs : Array (Option Nat)) (allTrue : Array Bool)
    (unc : Array Nat) (members : Array Nat) (hcp : childrenPrecede ex.dag.nodes = true) :
    mkSCtxL ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc
      (parentsOf ex.dag) (Array.replicate ex.dag.size 0) members =
    (mkSCtx ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc members,
      setPositions (Array.replicate ex.dag.size 0)
        (upClosure ex.dag ((markTable ex.dag.size members)[·]!))) := by
  obtain ⟨hinv, hdone⟩ := upWalk_spec ex.dag members
  have hCs := upClosure_sorted ex.dag ((markTable ex.dag.size members)[·]!)
  have hCmem := mem_upClosure hcp ((markTable ex.dag.size members)[·]!)
  have hCinc := strictInc_of_sorted hCs
  have hCin : ∀ i, i < (upClosure ex.dag ((markTable ex.dag.size members)[·]!)).size →
      (upClosure ex.dag ((markTable ex.dag.size members)[·]!))[i]! < ex.dag.size :=
    fun i hi => ((hCmem _).mp (mem_of_getElem! hi)).lt
  -- the closure and the marks of the walk
  have hres : (if (upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0)).2.2.isEmpty then
        (((upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0)).2.1.toList.mergeSort
          fun a b => decide (a ≤ b)).toArray,
         (upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0)).1)
      else (upClosure ex.dag ((markTable ex.dag.size members)[·]!),
        clearPositions (upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0)).1
          (upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0)).2.1)).1 =
      upClosure ex.dag ((markTable ex.dag.size members)[·]!) ∧
    setPositions (if (upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0)).2.2.isEmpty then
        (((upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0)).2.1.toList.mergeSort
          fun a b => decide (a ≤ b)).toArray,
         (upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0)).1)
      else (upClosure ex.dag ((markTable ex.dag.size members)[·]!),
        clearPositions (upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0)).1
          (upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0)).2.1)).2
      (upClosure ex.dag ((markTable ex.dag.size members)[·]!)) =
      setPositions (Array.replicate ex.dag.size 0)
        (upClosure ex.dag ((markTable ex.dag.size members)[·]!)) := by
    generalize upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0) = r at hinv hdone
    obtain ⟨vis, out, stack⟩ := r
    by_cases he : stack.isEmpty = true
    · simp only [he, if_true]
      have hst : stack.toList = [] := by
        rw [Array.isEmpty_iff] at he; subst he; rfl
      have hfound := hdone hst
      have hc : (out.toList.mergeSort fun a b => decide (a ≤ b)).toArray =
          upClosure ex.dag ((markTable ex.dag.size members)[·]!) :=
        mergeSort_eq_of_mem hinv.nodup (fun t => (hfound t).trans (hCmem t).symm) hCs
      refine ⟨hc, ?_⟩
      apply setPositions_congr _ _ _ hCinc (by rw [hinv.size]; simp)
        (fun i hi => by rw [hinv.size]; exact hCin i hi)
      intro u hu
      rw [hinv.marks u]
      have hnot : u ∉ out.toList := by
        intro hm
        have hmC := (hCmem u).mpr ((hfound u).mp hm)
        rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hmC
        obtain ⟨i, hi, rfl⟩ := hmC
        exact hu i hi (by rw [getElem!_pos _ i hi])
      rw [if_neg hnot]
      by_cases hlt : u < ex.dag.size
      · rw [getElem!_pos _ u (by simpa using hlt)]; simp
      · rw [getElem!_neg _ u (by simpa using hlt)]; rfl
    · simp only [he, Bool.false_eq_true, if_false]
      refine ⟨trivial, ?_⟩
      rw [clearPositions_zero vis out ex.dag.size hinv.size (fun u hu => by
        rw [hinv.marks u]
        have hnot : u ∉ out.toList := by
          intro hm
          rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hm
          obtain ⟨i, hi, rfl⟩ := hm
          exact hu i hi (by rw [getElem!_pos _ i hi])
        rw [if_neg hnot])]
  obtain ⟨hcl, hpos⟩ := hres
  unfold mkSCtxL mkSCtx
  simp only
  generalize upWalk (parentsOf ex.dag) members (Array.replicate ex.dag.size 0) = r at hcl hpos
  obtain ⟨vis, out, stack⟩ := r
  simp only at hcl hpos ⊢
  rw [hcl, hpos]
  have hroots : (fun (r : Nat) => (setPositions (Array.replicate ex.dag.size 0)
      (upClosure ex.dag ((markTable ex.dag.size members)[·]!)))[r]! != 0) =
      fun (r : Nat) => (markTable ex.dag.size (upClosure ex.dag ((markTable ex.dag.size members)[·]!)))[r]! := by
    funext r
    have hpf := setPositions_posFn _ ex.dag.size hCinc hCin
    rw [markTable_read]
    by_cases hm : r ∈ (upClosure ex.dag ((markTable ex.dag.size members)[·]!)).toList
    · have hlt := ((hCmem r).mp hm).lt
      rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hm
      obtain ⟨i, hi, hx⟩ := hm
      have := (hpf r i).mpr ⟨hi, by simp only; rw [getElem!_pos _ i hi]; exact hx⟩
      rw [posOf_some] at this
      rw [this]
      have : (upClosure ex.dag ((markTable ex.dag.size members)[·]!)).contains r = true := by
        rw [Array.contains_iff_mem, Array.mem_iff_getElem]; exact ⟨i, hi, hx⟩
      have hlt' : (upClosure ex.dag ((markTable ex.dag.size members)[·]!))[i] < ex.dag.size := by
        have := hCin i hi
        rwa [getElem!_pos _ i hi] at this
      simp [← hx, hlt']
    · have hnone : ∀ j, ¬ posOf (setPositions (Array.replicate ex.dag.size 0)
          (upClosure ex.dag ((markTable ex.dag.size members)[·]!))) r = some j := by
        intro j hj
        obtain ⟨hj1, hj2⟩ := (hpf r j).mp hj
        simp only at hj2
        exact hm (hj2 ▸ mem_of_getElem! hj1)
      have h0 : (setPositions (Array.replicate ex.dag.size 0)
          (upClosure ex.dag ((markTable ex.dag.size members)[·]!)))[r]! = 0 := by
        cases hz : (setPositions (Array.replicate ex.dag.size 0)
            (upClosure ex.dag ((markTable ex.dag.size members)[·]!)))[r]! with
        | zero => rfl
        | succ k => exact absurd ((posOf_some _ r k).mpr hz) (hnone k)
      have : (upClosure ex.dag ((markTable ex.dag.size members)[·]!)).contains r = false := by
        rw [Bool.eq_false_iff, ne_eq, Array.contains_iff_mem, ← Array.mem_toList_iff]
        exact hm
      simp only [h0, this, bne_self_eq_false, Bool.and_false]
  rw [hroots]

end LocalSearch

/-! ### The loop -/

namespace LocalSearch

theorem clear_set_zero (n : Nat) (xs : Array Nat) (hs : strictInc xs = true)
    (hin : ∀ i, i < xs.size → xs[i]! < n) :
    clearPositions (setPositions (Array.replicate n 0) xs) xs = Array.replicate n 0 := by
  obtain ⟨h1, h2⟩ := setPositions_read (Array.replicate n 0) xs hs (by simpa using hin)
  apply clearPositions_zero _ _ n (by rw [h1]; simp)
  intro u hu
  rw [h2 u, dif_neg (fun ⟨j, hj, hx⟩ => hu j hj hx)]
  by_cases h : u < n
  · rw [getElem!_pos _ u (by simpa using h)]; simp
  · rw [getElem!_neg _ u (by simpa using h)]; rfl

theorem localSearchOK_inc {cx : SCtx} (h : localSearchOK cx = true) :
    strictInc cx.area = true ∧ strictInc cx.closure = true := by
  unfold localSearchOK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.2, h.1.2⟩

theorem foldlM_sim {ε α β γ : Type} (f : α → γ → Except ε α) (g : β → γ → Except ε β)
    (e : α → β) (hstep : ∀ a x, g (e a) x = (f a x).map e) :
    ∀ (l : List γ) (a : α), l.foldlM g (e a) = (l.foldlM f a).map e
  | [], _ => rfl
  | x :: l, a => by
    rw [List.foldlM_cons, List.foldlM_cons, hstep]
    cases f a x with
    | error _ => rfl
    | ok a' => exact foldlM_sim f g e hstep l a'

/-- One step of the compiled loop from cleared position tables. -/
theorem fastStep_eq (limits : Limits) (ex : Expanded) (f : GraphFacts) (up : UPrep)
    (cand : Array Bool) (b0 : UBounds) (vis0 : Array Nat × Array Nat) (rootCount : Array Nat)
    (slack : Nat) (theta : _root_.Int) (baseEv : DictEval) (widthCs : Array (Option Nat))
    (allTrue : Array Bool) (unc : Array Nat) (opaq : Array Bool)
    (hss : limits.uniformSubsetSearch = false) (hcp : childrenPrecede ex.dag.nodes = true)
    (a : Array CompResult × Nat × Nat) (members : Array Nat) :
    fastStep limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc
        (parentsOf ex.dag)
        (a, Array.replicate up.prep.dag.size 0, Array.replicate ex.dag.size 0) members =
      (specStep limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc opaq
        a members).map
        (fun a => (a, Array.replicate up.prep.dag.size 0, Array.replicate ex.dag.size 0)) := by
  obtain ⟨results, states, costEvals⟩ := a
  unfold fastStep specStep
  simp only [hss, Bool.false_eq_true, if_false]
  rw [mkSCtxL_eq ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc members hcp]
  simp only
  have hCs := upClosure_sorted ex.dag ((markTable ex.dag.size members)[·]!)
  have hCmem := mem_upClosure hcp ((markTable ex.dag.size members)[·]!)
  have hCinc := strictInc_of_sorted hCs
  have hCin : ∀ i, i < (upClosure ex.dag ((markTable ex.dag.size members)[·]!)).size →
      (upClosure ex.dag ((markTable ex.dag.size members)[·]!))[i]! < ex.dag.size :=
    fun i hi => ((hCmem _).mp (mem_of_getElem! hi)).lt
  have hzC : clearPositions (setPositions (Array.replicate ex.dag.size 0)
      (upClosure ex.dag ((markTable ex.dag.size members)[·]!)))
      (upClosure ex.dag ((markTable ex.dag.size members)[·]!)) =
      Array.replicate ex.dag.size 0 := clear_set_zero _ _ hCinc hCin
  generalize hcx : mkSCtx ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc
    members = cx
  have hcl : cx.closure = upClosure ex.dag ((markTable ex.dag.size members)[·]!) := by
    rw [← hcx]; unfold mkSCtx; rfl
  have hup : cx.up = up := by rw [← hcx]; unfold mkSCtx; rfl
  rw [hcl, hzC]
  by_cases hok : localSearchOK cx = true
  · rw [if_pos hok]
    obtain ⟨_, _, _, _, _, _, _, _, harea, _⟩ := localSearchOK_spec hok
    have hainc := (localSearchOK_inc hok).1
    have hain : ∀ i, i < cx.area.size → cx.area[i]! < up.prep.dag.size := by
      intro i hi; rw [← hup]; exact harea i hi
    have hzA : clearPositions (setPositions (Array.replicate up.prep.dag.size 0) cx.area)
        cx.area = Array.replicate up.prep.dag.size 0 := clear_set_zero _ _ hainc hain
    have hr : Ready cx (setPositions (Array.replicate up.prep.dag.size 0) cx.area)
        (setPositions (Array.replicate ex.dag.size 0)
          (upClosure ex.dag ((markTable ex.dag.size members)[·]!))) :=
      ⟨hok, setPositions_posFn _ _ hainc hain,
        by rw [hcl]; exact setPositions_posFn _ _ hCinc hCin⟩
    rw [searchComponentL_eq hr, hzA]
    cases searchComponent cx limits states costEvals with
    | error _ => rfl
    | ok v => rfl
  · rw [if_neg hok]
    cases searchComponent cx limits states costEvals with
    | error _ => rfl
    | ok v => rfl

end LocalSearch

open LocalSearch in
/-- **The compiled component loop.** `searchComponentsWithFast` (the closure
walk, the area- and closure-local search, two shared position tables) computes
`searchComponentsWith` for every input. -/
@[csimp] theorem searchComponentsWith_eq_fast :
    @searchComponentsWith = @searchComponentsWithFast := by
  funext limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc opaq comps
  unfold searchComponentsWithFast
  by_cases hg : (limits.uniformSubsetSearch || !childrenPrecede ex.dag.nodes) = true
  · rw [if_pos hg]
  · rw [if_neg hg]
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hg
    obtain ⟨hss, hcp⟩ := hg
    unfold searchComponentsWith
    rw [← Array.foldlM_toList, ← Array.foldlM_toList]
    have key := foldlM_sim
      (specStep limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc opaq)
      (fastStep limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc
        (parentsOf ex.dag))
      (fun a => (a, Array.replicate up.prep.dag.size 0, Array.replicate ex.dag.size 0))
      (fastStep_eq limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc opaq
        (by simpa using hss) hcp) comps.toList ((#[] : Array CompResult), 0, 0)
    rw [key]
    cases List.foldlM (specStep limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs
      allTrue unc opaq) ((#[] : Array CompResult), 0, 0) comps.toList <;> rfl

end Ix.Sharing.Exact

end
