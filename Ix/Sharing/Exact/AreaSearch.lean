/-
  Exact minimum sharing under a uniform reference width: the component search
  on the components' areas with the truncated evaluation.

  `SCtx.phiE` (the component cost of the search) evaluates the members and all
  their ancestors (`SCtx.closure`) under the dictionary model, at every search
  node. The truncated evaluation (`UPrep.node`: a certain-stored term is a
  `w`-byte leaf that ends every telescope spine running into it) needs only
  the area (the members and their ancestors up to the first certain-stored
  term), which is a small part of the closure. Under the dictionary model a
  telescope running into a certain-stored term `c` is never shorter than the
  cut at `c` when `c`'s inline writing and its merged continuation cost at
  least `w`, and that cut is the truncated model's natural ending; terms
  outside the area keep their base values. So, with `K` the base costs of the
  roots and certain-stored entries in the closure but outside the area,

    phiE avail stored = (truncated area evaluation) + K

  for every `avail` and `stored`, provided every certain-stored term passes the
  opacity test (`tGuard`), which the classification guarantees for every
  certain-stored term (gain at least 1) and which is checked: once per stage
  for the base values, and at every evaluation for the certain-stored terms of
  the area. A failed test falls back to the specification's evaluation. The
  work charged (`closure.size + stored.size`) is unchanged; the closure size
  comes from one upward walk per component, without sorting.

  This module holds the compiled search; `Ix.Sharing.Exact.AreaProof` to
  `Ix.Sharing.Exact.AreaProof6` prove it equal to the specification's loop
  `searchComponentsWith` for the tables of a stage
  (`AreaProof.searchComponentsArea_eq`), and `Ix.Sharing.Exact.TieredFast`
  runs it in the recompiled copies of the construction.
-/
module

public import Ix.Sharing.Exact.UniformSearchLocal
import all Ix.Sharing.Exact.Basic
import all Ix.Sharing.Exact.Dag
import all Ix.Sharing.Exact.Dictionary
import all Ix.Sharing.Exact.UniformSearch
import all Ix.Sharing.Exact.UniformSearchLocal

public section

namespace Ix.Sharing.Exact

open Ixon

/-! ## The truncated tables

Spine lengths and tails with spines ending at opaque terms, and the truncated
evaluation of every term with no member available (`TBase`), computed once per
stage. A row is `(cost, inline cost, spine sum, descendant link)`, the link
encoded as `0` (none) or `u + 1`. -/

/-- One step of `tSpineTables`: the truncated spine length and tail of `t`
from those of its spine successor. -/
def tSpineStep (dag : Dag) (family : Array Family) (opaq : Array Bool)
    (st : Array Nat × Array Nat) (t : Nat) : Array Nat × Array Nat :=
  match st with
  | (len, tl) =>
    let fam := family[t]!
    if fam != .none then
      let nxt := (dag.node t).spineNext
      if family[nxt]! == fam && !opaq[nxt]! then (len.set! t (len[nxt]! + 1), tl.set! t tl[nxt]!)
      else (len.set! t 1, tl.set! t nxt)
    else (len, tl)

/-- Truncated spine lengths and tails, children before parents. -/
def tSpineTables (dag : Dag) (family : Array Family) (opaq : Array Bool) :
    Array Nat × Array Nat :=
  foldRange (tSpineStep dag family opaq) 0 dag.size
    (Array.replicate dag.size 0, Array.replicate dag.size 0)

/-- The internal cuts of a truncated telescope: follow the encoded descendant
links (at most `fuel`), keeping the cheapest option. -/
@[specialize] def tScan (tLen : Array Nat) (w : Nat) (getS getB : Nat → Nat) (l s : Nat) :
    Nat → Nat → Nat → Nat
  | 0, _, best => best
  | fuel + 1, cur, best =>
    if cur = 0 then best
    else
      let cand := tag4Size (l - tLen[cur - 1]!) + (s - getS (cur - 1)) + w
      tScan tLen w getS getB l s fuel (getB (cur - 1)) (if cand < best then cand else best)

/-- The truncated row of `t` (`UPrep.node`) from readers of the rows below it:
`(cost, inline cost, spine sum, encoded descendant link)`. `X` marks the
available members. -/
@[inline] def tRow (p : Prep) (opaq : Array Bool) (tLen tTail : Array Nat) (w : Nat)
    (X : Nat → Bool) (getC getS getB : Nat → Nat) (t : Nat) : Nat × Nat × Nat × Nat :=
  let node := p.dag.node t
  let fam := p.family[t]!
  if fam == .none then
    let inl := node.children.foldl (fun acc c => acc + getC c) node.head.ownBytes
    (if opaq[t]! then w else if X t then min w inl else inl, inl, 0, 0)
  else
    let nxt := node.spineNext
    let same := p.family[nxt]! == fam && !opaq[nxt]!
    let s := node.sideExtra + getC node.sideChild + (if same then getS nxt else 0)
    let bl := if same then (if X nxt then nxt + 1 else getB nxt) else 0
    let l := tLen[t]!
    let inl := tScan tLen w getS getB l s l bl (tag4Size l + s + getC tTail[t]!)
    (if opaq[t]! then w else if X t then min w inl else inl, inl, s, bl)

/-- The truncated tables of a stage. -/
structure TBase where
  tLen : Array Nat
  tTail : Array Nat
  cost : Array Nat
  inl : Array Nat
  sides : Array Nat
  below : Array Nat
  deriving Inhabited

/-- One step of the base evaluation: push the row of `t`. -/
def tBaseStep (p : Prep) (opaq : Array Bool) (tLen tTail : Array Nat) (w : Nat)
    (st : Array Nat × Array Nat × Array Nat × Array Nat) (t : Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat :=
  match st with
  | (C, I, S, B) =>
    match tRow p opaq tLen tTail w (fun _ => false) (C[·]!) (S[·]!) (B[·]!) t with
    | (c, i, s, b) => (C.push c, I.push i, S.push s, B.push b)

/-- The truncated tables: spine tables and every term's row with nothing
available. -/
def TBase.ofPrep (p : Prep) (w : Nat) (opaq : Array Bool) : TBase :=
  let n := p.dag.size
  match tSpineTables p.dag p.family opaq with
  | (tLen, tTail) =>
    match foldRange (tBaseStep p opaq tLen tTail w) 0 n
        (Array.mkEmpty n, Array.mkEmpty n, Array.mkEmpty n, Array.mkEmpty n) with
    | (C, I, S, B) => { tLen := tLen, tTail := tTail, cost := C, inl := I, sides := S, below := B }

/-- The opacity test of an opaque term on its row: its inline writing and,
for a telescope, its truncated continuation cost at least `w`. -/
@[inline] def tGuard (p : Prep) (tTail : Array Nat) (w : Nat) (getC getI getS : Nat → Nat)
    (c : Nat) : Bool :=
  decide (w ≤ getI c) && (p.family[c]! == .none || decide (w ≤ getS c + getC tTail[c]!))

/-- The stage's tables are what the area search needs: the truncated tables
have the DAG's size, and every opaque term passes the opacity test on its base
row. -/
def tStageOK (p : Prep) (w : Nat) (opaq : Array Bool) (tb : TBase) : Bool :=
  let n := p.dag.size
  tb.tLen.size == n && tb.tTail.size == n && tb.cost.size == n && tb.inl.size == n &&
    tb.sides.size == n && tb.below.size == n && opaq.size == n &&
    (List.range n).all fun c =>
      !opaq[c]! || tGuard p tb.tTail w (tb.cost[·]!) (tb.inl[·]!) (tb.sides[·]!) c

/-! ## The area evaluation -/

/-- The value of `c` in an area table `L` (by area position), or in the base
table outside the area. -/
@[inline] def rdA (pos : Array Nat) (L base : Array Nat) (c : Nat) : Nat :=
  let q := pos[c]!
  if q != 0 && q - 1 < L.size then L[q - 1]! else base[c]!

/-- Whether `c` is an available member, by its area position. -/
@[inline] def avA (pos : Array Nat) (fl : Array Bool) (c : Nat) : Bool :=
  let q := pos[c]!
  q != 0 && fl[q - 1]!

/-- The truncated rows of the area terms (ascending), by area position:
costs, inline costs, spine sums and links. -/
def areaFold (p : Prep) (opaq : Array Bool) (tb : TBase) (w : Nat) (area pos : Array Nat)
    (fl : Array Bool) : Array Nat × Array Nat × Array Nat × Array Nat :=
  let k := area.size
  foldRange (fun (st : Array Nat × Array Nat × Array Nat × Array Nat) i =>
    match st with
    | (C, I, S, B) =>
      match tRow p opaq tb.tLen tb.tTail w (avA pos fl) (rdA pos C tb.cost) (rdA pos S tb.sides)
          (rdA pos B tb.below) area[i]! with
      | (c, inl, s, b) => (C.push c, I.push inl, S.push s, B.push b))
    0 k (Array.mkEmpty k, Array.mkEmpty k, Array.mkEmpty k, Array.mkEmpty k)

/-- What the area search keeps per component besides its context: the
closure's size, the constant `K` (base costs of the roots and base entry costs
of the opaque terms in the closure but outside the area), the roots in the
area (with repetitions) and the opaque terms of the area. -/
structure AAux where
  csize : Nat
  K : Nat
  rootsA : Array Nat
  storedA : Array Nat

/-- The component cost of `SCtx.phiE` from the area evaluation, when every
opaque term of the area passes the opacity test; otherwise the
specification's evaluation on the context `fb ()` (with its closure
positions). -/
def phiA (cx : SCtx) (posA : Array Nat) (tb : TBase) (aux : AAux)
    (fb : Unit → SCtx × Array Nat) (avail : Nat → Bool) (stored : Array Nat) : Nat × Nat :=
  let w := cx.up.w
  match areaFold cx.up.prep cx.up.opaq tb w cx.area posA (memberFlags cx posA avail) with
  | (C, I, S, _) =>
    if aux.storedA.all (tGuard cx.up.prep tb.tTail w (rdA posA C tb.cost) (rdA posA I tb.inl)
        (rdA posA S tb.sides)) then
      let roots := aux.rootsA.foldl (fun acc r => acc + rdA posA C tb.cost r) 0
      let base := aux.storedA.foldl (fun acc c => acc + rdA posA I tb.inl c) 0
      let entries := stored.foldl (fun acc x => acc + rdA posA I tb.inl x) 0
      (aux.K + roots + base + entries, aux.csize + stored.size)
    else
      match fb () with
      | (cs, posC) => phiEL2 cs posA posC avail stored

/-- `SCtx.sepCheck` over the area: the reach labels of the area terms, every
other term unlabeled-reaching. -/
def sepCheckA (cx : SCtx) (posA : Array Nat) (g inRed outRed : Array Nat) : Bool :=
  let n := cx.up.prep.dag.size
  let bR := reboundL cx posA outRed
  let opqR := fun t => opqArrR cx posA bR inRed t
  let lab := sepLab n cx.members g inRed outRed
  let rl := reachLabelsL cx.up.prep.dag cx.area posA opqR lab
  g.all (fun t => (decide (t < n) && cx.members.contains t) && lab t == some 1) &&
    cx.members.all fun v => (decide (v < n) && outRed.contains v) || opqR v ||
      readAtF (posOf posA) rl id (fun _ => none) v != some none

/-! ## The search on the area -/

mutual
/-- `SCtx.solveP` on the area. -/
def solvePA (cx : SCtx) (posA : Array Nat) (tb : TBase) (aux : AAux)
    (fb : Unit → SCtx × Array Nat) (limits : Limits) :
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
    | some tb' => pure (tb', { st with memoHits := st.memoHits + 1 })
    | none =>
      unless sepCheckA cx posA g inRed outRed do
        throw (.internal "search group is not separated")
      let (tb', st) ← solveBodyA cx posA tb aux fb limits fuel g inRed outRed st
      pure (tb', { st with memo := st.memo.insert (g, entries) tb' })

/-- `SCtx.solveBody` on the area. -/
def solveBodyA (cx : SCtx) (posA : Array Nat) (tb : TBase) (aux : AAux)
    (fb : Unit → SCtx × Array Nat) (limits : Limits) :
    Nat → Array Nat → Array Nat → Array Nat → SState → Except SharingError (CTable × SState)
  | 0, _, _, _, _ => throw (.internal "component search fuel exhausted")
  | fuel + 1, g, inRed, outRed, st => do
    let inSet : Std.HashSet Nat := inRed.foldl (·.insert ·) {}
    let (phi0, work) := phiA cx posA tb aux fb (fun t => inSet.contains t) inRed
    let st ← chargeP limits (work + cx.area.size) st
    let (tb', st) ← nodePA cx posA tb aux fb limits fuel phi0 inRed outRed outRed.size #[] g #[] st
    pure (tb'.trim cx.slack, st)

/-- `SCtx.nodeP` on the area. -/
def nodePA (cx : SCtx) (posA : Array Nat) (tb : TBase) (aux : AAux)
    (fb : Unit → SCtx × Array Nat) (limits : Limits) :
    Nat → Nat → Array Nat → Array Nat → Nat → Array Nat → Array Nat → CTable → SState →
      Except SharingError (CTable × SState)
  | 0, _, _, _, _, _, _, _, _ => throw (.internal "component search fuel exhausted")
  | fuel + 1, phi0, inCtx, outAll, nOutCtx, localIn, und, ct, st => do
    let (localIn, open_, b) := reclassifyL cx posA outAll localIn und
    let und := open_.map (·.1)
    let inAll := inCtx ++ localIn
    let inSet : Std.HashSet Nat := inAll.foldl (·.insert ·) {}
    let undSet : Std.HashSet Nat := und.foldl (·.insert ·) {}
    let (phi, work) := phiA cx posA tb aux fb (fun t => inSet.contains t || undSet.contains t) inAll
    let st ← chargeP limits (work + 2 * cx.area.size) st
    let delta : _root_.Int := (phi : _root_.Int) - (phi0 : _root_.Int)
    if und.isEmpty then return (ct.add (delta, localIn), st)
    if ct.prunes delta cx.slack then return (ct, st)
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
      let (phiNone, work) := phiA cx posA tb aux fb (fun t => inSet.contains t) inAll
      let st ← chargeP limits work st
      let base : _root_.Int := (phiNone : _root_.Int) - (phi0 : _root_.Int)
      let (comb, st) ← splitPA cx posA tb aux fb limits fuel inAll outAll groups.toList
        #[some (base, localIn)] st
      return (comb.foldl (fun acc o => match o with
        | some e => acc.add e
        | none => acc) ct, st)
    let some (t, gt) := pickBranch open_ | return (ct, st)
    let und' := und.erase t
    if gt > 0 then
      let (ct, st) ← nodePA cx posA tb aux fb limits fuel phi0 inCtx outAll nOutCtx
        (mergeSorted localIn #[t]) und' ct st
      nodePA cx posA tb aux fb limits fuel phi0 inCtx (outAll.push t) nOutCtx localIn und' ct st
    else
      let (ct, st) ← nodePA cx posA tb aux fb limits fuel phi0 inCtx (outAll.push t) nOutCtx
        localIn und' ct st
      nodePA cx posA tb aux fb limits fuel phi0 inCtx outAll nOutCtx (mergeSorted localIn #[t])
        und' ct st

/-- `SCtx.splitP` on the area. -/
def splitPA (cx : SCtx) (posA : Array Nat) (tb : TBase) (aux : AAux)
    (fb : Unit → SCtx × Array Nat) (limits : Limits) :
    Nat → Array Nat → Array Nat → List (Array Nat) → CTable → SState →
      Except SharingError (CTable × SState)
  | 0, _, _, _, _, _ => throw (.internal "component search fuel exhausted")
  | _ + 1, _, _, [], comb, st => pure (comb, st)
  | fuel + 1, inAll, outAll, grp :: grps, comb, st => do
    let (sub, st) ← solvePA cx posA tb aux fb limits fuel grp inAll outAll st
    splitPA cx posA tb aux fb limits fuel inAll outAll grps (comb.conv sub) st
end

/-- `searchComponent` on the area. -/
def searchComponentA (cx : SCtx) (posA : Array Nat) (tb : TBase) (aux : AAux)
    (fb : Unit → SCtx × Array Nat) (limits : Limits) (states costEvals : Nat) :
    Except SharingError (CompResult × Nat × Nat) := do
  unless areaParentsOK cx.up.prep.dag.size cx do
    throw (.internal "component parents are not duplicate-free terms")
  let st0 : SState := { states, costEvals }
  let (ct, st) ← solvePA cx posA tb aux fb limits (8 * cx.members.size + 8) cx.members #[] #[] st0
  let some bd := ct.best | throw (.internal "component search found no choice")
  let some bs := bestSetOf ct bd | throw (.internal "component search found no choice")
  pure ({ members := cx.members, bestDelta := bd, bestSet := bs, bySize := ct },
    st.states, st.costEvals)

/-! ## The component loop -/

/-- The area's checked properties: its terms are strictly increasing terms of
the DAG, it holds the members, and the parents of each of its non-opaque terms
are in it (by the parent lists `P` and the area positions `posA`). -/
def areaOK (n : Nat) (opaq : Array Bool) (P : Array (Array Nat)) (members area posA : Array Nat) :
    Bool :=
  strictInc area && area.all (· < n) && members.all (fun m => posA[m]! != 0) &&
    area.all fun y => opaq[y]! || P[y]!.all (fun q => posA[q]! != 0)

/-- The light context of a component: `mkSCtx` without the closure (and the
roots and opaque terms of the closure), which the area search does not read. -/
def mkACtx (ex : Expanded) (f : GraphFacts) (up : UPrep) (cand : Array Bool) (b0 : UBounds)
    (vis0 : Array Nat × Array Nat) (rootCount : Array Nat) (slack : Nat) (theta : _root_.Int)
    (baseEv : DictEval) (widthCs : Array (Option Nat)) (allTrue : Array Bool) (unc : Array Nat)
    (members area : Array Nat) : SCtx :=
  let areaIdx : Std.HashMap Nat Nat :=
    (Array.range area.size).foldl (fun acc j => acc.insert area[j]! j) {}
  let memberIdx : Std.HashMap Nat Nat :=
    (Array.range members.size).foldl (fun acc j => acc.insert members[j]! j) {}
  let inEdges := area.map fun y => f.parents[y]!.map fun q => edgeCount ex.dag q y
  let rootOcc := area.map (rootCount[·]!)
  { up := up, facts := f, cand := cand, bounds0 := b0, vis0 := vis0, members := members,
    memberIdx := memberIdx, area := area, areaIdx := areaIdx, inEdges := inEdges,
    rootOcc := rootOcc, slack := slack, theta := theta, baseEv := baseEv, widthCs := widthCs,
    allTrue := allTrue, closure := #[], rootsC := #[], storedInC := #[], allUnc := unc }

/-- The constant part of `phiA`: over the terms `found` of the closure walk
(marked in `vis`), the base entry costs of the opaque ones outside the area,
and over the roots in the closure but outside the area, their base costs. -/
def areaK (tb : TBase) (opaq : Array Bool) (roots found vis posA : Array Nat) : Nat :=
  let k := found.foldl (fun k t =>
    if posA[t]! != 0 then k else if opaq[t]! then k + tb.inl[t]! else k) 0
  roots.foldl (fun k r => if vis[r]! != 0 && posA[r]! == 0 then k + tb.cost[r]! else k) k

/-- One component of the area loop: the area and its positions, the closure
walk (for the closure's size and `K`), the light context and the area search.
When a check fails it runs the component as `fastStep` does. The two position
tables are returned cleared. -/
def fastStepA (limits : Limits) (ex : Expanded) (f : GraphFacts) (up : UPrep)
    (cand : Array Bool) (b0 : UBounds) (vis0 : Array Nat × Array Nat) (rootCount : Array Nat)
    (slack : Nat) (theta : _root_.Int) (baseEv : DictEval) (widthCs : Array (Option Nat))
    (allTrue : Array Bool) (unc : Array Nat) (P : Array (Array Nat)) (tb : TBase)
    (acc : (Array CompResult × Nat × Nat) × Array Nat × Array Nat) (members : Array Nat) :
    Except SharingError ((Array CompResult × Nat × Nat) × Array Nat × Array Nat) :=
  match acc with
  | ((results, states, costEvals), posA, posC) =>
    let n := ex.dag.size
    if members.all (fun m => decide (m < n) && !up.opaq[m]!) then
      let area := componentArea up f members
      let posA := setPositions posA area
      if areaOK n up.opaq P members area posA then
        match upWalk P members posC with
        | (vis, found, stack) =>
          if stack.isEmpty && area.all (fun y => vis[y]! != 0) then
            let aux : AAux := AAux.mk found.size (areaK tb up.opaq ex.roots found vis posA)
              (ex.roots.filter (posA[·]! != 0)) (area.filter (up.opaq[·]!))
            let posC := clearPositions vis found
            let cx := mkACtx ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc
              members area
            if localSearchOK cx then
              let fb := fun (_ : Unit) =>
                let cs := mkSCtx ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue
                  unc members
                (cs, setPositions (Array.replicate n 0) cs.closure)
              match searchComponentA cx posA tb aux fb limits states costEvals with
              | .error e => .error e
              | .ok (r, states, costEvals) =>
                .ok ((results.push r, states, costEvals), clearPositions posA area, posC)
            else
              fastStep limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc
                P ((results, states, costEvals), clearPositions posA area, posC) members
          else
            fastStep limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc P
              ((results, states, costEvals), clearPositions posA area, clearPositions vis found)
              members
      else
        fastStep limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc P
          ((results, states, costEvals), clearPositions posA area, posC) members
    else
      fastStep limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc P
        ((results, states, costEvals), posA, posC) members

/-- `searchComponentsWith` with the area search: the truncated tables computed
once, every component searched on its area. It runs `searchComponentsWithFast`
when the subset search is requested, the DAG's children do not precede their
parents, or the stage's tables fail `tStageOK`. -/
def searchComponentsArea (limits : Limits) (ex : Expanded) (f : GraphFacts) (up : UPrep)
    (cand : Array Bool) (b0 : UBounds) (vis0 : Array Nat × Array Nat) (rootCount : Array Nat)
    (slack : Nat) (theta : _root_.Int) (baseEv : DictEval) (widthCs : Array (Option Nat))
    (allTrue : Array Bool) (unc : Array Nat) (opaq : Array Bool) (comps : Array (Array Nat)) :
    Except SharingError (Array CompResult × Nat × Nat) :=
  if limits.uniformSubsetSearch || !childrenPrecede ex.dag.nodes then
    searchComponentsWithFast limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs
      allTrue unc opaq comps
  else
    let tb := TBase.ofPrep up.prep up.w up.opaq
    if !tStageOK up.prep up.w up.opaq tb then
      searchComponentsWithFast limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs
        allTrue unc opaq comps
    else
      (comps.foldlM (init := (((#[] : Array CompResult), 0, 0),
          Array.replicate up.prep.dag.size 0, Array.replicate ex.dag.size 0))
        (fastStepA limits ex f up cand b0 vis0 rootCount slack theta baseEv widthCs allTrue unc
          (parentsOf ex.dag) tb)).map (·.1)

end Ix.Sharing.Exact

end
