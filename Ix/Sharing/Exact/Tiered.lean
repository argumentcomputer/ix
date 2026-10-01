/-
  Tiered canonical sharing: uniform-width selection, slot allocation, and
  re-materialization under a Share layout `widthAt : index → width`.

  Layouts (`ShareLayout.widthAt`, monotone, at least 1):
  * `tag4`: a pricing layout only: Shares priced by `shareWidth` (the TagN
    width, `Ixon.tagNByteWidth 4`) with the 2-byte tier ending at index 256.
    It goes away together with the `Ixon.ShareCodec` shim in `Basic.lean`.
  * `tagN` (TagN): the wire Share code (`putTagN 4 0xB idx`), whose widths
    climb in rungs of 1, 2, 3, 4, 5 and 9 bytes (`tagNWidth`, which also
    documents the bit layout); `Ixon.ShareCodec.current` is `.tagN`.
  The output is written with the current wire codec; `modelBytes` is the
  layout price, and the two agree whenever the layout is the wire layout
  (`ShareLayout.wire`), which is checked.

  ## Width selection
  Phase 1 runs at each uniform width `w ∈ {1, 2, 3}`, each result is carried
  through phases 2 and 3, and the construction returns the candidate with
  the fewest real layout bytes (the phase-3 length priced by the layout);
  ties go to the lower `w` (then `setPrec` on the stored set). Each
  candidate is exact per phase as described below; the final choice is the
  real-byte minimum over the three candidates, not a global optimum over
  all tables and orders. (Choosing `w` from the candidate count alone,
  `ShareLayout.uniformWidth`, overestimates the widths: the optimum stores
  far fewer terms than there are candidates.) `fixedWidth := some w` runs
  the single candidate at `w`, for experiments and tests.

  Proved (`Ix/Compile/Verify/Tiered*.lean`, no `sorry`): the width selection
  (`canonicalTieredCore_select`), phase 1 (`optimizeUniform_least`), the
  first tier, backwardness and the 2-byte-tier optimality of phase 2
  (`firstTier_spec`, `allocate_spec`, `allocate_optimal`), the per-part
  minimality, expansion and length bound of phase 3
  (`materializeTable_min`, `rematerialize_spec`, `phase3_le_phase1`), and the
  determinism, round trip and format domain of the output
  (`canonicalTiered_det`, `canonicalTiered_reexpand`, `canonicalTiered_format`).
  The composition is not claimed to be a global byte minimum.

  ## Phase 1: selection (exact for the uniform model)
  `S` and its bodies are `optimizeSharingUniform w`: a minimum of the
  uniform-`w` model length (exact, with the pinned tie order).

  ## Phase 2: slot allocation
  From the phase-1 output: `ref(t)` = the number of `Share(t)` in the phase-1
  entries and roots; `t` depends on `u` when `t`'s phase-1 body contains
  `Share(u)`.
  * First tier (exact): `F` is a maximum-`ref` set of at most 8 stored terms
    closed under dependencies, so `F` can occupy indices `0..|F|-1`. Ties:
    order the stored terms by (`ref` descending, ID ascending); among
    maximum sets the one that, at the first term in this order where two
    sets differ, contains it. Found by branch and bound with the bound
    "current weight + the largest remaining weights that still fit".
  * Remaining entries (pinned, not optimized): `F` in the pinned priority
    order (stored descendants first, larger in-degree, smaller ID), then the
    rest in the Kahn priority order (`kahnOrder`): repeatedly the available
    entry (every entry its phase-1 body references already placed) with the
    largest `ref`, ties by the smaller ID.
  * Guard: if this order's reference cost `Σ ref(t)·widthAt(index t)` is
    larger than the phase-1 order's, the phase-1 order is kept.
  Optimality (`allocate_optimal`): with the `ref` counts fixed, the
  allocation minimizes `Σ ref·widthAt` over all orders respecting the
  dependencies whenever all entries beyond the first tier share one width
  (`|S| ≤ tier2End`), since then that sum is `2·Σref − Σ_{first 8} ref`.
  Beyond that only the first tier is optimized.

  ## Phase 3: re-materialization (exact per part)
  Every entry is re-encoded with `C_M` under the entries before it, priced
  by their real widths `widthAt(index)`, and the roots under all entries
  (so an occurrence may now inline instead of referencing). Each part is a
  minimum for its dictionary, with the byte-least tie-break. The phase-1
  bodies are valid in the allocated order (dependencies come first), so
  the result is no longer than the phase-1 bodies in this order, which by
  the guard is no longer than the phase-1 output priced by the layout
  (`phase3_le_phase1`). This is also checked, and the output is serialized,
  measured and re-expanded.

  The construction is a function of the expanded AST and the layout, so
  normalizing its output reproduces it.
-/
module

public import Ix.Sharing.Exact.Uniform

public section

namespace Ix.Sharing.Exact

open Ixon

/-! ## TagN Share code

A Share is the `f = 4` instance of the Ixon TagN integer code
(`Ixon.putTagN 4`, see `Ix/Ixon.lean`): one header byte
`[flag:4][L][M][c1][c0]` (flag `0xB`) followed by 0, 1, 2, 3, 4 or 8
little-endian bytes. The low nibble selects a rung:

* `L = 0`: no following byte; the 3 bits `M c1 c0` are the index, `0..7`.
* `L = 1, M = 0`: 1 following byte; `value = c1 c0 · 2^8 + byte` (10 bits)
  and `index = 8 + value`, so indices `8 .. 8 + 2^10 - 1`.
* `L = 1, M = 1, c = c1 c0 ∈ {0, 1, 2, 3}`: `2`, `3`, `4` or `8` following
  bytes holding `value`, and `index = (end of the previous rung) + value`.
  Every code is valid.

Every rung starts where the previous one ends, so each index has exactly
one encoding and every valid encoding is the encoding of its index (the code
is bijective). Rung ends: `8`, `8 + 2^10`, `+ 2^16`, `+ 2^24`, `+ 2^32`,
`+ 2^64`; byte widths: 1, 2, 3, 4, 5, 9. The rung ends and `tagNWidth` below are by definition
`Ixon.tagNEnd* 4` and `Ixon.tagNByteWidth 4`, the single width-by-index
function for this code. -/

/-- End (exclusive) of the 1-byte rung. -/
def tagNRung1End : Nat := Ixon.tagNEnd1 4
/-- End of the 2-byte rung (2 + 8 value bits). -/
def tagNRung2End : Nat := Ixon.tagNEnd2 4
/-- End of the 3-byte rung (2 following bytes). -/
def tagNRung3End : Nat := Ixon.tagNEnd3 4
/-- End of the 4-byte rung (3 following bytes). -/
def tagNRung4End : Nat := Ixon.tagNEnd4 4
/-- End of the 5-byte rung (4 following bytes). -/
def tagNRung5End : Nat := Ixon.tagNEnd5 4
/-- End of the 9-byte rung (8 following bytes); larger indices have no
encoding. -/
def tagNRung6End : Nat := Ixon.tagNEnd6 4

/-- Byte width of the TagN Share at index `i` (`i < tagNRung6End`;
larger indices are not encodable and are priced at the top rung). -/
def tagNWidth (i : Nat) : Nat := Ixon.tagNByteWidth 4 i

/-! ## Layouts -/

/-- A Share width layout. -/
inductive ShareLayout where
  /-- Shares priced by `shareWidth` (the TagN width) with the 2-byte tier ending
  at 256; a pricing layout only. -/
  | tag4
  /-- The TagN Share code (`tagNWidth`). -/
  | tagN
  deriving BEq, Repr, Inhabited

/-- The layout of a wire Share codec. -/
def ShareLayout.ofCodec : Ixon.ShareCodec → ShareLayout
  | .tag4 => .tag4
  | .tagN => .tagN

/-- The layout of the current wire codec `Ixon.ShareCodec.current`. -/
def ShareLayout.wire : ShareLayout := .ofCodec Ixon.ShareCodec.current

/-- Width of the Share at table index `i`. -/
def ShareLayout.widthAt : ShareLayout → Nat → Nat
  | .tag4, i => shareWidth i
  | .tagN, i => tagNWidth i

/-- First index whose width exceeds 2. -/
def ShareLayout.tier2End : ShareLayout → Nat
  | .tag4 => 256
  | .tagN => tagNRung2End

/-- Nominal uniform width for `k` candidates (`k` up to 8 fit the 1-byte
rung, up to `tier2End` the 2-byte rung). The canonical path tries every
width instead (see the module doc); this is reported in the statistics. -/
def ShareLayout.uniformWidth (l : ShareLayout) (k : Nat) : Nat :=
  if k ≤ 8 then 1 else if k ≤ l.tier2End then 2 else 3

/-- Variable length of an encoding with Shares priced by the layout. -/
def layoutBytes (l : ShareLayout) (sharing roots : Array Ixon.Expr) : Nat :=
  let size := fun e => (sizeInfoWith l.widthAt e).full
  tag0Size sharing.size + sharing.foldl (fun acc e => acc + size e) 0 +
    roots.foldl (fun acc e => acc + size e) 0

/-! ## Share references of an encoding -/

/-- All `Share` indices in an expression, with multiplicity. -/
def shareIndices : Ixon.Expr → Array Nat → Array Nat
  | .share i, acc => acc.push i.toNat
  | .prj _ _ v, acc => shareIndices v acc
  | .app f a, acc => shareIndices a (shareIndices f acc)
  | .lam _ t b, acc => shareIndices b (shareIndices t acc)
  | .all _ _ t b, acc => shareIndices b (shareIndices t acc)
  | .letE _ t v b, acc => shareIndices b (shareIndices v (shareIndices t acc))
  | _, acc => acc

/-! ## First-tier allocation -/

/-- Fail with an internal error unless `b` holds. -/
def checkInternal (b : Bool) (msg : String) : Except SharingError Unit :=
  if b then pure () else throw (.internal msg)

/-- Add the closure of `d` to a partial closure (`none` once above `cap`). -/
def tierClosureUnion (cap : Nat) (cl : Std.HashMap Nat (Option (List Nat)))
    (acc : Option (List Nat)) (d : Nat) : Option (List Nat) :=
  match acc, cl.getD d none with
  | some a, some c =>
    let u := c.foldl (fun a x => a.insert x) a
    if u.length ≤ cap then some u else none
  | _, _ => none

/-- The first-tier closures, in an order `topo` where every term's
dependencies come before it: the closure of `t` is `t` with the closures of
its dependencies, or `none` when it has more than `cap` terms. A dependency
that is not yet closed, or a repeated term, is an internal error. -/
def tierClosures (topo : Array Nat) (deps : Nat → List Nat) (cap : Nat) :
    Except SharingError (Std.HashMap Nat (Option (List Nat))) :=
  topo.foldlM (init := {}) fun cl t => do
    checkInternal (!cl.contains t) "a stored term repeats in the phase-1 table"
    checkInternal ((deps t).all cl.contains) "a phase-1 body references a later entry"
    let acc := (deps t).foldl (tierClosureUnion cap cl) (some [t])
    return cl.insert t (acc.bind fun a => if a.length ≤ cap then some a else none)

/-- Bound of the first-tier search: `acc` plus the largest `room` weights
among `rest` outside `inF` (`rest` is in decreasing weight). -/
def tierBound (weight : Nat → Nat) (inF : List Nat) : List Nat → Nat → Nat → Nat
  | [], _, acc => acc
  | t :: ts, room, acc =>
    if room = 0 then acc
    else if inF.contains t then tierBound weight inF ts room acc
    else tierBound weight inF ts (room - 1) (acc + weight t)

/-- First-tier search state: the best set with its weight, and the states
visited. -/
structure TierState where
  best : Option (Nat × List Nat) := none
  states : Nat := 0
  deriving Inhabited

/-- Whether a subtree with bound `bound` is pruned: some set of weight at
least `bound` is already found. -/
def tierPruned (best : Option (Nat × List Nat)) (bound : Nat) : Bool :=
  match best with
  | some (b, _) => bound ≤ b
  | none => false

/-- Keep the best set: `inF` (of weight `cur`) replaces it only if heavier. -/
def tierUpd (best : Option (Nat × List Nat)) (cur : Nat) (inF : List Nat) :
    Option (Nat × List Nat) :=
  match best with
  | some (b, _) => if cur > b then some (cur, inF) else best
  | none => some (cur, inF)

/-- Depth-first branch and bound over `items` (in the search order), deciding
`items[pos]`: "include" (its closure joins `inF`, if no excluded term is in
it and it fits) before "exclude". `cur` is the weight of `inF`. The first
maximum found is the tie-break winner, so a subtree is pruned when its
bound does not exceed the best weight. -/
def tierDfs (items : Array Nat) (weight : Nat → Nat) (closure : Nat → Option (List Nat))
    (cap : Nat) (limits : Limits) :
    Nat → Nat → Nat → List Nat → Std.HashSet Nat → TierState →
      Except SharingError TierState
  | 0, _, _, _, _, _ => throw (.internal "first-tier search fuel exhausted")
  | fuel + 1, pos, cur, inF, excluded, st =>
    if st.states + 1 > limits.maxStates then
      throw (.resourceExhausted .states limits.maxStates)
    else
      let st := { st with states := st.states + 1 }
      if tierPruned st.best
          (tierBound weight inF (items.toList.drop pos) (cap - inF.length) cur) then
        pure st
      else if pos ≥ items.size then
        pure { st with best := tierUpd st.best cur inF }
      else
        let t := items[pos]!
        if inF.contains t then
          tierDfs items weight closure cap limits fuel (pos + 1) cur inF excluded st
        else do
          let st ← match closure t with
            | some c =>
              let new := c.filter (!inF.contains ·)
              if !c.any excluded.contains && inF.length + new.length ≤ cap then
                tierDfs items weight closure cap limits fuel (pos + 1)
                  (new.foldl (fun acc u => acc + weight u) cur) (inF ++ new) excluded st
              else pure st
            | none => pure st
          tierDfs items weight closure cap limits fuel (pos + 1) cur inF (excluded.insert t) st

/-- The first-tier search order: weight descending, then ID ascending. -/
def tierOrder (weight : Nat → Nat) (a b : Nat) : Bool :=
  weight a > weight b || (weight a == weight b && a ≤ b)

/-- Maximum-weight set of at most `cap` stored terms closed under `deps`
(tie order as in the module doc). The stored terms are given in an order
`topo` with every term's dependencies before it. Returns the set
(ascending) and the states visited. -/
def firstTier (topo : Array Nat) (weight : Nat → Nat) (deps : Nat → List Nat) (cap : Nat)
    (limits : Limits) : Except SharingError (Array Nat × Nat) := do
  let items := (topo.toList.mergeSort (tierOrder weight)).toArray
  let cl ← tierClosures topo deps cap
  let st ← tierDfs items weight (fun t => cl.getD t none) cap limits (items.size + 2) 0 0 []
    {} {}
  match st.best with
  | some (_, s) => return ((s.mergeSort (· ≤ ·)).toArray, st.states)
  | none => return (#[], st.states)

/-! ## Phase 2: slot allocation -/

/-- Reference counts by phase-1 index: the `Share(i)` (`i < m`) in `exprs`. -/
def shareCounts (m : Nat) (exprs : Array Ixon.Expr) : Array Nat :=
  exprs.foldl (fun refs e => (shareIndices e #[]).foldl
    (fun refs i => if i < refs.size then refs.modify i (· + 1) else refs) refs)
    (Array.replicate m 0)

/-- The terms a phase-1 body references: `order1[i]` for every `Share(i)`. -/
def bodyRefs (order1 : Array Nat) (e : Ixon.Expr) : List Nat :=
  ((shareIndices e #[]).filterMap (order1[·]?)).toList

/-- Reference count of every stored term: its Shares in the phase-1 entries
and roots. -/
def tierWeights (order1 : Array Nat) (entries1 roots1 : Array Ixon.Expr) :
    Std.HashMap Nat Nat :=
  let refs := shareCounts order1.size (entries1 ++ roots1)
  (List.range order1.size).foldl (fun m i => m.insert order1[i]! refs[i]!) {}

/-- The stored terms each phase-1 body references. -/
def tierDeps (order1 : Array Nat) (entries1 : Array Ixon.Expr) :
    Std.HashMap Nat (List Nat) :=
  (List.range order1.size).foldl
    (fun m i => m.insert order1[i]! (bodyRefs order1 (entries1[i]?.getD default))) {}

/-- Whether every term's dependencies come before it in `order`. -/
def respectsDeps (order : Array Nat) (deps : Nat → List Nat) : Bool :=
  let pos : Std.HashMap Nat Nat := order.zipIdx.foldl (fun m (t, i) => m.insert t i) {}
  order.zipIdx.all fun (t, i) => (deps t).all fun d => (pos.get? d).any (· < i)

/-- The Kahn priority order of `rest`: repeatedly place the available term
(every dependency of it in `rest` already placed) of the largest weight,
ties by the smaller ID (`tierOrder`). Terms left over, which acyclic
dependencies never leave, follow in priority order. -/
def kahnOrder (weight : Nat → Nat) (deps : Nat → List Nat) (rest : Array Nat) : Array Nat :=
  Id.run do
  -- Ranks in priority order; the ready set is kept by rank.
  let sorted := (rest.toList.mergeSort (tierOrder weight)).toArray
  let m := sorted.size
  let rank : Std.HashMap Nat Nat := sorted.zipIdx.foldl (fun r (t, i) => r.insert t i) {}
  let mut pend : Array Nat := Array.replicate m 0
  let mut users : Array (Array Nat) := Array.replicate m #[]
  for h : i in [0:m] do
    let ds := ((deps sorted[i]).filterMap rank.get?).eraseDups
    pend := pend.set! i ds.length
    for d in ds do
      users := users.modify d (·.push i)
  let mut ready : Std.TreeSet Nat :=
    Std.TreeSet.ofList ((List.range m).filter (pend[·]! == 0))
  let mut placed : Array Bool := Array.replicate m false
  let mut out : Array Nat := #[]
  for _ in [0:m] do
    match ready.min? with
    | none => break
    | some r =>
      ready := ready.erase r
      placed := placed.set! r true
      out := out.push sorted[r]!
      for u in users[r]! do
        pend := pend.modify u (· - 1)
        if pend[u]! == 0 then ready := ready.insert u
  for h : i in [0:m] do
    if !placed[i]! then out := out.push sorted[i]
  return out

/-- Reference cost `Σ weight(t) · widthAt(index t)` of a table order. -/
def refCost (layout : ShareLayout) (weight : Nat → Nat) (order : Array Nat) : Nat :=
  order.zipIdx.foldl (fun acc (t, i) => acc + weight t * layout.widthAt i) 0

/-- The slot allocation of phase 2. -/
structure Allocation where
  /-- The first tier (ascending). -/
  tier : Array Nat
  slotStates : Nat
  /-- The final table order. -/
  order : Array Nat
  /-- The guard kept the phase-1 order. -/
  kept : Bool
  /-- Reference cost of the phase-1 order and of the final order. -/
  refCost1 : Nat
  refCostFinal : Nat
  deriving Inhabited

/-- Phase 2 on the phase-1 table `order1` with entries `entries1` and roots
`roots1`: the first tier, then the pinned order, unless the guard keeps the
phase-1 order. The final order is checked to place every body reference
before its user, and the pinned order to be a permutation of the phase-1
table. -/
def allocate (layout : ShareLayout) (limits : Limits) (dag : Dag) (deg : Array Nat)
    (order1 : Array Nat) (entries1 roots1 : Array Ixon.Expr) :
    Except SharingError Allocation := do
  let wm := tierWeights order1 entries1 roots1
  let dm := tierDeps order1 entries1
  let weight := fun t => wm.getD t 0
  let deps := fun t => dm.getD t []
  let stored := (order1.toList.mergeSort (· ≤ ·)).toArray
  let (tier, slotStates) ← firstTier order1 weight deps (min 8 order1.size) limits
  let rest := stored.filter (!tier.contains ·)
  let order2 := pinnedOrder dag deg tier ++ kahnOrder weight deps rest
  checkInternal ((order2.toList.mergeSort (· ≤ ·)).toArray == stored)
    "the allocated order is not a permutation of the phase-1 table"
  let kept : Bool := refCost layout weight order2 > refCost layout weight order1
  let order := if kept then order1 else order2
  checkInternal (respectsDeps order deps) "the allocated order places a body reference after its user"
  return { tier, slotStates, order, kept, refCost1 := refCost layout weight order1,
           refCostFinal := refCost layout weight order }

/-! ## Result -/

/-- Statistics of the tiered construction. -/
structure TieredStats where
  layout : ShareLayout
  /-- Terms with in-degree ≥ 2 and unshared length ≥ 2. -/
  candidateCount : Nat
  /-- Nominal width for the candidate count (`ShareLayout.uniformWidth`). -/
  nominalW : Nat
  /-- Phase-1 uniform width of the returned candidate (the winning width). -/
  w : Nat
  /-- Final layout length of every candidate run, as `(w, bytes)` in
  increasing `w` (one entry under `fixedWidth`). -/
  candidateLengths : Array (Nat × Nat) := #[]
  /-- Phase-1 uniform-model length. -/
  phase1ModelBytes : Nat
  /-- Phase-1 output priced by the layout (its own order). -/
  phase1LayoutBytes : Nat
  /-- First-tier search states. -/
  slotStates : Nat
  firstTier : Array Nat
  /-- The guard kept the phase-1 order. -/
  keptPhase1Order : Bool
  /-- Reference cost `Σ ref·widthAt` of the phase-1 and the final order. -/
  phase1RefCost : Nat
  finalRefCost : Nat
  /-- Final length priced by the layout. -/
  phase3LayoutBytes : Nat
  /-- `phase1LayoutBytes - phase3LayoutBytes`. -/
  savings : Nat
  deriving Repr, Inhabited

/-- Tiered result: the usual result (`modelBytes` = layout price,
`variableBytes` = length serialized with `Ixon.ShareCodec.current`), the phase-1
result, statistics. -/
structure TieredSharingResult where
  result : ExactSharingResult
  phase1 : UniformSharingResult
  stats : TieredStats
  deriving Inhabited

/-- Phase-3 output of one candidate. -/
structure Rematerialized where
  entries : Array Ixon.Expr
  roots : Array Ixon.Expr
  /-- Length priced by the layout. -/
  bytes : Nat
  work : Nat
  /-- Serialized length (`serExpr`, the TagN wire). -/
  measured : Nat
  deriving Inhabited

/-- Phase 3: re-materialize the table `order` and the roots under the real
widths, check the price against the layout length and against phase 1, and
re-expand the output. -/
def rematerialize (layout : ShareLayout) (limits : Limits) (ex : Expanded) (order : Array Nat)
    (phase1Layout : Nat) : Except SharingError Rematerialized := do
  let (entries, roots, predicted, work) ←
    materializeTable (Prep.ofDag ex.dag) order ex.roots limits layout.widthAt
  let priced := layoutBytes layout entries roots
  checkInternal (priced == predicted)
    s!"layout length {priced} differs from the evaluation {predicted}"
  checkInternal (predicted ≤ phase1Layout)
    s!"re-materialization {predicted} is longer than phase 1 {phase1Layout}"
  let (entryIds, rootIds, _) ← reexpand limits ex.dag entries roots
  checkInternal (entryIds == order) "re-materialized entries do not expand to the stored terms"
  checkInternal (rootIds == ex.roots) "re-materialized roots do not expand to the input roots"
  -- The real length: the bytes written with the current wire codec.
  let measured := tag0Size entries.size +
    (entries ++ roots).foldl (fun acc e => acc + (serExpr e).size) 0
  checkInternal (layout != ShareLayout.wire || measured == predicted)
    s!"serialized length {measured} differs from the wire-layout price {predicted}"
  checkInternal ((entries ++ roots).all fun e => (wireCounts e).isSome)
    "a re-materialized expression has a count outside the wire domain"
  return { entries, roots, bytes := predicted, work, measured }

/-- Assemble one candidate from its three phases. -/
def tieredResult (layout : ShareLayout) (ex : Expanded) (w : Nat) (u : UniformSharingResult)
    (a : Allocation) (m : Rematerialized) : TieredSharingResult :=
  let p := Prep.ofDag ex.dag
  let f := graphFacts ex.dag ex.roots
  let k := ((Array.range ex.dag.size).filter fun t => f.deg[t]! ≥ 2 && p.base[t]! ≥ 2).size
  let phase1Layout := layoutBytes layout u.result.sharing u.result.roots
  let stats : TieredStats :=
    { layout := layout, candidateCount := k, nominalW := layout.uniformWidth k, w := w,
      candidateLengths := #[(w, m.bytes)], phase1ModelBytes := u.result.modelBytes,
      phase1LayoutBytes := phase1Layout, slotStates := a.slotStates, firstTier := a.tier,
      keptPhase1Order := a.kept, phase1RefCost := a.refCost1, finalRefCost := a.refCostFinal,
      phase3LayoutBytes := m.bytes, savings := phase1Layout - m.bytes }
  let rstats : Stats :=
    { u.result.stats with materializedNodes := m.work, outputBytes := m.measured }
  let res : ExactSharingResult :=
    { u.result with
      roots := m.roots, sharing := m.entries, tableTerms := a.order,
      variableBytes := m.measured, modelBytes := m.bytes, stats := rstats }
  { result := res, phase1 := u, stats := stats }

/-- One candidate of the tiered construction: phases 1–3 with phase-1
uniform width `w`. -/
def tieredAtWidth (layout : ShareLayout) (limits : Limits) (ex : Expanded) (w : Nat) :
    Except SharingError TieredSharingResult := do
  let u ← optimizeUniformExpanded w limits ex
  let a ← allocate layout limits ex.dag (graphFacts ex.dag ex.roots).deg u.result.tableTerms
    u.result.sharing u.result.roots
  let m ← rematerialize layout limits ex a.order
    (layoutBytes layout u.result.sharing u.result.roots)
  return tieredResult layout ex w u a m

/-- Whether candidate `a` beats `b`: fewer final layout bytes, then the
lower width, then `setPrec` on the stored set. -/
def tieredBetter (a b : TieredSharingResult) : Bool :=
  a.stats.phase3LayoutBytes < b.stats.phase3LayoutBytes ||
    (a.stats.phase3LayoutBytes == b.stats.phase3LayoutBytes &&
      (a.stats.w < b.stats.w ||
        (a.stats.w == b.stats.w && setPrec a.phase1.stored b.phase1.stored)))

/-- The tiered construction on the canonical DAG `dag` and root IDs
`roots` alone: the candidate with the fewest final layout bytes over the
phase-1 widths 1, 2 and 3 (module doc), or the single candidate at
`fixedWidth`. -/
def canonicalTieredCore (layout : ShareLayout) (limits : Limits) (dag : Dag)
    (roots : Array Nat) (fixedWidth : Option Nat := none) :
    Except SharingError TieredSharingResult :=
  let ex : Expanded := { dag, roots, visits := 0, internedNodes := 0 }
  match fixedWidth with
  | some w => tieredAtWidth layout limits ex w
  | none => do
    let c1 ← tieredAtWidth layout limits ex 1
    let c2 ← tieredAtWidth layout limits ex 2
    let c3 ← tieredAtWidth layout limits ex 3
    let best := #[c2, c3].foldl (fun b c => if tieredBetter c b then c else b) c1
    let lengths := #[c1, c2, c3].map fun c => (c.stats.w, c.stats.phase3LayoutBytes)
    return { best with stats := { best.stats with candidateLengths := lengths } }

/-- Record the expansion statistics of `ex` in a result. -/
def withExpansionStats (ex : Expanded) (r : TieredSharingResult) : TieredSharingResult :=
  { r with
    result := { r.result with
      stats := { r.result.stats with exprVisits := ex.visits, internedNodes := ex.internedNodes } }
    phase1 := { r.phase1 with
      result := { r.phase1.result with
        stats := { r.phase1.result.stats with
          exprVisits := ex.visits, internedNodes := ex.internedNodes } } } }

/-- The tiered canonical construction on an expanded input: a function of
its DAG and root IDs (`canonicalTieredCore`), with the expansion statistics
recorded. -/
def canonicalTieredExpanded (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (fixedWidth : Option Nat := none) : Except SharingError TieredSharingResult := do
  let r ← canonicalTieredCore layout limits ex.dag ex.roots fixedWidth
  return withExpansionStats ex r

end Ix.Sharing.Exact

end
