/-
  Tiered canonical sharing: uniform-width selection, slot allocation, and
  re-materialization under a Share layout `widthAt : index → width`.

  Layouts (`ShareLayout.widthAt`, monotone, at least 1):
  * `tag4`: the Ixon Tag4 Share: 1 byte below index 8, 2 below 256, 3 below
    65536, … (the serialized width).
  * `tagN` (TagN): the nibble-bootstrapped Share code whose widths
    climb in rungs of 1, 2, 3, 5 and 9 bytes (`tagNWidth`, which also
    documents the bit layout). It is the wire code when
    `Ixon.ShareCodec.current` is `.tagN` (format version 3 writes Tag4).
  The output is written with the current wire codec; `modelBytes` is the
  layout price, and the two agree whenever the layout is the wire layout
  (`ShareLayout.wire`), which is checked.

  ## Phase 1: selection (exact for the uniform model)
  `K` = number of terms with compact in-degree ≥ 2 and unshared length ≥ 2.
  `w = 1` if `K ≤ 8`, `2` if `K ≤ tier2End` (256 for tag4, 1032 for tagN),
  else `3`. `S` and its bodies are `optimizeSharingUniform w`: a minimum of
  the uniform-`w` model length (exact, with the pinned tie order).

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
    rest in the same pinned order.
  * Guard: if this order's reference cost `Σ ref(t)·widthAt(index t)` is
    larger than the phase-1 order's, the phase-1 order is kept.
  Optimality claim: with the `ref` counts fixed, the allocation minimizes
  `Σ ref·widthAt` over all orders respecting the dependencies whenever all
  entries beyond the first tier share one width (`|S| ≤ tier2End`), since
  then that sum is `w₂·Σref - (w₂-1)·Σ_{F} ref`. Beyond that only the first
  tier is optimized.

  ## Phase 3: re-materialization (exact per part)
  Every entry is re-encoded with `C_M` under the entries before it, priced
  by their real widths `widthAt(index)`, and the roots under all entries
  (so an occurrence may now inline instead of referencing). Each part is a
  minimum for its dictionary, with the byte-least tie-break. The phase-1
  bodies are valid in the allocated order (dependencies come first), so
  the result is no longer than the phase-1 bodies in this order, which by
  the guard is no longer than the phase-1 output priced by the layout. This
  is checked, and the output is serialized, measured and re-expanded.

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
`[flag:4][L][M][c1][c0]` (flag `0xB`) followed by 0, 1, 2, 4 or 8
little-endian bytes. The low nibble selects a rung:

* `L = 0`: no following byte; the 3 bits `M c1 c0` are the index, `0..7`.
* `L = 1, M = 0`: 1 following byte; `value = c1 c0 · 2^8 + byte` (10 bits)
  and `index = 8 + value`, so indices `8 .. 8 + 2^10 - 1`.
* `L = 1, M = 1, c = c1 c0 ∈ {0, 1, 2}`: `2`, `4` or `8` following bytes
  holding `value`, and `index = (end of the previous rung) + value`.
* `L = 1, M = 1, c = 3`: invalid.

Every rung starts where the previous one ends, so each index has exactly
one encoding and every valid encoding is the encoding of its index (the code
is bijective). Rung ends: `8`, `8 + 2^10`, `+ 2^16`, `+ 2^32`, `+ 2^64`; byte
widths: 1, 2, 3, 5, 9. The rung ends and `tagNWidth` below are by definition
`Ixon.tagNEnd* 4` and `Ixon.tagNByteWidth 4`, the single width-by-index
function for this code. -/

/-- End (exclusive) of the 1-byte rung. -/
def tagNRung1End : Nat := Ixon.tagNEnd1 4
/-- End of the 2-byte rung (2 + 8 value bits). -/
def tagNRung2End : Nat := Ixon.tagNEnd2 4
/-- End of the 3-byte rung (2 following bytes). -/
def tagNRung3End : Nat := Ixon.tagNEnd3 4
/-- End of the 5-byte rung (4 following bytes). -/
def tagNRung4End : Nat := Ixon.tagNEnd4 4
/-- End of the 9-byte rung (8 following bytes); larger indices have no
encoding. -/
def tagNRung5End : Nat := Ixon.tagNEnd5 4

/-- Byte width of the TagN Share at index `i` (`i < tagNRung5End`;
larger indices are not encodable and are priced at the top rung). -/
def tagNWidth (i : Nat) : Nat := Ixon.tagNByteWidth 4 i

/-! ## Layouts -/

/-- A Share width layout. -/
inductive ShareLayout where
  /-- The Ixon Tag4 Share (the serialized width). -/
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

/-- Phase-1 uniform width for `k` candidates. -/
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

/-- Inputs of the first-tier search, over stored terms. -/
structure TierProblem where
  /-- Stored terms in search order: `ref` descending, ID ascending. -/
  items : Array Nat
  weight : Std.HashMap Nat Nat
  /-- Dependency closure (including the term), if it has at most `cap`
  terms. -/
  closure : Std.HashMap Nat (Array Nat)
  cap : Nat
  deriving Inhabited

/-- Search state. -/
structure TierState where
  best : Option (Nat × Array Nat) := none
  states : Nat := 0

abbrev TierM := StateT TierState (Except SharingError)

/-- Depth-first branch and bound, "include" before "exclude"; the first
maximum found is the tie-break winner, so later subtrees are pruned when
their bound does not exceed the best weight. -/
def TierProblem.dfs (pr : TierProblem) (limits : Limits) :
    Nat → Nat → Nat → Array Nat → Std.HashSet Nat → TierM Unit
  | 0, _, _, _, _ => throw (.internal "first-tier search fuel exhausted")
  | fuel + 1, pos, cur, inF, excluded => do
    let st ← get
    if st.states + 1 > limits.maxStates then
      throw (.resourceExhausted .states limits.maxStates)
    set { st with states := st.states + 1 }
    -- Bound: the largest remaining weights that still fit.
    let room := pr.cap - inF.size
    let mut bound := cur
    let mut taken := 0
    for t in pr.items.extract pos pr.items.size do
      if taken ≥ room then break
      if inF.contains t then continue
      bound := bound + pr.weight.getD t 0
      taken := taken + 1
    if let some (b, _) := (← get).best then
      if bound ≤ b then return
    if pos ≥ pr.items.size then
      match (← get).best with
      | some (b, _) => if cur > b then modify fun s => { s with best := some (cur, inF) }
      | none => modify fun s => { s with best := some (cur, inF) }
      return
    let t := pr.items[pos]!
    if inF.contains t then
      pr.dfs limits fuel (pos + 1) cur inF excluded
    else
      if let some cl := pr.closure.get? t then
        let new := cl.filter (!inF.contains ·)
        if !cl.any excluded.contains && inF.size + new.size ≤ pr.cap then
          let w := new.foldl (fun acc u => acc + pr.weight.getD u 0) 0
          pr.dfs limits fuel (pos + 1) (cur + w) (inF ++ new) excluded
      pr.dfs limits fuel (pos + 1) cur inF (excluded.insert t)

/-- Maximum-weight dependency-closed set of at most `cap` stored terms (tie
order as in the module doc). `deps t` are the terms `t` references. Returns
the set (ascending) and the states visited. -/
def firstTier (stored : Array Nat) (weight : Std.HashMap Nat Nat)
    (deps : Std.HashMap Nat (Array Nat)) (cap : Nat) (limits : Limits) :
    Except SharingError (Array Nat × Nat) := do
  let items := stored.qsort fun a b =>
    let wa := weight.getD a 0
    let wb := weight.getD b 0
    wa > wb || (wa == wb && a < b)
  -- Closures with early cutoff above `cap`.
  let mut closure : Std.HashMap Nat (Array Nat) := {}
  for t in stored do
    let mut seen : Std.HashSet Nat := {}
    let mut stack := #[t]
    let mut ok := true
    for _ in [0:stored.size * 4 + 4] do
      match stack.back? with
      | none => break
      | some u =>
        stack := stack.pop
        if seen.contains u then continue
        seen := seen.insert u
        if seen.size > cap then
          ok := false
          break
        stack := stack ++ deps.getD u #[]
    if ok then closure := closure.insert t (seen.toArray.qsort (· < ·))
  let pr : TierProblem := { items, weight, closure, cap }
  let ((), st) ← (pr.dfs limits (items.size + 2) 0 0 #[] {}).run {}
  match st.best with
  | some (_, s) => return (s.qsort (· < ·), st.states)
  | none => return (#[], st.states)

/-! ## Result -/

/-- Statistics of the tiered construction. -/
structure TieredStats where
  layout : ShareLayout
  /-- Terms with in-degree ≥ 2 and unshared length ≥ 2. -/
  candidateCount : Nat
  /-- Phase-1 uniform width. -/
  w : Nat
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

/-- The tiered canonical construction on an expanded input. -/
def canonicalTieredExpanded (layout : ShareLayout) (limits : Limits) (ex : Expanded) :
    Except SharingError TieredSharingResult := do
  let p := Prep.ofDag ex.dag
  let n := ex.dag.size
  let f := graphFacts ex.dag ex.roots
  let k := ((Array.range n).filter fun t => f.deg[t]! ≥ 2 && p.base[t]! ≥ 2).size
  let w := layout.uniformWidth k
  -- Phase 1.
  let u ← optimizeUniformExpanded w limits ex
  let order1 := u.result.tableTerms
  let entries1 := u.result.sharing
  let roots1 := u.result.roots
  let phase1Layout := layoutBytes layout entries1 roots1
  -- Phase 2: reference counts and dependencies from the phase-1 output.
  let mut refs : Array Nat := Array.replicate order1.size 0
  for e in entries1 ++ roots1 do
    for i in shareIndices e #[] do
      if i < refs.size then refs := refs.modify i (· + 1)
  let mut weight : Std.HashMap Nat Nat := {}
  let mut deps : Std.HashMap Nat (Array Nat) := {}
  for h : i in [0:order1.size] do
    let t := order1[i]
    weight := weight.insert t refs[i]!
    let ds := (shareIndices (entries1[i]?.getD default) #[]).filterMap (order1[·]?)
    deps := deps.insert t (ds.foldl (fun acc d => if acc.contains d then acc else acc.push d) #[])
  let stored := order1.qsort (· < ·)
  let (tier, slotStates) ← firstTier stored weight deps (min 8 stored.size) limits
  let rest := stored.filter (!tier.contains ·)
  let order2 := pinnedOrder ex.dag f.deg tier ++ pinnedOrder ex.dag f.deg rest
  let refCost (ord : Array Nat) : Nat :=
    ord.zipIdx.foldl (fun acc (t, i) => acc + weight.getD t 0 * layout.widthAt i) 0
  let kept := refCost order2 > refCost order1
  let order := if kept then order1 else order2
  -- Phase 3.
  let (entries, roots, predicted, work) ← materializeTable p order ex.roots limits layout.widthAt
  let priced := layoutBytes layout entries roots
  unless priced == predicted do
    throw (.internal s!"layout length {priced} differs from the evaluation {predicted}")
  unless predicted ≤ phase1Layout do
    throw (.internal s!"re-materialization {predicted} is longer than phase 1 {phase1Layout}")
  let (entryIds, rootIds, _) ← reexpand limits ex.dag entries roots
  unless entryIds == order do
    throw (.internal "re-materialized entries do not expand to the stored terms")
  unless rootIds == ex.roots do
    throw (.internal "re-materialized roots do not expand to the input roots")
  -- The real length: the bytes written with the current wire codec.
  let measured := tag0Size entries.size +
    (entries ++ roots).foldl (fun acc e => acc + (serExpr e).size) 0
  if layout == ShareLayout.wire && measured != predicted then
    throw (.internal s!"serialized length {measured} differs from the wire-layout price {predicted}")
  let stats : TieredStats :=
    { layout := layout, candidateCount := k, w := w, phase1ModelBytes := u.result.modelBytes,
      phase1LayoutBytes := phase1Layout, slotStates := slotStates, firstTier := tier,
      keptPhase1Order := kept, phase1RefCost := refCost order1, finalRefCost := refCost order,
      phase3LayoutBytes := predicted, savings := phase1Layout - predicted }
  let rstats : Stats := { u.result.stats with materializedNodes := work, outputBytes := measured }
  let res : ExactSharingResult :=
    { u.result with
      roots := roots, sharing := entries, tableTerms := order,
      variableBytes := measured, modelBytes := predicted, stats := rstats }
  return { result := res, phase1 := u, stats := stats }

end Ix.Sharing.Exact

end
