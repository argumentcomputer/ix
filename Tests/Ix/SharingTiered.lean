/-
  Tests for the tiered canonical construction (`Ix.Sharing.Exact.Tiered`):
  §2 fixtures under both layouts, inputs where slot allocation changes the
  order, the "never longer than phase 1" guarantee, idempotence, and a brute
  force for the first-tier allocation.
-/
module

public import Tests.Ix.SharingExact

public section

open LSpec Ixon Ix.Sharing.Exact Tests.SharingExact

-- Groups are functions run from deferred IO actions.
set_option compiler.extract_closed false

namespace Tests.SharingTiered

def layouts : List ShareLayout := [.tag4, .f64]

def fixtureTests (_ : Unit) : TestSeq :=
  let (nine, hot) := nineRef
  let w2 := witness2
  let w16 := axiomOf (arr (chain 16) (chain 16))
  layouts.foldl (init := .done) fun acc l =>
    acc ++ group s!"fixtures, layout {reprStr l}" (
      withOk "T2" (normalizeConstantSharingTiered l w2) (fun n =>
        test s!"T2 → T2: {cbytes n} bytes = 17, d200009117b0b001921700170000000100"
          (cbytes n == 17 && hexOf (serConstant n) == "d200009117b0b001921700170000000100")) ++
      withOk "T16" (normalizeConstantSharingTiered l w16) (fun n =>
        test s!"T16 → T16: {cbytes n} bytes = 46" (cbytes n == 46)) ++
      withOk "nine" (canonicalSharingTieredTable l #[] (constantInfoRoots nine.info)) (fun r =>
        withOk "nine" (normalizeConstantSharingTiered l nine) fun n =>
          test s!"nine Refs: {cbytes n} bytes = 578; w={r.stats.w}; first tier {r.stats.firstTier} holds the hot atom; phase-1 layout {r.stats.phase1LayoutBytes}, final {r.stats.phase3LayoutBytes}"
            (cbytes n == 578 && r.stats.w == 2 && r.stats.firstTier.contains 2 &&
              (n.sharing.findIdx? (· == hot)).map (fun i => decide (i < 8)) == some true)))

/-- A heavy parent `P` over two lighter children, next to more than eight
ready atoms used three times each. The pinned order fills the first tier
with atoms; the allocation puts `P` and its children there. -/
def genHeavyParent : RGen (Array Ixon.Expr) := do
  let nAtoms := 9 + (← rand 4)
  let atoms : Array Ixon.Expr := (Array.range nAtoms).map fun j =>
    .ref (j + 10).toUInt64 (Array.replicate (1 + j % 3) 0)
  let c1 : Ixon.Expr := .ref 1 #[0, 0, 0]
  let c2 : Ixon.Expr := .ref 2 #[0, 0, 1]
  let parent : Ixon.Expr := if (← rand 2) == 0 then .app c1 c2 else arr c1 c2
  let mut roots : Array Ixon.Expr := #[]
  for a in atoms do
    for _ in [0:2 + (← rand 3)] do roots := roots.push a
  for _ in [0:8 + (← rand 15)] do roots := roots.push (.app (.var 1) parent)
  roots := roots.push c1
  roots := roots.push c2
  return roots

def allocationTests (_ : Unit) : TestSeq :=
  let (checked, changed, saved, err) := runGen 71 do
    let mut checked := 0
    let mut changed := 0
    let mut saved := 0
    let mut err : Option String := none
    for i in [0:120] do
      if err.isSome then break
      let roots ← if i % 2 == 0 then genHeavyParent else genRoots 6 16 5
      let c := wrapRoots roots i
      for l in layouts do
        match canonicalSharingTieredTable l #[] (constantInfoRoots c.info),
            normalizeConstantSharingTiered l c with
        | .ok r, .ok n =>
          checked := checked + 1
          if r.stats.finalRefCost < r.stats.phase1RefCost then changed := changed + 1
          if r.stats.savings > 0 then saved := saved + 1
          let fixedOk := match fixedConstantBytes c with
            | .ok fx => cbytes n == fx + r.result.variableBytes
            | .error _ => false
          let idem := (normalizeConstantSharingTiered l n).toOption.map serConstant ==
            some (serConstant n)
          unless r.stats.phase3LayoutBytes ≤ r.stats.phase1LayoutBytes &&
              r.stats.finalRefCost ≤ r.stats.phase1RefCost && fixedOk && idem &&
              (l != .tag4 || r.result.modelBytes == r.result.variableBytes) do
            err := some s!"case {i} {reprStr l}: phase1={r.stats.phase1LayoutBytes} final={r.stats.phase3LayoutBytes} refcost {r.stats.phase1RefCost}->{r.stats.finalRefCost} fixed={fixedOk} idem={idem}"
        | .error e, _ | _, .error e => err := some s!"case {i} {reprStr l}: error {reprStr e}"
    return (checked, changed, saved, err)
  group "slot allocation and re-materialization" <|
    test s!"{checked} runs (120 inputs × 2 layouts): final ≤ phase 1 in layout bytes and in reference cost; serialized = fixed + variable; Tag4 price = serialized; idempotent ({changed} runs where allocation lowered the reference cost, {saved} with positive savings)"
      (err.isNone && checked == 240 && changed > 0) ++
    (match err with | some m => test m false | none => .done)

/-- Brute force over all subsets: dependency-closed, at most `cap` terms,
maximum weight, ties by the greatest indicator vector in the order
(weight descending, ID ascending). -/
def bruteTier (n : Nat) (weight : Array Nat) (deps : Array (Array Nat)) (cap : Nat) :
    Array Nat := Id.run do
  let items := (Array.range n).qsort fun a b =>
    weight[a]! > weight[b]! || (weight[a]! == weight[b]! && a < b)
  let mut best : Option (Nat × Array Bool) := none
  for mask in [0:2 ^ n] do
    let inS (t : Nat) := (mask >>> t) % 2 == 1
    let members := (Array.range n).filter inS
    if members.size > cap then continue
    unless members.all (fun t => deps[t]!.all inS) do continue
    let wsum := members.foldl (fun acc t => acc + weight[t]!) 0
    let vec := items.map inS
    let better := match best with
      | none => true
      | some (bw, bv) =>
        wsum > bw || (wsum == bw && Id.run do
          for h : i in [0:vec.size] do
            if vec[i] != bv[i]! then return vec[i]
          return false)
    if better then best := some (wsum, vec)
  match best with
  | some (_, vec) => (items.zipIdx.filter (fun (_, i) => vec[i]!)).map (·.1) |>.qsort (· < ·)
  | none => #[]

def tierBruteTests (_ : Unit) : TestSeq :=
  let (checked, err) := runGen 73 do
    let mut checked := 0
    let mut err : Option String := none
    for i in [0:300] do
      if err.isSome then break
      let n := 1 + (← rand 12)
      let mut weight : Array Nat := #[]
      let mut deps : Array (Array Nat) := #[]
      for t in [0:n] do
        weight := weight.push (1 + (← rand 4))
        let mut ds : Array Nat := #[]
        for u in [0:t] do
          if (← rand 4) == 0 then ds := ds.push u
        deps := deps.push ds
      let cap := min 8 (1 + (← rand n))
      let wmap : Std.HashMap Nat Nat := (Array.range n).foldl (fun m t => m.insert t weight[t]!) {}
      let dmap : Std.HashMap Nat (Array Nat) := (Array.range n).foldl (fun m t => m.insert t deps[t]!) {}
      match firstTier (Array.range n) wmap dmap cap {} with
      | .ok (s, _) =>
        checked := checked + 1
        let expected := bruteTier n weight deps cap
        unless s == expected do
          err := some s!"case {i}: n={n} cap={cap} weights={weight} deps={deps} search={s} brute={expected}"
      | .error e => err := some s!"case {i}: error {reprStr e}"
    return (checked, err)
  group "first-tier allocation vs brute force" <|
    test s!"{checked} random dependency DAGs (≤ 12 terms, cap ≤ 8, weights 1–4): branch and bound = enumeration, including ties"
      (err.isNone && checked == 300) ++
    (match err with | some m => test m false | none => .done)

def layoutTests (_ : Unit) : TestSeq :=
  test "F64 widths: 1 below 8, 2 below 1032, 3 below 66568, 5 below 66568+2^32, then 9"
    ([7, 8, 1031, 1032, 66567, 66568, 66568 + 2 ^ 32 - 1, 66568 + 2 ^ 32].map ShareLayout.f64.widthAt ==
      [1, 2, 2, 3, 3, 5, 5, 9]) ++
  test "uniform width by candidate count: tag4 1/2/3 at 8/256/257, f64 2 up to 1032"
    (ShareLayout.tag4.uniformWidth 8 == 1 && ShareLayout.tag4.uniformWidth 256 == 2 &&
      ShareLayout.tag4.uniformWidth 257 == 3 && ShareLayout.f64.uniformWidth 1032 == 2 &&
      ShareLayout.f64.uniformWidth 1033 == 3)

public def suite : List TestSeq := [
  deferred "tiered layouts" layoutTests,
  deferred "tiered fixtures" fixtureTests,
  deferred "tiered allocation" allocationTests,
  deferred "first-tier brute force" tierBruteTests,
]

end Tests.SharingTiered
