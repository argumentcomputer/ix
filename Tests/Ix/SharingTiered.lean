/-
  Tests for the tiered canonical construction (`Ix.Sharing.Exact.Tiered`):
  §2 fixtures under the wire layout (TagN), inputs where slot allocation changes the
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

def layouts : List ShareLayout := [.tagN]

/-- The pinned width selection: three candidates (w = 1, 2, 3), the result is
the first one with the fewest final layout bytes. -/
def selectionOk (r : TieredSharingResult) : Bool :=
  let ls := r.stats.candidateLengths
  let best := ls.foldl (fun m (_, b) => min m b) r.stats.phase3LayoutBytes
  ls.map (·.1) == #[1, 2, 3] && r.stats.phase3LayoutBytes == best &&
    (ls.find? (·.2 == best)).map (·.1) == some r.stats.w

/-- The candidate at phase-1 width `w` alone (`tieredAtWidth`) on the
expanded roots of `c`. -/
def candidateAt (l : ShareLayout) (c : Constant) (w : Nat) :
    Except SharingError TieredSharingResult := do
  let ex ← expand {} c.sharing (constantInfoRoots c.info) true
  tieredAtWidth l {} ex w

/-- Every recorded candidate length is that of the candidate run alone, and
the result is byte-identical to the candidate at its winning width. -/
def candidatesOk (l : ShareLayout) (c : Constant) (r : TieredSharingResult) : Bool :=
  r.stats.candidateLengths.all (fun (w, b) =>
    match candidateAt l c w with
    | .ok cw => cw.stats.w == w && cw.stats.phase3LayoutBytes == b &&
        cw.stats.candidateLengths == #[(w, b)]
    | .error _ => false) &&
  match candidateAt l c r.stats.w with
  | .ok cw => cw.result.sharing == r.result.sharing && cw.result.roots == r.result.roots
  | .error _ => false

/-- `candidatesOk` for the canonical result of `c`. -/
def sameAsCandidates (l : ShareLayout) (c : Constant) : Bool :=
  match canonicalSharingTieredTable l c.sharing (constantInfoRoots c.info) with
  | .ok r => candidatesOk l c r
  | .error _ => false

def fixtureTests (_ : Unit) : TestSeq :=
  let (nine, hot) := nineRef
  let w2 := witness2
  let w16 := axiomOf (arr (chain 16) (chain 16))
  layouts.foldl (init := .done) fun acc l =>
    acc ++ group s!"fixtures, layout {reprStr l}" (
      withOk "T2" (normalizeConstantSharingTiered l w2) (fun n =>
        test s!"T2 → T2: {cbytes n} bytes = 17, d200009117b0b001921700170000000100"
          (cbytes n == 17 && hexOf (serConstant n) == "d200009117b0b001921700170000000100" &&
            sameAsCandidates l w2)) ++
      withOk "T16" (normalizeConstantSharingTiered l w16) (fun n =>
        test s!"T16 → T16: {cbytes n} bytes = 46, the candidates run alone agree"
          (cbytes n == 46 && sameAsCandidates l w16)) ++
      withOk "nine" (canonicalSharingTieredTable l #[] (constantInfoRoots nine.info)) (fun r =>
        withOk "nine" (normalizeConstantSharingTiered l nine) fun n =>
          test s!"nine Refs: {cbytes n} bytes = 578, the candidates run alone agree; w={r.stats.w} (candidates {r.stats.candidateLengths}); first tier {r.stats.firstTier} holds the hot atom; phase-1 layout {r.stats.phase1LayoutBytes}, final {r.stats.phase3LayoutBytes}"
            (cbytes n == 578 && selectionOk r && sameAsCandidates l nine &&
              r.stats.firstTier.contains 2 &&
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
  let (checked, changed, saved, beatOther, err) := runGen 71 do
    let mut checked := 0
    let mut changed := 0
    let mut saved := 0
    let mut beatOther := 0
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
          let fixedOk := cbytes n == fixedConstantBytes c + r.result.variableBytes
          let idem := (normalizeConstantSharingTiered l n).toOption.map serConstant ==
            some (serConstant n)
          -- every candidate run alone has its recorded length, and the result
          -- is the candidate at its winning width
          let candOk := candidatesOk l c r
          if r.stats.candidateLengths.any (·.2 > r.stats.phase3LayoutBytes) then
            beatOther := beatOther + 1
          unless r.stats.phase3LayoutBytes ≤ r.stats.phase1LayoutBytes &&
              r.stats.finalRefCost ≤ r.stats.phase1RefCost && fixedOk && idem &&
              selectionOk r && candOk &&
              (l != ShareLayout.wire || r.result.modelBytes == r.result.variableBytes) do
            err := some s!"case {i} {reprStr l}: phase1={r.stats.phase1LayoutBytes} final={r.stats.phase3LayoutBytes} refcost {r.stats.phase1RefCost}->{r.stats.finalRefCost} fixed={fixedOk} idem={idem} selection={selectionOk r} {r.stats.candidateLengths} candidates={candOk}"
        | .error e, _ | _, .error e => err := some s!"case {i} {reprStr l}: error {reprStr e}"
    return (checked, changed, saved, beatOther, err)
  group "slot allocation and re-materialization" <|
    test s!"{checked} runs (120 inputs, TagN layout): final ≤ phase 1 in layout bytes and in reference cost; serialized = fixed + variable; wire price = serialized; idempotent; the fewest bytes over w = 1, 2, 3 (lower w at a tie), each candidate as when run alone ({changed} runs where allocation lowered the reference cost, {saved} with positive savings, {beatOther} where another width was longer)"
      (err.isNone && checked == 120 && changed > 0) ++
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
      match firstTier (Array.range n) (weight[·]!) (fun t => deps[t]!.toList) cap {} with
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

/-- Reference Kahn priority order: repeatedly the remaining term whose
dependencies in `rest` are all placed, of the largest weight, then the
smallest ID. -/
def kahnRef (weight : Nat → Nat) (deps : Nat → List Nat) (rest : Array Nat) : Array Nat :=
  Id.run do
  let mut out : Array Nat := #[]
  let mut remaining := rest.toList
  for _ in [0:rest.size] do
    let ready := remaining.filter fun t =>
      (deps t).all fun d => !rest.contains d || out.contains d
    match ready.foldl (fun acc t => match acc with
        | none => some t
        | some a => if tierOrder weight t a && t != a then some t else acc) none with
    | none => break
    | some t =>
      out := out.push t
      remaining := remaining.erase t
  return out

def kahnTests (_ : Unit) : TestSeq :=
  let (checked, err) := runGen 91 do
    let mut checked := 0
    let mut err : Option String := none
    for i in [0:300] do
      if err.isSome then break
      let n := 1 + (← rand 30)
      let mut weight : Array Nat := #[]
      let mut deps : Array (List Nat) := #[]
      let mut rest : Array Nat := #[]
      for t in [0:n] do
        weight := weight.push (1 + (← rand 5))
        let mut ds : List Nat := []
        for u in [0:t] do
          if (← rand 5) == 0 then ds := u :: ds
        -- occasional repeated references
        if (← rand 4) == 0 then if let some d := ds.head? then ds := d :: ds
        deps := deps.push ds
        if (← rand 4) != 0 then rest := rest.push t
      let got := kahnOrder (weight[·]!) (deps[·]!) rest
      let want := kahnRef (weight[·]!) (deps[·]!) rest
      checked := checked + 1
      unless got == want do
        err := some s!"case {i}: weights={weight} deps={deps} rest={rest} kahn={got} reference={want}"
    return (checked, err)
  group "Kahn priority order" <|
    test s!"{checked} random dependency DAGs (≤ 30 terms, weights 1–5, repeated references, dependencies outside the set): kahnOrder = the reference order"
      (err.isNone && checked == 300) ++
    (match err with | some m => test m false | none => .done)

def layoutTests (_ : Unit) : TestSeq :=
  test "TagN widths: 1 below 8, 2 below 1032, 3 below 66568, 4 below 16843784, 5 below 4311811080, then 9"
    ([7, 8, 1031, 1032, 66567, 66568, 16843783, 16843784, 4311811079, 4311811080].map
        ShareLayout.tagN.widthAt == [1, 2, 2, 3, 3, 4, 4, 5, 5, 9] &&
      tagNRung2End == 1032 && tagNRung3End == 66568 && tagNRung4End == 16843784 &&
      tagNRung5End == 4311811080) ++
  test "the wire layout is TagN" (ShareLayout.wire == .tagN)

public def suite : List TestSeq := [
  deferred "tiered layouts" layoutTests,
  deferred "tiered fixtures" fixtureTests,
  deferred "tiered allocation" allocationTests,
  deferred "first-tier brute force" tierBruteTests,
  deferred "Kahn priority order" kahnTests,
]

end Tests.SharingTiered
