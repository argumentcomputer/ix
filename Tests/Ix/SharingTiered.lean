/-
  Tests for the tiered canonical construction (`Ix.Sharing.Exact.Tiered`):
  §2 fixtures under the wire layout (TagN), inputs where slot allocation changes the
  order, the "never longer than phase 1" guarantee, idempotence, a brute
  force for the first-tier allocation, the production path at scale (the
  parallel widths, a table past the 3-byte rung that makes the phase-2 guard
  keep the phase-1 order, a long spine, deep inputs) and every production
  limit reached through `canonicalSharingTiered` and the compiler's builder.
-/
module

public import Tests.Ix.SharingExact

public section

open LSpec Ixon Ix.Sharing.Exact Tests.SharingExact

-- Groups are functions run from deferred IO actions.
set_option compiler.extract_closed false

namespace Tests.SharingTiered

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
  let l := ShareLayout.tagN
  group "fixtures, TagN layout" (
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
      let l := ShareLayout.tagN
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
            r.result.modelBytes == r.result.variableBytes do
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

/-- An application spine of `1 + apps` nodes over `u = app(var 0, var 1)`
(the spine's last term), next to hot references: 100 copies of the spine, 20
of `u`, and 500 of each of eight references. With `apps = 1287` the phase-2
order of one candidate stores the spine before `u`, so phase 3 cannot price
it from the whole dictionary; with `apps = 1286` every candidate's order
allows it. -/
def spineWitness (apps : Nat) : Array Ixon.Expr := Id.run do
  let u : Ixon.Expr := .app (.var 0) (.var 1)
  let t := (List.range apps).foldl (fun acc i => .app acc (.var (2 + i).toUInt64)) u
  let mut roots : Array Ixon.Expr := (Array.replicate 100 t) ++ Array.replicate 20 u
  for h in [0:8] do
    roots := roots ++ Array.replicate 500 (.ref (100 + h).toUInt64 #[0, 0])
  return roots

/-- The phase-3 materialization against the per-prefix specification: the
same entries, roots, predicted length and work, or the same error. -/
def sameMaterialization (p : Prep) (order roots : Array Nat) (widthAt : Nat → Nat) : Bool :=
  match materializeTableOnePass p order roots {} widthAt, materializeTable p order roots {} widthAt with
  | .ok (e1, r1, p1, w1), .ok (e2, r2, p2, w2) => e1 == e2 && r1 == r2 && p1 == p2 && w1 == w2
  | .error e1, .error e2 => reprStr e1 == reprStr e2
  | _, _ => false

/-- Per candidate width: whether its table order takes the per-prefix path,
and whether the one-pass materialization agrees with the specification. -/
def candidatePaths (roots : Array Ixon.Expr) :
    Except SharingError (Array (Nat × Bool × Bool)) := do
  let ex ← expand {} #[] roots true
  let p := Prep.ofDag ex.dag
  [1, 2, 3].toArray.mapM fun w => do
    let r ← tieredAtWidth .tagN {} ex w
    let order := r.result.tableTerms
    let onePass := onePassOrder ex.dag order ex.roots (indexOfPrefix ex.dag.size order order.size)
    return (w, !onePass, sameMaterialization p order ex.roots ShareLayout.tagN.widthAt)

def fallbackTests (_ : Unit) : TestSeq :=
  withOk "spine witness" (candidatePaths (spineWitness 1287)) (fun paths =>
    withOk "spine witness" (canonicalSharingTieredTable .tagN #[] (spineWitness 1287)) fun r =>
      let perPrefix := (paths.filter (·.2.1)).size
      test s!"spine of 1288 nodes: {perPrefix} candidate takes the per-prefix path (expected 1), candidates {r.stats.candidateLengths} (expected #[(1, 7106), (2, 7106), (3, 7123)]), every candidate equal to the specification"
        (perPrefix == 1 && paths.all (·.2.2) &&
          r.stats.candidateLengths == #[(1, 7106), (2, 7106), (3, 7123)])) ++
  withOk "spine control" (candidatePaths (spineWitness 1286)) fun paths =>
    let perPrefix := (paths.filter (·.2.1)).size
    test s!"spine of 1287 nodes: {perPrefix} candidates take the per-prefix path (expected 0), every candidate equal to the specification"
      (perPrefix == 0 && paths.all (·.2.2))

def layoutTests (_ : Unit) : TestSeq :=
  test "TagN widths: 1 below 8, 2 below 1032, 3 below 66568, 4 below 16843784, 5 below 4311811080, then 9"
    ([7, 8, 1031, 1032, 66567, 66568, 16843783, 16843784, 4311811079, 4311811080].map
        ShareLayout.tagN.widthAt == [1, 2, 2, 3, 3, 4, 4, 5, 5, 9] &&
      tagNRung2End == 1032 && tagNRung3End == 66568 && tagNRung4End == 16843784 &&
      tagNRung5End == 4311811080)

/-! ## The production construction at scale -/

/-- `fillers` terms `X_i` (7-byte Refs), each used once directly and twice
inside each of the wrappers `app (var 0) X_i` and `app (var 1) X_i`, and
`chains` pairs: `A_j` (a 7-byte Ref used three times directly and once inside
`B_j`) and the binder `B_j`, used 40 times.

With more than 1,032 fillers the table crosses the 3-byte TagN rung, and the
DAG (more than `tieredParMin` terms) takes the parallel-widths branch of
`tieredCandidates`. At phase-1 widths 2 and 3 the wrappers stay inline, so a
filler's Share count (5) exceeds its in-degree (3), while `A_j` has 4 of
each: the phase-1 order (in-degree first) places every chain early, the
phase-2 Kahn order (Share count first) places the chains outside the first
tier after every filler, beyond index 1,032, and the guard keeps the phase-1
order. -/
def scaleRoots (fillers chains : Nat) : Array Ixon.Expr := Id.run do
  let mut roots : Array Ixon.Expr := #[]
  for i in [0:fillers] do
    let x : Ixon.Expr := .ref i.toUInt64 #[0, 0, 0, 0, 0]
    roots := roots.push x
    for _ in [0:2] do roots := roots.push (.app (.var 0) x)
    for _ in [0:2] do roots := roots.push (.app (.var 1) x)
  for j in [0:chains] do
    let a : Ixon.Expr := .ref (fillers + 2 * j).toUInt64 #[0, 0, 0, 0, 0]
    let b : Ixon.Expr := .lam .many a (.app (.var 0) (.ref (fillers + 2 * j + 1).toUInt64 #[0]))
    for _ in [0:3] do roots := roots.push a
    for _ in [0:40] do roots := roots.push b
  return roots

/-- An App spine of `n` arguments whose head is the repeated (stored) term
`s`, next to `s` itself: the spine's telescope count is in the 3-byte TagN
rung for `n ≥ 1032`. -/
def spineRoots (n : Nat) : Array Ixon.Expr :=
  let s : Ixon.Expr := .ref 3 #[0, 0, 0, 0, 0]
  #[(List.range n).foldl (fun acc i => .app acc (.var (i % 3).toUInt64)) s, s, s]

/-- The checks of one production run on `c`: the result is the candidate at
its winning width with every candidate as when run alone
(`candidatesOk`, which runs the widths one after the other), the serialized
length is the fixed part plus the variable bytes, the wire price equals the
serialized length, and normalizing the output reproduces it. -/
def productionOk (c : Constant) (r : TieredSharingResult) (n : Constant) : Bool :=
  selectionOk r && candidatesOk .tagN c r &&
    cbytes n == fixedConstantBytes c + r.result.variableBytes &&
    r.result.modelBytes == r.result.variableBytes &&
    (normalizeConstantSharingTiered .tagN n).toOption.map serConstant == some (serConstant n)

def scaleTests (_ : Unit) : TestSeq :=
  let big := wrapRoots (scaleRoots 1040 12) 0
  let spine := wrapRoots (spineRoots 1288) 0
  let d := 10000
  let shared : Ixon.Expr := .ref 5 #[0, 0, 0, 0, 0]
  let nested : Ixon.Expr :=
    (List.range d).foldl (fun acc i => .app (.var (i % 2).toUInt64) acc) shared
  let telescope : Ixon.Expr :=
    (List.range d).foldl (fun acc i => .lam .many (.var (i % 3).toUInt64) acc) shared
  let deep := wrapRoots #[nested, telescope, shared] 0
  group "the production construction at scale" <|
    withOk "1040 fillers" (canonicalSharingTieredTable .tagN #[] (constantInfoRoots big.info))
      (fun r => withOk "1040 fillers" (normalizeConstantSharingTiered .tagN big) fun n =>
        test s!"{r.result.stats.distinctSubterms} terms (parallel widths, ≥ {tieredParMin}), {n.sharing.size} entries (> 1032: 3-byte Shares), the phase-2 guard keeps the phase-1 order (reference cost {r.stats.phase1RefCost}); widths run alone agree, idempotent, serialized = fixed + variable"
          (r.result.stats.distinctSubterms ≥ tieredParMin && n.sharing.size > 1032 &&
            r.stats.keptPhase1Order && r.stats.finalRefCost == r.stats.phase1RefCost &&
            productionOk big r n)) ++
    withOk "spine" (canonicalSharingTieredTable .tagN #[] (constantInfoRoots spine.info))
      (fun r => withOk "spine" (normalizeConstantSharingTiered .tagN spine) fun n =>
        test s!"a 1288-argument App spine over a stored head: {cbytes n} bytes, {n.sharing.size} entries; widths run alone agree, idempotent, serialized = fixed + variable"
          (n.sharing.size ≥ 1 && productionOk spine r n)) ++
    withOk "deep" (canonicalSharingTieredTable .tagN #[] (constantInfoRoots deep.info))
      (fun r => withOk "deep" (normalizeConstantSharingTiered .tagN deep) fun n =>
        test s!"{d}-deep argument nesting and a {d}-binder telescope over a shared Ref: {cbytes n} bytes, {n.sharing.size} entries; widths run alone agree, idempotent, serialized = fixed + variable"
          (n.sharing.size ≥ 1 && productionOk deep r n))

/-! ## The production construction under its limits -/

/-- `canonicalSharingTiered` on `roots` under the default limits with one
limit changed fails with exactly `resourceExhausted r v`. -/
def failsWith (roots : Array Ixon.Expr) (l : Limits) (r : Resource) (v : Nat) : Bool :=
  match canonicalSharingTiered .tagN roots l with
  | .error (.resourceExhausted r' v') => r' == r && v' == v
  | _ => false

/-- The compiler's builder on `c` under `l` fails with the `resourceLimit`
error naming the limit `key`, its value and its override. -/
def compilerFailsWith (c : Constant) (l : Limits) (key : String) (v : Nat) : Bool :=
  match Ix.CompileM.buildConstantWithSharing l c.info c.refs c.univs with
  | .error (.resourceLimit msg) =>
    (msg.splitOn s!"resource exhausted: {key} (limit {v})").length > 1 &&
      (msg.splitOn s!"--sharing-limits {key}=N (IX_SHARING_LIMITS)").length > 1
  | _ => false

def productionLimitTests (_ : Unit) : TestSeq :=
  let t16c := axiomOf (arr (chain 16) (chain 16))
  let t16 := constantInfoRoots t16c.info
  -- 128 two-use atoms: 128 uncertain components and the table-count bracket
  -- knapsack (`Tests.SharingUniform.bracketTests`).
  let atomRoots : Array Ixon.Expr := (Array.range 128).foldl
    (fun acc i => let a : Ixon.Expr := .ref i.toUInt64 #[0]; acc ++ #[a, a]) #[]
  let atomsC := wrapRoots atomRoots 0
  let d : Limits := {}
  let cases : List (String × Constant × Limits × Resource × Nat) := [
    ("T16", t16c, { d with maxExprVisits := 3 }, .exprVisits, 3),
    ("T16", t16c, { d with maxDepth := 2 }, .depth, 2),
    ("T16", t16c, { d with maxNodes := 2 }, .nodes, 2),
    ("T16", t16c, { d with maxStates := 0 }, .states, 0),
    ("128 atoms", atomsC, { d with maxStates := 50 }, .states, 50),
    ("128 atoms", atomsC, { d with maxCostEvals := 10 }, .costEvals, 10),
    ("T16", t16c, { d with maxOutputBytes := 10 }, .outputBytes, 10),
    ("T16", t16c, { d with maxMaterialize := 3 }, .materialize, 3),
    ("T16", t16c, { d with maxMaterializeWork := 3 }, .materializeWork, 3),
    ("128 atoms", atomsC, { d with maxKnapsackCells := 10 }, .knapsackCells, 10)]
  group "the production construction under its limits" <|
    cases.foldl (init := .done) (fun acc (name, c, l, r, v) =>
      acc ++ test s!"{name}: {r.key} = {v} → canonicalSharingTiered fails with resourceExhausted {r.key} {v}; the compiler's builder with resourceLimit naming --sharing-limits {r.key}=N"
        (failsWith (constantInfoRoots c.info) l r v && compilerFailsWith c l r.key v)) ++
    test "the transitions limit meters only the width-state oracle: maxTransitions = 0 leaves T16 and the 128 atoms unchanged"
      ((canonicalSharingTiered .tagN t16 { d with maxTransitions := 0 }).toOption.map
          (·.result.sharing) == (canonicalSharingTiered .tagN t16).toOption.map (·.result.sharing) &&
        (canonicalSharingTiered .tagN atomRoots { d with maxTransitions := 0 }).toOption.map
          (·.result.variableBytes) ==
          (canonicalSharingTiered .tagN atomRoots).toOption.map (·.result.variableBytes) &&
        (canonicalSharingTiered .tagN t16).toOption.isSome)

public def suite : List TestSeq := [
  deferred "tiered layouts" layoutTests,
  deferred "tiered fixtures" fixtureTests,
  deferred "tiered allocation" allocationTests,
  deferred "first-tier brute force" tierBruteTests,
  deferred "Kahn priority order" kahnTests,
  deferred "phase-3 per-prefix fallback" fallbackTests,
  deferred "tiered at scale" scaleTests,
  deferred "tiered limits" productionLimitTests,
]

end Tests.SharingTiered
