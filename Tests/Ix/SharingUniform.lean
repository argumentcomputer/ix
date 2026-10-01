/-
  Tests for the uniform-width exact optimizer (`Ix.Sharing.Exact.Uniform`).

  The reference is the width-state search run with every Share priced `w`
  (`optimizeSharingUniformReference`), which explores all table orders and
  subsets of the R1/R2 candidates. On every generated input we check:
  * equal minimum model length;
  * every certain-stored term is in the reference optimum, and no
    certain-excluded term is (both classes are "every/no minimum" claims);
  * model length ≤ unshared; the output re-expands to the input (checked
    inside the optimizer).
  Inputs include spine prefixes used only as prefixes, Apps with a 2-byte
  payload, and parent/child pairs whose sharing interacts.
-/
module

public import Tests.Ix.SharingExact

public section

open LSpec Ixon Ix.Sharing.Exact Tests.SharingExact

-- Groups are functions run from deferred IO actions.
set_option compiler.extract_closed false

namespace Tests.SharingUniform

/-- Independent uniform-model cost of independent atoms: choose a subset,
pay its entries and `w` per use, inline the rest. -/
def atomsUniformBrute (w : Nat) (sizes occs : Array Nat) : Nat := Id.run do
  let n := sizes.size
  let mut best := 0
  for mask in [0:2 ^ n] do
    let inS (i : Nat) := (mask >>> i) % 2 == 1
    let mut cost := tag0Size ((List.range n).filter inS).length
    for i in [0:n] do
      cost := cost + (if inS i then sizes[i]! + occs[i]! * w else occs[i]! * sizes[i]!)
    if mask == 0 || cost < best then best := cost
  return best

/-- Spine prefixes `f a` that only occur as prefixes of longer spines. -/
def genPrefixes : RGen (Array Ixon.Expr) := do
  let f ← genLeaf
  let a ← genLeaf
  let b ← genLeaf
  let pre : Ixon.Expr := if (← rand 2) == 0 then .app f a else .app (.app f a) b
  let mut roots : Array Ixon.Expr := #[]
  for i in [0:2 + (← rand 4)] do
    let x : Ixon.Expr := .var (i % 3).toUInt64
    let y ← genLeaf
    roots := roots.push (if (← rand 2) == 0 then .app pre x else .app (.app pre x) y)
  return roots

/-- Apps with a 2-byte payload used in several head positions. -/
def genSmallPayload : RGen (Array Ixon.Expr) := do
  let e : Ixon.Expr := .app (.var (← rand 2).toUInt64) (.var 1)
  let mut roots : Array Ixon.Expr := #[]
  for _ in [0:2 + (← rand 5)] do
    roots := roots.push <| match ← rand 3 with
      | 0 => .app (.ref 1 #[]) e
      | 1 => .lam .many e (.var 0)
      | _ => arr e (.sort 0)
  return roots

/-- A child `c` inside a parent `p`, each used a few times. -/
def genPairs : RGen (Array Ixon.Expr) := do
  let pool ← (List.range 3).toArray.mapM fun _ => genLeaf
  let c ← genNode pool
  let p : Ixon.Expr := match ← rand 3 with
    | 0 => .app c pool[0]!
    | 1 => arr pool[1]! c
    | _ => .prj 0 1 c
  let mut roots : Array Ixon.Expr := #[]
  for _ in [0:1 + (← rand 4)] do roots := roots.push (.app (.var 2) p)
  for _ in [0:1 + (← rand 4)] do roots := roots.push (.lam .many c (.var 0))
  return roots

/-- A nested App chain `u₁ = f a₁`, `uᵢ₊₁ = uᵢ aᵢ₊₁` whose prefixes are also
used on their own, so uncertain terms connect along the chain. -/
def genChain : RGen (Array Ixon.Expr) := do
  let leaves ← (List.range 3).toArray.mapM fun _ => genLeaf
  let mut u : Ixon.Expr := .app leaves[0]! leaves[1]!
  let mut roots : Array Ixon.Expr := #[]
  for _ in [0:3 + (← rand 6)] do
    for _ in [0:1 + (← rand 2)] do
      roots := roots.push (if (← rand 2) == 0 then .app (.var 7) u else arr u (.sort 0))
    u := .app u leaves[← rand 3]!
  roots := roots.push u
  return roots

def genUniformRoots : RGen (Array Ixon.Expr) := do
  match ← rand 6 with
  | 0 => genPrefixes
  | 1 => genSmallPayload
  | 2 => genPairs
  | 3 => genChain
  | _ => genRoots 5 12 4

/-- Check one input at width `w` against the reference. Returns
`(checked?, stats)` or an error message. -/
def checkUniform (w : Nat) (roots : Array Ixon.Expr) :
    Except String (Nat × Nat × Nat × Nat) :=
  match optimizeSharingUniform w roots, optimizeSharingUniformReference w roots,
      optimizeSharingUniformReference w roots {} (minInDegree2 := true) with
  | .ok u, .ok r, .ok rr =>
    let refSet := r.tableTerms
    if u.result.modelBytes != r.modelBytes || rr.modelBytes != r.modelBytes then
      .error s!"w={w}: uniform={u.result.modelBytes} reference={r.modelBytes} restricted={rr.modelBytes} stored={u.stored} ref={refSet} roots={reprStr roots}"
    else if !u.certainStored.all rr.tableTerms.contains then
      .error s!"w={w}: certain-stored {u.certainStored} not in restricted reference optimum {rr.tableTerms} roots={reprStr roots}"
    else if u.certainExcluded.any refSet.contains || u.certainExcluded.any rr.tableTerms.contains then
      .error s!"w={w}: certain-excluded {u.certainExcluded} in reference optimum {refSet} roots={reprStr roots}"
    else if u.result.modelBytes > u.result.unsharedBytes then
      .error s!"w={w}: model {u.result.modelBytes} > unshared {u.result.unsharedBytes}"
    else
      let maxComp := u.components.foldl (fun acc c => max acc c.size) 0
      .ok (u.certainStored.size, u.certainExcluded.size, u.uncertain.size, maxComp)
  | .error e, _, _ => .error s!"w={w}: uniform error {reprStr e} roots={reprStr roots}"
  | _, .error e, _ | _, _, .error e => .error s!"w={w}: reference error {reprStr e} roots={reprStr roots}"

def agreementTests (_ : Unit) : TestSeq :=
  let (checked, cs, ce, un, maxComp, withUncertain, err) := runGen 61 do
    let mut checked := 0
    let mut cs := 0
    let mut ce := 0
    let mut un := 0
    let mut maxComp := 0
    let mut withUncertain := 0
    let mut err : Option String := none
    for i in [0:3000] do
      if checked ≥ 400 || err.isSome then break
      let roots ← genUniformRoots
      let w := [1, 2, 3, 5][← rand 4]!
      -- Keep the reference search small.
      let refCands := match sharingProfile (wrapRoots roots 0) with
        | .ok p => p.candidates
        | .error _ => 100
      if refCands > 11 then continue
      match checkUniform w roots with
      | .ok (a, b, c, m) =>
        checked := checked + 1
        cs := cs + a
        ce := ce + b
        un := un + c
        maxComp := max maxComp m
        if c > 0 then withUncertain := withUncertain + 1
      | .error m => err := some s!"case {i}: {m}"
    return (checked, cs, ce, un, maxComp, withUncertain, err)
  group "uniform optimizer vs width-state reference (uniform widths)" <|
    test s!"{checked} generated inputs (w ∈ 1,2,3,5; prefixes, 2-byte payloads, parent/child pairs, App chains, general): equal minimum (also = in-degree-≥2 reference); certain-stored ⊆ restricted optimum; certain-excluded in neither optimum; ≤ unshared ({cs} certain-stored, {ce} certain-excluded, {un} uncertain terms; {withUncertain} inputs with uncertain terms; largest component {maxComp})"
      (err.isNone && checked == 400) ++
    (match err with | some m => test m false | none => .done)

def witnessTests (_ : Unit) : TestSeq :=
  let roots := constantInfoRoots witness2.info
  let run (w : Nat) := optimizeSharingUniform w roots
  group "uniform witness T2 → T2 (ids P=0 T1=1 T2=2 R=3)" <|
    withOk "w=1" (run 1) (fun u =>
      test s!"w=1: T2 certain-stored, stores only T2, model {u.result.modelBytes} = 11"
        (u.certainStored == #[2] && u.stored == #[2] && u.result.modelBytes == 11 &&
          u.result.variableBytes == 11)) ++
    withOk "w=2" (run 2) (fun u =>
      test s!"w=2: T2 uncertain (gain 1), search stores only T2, model {u.result.modelBytes} = 13"
        (u.uncertain == #[2] && u.stored == #[2] && u.result.modelBytes == 13)) ++
    withOk "w=3" (run 3) (fun u =>
      test s!"w=3: T2 uncertain, search stores nothing, model {u.result.modelBytes} = 14 (unshared); T1 certain-excluded"
        (u.uncertain == #[2] && u.stored.isEmpty && u.result.modelBytes == 14 &&
          u.certainExcluded.contains 1)) ++
    test "w=1,2,3 agree with the reference search"
      ([1, 2, 3].all fun w => (checkUniform w roots).toOption.isSome) ++
    test "w=0 is rejected" (isErr (optimizeSharingUniform 0 roots) fun
      | .formatBound _ _ => true
      | _ => false)

def t16Tests (_ : Unit) : TestSeq :=
  let roots := constantInfoRoots (axiomOf (arr (chain 16) (chain 16))).info
  group "uniform T16 → T16" <|
    withOk "w=1" (optimizeSharingUniform 1 roots) (fun u =>
      withOk "reference" (optimizeSharingUniformReference 1 roots) fun r =>
        test s!"w=1: model {u.result.modelBytes} = reference {r.modelBytes}; classes {u.certainStored.size} stored / {u.uncertain.size} uncertain / {u.certainExcluded.size} excluded; {u.statesVisited} states vs reference {r.stats.statesReached}"
          (u.result.modelBytes == r.modelBytes && (checkUniform 1 roots).toOption.isSome))

/-- 128 and 129 independent atoms whose sharing saves exactly one byte each:
the table count crosses 128. -/
def bracketTests (_ : Unit) : TestSeq :=
  let atoms (n : Nat) : Array Ixon.Expr := (Array.range n).map fun i => .ref i.toUInt64 #[0]
  let rootsOf (n : Nat) := (atoms n).foldl (fun acc a => acc ++ #[a, a]) #[]
  let sizes (n : Nat) := (atoms n).map exprSize
  group "table-count bracket coupling" <|
    withOk "128 atoms" (optimizeSharingUniform 1 (rootsOf 128)) (fun u =>
      test s!"128 atoms: all uncertain; storing 127 ties storing 128 (one count byte); the tie order leaves out the smallest ID; model {u.result.modelBytes} = 642"
        (u.uncertain.size == 128 && u.stored.size == 127 && !u.stored.contains 0 &&
          u.lowerBracket && u.result.modelBytes == 1 + 127 * 5 + 6 &&
          u.result.modelBytes == 2 + 128 * 5)) ++
    withOk "129 atoms" (optimizeSharingUniform 1 (rootsOf 129)) (fun u =>
      test s!"129 atoms (the last, Ref(128), is 4 bytes and certain-stored): keeps all 129, model {u.result.modelBytes} = 648"
        (u.stored.size == 129 && !u.lowerBracket && u.certainStored == #[128] &&
          u.result.modelBytes == 2 + 128 * 5 + 6)) ++
    test "atom brute force agrees on 10 atoms with mixed sizes and uses"
      (let as : Array Ixon.Expr := (Array.range 10).map fun i =>
          .ref i.toUInt64 (Array.replicate (i % 3) 0)
       let occs := (Array.range 10).map fun i => 1 + i % 4
       let roots := (Array.range 10).foldl (fun acc i => acc ++ Array.replicate occs[i]! as[i]!) #[]
       [1, 2, 3].all fun w =>
         (optimizeSharingUniform w roots).toOption.map (·.result.modelBytes) ==
           some (atomsUniformBrute w (as.map exprSize) occs)) ++
    test "sizes" ((sizes 3).all (· == 3))

def propertyTests (_ : Unit) : TestSeq :=
  let (checked, err) := runGen 67 do
    let mut checked := 0
    let mut err : Option String := none
    for i in [0:200] do
      if err.isSome then break
      let roots ← genRoots 6 16 4
      let c := wrapRoots roots i
      let w := [1, 2, 4][← rand 3]!
      match normalizeConstantSharingUniform w c with
      | .ok n =>
        checked := checked + 1
        let again := (normalizeConstantSharingUniform w n).toOption.map serConstant
        let fresh := match deConstant (serConstant c) with
          | .ok c' => (normalizeConstantSharingUniform w c').toOption.map serConstant
          | .error _ => none
        unless again == some (serConstant n) && fresh == some (serConstant n) do
          err := some s!"case {i}: not idempotent or representation dependent"
      | .error e => err := some s!"case {i}: error {reprStr e}"
    return (checked, err)
  group "uniform properties" <|
    test s!"{checked} constants: normalize is idempotent and independent of pointer layout" (err.isNone && checked == 200) ++
    (match err with | some m => test m false | none => .done)

public def suite : List TestSeq := [
  deferred "uniform witness" witnessTests,
  deferred "uniform vs reference" agreementTests,
  deferred "uniform T16" t16Tests,
  deferred "uniform table-count brackets" bracketTests,
  deferred "uniform properties" propertyTests,
]

end Tests.SharingUniform
