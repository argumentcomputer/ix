import IxCCTests.Grounding.Run
import IxCCTests.Corpus.Manifest

/-! # `tests-grounding`: the canonicity-free family's decided fact on the corpus

`noCanonB` (`IxCCGrounding.Facts`) on the 34 corpus closures the check accepts: true on 32, false
on `phase1-decline/erase` and `OS16-plain`, each for one `case` entry over a family with a level
parameter (its recursor's rules do not compare parameters). Controls on `decide`: the
`Decidable.casesOn` entry's recursor made to compare parameters (its rules marked not blind) makes
`noCanonB` false and leaves every conjunct of the check true; a constructor of that recursor given a
level parameter makes `noCanonB` false, and the check's `stored` and `caseShape` with it: the landed
check already refuses a constructor whose level count differs from its family's (`CaseWF.ctorRaw`,
and `stored` against the program's levels), which is why no mutation of that kind leaves the check
true.

`litDefsB` (`IxCCGrounding.Facts`, the premise under which #678's `lit_ops` gives `NatAccel`: every
`Nat` role the reading stores is stored as a definition) on the same 34: true on all, by name. Of
the fifteen roles a closure stores those its program reaches, each a definition without level
parameters, and nothing else (measured on all 50 loaded closures). Controls on `decide`: `Nat.add`
stored as an axiom makes it false; `Nat.beq` not stored at all leaves it true (a role that is not
stored needs nothing: no term naming it denotes). -/

namespace IxCCTests.Grounding.NoCanon

open IxCC IxCC.Grounding IxCCTests.Grounding
open IxCC.Src (CId)
open IxCCTests.Src (Assert expect)

/-- The accepted closures, by label: the family closures (with their non-declined roots) and the
extra ones (all roots). -/
def acceptedFamily : List String :=
  ["bench-k1/fib", "bench-k1/ackermann", "bench-k1/tak", "bench-k1/gcd", "bench-k1/even-odd",
   "bench-k1/sfib", "grounding/decide", "phase1-scalar/strictAndOr", "phase1-scalar/tuple",
   "phase1-scalar/bigctor", "phase1-scalar/natShiftr", "phase1-boundary/boundary",
   "phase1-boundary/tags16", "phase1-boundary/tags17", "phase1-boundary/tags125",
   "phase1-decline/closures", "phase1-decline/params", "phase1-decline/erase",
   "phase1-decline/symbols", "phase1-abi/abi"]

def acceptedExtra : List String :=
  ["OS01-annotated", "OS01-plain", "OS02-plain", "OS03-annotated", "OS03-plain",
   "OS03b-annotated", "OS03b-plain", "OS13-annotated", "OS13-plain", "OS14-annotated",
   "OS14-plain", "OS16-plain", "OS22-annotated", "OS22-plain"]

/-- The two accepted closures that do not qualify. -/
def notQualifying : List String := ["phase1-decline/erase", "OS16-plain"]

def familyFiles : List String :=
  ["fixtures/ixon-v4/bench-k1/corpus.json", "fixtures/corpus/grounding/corpus.json",
   "fixtures/corpus/phase1-scalar/corpus.json", "fixtures/corpus/phase1-boundary/corpus.json",
   "fixtures/corpus/phase1-decline/corpus.json", "fixtures/corpus/phase1-abi/corpus.json"]

def jobs : IO (List (String × String × List String)) := do
  let mut out := []
  for f in familyFiles do
    let fam ← IxCCTests.Corpus.Family.read f
    for fx in fam.fixtures do
      let label := s!"{fam.family}/{fx.name}"
      if !acceptedFamily.contains label then continue
      let roots := fx.roots.filter (·.decline.isNone) |>.map (·.name)
      let roots := if roots.isEmpty then fx.roots.map (·.name) else roots
      out := out ++ [(label, s!"{fam.directory}/{fx.closure.path.replace ".ixe" ""}", roots)]
  return out ++ acceptedExtra.map fun n => (n, s!"fixtures/ownership/{n}", [])

/-- The median time, in µs, of `n` evaluations of `f k` (`k` the evaluation's index, so that none
is shared with or hoisted out of another), and the last result. -/
def medianUs (n : Nat) (f : Nat → Bool) : IO (Bool × Nat) := do
  let mut ts : Array Nat := #[]
  let mut b := false
  for k in [0:n] do
    let t0 ← IO.monoNanosNow
    b ← IO.lazyPure fun _ => f k
    let t1 ← IO.monoNanosNow
    ts := ts.push ((t1 - t0) / 1000)
  return (b, (ts.qsort (· < ·))[n / 2]!)

def run : IO Bool := do
  let a : Assert ← IO.mkRef 0
  try
    let js ← jobs
    expect a (js.length == 34) s!"noCanon: {js.length} accepted closures found, expected 34"
    let mut yes : Nat := 0
    let mut no : List String := []
    let mut tagsUs : Nat := 0
    let mut ldUs : Nat := 0
    for (label, stem, roots) in js do
      let (i, _) ← loadClosure label stem roots
      let b := noCanonB i.src i.env i.κ i.Sl
      -- the cost on the largest accepted closure: the median of 9 evaluations, each on an
      -- environment the compiler cannot share between them
      if label == "phase1-boundary/tags125" then
        tagsUs := (← medianUs 9 fun k => noCanonB i.src (if k == 1000000 then default else i.env)
          i.κ i.Sl).2
        ldUs := (← medianUs 9 fun k => litDefsB (if k == 1000000 then default else i.env)).2
      expect a (b == !notQualifying.contains label)
        s!"noCanon: {label}: noCanonB {b}, expected {!notQualifying.contains label}"
      if b then yes := yes + 1 else no := no ++ [label]
      -- the `NatAccel` adapter's premise: every `Nat` role stored is stored as a definition
      expect a (litDefsB i.env) s!"litDefs: {label}: litDefsB false"
    expect a (yes == 32 && no == notQualifying)
      s!"noCanon: noCanonB true on {yes}, false on {no}"
    -- controls, on `decide`: its `case` entry over `Decidable` (rules not comparing parameters,
    -- constructors without level parameters)
    let (di, _) ← loadClosure "decide" "fixtures/corpus/grounding/decide" ["Grounding.decideFib10"]
    expect a ((failing di).isEmpty && noCanonB di.src di.env di.κ di.Sl)
      s!"decide: check {failing di}, noCanonB {noCanonB di.src di.env di.κ di.Sl}"
    let some (c, r) := di.Sl.findSome? (fun c => match di.src.table.resolveOf c with
        | some (.case r) => match caseShape? di.env (di.κ c) (di.κ r) with
          | some sh => if sh.nP == 1 && sh.indLevels.isEmpty then some (c, r) else none
          | none => none
        | _ => none) | throw (IO.userError "decide: no Decidable case entry")
    -- the recursor's rules marked not blind: they compare parameters
    let mB := { di with env := mapConst di.env (di.κ r) fun
      | .recInfo cv mI rP rules => .recInfo cv mI rP (rules.map fun (rl : Ix.Kernel.RecRule .anon) => { rl with paramsBlind := false })
      | ci => ci }
    expect a ((failing mB).isEmpty && !noCanonB mB.src mB.env mB.κ mB.Sl)
      s!"decide: c{r}'s rules comparing parameters: check {failing mB}, noCanonB {noCanonB mB.src mB.env mB.κ mB.Sl}"
    -- a constructor of the recursor given a level parameter
    let some (.recInfo _ _ _ (rl0 :: _)) := di.env.find? (di.κ r) | throw (IO.userError "decide: no rule")
    let mL := { di with env := mapConst di.env rl0.ctor fun
      | .ctorInfo cv nP nF => .ctorInfo { cv with levelParams := [99] } nP nF
      | ci => ci }
    expect a (!noCanonB mL.src mL.env mL.κ mL.Sl && (failing mL).contains "caseShape")
      s!"decide: a constructor of c{r} given a level parameter: check {failing mL}, noCanonB {noCanonB mL.src mL.env mL.κ mL.Sl}"
    IO.println s!"noCanon: noCanonB true on {yes} of the 34 accepted closures, false on {no} \
      (a case entry over a family with a level parameter); tags125 {tagsUs} µs (median of 9); \
      decide (case c{c}): its recursor's rules comparing parameters: noCanonB false, every \
      conjunct true; a constructor given a level parameter: noCanonB false, the check's {failing mL} false too"
    -- `litDefsB` controls, on `decide` (it stores `Nat.add` and `Nat.beq` as definitions): `Nat.add`
    -- stored as an axiom is refused (#678's `lit_ops` says nothing of it); `Nat.beq` not stored at
    -- all is accepted (no term naming it denotes, so the law is not needed there)
    let addK : KKey := primKey .add
    let beqK : KKey := primKey .beq
    expect a ((match di.env.find? addK with | some (.defnInfo ..) => true | _ => false) &&
        (match di.env.find? beqK with | some (.defnInfo ..) => true | _ => false))
      "decide: Nat.add and Nat.beq are not both stored as definitions"
    let envAx := mapConst di.env addK fun
      | .defnInfo cv _ _ => .axiomInfo cv
      | ci => ci
    expect a (!litDefsB envAx) "decide: Nat.add stored as an axiom: litDefsB true"
    let envNo : KEnv := { di.env with consts := di.env.consts.filter fun ci => ci.name != beqK }
    expect a ((envNo.find? beqK).isNone && litDefsB envNo)
      "decide: Nat.beq not stored: litDefsB false"
    IO.println s!"litDefs: litDefsB true on the 34 accepted closures; tags125 {ldUs} µs (median of \
      9); decide: Nat.add stored as an axiom: litDefsB false; Nat.beq not stored: litDefsB true"
    IO.println s!"tests-grounding (noCanon): {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: grounding (noCanon): {error}"
    return false

end IxCCTests.Grounding.NoCanon
