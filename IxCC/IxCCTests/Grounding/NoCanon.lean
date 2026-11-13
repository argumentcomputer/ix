import IxCCTests.Grounding.Run
import IxCCTests.Corpus.Manifest
import IxCCGrounding.CaseLevels
import IxCC.Src.Relevance.Check

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
stored needs nothing: no term naming it denotes).

Step A (`IxCCGrounding.CaseLevels`, `rootSound_678A`): `noCanonAB` (`noCanonB` less the level
condition at `case` entries) and `instCheckB` on the instance set `instWalk` returns from every
root are true on the same 34, so the family over the instance set holds on all 34 (`erase` and
`OS16-plain` included). Controls on `OS16-plain`: a constructor of its `List`-shaped family raised
one level in one value, in the reading and the program alike, leaves the check and `noCanonAB`
true and makes `instCheckB` false (the family used at two level instantiations); the same
constructor at level 1 bound by a `let` in that value is not walked (`instCheckB` stays true), and
the check refuses the program at `valueCorr`, which is what keeps the walk's stopping at a
`let` out of every theorem. -/

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

/-! ## Step A: the verified instance set -/

/-- The roots of a loaded closure. -/
def rootsOf (i : Input) : List CId := i.src.roots.map (·.2)

/-- The instance set from every root, and whether `instCheckB` accepts it with every root as a seed. -/
def instOk (i : Input) : Bool :=
  match instWalk i.src (rootsOf i) 1000000 with
  | some Inst => instCheckB i.src i.env i.κ i.lpsOf (rootsOf i) Inst
  | none => false

/-- Every occurrence of the constructor `d` raised one level (the program's side). -/
def raiseS (d : CId) : IxCC.Src.Term → IxCC.Src.Term
  | .const c us => if c == d then .const c (us.map .succ) else .const c us
  | .app f a m r => .app (raiseS d f) (raiseS d a) m r
  | .lam b t u => .lam b (raiseS d t) (raiseS d u)
  | .pi b r t u => .pi b r (raiseS d t) (raiseS d u)
  | .letE x r t v u => .letE x r (raiseS d t) (raiseS d v) (raiseS d u)
  | .proj s n e => .proj s n (raiseS d e)
  | t => t

/-- The same in the kernel's reading. -/
def raiseK (k : KKey) : KExpr → KExpr
  | .const c ls => if c == k then .const c (ls.map .succ) else .const c ls
  | .app f a => .app (raiseK k f) (raiseK k a)
  | .lam A b m => .lam (raiseK k A) (raiseK k b) m
  | .forallE A b m => .forallE (raiseK k A) (raiseK k b) m
  | .proj s n e => .proj s n (raiseK k e)
  | e => e

/-- A constant of `Sl` with a value (no table entry) whose value names a constructor `d` of a
family with level parameters that a `case` entry of `Sl` is over. -/
def plantSite (i : Input) : Option (CId × CId) :=
  let fams := i.Sl.filterMap fun c =>
    match i.src.table.resolveOf c with
    | some (.case r) =>
      match i.src.decl? r with
      | some (.recr _ _ _ _ _ _ _ ind _ _) =>
        match i.src.decl? ind with
        | some (.induct _ lv _ _ _ _) => if lv > 0 then some ind else none
        | _ => none
      | _ => none
    | _ => none
  i.Sl.findSome? fun c =>
    match i.src.table.resolveOf c, i.src.decl? c with
    | none, some (.defn .defn .safe _ _ v) =>
      (constsOf v).findSome? fun d =>
        match i.src.decl? d with
        | some (.ctor _ lv ind _ _ _ _) => if lv > 0 && fams.contains ind then some (c, d) else none
        | _ => none
    | _, _ => none

def run : IO Bool := do
  let a : Assert ← IO.mkRef 0
  try
    let js ← jobs
    expect a (js.length == 34) s!"noCanon: {js.length} accepted closures found, expected 34"
    let mut yes : Nat := 0
    let mut no : List String := []
    let mut tagsUs : Nat := 0
    let mut ldUs : Nat := 0
    let mut famA : Nat := 0
    let mut instUs : Nat := 0
    let mut instN : Nat := 0
    for (label, stem, roots) in js do
      let (i, _) ← loadClosure label stem roots
      let b := noCanonB i.src i.env i.κ i.Sl
      -- step A: `noCanonAB` and the verified instance set, on every accepted closure
      let bA := noCanonAB i.src i.env i.κ i.Sl
      let iA := instOk i
      expect a (bA && iA) s!"levels: {label}: noCanonAB {bA}, instCheckB {iA}"
      if bA && iA && litDefsB i.env then famA := famA + 1
      -- the cost on the largest accepted closure: the median of 9 evaluations, each on an
      -- environment the compiler cannot share between them
      if label == "phase1-boundary/tags125" then
        tagsUs := (← medianUs 9 fun k => noCanonB i.src (if k == 1000000 then default else i.env)
          i.κ i.Sl).2
        ldUs := (← medianUs 9 fun k => litDefsB (if k == 1000000 then default else i.env)).2
        match instWalk i.src (rootsOf i) 1000000 with
        | some Inst =>
          instN := Inst.length
          instUs := (← medianUs 9 fun k => instCheckB i.src (if k == 1000000 then default else i.env)
            i.κ i.lpsOf (rootsOf i) Inst).2
        | none => pure ()
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
    -- step A: the family over the verified instance set accepts all 34 (`erase` and `OS16-plain`
    -- among them); on `OS16-plain`, a constructor of its `List`-shaped family raised one level in
    -- one value, in the reading and the program alike, leaves the check and `noCanonAB` true and
    -- makes `instCheckB` false; the same constructor hidden under a `let` in that value is not walked
    -- (`instCheckB` true) and the check refuses the program at `valueCorr` (`TermCorr` has no `let`)
    expect a (famA == 34) s!"levels: the family over the instance set holds on {famA} of 34"
    let (oi, _) ← loadClosure "OS16-plain" "fixtures/ownership/OS16-plain" []
    let some (c, d) := plantSite oi | throw (IO.userError "OS16-plain: no plant site")
    let some (.defn k s lv ty v) := oi.src.decl? c | throw (IO.userError "OS16-plain: no value")
    let envR := mapConst oi.env (oi.κ c) fun
      | .defnInfo cv val h => .defnInfo cv (raiseK (oi.κ d) val) h
      | ci => ci
    let raised := { oi with src := oi.src.setDecl c (.defn k s lv ty (raiseS d v)), env := envR }
    expect a (instOk oi && (failing raised).isEmpty && noCanonAB raised.src raised.env raised.κ raised.Sl &&
        !instOk raised)
      s!"levels: OS16-plain, c{d} raised in c{c}: check {failing raised}, instCheckB {instOk raised}"
    let hidden := { oi with src := oi.src.setDecl c (.defn k s lv ty
      (.letE default default (.sort .zero) (.const d [.succ .zero])
        (IxCC.Src.Relevance.Check.Canonical.liftTerm 1 0 v))) }
    expect a (instOk hidden && (failing hidden).contains "valueCorr")
      s!"levels: OS16-plain, c{d} at level 1 under a let in c{c}: check {failing hidden}, instCheckB {instOk hidden}"
    IO.println s!"levels: noCanonAB and instCheckB true on the 34 accepted closures, the family on {famA}; \
      tags125 {instN} instances, instCheckB {instUs} µs (median of 9); OS16-plain: c{d} raised one level \
      in c{c}: instCheckB false, the check true; under a let: instCheckB true, the check refuses at \
      {failing hidden}"
    IO.println s!"tests-grounding (noCanon): {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: grounding (noCanon): {error}"
    return false

end IxCCTests.Grounding.NoCanon
