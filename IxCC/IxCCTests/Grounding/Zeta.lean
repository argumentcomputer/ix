import IxCCTests.Grounding.Run
import IxCCTests.Corpus.Manifest
import IxCC.Src.Relevance.Check

/-! # `tests-grounding`: step C, a `let` in a run term

The kernel stores a run term's ζ-reduct, and the check's correspondence (`valueCorr`, `eqnCorr`:
`corrSB []`, `TermCorrS` decided) relates the Src term with its `let`s to it through a
substitution: a live `let`'s variable stands for its value's copy, which must occur with no binder
between; a dead `let`'s for nothing; a `let` whose variable meets its copy only under a binder (a
"deep" `let`) is refused.

* **The corpus.** Of the 67 constants of the corpus closures whose run term the let-free
  correspondence (`termCorrB`) refuses, `corrSB []` accepts 61, by closure (`expectCorr`, the
  table `zetaTable`); it refuses 3 for a string literal (`phase1-decline/strings` c262,
  `phase1-decline/panic` c363 and c322, numbered c359 and c318 before the closures were refrozen with
  their word equations: step S) and 3 for a deep `let` (`phase2-arity/arity` c597,
  `phase2-closures/closures` c272 and c19), each asserted by name with its reason. The three
  closures it unlocks (`fields254`, `machines`, `natural`) are checked with the accepted closures
  (`IxCCTests.Grounding.NoCanon`); here, the other eleven closures' false conjuncts, by name.
* **Planted, on `fib`'s root** (its stored value and run term unchanged otherwise): a live `let`
  around the value (`let x := v; x`) and a dead one (`let x := 99; v`) are accepted, every conjunct
  true, and SrcEval still reads back `55`; the live `let`'s value replaced by a term that does not
  correspond to its copy is refused at `valueCorr` alone; a `let` whose variable occurs only under
  a λ (`let x := v; λ _. x` against the stored `λ _. v`) is refused at `valueCorr` alone, as deep.
-/

namespace IxCCTests.Grounding.Zeta

open IxCC IxCC.Grounding IxCCTests.Grounding
open IxCC.Src (Term CId Value)
open IxCCTests.Src (Assert expect)

/-- Does a Src term hold a string literal? -/
def hasStrLit : Term → Bool
  | .strLit _ => true
  | .app f a _ _ => hasStrLit f || hasStrLit a
  | .lam _ d b | .pi _ _ d b => hasStrLit d || hasStrLit b
  | .letE _ _ t v b => hasStrLit t || hasStrLit v || hasStrLit b
  | .proj _ _ e => hasStrLit e
  | _ => false

/-- Does the check meet a deep `let` (its variable's copy occurs only under a binder), walking as
`corrSB` walks? -/
def deepLet : Term → KExpr → Bool
  | .app f a _ _, .app f' a' => deepLet f f' || deepLet a a'
  | .lam _ d b, .lam d' b' _ => deepLet d d' || deepLet b b'
  | .pi _ _ d c, .forallE d' c' _ => deepLet d d' || deepLet c c'
  | .proj _ _ x, .proj _ _ x' => deepLet x x'
  | .letE _ _ _ v b, e =>
    match zcopy b e with
    | some v' => !subAt0B v' e || deepLet v v' || deepLet b e
    | none => deepLet b e
  | _, _ => false

/-- What the substitution check does on a closure: of the constants of `Sl` whose run pair the
let-free correspondence refuses, the number `corrSB []` accepts, and those it refuses, each with
its reason (`deep`, `string`, or `other`). -/
def corrOf (i : Input) : Nat × List (CId × String) := Id.run do
  let mut ok := 0
  let mut bad : List (CId × String) := []
  for c in i.Sl do
    for (t, e) in runPairsB i.src i.env i.κ c do
      if termCorrB i.κ (i.lpsOf c) t e then continue
      if corrSB i.κ (i.lpsOf c) [] t e then ok := ok + 1
      else
        let why := if deepLet t e then "deep" else if hasStrLit t then "string" else "other"
        bad := bad ++ [(c, why)]
  return (ok, bad)

/-- The closures holding the 67 constants: label, the number `corrSB []` accepts, the refused
ones with their reasons. -/
def zetaTable : List (String × Nat × List (CId × String)) :=
  [("bench-k1/sum-loop", 3, []), ("bench-k1/collatz", 3, []), ("bench-k1/prime-count", 3, []),
   ("phase1-scalar/scalar", 12, []), ("phase1-boundary/fields254", 1, []),
   ("phase1-resource/resource", 4, []), ("phase1-decline/loops", 4, []),
   ("phase1-decline/strings", 7, [(262, "string")]),
   ("phase1-decline/panic", 2, [(363, "string"), (322, "string")]),
   ("phase2-closures/closures", 4, [(272, "deep"), (19, "deep")]),
   ("phase1-machines/machines", 3, []), ("phase1-machines/natural", 4, []),
   ("phase2-arity/arity", 0, [(597, "deep")]),
   ("fixtures/ixon-v4/src-diag/diag", 11, [])]

/-- Assert a closure's line of `zetaTable`; the number accepted. -/
def expectCorr (a : Assert) (label : String) (i : Input) : IO Nat := do
  let some (_, n, bad) := zetaTable.find? (·.1 == label) | return 0
  let (ok, bad') := corrOf i
  expect a (ok == n && bad'.length == bad.length && bad.all bad'.contains)
    s!"zeta: {label}: corrSB accepts {ok} (expected {n}), refuses {bad'} (expected {bad})"
  return ok

/-- The false conjuncts of the eleven closures of `zetaTable` the check still refuses. -/
def refusedTable : List (String × List String) :=
  [("bench-k1/sum-loop", ["eqnShape"]), ("bench-k1/collatz", ["eqnShape"]),
   ("bench-k1/prime-count", ["eqnShape"]), ("phase1-scalar/scalar", ["eqnShape"]),
   ("phase1-resource/resource", ["caseRec", "eqnShape", "caseShape"]),
   ("phase1-decline/loops", ["eqnShape"]),
   ("phase1-decline/strings", ["noWord", "caseRec", "proj", "valueCorr", "caseShape", "caseProg"]),
   ("phase1-decline/panic", ["noWord", "proj", "valueCorr"]),
   ("phase2-closures/closures", ["caseRec", "eqnCorr", "valueCorr", "caseShape"]),
   ("phase2-arity/arity", ["valueCorr"]),
   ("fixtures/ixon-v4/src-diag/diag",
     ["declOk", "recShape", "notOpaque", "proj", "caseShape", "caseProg"])]

def familyFiles : List String :=
  ["fixtures/ixon-v4/bench-k1/corpus.json", "fixtures/corpus/phase1-scalar/corpus.json",
   "fixtures/corpus/phase1-resource/corpus.json", "fixtures/corpus/phase1-decline/corpus.json",
   "fixtures/corpus/phase2-closures/corpus.json", "fixtures/corpus/phase2-arity/corpus.json"]

/-- The eleven refused closures, with their non-declined roots (`diag`: all). -/
def jobs : IO (List (String × String × List String)) := do
  let mut out := []
  for f in familyFiles do
    let fam ← IxCCTests.Corpus.Family.read f
    for fx in fam.fixtures do
      let label := s!"{fam.family}/{fx.name}"
      if !(refusedTable.any (·.1 == label)) then continue
      let roots := fx.roots.filter (·.decline.isNone) |>.map (·.name)
      let roots := if roots.isEmpty then fx.roots.map (·.name) else roots
      out := out ++ [(label, s!"{fam.directory}/{fx.closure.path.replace ".ixe" ""}", roots)]
  let d := "fixtures/ixon-v4/src-diag/diag"
  return out ++ [(d, d, [])]

/-- The root's value made `w` in the program (the stored value `val` in the reading). -/
def setRoot (i : Input) (w : Term) (val? : Option KExpr := none) : Option Input := do
  let some (.defn k s lv ty _) := i.src.decl? i.rootId | none
  let env := match val? with
    | some val => mapConst i.env (i.κ i.rootId) fun
        | .defnInfo cv _ h => .defnInfo cv val h
        | ci => ci
    | none => i.env
  some { i with src := i.src.setDecl i.rootId (.defn k s lv ty w), env }

/-- SrcEval on `fib`'s root at `10`, read back. -/
def fibOut (i : Input) : Option IxCC.Sem.Obs :=
  match IxCC.Src.run i.src 100000 i.rootId [.lit 10] with
  | .ok v => IxCC.Src.readbackAll i.src v
  | _ => none

def run : IO Bool := do
  let a : Assert ← IO.mkRef 0
  try
    let js ← jobs
    expect a (js.length == 11) s!"zeta: {js.length} refused closures found, expected 11"
    let mut total := 0
    for (label, stem, roots) in js do
      let (i, _) ← loadClosure label stem roots
      total := total + (← expectCorr a label i)
      let f := failing i
      let some (_, exp) := refusedTable.find? (·.1 == label) | throw (IO.userError label)
      expect a (f == exp) s!"zeta: {label}: false conjuncts {f}, expected {exp}"
    expect a (total == 53)
      s!"zeta: corrSB accepts {total} constants of the eleven refused closures, expected 53"
    IO.println s!"zeta: corrSB [] accepts {total} of the constants the let-free check refuses in \
      the eleven closures still refused (the other 8 of 61 in fields254, machines, natural); \
      refused: strings c262, panic c363 c322 (string literals), closures c272 c19, arity c597 \
      (deep lets); the eleven closures' false conjuncts as expected"
    -- planted, on `fib`'s root
    let some fs := subjects.head? | throw (IO.userError "no subject")
    let (fi, _) ← load fs
    let some (.defn _ _ _ _ v) := fi.src.decl? fi.rootId | throw (IO.userError "fib: no root value")
    let some (.defnInfo _ val _) := fi.env.find? (fi.κ fi.rootId)
      | throw (IO.userError "fib: no stored root value")
    let lt (x b : Term) : Term := .letE default default (.sort .zero) x b
    let liftV := IxCC.Src.Relevance.Check.Canonical.liftTerm 1 0 v
    let some live := setRoot fi (lt v (.var 0)) | throw (IO.userError "fib: live")
    let some dead := setRoot fi (lt (.natLit 99) liftV) | throw (IO.userError "fib: dead")
    let some wrong := setRoot fi (lt (.natLit 7) (.var 0)) | throw (IO.userError "fib: wrong")
    let some deep := setRoot fi (lt v (.lam default (.sort .zero) (.var 1)))
        (some (.lam (.sort .zero) val bmN)) | throw (IO.userError "fib: deep")
    expect a ((failing live).isEmpty && fibOut live == some (.nat 55))
      s!"zeta: fib, a live let around the root's value: false conjuncts {failing live}, read back {repr (fibOut live)}"
    expect a ((failing dead).isEmpty && fibOut dead == some (.nat 55))
      s!"zeta: fib, a dead let before the root's value: false conjuncts {failing dead}, read back {repr (fibOut dead)}"
    expect a (failing wrong == ["valueCorr"])
      s!"zeta: fib, a live let whose value is not its copy: false conjuncts {failing wrong}"
    let deepRun := (runPairsB deep.src deep.env deep.κ deep.rootId).all fun (t, e) => deepLet t e
    expect a (failing deep == ["valueCorr"] && deepRun)
      s!"zeta: fib, a let used only under a λ: false conjuncts {failing deep}, deep {deepRun}"
    IO.println "zeta: fib: a live let around the root's value and a dead one before it: every \
      conjunct true, SrcEval reads back 55; the live let's value not its copy: valueCorr alone \
      false; a let used only under a λ: valueCorr alone false (deep)"
    IO.println s!"tests-grounding (zeta): {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: grounding (zeta): {error}"
    return false

end IxCCTests.Grounding.Zeta
