import IxCCTests.Grounding.NoCanon
import IxCCGrounding.SelRetype

/-! # `tests-grounding`: step 1b, every run-term site typed from `graded`, and step Ap

`headRegimeSB` (`IxCCGrounding.GradedHead`, the per-spine decision the root theorem
`rootSound_678AG_of_check` reads) on every committed closure the grounding measurements load (the
ten corpus families, 36 closures, and the fifteen extra ones: 51):

* true on the 37 closures the check accepts, by name (since step C: `fields254`, `machines`,
  `natural` added), so the family without a typing hypothesis holds on all 37: on `natural`,
  `headRegimeResB` (1a) is false (74 site-profile instances under its `let`s whose heads it reads as
  written) and `headRegimeSB` true;
* false on exactly `phase2-closures/closures` (a bound-variable head whose context type is a
  definition applied to more arguments than its value has λs) and `src-diag/diag` (projection
  heads), both refused by the check as well;
* equal to the per-site reading `headRegimeGB` on every closure (and on every planted control);
* on the accepted closures, the sites 1a's reading as written (`headRegimeB`: constant heads only,
  the stored type not unfolded) refuses at some `Ok` profile: 436 on the 37, of which 322 on the
  34 accepted before step C, all decided here (GR14's "70 sites" were by his
  probe's reading, a bound-variable head's context type read as written);
* on `OS02-plain`, the one site the direct route refuses is decided.

Planted controls, each refused on every closure where it applies: the one definition unfolded at
sites (`#7e081ef3d58e`, `DecidableEq`-like) with its first `∀` datum made a proposition everywhere
(`ifAllZero []`), its unfolding made endless (`λ x. D x`: fuel, fail closed), its first λ datum made
a proposition everywhere (3 plants on each of the 25 closures with a δ site: 75); and a constant
with a bound-variable head whose context type is a `∀`, its λ domains' `∀` data made propositions
everywhere (32 closures).

Step Ap (`IxCCGrounding.SelRetype`), in the same pass over the 51: `selEnv` retypes exactly the
`for`-loop function of the six `for`-loop closures and moves only their `eqnShape` conjunct (false
to true), nothing on the other 45; on each of the six, three planted controls are refused by
`eqnShape` on `selEnv` (the selector's value made `λ α s. α → α`, its first λ's datum made a
proposition, the selected argument made `Nat`); the family over six fields read on `selEnv`
(`groundCheck`, `noCanonAB`, `litDefsB`, `instCheckB`, `headRegimeSB`) holds on 44: the 37 the check
accepted when step Ap landed, the six (`resource` since step E0, which admits its `Empty.casesOn`
entry, of kind `empty`: `IxCCTests.Grounding.CaseEmpty`) and `arity` (since step C's closure-capture
case: `IxCCTests.Grounding.LetClo`).

The word subject `grounding/words` (fixed-width word arithmetic only, stage W1: 30 word entries) is
refused by that family by `noWord` alone: on `selEnv` every other conjunct of `groundCheck` and
every other part is true, also with the word entries' runtime references (the tower's six
constructors, which no run term names) added to its closure. -/

namespace IxCCTests.Grounding.GradedHead

open IxCC IxCC.Grounding IxCCTests.Grounding
open Ix.Kernel (Level BinderMeta PropWhen Expr ConstantInfo LevelParam ConstantVal)
open IxCC.Src (Term CId Levels)
open IxCCTests.Src (Assert expect)

/-- The ten corpus families of the grounding measurements. -/
def familyFiles : List String :=
  ["fixtures/ixon-v4/bench-k1/corpus.json", "fixtures/corpus/grounding/corpus.json",
   "fixtures/corpus/phase1-scalar/corpus.json", "fixtures/corpus/phase1-boundary/corpus.json",
   "fixtures/corpus/phase1-resource/corpus.json", "fixtures/corpus/phase1-decline/corpus.json",
   "fixtures/corpus/phase1-abi/corpus.json", "fixtures/corpus/phase2-closures/corpus.json",
   "fixtures/corpus/phase1-machines/corpus.json", "fixtures/corpus/phase2-arity/corpus.json"]

/-- The fourteen ownership closures (as `NoCanon` labels them) and `diag`. -/
def extra : List (String × String) :=
  (NoCanon.acceptedExtra.map fun n => (n, s!"fixtures/ownership/{n}")) ++
    [("diag", "fixtures/ixon-v4/src-diag/diag")]

/-- Every closure: label, stem, roots (the family closures with their non-declined roots, all when
every root declines; the extra ones with all roots). -/
def allJobs : IO (List (String × String × List String)) := do
  let mut out := []
  for f in familyFiles do
    let fam ← IxCCTests.Corpus.Family.read f
    for fx in fam.fixtures do
      let roots := fx.roots.filter (·.decline.isNone) |>.map (·.name)
      let roots := if roots.isEmpty then fx.roots.map (·.name) else roots
      out := out ++ [(s!"{fam.family}/{fx.name}",
        s!"{fam.directory}/{fx.closure.path.replace ".ixe" ""}", roots)]
  return out ++ extra.map fun (l, s) => (l, s, [])

def accepted : List String := NoCanon.acceptedFamily ++ NoCanon.acceptedExtra

/-- The two closures the per-spine decision refuses. -/
def refused : List String := ["phase2-closures/closures", "diag"]

/-- The sites 1a's reading as written refuses on the accepted closures, at some `Ok` profile (322 on
the 34 accepted before step C, whose run terms hold no `let`; since C, 436 on the 37: those 322 and
114 on `fields254`, `machines` and `natural`, sites under their `let`s among them). -/
def gapExpected : Nat := 436

/-- The closures with a site whose head type unfolds a definition (three δ plants each). -/
def deltaClosuresExpected : Nat := 25

/-- The closures with a bound-variable head of a `∀` context type (one plant each). -/
def bvExpected : Nat := 32

/-- In a type's binder domains, the selector `D`'s first argument (the one `autoParam` and
`optParam` select) replaced by `Nat`. -/
def swapSelArg (D : KKey) (T : KExpr) : KExpr :=
  let swap : KExpr → KExpr := fun f =>
    match f.getAppFn with
    | .const D' vs =>
      if D' == D then Expr.mkAppN (.const D' vs) (f.getAppArgs.set 0 (.const Ix.Kernel.natName []))
      else f
    | _ => f
  piTele ((splitAll T).1.map fun p => (swap p.1, p.2)) (splitAll T).2

/-- The six closures whose `for`-loop function (`Std.Legacy.Range.forIn'.loop`) has an `autoParam`
binder where its equation theorem binds the bare proposition (step Ap). -/
def forLoops : List String :=
  ["bench-k1/sum-loop", "bench-k1/collatz", "bench-k1/prime-count", "phase1-scalar/scalar",
   "phase1-resource/resource", "phase1-decline/loops"]

/-- The three closures step C added to the accepted ones. -/
def addedByC : List String :=
  ["phase1-boundary/fields254", "phase1-machines/machines", "phase1-machines/natural"]

/-- The three corpus fixtures refused before the check (the annotation of
`typeFormerPolymorphism`; the decoder's consumer budget at `fields255` and `tags126`): not
loaded, so not counted among the 51. -/
def notLoaded : List String :=
  ["phase1-scalar/typeFormerPolymorphism", "phase1-boundary/fields255", "phase1-boundary/tags126"]

def sB (i : Input) : Bool := headRegimeSB i.src i.env i.κ i.lpsOf i.ann i.Sl
def gB (i : Input) : Bool := headRegimeGB i.src i.env i.κ i.lpsOf i.ann i.Sl

/-- The word subject (fixed-width word arithmetic, stage W1; `fixtures/corpus/grounding/words`). -/
def wordsLabel : String := "grounding/words"

/-- `Sl` with each word entry's runtime references (`Program.runtimeRefs`: the tower's
constructors, which no run term names) added. -/
def wordClosure (i : Input) : List CId :=
  let refs := (i.Sl.flatMap fun c => match i.src.table.resolveOf c with
    | some (.word ..) => (i.src.runtimeRefs c).map (·.1)
    | _ => []).eraseDups
  i.Sl ++ refs.filter (!i.Sl.contains ·)

/-- The sites 1a's reading as written refuses at some `Ok` profile (constants within
`maxDirectParams` level parameters, at their `Ok` profiles). -/
def gap1a (i : Input) : Nat := Id.run do
  let tab := KTab.of i.env
  let mut n := 0
  for c in i.Sl do
    if lvlsOf i.src c > maxDirectParams then continue
    for x in runPairsB i.src i.env i.κ c do
      for sP in evalSitesPs (okProfiles i.src i.ann c) [] x.1 x.2 do
        if !sP.2.all (headRegimeB tab (i.lpsOf c) · sP.1.2.1) then n := n + 1
  return n

/-- The definitions a site's head type unfolds (δ) within `n` binders. -/
def deltaHeads (tab : KTab) : Nat → Nat → KExpr → List KKey
  | _, 0, _ => []
  | f, n + 1, .forallE _ b _ => deltaHeads tab f n b
  | 0, _, _ => []
  | f + 1, n + 1, T =>
    match T.getAppFn with
    | .const D _ =>
      match tab[D]? with
      | some (.defnInfo _ val _) =>
        match lamPeel T.getAppArgs.length val with
        | some (_, body) => D :: deltaHeads tab f (n + 1) body
        | none => []
      | _ => []
    | _ => []
termination_by f n => (f, n)

/-- The definitions a closure's sites unfold. -/
def unfolded (i : Input) : List KKey := Id.run do
  let tab := KTab.of i.env
  let mut out : List KKey := []
  for c in i.Sl do
    for x in runPairsB i.src i.env i.κ c do
      for sP in evalSitesPs (okProfiles i.src i.ann c) [] x.1 x.2 do
        let f := sP.1.2.1
        match f.getAppFn with
        | .const k _ =>
          match tab[k]? with
          | some ci =>
            for D in deltaHeads tab headFuel (f.getAppArgs.length + 1) ci.toConstantVal.type do
              if !out.contains D then out := out ++ [D]
          | none => pure ()
        | _ => pure ()
  return out

/-- The first `∀` after the leading λs, its datum replaced. -/
def setFirstPi (pw : PropWhen) : KExpr → KExpr
  | .lam d b m => .lam d (setFirstPi pw b) m
  | .forallE d b m => .forallE d b { m with pw }
  | e => e

/-- Every `∀` datum, everywhere in a term, replaced. -/
def setPis (pw : PropWhen) : KExpr → KExpr
  | .forallE d b m => .forallE (setPis pw d) (setPis pw b) { m with pw }
  | .app f a => .app (setPis pw f) (setPis pw a)
  | .lam d b m => .lam (setPis pw d) (setPis pw b) m
  | e => e

/-- Every λ domain's `∀` data replaced. -/
def setLamDoms (pw : PropWhen) : KExpr → KExpr
  | .lam d b m => .lam (setPis pw d) (setLamDoms pw b) m
  | .app f a => .app (setLamDoms pw f) (setLamDoms pw a)
  | e => e

/-- `λ x₁ … xₖ. D.{ps} x₁ … xₖ`: a value whose unfolding never ends. -/
def selfLoop (D : KKey) (cv : ConstantVal .anon) (v : KExpr) : KExpr :=
  go 0 v
where
  go : Nat → KExpr → KExpr
    | k, .lam d b m => .lam d (go (k + 1) b) m
    | k, _ => Expr.mkAppN (.const D (cv.levelParams.map Level.param)) (bvarsFrom 0 k)

/-- A constant of `Sl` with a site whose head is a bound variable of a `∀` context type. -/
def bvarHeadConst (i : Input) : Option CId :=
  i.Sl.find? fun c => (runPairsB i.src i.env i.κ c).any fun x =>
    (evalSitesPs (okProfiles i.src i.ann c) [] x.1 x.2).any fun sP =>
      match sP.1.2.1.getAppFn with
      | .bvar j => (match sP.1.1[j]? with | some (.forallE ..) => true | _ => false)
      | _ => false

def run : IO Bool := do
  let a : Assert ← IO.mkRef 0
  try
    let js0 ← allJobs
    for (label, stem, roots) in js0.filter (notLoaded.contains ·.1) do
      let r ← try
          let _ ← loadClosure label stem roots
          pure true
        catch _ => pure false
      expect a (!r) s!"graded1b: {label} loads; it was refused before the check"
    let js := js0.filter (!notLoaded.contains ·.1)
    expect a (js.length == 51) s!"graded1b: {js.length} closures found, expected 51"
    let mut nAcc := 0
    let mut sFalse : List String := []
    let mut gap := 0
    let mut gap34 := 0
    let mut nDelta := 0
    let mut nDeltaClosures := 0
    let mut nBv := 0
    let mut tS := 0
    let mut tG := 0
    let mut lines : List String := []
    let mut natRes : Option Bool := none
    let mut natS : Option Bool := none
    let mut nAp := 0
    let mut nApPlants := 0
    let mut famAGp : List String := []
    let mut nWords := 0
    for (label, stem, roots) in js do
      let (i, _) ← loadClosure label stem roots
      let t0 ← IO.monoNanosNow
      let s ← IO.lazyPure fun _ => sB i
      let t1 ← IO.monoNanosNow
      let g ← IO.lazyPure fun _ => gB i
      let t2 ← IO.monoNanosNow
      tS := tS + (t1 - t0)
      tG := tG + (t2 - t1)
      expect a (s == g) s!"graded1b: {label}: per-spine {s}, per-site {g}"
      if accepted.contains label then
        expect a s s!"graded1b: {label}: accepted by the check, headRegimeSB false"
        nAcc := nAcc + 1
        let ng := gap1a i
        gap := gap + ng
        if !addedByC.contains label then gap34 := gap34 + ng
      else if !s then sFalse := sFalse ++ [label]
      if ["phase1-boundary/tags125", "phase1-boundary/fields254", "phase1-scalar/bigctor",
          "bench-k1/sum-loop"].contains label then
        lines := lines ++ [s!"{label} {(t1 - t0) / 1000} µs per spine, {(t2 - t1) / 1000} µs per site"]
      -- the δ plants: each definition unfolded at sites (the first two)
      let Ds := unfolded i
      if !Ds.isEmpty then nDeltaClosures := nDeltaClosures + 1
      for D in Ds.take 2 do
        let e1 := mapConst i.env D fun
          | .defnInfo cv v h => .defnInfo cv (setFirstPi (.ifAllZero []) v) h
          | ci => ci
        let e2 := mapConst i.env D fun
          | .defnInfo cv v h => .defnInfo cv (selfLoop D cv v) h
          | ci => ci
        let e3 := mapConst i.env D fun
          | .defnInfo cv (.lam d b m) h => .defnInfo cv (.lam d b { m with pw := .ifAllZero [] }) h
          | ci => ci
        for (nm, e) in [("first ∀ datum a proposition", e1), ("endless unfolding", e2),
            ("first λ datum a proposition", e3)] do
          let j := { i with env := e }
          let (bs, bg) := (sB j, gB j)
          expect a (!bs && !bg) s!"graded1b: {label}: δ plant ({nm}): per-spine {bs}, per-site {bg}"
          nDelta := nDelta + 1
      -- the bound-variable plant
      match bvarHeadConst i with
      | some c =>
        let e4 := mapConst i.env (i.κ c) fun
          | .defnInfo cv v h => .defnInfo cv (setLamDoms (.ifAllZero []) v) h
          | ci => ci
        let j := { i with env := e4 }
        let (bs, bg) := (sB j, gB j)
        expect a (!bs && !bg)
          s!"graded1b: {label}: c{c}'s λ domains' ∀ data made propositions: per-spine {bs}, per-site {bg}"
        nBv := nBv + 1
      | none => pure ()
      -- Ap: the check on `selEnv` retypes exactly the `for`-loop function of the six closures and
      -- moves nothing but its `eqnShape`; the family over six fields on `selEnv`
      let env' := selEnv i.src i.env i.κ i.Sl
      let retyped := (i.env.consts.zip env'.consts).filter fun (x, y) =>
        x.toConstantVal.type != y.toConstantVal.type
      let parts := checkParts i.src i.env i.κ i.lpsOf i.ann i.Sl
      let parts' := checkParts i.src env' i.κ i.lpsOf i.ann i.Sl
      let moved := (parts.zip parts').filterMap fun (x, y) =>
        if x.2 != y.2 then some (x.1, x.2, y.2) else none
      if forLoops.contains label then
        expect a (retyped.length == 1 && moved == [("eqnShape", false, true)])
          s!"Ap: {label}: {retyped.length} constants retyped, conjuncts moved {moved}"
        nAp := nAp + 1
        -- the selector the retyping read, and the function it retyped
        let some (fx, fy) := retyped.head? | throw (IO.userError s!"Ap: {label}: nothing retyped")
        let sels := ((splitAll fx.toConstantVal.type).1.zip (splitAll fy.toConstantVal.type).1).filterMap
          fun ((d, _), (d', _)) => if d != d' then
            (match d.getAppFn with | .const D _ => some D | _ => none) else none
        let some D := sels.head? | throw (IO.userError s!"Ap: {label}: no selector domain")
        let eqnOn (e : KEnv) : Bool := i.Sl.all (eqnShapeOkB i.src (selEnv i.src e i.κ i.Sl) i.κ)
        -- the selector's value made `λ α s. α → α` (a default that changes the type)
        let ePl1 := mapConst i.env D fun
          | .defnInfo cv _ h => .defnInfo cv (.lam (.sort (.param 0)) (.lam (.sort .zero)
              (.forallE (.bvar 1) (.bvar 2) { pw := .never }) { pw := .never }) { pw := .never }) h
          | ci => ci
        -- its first λ's datum made a proposition everywhere
        let ePl2 := mapConst i.env D fun
          | .defnInfo cv (.lam d b _) h => .defnInfo cv (.lam d b { pw := .ifAllZero [] }) h
          | ci => ci
        -- the selected argument made `Nat` in the function's type
        let ePl3 := mapConst i.env fx.name fun
          | .defnInfo cv v h => .defnInfo { cv with type := swapSelArg D cv.type } v h
          | ci => ci
        let (r1, r2, r3) := (eqnOn ePl1, eqnOn ePl2, eqnOn ePl3)
        expect a (eqnOn i.env && !r1 && !r2 && !r3)
          s!"Ap: {label}: eqnShape on selEnv {eqnOn i.env}; planted: selector value {r1}, selector datum {r2}, selected argument {r3}"
        nApPlants := nApPlants + 3
      else
        expect a (retyped.isEmpty && moved.isEmpty)
          s!"Ap: {label}: {retyped.length} constants retyped, conjuncts moved {moved}"
      let j' := { i with env := env' }
      if (failing j').isEmpty && noCanonAB i.src env' i.κ i.Sl && litDefsB env' && NoCanon.instOk j' &&
          sB j' then
        famAGp := famAGp ++ [label]
      -- the word subject (stage W1): the family over six fields refuses it by `noWord` alone, every
      -- other conjunct and part true on `selEnv`; so also with the word entries' runtime references
      -- (the tower's constructors, which no run term names) added to the closure
      if label == wordsLabel then
        let nW := (i.Sl.filter fun c => match i.src.table.resolveOf c with
          | some (.word ..) => true
          | _ => false).length
        let slP := wordClosure i
        let jP := { i with env := selEnv i.src i.env i.κ slP, Sl := slP }
        let partsOk := fun (j : Input) => failing j == ["noWord"] && noCanonAB j.src j.env j.κ j.Sl &&
          litDefsB j.env && NoCanon.instOk j && sB j
        expect a (nW == 30 && partsOk j' && slP.length == i.Sl.length + 6 && partsOk jP)
          s!"words: {nW} word entries; on selEnv false {failing j'}, noCanonAB \
            {noCanonAB i.src env' i.κ i.Sl}, litDefsB {litDefsB env'}, instOk {NoCanon.instOk j'}, \
            headRegimeSB {sB j'}; with the runtime references {slP.length - i.Sl.length} more \
            constants, false {failing jP}"
        nWords := nWords + 1
      if label == "phase1-machines/natural" then
        natRes := some (headRegimeResB i.src i.env i.κ i.lpsOf i.ann i.Sl)
        natS := some s
      -- `OS02-plain`: the one site the direct route refuses, decided here
      if label == "OS02-plain" then
        expect a ((refusedSites i).length == 1 && s)
          s!"graded1b: OS02-plain: {(refusedSites i).length} sites the direct route refuses, headRegimeSB {s}"
    IO.println s!"graded1b: headRegimeSB true on {nAcc} of the {accepted.length} accepted closures, \
      false on {sFalse}; per-spine and per-site verdicts equal on all 51 and on every plant; 1a's \
      reading as written refuses {gap} sites of the accepted closures, all decided; natural (whose \
      sites under `let`s 1a refuses): headRegimeResB {natRes}, headRegimeSB {natS}; OS02-plain's \
      direct-refused site decided; {nDelta} δ plants ({nDeltaClosures} closures) and {nBv} \
      bound-variable plants refused; all 51: {tS / 1000000} ms per spine, {tG / 1000000} ms per \
      site; {lines}"
    expect a (nAcc == accepted.length && accepted.length == 37)
      s!"graded1b: headRegimeSB true on {nAcc} of {accepted.length} accepted closures, expected 37 of 37"
    expect a (sFalse == refused) s!"graded1b: headRegimeSB false on {sFalse}, expected {refused}"
    expect a (natRes == some false && natS == some true)
      s!"graded1b: natural: headRegimeResB {natRes}, headRegimeSB {natS}"
    expect a (gap34 == 322)
      s!"graded1b: 1a's reading as written refuses {gap34} sites on the 34 accepted before step C, expected 322"
    expect a (gap == gapExpected)
      s!"graded1b: 1a's reading as written refuses {gap} sites on the accepted closures, expected {gapExpected}"
    expect a (nDelta == 3 * deltaClosuresExpected && nDeltaClosures == deltaClosuresExpected)
      s!"graded1b: {nDelta} δ plants on {nDeltaClosures} closures, expected 3 on each of {deltaClosuresExpected}"
    expect a (nBv == bvExpected) s!"graded1b: {nBv} bound-variable plants, expected {bvExpected}"
    IO.println s!"Ap: selEnv retypes the for-loop function of each of the {nAp} for-loop closures and \
      moves only its eqnShape (false to true), nothing on the other {js.length - nAp}; {nApPlants} \
      planted controls refused; the family over six fields on selEnv holds on {famAGp.length}: \
      {famAGp.filter (!accepted.contains ·)} beyond the {accepted.length} the check accepts"
    expect a (nAp == forLoops.length && nApPlants == 3 * forLoops.length)
      s!"Ap: {nAp} for-loop closures retyped, {nApPlants} plants"
    expect a (famAGp.length == 44 && accepted.all famAGp.contains &&
        famAGp.filter (!accepted.contains ·) == forLoops ++ ["phase2-arity/arity"])
      s!"Ap: the family over six fields on selEnv holds on {famAGp}"
    expect a (nWords == 1 && !famAGp.contains wordsLabel) s!"words: {wordsLabel} seen {nWords} times"
    IO.println s!"words: {wordsLabel} (30 word entries) is refused by the family over six fields on \
      selEnv by noWord alone, every other conjunct and part true, also with the tower's constructors \
      (the word entries' runtime references, 6 constants) added to its closure"
    IO.println s!"tests-grounding (graded1b): {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: grounding (graded1b): {error}"
    return false

end IxCCTests.Grounding.GradedHead
