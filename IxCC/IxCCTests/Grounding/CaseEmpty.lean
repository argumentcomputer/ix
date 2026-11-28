import IxCCTests.Grounding.GradedHead

/-! # `tests-grounding`: step E0, a `case` entry whose recursor is of kind `empty`

SrcEval traps at a `case` head whose recursor is of kind `empty` (`Src/Semantics.lean`, F4 at
`.cases`), so the fundamental lemma never asks F5 there and the check reads no shape there:
`caseRec` admits the kind beside `ordinary` (with the arity condition), `caseShape` and `caseProg`
are true at such an entry, and `CaseFacts`, `CaseFactsRead` and `FundHyps.cases` are asked only at
entries of kind `ordinary`.

On `phase1-resource/resource` (the one corpus closure with such an entry, `Empty.casesOn` under
`Resource.trapEmpty`): the entry is the only one of kind `empty`, its recursor stores no rule, and
the three conjuncts hold at it; the check's false conjuncts are `eqnShape` alone on the reading
and none on `selEnv`; at the root `Resource.trapEmpty` every hypothesis of
`rootSound_678AGp_of_check` that is decided holds (the check, `noCanonAB`, `litDefsB` on `selEnv`,
`instCheckB` with the root as the seed, `headRegimeSB`), and SrcEval traps on the manifest's two
arguments, so the theorem says nothing of those runs: it speaks of a run that returns a value.
Controls on the same entry, each refused: its recursor's kind made `ordinary` (then the shape is
read, and `caseShape` refuses a family without constructors), made `subsingleton` (`caseRec`
refuses it, and the shape is read), and the stored `casesOn` given a type with fewer binders than
the head takes (`caseRec`, at the arity). -/

namespace IxCCTests.Grounding.CaseEmpty

open IxCC IxCC.Grounding IxCCTests.Grounding
open IxCC.Src (Term CId Value)
open IxCCTests.Src (Assert expect)

/-- The `case` entries of `Sl` whose recursor is of kind `empty`, with the recursor. -/
def emptyCases (i : Input) : List (CId × CId) :=
  i.Sl.filterMap fun c => match i.src.table.resolveOf c with
    | some (.case r) => if i.src.table.recKindOf r == some .empty then some (c, r) else none
    | _ => none

/-- The table's kind of recursor `r` made `k`. -/
def setKind (i : Input) (r : CId) (k : IxCC.Src.RecKind) : Input :=
  { i with src := { i.src with table := { i.src.table with
      recKind := i.src.table.recKind.insert r k } } }

/-- The stored constant `c` given the type `Sort 0` (no binder). -/
def cutType (i : Input) (c : CId) : Input :=
  { i with env := mapConst i.env (i.κ c) fun
      | .defnInfo cv v h => .defnInfo { cv with type := .sort .zero } v h
      | ci => ci }

/-- The constants SrcEval may reach from `seeds` (as the loaders compute `Sl`). -/
def reach (i : Input) (seeds : List CId) : List CId := Id.run do
  let mut sl := seeds
  let mut todo := seeds
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    for t in runTerms i.src c do
      for d in constsOf t do
        if !sl.contains d then
          sl := sl ++ [d]
          todo := todo ++ [d]
  return sl

/-- The false conjuncts of the check on `selEnv`. -/
def failingSel (i : Input) : List String :=
  failing { i with env := selEnv i.src i.env i.κ i.Sl }

def run : IO Bool := do
  let a : Assert ← IO.mkRef 0
  try
    let all ← GradedHead.allJobs
    let some (label, stem, roots) := all.find? (·.1 == "phase1-resource/resource")
      | throw (IO.userError "no resource closure")
    let (i, _) ← loadClosure label stem roots
    let es := emptyCases i
    expect a (es.length == 1) s!"caseEmpty: entries of kind empty {es}, expected one"
    let some (c, r) := es.head? | throw (IO.userError "no entry of kind empty")
    let noRule := match i.env.find? (i.κ r) with
      | some (.recInfo _ _ _ rules) => rules.isEmpty
      | _ => false
    expect a noRule s!"caseEmpty: c{c}'s recursor c{r} stores a rule"
    expect a (caseRecB i.src i.env i.κ c && caseShapeB i.src i.env i.κ c &&
        caseProgOkB i.src i.env i.κ i.Sl c)
      s!"caseEmpty: caseRec, caseShape, caseProg at c{c}: {caseRecB i.src i.env i.κ c}, \
        {caseShapeB i.src i.env i.κ c}, {caseProgOkB i.src i.env i.κ i.Sl c}"
    let f := failing i
    let fs := failingSel i
    expect a (f == ["eqnShape"] && fs.isEmpty)
      s!"caseEmpty: false conjuncts {f} on the reading (expected [eqnShape]), {fs} on selEnv (expected [])"
    -- the root whose closure holds the entry
    let rs := (i.src.roots.map (·.2)).filter fun rt => (reach i [rt]).contains c
    expect a (rs.length == 1) s!"caseEmpty: roots reaching c{c}: {rs}, expected one"
    let some rt := rs.head? | throw (IO.userError "no root reaches the entry")
    let pins := [i.src.known.boolTrue, i.src.known.boolFalse].filterMap id
    let sl := reach i (rt :: pins.filter (· != rt))
    let ir : Input := { i with Sl := sl, rootId := rt }
    let env' := selEnv i.src i.env i.κ sl
    let jr : Input := { ir with env := env' }
    let inst := match instWalk i.src [rt] 1000000 with
      | some Inst => instCheckB i.src env' i.κ i.lpsOf [rt] Inst
      | none => false
    let fam := (failing jr).isEmpty && noCanonAB i.src env' i.κ sl && litDefsB env' && inst &&
      GradedHead.sB jr
    expect a fam s!"caseEmpty: the decided hypotheses of rootSound_678AGp_of_check at c{rt}: \
      false conjuncts {failing jr}, noCanonAB {noCanonAB i.src env' i.κ sl}, litDefsB \
      {litDefsB env'}, instCheckB {inst}, headRegimeSB {GradedHead.sB jr}"
    let outs := [0, 7].map fun n => match IxCC.Src.run i.src 100000 rt [.lit n] with
      | .trap => "trap"
      | .ok _ => "ok"
      | .stuck => "stuck"
      | .timeout => "timeout"
      | .resource _ => "resource"
    expect a (outs == ["trap", "trap"]) s!"caseEmpty: SrcEval at c{rt} on 0 and 7: {outs}"
    -- controls
    let fOrd := failingSel (setKind i r .ordinary)
    expect a (fOrd == ["caseShape"])
      s!"caseEmpty: kind ordinary at c{r}: false conjuncts {fOrd}, expected [caseShape]"
    let fSub := failingSel (setKind i r (.subsingleton (.allZero []) []))
    expect a (fSub == ["caseRec", "caseShape"])
      s!"caseEmpty: kind subsingleton at c{r}: false conjuncts {fSub}, expected [caseRec, caseShape]"
    let fCut := failingSel (cutType i c)
    expect a (fCut == ["caseRec"])
      s!"caseEmpty: c{c} stored with type Sort 0: false conjuncts {fCut}, expected [caseRec]"
    IO.println s!"caseEmpty: on {label} the one case entry of kind empty (c{c}, recursor c{r}, no \
      rule) passes caseRec, caseShape, caseProg; false conjuncts {f} on the reading, none on \
      selEnv; at the root c{rt} every decided hypothesis of rootSound_678AGp_of_check holds and \
      SrcEval traps on 0 and 7; controls refused: kind ordinary {fOrd}, kind subsingleton {fSub}, \
      casesOn's type cut {fCut}"
    IO.println s!"tests-grounding (caseEmpty): {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: grounding (caseEmpty): {error}"
    return false

end IxCCTests.Grounding.CaseEmpty
