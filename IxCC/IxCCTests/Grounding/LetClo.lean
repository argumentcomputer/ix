import IxCCTests.Grounding.CaseEmpty
import IxCCTests.Grounding.Zeta

/-! # `tests-grounding`: step C's closure-capture shape of a deep `let`

A `let` whose body is a λ and whose copy (in the `let`'s context) occurs, lifted past the λ, in the
λ's body with no binder between (`λa. let k := a * a; λb. k + b`): SrcEval evaluates the value at
the `let` and returns a closure; the closure's environment is related at every member of the λ's
domain (`RelV.clo`), where the value runs against the lifted copy (`Runs.letClo`). The check's
correspondence accepts the shape after the live case fails (`TermCorrS.letClo`, `corrSB`), and the
typing routes list the value's sites in the λ's context (`evalSites`, `evalSitesP`, 1a, 1b).

* **`phase2-arity/arity`**: exactly one constant, `Arity.main11`, is accepted by the closure case
  and refused by the live case alone (`Zeta.corrSBLive`); every conjunct of the check holds on the
  closure, and 1a's and 1b's decisions (`headRegimeResB`, `headRegimeSB`) with it; at the root every
  decided hypothesis of `rootSound_678AGp_of_check` holds, and SrcEval reads back `13` on the
  manifest's case `(3, 4)`.
* **`phase2-closures/closures`**: exactly one constant (under `Closures.storedApply`) is accepted by
  the closure case; exactly one constant's run pair is still refused (`Closures.coreKnot`, the
  minor-premise shape); the check's false conjuncts are `caseRec`, `eqnCorr`, `caseShape`; at
  `storedApply` every decided hypothesis of `rootSound_678AGp_of_check` holds and SrcEval reads back
  the manifest's four values.

The controls (a copy under a second binder, a body that is not a λ, a copy that is not the value,
each refused at `valueCorr` alone; the plant of the shape itself accepted) are in
`IxCCTests.Grounding.Zeta`. -/

namespace IxCCTests.Grounding.LetClo

open IxCC IxCC.Grounding IxCCTests.Grounding
open IxCC.Src (Term CId Value)
open IxCCTests.Src (Assert expect)

/-- The constants of `Sl` with a run pair the check's decider accepts and the live case alone
refuses. -/
def cloConsts (i : Input) : List CId :=
  i.Sl.filter fun c => (runPairsB i.src i.env i.κ c).any fun (t, e) =>
    corrSB i.κ (i.lpsOf c) [] t e && !Zeta.corrSBLive i.κ (i.lpsOf c) [] t e

/-- The constants of `Sl` with a run pair the check's decider refuses. -/
def refusedConsts (i : Input) : List CId :=
  i.Sl.filter fun c => (runPairsB i.src i.env i.κ c).any fun (t, e) =>
    !corrSB i.κ (i.lpsOf c) [] t e

/-- The roots whose closure holds `c`. -/
def rootsReaching (i : Input) (c : CId) : List CId :=
  (i.src.roots.map (·.2)).filter fun rt => (CaseEmpty.reach i [rt]).contains c

/-- The decided hypotheses of `rootSound_678AGp_of_check` at the root `rt` (its own `Sl`, the root
as `instCheckB`'s seed). -/
def familyAt (i : Input) (rt : CId) : Bool :=
  let pins := [i.src.known.boolTrue, i.src.known.boolFalse].filterMap id
  let sl := CaseEmpty.reach i (rt :: pins.filter (· != rt))
  let env' := selEnv i.src i.env i.κ sl
  let jr : Input := { i with Sl := sl, rootId := rt, env := env' }
  let inst := match instWalk i.src [rt] 1000000 with
    | some Inst => instCheckB i.src env' i.κ i.lpsOf [rt] Inst
    | none => false
  (failing jr).isEmpty && noCanonAB i.src env' i.κ sl && litDefsB env' && inst && GradedHead.sB jr

/-- SrcEval at `rt` on literal arguments, read back. -/
def readAt (i : Input) (rt : CId) (args : List Nat) : Option IxCC.Sem.Obs :=
  match IxCC.Src.run i.src 100000 rt (args.map .lit) with
  | .ok v => IxCC.Src.readbackAll i.src v
  | _ => none

def run : IO Bool := do
  let a : Assert ← IO.mkRef 0
  try
    let all ← GradedHead.allJobs
    -- `arity`
    let some (la, sa, ra) := all.find? (·.1 == "phase2-arity/arity")
      | throw (IO.userError "no arity closure")
    let (ia, _) ← loadClosure la sa ra
    let ca := cloConsts ia
    expect a (ca.length == 1) s!"letClo: arity: accepted by the closure case alone {ca}, expected one"
    let some c1 := ca.head? | throw (IO.userError "arity: no closure-capture constant")
    let fa := failing ia
    let r1a := headRegimeResB ia.src ia.env ia.κ ia.lpsOf ia.ann ia.Sl
    let r1b := GradedHead.sB ia
    expect a (fa.isEmpty && r1a && r1b)
      s!"letClo: arity: false conjuncts {fa}, headRegimeResB {r1a}, headRegimeSB {r1b}"
    let rs := rootsReaching ia c1
    expect a (rs == [c1]) s!"letClo: arity: roots reaching c{c1}: {rs}, expected the constant itself"
    expect a (familyAt ia c1) s!"letClo: arity: a decided hypothesis of the widest family fails at c{c1}"
    let o1 := readAt ia c1 [3, 4]
    expect a (o1 == some (.nat 13)) s!"letClo: arity: SrcEval at c{c1} on 3 4 reads back {repr o1}"
    -- `closures`
    let some (lc, sc, rc) := all.find? (·.1 == "phase2-closures/closures")
      | throw (IO.userError "no closures closure")
    let (ic, _) ← loadClosure lc sc rc
    let cc := cloConsts ic
    expect a (cc.length == 1)
      s!"letClo: closures: accepted by the closure case alone {cc}, expected one"
    let some c2 := cc.head? | throw (IO.userError "closures: no closure-capture constant")
    let rc' := refusedConsts ic
    expect a (rc'.length == 1) s!"letClo: closures: run pairs still refused at {rc'}, expected one"
    let fc := failing ic
    expect a (fc == ["caseRec", "eqnCorr", "caseShape"])
      s!"letClo: closures: false conjuncts {fc}, expected [caseRec, eqnCorr, caseShape]"
    let rs2 := rootsReaching ic c2
    expect a (rs2.length == 1) s!"letClo: closures: roots reaching c{c2}: {rs2}, expected one"
    let some rt := rs2.head? | throw (IO.userError "closures: no root")
    expect a (familyAt ic rt)
      s!"letClo: closures: a decided hypothesis of the widest family fails at c{rt}"
    let outs := [([0, 3], 1), ([1, 3], 4), ([4, 2], 142), ([8, 5], 107)].map fun (xs, n) =>
      (readAt ic rt xs, n)
    expect a (outs.all fun (o, n) => o == some (.nat n))
      s!"letClo: closures: SrcEval at c{rt} reads back {outs.map fun (o, _) => repr o}"
    IO.println s!"letClo: arity: c{c1} accepted by the closure case alone, every conjunct and 1a's \
      and 1b's decisions true, every decided hypothesis of rootSound_678AGp_of_check at the root, \
      SrcEval 13 on (3, 4); closures: c{c2} accepted by the closure case alone, c{rc'} still \
      refused (the minor-premise shape), false conjuncts {fc}, at c{rt} every decided hypothesis \
      and SrcEval's four values"
    IO.println s!"tests-grounding (letClo): {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: grounding (letClo): {error}"
    return false

end IxCCTests.Grounding.LetClo
