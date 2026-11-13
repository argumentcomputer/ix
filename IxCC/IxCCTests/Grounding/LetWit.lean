import IxCCTests.Grounding.LetClo

/-! # `tests-grounding`: the witness shape (the minor-premise shape of a deep `let`)

A `let` whose copy is not at depth 0 and is not of the closure-capture shape, the copy reached from
the `let`'s kernel term through applications, projections and λs whose domains are closed
level-free constants (a `match`'s minor premises `λ (_ : Unit). … x …`; `λ (_ : Nat). …`): where
each domain has a witness (a stored constant of exactly that type, the conjunct `letWit`), every
environment of the `let`'s context extends to one of the λs' context, where the value runs against
the copy lifted past them (`Runs.letWit`). The check's correspondence accepts the shape after the
live case and the closure-capture case fail (`TermCorrS.letWit`, `corrSB`, `witSite?`), and the
typing routes list the value's sites in the λs' context (`evalSites`, `evalSitesP`, 1a, 1b).

* **The corpus** (the 51 closures the suite loads, asserted in `IxCCTests.Grounding.GradedHead`'s
  pass over them, and `src-words`, here: 52): the conjunct `letWit` holds on every one; no run pair
  the decider as landed with step C accepted (`Zeta.corrSBClo`) is refused; the decider accepts
  more exactly at `closures` c19 (`Closures.coreKnot`) and `src-words` c619, c229, c803, c520
  (`Words.u8` … `Words.u64`), by name (`Zeta.witExpected`).
* **`phase2-closures/closures`**: no run pair is refused; the check's false conjuncts are
  `caseRec` and `caseShape` (`PUnit.casesOn`); at `Closures.knot` every decided hypothesis of
  `rootSound_678AGp_of_check` holds and SrcEval reads back the manifest's five values.
* **`src-words`**: no run pair is refused; the check's false conjunct is `noWord` alone (the word
  case), on the closure and at each of its four roots, where 1b's decision holds.
* **Planted, on `fib`'s root**: `let x := v; (λ (_ : Nat). x) 0` and, at depth 2,
  `let x := v; (λ (_ : Nat) (_ : Nat). x) 0 0` are accepted by the witness case alone, every
  conjunct true, SrcEval still reads back `55`. Refused: a domain that is not a closed constant
  (`Nat → Nat`) and a copy under a `∀`, at `valueCorr` alone; a closed constant domain with no
  stored constant of that type (the root's own key), at `letWit` alone. The live plant, the
  closure-capture plant and the closure-capture plant whose copy is not the value are not seen
  by the witness case (`witSite?` none), so the order of the cases changes nothing accepted or
  refused before.
* **On `src-words`**: the witness of the minor premises' domain (`Unit.unit`) with its stored type
  replaced by the domain's unfolding (`PUnit.{1}`, equal up to δ, not syntactically) is refused at
  `letWit` alone (with `noWord`, false before). -/

namespace IxCCTests.Grounding.LetWit

open IxCC IxCC.Grounding IxCCTests.Grounding
open Ix.Kernel (ConstantInfo)
open IxCC.Src (Term CId Value)
open IxCCTests.Src (Assert expect)

/-- A conjunct of the check, by name. -/
def part (i : Input) (n : String) : Option Bool :=
  (checkParts i.src i.env i.κ i.lpsOf i.ann i.Sl).lookup n

/-- The false conjuncts at the root `rt` (its own `Sl`). -/
def failingAt (i : Input) (rt : CId) : List String :=
  let pins := [i.src.known.boolTrue, i.src.known.boolFalse].filterMap id
  failing { i with Sl := CaseEmpty.reach i (rt :: pins.filter (· != rt)), rootId := rt }

/-- 1b's decision at the root `rt` (its own `Sl`). -/
def sBAt (i : Input) (rt : CId) : Bool :=
  let pins := [i.src.known.boolTrue, i.src.known.boolFalse].filterMap id
  GradedHead.sB { i with Sl := CaseEmpty.reach i (rt :: pins.filter (· != rt)), rootId := rt }

/-- The witness sites of a root's run pair (the `let`s at which `witSite?` fires). -/
def witSitesOf (i : Input) : List (List KExpr × KExpr) :=
  (runPairsB i.src i.env i.κ i.rootId).flatMap fun (t, e) =>
    match t with
    | .letE _ _ _ _ b => (witSite? b e).toList
    | _ => []

/-- A stored constant's type replaced. -/
def setType (T : KExpr) : ConstantInfo .anon → ConstantInfo .anon
  | .defnInfo cv v h => .defnInfo { cv with type := T } v h
  | .ctorInfo cv np nf => .ctorInfo { cv with type := T } np nf
  | ci => ci

def run : IO Bool := do
  let a : Assert ← IO.mkRef 0
  try
    -- the suite's 51 closures are asserted in `GradedHead`'s pass over them (one load each)
    let all ← GradedHead.allJobs
    let all := all.filter (!GradedHead.notLoaded.contains ·.1)
    let words := ("src-words", "fixtures/ixon-v4/src-words/words", ([] : List String))
    -- `closures`: `knot`
    let some (lc, sc, rc) := all.find? (·.1 == "phase2-closures/closures")
      | throw (IO.userError "no closures closure")
    let (ic, _) ← loadClosure lc sc rc
    let rf := LetClo.refusedConsts ic
    expect a rf.isEmpty s!"letWit: closures: run pairs still refused at {rf}, expected none"
    let fc := failing ic
    expect a (fc == ["caseRec", "caseShape"])
      s!"letWit: closures: false conjuncts {fc}, expected [caseRec, caseShape]"
    let rs := LetClo.rootsReaching ic 19
    expect a (rs.length == 1) s!"letWit: closures: roots reaching c19: {rs}, expected one"
    let some knot := rs.head? | throw (IO.userError "closures: no root reaching c19")
    expect a (LetClo.familyAt ic knot)
      s!"letWit: closures: a decided hypothesis of the widest family fails at c{knot}"
    let outs := [([0, 0], 0), ([3, 2], 103), ([5, 3], 5), ([10, 4], 110), ([4, 9], 4)].map
      fun (xs, v) => (LetClo.readAt ic knot xs, v)
    expect a (outs.all fun (o, v) => o == some (.nat v))
      s!"letWit: closures: SrcEval at c{knot} reads back {outs.map fun (o, _) => repr o}"
    -- `src-words`
    let (iw, _) ← loadClosure words.1 words.2.1 words.2.2
    let lostW := Zeta.lostConsts iw
    let wcW := Zeta.witConsts iw
    let expW := (Zeta.witExpected.lookup "src-words").getD []
    expect a (part iw "letWit" == some true && lostW.isEmpty && wcW == expW)
      s!"letWit: src-words: letWit {part iw "letWit"}, accepted with step C and refused now \
        {lostW}, accepted by the witness case alone {wcW} (expected {expW})"
    let rw := LetClo.refusedConsts iw
    expect a rw.isEmpty s!"letWit: src-words: run pairs still refused at {rw}, expected none"
    let fw := failing iw
    expect a (fw == ["noWord"]) s!"letWit: src-words: false conjuncts {fw}, expected [noWord]"
    let wroots := iw.src.roots.map (·.2)
    expect a (wroots.length == 4) s!"letWit: src-words: {wroots.length} roots, expected 4"
    for rt in wroots do
      let fr := failingAt iw rt
      expect a (fr == ["noWord"] && sBAt iw rt)
        s!"letWit: src-words: at c{rt} false conjuncts {fr} (expected [noWord]), 1b {sBAt iw rt}"
    -- a witness whose stored type is the domain only up to unfolding
    let some (t619, e619) := (runPairsB iw.src iw.env iw.κ 619).head?
      | throw (IO.userError "src-words: no run pair at c619")
    let doms := witDoms t619 e619
    let some D := doms.head? | throw (IO.userError "src-words: no witness domain at c619")
    let some Dk := (match D with | .const k [] => some k | _ => none)
      | throw (IO.userError "src-words: the witness domain is not a closed constant")
    let some (.defnInfo _ Dval _) := iw.env.find? Dk
      | throw (IO.userError "src-words: the witness domain is not a stored definition")
    let wits := iw.env.consts.filter fun ci =>
      decide (ci.toConstantVal.type = D) && ci.toConstantVal.levelParams.isEmpty &&
        (match ci with | .ctorInfo .. | .defnInfo .. => true | _ => false)
    expect a (doms.all (· == D) && wits.length == 1)
      s!"letWit: src-words: domains {doms.length}, one domain {doms.all (· == D)}, witnesses {wits.length}"
    let some w := wits.head? | throw (IO.userError "src-words: no witness")
    let iw' := { iw with env := mapConst iw.env w.toConstantVal.name (setType Dval) }
    let fw' := failing iw'
    expect a (fw' == ["noWord", "letWit"])
      s!"letWit: src-words, the witness's stored type unfolded: false conjuncts {fw'}"
    -- planted, on `fib`'s root
    let some fs := subjects.head? | throw (IO.userError "no subject")
    let (fi, _) ← load fs
    let some (.defn _ _ _ _ v) := fi.src.decl? fi.rootId | throw (IO.userError "fib: no root value")
    let some (.defnInfo _ val _) := fi.env.find? (fi.κ fi.rootId)
      | throw (IO.userError "fib: no stored root value")
    let some natC := fi.src.known.nat | throw (IO.userError "fib: no Nat")
    expect a (fi.κ natC == Ix.Kernel.natName) s!"letWit: fib: Nat's key"
    let natT : Term := .const natC []
    let natK : KExpr := .const Ix.Kernel.natName []
    let lt (x b : Term) : Term := .letE default default (.sort .zero) x b
    let app (f x : Term) : Term := .app f x default default
    let lam (d b : Term) : Term := .lam default d b
    let accepted (j : Input) : Bool :=
      (runPairsB j.src j.env j.κ j.rootId).all fun (t, e) =>
        corrSB j.κ (j.lpsOf j.rootId) [] t e && !Zeta.corrSBClo j.κ (j.lpsOf j.rootId) [] t e
    let some wit1 := Zeta.setRoot fi (lt v (app (lam natT (.var 1)) (.natLit 0)))
        (some (.app (.lam natK val bmN) (litE 0))) | throw (IO.userError "fib: wit1")
    expect a ((failing wit1).isEmpty && accepted wit1 && Zeta.fibOut wit1 == some (.nat 55))
      s!"letWit: fib, let x := v; (λ (_ : Nat). x) 0: false conjuncts {failing wit1}, the \
        witness case alone {accepted wit1}, read back {repr (Zeta.fibOut wit1)}"
    let some wit2 := Zeta.setRoot fi
        (lt v (app (app (lam natT (lam natT (.var 2))) (.natLit 0)) (.natLit 0)))
        (some (.app (.app (.lam natK (.lam natK val bmN) bmN) (litE 0)) (litE 0)))
        | throw (IO.userError "fib: wit2")
    expect a ((failing wit2).isEmpty && accepted wit2 && Zeta.fibOut wit2 == some (.nat 55))
      s!"letWit: fib, let x := v; (λ (_ : Nat) (_ : Nat). x) 0 0: false conjuncts \
        {failing wit2}, the witness case alone {accepted wit2}, read back {repr (Zeta.fibOut wit2)}"
    let fnT : Term := .pi default default natT natT
    let some nonConst := Zeta.setRoot fi (lt v (app (lam fnT (.var 1)) (.natLit 0)))
        (some (.app (.lam (.forallE natK natK bmN) val bmN) (litE 0)))
        | throw (IO.userError "fib: nonConst")
    expect a (failing nonConst == ["valueCorr"])
      s!"letWit: fib, a domain that is not a closed constant (Nat → Nat): false conjuncts \
        {failing nonConst}"
    let some underPi := Zeta.setRoot fi
        (lt v (app (lam natT (.pi default default natT (.var 2))) (.natLit 0)))
        (some (.app (.lam natK (.forallE natK val bmN) bmN) (litE 0)))
        | throw (IO.userError "fib: underPi")
    expect a (failing underPi == ["valueCorr"])
      s!"letWit: fib, a copy under a ∀: false conjuncts {failing underPi}"
    let some noWit := Zeta.setRoot fi
        (lt v (app (lam (.const fi.rootId []) (.var 1)) (.natLit 0)))
        (some (.app (.lam (.const (fi.κ fi.rootId) []) val bmN) (litE 0)))
        | throw (IO.userError "fib: noWit")
    expect a (failing noWit == ["letWit"])
      s!"letWit: fib, a closed constant domain with no stored constant of that type: false \
        conjuncts {failing noWit}"
    -- the order of the cases: the live and closure-capture plants never reach the witness case
    let some live := Zeta.setRoot fi (lt v (.var 0)) | throw (IO.userError "fib: live")
    let some clo := Zeta.setRoot fi (lt v (lam (.sort .zero) (.var 1)))
        (some (.lam (.sort .zero) val bmN)) | throw (IO.userError "fib: clo")
    let some notCopy := Zeta.setRoot fi (lt v (lam (.sort .zero) (.var 1)))
        (some (.lam (.sort .zero) (litE 7) bmN)) | throw (IO.userError "fib: notCopy")
    let unseen := [live, clo, notCopy].all fun j => (witSitesOf j).isEmpty
    expect a (unseen && (failing live).isEmpty && (failing clo).isEmpty &&
        failing notCopy == ["valueCorr"])
      s!"letWit: fib, the live and closure-capture plants: witness sites {unseen}, false \
        conjuncts {failing live} {failing clo} {failing notCopy}"
    IO.println s!"letWit: src-words: letWit true, nothing accepted with step C refused, the \
      witness case alone accepting {wcW}; closures: false conjuncts {fc}, at c{knot} every decided \
      hypothesis and SrcEval's five values; src-words: false conjuncts {fw}, at each of its 4 \
      roots noWord alone and 1b true; the \
      witness's stored type unfolded: {fw'}; fib: the shape at depths 1 and 2 accepted (55), \
      refused: a non-constant domain and a copy under a ∀ (valueCorr), a domain without a witness \
      (letWit); the live and closure-capture plants not seen by the witness case"
    IO.println s!"tests-grounding (letWit): {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: grounding (letWit): {error}"
    return false

end IxCCTests.Grounding.LetWit
