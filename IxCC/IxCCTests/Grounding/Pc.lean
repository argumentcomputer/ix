import IxCCTests.Grounding.LetWit
import IxCCGrounding.PcRoot

/-! # `tests-grounding`: the Pc family (step Pc, `PUnit.casesOn` at its ordinary instances)

The Pc family's check `groundCheckWP` (`IxCCGrounding.PcRoot`: the word family's check with
`caseRec` replaced by `caseRecP`, which admits a `case` entry of kind `subsingleton` in the PUnit
shape, and `caseShape` by `caseShapeP`, which reads no sort clause at such an entry) and the other
decided hypotheses of `rootSound_678AGpWP_of_check` (`noCanonAB`, `litDefsB`, `instCheckB`, the
instance condition `pcInstB`, `headRegimeSB`), on `selEnv` of the closure with the word entries'
runtime references, as the word family's are read in `GradedHead`:

* **The families on all 52** (the suite's 51 and `src-words`): the word family on 46 (45 of the 51),
  the Pc family on 47: the same and `phase2-closures/closures`.
* **`closures`**: its one `subsingleton`-kind entry, c214 (`PUnit.casesOn`, recursor c71 of kind
  `subsingleton (allZero [1]) []`), refused by the landed `caseRec` and `caseShape` and admitted by
  `caseRecP` (every PUnit clause true) and `caseShapeP`; the check's false conjuncts `[caseRec,
  caseShape]` under the word family and none under the Pc family. Per root: the word family at c268,
  c116, c46, c207 (as before); the Pc family at those and at c39 and c140 (`stateLoop`,
  `stateLoopSE`, whose only instance of c214 is at `[1, 1]`, where the kind is `ordinary`).
* **Controls on `closures`**, each with the unplanted input accepted by the same decision and the
  plant shown to change what it reads: the instance at level 0 (root c46's instance set with
  `(c214, [0, 0])` added and walked closed: `pcInstB` alone false; at c39, c140, c207 the same plant
  fails `instCheckB` as well, recorded); a field (the kind's field sources `[proof]`: `caseRecP`
  alone, clause `srcs`); an index (the recursor's declaration with one index: `caseRecP` and the
  landed `caseProg`, which already requires `ni = 0`, so an index cannot be isolated to one
  conjunct); the constructor's class made `rel` (`caseRecP` alone, clause `class`); `w` made
  `allZero [0]` (`caseRecP` alone, clause `w`); `w` made always (`caseRecP` and `pcInstB`).
* **`strings` c823** (`phase1-decline`): an `Eq`-like entry (two parameters, one index, a family in
  `Prop`, one constructor without fields and without a class), refused by the PUnit clauses `np`,
  `ni`, `class`; `strings` false at `[caseRecP, proj, valueCorr, caseShapeP, caseProg]` (the word
  family: `[caseRec, proj, valueCorr, caseShape, caseProg]`). -/

namespace IxCCTests.Grounding.Pc

open IxCC IxCC.Grounding IxCCTests.Grounding
open IxCC.Src (Term CId Program)
open IxCCTests.Src (Assert expect)

def failW (i : Input) : List String :=
  (checkPartsW i.src i.env i.κ i.lpsOf i.ann i.Sl).filterMap fun (n, b) => if b then none else some n

def failWP (i : Input) : List String :=
  (checkPartsWP i.src i.env i.κ i.lpsOf i.ann i.Sl).filterMap fun (n, b) =>
    if b then none else some n

/-- `i` read as the word and Pc families read it: `selEnv` of the closure with the word entries'
runtime references. -/
def famOn (i : Input) : Input :=
  let sl := GradedHead.wordClosure i
  { i with env := selEnv i.src i.env i.κ sl, Sl := sl }

/-- The same at one root (its own closure). -/
def atRoot (i : Input) (rt : CId) : Input :=
  let pins := [i.src.known.boolTrue, i.src.known.boolFalse].filterMap id
  famOn { i with Sl := CaseEmpty.reach i (rt :: pins.filter (· != rt)), rootId := rt }

/-- The decided hypotheses other than the check, by name, on an instance set seeded by `roots`. -/
def partsWith (i : Input) (roots : List CId) (Inst : List (CId × IxCC.Src.Levels)) :
    List (String × Bool) :=
  [("noCanonAB", noCanonAB i.src i.env i.κ i.Sl), ("litDefsB", litDefsB i.env),
   ("instCheckB", instCheckB i.src i.env i.κ i.lpsOf roots Inst),
   ("pcInstB", pcInstB i.src Inst), ("headRegimeSB", GradedHead.sB i)]

def falseOf (ps : List (String × Bool)) : List String :=
  ps.filterMap fun (n, b) => if b then none else some n

/-- The false decided hypotheses of the word family (`pc := false`) or the Pc family, on `i` as
given (already read by `famOn`), the instance set walked from `roots`. -/
def famFalse (i : Input) (roots : List CId) (pc : Bool) : List String :=
  match instWalk i.src roots 1000000 with
  | none => ["instWalk"]
  | some Inst =>
    let check := if pc then failWP i else failW i
    let ps := (partsWith i roots Inst).filter fun (n, _) => pc || n != "pcInstB"
    check ++ falseOf ps

/-- The `case` entries of `Sl` whose recursor is of kind `subsingleton`, with the recursor. -/
def subEntries (i : Input) : List (CId × CId) :=
  i.Sl.filterMap fun c => match i.src.table.resolveOf c with
    | some (.case r) => match i.src.table.recKindOf r with
      | some (.subsingleton _ _) => some (c, r)
      | _ => none
    | _ => none

def clausesFalse (i : Input) (c r : CId) : List String :=
  match i.src.table.recKindOf r with
  | some (.subsingleton w srcs) =>
    falseOf (punitClauses i.src i.env i.κ i.ann i.Sl c r w srcs)
  | _ => ["notSubsingleton"]

def setClass (i : Input) (d : CId) (cls : IxCC.Src.Rel) : Input :=
  match i.ann.consts.get? d with
  | some r => { i with ann := { i.ann with consts := i.ann.consts.insert d { r with result := cls } } }
  | none => i

def closuresLabel : String := "phase2-closures/closures"

def run : IO Bool := do
  let a : Assert ← IO.mkRef 0
  try
    let all ← GradedHead.allJobs
    let all := all.filter (!GradedHead.notLoaded.contains ·.1)
    let jobs := all ++ [("src-words", "fixtures/ixon-v4/src-words/words", [])]
    -- the families on all 52
    let mut famW : List String := []
    let mut famWP : List String := []
    let mut strings? : Option Input := none
    let mut closures? : Option Input := none
    for (label, stem, roots) in jobs do
      let (i, _) ← loadClosure label stem roots
      let j := famOn i
      let rts := NoCanon.rootsOf i
      if (famFalse j rts false).isEmpty then famW := famW ++ [label]
      if (famFalse j rts true).isEmpty then famWP := famWP ++ [label]
      if label == "phase1-decline/strings" then strings? := some i
      if label == closuresLabel then closures? := some i
    expect a (jobs.length == 52 && famW.length == 46 && (famW.filter (· != "src-words")).length == 45 &&
        famWP.length == 47 && famW.all famWP.contains && famWP.filter (!famW.contains ·) == [closuresLabel])
      s!"pc: on {jobs.length} closures the word family holds on {famW.length}, the Pc family on \
        {famWP.length}, beyond the word family's {famWP.filter (!famW.contains ·)}, expected 46, 47 \
        and [{closuresLabel}]"
    let some ic := closures? | throw (IO.userError "pc: no closures closure")
    let jc := famOn ic
    -- the entry
    let es := subEntries jc
    expect a (es == [(214, 71)]) s!"pc: closures' subsingleton-kind entries {es}, expected [(214, 71)]"
    let (c, r) := (214, 71)
    let kindOk := jc.src.table.recKindOf r == some (.subsingleton (.allZero [1]) [])
    expect a (kindOk && !caseRecB jc.src jc.env jc.κ c && !caseShapeB jc.src jc.env jc.κ c &&
        caseRecPB jc.src jc.env jc.κ jc.ann jc.Sl c && caseShapePB jc.src jc.env jc.κ c &&
        caseProgOkB jc.src jc.env jc.κ jc.Sl c && (clausesFalse jc c r).isEmpty)
      s!"pc: closures c{c}: kind {repr (jc.src.table.recKindOf r)}; caseRec \
        {caseRecB jc.src jc.env jc.κ c}, caseShape {caseShapeB jc.src jc.env jc.κ c}, caseRecP \
        {caseRecPB jc.src jc.env jc.κ jc.ann jc.Sl c}, caseShapeP {caseShapePB jc.src jc.env jc.κ c}, \
        caseProg {caseProgOkB jc.src jc.env jc.κ jc.Sl c}, PUnit clauses false {clausesFalse jc c r}"
    expect a (failW jc == ["caseRec", "caseShape"] && (failWP jc).isEmpty)
      s!"pc: closures: false conjuncts {failW jc} under the word family, {failWP jc} under the Pc \
        family; expected [caseRec, caseShape] and none"
    -- per root
    let rts := NoCanon.rootsOf ic
    let rW := rts.filter fun rt => (famFalse (atRoot ic rt) [rt] false).isEmpty
    let rWP := rts.filter fun rt => (famFalse (atRoot ic rt) [rt] true).isEmpty
    let instsAt (rt : CId) : List (CId × IxCC.Src.Levels) :=
      match instWalk ic.src [rt] 1000000 with
      | some Inst => Inst.filter (·.1 == c)
      | none => []
    expect a (rts == [268, 116, 39, 140, 46, 207] && rW == [268, 116, 46, 207] && rWP == rts &&
        instsAt 39 == [(c, [1, 1])] && instsAt 140 == [(c, [1, 1])] &&
        failW (atRoot ic 39) == ["caseRec", "caseShape"] &&
        failW (atRoot ic 140) == ["caseRec", "caseShape"])
      s!"pc: closures' roots {rts}: the word family at {rW}, the Pc family at {rWP}; c{c}'s \
        instances at c39 {instsAt 39}, at c140 {instsAt 140}"
    -- control: the instance at level 0, at root c46 (the Inst plant); recorded at the others
    let lvl0 (rt : CId) : Option (List String × Bool × Bool) := do
      let Inst ← instWalk ic.src [rt] 1000000
      let Inst' ← instWalk.go ic.src 1000000 [(rt, []), (c, [0, 0])] []
      let jr := atRoot ic rt
      some (failWP jr ++ falseOf (partsWith jr [rt] Inst'), pcInstB ic.src Inst,
        Inst'.length == Inst.length + 1 && Inst'.contains (c, [0, 0]))
    expect a (lvl0 46 == some (["pcInstB"], true, true))
      s!"pc: level-0 control at c46 (unplanted pcInstB, planted false parts, the plant adding \
        exactly ({c}, [0, 0])): {lvl0 46}"
    let others := [268, 116, 39, 140, 207].map fun rt => (rt, (lvl0 rt).map (·.1))
    expect a (others == [(268, some ["pcInstB"]), (116, some ["pcInstB"]),
        (39, some ["instCheckB", "pcInstB"]), (140, some ["instCheckB", "pcInstB"]),
        (207, some ["instCheckB", "pcInstB"])])
      s!"pc: the level-0 plant at the other roots: {others}"
    -- controls on the closure: each plant changes what `caseRecPB` (or `caseProg`) reads
    let unpl := famFalse jc rts true
    expect a unpl.isEmpty s!"pc: closures unplanted: false {unpl}"
    -- the datum each plant changes: the recursor's kind and declaration, c78's class
    let datum (i' : Input) : String :=
      s!"{repr (i'.src.table.recKindOf r)} {repr (i'.src.decl? r)} {repr (constClass i'.ann 78)}"
    let plant (tag : String) (i' : Input) (exp : List String) (expClauses : Option (List String)) :
        IO Unit := do
      let j' := famOn i'
      let got := famFalse j' rts true
      let cl := clausesFalse j' c r
      let changed := datum i' != datum ic
      expect a (changed && got == exp && (expClauses.all (· == cl)))
        s!"pc: closures, {tag}: the datum read changed {changed}; false {got} (expected {exp}), \
          PUnit clauses false {cl} (expected {expClauses})"
    match ic.src.table.recKindOf r, ic.src.decl? r with
    | some (.subsingleton w _), some (.recr sf kk lv np nmot nmin _ ind rules ty) =>
      plant "a field (the kind's field sources [proof])"
        (CaseEmpty.setKind ic r (.subsingleton w [.proof])) ["caseRecP"] (some ["srcs"])
      plant "w made allZero [0]" (CaseEmpty.setKind ic r (.subsingleton (.allZero [0]) []))
        ["caseRecP"] (some ["w"])
      plant "w made always" (CaseEmpty.setKind ic r (.subsingleton (.allZero []) []))
        ["caseRecP", "pcInstB"] (some ["w"])
      -- an index cannot be isolated to one conjunct: the landed `caseProg` already requires
      -- `ni = 0`, and `caseRecP` reads the same declaration field (its clause `ni`, and the arity)
      plant "an index (the recursor's declaration with ni = 1; caseProg already requires ni = 0, \
          so an index is refused by caseRecP and the landed caseProg together)"
        { ic with src := ic.src.setDecl r (.recr sf kk lv np nmot nmin 1 ind rules ty) }
        ["caseRecP", "caseProg"] (some ["ni"])
      plant "the constructor c78's class made rel" (setClass ic 78 .rel) ["caseRecP"]
        (some ["class"])
      expect a (constClass ic.ann 78 == some (.proof (.allZero [0])))
        s!"pc: c78's class {repr (constClass ic.ann 78)}, expected proof (allZero [0])"
    | _, _ => throw (IO.userError "pc: c71 is not a subsingleton-kind recursor")
    -- strings c823
    let some is := strings? | throw (IO.userError "pc: no strings closure")
    let js := famOn is
    let esS := subEntries js
    expect a (esS == [(823, 3002)] && clausesFalse js 823 3002 == ["np", "ni", "class"] &&
        js.src.table.recKindOf 3002 == some (.subsingleton (.allZero []) []) &&
        failWP js == ["caseRecP", "proj", "valueCorr", "caseShapeP", "caseProg"] &&
        failW js == ["caseRec", "proj", "valueCorr", "caseShape", "caseProg"])
      s!"pc: strings: subsingleton-kind entries {esS}, c823's PUnit clauses false \
        {clausesFalse js 823 3002}; false {failWP js} under the Pc family, {failW js} under the \
        word family"
    IO.println s!"pc: the word family holds on {famW.length} of {jobs.length} closures, the Pc family \
      on {famWP.length} (with {closuresLabel}); closures' c214 admitted by caseRecP and caseShapeP, \
      the Pc family at its six roots (c39 and c140 now in); six controls on closures (the level-0 \
      instance refused by pcInstB alone at c46; a field, w made allZero [0], the class made rel by \
      caseRecP alone; an index by caseRecP and caseProg; w made always by caseRecP and pcInstB); \
      strings c823 (Eq-like) refused at np, ni, class"
    IO.println s!"tests-grounding (pc): {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: grounding (pc): {error}"
    return false

end IxCCTests.Grounding.Pc
