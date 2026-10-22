import LSpec
import Ix.Meta
import Ix.LeanIngress
import IxC.Kernel.Tier.Answer
import Tests.Ix.Kernel.SourceIngress
import Tests.Ix.Kernel.TierIndDefs

/-! # The tier's typing-only inductive install and its answer view (`lake test -- kernel-tier-ind`)

M7 Q1, T1. The fixtures of `Tests.Ix.Kernel.TierIndDefs` are canonicalized,
their logical closure (`List` and the prelude) is checked in Source mode
(`checkSource`), and on top of it:

* **the blocks**, through the Source ingress's tier conversion
  (`convertTierInductive`) and `Ix.Kernel.Tier.indC`: the reflexive `U`, the
  nested `UN` and polymorphic MLList-shaped `Poly` (including their nested
  recursors), the negative `UNeg`
  (positivity is not checked), the structure `S` (a projection table), the
  mutual `A`/`B`, and the family `PF` without its recursor, each typed and
  pushed onto the check view and the answer view;
* **the definitions** `S.b` (its value a `.proj`, typed through `S`'s table
  in the check view) and `kdef`, through the tier's own `checkDeclC`, with
  their δ forms (`defsAnswerC`) in the answer view;
* **the questions**: ι (`qIota`), a nested auxiliary's ι (`qNested`),
  structure η through δ and `.proj` (`qEtaL`/`qEtaR`), δ (`qDelta`) are
  decided `true` in the answer view, and the first, third and fourth `false`
  in the check view (opaque); proof irrelevance at the family (`qPfL`/`qPfR`)
  is `true`; a term naming the family's absent recursor is refused;
* **the declines**: `U`'s rules swapped (a rule without its equation's type),
  `A.a` claimed by `B` (a constructor not returning its former), `Big` with
  its type lowered to `Type` (a field's universe above its type's), and
  `Poly` recursor headers with reordered, extra, duplicate or missing levels. -/

open LSpec
open Ix.LeanIngress
open Ix.Kernel (Expr FEnv mkFEnv)
open Ix.Kernel.Tier
open Tests.Ix.Kernel.SourceIngress (envOf)
open Tests.Ix.Kernel.SourceIngressStep (condense)

namespace Tests.Ix.Kernel.TierInd

def defsModule : Lean.Name := `Tests.Ix.Kernel.TierIndDefs

def defs (n : String) : Lean.Name := defsModule ++ n.toName

def ixn (n : Lean.Name) : Ix.Name := Ix.Name.fromLeanName n

def readMsg : _root_.Ix.Kernel.Reader.ReadError → String
  | .malformed m => s!"malformed: {m}"
  | .declined m => s!"declined: {m}"

/-- A block's group from its formers' and recursors' names. -/
def groupOf (env : Ix.Environment) (formers recs : List Lean.Name) :
    Except String (Array Ix.InductiveVal × Array (Array Ix.ConstructorVal) × Array Ix.RecursorVal) := do
  let mut types := #[]
  let mut ctors := #[]
  for n in formers do
    let some (.inductInfo t) := env.get? (ixn n) | throw s!"{n}: not an inductive"
    types := types.push t
    let mut cs := #[]
    for c in t.ctors do
      let some (.ctorInfo cv) := env.get? c | throw s!"{n}: a constructor is missing"
      cs := cs.push cv
    ctors := ctors.push cs
  let mut rs := #[]
  for n in recs do
    let some (.recInfo r) := env.get? (ixn n) | throw s!"{n}: not a recursor"
    rs := rs.push r
  return (types, ctors, rs)

/-- A block as the tier takes it. -/
def tierBlock (env : Ix.Environment) (formers recs : List Lean.Name) : Except String (TierInd .source) := do
  let (ts, cs, rs) ← groupOf env formers recs
  (convertTierInductive ts cs rs).mapError readMsg

/-- A definition's value, converted. -/
def valueOf (env : Ix.Environment) (n : Lean.Name) : Except String (Expr .source) := do
  let (cnst, value) ← match env.get? (ixn n) with
    | some (.defnInfo v) => pure (v.cnst, v.value)
    | some (.thmInfo v) => pure (v.cnst, v.value)
    | _ => throw s!"{n}: not a definition or a theorem"
  match exprsOf #[(⟨cnst.levelParams, false⟩, value)] with
  | .ok ks => pure ks[0]!
  | .error e => throw (readMsg e)

/-- `a ≡ b` decided over an index's cached functions, both annotated first. -/
def decide' (r : Ix.Kernel.Cached.CoreFnsI .source) (a b : Expr .source) : Except String Bool :=
  match (do
      let a ← r.annotate 0 a
      let b ← r.annotate 0 b
      r.defeq 0 a b : Ix.Kernel.Cached.CheckCM .source Bool) {} with
  | .ok (v, _) => .ok v
  | .error e => .error (toString e)

/-- The type of `a` over an index's cached functions, annotated first (an
unknown constant is refused here). -/
def infer' (r : Ix.Kernel.Cached.CoreFnsI .source) (a : Expr .source) : Except String (Expr .source) :=
  match (do
      let a ← r.annotate 0 a
      r.infer 0 a : Ix.Kernel.Cached.CheckCM .source (Expr .source)) {} with
  | .ok (v, _) => .ok v
  | .error e => .error (toString e)

/-- The check view's functions. -/
def checkKnot (fe : FEnv .source) : Ix.Kernel.Cached.CoreFnsI .source :=
  Ix.Kernel.Cached.coreKnotI .verified fe Ix.Kernel.checkFuel

/-- The blocks, in install order: name, formers, recursors. -/
def blocks : List (String × List Lean.Name × List Lean.Name) := [
  ("U", [defs "U"], [defs "U.rec"]),
  ("UN", [defs "UN"], [defs "UN.rec", defs "UN.rec_1"]),
  ("Poly", [defs "Poly"], [defs "Poly.rec", defs "Poly.rec_1"]),
  ("UNeg", [defs "UNeg"], [defs "UNeg.rec"]),
  ("S", [defs "S"], [defs "S.rec"]),
  ("A/B", [defs "A", defs "B"], [defs "A.rec", defs "B.rec"]),
  ("PF (no recursor)", [defs "PF"], [])]

def evaluate : IO (Array String × Array String) := do
  let leanEnv ← getCompileEnv #[defsModule]
  let logEnv ← envOf leanEnv #[`List, `Thunk, `Id]
  let kenv ← match checkSource logEnv (condense logEnv) with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"checkSource on the logical closure: {e}")
  let fe₀ := mkFEnv kenv
  let fix ← envOf leanEnv (#["U", "UN", "Poly", "UNeg", "S", "A", "PF", "Big", "kdef", "qIota", "qNested", "qPoly",
    "qEtaL", "qEtaR", "qDelta", "qTrue", "qPfL", "qPfR", "qPfRec"].map defs)
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let mut fe := fe₀
  let mut av := AnswerView.ofLogical fe₀
  -- the blocks
  for (name, formers, recs) in blocks do
    match tierBlock fix formers recs with
    | .error e => errors := errors.push s!"{name}: conversion: {e}"
    | .ok b =>
      match indC fe b with
      | .ok o =>
        fe := pushAll fe o.checkInfos
        av := av.pushInd o
        lines := lines.push s!"{name}: typed ({o.types.length} formers, {o.ctors.length} constructors, \
          {o.recs.length} recursors, {o.tables.length} projection tables)"
      | .error e => errors := errors.push s!"{name}: {e}"
  -- the partition
  match groupOf fix [defs "U"] [defs "U.rec"], groupOf fix [defs "PF"] [defs "PF.rec"] with
  | .ok (ts, cs, rs), .ok (ts', cs', rs') =>
    unless isTierInductive (.inductive ts cs rs) && !isTierInductive (.inductive ts' cs' rs') do
      errors := errors.push "isTierInductive: U is not a tier group or PF is"
  | _, _ => errors := errors.push "isTierInductive: groups missing"
  -- the definitions: the tier's check, then their δ forms
  for n in [defs "S.b", defs "kdef"] do
    match fix.get? (ixn n) with
    | some ci@(.defnInfo v) =>
      match convertTier (.definitions #[ci]) with
      | .ok d@(.defs _ ms) =>
        match checkDeclC fe₀ fe d with
        | .ok (fe', _) =>
          match defsAnswerC fe (ms.map fun (cv, val) => (cv, val, hintOf v.hints)) with
          | .ok infos =>
            av := av.pushInfos infos
            fe := fe'
            lines := lines.push s!"{n}: typed, δ form in the answer view"
          | .error e => errors := errors.push s!"{n}: δ form: {e}"
        | .error e => errors := errors.push s!"{n}: tier: {e}"
      | .ok _ => errors := errors.push s!"{n}: not a definition block"
      | .error e => errors := errors.push s!"{n}: {readMsg e}"
    | _ => errors := errors.push s!"{n}: missing"
  -- the questions: (left, right, answer view's verdict, check view's verdict if asked)
  let qs : List (String × String × Bool × Option Bool) := [
    ("qIota", "qTrue", true, some false), ("qNested", "qTrue", true, none),
    ("qPoly", "qTrue", true, some false),
    ("qEtaL", "qEtaR", true, some false), ("qDelta", "qTrue", true, some false),
    ("qPfL", "qPfR", true, none)]
  for (l, r, wantA, wantC?) in qs do
    match valueOf fix (defs l), valueOf fix (defs r) with
    | .ok a, .ok b =>
      match decide' av.knot a b with
      | .ok got =>
        lines := lines.push s!"{l} ≡ {r}: answer view {got}"
        unless got == wantA do errors := errors.push s!"{l} ≡ {r}: answer view {got}, expected {wantA}"
      | .error e => errors := errors.push s!"{l} ≡ {r}: answer view refused: {e}"
      if let some wantC := wantC? then
        match decide' (checkKnot fe) a b with
        | .ok got =>
          lines := lines.push s!"{l} ≡ {r}: check view {got}"
          unless got == wantC do errors := errors.push s!"{l} ≡ {r}: check view {got}, expected {wantC}"
        | .error e => errors := errors.push s!"{l} ≡ {r}: check view refused: {e}"
    | _, _ => errors := errors.push s!"{l}, {r}: values missing"
  match valueOf fix (defs "qPfRec") with
  | .ok a =>
    match infer' av.knot a with
    | .ok _ => errors := errors.push "qPfRec: the family's absent recursor was answered"
    | .error e => lines := lines.push s!"qPfRec: refused ({e})"
  | .error e => errors := errors.push s!"qPfRec: {e}"
  -- the declines, each at the logical index (with the blocks it needs)
  let expectDecline (name : String) (b : Except String (TierInd .source)) (at_ : FEnv .source)
      (needle : String) (errors lines : Array String) : Array String × Array String :=
    match b with
    | .error e => (errors.push s!"{name}: conversion: {e}", lines)
    | .ok b =>
      match indC at_ b with
      | .ok _ => (errors.push s!"{name}: typed, expected a decline", lines)
      | .error e =>
        let msg := toString e
        if (msg.splitOn needle).length > 1 then (errors, lines.push s!"{name}: declined ({msg})")
        else (errors.push s!"{name}: declined, but not by the expected check: {msg}", lines)
  let swapped := (tierBlock fix [defs "U"] [defs "U.rec"]).map fun b =>
    { b with recs := b.recs.map fun (cv, sh, rules) => (cv, sh, rules.map fun rl =>
        match rules.find? (·.ctor != rl.ctor) with
        | some other => { rl with rhs := other.rhs }
        | none => rl) }
  (errors, lines) := expectDecline "U, rules swapped" swapped fe₀ "equation's type" errors lines
  let misowned := (tierBlock fix [defs "A", defs "B"] [defs "A.rec", defs "B.rec"]).map fun b =>
    { b with ctors := b.ctors.map fun (cv, i, nF) =>
        if cv.name == ingressKey (ixn (defs "A.a")) then (cv, 1 - i, nF) else (cv, i, nF) }
  (errors, lines) := expectDecline "A.a claimed by B" misowned fe₀ "does not return its former"
    errors lines
  let lowered := (tierBlock fix [defs "Big"] []).map fun b =>
    { b with types := b.types.map fun (cv, nIdx) => ({ cv with type := .sort (.succ .zero) }, nIdx) }
  (errors, lines) := expectDecline "Big at Type" lowered fe₀ "universe above" errors lines
  -- A header still has to declare distinct, sufficient levels, and only
  -- the established order is admitted. In particular [0,1], which passed
  -- the former prefix guard, is not Poly's large-eliminator order [1,0].
  let poly := tierBlock fix [defs "Poly"] [defs "Poly.rec", defs "Poly.rec_1"]
  for (label, levels, why) in [
      ("reordered", [0, 1], "are not its block's"),
      ("extra", [2, 1, 0], "are not its block's"),
      ("duplicate", [1, 0, 0], "duplicate universe parameters"),
      ("missing", [1], "undeclared universe parameter")] do
    let bad := poly.map fun b =>
      { b with recs := b.recs.map fun (cv, sh, rules) => ({ cv with levelParams := levels }, sh, rules) }
    (errors, lines) := expectDecline s!"Poly, {label} levels" bad fe₀ why errors lines
  return (errors, lines)

def tierInd : TestSeq :=
  .individualIO "the tier's typing-only inductive install and its answer view" none (do
    let (errors, lines) ← evaluate
    for l in lines do IO.println l
    let msg := if errors.isEmpty then none else some ("\n".intercalate errors.toList)
    return (errors.isEmpty, lines.size, 0, msg)) .done

def suite : List TestSeq := [tierInd]

end Tests.Ix.Kernel.TierInd
