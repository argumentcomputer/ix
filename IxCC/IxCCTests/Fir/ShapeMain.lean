import IxCC.Recheck.Produce
import IxCC.Fir.ShapeInfer
import IxCC.Fir.Rep
import IxCCTests.Recheck.Audit

/-! # `tests-fir-shape`: the shape producer and the shape checker at `Fir`

For each closure of the committed K1 benchmarks (`fixtures/ixon-v4/bench-k1`) and of the scalar
corpus (`fixtures/corpus/phase1-scalar`): the kernel accepts the closure (`Recheck.ingress`), the
recheck producer proposes its certificate, the certified front half (`Recheck.front`,
`Lam.erase`, `Recheck.middle`) makes the `Fir` program, the untrusted producer
(`Fir.ShapeInfer.infer`) proposes a shape certificate, and the checker (`Fir.Shape.check`)
decides it. One line per root: `accept` with the root function's shapes, or `refuse` with the
first node the checker refuses in a function the root reaches (`Fir.ShapeInfer.whyRoot`, a
diagnosis for reading). Then a table per family.

Per closure, also: the certificate that states nothing (`ShapeInfer.trivial`) checks; a mutant
of the proposal (one listed variable claimed to be an enumeration no table lists) is refused;
the native flow condition (`Fir.Rep.flowsOk`); the derived layout (`Fir.Rep.ofShapes`: how many
variables are raw words) and its elaboration (`Fir.Rep.elaborateShapes`: how many `box` and
`unbox` it inserts). Before the closures, five controls of the flow condition on a function
returning a packed byte array, at result shapes the checker accepts or refuses.

The suite fails (exit 1) when a closure does not load (ingress), when a trivial certificate is
refused, when a mutant is accepted, or when a control disagrees. A refused proposal is reported,
not a failure: the producer is untrusted, and the hand-off then carries the trivial certificate.
A closure the certified front half declines (the corpus documents `typeFormerPolymorphism`'s
`relevance-C2`) has no `Fir` program and is counted apart. `FIRSHAPE_ONLY=<family>` runs one
family; `FIRSHAPE_DETAIL=1` prints every reachable function's variable shapes.

At build time the checker's path is audited for the kernel-evaluable style
(`IxCCTests.Recheck.Audit.violations`), as `Recheck.run`'s is: it is destined for the certificate
replay. -/

open IxCC

namespace IxCCTests.FirShape

open IxCC.Shape
open IxCC.Fir.ShapeInfer

/-! ## The checker's path is in kernel-evaluable style -/

run_cmd do
  let env ← Lean.getEnv
  for root in [``IxCC.Fir.Shape.check, ``IxCC.Fir.Rep.flowsOk, ``IxCC.Fir.Rep.ofShapes] do
    let found := IxCCTests.Recheck.Audit.violations env root
    unless found.isEmpty do
      throwError "{root}'s path is not in kernel-evaluable style: {found.toList}"

/-! ## Fixtures -/

def families : List (String × String) :=
  [("bench-k1", "fixtures/ixon-v4/bench-k1"),
   ("phase1-scalar", "fixtures/corpus/phase1-scalar")]

/-- The closures of a directory: each `.ixe` with its sidecar (`<stem>.equations.json`, else
`equations.json`), as `tests-shape` finds them. -/
def closuresOf (dir : String) : IO (List (String × String × String)) := do
  let entries ← System.FilePath.readDir dir
  let names := (entries.toList.map fun e => e.fileName).filter fun n => n.endsWith ".ixe"
  let names := names.mergeSort fun a b => a ≤ b
  let mut out := []
  for n in names do
    let stem := (System.FilePath.mk n).fileStem.getD n
    let cands := [s!"{dir}/{stem}.equations.json", s!"{dir}/equations.json"]
    let mut eqs := none
    for c in cands do
      if eqs.isNone && (← System.FilePath.pathExists c) then eqs := some c
    match eqs with
    | some e => out := out ++ [(stem, s!"{dir}/{n}", e)]
    | none => IO.println s!"{dir}/{n}: no sidecar found, skipped"
  return out

/-- A closure through the certified front half: the checked source, the `Fir` program, and the
names of the roots in order; or why the front half declines it (`.inr`). An ingress failure
throws. -/
def loadFir (ixe eqs : String) :
    IO ((Src.Program × Fir.Program × List String) ⊕ String) := do
  let bytes ← IO.FS.readBinFile ixe
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let names := match Src.Hints.ofK1Json json with
    | .ok h => h.roots.toList.map fun (r : Ixon.Address × Option String) => r.2.getD "?"
    | .error _ => []
  let k ← match Recheck.ingress bytes json [] with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"ingress: {e.render}")
  let cfg : Recheck.Config := {}
  let cfg := cfg.forInput k
  let c ← match Recheck.produce cfg k with
    | .ok c => pure c
    | .error e => return .inr s!"the recheck producer declines: {e.render}"
  let (src, checked) ← match Recheck.front cfg k.program c with
    | .ok r => pure r
    | .error e => return .inr s!"front: {e.render}"
  let (lam, _) ← match Lam.erase src checked with
    | .ok r => pure r
    | .error _ => return .inr "erasure declines"
  let (_, fir, _, _) ← match Recheck.middle c src lam with
    | .ok r => pure r
    | .error e => return .inr s!"middle: {e.render}"
  return .inl (src, fir, names)

/-! How many `box` and `unbox` the elaboration inserted. -/
mutual
def coercions : Fir.Rep.RepCode → Nat
  | .bind _ r k =>
    (match r with
      | .box _ | .unbox _ => 1
      | _ => 0) + coercions k
  | .jp _ _ _ b k => coercions b + coercions k
  | .case _ alts d => coercionsAlts alts + coercionsOpt d
  | _ => 0
def coercionsAlts : List Fir.Rep.RepAlt → Nat
  | [] => 0
  | .mk _ b :: rest => coercions b + coercionsAlts rest
def coercionsOpt : Option Fir.Rep.RepCode → Nat
  | none => 0
  | some c => coercions c
end

/-- The listed positions the derived layout holds as raw words. -/
def rawWords (P : Fir.Program) (cert : Fir.Shape.ShapeCert) : Nat :=
  P.funs.toList.foldl (init := 0) fun n e =>
    let fc := Fir.Rep.funCertOf (cert.fn e.1)
    n + (fc.vars.toList.filter fun (_, r) => r == .word).length

/-! ## Controls for the native flow condition (no primitive makes an array, so no closure has an
array shape): one function returning its parameter, at shapes the checker accepts. -/

def idProgram : Fir.Program :=
  { funs := Src.NatMap.ofList [(0, { key := default, params := [(0, .tobj)], body := .ret (.var 0) })]
    size := 1, exports := [0], ctors := [], known := {} }

def idCert (ret : Shape) : Fir.Shape.ShapeCert :=
  { funs := Src.NatMap.ofList
      [(0, { params := [.arr (.natLt 256) none], ret
             vars := Src.NatMap.ofList [(0, .arr (.natLt 256) none)] })] }

/-- `(result shape, the checker accepts, the flow condition holds)`, expected. -/
def flowControls : List (Shape × Bool × Bool) :=
  [(.arr (.natLt 256) none, true, true),
   (.arr (.natLt 256) (some 3), false, true),
   (.arr (.natLt 65536) none, true, false),
   (.arr .any none, true, false),
   (.any, true, false)]

def runFlowControls : IO (List String) := do
  let mut bad := []
  for (ret, wantCheck, wantFlow) in flowControls do
    let c := idCert ret
    let gotCheck := Fir.Shape.check idProgram c
    let gotFlow := Fir.Rep.flowsOk idProgram c
    IO.println s!"control: a packed byte array returned at {render ret}: checker \
      {if gotCheck then "accepts" else "refuses"}, flow condition \
      {if gotFlow then "holds" else "fails"}"
    if gotCheck != wantCheck || gotFlow != wantFlow then
      bad := bad ++ [s!"flow control at {render ret}"]
  return bad

/-- The inductive of a source constructor. -/
def indOf (p : Src.Program) (c : Src.CId) : Option Src.CId :=
  match p.decl? c with
  | some (.ctor _ _ ind _ _ _ _) => some ind
  | _ => none

/-- The proposal with one listed variable of the root's reachable functions claimed to be an
enumeration the certificate does not list (it has no table entry, so no right-hand side, no
parameter declaration and no join declaration can give it). -/
def mutant (P : Fir.Program) (cert : Fir.Shape.ShapeCert) (root : Fir.FunId) :
    Option Fir.Shape.ShapeCert :=
  (reachable P root).findSome? fun f =>
    let fs := cert.fn f
    match fs.vars.toList.head? with
    | some (x, _) =>
      let bogus : Src.CId := 1000000007
      some { cert with funs := cert.funs.insert f { fs with vars := fs.vars.insert x (.enum bogus) } }
    | none => none

def censusLine (c : Census) : String :=
  s!"nat {c.nat}, natLt {c.natLt}, enum {c.enum}, data {c.data}, fn {c.fn}, other {c.other}"

structure Row where
  family : String
  roots : Nat := 0
  accepted : Nat := 0
  closures : Nat := 0
  closuresChecked : Nat := 0
  declined : Nat := 0

def run : IO UInt32 := do
  let only ← IO.getEnv "FIRSHAPE_ONLY"
  let detail := (← IO.getEnv "FIRSHAPE_DETAIL").isSome
  let mut failures : List String := ← runFlowControls
  let mut rows : List Row := []
  for (family, dir) in families do
    if only.isSome && only != some family then continue
    let mut row : Row := { family }
    for (stem, ixe, eqs) in ← closuresOf dir do
      let label := s!"{family} {stem}"
      let loaded ← try
          pure (some (← loadFir ixe eqs))
        catch e =>
          IO.println s!"{label}: not loaded: {(toString e).take 300}"
          pure none
      let some loaded := loaded
        | failures := failures ++ [s!"{label}: not loaded"]
      if let .inr why := loaded then
        IO.println s!"{label}: the certified front half declines, no Fir program: {why.take 200}"
        row := { row with declined := row.declined + 1 }
        continue
      let .inl (src, fir, names) := loaded | continue
      row := { row with closures := row.closures + 1 }
      let t0 ← IO.monoMsNow
      let cert := infer fir { indOf := indOf src, rootParam := .nat }
      let t1 ← IO.monoMsNow
      let ok := Fir.Shape.check fir cert
      let t2 ← IO.monoMsNow
      let flows := Fir.Rep.flowsOk fir cert
      let trivialOk := Fir.Shape.check fir (trivial fir)
      let elaborated := Fir.Rep.elaborateShapes fir cert
      let boxes := elaborated.funs.toList.foldl (init := 0) fun n e => n + coercions e.2.body
      if ok then row := { row with closuresChecked := row.closuresChecked + 1 }
      IO.println s!"{label}: {fir.funs.toList.length} functions, {cert.datas.length} data \
        entries, {cert.enums.length} enumerations; produced in {t1 - t0} ms, checked in \
        {t2 - t1} ms: {if ok then "accept" else "refuse"}; flow condition \
        {if flows then "holds" else "fails"}; derived layout: {rawWords fir cert} raw-word \
        variables, {boxes} box/unbox inserted; trivial certificate \
        {if trivialOk then "accepted" else "REFUSED"}"
      unless trivialOk do failures := failures ++ [s!"{label}: trivial certificate refused"]
      for (root, i) in fir.exports.zipIdx do
        let name := (names[i]?).getD s!"root{i}"
        row := { row with roots := row.roots + 1 }
        let fs := cert.fn root
        let sig := s!"{fs.params.map render} -> {render fs.ret}"
        let verdict ← match (if Fir.Shape.wfOk cert then whyRoot fir cert root
            else some "the data table lists a constructor twice") with
          | none =>
            row := { row with accepted := row.accepted + 1 }
            pure s!"accept {sig}; reachable variables: {censusLine (census fir cert root)}"
          | some why => pure s!"refuse: {why}"
        let mutantOk := match mutant fir cert root with
          | some m => if Fir.Shape.check fir m then "MUTANT ACCEPTED" else "mutant refused"
          | none => "no listed variable to mutate"
        if mutantOk == "MUTANT ACCEPTED" then
          failures := failures ++ [s!"{label} {name}: mutant accepted"]
        IO.println s!"  {name} (f{root}): {verdict}; {mutantOk}"
        if detail then
          for f in reachable fir root do
            let fs := cert.fn f
            IO.println s!"    f{f}: {fs.params.map render} -> {render fs.ret}; \
              {fs.vars.toList.map fun (x, σ) => s!"v{x}:{render σ}"}"
    rows := rows ++ [row]
  IO.println "family: closures with a Fir program, closures whose proposal checks, roots, \
    roots accepted, closures the front half declines"
  for r in rows do
    IO.println s!"  {r.family}: {r.closures}, {r.closuresChecked}, {r.roots}, {r.accepted}, \
      {r.declined}"
  if failures.isEmpty then
    IO.println "tests-fir-shape: ok"
    return 0
  else
    IO.println s!"tests-fir-shape: FAILED: {failures}"
    return 1

end IxCCTests.FirShape

def main : IO UInt32 := IxCCTests.FirShape.run
