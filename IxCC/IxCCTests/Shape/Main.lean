import IxCC.Recheck.Produce
import IxCCCorrect.Shape2Produce

/-! # `tests-shape`: the shape producer and the shape check on committed closures

For each committed closure listed below and each of its roots: the kernel accepts the
closure (`Recheck.ingress`), the front end builds the checked source SrcEval runs (the
table, the annotation, lazification, as `tests-grounding` does), the untrusted producer
proposes a shape certificate (`IxCC.Correct.Shape2.Produce.produce`), and the decision
`IxCC.Correct.Shape2.certOk` is run on it. One line per root: `accept`, or `reject` with the
first instance the decision refuses (its constant's kind and address, its levels and the
proposed shape). The suite reports; it asserts nothing, and always exits 0 once every closure
loads. -/

open IxCC IxCC.Src IxCC.Correct.Shape2

namespace IxCCTests.Shape

/-- The checked source of a closure, with every sidecar root. -/
def loadSrc (stem : String) : IO Src.Program := do
  let bytes ← IO.FS.readBinFile s!"{stem}.ixe"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{stem}.equations.json"))
  let k ← match Recheck.ingress bytes json [] with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"{stem}: ingress: {e.render}")
  let cfg : Recheck.Config := {}
  let cfg := cfg.forInput k
  let P := k.program
  let (table, _, _) := Src.Table.build cfg.table P k.hints.proposals
  let p0 := { P with table }
  let ann ← IO.ofExcept (k.kernel.annotateChecked p0)
  match Src.Recheck.annotation p0 ann with
  | .ok r => pure r.1
  | .error _ => throw (IO.userError s!"{stem}: the annotation was refused")

/-- What kind of constant `c` is, as SrcEval resolves it. -/
def kindOf (p : Src.Program) (c : CId) : String :=
  match p.table.resolveOf c with
  | some (.prim op) => s!"prim {op.name}"
  | some (.word _ _ _) => "word"
  | some (.csimp _ _ _) => "csimp"
  | some (.eqn _ _) => "eqn"
  | some (.case _) => "case"
  | none =>
    match p.decl? c with
    | some (.recr _ _ _ np nmot nmin ni _ _ _) =>
      let kind := match p.table.recKindOf c with
        | some .ordinary => "ordinary"
        | some (.subsingleton _ _) => "subsingleton"
        | some .empty => "empty"
        | none => "no kind"
      s!"recursor ({kind}, {np} params, {nmot} motives, {nmin} minors, {ni} indices)"
    | some d => d.kindName
    | none => "no declaration"

def hex (a : Ixon.Address) : String := a.toHex

/-- The constants a term names, in order, without repeats. -/
def constsIn : Src.Term → List CId → List CId
  | .const c _, acc => if acc.contains c then acc else acc ++ [c]
  | .app f a _ _, acc => constsIn a (constsIn f acc)
  | .lam _ _ t, acc => constsIn t acc
  | .letE _ _ _ _ v b, acc => constsIn b (constsIn v acc)
  | .proj _ _ e, acc => constsIn e acc
  | _, acc => acc

/-- The term SrcEval runs for a constant, if it unfolds one. -/
def bodyOf (p : Src.Program) (c : CId) : Option Src.Term :=
  match p.table.resolveOf c with
  | some (.eqn _ body) => some body
  | some _ => none
  | none =>
    match p.decl? c with
    | some (.defn .defn .safe _ _ v) => some v
    | _ => none

/-- A shape on one line. -/
def showShape : Shape → String
  | .nat => "N"
  | .enum i => s!"E{i}"
  | .data d => s!"D{d}"
  | .irr => "_"
  | .fn a b => s!"({showShape a} -> {showShape b})"

/-- A term on one line: `#i` a variable, `cN` a constant, `~a` an argument irrelevant at `ls`,
`'a` a by-name one, `\` a λ (`\~` irrelevant binder), `T` a type or sort. -/
def showTerm (ls : Levels) : Src.Term → String
  | .var i => s!"#{i}"
  | .sort _ => "S"
  | .pi _ _ _ => "T"
  | .const c _ => s!"c{c}"
  | .natLit n => s!"{n}"
  | .strLit _ => "str"
  | .proj s i e => s!"{showTerm ls e}.{i}@{s}"
  | .lam b _ t => (if b.rel.irrAt ls then "\\~" else "\\") ++ (if b.propWhen.allowsBeta ls then "" else "!") ++ showTerm ls t
  | .letE _ _ r _ v t => s!"let{if r.irrAt ls then "~" else ""} {showTerm ls v}; {showTerm ls t}"
  | .app f a m r =>
    let arg := if r.irrAt ls then "~" else (if m == .byName then "'" else "") ++ showTerm ls a
    s!"({showTerm ls f} {arg})"

/-- Detail of a refused instance, for reading: its body and the constants it names. -/
def detail (p : Src.Program) (cert : Cert) (c : CId) (ls : Levels) : String :=
  match bodyOf p c with
  | some t =>
    let cs := constsIn t []
    let lines := cs.map fun d =>
      let shapes := (cert.insts.filter fun e => e.1 == d).map fun e => s!"{e.2.1}:{showShape e.2.2}"
      s!"    #{d} {kindOf p d} {(hex (p.addr d)).take 12} {shapes}"
    s!"  body: {(showTerm ls t).take 1500}\n  names:\n" ++ "\n".intercalate lines
  | none => s!"  (no body; levels {ls})"

/-- Run the producer and the decision on root `i` of `p`. -/
def runRoot (label : String) (p : Src.Program) (i : Nat) (name : String) : IO Bool := do
  let some (_, c) := p.roots[i]? | do
    IO.println s!"{label} {name}: no such root"
    return false
  let cert := Produce.produce p c
  let size := s!"{cert.insts.length} instances, {cert.enums.length} enumerations, \
    {cert.datas.length} data entries"
  if certOk p cert then
    let rootShape := match cert.insts.head? with
      | some e => showShape e.2.2
      | none => "?"
    IO.println s!"{label} {name}: accept, root shape {rootShape} ({size})"
    return true
  else
    match cert.insts.find? fun e => !entryOk p cert e.1 e.2.1 e.2.2 with
    | some (d, ls, σ) =>
      IO.println s!"{label} {name}: reject ({size}); first refused instance: {kindOf p d} \
        {hex (p.addr d)} at levels {ls}, shape {showShape σ}"
      if (← IO.getEnv "SHAPE_DETAIL").isSome then IO.println (detail p cert d ls)
    | none =>
      IO.println s!"{label} {name}: reject ({size}); every instance passes, an enumeration or \
        data entry is refused"
    return false

def benchK1 : List String :=
  ["ackermann", "collatz", "even-odd", "fib", "gcd", "prime-count", "sfib", "sum-loop", "tak"]

def run : IO UInt32 := do
  let mut accepted := 0
  let mut total := 0
  for b in benchK1 do
    let p ← loadSrc s!"fixtures/ixon-v4/bench-k1/{b}"
    total := total + 1
    if ← runRoot "bench-k1" p 0 b then accepted := accepted + 1
  let stem := "fixtures/corpus/phase1-scalar/scalar"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{stem}.equations.json"))
  let names := match Src.Hints.ofK1Json json with
    | .ok h => h.roots.toList.map fun (r : Ixon.Address × Option String) => r.2.getD "?"
    | .error _ => []
  let p ← loadSrc stem
  for (name, i) in names.zipIdx do
    total := total + 1
    if ← runRoot "scalar" p i name then accepted := accepted + 1
  IO.println s!"accepted {accepted} of {total} roots"
  return 0

end IxCCTests.Shape

def main : IO UInt32 := IxCCTests.Shape.run
