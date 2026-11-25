import IxCC.Recheck.Produce
import IxCC.Recheck.Proof.Front
import IxCCCorrect.GroundCheck
import IxCCCorrect.GroundShape
import IxCCCorrect.Unique

/-! # `tests-grounding pipeline`: the pipeline's grounding check on every committed root

`IxCC.Correct.groundCheck` (`IxCCCorrect.GroundCheck`) is the function a `compile` calls after the
certificate checker accepts: its acceptance is the hypothesis `GroundOk` of the composed theorems
(`IxCCCorrect.Compose`, `IxCCCorrect.ComposeExe`). This report runs it root by root on the
committed families `tests-shape` measures (same directories, same closures, same root labels, so
the two reports can be joined by line), and on three more (`phase1-decline`, `src-words`,
`src-diag`).

For each closure: ingress with every sidecar root (the kernel's acceptance), then the compiler
(`Recheck.compileInputRetry`). Where it compiles, the check reads what the certificate checker
checked: the artifact's source and checked annotation, the certificate's annotation, and root
`i`'s view. Where the compiler declines the closure (a root it refuses fails all of them), the
check reads the checked source the front end builds (as `tests-grounding`'s loaders do) and a
stand-in view that tags a constructor by its declared index; such closures are marked
`source only`, and the view matters only at an enumeration result. Root `i` is checked as root 0
of the program with that root alone, at its own address as the claimed target.

One line per root: `accept` with the calling convention the check returns, or `refuse` with the
first refusal (`groundRefusal`). Then a table per family and a histogram of first refusals. It
reports; it asserts nothing. `GROUND_ONLY=<family>` runs one family. -/

namespace IxCCTests.Grounding.Pipeline

open IxCC IxCC.Src IxCC.Sem IxCC.Correct

/-- The committed families: a label and the directory of its closures (the first fifteen are
`tests-shape`'s, in its order). -/
def families : List (String × String) :=
  [("bench-k1", "fixtures/ixon-v4/bench-k1"),
   ("k1", "fixtures/ixon-v4/k1"),
   ("phase1-scalar", "fixtures/corpus/phase1-scalar"),
   ("phase1-abi", "fixtures/corpus/phase1-abi"),
   ("phase1-boundary", "fixtures/corpus/phase1-boundary"),
   ("phase1-machines", "fixtures/corpus/phase1-machines"),
   ("phase1-resource", "fixtures/corpus/phase1-resource"),
   ("phase2-arity", "fixtures/corpus/phase2-arity"),
   ("phase2-closures", "fixtures/corpus/phase2-closures"),
   ("grounding", "fixtures/corpus/grounding"),
   ("ownership", "fixtures/ownership"),
   ("rc-budget", "fixtures/rc/budget"),
   ("rc-deep", "fixtures/rc/deep"),
   ("rc-real-source", "fixtures/rc/real-source"),
   ("fold", "fixtures/fold"),
   ("phase1-decline", "fixtures/corpus/phase1-decline"),
   ("src-words", "fixtures/ixon-v4/src-words"),
   ("src-diag", "fixtures/ixon-v4/src-diag")]

/-- The closures of a directory: each `.ixe` with its sidecar (`<stem>.equations.json`, else
`consumer.equations.json`, else `equations.json`). -/
def closuresOf (dir : String) : IO (List (String × String × String)) := do
  let entries ← System.FilePath.readDir dir
  let names := (entries.toList.map fun e => e.fileName).filter fun n => n.endsWith ".ixe"
  let names := names.mergeSort fun a b => a ≤ b
  let mut out := []
  for n in names do
    let stem := n.replace ".ixe" ""
    let cands := [s!"{dir}/{stem}.equations.json", s!"{dir}/consumer.equations.json",
      s!"{dir}/equations.json"]
    let mut eqs := none
    for c in cands do
      if eqs.isNone && (← System.FilePath.pathExists c) then eqs := some c
    match eqs with
    | some e => out := out ++ [(stem, s!"{dir}/{n}", e)]
    | none => IO.println s!"{dir}/{n}: no sidecar found, skipped"
  return out

/-- A stand-in for a root's view where the compiler declines the closure: a number as itself, a
field-less constructor at its declared index. -/
def standInView (p : Program) : View := fun o =>
  match o with
  | some (.nat n) => some (some (.nat n))
  | some (.ctor cid []) => some (some (.ctor (IxCC.Grounding.readTag p cid) []))
  | _ => none

/-- What the check reads of a closure. -/
structure Loaded where
  kernel : Src.KernelFront.Kernel
  names : List String
  src : Program
  checked : Relevance.Checked
  ann : Relevance.Ann
  view : Nat → View
  mode : String

def load (ixe eqs : String) : IO Loaded := do
  let bytes ← IO.FS.readBinFile ixe
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let k ← match Recheck.ingress bytes json [] with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"ingress: {e.render}")
  match Recheck.compileInputRetry {} k with
  | .ok (c, a) =>
    return { kernel := k.kernel, names := k.names, src := a.src, checked := a.checked,
             ann := c.relevance, view := fun i => a.front.view i, mode := "compiled" }
  | .error e =>
    let cfg : Recheck.Config := {}
    let cfg := cfg.forInput k
    let P := k.program
    let (table, _, _) := Src.Table.build cfg.table P k.hints.proposals
    let p0 := { P with table }
    let ann ← IO.ofExcept (k.kernel.annotateChecked p0)
    match Src.Recheck.annotation p0 ann with
    | .ok (src, checked) =>
      return { kernel := k.kernel, names := k.names, src, checked, ann,
               view := fun _ => standInView src, mode := s!"source only: compiler {e.code}" }
    | .error _ => throw (IO.userError "the annotation was refused")

def showAbi (abi : Abi) : String :=
  let res := match abi.result with
    | .nat => "Nat"
    | .enum cs => s!"enum of {cs.length}"
  s!"{abi.params.length} Nat -> {res}"

def bump (key : String) : List (String × Nat) → List (String × Nat)
  | [] => [(key, 1)]
  | (k, n) :: rest => if k == key then (k, n + 1) :: rest else (k, n) :: bump key rest

/-- The shape side of the escape-free check (`IxCC.Correct.groundShapeCheck`) at root `root`:
the untrusted producer's certificate, `certOk`, and `shapeRootB` at the root's first-order type.
The producer runs at most 4000 steps and a certificate of 4000 instances or more is not checked
(as `tests-shape` does at the shapes lane's tip: `Closures.polyRec` does not converge, and the
producer's instance list is quadratic). -/
def shapeOf (p : Program) (root : CId) : Bool × String :=
  match resTy p root with
  | none => (false, "no first-order result type")
  | some res =>
    let sc := Shape2.Produce.produce p root 400 4000
    if sc.insts.length ≥ 4000 then (false, "the producer did not converge (4000 instances)")
    else if !Shape2.certOk p sc then (false, "certOk refused the produced certificate")
    else if !shapeRootB p sc root (arityOf p root) res then
      (false, "the certificate does not list the root at its first-order type")
    else (true, "shape ok")

/-- A stored constant of type `Bool.true = Bool.false → False` (the witness `numeralBasisB` asks
for), if the environment has one. -/
def neKey? (env : IxCC.Grounding.KEnv) : Option IxCC.Grounding.KKey :=
  let cands := env.consts.filter fun ci => match ci.toConstantVal.type with
    | .forallE _ (.const f []) _ => f == Ix.Kernel.falseName
    | _ => false
  (cands.find? fun ci => IxCC.Grounding.boolTrueNeFalseB env ci.name).map (·.name)

/-- A stored constant of type `Bool.false = Bool.true → False` (the other orientation, which
`numeralBasisB` does not accept: reported only). -/
def neKeyRev? (env : IxCC.Grounding.KEnv) : Option IxCC.Grounding.KKey :=
  let d := IxCC.Grounding.eqE (.succ .zero) (.const IxCC.Grounding.boolKey [])
    (.const Ix.Kernel.boolFalseName []) (.const Ix.Kernel.boolTrueName [])
  (env.consts.find? fun ci => match ci.toConstantVal.type with
    | .forallE d' (.const f []) _ => decide (d' = d) && f == Ix.Kernel.falseName
    | _ => false).map (·.name)

def run : IO Bool := do
  let only ← IO.getEnv "GROUND_ONLY"
  let out ← IO.getStdout
  let mut rows : List (String × Nat × Nat × Nat × Nat) := []
  let mut hist : List (String × Nat) := []
  let mut shapeHist : List (String × Nat) := []
  let mut unloadable : List String := []
  let mut witnessed : List String := []
  for (family, dir) in families do
    if only.isSome && only != some family then continue
    let mut total := 0
    let mut accepted := 0
    let mut escapeFree := 0
    let mut separated := 0
    for (stem, ixe, eqs) in ← closuresOf dir do
      let label := s!"{family} {stem}"
      let loaded ← try
        let ld ← load ixe eqs
        pure (some ld)
      catch e =>
        IO.println s!"{label}: not loaded: {(toString e).take 300}"
        pure none
      match loaded with
      | none => unloadable := unloadable ++ [label]
      | some ld =>
        let env := ld.kernel.acc.env
        let ne := neKey? env
        let sep := match ne with
          | some kNe => numeralBasisB env kNe
          | none => false
        if ne.isSome || (neKeyRev? env).isSome then
          witnessed := witnessed ++ [s!"{label} (true≠false: {ne.isSome}, false≠true: {(neKeyRev? env).isSome})"]
        IO.println s!"{label}: {ld.src.roots.length} roots, {ld.mode}, numerals separated: {sep}"
        for (name, i) in ld.names.zipIdx do
          let some r := ld.src.roots[i]? | continue
          total := total + 1
          let srcI := { ld.src with roots := [r] }
          let t0 ← IO.monoMsNow
          match groundCheck ld.kernel srcI ld.checked ld.ann (ld.view i) r.1 with
          | .ok abi =>
            accepted := accepted + 1
            let (sok, sreason) := shapeOf srcI r.2
            let compiled := ld.mode == "compiled"
            let ef := sok && compiled
            if ef then escapeFree := escapeFree + 1
            else shapeHist := bump (if sok then "source only (the compiler declined)" else sreason) shapeHist
            let natRes := abi.result == ResTy.nat
            if sep && natRes then separated := separated + 1
            let efS := if ef then "escape-free" else if sok then "shape ok, source only" else s!"shape: {sreason}"
            IO.println s!"{label} {name}: accept, {showAbi abi}; {efS} ({(← IO.monoMsNow) - t0} ms)"
          | .error reason =>
            hist := bump reason hist
            IO.println s!"{label} {name}: refuse, {reason} ({(← IO.monoMsNow) - t0} ms)"
          out.flush
    rows := rows ++ [(family, total, accepted, escapeFree, separated)]
  IO.println "family: roots, accepted by groundCheck, escape-free (groundShapeCheck: also compiled and shaped), unique (a Nat result in an environment that separates numerals)"
  let mut tot := (0, 0, 0, 0)
  for (family, n, a, e, s) in rows do
    IO.println s!"  {family}: {n}, {a}, {e}, {s}"
    tot := (tot.1 + n, tot.2.1 + a, tot.2.2.1 + e, tot.2.2.2 + s)
  IO.println s!"  all: {tot.1}, {tot.2.1}, {tot.2.2.1}, {tot.2.2.2}"
  IO.println "first refusals of groundCheck:"
  for (k, n) in hist.mergeSort fun a b => a.2 ≥ b.2 do
    IO.println s!"  {n}  {k}"
  IO.println "accepted by groundCheck, not escape-free:"
  for (k, n) in shapeHist.mergeSort fun a b => a.2 ≥ b.2 do
    IO.println s!"  {n}  {k}"
  IO.println s!"closures storing a Bool.true/Bool.false separation: {witnessed}"
  if !unloadable.isEmpty then IO.println s!"not loaded: {unloadable}"
  IO.println s!"tests-grounding (pipeline): groundCheck accepted {tot.2.1} of {tot.1} roots, {tot.2.2.1} escape-free"
  return true

end IxCCTests.Grounding.Pipeline
