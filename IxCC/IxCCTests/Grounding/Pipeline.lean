import IxCC.Recheck.Produce
import IxCC.Recheck.Proof.Front
import IxCCCorrect.GroundCheck

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

def run : IO Bool := do
  let only ← IO.getEnv "GROUND_ONLY"
  let out ← IO.getStdout
  let mut rows : List (String × Nat × Nat) := []
  let mut hist : List (String × Nat) := []
  let mut unloadable : List String := []
  for (family, dir) in families do
    if only.isSome && only != some family then continue
    let mut total := 0
    let mut accepted := 0
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
        IO.println s!"{label}: {ld.src.roots.length} roots, {ld.mode}"
        for (name, i) in ld.names.zipIdx do
          let some r := ld.src.roots[i]? | continue
          total := total + 1
          let srcI := { ld.src with roots := [r] }
          let t0 ← IO.monoMsNow
          match groundCheck ld.kernel srcI ld.checked ld.ann (ld.view i) r.1 with
          | .ok abi =>
            accepted := accepted + 1
            IO.println s!"{label} {name}: accept, {showAbi abi} ({(← IO.monoMsNow) - t0} ms)"
          | .error reason =>
            hist := bump reason hist
            IO.println s!"{label} {name}: refuse, {reason} ({(← IO.monoMsNow) - t0} ms)"
          out.flush
    rows := rows ++ [(family, total, accepted)]
  IO.println "family: roots, accepted by groundCheck"
  let mut tot := (0, 0)
  for (family, n, a) in rows do
    IO.println s!"  {family}: {n}, {a}"
    tot := (tot.1 + n, tot.2 + a)
  IO.println s!"  all: {tot.1}, {tot.2}"
  IO.println "first refusals:"
  for (k, n) in hist.mergeSort fun a b => a.2 ≥ b.2 do
    IO.println s!"  {n}  {k}"
  if !unloadable.isEmpty then IO.println s!"not loaded: {unloadable}"
  IO.println s!"tests-grounding (pipeline): groundCheck accepted {tot.2} of {tot.1} roots"
  return true

end IxCCTests.Grounding.Pipeline
