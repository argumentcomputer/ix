import IxCCTests.Src.Steps
import IxCCTests.Corpus.Manifest
import IxCCTests.Src.Bench

/-! # `src-steps`: SrcEval step counts

```text
src-steps CLOSURE.ixe --equations EQ.json --root NAME [--no-typecheck] [--clock K] ARG...
src-steps --manifest CORPUS.json [--no-typecheck] [--clock K]
src-steps --manifests [--no-typecheck] [--clock K]
```

The first form runs `ixcc`'s front end on the closure (ingress with erased
typing unless `--no-typecheck`, then the producer's front half), runs root
`NAME` on the `Nat` arguments under SrcEval at clock `K` (default 2,000,000; the clock bounds the nesting depth of
charged steps, so a deeper run, such as a boundary case that never returns,
reports a timeout), and
prints one JSON object (`ixcc/src-steps/1`): the closure, root, arguments and
clock; the result (`{"outcome": "ok", "value": …}` read back as `Src.readback`
reads it, or the failure); the step counts (`charged` and its parts, the
uncharged rule applications, term nodes); and `leastClock`, the least clock at
which `Src.run` reaches the same outcome (`null` on a timeout). The unit is
defined in `docs/source-steps.md`. A front-end decline prints an object with
`declined` (stage, code and the front end's message) and exits 1.

`--manifest` runs every case of every root of an `ixcc/corpus/1` manifest that
the corpus suite runs at the source level (roots compiled `together` are
ingested together, as there), one object per case, per declined root, or per
skipped case (`skipped`: an argument of at least `2⁶³`, no source value, or
Lean's interpreter failing on it); `--manifests` runs every registered
family. They exit 0 when every line was produced (declines included, since a
family records its declines), 1 if a counted run disagreed with `Src.run`.
Paths are relative to the package root, as in the manifests. SrcEval nests a
native frame per recursive call, so the tool re-runs itself once with a large
Lean stack (`LEAN_STACK_SIZE_KB`, `stackKb`), as `tests-corpus` does. -/

namespace IxCCTests.Src.StepsTool

open IxCC IxCC.Src IxCCTests.Src.Steps
open IxCCTests.Corpus (Family Fixture Root families)
open System (FilePath)

structure Options where
  closure : Option String := none
  equations : Option String := none
  roots : List String := []
  manifests : List String := []
  allManifests : Bool := false
  typecheck : Bool := true
  clock : Nat := 2000000
  args : List Nat := []

/-- The child's Lean stack: 16 GiB of address space, touched only as deep as a
run goes (the default clock bounds that depth). -/
def stackKb : Nat := 16 * 1024 * 1024

def usage : String :=
  "usage: src-steps CLOSURE.ixe --equations EQ.json --root NAME [--no-typecheck] [--clock K] ARG...\n" ++
  "       src-steps --manifest CORPUS.json [--no-typecheck] [--clock K]\n" ++
  "       src-steps --manifests [--no-typecheck] [--clock K]"

def parse : Options → List String → Except String Options
  | o, [] => .ok o
  | o, "--equations" :: f :: rest => parse { o with equations := some f } rest
  | o, "--root" :: n :: rest => parse { o with roots := o.roots ++ [n] } rest
  | o, "--manifest" :: f :: rest => parse { o with manifests := o.manifests ++ [f] } rest
  | o, "--manifests" :: rest => parse { o with allManifests := true } rest
  | o, "--no-typecheck" :: rest => parse { o with typecheck := false } rest
  | o, "--clock" :: k :: rest =>
    match k.toNat? with
    | some k => parse { o with clock := k } rest
    | none => .error s!"--clock takes a number, not {k}"
  | o, a :: rest =>
    if a.startsWith "--" then .error s!"unknown option {a}"
    else if o.closure.isNone then parse { o with closure := some a } rest
    else match a.toNat? with
      | some n => parse { o with args := o.args ++ [n] } rest
      | none => .error s!"an argument must be a natural number, not {a}"

def emit (j : Lean.Json) : IO Unit := do
  IO.println j.compress
  (← IO.getStdout).flush

/-- A case the corpus suite does not run at the source level (`tests-corpus`):
an argument of at least `2⁶³`, no source value in the manifest, or Lean's
interpreter failing on it. Such a case need not return in practice (a count
over `0 … 2⁶³`, say), so the tool skips it. -/
def skipReason (r : Root) (c : IxCCTests.Corpus.Case) : Option String :=
  if c.args.any (· ≥ IxCCTests.Corpus.limit) then some "an argument of at least 2^63"
  else if (c.sourceObs r).isNone then some "no source value in the manifest"
  else if c.leanFails then some "Lean's interpreter fails on it"
  else none

def skippedJson (closure root : String) (args : List Nat) (why : String) : Lean.Json :=
  Lean.Json.mkObj [("format", (format : Lean.Json)), ("closure", (closure : Lean.Json)),
    ("root", (root : Lean.Json)), ("args", Lean.Json.arr (args.map fun (n : Nat) => (n : Lean.Json)).toArray),
    ("skipped", (why : Lean.Json))]

/-- One line per case of root `name` (ingested with `together`): a measured
run, or the decline. Returns whether every counted run agreed with `Src.run`. -/
def runRoot (closure : FilePath) (equations : FilePath) (label name : String) (together : List String)
    (cases : List (List Nat)) (typecheck : Bool) (clock : Nat) : IO (Bool × Bool) := do
  let bytes ← IO.FS.readBinFile closure
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile equations))
  match ← IO.lazyPure fun _ => front bytes json (name :: together) typecheck with
  | .error e =>
    emit (declinedJson label name e)
    return (true, false)
  | .ok (inp, ps) =>
    let root ← IO.ofExcept (rootOf inp ps.src name)
    let mut agreed := true
    for args in cases do
      match ← IO.lazyPure fun _ => measure ps.src root args clock with
      | .ok m => emit (runJson label name args ps.src ps.checked m)
      | .error msg =>
        agreed := false
        IO.eprintln s!"src-steps: {label} {name} {args}: {msg}"
    return (agreed, true)

def runManifest (path : String) (typecheck : Bool) (clock : Nat) : IO Bool := do
  let m ← Family.read path
  let dir : FilePath := m.directory
  let mut ok := true
  for f in m.fixtures do
    for r in f.roots do
      let label := (dir / f.closure.path).toString
      for c in r.cases do
        if let some why := skipReason r c then emit (skippedJson label r.name c.args why)
      let run := r.cases.filter fun c => (skipReason r c).isNone
      let (agreed, _) ← runRoot (dir / f.closure.path) (dir / f.equations.path)
        label r.name r.together (run.map (·.args)) typecheck clock
      ok := ok && agreed
  return ok

def main (args : List String) : IO UInt32 := do
  -- re-run once with a large stack for SrcEval's native recursion
  if (← IO.getEnv "IXCC_SRC_STEPS_CHILD").isNone then
    let env : Array (String × Option String) :=
      #[("LEAN_STACK_SIZE_KB", some (toString stackKb)),
        ("IXCC_SRC_STEPS_CHILD", some "1")]
    let child ← IO.Process.spawn { cmd := (← IO.appPath).toString, args := args.toArray, env := env }
    return ← child.wait
  match parse {} args with
  | .error e =>
    IO.eprintln s!"src-steps: {e}\n{usage}"
    return 2
  | .ok o =>
    if o.allManifests || !o.manifests.isEmpty then
      let paths := if o.allManifests then families.map (·.toString) else o.manifests
      let mut ok := true
      for p in paths do ok := ok && (← runManifest p o.typecheck o.clock)
      return if ok then 0 else 1
    match o.closure, o.equations, o.roots with
    | some c, some e, [r] =>
      let (agreed, ran) ← runRoot c e c r [] [o.args] o.typecheck o.clock
      return if !ran then 1 else if agreed then 0 else 1
    | _, _, _ =>
      IO.eprintln s!"src-steps: a closure, --equations and exactly one --root are required\n{usage}"
      return 2

end IxCCTests.Src.StepsTool
