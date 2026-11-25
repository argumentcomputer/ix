import IxCCAiur.Driver

/-! # `ixcc-aiur`

```text
ixcc-aiur CLOSURE.ixe EQUATIONS.json [--root NAME] [--args N,N,…] [-o PACKAGE.ixa] [--stats]
```

Takes one root of a closure through the front half (`Recheck.runFir`), the
lowering and Formal Aiur's preparation; evaluates the world check on the
prepared source (`World.checkWorld`, the hypothesis of the theorems in
`IxCCAiur.Claim`); evaluates the root on the `Nat` arguments at Fir and on
Aiur's evaluator; and, when the check holds and the two observations agree,
writes the execution package for that invocation (`Driver.package`).
`--stats` prints the compiled chips. With several roots, `--root` selects
one; the entry is export 0 of what is selected.

It proves nothing itself: the package goes to the Rust host
(`cargo run --release -p aiur --features parallel --example ixcc_prove`). -/

open IxCC IxCC.AiurBackend

namespace IxCC.AiurBackend.Main

structure Options where
  closure : Option String := none
  equations : Option String := none
  root : Option String := none
  args : List Nat := []
  out : Option String := none
  stats : Bool := false

def usage : String :=
  "usage: ixcc-aiur CLOSURE.ixe EQUATIONS.json [--root NAME] [--args N,N,...] [-o PACKAGE.ixa] [--stats]"

def parseNats (s : String) : Except String (List Nat) :=
  (s.splitOn ",").filter (· != "") |>.mapM fun w =>
    match w.toNat? with
    | some n => .ok n
    | none => .error s!"not a natural number: {w}"

def parse : List String → Options → Except String Options
  | [], o => .ok o
  | "--root" :: name :: rest, o => parse rest { o with root := some name }
  | "--args" :: ns :: rest, o => do parse rest { o with args := ← parseNats ns }
  | "-o" :: path :: rest, o => parse rest { o with out := some path }
  | "--stats" :: rest, o => parse rest { o with stats := true }
  | arg :: rest, o =>
    if arg.startsWith "-" then .error s!"unknown option {arg}"
    else if o.closure.isNone then parse rest { o with closure := some arg }
    else if o.equations.isNone then parse rest { o with equations := some arg }
    else .error s!"unexpected argument {arg}"

def showObs : Option Sem.Obs → String
  | some o => reprStr o
  | none => "none"

def run (o : Options) : IO UInt32 := do
  let (some closure, some equations) := (o.closure, o.equations)
    | IO.eprintln usage; return 2
  let bytes ← IO.FS.readBinFile closure
  let text ← IO.FS.readFile equations
  let json ← IO.ofExcept (Src.Hints.checkJsonText text >>= fun () => Lean.Json.parse text)
  let start ← IO.monoMsNow
  let front ← IO.ofExcept (Driver.front bytes json o.root.toList)
  let fir := front.levels.fir
  IO.println s!"front: roots {front.input.names}, fir functions {fir.funList.length}, \
    constructors {fir.ctors.length}, exports {fir.exports.length} ({(← IO.monoMsNow) - start} ms)"
  let start ← IO.monoMsNow
  let linked ← IO.ofExcept (Driver.link fir 0)
  IO.println s!"lowered: {linked.lowered.functions.length} functions, entry {linked.entry} \
    ({(← IO.monoMsNow) - start} ms)"
  let world := Driver.worldReport linked
  IO.println s!"world: tables {world.tables}, library {world.library}, functions {world.functions}, \
    refuses changed bodies and a changed table {world.refuses}"
  unless world.failing.isEmpty do
    IO.println s!"world: lowered functions that differ from the prepared source: {world.failing}"
  IO.println s!"shape: {Driver.shapeCheck front.levels o.args.length} \
    (root 0 at {o.args.length} Nat arguments; where true the claim has no stuck-source disjunct)"
  let start ← IO.monoMsNow
  let expected := Driver.firRun fir 0 o.args
  IO.println s!"fir: {reprStr expected} ({(← IO.monoMsNow) - start} ms)"
  let start ← IO.monoMsNow
  let actual := Driver.aiurRun fir linked o.args
  match actual with
  | .ok (value, obs) =>
    IO.println s!"aiur: value {reprStr value}, observation {showObs obs} ({(← IO.monoMsNow) - start} ms)"
  | .error e => IO.println s!"aiur: no derivation found: {e} ({(← IO.monoMsNow) - start} ms)"
  let agree := match expected, actual with
    | .ok (some a), .ok (_, some b) => a == b
    | _, _ => false
  IO.println s!"agree: {agree}"
  if o.stats then
    let start ← IO.monoMsNow
    let chips ← IO.ofExcept (Driver.chipStats linked)
    IO.println s!"chips: {chips.length} ({(← IO.monoMsNow) - start} ms)"
    for (name, columns, sends, memory) in chips do
      IO.println s!"chip {name}: columns {columns}, calls {sends}, memory {memory}"
  if let some path := o.out then
    unless world.ok do
      IO.eprintln "ixcc-aiur: the world check failed; no package written"
      return 1
    unless agree do
      IO.eprintln "ixcc-aiur: the evaluators do not agree on a value; no package written"
      return 1
    let start ← IO.monoMsNow
    let package ← IO.ofExcept (Driver.package linked o.args)
    Aiur.Artifact.write path package
    IO.println s!"package: {path}, {package.size} bytes ({(← IO.monoMsNow) - start} ms)"
  return 0

end IxCC.AiurBackend.Main

def main (argv : List String) : IO UInt32 := do
  match IxCC.AiurBackend.Main.parse argv {} with
  | .ok o => IxCC.AiurBackend.Main.run o
  | .error e =>
    IO.eprintln s!"ixcc-aiur: {e}"
    IO.eprintln IxCC.AiurBackend.Main.usage
    return 2
