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
  args : Option (List Nat) := none
  out : Option String := none
  execPackage : Bool := false
  stats : Bool := false

def usage : String :=
  "usage: ixcc-aiur CLOSURE.ixe [--equations EQUATIONS.json | EQUATIONS.json] \
[--root NAME|ADDR|NAME=ADDR] [--args N,N,...] [-o PACKAGE.ixa] [--exec] [--stats]"

def parseNats (s : String) : Except String (List Nat) :=
  (s.splitOn ",").filter (· != "") |>.mapM fun w =>
    match w.toNat? with
    | some n => .ok n
    | none => .error s!"not a natural number: {w}"

def parse : List String → Options → Except String Options
  | [], o => .ok o
  | "--equations" :: path :: rest, o => parse rest { o with equations := some path }
  | "--root" :: name :: rest, o => parse rest { o with root := some name }
  | "--args" :: ns :: rest, o => do parse rest { o with args := some (← parseNats ns) }
  | "-o" :: path :: rest, o => parse rest { o with out := some path }
  | "--exec" :: rest, o => parse rest { o with execPackage := true }
  | "--stats" :: rest, o => parse rest { o with stats := true }
  | arg :: rest, o =>
    if arg.startsWith "-" then .error s!"unknown option {arg}"
    else if o.closure.isNone then parse rest { o with closure := some arg }
    else if o.equations.isNone then parse rest { o with equations := some arg }
    else .error s!"unexpected argument {arg}"

def showObs : Option Sem.Obs → String
  | some o => reprStr o
  | none => "none"

def printChipStats (chips : List (String × Nat × Nat × Nat)) (ms : Nat) : IO Unit := do
  IO.println s!"chips: {chips.length} ({ms} ms)"
  for (name, columns, sends, memory) in chips do
    IO.println s!"chip {name}: columns {columns}, calls {sends}, memory {memory}"

def run (o : Options) : IO UInt32 := do
  let some closure := o.closure
    | IO.eprintln usage; return 2
  let bytes ← IO.FS.readBinFile closure
  let start ← IO.monoMsNow
  let front ← match o.equations with
    | some eqPath =>
      let text ← IO.FS.readFile eqPath
      let json ← IO.ofExcept (Src.Hints.checkJsonText text >>= fun () => Lean.Json.parse text)
      IO.ofExcept (Driver.front bytes json o.root.toList)
    | none =>
      IO.ofExcept (Driver.frontAuto bytes o.root.toList)
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
  let arity := match o.args with
    | some ns => ns.length
    | none =>
      match fir.exports[0]?.bind fir.fun? with
      | some fd => fd.params.length
      | none => 0
  IO.println s!"shape: {Driver.shapeCheck front.levels arity} \
    (root 0 at {arity} Nat arguments; where true the claim has no stuck-source disjunct)"
  let mut agree := true
  if let some args := o.args then
    let start ← IO.monoMsNow
    let expected := Driver.firRun fir 0 args
    IO.println s!"fir: {reprStr expected} ({(← IO.monoMsNow) - start} ms)"
    let start ← IO.monoMsNow
    let actual := Driver.aiurRun fir linked args
    match actual with
    | .ok (value, obs) =>
      IO.println s!"aiur: value {reprStr value}, observation {showObs obs} ({(← IO.monoMsNow) - start} ms)"
    | .error e => IO.println s!"aiur: no derivation found: {e} ({(← IO.monoMsNow) - start} ms)"
    agree := match expected, actual with
      | .ok (some a), .ok (_, some b) => a == b
      | _, _ => false
    IO.println s!"agree: {agree}"
  if let some path := o.out then
    unless world.ok do
      IO.eprintln "ixcc-aiur: the world check failed; no package written"
      return 1
    unless agree do
      IO.eprintln "ixcc-aiur: the evaluators do not agree on a value; no package written"
      return 1
    let kind : CompiledCert.ArtifactKind := if o.execPackage then .execution else .program
    let start ← IO.monoMsNow
    let compiled ← IO.ofExcept (Driver.compilePackage linked kind (o.args.getD []))
    let elapsed := (← IO.monoMsNow) - start
    if o.stats then
      printChipStats compiled.chips elapsed
    Aiur.Artifact.write path compiled.bytes
    IO.println s!"package: {path}, {compiled.bytes.size} bytes, kind {compiled.kind.label}, \
      blake3 {compiled.digest} ({elapsed} ms)"
  else if o.stats then
    let start ← IO.monoMsNow
    let chips ← IO.ofExcept (Driver.chipStats linked)
    printChipStats chips ((← IO.monoMsNow) - start)
  return 0

end IxCC.AiurBackend.Main

def main (argv : List String) : IO UInt32 := do
  match IxCC.AiurBackend.Main.parse argv {} with
  | .ok o => IxCC.AiurBackend.Main.run o
  | .error e =>
    IO.eprintln s!"ixcc-aiur: {e}"
    IO.eprintln IxCC.AiurBackend.Main.usage
    return 2
