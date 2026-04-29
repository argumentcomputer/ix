module
public import Cli
public import Ix.Common
public import Ix.KernelCheck
public import Ix.Meta
public import Ix.Cli.ValidateCmd

public section

open Ix.KernelCheck

namespace Ix.Cli.CheckIxonCmd

private structure SeedSpec where
  prefixes : List Lean.Name := []
  exacts : List Lean.Name := []

private def SeedSpec.isEmpty (s : SeedSpec) : Bool :=
  s.prefixes.isEmpty && s.exacts.isEmpty

private def readNamesFile (path : String) : IO (List Lean.Name) := do
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n"
  pure <| lines.filterMap fun raw =>
    let cs := raw.toList.dropWhile Char.isWhitespace
    let trimmed := String.ofList (cs.reverse.dropWhile Char.isWhitespace).reverse
    if trimmed.isEmpty || trimmed.startsWith "#" then none
    else some trimmed.toName

private def resolveSeedSpec (p : Cli.Parsed) : IO (Option SeedSpec) := do
  let nsFlag := p.flag? "ns"
  let constsFlag := p.flag? "consts"
  let fileFlag := p.flag? "consts-file"
  if nsFlag.isNone && constsFlag.isNone && fileFlag.isNone then
    return none
  let mut prefixes : List Lean.Name := []
  let mut exacts : List Lean.Name := []
  if let some flag := nsFlag then
    let raw := flag.as! String
    prefixes := parsePrefixes raw
    if prefixes.isEmpty then
      IO.println s!"[check-ixon] warning: --ns '{raw}' parsed to empty list"
  if let some flag := constsFlag then
    let raw := flag.as! String
    let parsed := parsePrefixes raw
    if parsed.isEmpty then
      IO.println s!"[check-ixon] warning: --consts '{raw}' parsed to empty list"
    exacts := exacts ++ parsed
  if let some flag := fileFlag then
    let path := flag.as! String
    let parsed ← readNamesFile path
    if parsed.isEmpty then
      IO.println s!"[check-ixon] warning: --consts-file '{path}' yielded zero names"
    else
      IO.println s!"[check-ixon] --consts-file '{path}': read {parsed.length} name(s)"
    exacts := exacts ++ parsed
  let spec : SeedSpec := { prefixes, exacts }
  if spec.isEmpty then
    IO.println "[check-ixon] warning: filter flags supplied but parsed to empty selection"
  return some spec

private def selectNames (allNames : Array Lean.Name)
    (spec : Option SeedSpec) : IO (Array Lean.Name) := do
  match spec with
  | none => pure allNames
  | some s =>
    let exactSet : Std.HashSet Lean.Name :=
      s.exacts.foldl (fun acc n => acc.insert n) (Std.HashSet.emptyWithCapacity s.exacts.length)
    let mut missing : Array Lean.Name := #[]
    for n in s.exacts do
      if !allNames.contains n then
        missing := missing.push n
    if !missing.isEmpty then
      IO.println s!"[check-ixon] warning: {missing.size}/{s.exacts.length} exact name(s) not in env:"
      let shown := min 20 missing.size
      for n in missing[:shown] do
        IO.println s!"  - {n}"
      if missing.size > 20 then
        IO.println s!"  ... ({missing.size - 20} more not shown)"
    let seeds := allNames.filter fun n =>
      exactSet.contains n || s.prefixes.any (·.isPrefixOf n)
    IO.println s!"[check-ixon] filter: {s.prefixes.length} prefix(es), {s.exacts.length} exact(s) -> {seeds.size} seed constants"
    pure seeds

private def reportFailures (failures : Array (Lean.Name × String))
    (limit : Nat := 30) : IO Unit := do
  if failures.isEmpty then return
  IO.println s!"[check-ixon] {failures.size} failure(s):"
  let shown := min limit failures.size
  for (name, msg) in failures[:shown] do
    IO.println s!"  x {name}: {msg}"
  if failures.size > limit then
    IO.println s!"  ... ({failures.size - limit} more failures suppressed)"

private def commentLine (msg : String) : String :=
  let oneLine := msg.replace "\n" " | "
  s!"# {oneLine}"

private def writeFailuresFile
    (path : String)
    (envPath : String)
    (seedCount : Nat)
    (failures : Array (Lean.Name × String))
    : IO Unit := do
  let mut buf : String :=
    "# ix check-ixon failures\n"
    ++ s!"# env: {envPath}\n"
    ++ s!"# seeds: {seedCount}\n"
    ++ s!"# failures: {failures.size}\n\n"
  for (name, msg) in failures do
    buf := buf ++ commentLine msg ++ "\n" ++ s!"{name}\n\n"
  IO.FS.writeFile path buf
  IO.println s!"[check-ixon] wrote {failures.size} failure(s) to {path}"

def runCheckIxonCmd (p : Cli.Parsed) : IO UInt32 := do
  let some env := p.flag? "env"
    | p.printError "error: must specify --env"
      return 1
  let envPath := env.as! String
  let verbose := p.flag? "verbose" |>.isSome

  IO.println s!"Running Ix kernel check on serialized env {envPath}"
  let namesInEnv ← rsIxonNamesFFI envPath
  IO.println s!"Total checkable names in env: {namesInEnv.size}"

  let spec ← resolveSeedSpec p
  let seedNames ← selectNames namesInEnv spec
  if spec.isSome && seedNames.isEmpty then
    IO.println "[check-ixon] error: filter resolved to zero constants; refusing to run full-env check"
    return 1
  IO.println s!"[check-ixon] checking {seedNames.size} seed constant(s)"

  let expectPass : Array Bool := Array.replicate seedNames.size true
  let start ← IO.monoMsNow
  let results ← rsCheckIxonFFI envPath seedNames expectPass (!verbose)
  let elapsed := (← IO.monoMsNow) - start

  let mut passed := 0
  let mut failures : Array (Lean.Name × String) := #[]
  for i in [:seedNames.size] do
    match results[i]! with
    | none => passed := passed + 1
    | some err => failures := failures.push (seedNames[i]!, err.message)

  IO.println s!"[check-ixon] checked {seedNames.size} constants in {elapsed.formatMs}"
  IO.println s!"[check-ixon] {passed}/{seedNames.size} passed"
  reportFailures failures

  if let some flag := p.flag? "fail-out" then
    writeFailuresFile (flag.as! String) envPath seedNames.size failures

  IO.println s!"##check-ixon## {elapsed} {passed} {failures.size} {seedNames.size}"
  return if failures.isEmpty then 0 else 1

end Ix.Cli.CheckIxonCmd

open Ix.Cli.CheckIxonCmd in
private def withCmdName (cmd : Cli.Cmd) (name : String) : Cli.Cmd :=
  match cmd with
  | Cli.Cmd.init m run subCmds ext =>
      Cli.Cmd.init { m with name := name } run subCmds ext

open Ix.Cli.CheckIxonCmd in
def checkIxonCmd : Cli.Cmd := withCmdName `[Cli|
  checkIxon VIA runCheckIxonCmd;
  "Typecheck a serialized Ixon environment through the Ix Rust kernel"

  FLAGS:
    env           : String; "Path to a serialized Ixon.Env file produced by `ix compile --out`"
    ns            : String; "Comma-separated Lean name prefixes to check"
    consts        : String; "Comma-separated exact constant names to check"
    "consts-file" : String; "Path to a file with one constant name per line. '#' comments and blank lines ignored."
    "fail-out"    : String; "Write failing constant names to this path"
    verbose;                "Log every constant on its own line (default: quiet ephemeral progress)"
] "check-ixon"

end
