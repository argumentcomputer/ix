import Lean

/-! # Verifying-key gate (`Scripts/CheckFormalKeys.lean`)

Fails when the certified formal Aiur programs' keys differ from the committed pins
in `tools/formal-aiur.keys`. Replaces `tools/check-formal-keys.sh`.

## What it protects

`tools/formal-aiur.keys` pins, for the IxVM, recursive verifier, and aggregation
programs, the program identity (the content digest of the compiled artifact) and
the BLAKE3 digest of the verifying key under the default STARK parameters.
`ix verify` and the aggregate acceptance check (`Ix.Cli.FormalAggregate.context`,
`accept`) embed the pins and reject keys that differ, and aggregate proofs commit
to the pinned IxVM and aggregation keys. `lake exe formal-keys`
(`Tests/FormalKeys.lean`) derives the pin file from the checkout's programs,
compiling any missing from the compiled-program cache, and this script compares
it with the committed file.

## Updating the pins

A mismatch means the compiled circuits or programs changed. Do not update the
pins merely to make this script pass: review the change, then commit the new
pins on their own, stating why the circuits changed. Regenerate them with:

```sh
lake env lean --run Scripts/CheckFormalKeys.lean --update
```

Usage:
  `lake env lean --run Scripts/CheckFormalKeys.lean [--check | --update | --self-test | --help]`
-/

namespace CheckFormalKeys

open System

def pinRelPath : FilePath := "tools" / "formal-aiur.keys"

def usage : String :=
  "usage: lake env lean --run Scripts/CheckFormalKeys.lean [--check | --update | --self-test | --help]\n\n" ++
  "Verifying-key gate comparing `lake exe formal-keys` output against `tools/formal-aiur.keys`."

inductive Mode where
  | check
  | update
  | selfTest
  | help
  deriving BEq, Repr

def parseArgs : List String → Except String Mode
  | [] | ["--check"] => .ok .check
  | ["--update"] => .ok .update
  | ["--self-test"] => .ok .selfTest
  | ["--help"] | ["-h"] => .ok .help
  | other => .error s!"unexpected arguments: {" ".intercalate other}"

/-- Find the repository root from `dir` by walking up to `lakefile.lean`. -/
partial def findRepoRoot (dir : FilePath) : IO FilePath := do
  if ← (dir / "lakefile.lean").pathExists then
    return dir
  match dir.parent with
  | some parent =>
    if parent == dir then
      throw <| IO.userError "could not locate repository root (lakefile.lean)"
    findRepoRoot parent
  | none =>
    throw <| IO.userError "could not locate repository root (lakefile.lean)"

/-- Render a concise line-by-line diff between committed and derived pin texts. -/
def formatLineDiff (committed actual : String) : String := Id.run do
  let oldLines := (committed.splitOn "\n").toArray
  let newLines := (actual.splitOn "\n").toArray
  let n := max oldLines.size newLines.size
  let mut out : Array String := #[]
  for i in [:n] do
    let a := oldLines[i]?
    let b := newLines[i]?
    if a != b then
      if let some l := a then
        out := out.push s!"- (line {i + 1}) {l}"
      if let some l := b then
        out := out.push s!"+ (line {i + 1}) {l}"
  return "\n".intercalate out.toList

def ensure (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

def selfTest : IO Unit := do
  ensure ((parseArgs []).toOption == some .check) "default mode is check"
  ensure ((parseArgs ["--check"]).toOption == some .check) "explicit --check mode"
  ensure ((parseArgs ["--update"]).toOption == some .update) "--update mode"
  ensure ((parseArgs ["--self-test"]).toOption == some .selfTest) "--self-test mode"
  ensure ((parseArgs ["--help"]).toOption == some .help) "--help mode"
  ensure ((parseArgs ["-h"]).toOption == some .help) "-h mode"
  ensure ((parseArgs ["--bogus"]).toOption.isNone) "reject unknown flag"
  ensure ((parseArgs ["--check", "--update"]).toOption.isNone) "reject conflicting flags"
  let diff := formatLineDiff "a\nb\nc\n" "a\nB\nc\n"
  ensure (diff == "- (line 2) b\n+ (line 2) B") s!"unexpected diff output: {diff}"
  ensure (formatLineDiff "same\n" "same\n" == "") "identical inputs yield empty diff"
  IO.println "[check-formal-keys] self-tests passed."

/-- When invoked via `lake env lean --run`, `lake env` injects `LEAN_SYSROOT`
equal to the toolchain sysroot, which differs from an outer shell where
`LEAN_SYSROOT` is unset and would invalidate `rustInputDeps` / `lean-ffi`.
Clear it for child `lake` calls when `lake env` injected it. -/
def lakeChildEnv : IO (Array (String × Option String)) := do
  if (← IO.getEnv "LEAN_RECURSION_COUNT").isSome then
    let sysroot := (← Lean.findSysroot).toString
    if (← IO.getEnv "LEAN_SYSROOT") == some sysroot then
      return #[("LEAN_SYSROOT", none)]
  return #[]

def run (mode : Mode) : IO UInt32 := do
  let repoRoot ← findRepoRoot (← IO.currentDir)
  let env ← lakeChildEnv
  let pinPath := repoRoot / pinRelPath

  -- Build `formal-keys` quietly on success; surface diagnostics on failure.
  let buildOut ← IO.Process.output {
    cmd := "lake"
    args := #["build", "formal-keys"]
    cwd := some repoRoot
    env
  }
  unless buildOut.exitCode == 0 do
    if !buildOut.stdout.isEmpty then IO.eprint buildOut.stdout
    if !buildOut.stderr.isEmpty then IO.eprint buildOut.stderr
    IO.eprintln s!"[check-formal-keys] `lake build formal-keys` failed with exit code {buildOut.exitCode}"
    return buildOut.exitCode

  -- Derive current pin file contents from the checkout's certified programs.
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["exe", "formal-keys"]
    cwd := some repoRoot
    env
    stdout := .piped
    stderr := .inherit
  }
  let actual ← child.stdout.readToEnd
  let exeCode ← child.wait
  unless exeCode == 0 do
    IO.eprintln s!"[check-formal-keys] `lake exe formal-keys` failed with exit code {exeCode}"
    return exeCode

  if mode == .update then
    IO.FS.writeFile pinPath actual
    IO.println s!"updated {pinRelPath}"
    IO.println "commit it on its own, after review, with the reason the circuits changed"
    return 0

  unless ← pinPath.pathExists do
    IO.eprintln s!"VERIFYING KEYS MISSING: committed pin file {pinRelPath} does not exist"
    return 1

  let committed ← IO.FS.readFile pinPath
  if committed == actual then
    IO.println s!"verifying keys match {pinRelPath}"
    return 0

  IO.eprintln s!"VERIFYING KEYS CHANGED: the certified programs differ from {pinRelPath}"
  let diffText := formatLineDiff committed actual
  unless diffText.isEmpty do
    IO.eprintln diffText
  IO.eprintln ""
  IO.eprintln "Review the change. If it is intended, update the pins in a separate commit (see Scripts/CheckFormalKeys.lean)."
  return 1

end CheckFormalKeys

def main (args : List String) : IO UInt32 := do
  match CheckFormalKeys.parseArgs args with
  | .error e =>
    IO.eprintln s!"error: {e}\n{CheckFormalKeys.usage}"
    return 2
  | .ok .help =>
    IO.println CheckFormalKeys.usage
    return 0
  | .ok .selfTest =>
    CheckFormalKeys.selfTest
    return 0
  | .ok mode =>
    CheckFormalKeys.run mode
