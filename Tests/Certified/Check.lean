/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean
import Tests.Certified.ImportManifest

/-! Independent provenance and byte/command regressions for the maintained
certified adapters. All historical inputs come from the local frozen archive. -/

open Lean System Tests.Certified.ImportManifest

namespace Tests.Certified.Check

private def need (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def run (cmd : String) (args : Array String) : IO IO.Process.Output := do
  let result ← IO.Process.output { cmd, args }
  need (result.exitCode == 0) s!"{cmd} failed ({result.exitCode}): {result.stdout}{result.stderr}"
  return result

private def sha256 (path : FilePath) : IO String := do
  return ((← run "sha256sum" #["--", path.toString]).stdout.splitOn " ").headD ""

private def files (directory : FilePath) : IO (Array String) := do
  let mut result := #[]
  for path in ← directory.walkDir do
    unless ← path.isDir do
      result := result.push ((path.toString.drop (directory.toString.length + 1)).toString)
  return result.qsort (· < ·)

private def compareTree (expected actual : FilePath) (jsonEquivalent : Bool := false) : IO Unit := do
  let expectedFiles ← files expected
  let actualFiles ← files actual
  need (expectedFiles == actualFiles) s!"fixture inventory differs: {expected} / {actual}"
  for relative in expectedFiles do
    let old ← IO.FS.readBinFile (expected / relative)
    let current ← IO.FS.readBinFile (actual / relative)
    if old == current then continue
    if jsonEquivalent && (FilePath.mk relative).extension == some "json" then
      let old ← IO.ofExcept (Json.parse (String.fromUTF8! old))
      let current ← IO.ofExcept (Json.parse (String.fromUTF8! current))
      need (old == current) s!"JSON protocol value differs: {relative}"
    else throw (IO.userError s!"fixture bytes differ: {relative} ({expected} / {actual})")

private def unpack (directory : FilePath) : IO Unit := do
  need ((← sha256 archive) == archiveSha256) "frozen C7 handoff archive identity changed"
  IO.FS.createDirAll directory
  let _ ← run "tar" #["-xzf", archive, "--no-same-owner", "--no-same-permissions", "-C", directory.toString]
  for row in selected do
    need ((← sha256 (directory / "adapters" / row.source)) == row.sourceSha256)
      s!"frozen adapter source identity changed: {row.source}"
    if let some target := row.target then
      need ((← sha256 target) == row.importedSha256)
        s!"maintained adapter changed; review import manifest: {target}"
  IO.println s!"C7 provenance passed: {selected.size} frozen sources, {(selected.filter (·.target.isSome)).size} maintained ports."

private def nativeCases := #[
  ("feature", "certified-feature-tests", none),
  ("ordinary", "certified-ordinary-tests", none),
  ("vm", "certified-vm-tests", none),
  ("source", "certified-source-tests", some "inputs"),
  ("fidelity", "certified-fidelity-tests", some "fidelity-inputs"),
  ("claim", "certified-claim-tests", some "claim-inputs"),
  ("modeled", "certified-modeled-tests", some "modeled-inputs")]

private def compareNative (frozen actual : FilePath) : IO Unit := do
  for (label, _, _) in nativeCases do
    need ((← IO.FS.readFile (frozen / s!"evidence/c7/{label}-tests.txt")) ==
      (← IO.FS.readFile (actual / s!"{label}-tests.txt"))) s!"native report differs: {label}"
    if #["source", "fidelity", "claim", "modeled"].contains label then
      need ((← IO.FS.readFile (frozen / s!"evidence/c7/{label}-loader.txt")) ==
        (← IO.FS.readFile (actual / s!"{label}-loader.txt"))) s!"loader report differs: {label}"
  for (old, current) in #[
      ("c5/inputs", "inputs"), ("c6/fidelity-inputs", "fidelity-inputs"),
      ("c7/claim-inputs", "claim-inputs"), ("c7/modeled-inputs", "modeled-inputs")] do
    compareTree (frozen / "evidence" / old) (actual / current)
  IO.println "Native reports and all generated source/envelope fixtures match frozen C7 bytes."

private def compareCLI (frozen actual : FilePath) : IO Unit := do
  for (old, current) in #[
      ("c5/cli-inputs", "cli-source"), ("c7/claim-cli-inputs", "cli-claims"),
      ("c7/modeled-cli-inputs", "cli-modeled")] do
    -- The new Lean driver prints JSON differently. Compare parsed protocol
    -- values; source, envelope, stdout and stderr remain byte-exact checks.
    compareTree (frozen / "evidence" / old) (actual / current) true
  IO.println "All CLI scenarios match the frozen inventory, protocol values, source/envelope bytes and process results."

private def runNative (frozen output : FilePath) : IO Unit := do
  for (label, executable, directory) in nativeCases do
    let args := directory.toArray.map (fun item => (output / FilePath.mk item).toString)
    let result ← run s!".lake/build/bin/{executable}" args
    IO.FS.writeFile (output / s!"{label}-tests.txt") result.stdout
    IO.FS.writeFile (output / s!"{label}-loader.txt") result.stderr
    IO.println s!"Native {label} tests passed."
  compareNative frozen output

private def runCLI (frozen output : FilePath) : IO Unit := do
  for (kind, inputs, target) in #[
      ("source", "inputs", "cli-source"), ("claims", "claim-inputs", "cli-claims"),
      ("modeled", "modeled-inputs", "cli-modeled")] do
    let result ← run ".lake/build/bin/certified-cli-tests" #[kind,
      ".lake/build/bin/certified-check", ".lake/build/bin/certified-claim-check",
      (output / inputs).toString, (output / target).toString]
    IO.print s!"CLI {kind}: {result.stdout}"
  compareCLI frozen output

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.FS.withTempDir fun directory => do
      let frozen := directory / "frozen"
      let output := directory / "actual"
      unpack frozen
      IO.FS.createDirAll output
      runNative frozen output
      runCLI frozen output
    IO.println "Certified adapter checks passed."
    return 0
  | ["--compare", frozen, actual] =>
    compareNative frozen actual
    compareCLI frozen actual
    return 0
  | _ =>
    IO.eprintln "usage: certified-adapter-tests [--compare FROZEN_DIRECTORY ACTUAL_DIRECTORY]"
    return 2

end Tests.Certified.Check

def main := Tests.Certified.Check.main
