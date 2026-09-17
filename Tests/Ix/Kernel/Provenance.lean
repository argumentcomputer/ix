/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Ix.Kernel.ImportManifest

/-! # Provenance gate for the ported model

Checks, against `Tests.Ix.Kernel.ImportManifest`:

* the inventory of `Ix/Kernel/**/*.lean` is exactly the ported targets plus
  the authored modules (a file added or removed without a manifest update
  fails);
* every ported file has the recorded SHA-256 and starts with the port header
  naming its source;
* the license and notice copies are present with their recorded hashes;
* with `--source <path>`, every recorded source hash matches the file at the
  pinned revision in that jj workspace (`jj file show`).

Hashing shells out to `sha256sum`. Exit code 0 on success, 1 on any failure. -/

open System Tests.Ix.Kernel.ImportManifest

private def fail (message : String) : IO Unit := throw (IO.userError message)

private def need (ok : Bool) (message : String) : IO Unit := unless ok do fail message

private def sha256 (path : FilePath) : IO String := do
  let result ← IO.Process.output { cmd := "sha256sum", args := #["--", path.toString] }
  need (result.exitCode == 0) result.stderr
  return (result.stdout.splitOn " ").headD ""

private def sha256String (contents : String) : IO String := do
  IO.FS.withTempFile fun handle path => do
    handle.putStr contents
    handle.flush
    sha256 path

private def sameFiles (what : String) (actual expected : Array String) : IO Unit := do
  let actual := actual.qsort (· < ·)
  let expected := expected.qsort (· < ·)
  unless actual == expected do
    let missing := expected.filter (!actual.contains ·)
    let extra := actual.filter (!expected.contains ·)
    fail s!"{what} inventory changed; missing {missing}, unexpected {extra}"

private def checkRow (row : PortedFile) (header : Bool) : IO Unit := do
  need (← (FilePath.mk row.target).pathExists) s!"missing ported file: {row.target}"
  need ((← sha256 row.target) == row.targetSha256) s!"ported content changed: {row.target}"
  if header then
    let contents ← IO.FS.readFile row.target
    need (contents.startsWith (portHeader row.source)) s!"port header missing or changed: {row.target}"

private def checkSource (workspace : String) (row : PortedFile) : IO Unit := do
  let shown ← IO.Process.output {
    cmd := "jj", args := #["-R", workspace, "file", "show", "-r", sourceRevision, s!"root:\"{row.source}\""] }
  need (shown.exitCode == 0) s!"cannot read {row.source} at {sourceRevision}: {shown.stderr}"
  need ((← sha256String shown.stdout) == row.sourceSha256) s!"source hash mismatch: {row.source}"

def main (args : List String) : IO UInt32 := do
  try
    let workspace? ← match args with
      | [] => pure none
      | ["--source", path] => pure (some path)
      | _ => fail "usage: kernel-provenance [--source <old-ix-workspace>]"; pure none
    let files := ((← (FilePath.mk "Ix/Kernel").walkDir).filter (·.extension == some "lean")).map (·.toString)
    let files := if ← (FilePath.mk "Ix/Kernel.lean").pathExists then files.push "Ix/Kernel.lean" else files
    let files := if ← (FilePath.mk "Ix/Address/Core.lean").pathExists then files.push "Ix/Address/Core.lean" else files
    sameFiles "Ix/Kernel source" files (ported.map (·.target) ++ authored)
    for row in ported do checkRow row true
    for row in licenses do checkRow row false
    if let some workspace := workspace? then
      for row in ported ++ licenses do checkSource workspace row
    IO.println s!"Kernel provenance OK: {ported.size} ported modules, {authored.size} authored modules, {licenses.size} license files{if workspace?.isSome then "; source hashes verified" else ""}."
    return 0
  catch e =>
    IO.eprintln s!"kernel-provenance: {e}"
    return 1
