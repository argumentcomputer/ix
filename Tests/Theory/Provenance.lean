/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean
import Tests.Theory.ImportManifest
import Tests.Theory.NamedManifest

open System Tests.Theory.ImportManifest

private def need (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def sha256 (path : FilePath) : IO String := do
  let result ← IO.Process.output { cmd := "sha256sum", args := #["--", path.toString] }
  need (result.exitCode == 0) result.stderr
  return (result.stdout.splitOn " ").headD ""

private def sameFiles (actual expected : Array String) : IO Unit :=
  need (actual.qsort (· < ·) == expected.qsort (· < ·)) "theory source inventory changed; review import provenance"

def main (args : List String) : IO Unit := do
  need (args.length ≤ 1) "usage: lake env lean --run Tests/Theory/Provenance.lean [CON_LECHE_REPOSITORY]"
  let actual := ((← (FilePath.mk "Ix/Theory").walkDir).filter (·.extension == some "lean")).map (·.toString)
  let named := actual.filter (·.startsWith "Ix/Theory/Named/")
  sameFiles ((actual.filter (!·.startsWith "Ix/Theory/Named/")).push "Ix/Theory.lean")
    (selected.map (·.target))
  sameFiles named ((Tests.Theory.NamedManifest.selected.map (·.target)).push
    "Ix/Theory/Named/Std/AxiomAudit.lean")
  need (← (FilePath.mk "Ix/Theory/Named/LICENSE").pathExists) "missing named-specification Apache license"
  need (← (FilePath.mk "Ix/Theory/Named/NOTICE").pathExists) "missing named-specification attribution"
  for row in selected do
    let contents ← IO.FS.readFile row.target
    need (!(contents.contains "import Ix.Theory.Named"))
      s!"set-model foundation depends on named checker proof support: {row.target}"
  let mut ports := #[]
  for directory in ["Ix/Theory/Model/SetTheory", "Ix/Theory/Model/SetModel"] do
    ports := ports ++ ((← (FilePath.mk directory).walkDir).filter (·.extension == some "lean")).map (·.toString)
  sameFiles ports (conLeche.map (·.target))
  need (← (FilePath.mk "Ix/Theory/LICENSE-APACHE").pathExists) "missing con-leche Apache license"
  for row in conLeche do
    need ((← sha256 row.target) == row.targetSha256) s!"con-leche port changed: {row.target}"
    let contents ← IO.FS.readFile row.target
    need (contents.startsWith s!"/-\nPorted from con-leche ({conLecheRevision}).\nSource: {row.source}\n" &&
      contents.contains "SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)")
      s!"con-leche notice changed: {row.target}"
    if let some repository := args.head? then
      let blob ← IO.Process.output {
        cmd := "git", args := #["-C", repository, "show", s!"{conLecheRevision}:{row.source}"] }
      need (blob.exitCode == 0) blob.stderr
      IO.FS.withTempFile fun handle path => do
        handle.putStr blob.stdout
        handle.flush
        need ((← sha256 path) == row.sourceSha256) s!"con-leche upstream hash mismatch: {row.source}"
  IO.println s!"Theory provenance OK: {selected.size} selected source files; {conLeche.size} con-leche ports, exact content and notices."
  IO.println s!"Named proof support: {named.size} local source files; separate from the set-model foundation."
