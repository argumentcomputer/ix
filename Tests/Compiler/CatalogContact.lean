import Ix.Compiler

/-!
Executable corpus-contact harness.  It loads one exact ix `.ixc` directory
through the bounded filesystem adapter, runs the complete deep catalog gate,
then sends the semantic constant union through `Pipeline.checkProgram`.
-/

open Ix.Compiler
open Ix.Compiler.Ixon

private def usage : String :=
  "usage: lake exe compiler-catalog-contact -- <catalog.ixc>"

def main (args : List String) : IO UInt32 := do
  let [directory] := args
    | IO.eprintln usage
      return 2
  match ← CatalogIO.loadDir directory with
  | .error error =>
    IO.eprintln s!"catalog-contact: ingress rejected: {repr error}"
    return 1
  | .ok loaded =>
    IO.println s!"members_root={loaded.manifest.membersRoot}"
    IO.println s!"content_root={loaded.manifest.contentRoot}"
    IO.println s!"stats={repr loaded.stats}"
    match Pipeline.checkProgram loaded.constants with
    | .error error =>
      IO.eprintln s!"catalog-contact: pipeline rejected: {repr error}"
      return 1
    | .ok _ =>
      IO.println "pipeline=accepted"
      return 0
