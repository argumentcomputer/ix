/-
  `ix prepare`

  Readies the default backend once per source revision, so later commands
  start immediately and from any directory: compiles the certified IxVM,
  recursive verifier and aggregation packages into the checkout's cache,
  concurrently, and prints their paths. `lake build ix` generates the native
  executors from the same cache (`formal_generated` in `lakefile.lean`). A
  package is compiled only when the linked compiler or the digest of its
  program changed.
-/
module
public import Cli
public import Ix.Cli.FormalAggregate

public section

namespace Ix.Cli.PrepareCmd
open Ix.Cli

def runPrepareCmd (p : Cli.Parsed) : IO UInt32 := do
  let root ← FormalAiur.repoRoot
  IO.println s!"checkout {root}"
  let absolute (path : String) : IO String := return (← IO.FS.realPath path).toString
  let targets := #[FormalProver.Target.ixvm, .verifier, .aggregation]
  let paths ← FormalAiur.targetPaths p targets
  for target in targets, path in paths do
    let full ← absolute path
    IO.println s!"{FormalAiur.generatedName target} artifact {full}"
  let linked ← Ix.FormalProver.executors
  IO.println s!"linked executors {", ".intercalate linked.toList}"
  return 0

end Ix.Cli.PrepareCmd

open Ix.Cli.PrepareCmd in
def prepareCmd : Cli.Cmd := `[Cli|
  prepare VIA runPrepareCmd;
  "Compile the default backend's certified artifacts ahead of time"

  FLAGS:
    "aiur-artifact" : String; "Use this trusted IxVM artifact instead of compiling one."
    "aiur-artifact-digest" : String; "Refuse an IxVM artifact whose BLAKE3 digest is not this one."
    "aggr-artifact" : String; "Use this trusted aggregation artifact instead of compiling one."
    "aggr-artifact-digest" : String; "Refuse an aggregation artifact whose BLAKE3 digest is not this one."
    "verifier-artifact" : String; "Use this trusted recursive verifier artifact instead of compiling one."
]
