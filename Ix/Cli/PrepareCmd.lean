/-
  `ix prepare`

  Readies the default backend once per source revision, so later commands
  start immediately and from any directory: compiles the certified IxVM,
  recursive verifier and aggregation programs with the compiler linked into
  `ix`, persists them as binary artifacts in the checkout's cache, and
  records them in `.lake/aiur/native-kernels.env`. The formal prover runs
  inside `ix`; the next `lake build ix` compiles native executors generated
  from these artifacts into it (see `formalNativeArtifacts` in
  `lakefile.lean`). Until then jobs run on the interpreter, with identical
  records and proofs. A program is compiled only when the linked compiler or
  its sources changed.
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
  let registry ← Ix.FormalProver.Registry.new
  let ixvm ← absolute (← FormalAiur.artifact p registry).path
  let verifier ← absolute (← FormalAiur.verifierArtifact p registry).path
  let aggregation ← absolute (← FormalAggregate.artifact p registry).path
  IO.println s!"ixvm artifact {ixvm}"
  IO.println s!"verifier artifact {verifier}"
  IO.println s!"aggregation artifact {aggregation}"
  let manifest := root / ".lake" / "aiur" / "native-kernels.env"
  IO.FS.createDirAll (root / ".lake" / "aiur")
  IO.FS.writeFile manifest s!"AIUR_IXVM_ARTIFACT={ixvm}\nAIUR_VERIFIER_ARTIFACT={verifier}\nAIUR_AGGREGATION_ARTIFACT={aggregation}\n"
  IO.println s!"native kernels {manifest}"
  let linked ← Ix.FormalProver.executors
  IO.println s!"linked executors {", ".intercalate linked.toList}"
  unless linked.contains "native-ixvm" do
    IO.println "rebuild with `lake build ix` to link the native executors for these artifacts"
  return 0

end Ix.Cli.PrepareCmd

open Ix.Cli.PrepareCmd in
def prepareCmd : Cli.Cmd := `[Cli|
  prepare VIA runPrepareCmd;
  "Compile the default backend's certified programs ahead of time and select their binary artifacts for its native executors"

  FLAGS:
    "aiur-artifact" : String; "Use this trusted IxVM artifact instead of compiling one."
    "aggr-artifact" : String; "Use this trusted aggregation artifact instead of compiling one."
    "verifier-artifact" : String; "Use this trusted recursive verifier artifact instead of compiling one."
]
