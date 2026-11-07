/-
  `ix prepare [--cuda]`

  Readies the default backend once per program and exporter build, so later commands
  start immediately and from any directory: builds its Rust hosts (CPU, and
  with `--cuda` the CUDA hosts too) and exports the certified IxVM and
  aggregation artifacts into the checkout's cache. Cargo rebuilds a host only
  when its sources changed; an artifact is exported only when its exporter or
  the digest of the program it embeds changed.
-/
module
public import Cli
public import Ix.Cli.FormalAggregate

public section

namespace Ix.Cli.PrepareCmd
open Ix.Cli

def runPrepareCmd (p : Cli.Parsed) : IO UInt32 := do
  IO.println s!"checkout {← FormalAiur.repoRoot}"
  let hosts := #[("ixvm", "ixvm-proof", "IX_AIUR_HOST"),
    ("stark-verifier", "stark-verifier", "IX_STARK_HOST"),
    ("ix-prover", "ix-prover", "IX_PROVER_HOST")]
  let devices := if p.hasFlag "cuda" then #[none, some 0] else #[none]
  for device in devices do
    for (package, binary, env) in hosts do
      IO.println s!"host {← FormalAiur.rustHost package binary env device (refresh := true)}"
  IO.println s!"ixvm artifact {← FormalAiur.artifact p}"
  IO.println s!"aggregation artifact {← FormalAggregate.artifact p}"
  return 0

end Ix.Cli.PrepareCmd

open Ix.Cli.PrepareCmd in
def prepareCmd : Cli.Cmd := `[Cli|
  prepare VIA runPrepareCmd;
  "Build the default backend's Rust hosts and export its certified artifacts ahead of time"

  FLAGS:
    "cuda"; "Also build the CUDA hosts (requires the CUDA toolkit)."
    "aiur-artifact" : String; "Use this trusted IxVM artifact instead of exporting one."
    "aggr-artifact" : String; "Use this trusted aggregation artifact instead of exporting one."
]
