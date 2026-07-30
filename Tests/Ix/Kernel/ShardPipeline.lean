/-
  End-to-end regression for the measured-ingress shard pipeline:

      Lean env → .ixe → `ix profile` (touch graph) → `ix shard`
      (measured packing) → check every shard (stub witnesses) →
      batch prove (classify → ghost → prove → verify → bind) →
      composed verdict → resume.

  This is the pipeline the sb/measured-ingress branch ships; until now
  its only end-to-end validation lived in ad-hoc session fixtures. The
  suite pins:

  - the packer produces a disjoint cover over a fresh v4 profile;
  - every shard's stub witness CHECKS through the native kernel (the
    fast-converging repair regime — a tiny closure needs no escalation);
  - the batched prove classifies stub consults, ghosts the rest, and
    every proof VERIFIES and binds to its shard's reconstructed claim
    (the composed verdict);
  - the proofs sidecar makes the run resumable (second run: 0 pending),
    exercising the row re-verification path;
  - the ghost-classification cache is written and hit.

  Artifacts live under `.lake/tmp-shard-pipeline/` (wiped per run);
  proofs land in the content-addressed store like any prove.
-/
import Ix.Meta
import Ix.Aiur.Protocol
import Ix.IxVM
import Ix.IxVM.ClaimHarness
import Ix.Ixon
import Ix.KernelCheck
import Ix.Cli.CheckCmd
import Ix.Cli.ProveCmd
import Ix.Cli.VerifyCmd
import LSpec

open LSpec

namespace Tests.Ix.Kernel.ShardPipeline

/-- Small but non-trivial roots: enough closure (~200 consts) to pack
    several shards at a small budget, with inductives, recursors, and
    string/Nat literals represented. -/
private def roots : Array Lean.Name :=
  #[`Nat.add, `List.append, `Nat.mul, `Char.ofNat]

private def dir : System.FilePath := ".lake" / "tmp-shard-pipeline"

def shardPipelineTests (env : Lean.Environment)
    (compiled : Aiur.CompiledToplevel) : IO TestSeq := do
  IO.FS.createDirAll dir
  let ixe := dir / "pipeline.ixe"
  let prof := dir / "pipeline.ixprof"
  let ixes := dir / "pipeline.ixes"
  let proofsCsv := (ixes.toString ++ ".proofs.csv" : System.FilePath)
  let ghostsCsv := (ixes.toString ++ ".ghosts.csv" : System.FilePath)
  for f in [ixe, prof, ixes, proofsCsv, ghostsCsv] do
    if ← f.pathExists then IO.FS.removeFile f

  -- Lean env → .ixe
  let ixonEnv ← IxVM.ClaimHarness.loadSharedIxonEnv roots env
  let bytes ← IO.ofExcept (Ixon.serEnv ixonEnv)
  IO.FS.writeBinFile ixe bytes

  -- .ixe → v4 profile (touch graph) → measured manifest. The tiny
  -- budget forces a multi-shard partition so cross-shard stubs exist.
  Ix.KernelCheck.rsProfileAnonFFI ixe.toString prof.toString true true "0" "aiur"
  Ix.KernelCheck.rsShardEspCapFFI prof.toString "0" "6" "5" "1"
    ixes.toString "aiur" ""

  let (parsedEnv, shards) ←
    match ← Ix.Cli.CheckCmd.loadEnvAndShards ixes.toString ixe.toString with
    | .error e => throw <| IO.userError s!"manifest/env load failed: {e}"
    | .ok r => pure r
  let mut tests : TestSeq :=
    test s!"packer produced a multi-shard partition ({shards.size})"
      (shards.size ≥ 2)
  let anyStubs := shards.any fun (_, _, stubbed) => !stubbed.isEmpty
  tests := tests ++ test "partition has cross-shard stubs" anyStubs

  -- Every shard checks on its stub witness through the native kernel.
  let checkRc ← Ix.Cli.CheckCmd.runShardManifestAllNative ixes.toString
    ixe.toString none compiled false none false
  tests := tests ++ test "all shards check (stub witnesses)" (checkRc == 0)

  -- Batched prove: classify → ghost → prove → verify → bind → compose.
  let (aiurSystem, compiled') ← match ← Ix.Cli.VerifyCmd.buildBackend with
    | .error e => throw <| IO.userError s!"backend build failed: {e}"
    | .ok b => pure b
  let envHandle ← match Aiur.EnvHandle.fromIxe ixe.toString with
    | .error e => throw <| IO.userError s!"EnvHandle.fromIxe: {e}"
    | .ok h => pure h
  let proveRc ← Ix.Cli.ProveCmd.runShardProveAllNative ixes.toString envHandle
    parsedEnv shards aiurSystem compiled' 1
  tests := tests ++ test "batch prove reaches the composed verdict" (proveRc == 0)
  tests := tests ++ test "proofs sidecar written" (← proofsCsv.pathExists)
  tests := tests ++ test "ghost-classification cache written"
    (← ghostsCsv.pathExists)

  -- Resume: every row must re-verify and be skipped; verdict unchanged.
  let resumeRc ← Ix.Cli.ProveCmd.runShardProveAllNative ixes.toString envHandle
    parsedEnv shards aiurSystem compiled' 1
  tests := tests ++ test "resume re-verifies rows and stays green" (resumeRc == 0)
  pure tests

end Tests.Ix.Kernel.ShardPipeline
