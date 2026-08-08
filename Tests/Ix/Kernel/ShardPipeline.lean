/-
  End-to-end regression for the Aiur shard pipeline:

      Lean env → .ixe → `ix profile` (touch graph) → `ix shard`
      (measured packing) → check every shard → batch prove
      (prove → verify → bind) → composed verdict → resume.

  The suite pins:

  - the packer produces a disjoint cover over a fresh touch-graph
    profile;
  - every shard CHECKS through the native kernel;
  - the batched prove reaches the composed verdict: every proof
    VERIFIES and binds to its shard's reconstructed claim;
  - the shard-proofs cache makes the run resumable (second run: 0
    pending), exercising the entry re-verification path.

  Artifacts live under `.lake/tmp-shard-pipeline/` (wiped per run),
  including a scratch cache root so the test never touches the global
  `~/.ix/cache`; proofs land in the content-addressed store like any
  prove.
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
  let cacheRoot := dir / "cache"
  for f in [ixe, prof, ixes] do
    if ← f.pathExists then IO.FS.removeFile f
  if ← cacheRoot.pathExists then IO.FS.removeDirAll cacheRoot

  -- Lean env → .ixe
  let ixonEnv ← IxVM.ClaimHarness.loadSharedIxonEnv roots env
  let bytes ← IO.ofExcept (Ixon.serEnv ixonEnv)
  IO.FS.writeBinFile ixe bytes

  -- .ixe → touch-graph profile → fixed 3-shard min-cut manifest. A fixed
  -- count (not the Aiur RAM packer, whose composed base exceeds any budget
  -- a ~200-constant env could fill) keeps the partition multi-shard and
  -- small; the claim layer is partition-agnostic, and the RAM packer has
  -- its own unit coverage.
  Ix.KernelCheck.rsProfileAnonFFI ixe.toString prof.toString true true "0" "aiur"
  Ix.KernelCheck.rsShardEspFFI prof.toString "3" "10" "1" ixes.toString

  let (parsedEnv, shards) ←
    match ← Ix.Cli.CheckCmd.loadEnvAndShards ixes.toString ixe.toString with
    | .error e => throw <| IO.userError s!"manifest/env load failed: {e}"
    | .ok r => pure r
  let mut tests : TestSeq :=
    test s!"packer produced a multi-shard partition ({shards.size})"
      (shards.size ≥ 2)

  -- Every shard checks through the native kernel.
  let checkRc ← Ix.Cli.CheckCmd.runShardManifestAllNative ixes.toString
    ixe.toString none compiled false none false
  tests := tests ++ test "all shards check" (checkRc == 0)

  -- Batched prove: prove → verify → bind → compose.
  let (aiurSystem, compiled') ← match ← Ix.Cli.VerifyCmd.buildBackend with
    | .error e => throw <| IO.userError s!"backend build failed: {e}"
    | .ok b => pure b
  let envHandle ← match Aiur.EnvHandle.fromIxe ixe.toString with
    | .error e => throw <| IO.userError s!"EnvHandle.fromIxe: {e}"
    | .ok h => pure h

  -- Scan-and-cut over the same env: measured thin-frontier segments →
  -- merge/re-measure → manifest. The budget barely clears the RAM-model
  -- base, so the tiny env still exercises cuts, the merge pass, and the
  -- refine rounds; the scanned partition must cover and check like the
  -- profiled one.
  let scanIxes := dir / "pipeline-scan.ixes"
  let scanFunIdx ← match compiled.getFuncIdx `verify_claim with
    | some i => pure i
    | none => throw <| IO.userError "verify_claim missing"
  let scanSystem := Aiur.AiurSystem.build compiled.bytecode
    Aiur.productionCommitmentParameters Aiur.productionFriParameters
  -- Empty worker-bin/ixe strings select the in-process thread pool: the
  -- test binary cannot exec itself as `ix shard-worker`.
  match Aiur.AiurSystem.scanShardsWithEnv scanSystem scanFunIdx
      envHandle "20" "5" "2" "1" scanIxes.toString "" "" with
  | .error e => throw <| IO.userError s!"shard scan failed: {e}"
  | .ok () => pure ()
  let (_, scanShards) ←
    match ← Ix.Cli.CheckCmd.loadEnvAndShards scanIxes.toString ixe.toString with
    | .error e => throw <| IO.userError s!"scan manifest load failed: {e}"
    | .ok r => pure r
  tests := tests ++
    test s!"scan produced a covering partition ({scanShards.size} shard(s))"
      (scanShards.size ≥ 1)
  let scanCheckRc ← Ix.Cli.CheckCmd.runShardManifestAllNative scanIxes.toString
    ixe.toString none compiled false none false
  tests := tests ++ test "all scanned shards check" (scanCheckRc == 0)
  let proveRc ← Ix.Cli.ProveCmd.runShardProveAllNative ixes.toString envHandle
    parsedEnv shards aiurSystem compiled' 1 (some cacheRoot)
  tests := tests ++ test "batch prove reaches the composed verdict" (proveRc == 0)
  let cacheEntries (ns : String) : IO Nat := do
    if !(← (cacheRoot / ns).pathExists) then return 0
    return (← (cacheRoot / ns).readDir).size
  tests := tests ++ test
    s!"shard-proofs cache written ({← cacheEntries "shard-proofs"} entries)"
    ((← cacheEntries "shard-proofs") == shards.size)

  -- Resume: every cached proof must re-verify and be skipped; verdict
  -- unchanged.
  let resumeRc ← Ix.Cli.ProveCmd.runShardProveAllNative ixes.toString envHandle
    parsedEnv shards aiurSystem compiled' 1 (some cacheRoot)
  tests := tests ++ test "resume re-verifies cached proofs and stays green"
    (resumeRc == 0)
  pure tests

end Tests.Ix.Kernel.ShardPipeline
