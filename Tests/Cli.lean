module

public import Ix.Cli.CheckCmd

/- Integration tests for the Ix CLI -/

def Tests.Cli.run (buildCmd: String) (buildArgs : Array String) (buildDir : Option System.FilePath) : IO Unit := do
  let proc : IO.Process.SpawnArgs :=
    match buildDir with
    | some bd => { cmd := buildCmd, args := buildArgs, cwd := bd }
    | none => { cmd := buildCmd, args := buildArgs }
  let out ← IO.Process.output proc
  if out.exitCode ≠ 0 then
    IO.eprintln out.stderr
    throw $ IO.userError out.stderr
  else
    IO.println out.stdout

private def Tests.Cli.expectError (label : String) (result : Except String α) : IO Unit := do
  match result with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError s!"{label}: expected an error"

/-- Regression coverage for selected-shard claim reconstruction. These are
    pure checks kept in the CLI suite because that is where the manifest parser
    and claim-binding helpers are exercised in CI. -/
private def Tests.Cli.testShardClaimValidation : IO Unit := do
  let malformedAddr := Address.blake3 "malformed shard constant".toUTF8
  let malformed : Ixon.LazyConstant := Ixon.LazyConstant.ofSlice ByteArray.empty 0 0
  let malformedEnv : Ixon.Env :=
    { consts := ({} : Std.HashMap Address Ixon.LazyConstant).insert
        malformedAddr malformed }
  Tests.Cli.expectError "malformed lazy constant must fail claim reconstruction"
    (Ix.Cli.CheckCmd.shardClaimDigest malformedEnv #[malformedAddr])

  let phantomAddr := Address.blake3 "phantom manifest block".toUTF8
  Tests.Cli.expectError "manifest block absent from env must be rejected"
    (Ix.Cli.CheckCmd.validateManifestBlocks ({} : Ixon.Env) #[#[phantomAddr]])
  Tests.Cli.expectError "phantom block must fail direct claim reconstruction"
    (Ix.Cli.CheckCmd.shardClaimDigest ({} : Ixon.Env) #[phantomAddr])

  let constant : Ixon.Constant :=
    { info := .axio { isUnsafe := false, lvls := 0, typ := .sort 0 }
      sharing := #[], refs := #[], univs := #[] }
  let constantAddr := Address.blake3 (Ixon.serConstant constant)
  let validEnv := ({} : Ixon.Env).storeConst constantAddr constant
  match Ix.Cli.CheckCmd.validateManifestBlocks validEnv #[#[constantAddr]] with
  | .error e => throw <| IO.userError s!"valid manifest block was rejected: {e}"
  | .ok () => pure ()
  match Ix.Cli.CheckCmd.ownedConstsForBlocks validEnv #[constantAddr] with
  | .error e => throw <| IO.userError s!"valid shard reconstruction failed: {e}"
  | .ok owned =>
    unless owned == #[constantAddr] do
      throw <| IO.userError
        s!"valid shard reconstructed {owned.size} owned constants instead of 1"

  -- The one-pass reconstruction (one env decode for the whole manifest) must
  -- agree shard for shard with the per-shard reconstruction.
  let other : Ixon.Constant :=
    { info := .axio { isUnsafe := false, lvls := 1, typ := .sort 0 }
      sharing := #[], refs := #[], univs := #[] }
  let otherAddr := Address.blake3 (Ixon.serConstant other)
  let twoEnv := validEnv.storeConst otherAddr other
  let shards : Array (Array Address) := #[#[constantAddr], #[otherAddr]]
  let perShard ← IO.ofExcept (shards.mapM (Ix.Cli.CheckCmd.shardClaimDigest twoEnv))
  let onePass ← IO.ofExcept (Ix.Cli.CheckCmd.shardClaimDigests twoEnv shards)
  unless onePass == perShard.map some do
    throw <| IO.userError
      "one-pass shard digests disagree with the per-shard digests"

  -- A shard owning no blocks has no CheckEnv claim; that is `none`, not a
  -- failure — the planner does emit empty shards, and they need no proof.
  match Ix.Cli.CheckCmd.shardClaimDigests twoEnv #[#[constantAddr], #[]] with
  | .error e => throw <| IO.userError s!"empty shard must not fail: {e}"
  | .ok ds =>
    unless ds == #[some perShard[0]!, none] do
      throw <| IO.userError "empty shard must reconstruct as `none`"

  Tests.Cli.expectError "a block owned by two shards must be rejected"
    (Ix.Cli.CheckCmd.ownedConstsPerShard twoEnv #[#[constantAddr], #[constantAddr]])

public def Tests.Cli.suite : IO UInt32 := do
  Tests.Cli.testShardClaimValidation
  Tests.Cli.run "lake" (#["exe", "ix", "--help"]) none
  --Tests.Cli.run "ix" (#["store", "ix_test/IxTest.lean"]) none
  --Tests.Cli.run "ix" (#["prove", "ix_test/IxTest.lean", "one"]) none
  return 0
