module

public import Tests.Aggr

/-!
# Converged aggregate host/driver semantics

M1-e ports the host, manifest, cache, verifier-value, and scheduler coverage
that originally lived beside the three-entrypoint aggregate circuit onto the
production `ix_aggr` claim and slot model. Circuit shape positives/negatives
remain in `Tests/Aggr.lean`; this file supplies the rest of the semantic union.
-/

public section

open LSpec Aiur

namespace Tests.Aggr

open Tests.MultiStark (expectOk expectErr recCommitParams innerFri u64le)

private def canonicalTree (leaves : Array Address) : Ix.AssumptionTree :=
  (Ix.AssumptionTree.canonical leaves).get!

private def u32le4 (n : Nat) : Array UInt8 :=
  (Array.range 4).map fun i => UInt8.ofNat ((n >>> (8 * i)) % 256)

private def minimalIxesFor (shards : Array (Array Address))
    (treeTail : Array UInt8) : ByteArray :=
  let putAddresses := fun (addresses : Array Address) =>
    addresses.foldl (fun out address => out ++ address.hash.data)
      (u32le4 addresses.size)
  let shard := fun id blocks => u32le4 id ++ Array.replicate 24 0 ++ #[0] ++
    putAddresses blocks ++ u32le4 0
  let body := (shards.mapIdx shard).foldl (· ++ ·) #[]
  ⟨#[0x49, 0x58, 0x45, 0x53, 0, 0, 0, 0] ++ Array.replicate 16 0 ++
    u32le4 shards.size ++ body ++ treeTail⟩

private def minimalIxes (treeTail : Array UInt8) : ByteArray :=
  minimalIxesFor #[#[], #[]] treeTail

private def singletonIxonEnv : Ixon.Env × Address :=
  let constant : Ixon.Constant :=
    ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.succ .zero]⟩
  let address := Address.blake3 (Ixon.serConstant constant)
  (({} : Ixon.Env).storeConst address constant, address)

private def pairIxonEnv : Ixon.Env × Address × Address :=
  let left : Ixon.Constant :=
    ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.succ .zero]⟩
  let right : Ixon.Constant :=
    ⟨.axio ⟨true, 0, .sort 0⟩, #[], #[], #[.succ .zero]⟩
  let leftAddress := Address.blake3 (Ixon.serConstant left)
  let rightAddress := Address.blake3 (Ixon.serConstant right)
  let env := (({} : Ixon.Env).storeConst leftAddress left)
    |>.storeConst rightAddress right
  (env, leftAddress, rightAddress)

/-- Two owned constants with one shared dependency exercise the one-pass
witness-closure union retained by the converged driver. -/
private def sharedClosureIxonEnv : Ixon.Env × Array Address × Address :=
  let shared : Ixon.Constant :=
    ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.succ .zero]⟩
  let sharedAddress := Address.blake3 (Ixon.serConstant shared)
  let left : Ixon.Constant :=
    ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[sharedAddress], #[]⟩
  let right : Ixon.Constant :=
    ⟨.axio ⟨true, 0, .ref 0 #[]⟩, #[], #[sharedAddress], #[]⟩
  let leftAddress := Address.blake3 (Ixon.serConstant left)
  let rightAddress := Address.blake3 (Ixon.serConstant right)
  let env := (({} : Ixon.Env).storeConst sharedAddress shared)
    |>.storeConst leftAddress left
    |>.storeConst rightAddress right
  (env, #[leftAddress, rightAddress], sharedAddress)

private def stage2FixtureAddressHex : String :=
  "c2fdce660eb66899efa303b41d4ca1611a62a688ef20684fdc327739d38bd67f"

private def stage2FixtureRootHex : String :=
  "3211abb340539c10220990fb095f8763cb3a364e111ebe57fb518992d42d7382"

private def stage2FixturePath : System.FilePath :=
  "Tests" / "Fixtures" / "Aggregate" / "mathlib-2026-09-03" /
    s!"{stage2FixtureAddressHex}.ixon-proof"

private def stage2FixtureStorePath (home : System.FilePath) : System.FilePath :=
  home / ".ix" / "store" / "c2" / "fd" / "ce" /
    "660eb66899efa303b41d4ca1611a62a688ef20684fdc327739d38bd67f"

/-- Pin a real whole-Mathlib root at the persisted-proof boundary. The 3.33 GB
environment and 52.5 MB manifest are identified in the adjacent provenance
record rather than checked in; this gate re-hashes and decodes the exact
wrapper, pins its unconditional root claim, and drives native cryptographic
verification through the production CLI/backend. -/
private def stage2FixtureValid : IO Bool := do
  try
    unless (← stage2FixturePath.pathExists) do
      IO.eprintln s!"Stage 2 fixture missing: {stage2FixturePath}"
      return false
    let bytes ← IO.FS.readBinFile stage2FixturePath
    if bytes.size != 9_813_583 then
      IO.eprintln s!"Stage 2 fixture is {bytes.size} bytes, expected 9813583"
      return false
    let some address := Address.fromString stage2FixtureAddressHex | do
      IO.eprintln "invalid pinned Stage 2 fixture address"
      return false
    let some root := Address.fromString stage2FixtureRootHex | do
      IO.eprintln "invalid pinned Stage 2 fixture root"
      return false
    let wrapper ← match Ix.Cli.VerifyCmd.decodeAggregateWrapperAt address bytes with
      | .error e => IO.eprintln s!"Stage 2 fixture wrapper rejected: {e}"; return false
      | .ok wrapper => pure wrapper
    if wrapper.claim != .checkEnv root none then
      IO.eprintln s!"Stage 2 fixture claim drifted: {wrapper.claim}"
      return false
    let ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"
    unless (← ixExe.pathExists) do
      IO.eprintln s!"{ixExe} missing — run `lake build IxTests` first"
      return false
    let exe ← IO.FS.realPath ixExe
    let home ← IO.FS.createTempDir
    try
      let storePath := stage2FixtureStorePath home
      let some storeDir := storePath.parent | do
        IO.eprintln s!"Stage 2 fixture store path has no parent: {storePath}"
        return false
      IO.FS.createDirAll storeDir
      IO.FS.writeBinFile storePath bytes
      let out ← IO.Process.output {
        cmd := "env"
        args := #[s!"HOME={home}", exe.toString, "verify", "--aggregate",
          stage2FixtureAddressHex] }
      if out.exitCode != 0 then
        IO.eprintln s!"Stage 2 fixture verification failed ({out.exitCode}): \
{out.stderr.take 500}"
        return false
      unless out.stdout.contains s!"ok: aggregate proof {stage2FixtureAddressHex} verifies" do
        IO.eprintln s!"Stage 2 fixture verifier returned no success marker: \
{out.stdout.takeEnd 500}"
        return false
      return true
    finally
      IO.FS.removeDirAll home
  catch e =>
    IO.eprintln s!"Stage 2 fixture test failed: {e}"
    return false

def semanticSuite : IO UInt32 := do
  let childCompiled ← match childProgram.compile with
    | .error e => IO.eprintln s!"aggr semantic child compilation failed: {e}"; return 1
    | .ok compiled => pure compiled
  let verifyIdx := childCompiled.getFuncIdx `fake_verify_claim |>.get!
  let fakeAggrIdx := childCompiled.getFuncIdx `fake_aggr |>.get!
  let ixvmSystem := AiurSystem.build childCompiled.bytecode recCommitParams innerFri
  let selfSystem := AiurSystem.build childCompiled.bytecode recCommitParams
    { innerFri with numQueries := 4 }
  let ixvmVk := ixvmSystem.vkBytes
  let selfVk := selfSystem.vkBytes
  let allowed := Aggr.allowedBlob ixvmVk verifyIdx selfVk fakeAggrIdx

  -- Recursion parameter and cache-key contract.
  let recursionDefaults := MultiStark.defaultRecursionParameters
  let defaultRecursionSystem :=
    MultiStark.buildRecursionSystem childCompiled.bytecode recursionDefaults
  let directDefaultSystem := AiurSystem.build childCompiled.bytecode
    Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  let expectedDefaultFriBytes : ByteArray :=
    ⟨u64le 0 ++ u64le 1 ++ u64le 100 ++ u64le 0 ++ u64le 20⟩
  let tunedFri : Aiur.FriParameters :=
    { recursionDefaults.fri with numQueries := 50 }
  let tunedFriParameters : MultiStark.RecursionParameters :=
    { recursionDefaults with fri := tunedFri }
  let tunedFriSystem :=
    MultiStark.buildRecursionSystem childCompiled.bytecode tunedFriParameters
  let tunedCommitment : Aiur.CommitmentParameters :=
    { recursionDefaults.commitment with logBlowup := 3 }
  let tunedCommitmentParameters : MultiStark.RecursionParameters :=
    { recursionDefaults with commitment := tunedCommitment }
  let tunedCommitmentSystem :=
    MultiStark.buildRecursionSystem childCompiled.bytecode tunedCommitmentParameters
  let defaultRecursionIdentityPreserved :=
    defaultRecursionSystem.vkBytes == directDefaultSystem.vkBytes
  let defaultFriEncodingStable :=
    recursionDefaults.cacheFriBytes.size == 40 &&
      recursionDefaults.cacheFriBytes == expectedDefaultFriBytes
  let recursionParametersIndependent :=
    tunedFriParameters.cacheFriBytes != recursionDefaults.cacheFriBytes &&
      tunedFriSystem.vkBytes != defaultRecursionSystem.vkBytes &&
      tunedCommitmentParameters.cacheFriBytes == recursionDefaults.cacheFriBytes &&
      tunedCommitmentSystem.vkBytes != defaultRecursionSystem.vkBytes

  -- Two conditional statements whose assumptions cross the subject boundary.
  let a := Address.blake3 "aggr-semantics-a".toUTF8
  let b := Address.blake3 "aggr-semantics-b".toUTF8
  let c := Address.blake3 "aggr-semantics-c".toUTF8
  let d := Address.blake3 "aggr-semantics-d".toUTF8
  let left : Aggr.CheckEnvTrees := {
    subjects := canonicalTree #[a, b]
    assumptions := some (canonicalTree #[c, d])
  }
  let right : Aggr.CheckEnvTrees := {
    subjects := canonicalTree #[c]
    assumptions := some (canonicalTree #[a])
  }
  let flatOutput := left.join right
  let structuralOutput := left.joinStructural right
  let flatHostCorrect :=
    flatOutput.subjects.leaves == (canonicalTree #[a, b, c]).leaves &&
      flatOutput.assumptions.map (·.leaves) == some #[d]
  let structuralHostCorrect :=
    structuralOutput.subjects.root ==
      Ix.Merkle.nodeHash left.subjects.root right.subjects.root &&
      structuralOutput.assumptions.map (·.leaves) == some #[d]
  let converted := Ix.Cli.AggregateCmd.toAggrCheckEnvTrees
    (Ix.Cli.AggregateCmd.fromAggrCheckEnvTrees structuralOutput)
  let hostConversionRoundTrip := converted.claim == structuralOutput.claim &&
    converted.subjects.leaves == structuralOutput.subjects.leaves &&
    converted.assumptions.map (·.leaves) ==
      structuralOutput.assumptions.map (·.leaves)

  let leftBytes := Ix.Claim.ser left.claim
  let rightBytes := Ix.Claim.ser right.claim
  let flatBytes := Ix.Claim.ser flatOutput.claim
  let leftOuter := Ix.Cli.AggregateCmd.aggregateOuterClaim
    allowed fakeAggrIdx left.claim
  let rightOuter := Ix.Cli.AggregateCmd.aggregateOuterClaim
    allowed fakeAggrIdx right.claim
  let flatOuter := Ix.Cli.AggregateCmd.aggregateOuterClaim
    allowed fakeAggrIdx flatOutput.claim
  let (_, leftProof, _) ← match selfSystem.prove fakeAggrIdx
      (Aggr.pubInput allowed leftBytes) default with
    | .error e => IO.eprintln s!"left aggregate prove failed: {e}"; return 1
    | .ok result => pure result
  let (_, rightProof, _) ← match selfSystem.prove fakeAggrIdx
      (Aggr.pubInput allowed rightBytes) default with
    | .error e => IO.eprintln s!"right aggregate prove failed: {e}"; return 1
    | .ok result => pure result
  let outerClaimBindsValue := leftOuter != rightOuter &&
    flatOuter == Aiur.buildClaim fakeAggrIdx (Aggr.pubInput allowed flatBytes) #[]

  let childRecursionParameters : MultiStark.RecursionParameters := {
    commitment := recCommitParams
    fri := innerFri
  }
  let leftKey := Ix.Cli.AggregateCmd.aggregateCacheKey selfVk
    childRecursionParameters leftOuter
  let cacheKeyStable := leftKey == Ix.Cli.AggregateCmd.aggregateCacheKey
    selfVk childRecursionParameters leftOuter
  let cacheKeyBindsOuter := leftKey != Ix.Cli.AggregateCmd.aggregateCacheKey
    selfVk childRecursionParameters rightOuter
  let cacheKeyBindsFri := leftKey != Ix.Cli.AggregateCmd.aggregateCacheKey
    selfVk { childRecursionParameters with fri := tunedFri } leftOuter
  let cacheKeyBindsVk := leftKey != Ix.Cli.AggregateCmd.aggregateCacheKey
    (selfVk.set! 0 (selfVk.data[0]! + 1)) childRecursionParameters leftOuter
  let cacheKeyBindsVersion := leftKey != Ix.Cli.AggregateCmd.aggregateCacheKey
    selfVk childRecursionParameters leftOuter 1
  let repeated07 : Nat := 506381209866536711
  let cacheVectorParameters : MultiStark.RecursionParameters := {
    commitment := Aiur.defaultCommitmentParameters
    fri := {
      logFinalPolyLen := repeated07
      maxLogArity := repeated07
      numQueries := repeated07
      commitProofOfWorkBits := repeated07
      queryProofOfWorkBits := repeated07
    }
  }
  let cacheKeyMatchesRustVector :=
    toString (Ix.Cli.AggregateCmd.aggregateCacheKey "vk".toUTF8
      cacheVectorParameters #[.ofNat 1, .ofNat 2, .ofNat 3]) ==
      "86ed059157e2915fe0a83f1afd58f31f7553659ad778669f6b795e1473e7afe0"

  let ops : Array Ix.Cli.CheckCmd.AggregationTree.FoldOp :=
    #[.leaf 0, .leaf 1, .join 0 1]
  let wrapPlan := Ix.Cli.AggregateCmd.schedulePlan ops #[2, 1] 8
  let directPlan := Ix.Cli.AggregateCmd.schedulePlan ops #[2, 1] 8 true
  let prepared : Array Ix.Cli.AggregateCmd.PreparedShard := #[
    { claim := left.claim,
      statement := Ix.Cli.AggregateCmd.fromAggrCheckEnvTrees left },
    { claim := right.claim,
      statement := Ix.Cli.AggregateCmd.fromAggrCheckEnvTrees right }
  ]
  let wrapSpecs := wrapPlan.bind fun plan =>
    Ix.Cli.AggregateCmd.buildAggrSlotSpecs plan prepared selfVk allowed
      verifyIdx fakeAggrIdx childRecursionParameters
  let directSpecs := directPlan.bind fun plan =>
    Ix.Cli.AggregateCmd.buildAggrSlotSpecs plan prepared selfVk allowed
      verifyIdx fakeAggrIdx childRecursionParameters
  let wrapSpecsComplete : Bool := match wrapSpecs with
    | .ok specs => match specs[0]?, specs[1]?, specs[2]? with
      | some leftSpec, some rightSpec, some rootSpec =>
        specs.size == 3 && leftSpec.kind == .aggr && rightSpec.kind == .aggr &&
          leftSpec.outerClaim == leftOuter && rightSpec.outerClaim == rightOuter &&
          rootSpec.statement.claim == flatOutput.claim &&
          rootSpec.outerClaim == flatOuter && leftSpec.cacheKey == leftKey
      | _, _, _ => false
    | .error _ => false
  let directSpecsUseRawLeaves : Bool := match directSpecs with
    | .ok specs => match specs[0]?, specs[1]?, specs[2]? with
      | some leftSpec, some rightSpec, some rootSpec =>
        leftSpec.kind == .ixvm && rightSpec.kind == .ixvm &&
          rootSpec.kind == .aggr && rootSpec.outerClaim == flatOuter
      | _, _, _ => false
    | .error _ => false
  let policiesShareRootClaim : Bool := match wrapSpecs, directSpecs with
    | .ok wraps, .ok direct => wraps.back?.map (·.outerClaim) ==
        direct.back?.map (·.outerClaim)
    | _, _ => false

  -- Verified cache/resume against the converged outer claim.
  let cachedWrapper : Ixon.Proof := {
    claim := left.claim
    proof := leftProof.toBytes
  }
  let validCached := Ix.Cli.AggregateCmd.validateAggregateCacheWrapper
    selfSystem left.claim leftOuter cachedWrapper
  let wrongCachedStatement := Ix.Cli.AggregateCmd.validateAggregateCacheWrapper
    selfSystem right.claim leftOuter cachedWrapper
  let wrongCachedOuter := Ix.Cli.AggregateCmd.validateAggregateCacheWrapper
    selfSystem left.claim rightOuter cachedWrapper
  let badProofBytes := leftProof.toBytes.set! 0
    (UInt8.ofNat ((leftProof.toBytes.data[0]!.toNat + 1) % 256))
  let badCachedProof := Ix.Cli.AggregateCmd.validateAggregateCacheWrapper
    selfSystem left.claim leftOuter { cachedWrapper with proof := badProofBytes }

  let cacheRoot ← IO.FS.createTempDir
  let cacheDir ← Ix.Cli.AggregateCmd.aggregateCacheDir (some cacheRoot)
  let missingEntry ← Ix.Cli.AggregateCmd.readAggregateCacheAddress cacheDir leftKey
  let cachedAddress := Address.blake3 (Ixon.Proof.ser cachedWrapper)
  Ix.Cli.AggregateCmd.writeAggregateCacheAddress cacheDir leftKey cachedAddress
  let presentEntry ← Ix.Cli.AggregateCmd.readAggregateCacheAddress cacheDir leftKey
  let tempEntryExists ← (cacheDir / s!"{leftKey}.tmp").pathExists
  IO.FS.writeFile (cacheDir / toString leftKey) "corrupt-cache-entry"
  let corruptEntry ← Ix.Cli.AggregateCmd.readAggregateCacheAddress cacheDir leftKey
  Ix.Cli.AggregateCmd.writeAggregateCacheAddress cacheDir leftKey cachedAddress
  let recoveredEntry ← Ix.Cli.AggregateCmd.readAggregateCacheAddress cacheDir leftKey
  let missingIndexIsMiss : Bool := match missingEntry with
    | .miss => true
    | _ => false
  let cacheIndexRoundTrip : Bool := match presentEntry with
    | .hit address => address == cachedAddress
    | _ => false
  let cacheTempGone := !tempEntryExists
  let corruptIndexRejected : Bool := match corruptEntry with
    | .invalid _ => true
    | _ => false
  let corruptIndexRecovers : Bool := match recoveredEntry with
    | .hit address => address == cachedAddress
    | _ => false
  let cachedBytes := Ixon.Proof.ser cachedWrapper
  let wrapperContentAddressAccepted : Bool :=
    match Ix.Cli.VerifyCmd.decodeAggregateWrapperAt cachedAddress cachedBytes with
    | .ok wrapper =>
      wrapper.claim == cachedWrapper.claim && wrapper.proof == cachedWrapper.proof
    | .error _ => false
  let wrapperContentAddressRejected : Bool :=
    let wrongAddress := Address.blake3 (cachedBytes.push 0xff)
    match Ix.Cli.VerifyCmd.decodeAggregateWrapperAt wrongAddress cachedBytes with
    | .error _ => true
    | .ok _ => false
  let resumed? ← match wrapSpecs with
    | .ok specs =>
      match specs[0]? with
      | some spec =>
        Ix.Cli.AggregateCmd.loadCachedAggregateProofWith
          (fun _ => pure cachedBytes) cacheDir 0 spec selfSystem
      | none => pure none
    | .error _ => pure none
  let corruptStore? ← match wrapSpecs with
    | .ok specs =>
      match specs[0]? with
      | some spec =>
        Ix.Cli.AggregateCmd.loadCachedAggregateProofWith
          (fun _ => pure (cachedBytes.push 0xff)) cacheDir 0 spec selfSystem
      | none => pure none
    | .error _ => pure none

  -- Manifest parsing, validate-before-prune, and value-based verification.
  let manifestPlan :=
    (Ix.Cli.CheckCmd.AggregationTree.node
      (.node (.leaf 0) (.leaf 1)) (.leaf 2)).foldPlan
  let expectedPlan : Array Ix.Cli.CheckCmd.AggregationTree.FoldOp :=
    #[.leaf 0, .leaf 1, .join 0 1, .leaf 2, .join 2 3]
  let parsedManifestPlan : Bool :=
    let valid := minimalIxes (#[1, 1, 0] ++ u32le4 0 ++ #[0] ++ u32le4 1)
    match Ix.Cli.CheckCmd.parseIxesManifest valid with
    | .ok view => view.aggregationTree.foldPlan ==
        (#[.leaf 0, .leaf 1, .join 0 1] :
          Array Ix.Cli.CheckCmd.AggregationTree.FoldOp)
    | .error _ => false
  let malformedManifestRejected : Bool :=
    let duplicate := minimalIxes (#[1, 1, 0] ++ u32le4 0 ++ #[0] ++ u32le4 0)
    match Ix.Cli.CheckCmd.parseIxesManifest duplicate with
    | .error _ => true
    | .ok _ => false
  let (singleEnv, singleAddr) := singletonIxonEnv
  let singleTreeTail := #[1, 1, 0] ++ u32le4 0 ++ #[1, 0] ++
    u32le4 1 ++ #[0] ++ u32le4 2
  let singleManifest := Ix.Cli.CheckCmd.parseIxesManifest
    (minimalIxesFor #[#[], #[singleAddr], #[]] singleTreeTail)
  let singleCoverage ← match singleManifest with
    | .ok view => Ix.Cli.CheckCmd.shardsCover singleEnv view.shards
    | .error _ => pure false
  let emptyPruningCorrect : Bool := match singleManifest with
    | .ok view => match view.pruneEmpty singleEnv with
      | .ok (pruned, counts) =>
        pruned.shards == #[#[singleAddr]] && pruned.shardIds == #[1] &&
          pruned.aggregationTree == .leaf 0 && counts == #[1]
      | .error _ => false
    | .error _ => false
  let singletonValueRoot : Bool := match singleManifest with
    | .ok view => match Ix.Cli.VerifyCmd.expectedFromManifest singleEnv view 0 with
      | .ok statement =>
        statement.claim == .checkEnv (canonicalTree #[singleAddr]).root none
      | .error _ => false
    | .error _ => false
  let (nativePlanOnlyFfiWorks, nativeVerifyRootMatches) ← do
    let dir ← IO.FS.createTempDir
    let ixePath := dir / "native-plan.ixe"
    let ixesPath := dir / "native-plan.ixes"
    match Ixon.serEnv singleEnv with
    | .error _ => pure (false, false)
    | .ok envBytes =>
      IO.FS.writeBinFile ixePath envBytes
      IO.FS.writeBinFile ixesPath <| minimalIxesFor #[#[singleAddr]]
        (#[1, 0] ++ u32le4 0 ++ #[0])
      match Aiur.EnvHandle.fromIxe ixePath.toString with
      | .error _ => pure (false, false)
      | .ok handle =>
        let planWorks := (ixvmSystem.aggregateStage2 selfSystem handle
          ixesPath.toString "" verifyIdx fakeAggrIdx 1
          (16 * 1024 * 1024 * 1024) 4096 0 false true
          childRecursionParameters.cacheFriBytes false true).isOk
        let expectedMatches := match Aiur.AiurSystem.aggregateExpected
            handle ixesPath.toString 4096 with
          | .error _ => false
          | .ok expected =>
            expected.constantCount == 1 && match
                Ixon.runGet Ix.Claim.get expected.claimBytes with
              | .ok claim =>
                claim == .checkEnv (canonicalTree #[singleAddr]).root none
              | .error _ => false
        pure (planWorks, expectedMatches)

  let (pairEnv, pairLeft, pairRight) := pairIxonEnv
  let pairManifest := Ix.Cli.CheckCmd.parseIxesManifest
    (minimalIxesFor #[#[pairLeft], #[pairRight]]
      (#[1, 1, 0] ++ u32le4 0 ++ #[0] ++ u32le4 1))
  let pairCoverage ← match pairManifest with
    | .ok view => Ix.Cli.CheckCmd.shardsCover pairEnv view.shards
    | .error _ => pure false
  let batchedShardPreparationCorrect : Bool := match pairManifest with
    | .ok view =>
      match Ix.Cli.AggregateCmd.prepareShards pairEnv view.shards view.shardIds with
      | .ok prepared =>
        prepared.map (·.claim) == (#[(.checkEnv
            (canonicalTree #[pairLeft]).root none : Ix.Claim),
          .checkEnv (canonicalTree #[pairRight]).root none] : Array Ix.Claim) &&
          prepared.all fun item => item.statement.claim == item.claim
      | .error _ => false
    | .error _ => false
  let flatManifestValue : Option Aggr.CheckEnvTrees := match pairManifest with
    | .ok view => (Ix.Cli.VerifyCmd.expectedFromManifest pairEnv view 8).toOption
    | .error _ => none
  let structuralManifestValue : Option Aggr.CheckEnvTrees := match pairManifest with
    | .ok view => (Ix.Cli.VerifyCmd.expectedFromManifest pairEnv view 0).toOption
    | .error _ => none
  let canonicalEnvTree := canonicalTree #[pairLeft, pairRight]
  let manifestFlatIsCanonical := flatManifestValue.map (·.claim) ==
    some (.checkEnv canonicalEnvTree.root none)
  let manifestStructuralIsHybrid := structuralManifestValue.map (·.claim) ==
    some (.checkEnv
      (Ix.Merkle.nodeHash (canonicalTree #[pairLeft]).root
        (canonicalTree #[pairRight]).root) none)
  let manifestValuesDiffer := flatManifestValue.map (·.claim) !=
    structuralManifestValue.map (·.claim)

  let shardPrepPreservesSemantics : Bool :=
    let (sharedEnv, owned, sharedAddress) := sharedClosureIxonEnv
    let legacyClosure : Std.HashSet Address := Id.run do
      let mut closure : Std.HashSet Address := {}
      for address in owned do
        closure := closure.union (IxVM.ClaimHarness.closureFrom sharedEnv address)
      pure closure
    let expectedOwned := canonicalTree owned
    let expectedFrontier := canonicalTree #[sharedAddress]
    match IxVM.ClaimHarness.shardCheckEnvClaimTrees sharedEnv owned,
        IxVM.ClaimHarness.shardCheckEnvClaim sharedEnv owned with
    | .ok (claimOnly, treesOnly), .ok (claimFull, closure, treesFull) =>
      let sameClosure := closure.size == legacyClosure.size &&
        closure.toArray.all legacyClosure.contains
      claimOnly == .checkEnv expectedOwned.root (some expectedFrontier.root) &&
        claimFull == claimOnly && sameClosure &&
        treesOnly.size == 2 && treesFull.size == 2 &&
        treesOnly.contains expectedOwned.root &&
        treesOnly.contains expectedFrontier.root &&
        treesFull.contains expectedOwned.root &&
        treesFull.contains expectedFrontier.root
    | _, _ => false

  -- A real aggregate-verifier audit fixture: two constants in one shard both
  -- depend on a constant in the other. The structural fold must discharge the
  -- frontier, and one verified stand-in aggregate proof then certifies exactly
  -- the three constants committed by the root statement.
  let (auditEnv, auditOwned, auditShared) := sharedClosureIxonEnv
  let auditManifest := Ix.Cli.CheckCmd.parseIxesManifest
    (minimalIxesFor #[auditOwned, #[auditShared]]
      (#[1, 1, 0] ++ u32le4 0 ++ #[0] ++ u32le4 1))
  let auditStatement := auditManifest.bind fun view =>
    Ix.Cli.VerifyCmd.expectedFromManifest auditEnv view 0
  let aggregateProofAuditsEveryConstant ← match auditStatement with
    | .error _ => pure false
    | .ok statement =>
      let expectedOuter := Ix.Cli.AggregateCmd.aggregateOuterClaim
        allowed fakeAggrIdx statement.claim
      match selfSystem.prove fakeAggrIdx
          (Aggr.pubInput allowed (Ix.Claim.ser statement.claim)) default with
      | .error _ => pure false
      | .ok (outer, proof, _) =>
        let wrapper : Ixon.Proof := { claim := statement.claim, proof := proof.toBytes }
        let bytes := Ixon.Proof.ser wrapper
        let address := Address.blake3 bytes
        let decoded := match Ix.Cli.VerifyCmd.decodeAggregateWrapperAt address bytes with
          | .ok decoded => decoded.claim == statement.claim && decoded.proof == proof.toBytes
          | .error _ => false
        let audited := match Ix.Cli.VerifyCmd.auditAggregateConstants auditEnv statement with
          | .ok count => count == 3
          | .error _ => false
        pure <| decoded && audited && outer == expectedOuter &&
          (selfSystem.verify expectedOuter proof).isOk
  let auditLeaves := auditOwned.push auditShared
  let rejected (result : Except String Nat) : Bool :=
    match result with
    | .error _ => true
    | .ok _ => false
  let missingConstantRejected :=
    rejected (Ix.Cli.VerifyCmd.auditAggregateConstants auditEnv {
      subjects := canonicalTree auditOwned
      assumptions := none
    })
  let foreignConstantRejected :=
    let foreign := Address.blake3 "aggregate-audit-foreign".toUTF8
    rejected (Ix.Cli.VerifyCmd.auditAggregateConstants auditEnv {
      subjects := canonicalTree (auditLeaves.push foreign)
      assumptions := none
    })
  let duplicateConstantRejected :=
    rejected (Ix.Cli.VerifyCmd.auditAggregateConstants auditEnv {
      subjects := .node (canonicalTree auditLeaves) (.leaf auditOwned[0]!)
      assumptions := none
    })
  let residualAssumptionRejected :=
    rejected (Ix.Cli.VerifyCmd.auditAggregateConstants auditEnv {
      subjects := canonicalTree auditLeaves
      assumptions := some (canonicalTree #[auditShared])
    })
  let productionStage2FixtureValid ← stage2FixtureValid

  -- Threshold policy and the RAM-gated DAG controller.
  let mixedSchedule := Ix.Cli.AggregateCmd.schedulePlan
    manifestPlan #[2, 2, 1] 4
  let mixedScheduleCorrect : Bool := match mixedSchedule with
    | .ok scheduled => match scheduled[2]?, scheduled[4]? with
      | some lower, some upper =>
        scheduled.size == 5 && lower.shape? == some 5 &&
          lower.subjectCount == 4 && !lower.structural &&
          upper.shape? == some 9 && upper.subjectCount == 5 && upper.structural
      | _, _ => false
    | .error _ => false
  let fakeWeights : Array Nat := #[8, 3, 4, 6, 5]
  let schedulerTrace := mixedSchedule.bind fun scheduled =>
    Ix.Cli.AggregateCmd.simulateAggregateSchedule scheduled fakeWeights 2 10
  let schedulerHeaviestFirst : Bool := match schedulerTrace with
    | .ok trace => trace.admissionOrder == #[0, 3, 1, 2, 4] &&
        trace.admissionBatches == #[#[0], #[3, 1], #[2], #[4]]
    | .error _ => false
  let schedulerWithinLimits : Bool := match schedulerTrace with
    | .ok trace => trace.maxReservedBytes <= 10 &&
        trace.admissionBatches.all (fun batch => batch.size <= 2)
    | .error _ => false
  let schedulerDependenciesHold : Bool := match schedulerTrace with
    | .ok trace =>
      let position (slot : Nat) := trace.admissionOrder.findIdx? (· == slot)
      match position 0, position 1, position 2, position 3, position 4 with
      | some p0, some p1, some p2, some p3, some p4 =>
        p0 < p2 && p1 < p2 && p2 < p4 && p3 < p4
      | _, _, _, _, _ => false
    | .error _ => false
  let oversizedRunsAlone : Bool := match mixedSchedule.bind fun scheduled =>
      Ix.Cli.AggregateCmd.simulateAggregateSchedule scheduled
        #[11, 3, 4, 6, 5] 2 10 with
    | .ok trace => trace.admissionBatches[0]? == some #[0] &&
        trace.admissionBatches.all fun batch =>
          batch.size == 1 || batch.all fun slot => fakeWeights[slot]! <= 10
    | .error _ => false
  let flatWeightAffine :=
    Ix.Cli.AggregateCmd.aggregateSlotRamBytes
      { op := .join 0 1, subjectCount := 7, structural := false } ==
      Ix.Cli.AggregateCmd.aggregateStructuralJoinRamBytes +
        7 * Ix.Cli.AggregateCmd.aggregateFlatJoinRamPerSubjectBytes
  let memTotalParsing := Ix.Cli.AggregateCmd.aggregateMemTotalBytes
    "MemTotal:       1024 kB\nMemFree: 512 kB\n" == some (1024 * 1024)
  let invalidScheduleRejected : Bool := match
      Ix.Cli.AggregateCmd.schedulePlan #[.join 0 1] #[] 4 with
    | .error _ => true
    | .ok _ => false

  let fakeRun (scheduled : Array Ix.Cli.AggregateCmd.ScheduledFold)
      (slotIdx : Nat) (slots : Array (Option ByteArray)) :
      IO (Except String ByteArray) := do
    let some item := scheduled[slotIdx]? | return .error "missing fake slot"
    match item.op with
    | .leaf shard => pure (.ok ⟨#[UInt8.ofNat shard, UInt8.ofNat slotIdx]⟩)
    | .join leftIdx rightIdx =>
      let some leftPayload := (slots[leftIdx]?).join
        | return .error "missing fake left child"
      let some rightPayload := (slots[rightIdx]?).join
        | return .error "missing fake right child"
      pure (.ok ((leftPayload ++ rightPayload).push (UInt8.ofNat slotIdx)))
  let schedulerSerialParallelParity ← match mixedSchedule with
    | .error _ => pure false
    | .ok scheduled =>
      let serial ← Ix.Cli.AggregateCmd.runAggregateDag scheduled fakeWeights
        1 10 (fakeRun scheduled)
      let parallel ← Ix.Cli.AggregateCmd.runAggregateDag scheduled fakeWeights
        2 10 (fakeRun scheduled)
      pure <| match serial, parallel with
        | .ok serial, .ok parallel => serial == parallel
        | _, _ => false
  let dependentStarted ← IO.mkRef false
  let failureRun (slotIdx : Nat) (_ : Array (Option Nat)) :
      IO (Except String Nat) := do
    if slotIdx == 0 then return .error "intentional leaf failure"
    if slotIdx == 2 then dependentStarted.set true
    pure (.ok slotIdx)
  let schedulerStopsAfterFailure ← match mixedSchedule with
    | .error _ => pure false
    | .ok scheduled =>
      let result ← Ix.Cli.AggregateCmd.runAggregateDag scheduled fakeWeights
        2 10 failureRun
      let started ← dependentStarted.get
      pure <| match result with
        | .error e => e.startsWith "slot 0: intentional leaf failure" && !started
        | .ok _ => false

  -- Exercise concurrent proof generation through the same Aiur system. Zero
  -- query PoW has a canonical witness, so wrapper-byte equality isolates DAG
  -- determinism rather than rayon choosing different valid grind witnesses.
  let scheduledSystem := AiurSystem.build childCompiled.bytecode recCommitParams
    { innerFri with queryProofOfWorkBits := 0 }
  let scheduledVk := scheduledSystem.vkBytes
  let scheduledAllowed := Aggr.allowedBlob ixvmVk verifyIdx scheduledVk fakeAggrIdx
  let scheduledOuter (claim : Ix.Claim) :=
    Ix.Cli.AggregateCmd.aggregateOuterClaim scheduledAllowed fakeAggrIdx claim
  let scheduledProofSlot (slotIdx : Nat)
      (slots : Array (Option ByteArray)) : IO (Except String ByteArray) := do
    let claim := if slotIdx == 0 then left.claim
      else if slotIdx == 1 then right.claim else flatOutput.claim
    if slotIdx == 2 then
      for (childIdx, childClaim) in #[(0, left.claim), (1, right.claim)] do
        let some proofBytes := (slots[childIdx]?).join
          | return .error s!"scheduled pair missing child {childIdx}"
        let proof ← match Aiur.Proof.ofBytesChecked proofBytes with
          | .error e => return .error e
          | .ok proof => pure proof
        match scheduledSystem.verify (scheduledOuter childClaim) proof with
        | .ok () => pure ()
        | .error e => return .error e
    let claimBytes := Ix.Claim.ser claim
    let (outer, proof, _) ← match scheduledSystem.prove fakeAggrIdx
        (Aggr.pubInput scheduledAllowed claimBytes) default with
      | .error e => return .error e
      | .ok result => pure result
    if outer != scheduledOuter claim then
      return .error s!"scheduled slot {slotIdx} outer claim mismatch"
    pure (.ok proof.toBytes)
  let scheduledWrapperBytes (proofs : Array ByteArray) : Array ByteArray :=
    proofs.mapIdx fun slotIdx proof =>
      let claim := if slotIdx == 0 then left.claim
        else if slotIdx == 1 then right.claim else flatOutput.claim
      Ixon.Proof.ser { claim, proof }
  let concurrentProofWrappersStable ← match wrapPlan with
    | .error _ => pure false
    | .ok scheduled =>
      let serial ← Ix.Cli.AggregateCmd.runAggregateDag scheduled #[8, 8, 4]
        1 16 scheduledProofSlot
      let parallel ← Ix.Cli.AggregateCmd.runAggregateDag scheduled #[8, 8, 4]
        2 16 scheduledProofSlot
      pure <| match serial, parallel with
        | .ok serial, .ok parallel =>
          scheduledWrapperBytes serial == scheduledWrapperBytes parallel
        | _, _ => false

  lspecIO (.ofList [("ix-aggr-semantics", [
    test "default recursion parameters preserve direct construction"
      defaultRecursionIdentityPreserved,
    test "recursion FRI cache encoding is the pinned 40-byte layout"
      defaultFriEncodingStable,
    test "FRI and commitment overrides independently change recursion identity"
      recursionParametersIndependent,
    test "aggregate cache version is 2" (Ix.Cli.AggregateCmd.aggregateCacheVersion == 2),
    test "aggregate cache key is stable for identical inputs" cacheKeyStable,
    test "aggregate cache key binds the uniform outer claim" cacheKeyBindsOuter,
    test "aggregate cache key binds recursion FRI parameters" cacheKeyBindsFri,
    test "aggregate cache key binds the recursion verifying key" cacheKeyBindsVk,
    test "aggregate cache key rejects version-1 entries" cacheKeyBindsVersion,
    test "Rust and Lean aggregate cache identity share a fixed vector"
      cacheKeyMatchesRustVector,
    test "wrap-first specs precompute every uniform claim and cache key"
      wrapSpecsComplete,
    test "direct specs retain raw IxVM leaves and one aggregate root"
      directSpecsUseRawLeaves,
    test "wrap-first and direct policies derive the same flat root claim"
      policiesShareRootClaim,
    test "aggregate outer claims bind the exact CheckEnv value" outerClaimBindsValue,
    expectOk "cache accepts an exactly bound valid aggregate wrapper" validCached,
    expectErr "cache rejects a wrapper for a different CheckEnv"
      wrongCachedStatement,
    expectErr "cache rejects a proof under a different aggregate claim"
      wrongCachedOuter,
    expectErr "cache rejects corrupted aggregate proof bytes" badCachedProof,
    test "missing cache index is a clean miss" missingIndexIsMiss,
    test "cache index atomically round-trips a store address" cacheIndexRoundTrip,
    test "cache atomic update leaves no temporary entry" cacheTempGone,
    test "cache treats a corrupt index as an invalid hint" corruptIndexRejected,
    test "cache atomically replaces a corrupt index" corruptIndexRecovers,
    test "aggregate verifier accepts a content-addressed proof wrapper"
      wrapperContentAddressAccepted,
    test "aggregate verifier rejects a wrapper stored under the wrong address"
      wrapperContentAddressRejected,
    test "cache resumes a content-addressed verified aggregate wrapper" resumed?.isSome,
    test "cache treats corrupt store content as a miss" corruptStore?.isNone,
    test "flat host fold constructs canonical union/discharge trees" flatHostCorrect,
    test "structural host fold constructs root-of-roots and survivors"
      structuralHostCorrect,
    test "driver CheckEnv conversion round-trips free-form roots"
      hostConversionRoundTrip,
    test "manifest tree lowers to post-order binary slots"
      (manifestPlan == expectedPlan),
    test "manifest parser exposes its validated bisection tree" parsedManifestPlan,
    test "manifest parser rejects repeated aggregation leaves"
      malformedManifestRejected,
    test "coverage accepts legacy zero-constant manifest leaves" singleCoverage,
    test "empty manifest leaves contract and retained ids remap densely"
      emptyPruningCorrect,
    test "one retained shard reconstructs one value-based root" singletonValueRoot,
    test "native Stage 2 FFI plans a serialized environment end-to-end"
      nativePlanOnlyFfiWorks,
    test "native verifier orchestration reproduces the Stage 2 root claim"
      nativeVerifyRootMatches,
    test "two-shard manifest passes exact environment coverage" pairCoverage,
    test "aggregate startup prepares every shard from one ownership pass"
      batchedShardPreparationCorrect,
    test "flat manifest value equals the canonical environment root"
      manifestFlatIsCanonical,
    test "structural manifest value equals the manifest-relative hybrid root"
      manifestStructuralIsHybrid,
    test "flat and structural schedules produce distinguishable values"
      manifestValuesDiffer,
    test "shard prep preserves trees and one-pass closure semantics"
      shardPrepPreservesSemantics,
    test "verified aggregate proof audit certifies every fixture constant"
      aggregateProofAuditsEveryConstant,
    test "dated Mathlib Stage 2 proof verifies under the production backend"
      productionStage2FixtureValid,
    test "aggregate constant audit rejects an omitted environment constant"
      missingConstantRejected,
    test "aggregate constant audit rejects a foreign subject"
      foreignConstantRejected,
    test "aggregate constant audit rejects a duplicate subject"
      duplicateConstantRejected,
    test "aggregate constant audit rejects residual assumptions"
      residualAssumptionRejected,
    test "threshold scheduling is flat below and structural above monotonically"
      mixedScheduleCorrect,
    test "RAM-gated scheduler admits ready work heaviest-first"
      schedulerHeaviestFirst,
    test "RAM-gated scheduler respects job and byte budgets"
      schedulerWithinLimits,
    test "RAM-gated scheduler waits for both pair children"
      schedulerDependenciesHold,
    test "an individually oversized scheduler slot is admitted alone"
      oversizedRunsAlone,
    test "flat self-pair RAM reserve is affine in subject leaves"
      flatWeightAffine,
    test "aggregate scheduler parses MemTotal for its default budget"
      memTotalParsing,
    test "invalid non-post-order schedules are rejected" invalidScheduleRejected,
    test "jobs=2 DAG execution is byte-identical to jobs=1"
      schedulerSerialParallelParity,
    test "a failed slot drains peers without starting dependent pairs"
      schedulerStopsAfterFailure,
    test "jobs=2 zero-PoW aggregate wrappers are byte-identical to jobs=1"
      concurrentProofWrappersStable,
    expectOk "stand-in aggregate proof verifies under its uniform outer claim"
      (selfSystem.verify leftOuter leftProof),
    expectOk "second stand-in aggregate proof verifies independently"
      (selfSystem.verify rightOuter rightProof)
  ])]) []

def convergedSuite : IO UInt32 := do
  let shapes ← smokeSuite
  let semantics ← semanticSuite
  return if shapes == 0 && semantics == 0 then 0 else 1

end Tests.Aggr

end
