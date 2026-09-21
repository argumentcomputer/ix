module

public import Tests.Aggr
public import Ix.Cli.VerifyCmd

/-!
# Aggregate statements, manifests, and verification

Pure statement/plan checks and cross-language manifest tests complement the
production circuit tests in `Tests/Aggr.lean`. Native cache and scheduler
regressions live beside the Rust controller.
-/

public section

open LSpec Aiur

namespace Tests.Aggr

open Tests.ProofHelpers (expectOk expectErr recCommitParams innerFri u64le)

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
record rather than checked in. This proof predates both the a8aab731 protocol
bump and the Ixon v3 claim envelope. The gate re-hashes the exact old wrapper,
pins its root bytes and unconditional flag, and checks rejection at the format
boundary. No legacy decoding path is added to the production reader. -/
private def stage2FixturePinnedAndFenced : IO Bool := do
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
    if Address.blake3 bytes != address || bytes[0]! != 0xF2 ||
        bytes.extract 1 33 != root.hash || bytes[33]! != 0 then
      IO.eprintln "Stage 2 fixture bytes or historical root drifted"
      return false
    match Ix.Cli.VerifyCmd.decodeAggregateWrapperAt address bytes with
    | .error "claim: unsupported object format" => pure ()
    | _ =>
      IO.eprintln "Stage 2 fixture did not reject at its format boundary"
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
      if out.exitCode == 0 then
        IO.eprintln "obsolete Stage 2 fixture unexpectedly verified under the current protocol"
        return false
      unless out.stderr.contains "claim: unsupported object format" ||
          out.stdout.contains "claim: unsupported object format" do
        IO.eprintln s!"obsolete Stage 2 fixture failed for an unexpected reason \
({out.exitCode}): {out.stderr.take 500}"
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
  let recursionDefaults := Aggr.defaultRecursionParameters
  let defaultRecursionSystem :=
    Aggr.buildRecursionSystem childCompiled.bytecode recursionDefaults
  let directDefaultSystem := AiurSystem.build childCompiled.bytecode
    Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  let expectedDefaultFriBytes : ByteArray :=
    ⟨u64le 0 ++ u64le 1 ++ u64le 100 ++ u64le 0 ++ u64le 20⟩
  let tunedFri : Aiur.FriParameters :=
    { recursionDefaults.fri with numQueries := 50 }
  let tunedFriParameters : Aggr.RecursionParameters :=
    { recursionDefaults with fri := tunedFri }
  let tunedFriSystem :=
    Aggr.buildRecursionSystem childCompiled.bytecode tunedFriParameters
  let tunedCommitment : Aiur.CommitmentParameters :=
    { recursionDefaults.commitment with logBlowup := 3 }
  let tunedCommitmentParameters : Aggr.RecursionParameters :=
    { recursionDefaults with commitment := tunedCommitment }
  let tunedCommitmentSystem :=
    Aggr.buildRecursionSystem childCompiled.bytecode tunedCommitmentParameters
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

  let childRecursionParameters : Aggr.RecursionParameters := {
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
  let cacheVectorParameters : Aggr.RecursionParameters := {
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
      statement := left },
    { claim := right.claim,
      statement := right }
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
  let cachedAddress := Address.blake3 (Ixon.Proof.ser cachedWrapper)
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
  let productionStage2FixturePinnedAndFenced ← stage2FixturePinnedAndFenced

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
    test "aggregate verifier accepts a content-addressed proof wrapper"
      wrapperContentAddressAccepted,
    test "aggregate verifier rejects a wrapper stored under the wrong address"
      wrapperContentAddressRejected,
    test "flat host fold constructs canonical union/discharge trees" flatHostCorrect,
    test "structural host fold constructs root-of-roots and survivors"
      structuralHostCorrect,
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
    test "dated Mathlib Stage 2 proof is pinned and fenced at its protocol boundary"
      productionStage2FixturePinnedAndFenced,
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
    test "flat self-pair RAM reserve is affine in subject leaves"
      flatWeightAffine,
    test "aggregate scheduler parses MemTotal for its default budget"
      memTotalParsing,
    test "invalid non-post-order schedules are rejected" invalidScheduleRejected,
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
