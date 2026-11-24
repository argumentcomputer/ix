module

public import LSpec
public import Tests.ProofHelpers
public import Ix.Aggr.Reference
public import Ix.Aggr.Verification
public import Ix.Cli.VerifyCmd
public import Ix.Cli.ClaimPolicy
public import Ix.DynamicLink.Codec

/-!
# Aggregate statements, manifests, and verification

Pure statement/plan checks and cross-language manifest tests.
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

private def bound (env : Ixon.Env) : Ixon.Env :=
  match Ix.Kernel.Reader.defaultTableBytes, Ix.Kernel.Reader.defaultTableAddress with
  | .ok bytes, .ok address => { env with roleBinding := some { address, bytes } }
  | _, _ => env

private def envCtx : Ix.ClaimContext :=
  Ix.ClaimContext.ofDefaultTable.toOption.getD default

private def singletonIxonEnv : Ixon.Env × Address :=
  let constant : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, {}, 0, .sort 1, .sort 0⟩, #[], #[], #[.zero, .succ .zero], #[]⟩
  let address := Address.blake3 (Ixon.serConstant constant)
  (bound (({} : Ixon.Env).storeConst address constant), address)

private def pairIxonEnv : Ixon.Env × Address × Address :=
  let left : Ixon.Constant :=
    ⟨.defn ⟨.opaq, .safe, {}, 0, .sort 1, .sort 0⟩, #[], #[], #[.zero, .succ .zero], #[]⟩
  let right : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, {}, 0, .sort 1, .sort 0⟩, #[], #[], #[.zero, .succ .zero], #[]⟩
  let leftAddress := Address.blake3 (Ixon.serConstant left)
  let rightAddress := Address.blake3 (Ixon.serConstant right)
  let env := (({} : Ixon.Env).storeConst leftAddress left)
    |>.storeConst rightAddress right
  (bound env, leftAddress, rightAddress)

private def sharedClosureIxonEnv : Ixon.Env × Array Address × Address :=
  let shared : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, {}, 0, .sort 1, .sort 0⟩, #[], #[], #[.zero, .succ .zero], #[]⟩
  let sharedAddress := Address.blake3 (Ixon.serConstant shared)
  let left : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, {}, 0, .sort 1, .ref 0 #[]⟩, #[], #[sharedAddress], #[.zero, .succ .zero], #[]⟩
  let right : Ixon.Constant :=
    ⟨.defn ⟨.opaq, .safe, {}, 0, .sort 1, .ref 0 #[]⟩, #[], #[sharedAddress], #[.zero, .succ .zero], #[]⟩
  let leftAddress := Address.blake3 (Ixon.serConstant left)
  let rightAddress := Address.blake3 (Ixon.serConstant right)
  let env := (({} : Ixon.Env).storeConst sharedAddress shared)
    |>.storeConst leftAddress left
    |>.storeConst rightAddress right
  (bound env, #[leftAddress, rightAddress], sharedAddress)

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
    match Aggr.decodeAggregateWrapperAt address bytes with
    | .error e =>
      unless e.startsWith "claim: unsupported object format" do
        IO.eprintln s!"Stage 2 fixture did not reject at its format boundary: {e}"
        return false
    | .ok _ =>
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
        IO.eprintln "historical Stage 2 fixture unexpectedly verified under the current protocol"
        return false
      let fenced (s : String) : Bool :=
        s.contains "claim: unsupported object format" ||
          s.contains "InvalidProofShape" || s.contains "does not decode" ||
          s.contains "unrecognized proof format"
      unless fenced out.stderr || fenced out.stdout do
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
  let verifyIdx : Nat := 0
  let fakeAggrIdx : Nat := 1
  let ixvmVk := "standin-ixvm-vk".toUTF8
  let selfVk := "standin-aggr-vk".toUTF8
  let allowed := Aggr.allowedBlob ixvmVk verifyIdx selfVk fakeAggrIdx

  -- Recursion parameter and cache-key contract.
  let recursionDefaults := Aggr.defaultRecursionParameters
  let expectedDefaultFriBytes : ByteArray :=
    ⟨u64le 0 ++ u64le 1 ++ u64le 128 ++ u64le 0 ++ u64le 20⟩
  let tunedFri : Aiur.FriParameters :=
    { recursionDefaults.fri with numQueries := 50 }
  let tunedFriParameters : Aggr.RecursionParameters :=
    { recursionDefaults with fri := tunedFri }
  let tunedCommitment : Aiur.CommitmentParameters :=
    { recursionDefaults.commitment with logBlowup := 3 }
  let tunedCommitmentParameters : Aggr.RecursionParameters :=
    { recursionDefaults with commitment := tunedCommitment }
  let defaultFriEncodingStable :=
    recursionDefaults.cacheFriBytes.size == 40 &&
      recursionDefaults.cacheFriBytes == expectedDefaultFriBytes
  let recursionParametersIndependent :=
    tunedFriParameters.cacheFriBytes != recursionDefaults.cacheFriBytes &&
      tunedCommitmentParameters.cacheFriBytes == recursionDefaults.cacheFriBytes

  -- Two conditional statements whose assumptions cross the subject boundary.
  let a := Address.blake3 "aggr-semantics-a".toUTF8
  let b := Address.blake3 "aggr-semantics-b".toUTF8
  let c := Address.blake3 "aggr-semantics-c".toUTF8
  let d := Address.blake3 "aggr-semantics-d".toUTF8
  let left : Aggr.CheckEnvTrees := {
    ctx := envCtx
    subjects := canonicalTree #[a, b]
    assumptions := some (canonicalTree #[c, d])
  }
  let right : Aggr.CheckEnvTrees := {
    ctx := envCtx
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
  let selfAssumingClaim : Ix.Claim :=
    .checkEnv envCtx (canonicalTree #[a]).root (some (canonicalTree #[a]).root)
  let selfAssumingTrees : Std.HashMap Address Ix.AssumptionTree :=
    ({} : Std.HashMap _ _).insert (canonicalTree #[a]).root (canonicalTree #[a])
  let ofClaimRejectsSelfAssumption :=
    (Aggr.CheckEnvTrees.ofClaim selfAssumingClaim selfAssumingTrees).isOk == false
  let selfAssumingStmt : Aggr.CheckEnvTrees :=
    { ctx := envCtx, subjects := canonicalTree #[a],
      assumptions := some (canonicalTree #[a]) }
  let hostJoinRejectsSelfDischarge :=
    (selfAssumingStmt.join selfAssumingStmt).assumptions.map (·.leaves) == some #[a] &&
    (selfAssumingStmt.joinStructural selfAssumingStmt).assumptions.map (·.leaves) == some #[a]
  let flatBytes := Ix.Claim.ser flatOutput.claim
  let leftOuter := Aggr.aggregateOuterClaim
    allowed fakeAggrIdx left.claim
  let rightOuter := Aggr.aggregateOuterClaim
    allowed fakeAggrIdx right.claim
  let flatOuter := Aggr.aggregateOuterClaim
    allowed fakeAggrIdx flatOutput.claim
  let outerClaimBindsValue := leftOuter != rightOuter &&
    flatOuter == Aiur.buildClaim fakeAggrIdx (Aggr.pubInput allowed flatBytes) #[]

  let childRecursionParameters : Aggr.RecursionParameters := {
    commitment := recCommitParams
    fri := innerFri
  }
  let leftKey := Aggr.aggregateCacheKey selfVk
    childRecursionParameters leftOuter
  let cacheKeyStable := leftKey == Aggr.aggregateCacheKey
    selfVk childRecursionParameters leftOuter
  let cacheKeyBindsOuter := leftKey != Aggr.aggregateCacheKey
    selfVk childRecursionParameters rightOuter
  let cacheKeyBindsFri := leftKey != Aggr.aggregateCacheKey
    selfVk { childRecursionParameters with fri := tunedFri } leftOuter
  let cacheKeyBindsVk := leftKey != Aggr.aggregateCacheKey
    (selfVk.set! 0 (selfVk.data[0]! + 1)) childRecursionParameters leftOuter
  let cacheKeyBindsVersion := leftKey != Aggr.aggregateCacheKey
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
    toString (Aggr.aggregateCacheKey "vk".toUTF8
      cacheVectorParameters #[.ofNat 1, .ofNat 2, .ofNat 3]) ==
      "86ed059157e2915fe0a83f1afd58f31f7553659ad778669f6b795e1473e7afe0"

  let ops : Array Ix.Shard.AggregationTree.FoldOp :=
    #[.leaf 0, .leaf 1, .join 0 1]
  let wrapPlan := Aggr.Reference.schedulePlan ops #[2, 1] 8
  let directPlan := Aggr.Reference.schedulePlan ops #[2, 1] 8 true
  let prepared : Array Aggr.Reference.PreparedShard := #[
    { claim := left.claim,
      statement := left },
    { claim := right.claim,
      statement := right }
  ]
  let wrapSpecs := wrapPlan.bind fun plan =>
    Aggr.Reference.buildAggrSlotSpecs plan prepared selfVk allowed
      verifyIdx fakeAggrIdx childRecursionParameters
  let directSpecs := directPlan.bind fun plan =>
    Aggr.Reference.buildAggrSlotSpecs plan prepared selfVk allowed
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

  let cachedWrapper : Ixon.Proof := {
    claim := left.claim
    proof := "standin-proof".toUTF8
  }
  let cachedAddress := Address.blake3 (Ixon.Proof.ser cachedWrapper)
  let cachedBytes := Ixon.Proof.ser cachedWrapper
  let wrapperContentAddressAccepted : Bool :=
    match Aggr.decodeAggregateWrapperAt cachedAddress cachedBytes with
    | .ok wrapper =>
      wrapper.claim == cachedWrapper.claim && wrapper.proof == cachedWrapper.proof
    | .error _ => false
  let wrapperContentAddressRejected : Bool :=
    let wrongAddress := Address.blake3 (cachedBytes.push 0xff)
    match Aggr.decodeAggregateWrapperAt wrongAddress cachedBytes with
    | .error _ => true
    | .ok _ => false

  let manifestPlan :=
    (Ix.Shard.AggregationTree.node
      (.node (.leaf 0) (.leaf 1)) (.leaf 2)).foldPlan
  let expectedPlan : Array Ix.Shard.AggregationTree.FoldOp :=
    #[.leaf 0, .leaf 1, .join 0 1, .leaf 2, .join 2 3]
  let parsedManifestPlan : Bool :=
    let valid := minimalIxes (#[1, 1, 0] ++ u32le4 0 ++ #[0] ++ u32le4 1)
    match Ix.Shard.parseIxesManifest valid with
    | .ok view => view.aggregationTree.foldPlan ==
        (#[.leaf 0, .leaf 1, .join 0 1] :
          Array Ix.Shard.AggregationTree.FoldOp)
    | .error _ => false
  let malformedManifestRejected : Bool :=
    let duplicate := minimalIxes (#[1, 1, 0] ++ u32le4 0 ++ #[0] ++ u32le4 0)
    match Ix.Shard.parseIxesManifest duplicate with
    | .error _ => true
    | .ok _ => false
  let (singleEnv, singleAddr) := singletonIxonEnv
  let singleTreeTail := #[1, 1, 0] ++ u32le4 0 ++ #[1, 0] ++
    u32le4 1 ++ #[0] ++ u32le4 2
  let singleManifest := Ix.Shard.parseIxesManifest
    (minimalIxesFor #[#[], #[singleAddr], #[]] singleTreeTail)
  let singleCoverage ← match singleManifest with
    | .ok view => Ix.Shard.shardsCover singleEnv view.shards
    | .error _ => pure false
  let emptyPruningCorrect : Bool := match singleManifest with
    | .ok view => match view.pruneEmpty singleEnv with
      | .ok (pruned, counts) =>
        pruned.shards == #[#[singleAddr]] && pruned.shardIds == #[1] &&
          pruned.aggregationTree == .leaf 0 && counts == #[1]
      | .error _ => false
    | .error _ => false
  let singletonValueRoot : Bool := match singleManifest with
    | .ok view => match Aggr.Reference.expectedFromManifest singleEnv view 0 with
      | .ok statement =>
        statement.claim == .checkEnv envCtx (canonicalTree #[singleAddr]).root none
      | .error _ => false
    | .error _ => false

  let (pairEnv, pairLeft, pairRight) := pairIxonEnv
  let pairManifest := Ix.Shard.parseIxesManifest
    (minimalIxesFor #[#[pairLeft], #[pairRight]]
      (#[1, 1, 0] ++ u32le4 0 ++ #[0] ++ u32le4 1))
  let pairCoverage ← match pairManifest with
    | .ok view => Ix.Shard.shardsCover pairEnv view.shards
    | .error _ => pure false
  let batchedShardPreparationCorrect : Bool := match pairManifest with
    | .ok view =>
      match Aggr.Reference.prepareShards pairEnv view.shards view.shardIds with
      | .ok prepared =>
        prepared.map (·.claim) == (#[(.checkEnv envCtx
            (canonicalTree #[pairLeft]).root none : Ix.Claim),
          .checkEnv envCtx (canonicalTree #[pairRight]).root none] : Array Ix.Claim) &&
          prepared.all fun item => item.statement.claim == item.claim
      | .error _ => false
    | .error _ => false
  let flatManifestValue : Option Aggr.CheckEnvTrees := match pairManifest with
    | .ok view => (Aggr.Reference.expectedFromManifest pairEnv view 8).toOption
    | .error _ => none
  let structuralManifestValue : Option Aggr.CheckEnvTrees := match pairManifest with
    | .ok view => (Aggr.Reference.expectedFromManifest pairEnv view 0).toOption
    | .error _ => none
  let canonicalEnvTree := canonicalTree #[pairLeft, pairRight]
  let manifestFlatIsCanonical := flatManifestValue.map (·.claim) ==
    some (.checkEnv envCtx canonicalEnvTree.root none)
  let manifestStructuralIsHybrid := structuralManifestValue.map (·.claim) ==
    some (.checkEnv envCtx
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
      claimOnly == .checkEnv envCtx expectedOwned.root (some expectedFrontier.root) &&
        claimFull == claimOnly && sameClosure &&
        treesOnly.size == 2 && treesFull.size == 2 &&
        treesOnly.contains expectedOwned.root &&
        treesOnly.contains expectedFrontier.root &&
        treesFull.contains expectedOwned.root &&
        treesFull.contains expectedFrontier.root
    | _, _ => false

  let (auditEnv, auditOwned, auditShared) := sharedClosureIxonEnv
  let auditManifest := Ix.Shard.parseIxesManifest
    (minimalIxesFor #[auditOwned, #[auditShared]]
      (#[1, 1, 0] ++ u32le4 0 ++ #[0] ++ u32le4 1))
  let auditStatement := auditManifest.bind fun view =>
    Aggr.Reference.expectedFromManifest auditEnv view 0
  let aggregateProofAuditsEveryConstant : Bool := match auditStatement with
    | .error _ => false
    | .ok statement =>
      match Aggr.auditAggregateConstants auditEnv statement with
      | .ok count => count == 3
      | .error _ => false
  let auditLeaves := auditOwned.push auditShared
  let rejected (result : Except String Nat) : Bool :=
    match result with
    | .error _ => true
    | .ok _ => false
  let missingConstantRejected :=
    rejected (Aggr.auditAggregateConstants auditEnv {
      ctx := envCtx
      subjects := canonicalTree auditOwned
      assumptions := none
    })
  let foreignConstantRejected :=
    let foreign := Address.blake3 "aggregate-audit-foreign".toUTF8
    rejected (Aggr.auditAggregateConstants auditEnv {
      ctx := envCtx
      subjects := canonicalTree (auditLeaves.push foreign)
      assumptions := none
    })
  let duplicateConstantRejected :=
    rejected (Aggr.auditAggregateConstants auditEnv {
      ctx := envCtx
      subjects := .node (canonicalTree auditLeaves) (.leaf auditOwned[0]!)
      assumptions := none
    })
  let residualAssumptionRejected :=
    rejected (Aggr.auditAggregateConstants auditEnv {
      ctx := envCtx
      subjects := canonicalTree auditLeaves
      assumptions := some (canonicalTree #[auditShared])
    })
  let productionStage2FixturePinnedAndFenced ← stage2FixturePinnedAndFenced

  let mixedSchedule := Aggr.Reference.schedulePlan
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
    Aggr.Reference.aggregateSlotRamBytes
      { op := .join 0 1, subjectCount := 7, structural := false } ==
      Aggr.Reference.aggregateStructuralJoinRamBytes +
        7 * Aggr.Reference.aggregateFlatJoinRamPerSubjectBytes
  let memTotalParsing := Aggr.aggregateMemTotalBytes
    "MemTotal:       1024 kB\nMemFree: 512 kB\n" == some (1024 * 1024)
  let invalidScheduleRejected : Bool := match
      Aggr.Reference.schedulePlan #[.join 0 1] #[] 4 with
    | .error _ => true
    | .ok _ => false

  -- Dynamic circuit linking: Mode 3a isolation, wire round-trips, CodecTag injectivity,
  -- H2 full-tuple allowlist pinning, M6 bridge.binding & VerifyCmd CLI dispatch.
  let dlVk := Address.blake3 "dynlink-ext-vk".toUTF8
  let dlOtherVk := Address.blake3 "dynlink-other-vk".toUTF8
  let dlTarget := Address.blake3 "dynlink-target".toUTF8
  let dlOtherTarget := Address.blake3 "dynlink-other-target".toUTF8
  let dlCert := Address.blake3 "dynlink-cert".toUTF8
  let dlNatZeroCert := Address.blake3 "dynlink-nat-zero-cert".toUTF8
  let dlEvalType := Address.blake3 "dynlink-eval-type-nat".toUTF8
  let dlMyPropType := Address.blake3 "dynlink-eval-type-myprop".toUTF8
  let dlCustomBinding := Address.blake3 "dynlink-custom-binding".toUTF8
  let dlEvalRoot := (canonicalTree #[a]).root
  let codecTagNoAliasing : Bool :=
    Ix.DynamicLink.CodecTag.ofUInt64 0 == .rawWords &&
    Ix.DynamicLink.CodecTag.ofUInt64 1 == .ixonAddrPair &&
    Ix.DynamicLink.CodecTag.ofUInt64 2 == .ixonAddrSingle &&
    (Ix.DynamicLink.CodecTag.ofUInt64 3).toUInt64 == 3 &&
    Ix.DynamicLink.CodecTag.ofUInt64 3 != .rawWords &&
    Ix.DynamicLink.CodecTag.ofUInt64 3 != .ixonAddrPair &&
    Ix.DynamicLink.CodecTag.ofUInt64 3 != .ixonAddrSingle
  let dlBridge : Ix.DynamicLink.BridgeBinding := {
    spec := envCtx.spec
    binding := envCtx.binding
    targetConst := dlTarget
    codec := .rawWords
    certConst := dlCert
  }
  let dlStmt : Ix.DynamicLink.DynamicLinkStatement := {
    circuit := { vkDigest := dlVk, entryIdx := 7 }
    pubInputs := #[1, 2]
    pubOutputs := #[3]
    bridge? := some dlBridge
  }
  let dlStmtBytes := Ix.DynamicLink.serDynamicLink dlStmt
  let dlStmtRoundTripsAndDisjoint : Bool :=
    (Ix.DynamicLink.deDynamicLink dlStmtBytes).toOption == some dlStmt &&
      (Ix.Claim.de dlStmtBytes).isOk == false
  let dlEntry : Ix.DynamicLink.LinkedCircuitEntry := {
    vkDigest := dlVk
    entryIdx := 7
    codec := .ixonAddrPair
    targetConst := dlTarget
    certConst := dlCert
    evalType := dlEvalType
    spec := envCtx.spec
    binding := envCtx.binding
  }
  let dlEntryBytes := Ix.DynamicLink.serLinkedCircuitEntry dlEntry
  let dlEntryRoundTripsAndDisjoint : Bool :=
    (Ix.DynamicLink.deLinkedCircuitEntry dlEntryBytes).toOption == some dlEntry &&
      (Ix.Claim.de dlEntryBytes).isOk == false
  let dlLinkedTree := canonicalTree #[dlEntry.address]
  let dlEvalClaim : Ix.DynamicLink.EvalAssumedClaim := {
    ctx := envCtx
    kind := .check dlTarget
    assumptions := none
    evalAssumptions := dlEvalRoot
  }
  let dlLinkedClaim : Ix.DynamicLink.LinkedClaim :=
    dlEvalClaim.withLinkedCircuit none dlLinkedTree.root
  let dlLinkedClaimWithEvals : Ix.DynamicLink.LinkedClaim :=
    dlEvalClaim.withLinkedCircuit (some dlEvalRoot) dlLinkedTree.root
  let dlLinkedBytes := Ix.DynamicLink.serLinkedClaim dlLinkedClaim
  let dlLinkedBytesWithEvals := Ix.DynamicLink.serLinkedClaim dlLinkedClaimWithEvals
  let dlEvalBytes := Ix.DynamicLink.serEvalAssumedClaim dlEvalClaim
  -- Mode 3a transitions 10->12, 11->13, 12->12, 13->13 and can NEVER emit validator 3 or 4.
  let mode3aCannotEmitValidator3Or4 : Bool :=
    let modes : Array (Aggr.ValidatorMode Address) := #[
      .evalAssumed envCtx.binding,
      .bindingEvalAssumed envCtx.binding,
      .linked envCtx.binding,
      .bindingLinked envCtx.binding
    ]
    modes.all (fun m =>
      match m.toLinkedMode with
      | some outM =>
        outM.isLinked && outM.validatorCode != 3 && outM.validatorCode != 4 &&
          (outM.validatorCode == 12 || outM.validatorCode == 13) &&
          outM.dischargeAllEvals.isNone
      | none => false) &&
    dlLinkedClaim.validator == 12 &&
    (Ix.DynamicLink.deLinkedClaim dlLinkedBytes).toOption == some dlLinkedClaim &&
    (Ix.DynamicLink.deLinkedClaim dlLinkedBytesWithEvals).toOption == some dlLinkedClaimWithEvals &&
    (Ix.Claim.de dlLinkedBytes).isOk == false &&
    (Ix.Claim.de dlLinkedBytesWithEvals).isOk == false &&
    (Ix.Claim.de dlEvalBytes).isOk == false
  let defaultPolicy : Ix.Cli.ClaimPolicy.Policy := {}
  let defaultPolicyRefusesLinked : Bool :=
    match Ix.Cli.ClaimPolicy.refusalLinkedClaim defaultPolicy dlLinkedClaim (some #[dlEntry]) with
    | .ok (some msg) => msg.contains "dynamically linked external circuits"
    | _ => false
  let defaultPolicyRefusesDynamicBytes : Bool :=
    (match Ix.Cli.ClaimPolicy.refusalDynamicBytes defaultPolicy dlLinkedBytes (some #[dlEntry]) with
      | .ok (some _) => true | _ => false) &&
    (match Ix.Cli.ClaimPolicy.refusalDynamicBytes defaultPolicy dlEvalBytes none with
      | .ok (some _) => true | _ => false) &&
    (match Ix.Cli.ClaimPolicy.refusalDynamicBytes defaultPolicy dlStmtBytes none with
      | .ok (some _) => true | _ => false)
  let tier1AllowPolicy : Ix.Cli.ClaimPolicy.Policy :=
    match Ix.Cli.ClaimPolicy.parseAllowedDynamicCircuit s!"{dlVk}:7" with
    | .ok entry => { allowedDynamicCircuits := #[entry] }
    | .error _ => {}
  let exactLinkedAllowPolicy : Ix.Cli.ClaimPolicy.Policy :=
    match Ix.Cli.ClaimPolicy.parseAllowedLinkedCircuit s!"{dlVk}:7:{dlTarget}:{dlCert}:{dlEvalType}" with
    | .ok entry => { allowedLinkedCircuits := #[entry] }
    | .error _ => {}
  let explicitCodecLinkedAllowPolicy : Ix.Cli.ClaimPolicy.Policy :=
    match Ix.Cli.ClaimPolicy.parseAllowedLinkedCircuit s!"{dlVk}:7:ixonAddrPair:{dlTarget}:{dlCert}:{dlEvalType}" with
    | .ok entry => { allowedLinkedCircuits := #[entry] }
    | .error _ => {}
  let wrongEntryAllowPolicy : Ix.Cli.ClaimPolicy.Policy :=
    match Ix.Cli.ClaimPolicy.parseAllowedLinkedCircuit s!"{dlVk}:8:{dlTarget}:{dlCert}:{dlEvalType}" with
    | .ok entry => { allowedLinkedCircuits := #[entry] }
    | .error _ => {}
  let wrongVkAllowPolicy : Ix.Cli.ClaimPolicy.Policy :=
    match Ix.Cli.ClaimPolicy.parseAllowedLinkedCircuit s!"{dlOtherVk}:7:{dlTarget}:{dlCert}:{dlEvalType}" with
    | .ok entry => { allowedLinkedCircuits := #[entry] }
    | .error _ => {}
  let tamperedBindingEntry : Ix.DynamicLink.LinkedCircuitEntry :=
    { dlEntry with binding := Address.blake3 "wrong-binding".toUTF8 }
  let tamperedBindingClaim : Ix.DynamicLink.LinkedClaim :=
    { dlLinkedClaim with linkedCircuits := (canonicalTree #[tamperedBindingEntry.address]).root }
  let wrongCodecEntry : Ix.DynamicLink.LinkedCircuitEntry :=
    { dlEntry with codec := .rawWords }
  let wrongCodecClaim : Ix.DynamicLink.LinkedClaim :=
    { dlLinkedClaim with linkedCircuits := (canonicalTree #[wrongCodecEntry.address]).root }
  let wrongTargetEntry : Ix.DynamicLink.LinkedCircuitEntry :=
    { dlEntry with targetConst := dlOtherTarget }
  let wrongTargetClaim : Ix.DynamicLink.LinkedClaim :=
    { dlLinkedClaim with linkedCircuits := (canonicalTree #[wrongTargetEntry.address]).root }
  let forgedNatZeroCertEntry : Ix.DynamicLink.LinkedCircuitEntry :=
    { dlEntry with certConst := dlNatZeroCert }
  let forgedNatZeroCertClaim : Ix.DynamicLink.LinkedClaim :=
    { dlLinkedClaim with linkedCircuits := (canonicalTree #[forgedNatZeroCertEntry.address]).root }
  let forgedMyPropEntry : Ix.DynamicLink.LinkedCircuitEntry :=
    { dlEntry with evalType := dlMyPropType }
  let forgedMyPropClaim : Ix.DynamicLink.LinkedClaim :=
    { dlLinkedClaim with linkedCircuits := (canonicalTree #[forgedMyPropEntry.address]).root }
  let forgedMyTrueMyFalseEntry : Ix.DynamicLink.LinkedCircuitEntry :=
    { dlEntry with certConst := dlNatZeroCert, evalType := dlMyPropType }
  let forgedMyTrueMyFalseClaim : Ix.DynamicLink.LinkedClaim :=
    { dlLinkedClaim with linkedCircuits := (canonicalTree #[forgedMyTrueMyFalseEntry.address]).root }
  let allowlistPolicyChecks : Bool :=
    -- Exact Mode-3a allowlist (both 5-part and explicit :ixonAddrPair: 6-part) is accepted.
    (Ix.Cli.ClaimPolicy.refusalLinkedClaim exactLinkedAllowPolicy dlLinkedClaim (some #[dlEntry])).toOption == some none &&
    (Ix.Cli.ClaimPolicy.refusalLinkedClaim explicitCodecLinkedAllowPolicy dlLinkedClaim (some #[dlEntry])).toOption == some none &&
    (Ix.Cli.ClaimPolicy.refusalDynamicBytes exactLinkedAllowPolicy dlLinkedBytes (some #[dlEntry])).toOption == some none &&
    -- H2: VK-wide wildcard `<vk>` is strictly REJECTED by both parsers.
    (Ix.Cli.ClaimPolicy.parseAllowedDynamicCircuit s!"{dlVk}").isOk == false &&
    (Ix.Cli.ClaimPolicy.parseAllowedLinkedCircuit s!"{dlVk}").isOk == false &&
    (Ix.Cli.ClaimPolicy.parseAllowedLinkedCircuit s!"{dlVk}:7").isOk == false &&
    -- H2: Non-ixonAddrPair codecs are rejected by parseAllowedLinkedCircuit.
    (Ix.Cli.ClaimPolicy.parseAllowedLinkedCircuit s!"{dlVk}:7:rawWords:{dlTarget}:{dlCert}:{dlEvalType}").isOk == false &&
    (Ix.Cli.ClaimPolicy.parseAllowedLinkedCircuit s!"{dlVk}:7:0:{dlTarget}:{dlCert}:{dlEvalType}").isOk == false &&
    (Ix.Cli.ClaimPolicy.parseAllowedLinkedCircuit s!"{dlVk}:7:2:{dlTarget}:{dlCert}:{dlEvalType}").isOk == false &&
    -- H2: Tier-1 `--allow-dynamic-circuit <vk>:<entry>` CANNOT authorize Mode-3a LinkedClaim.
    (match Ix.Cli.ClaimPolicy.refusalLinkedClaim tier1AllowPolicy dlLinkedClaim (some #[dlEntry]) with
      | .ok (some msg) => msg.contains "--allow-linked-circuit" | _ => false) &&
    -- H2: Wrong codec / targetConst / certConst / evalType are ALL rejected even when (vk, entry) matches.
    (match Ix.Cli.ClaimPolicy.refusalLinkedClaim exactLinkedAllowPolicy wrongCodecClaim (some #[wrongCodecEntry]) with
      | .ok (some msg) => msg.contains "requires ixonAddrPair" | _ => false) &&
    (match Ix.Cli.ClaimPolicy.refusalLinkedClaim exactLinkedAllowPolicy wrongTargetClaim (some #[wrongTargetEntry]) with
      | .ok (some msg) => msg.contains "is not allowlisted" | _ => false) &&
    (match Ix.Cli.ClaimPolicy.refusalLinkedClaim exactLinkedAllowPolicy forgedNatZeroCertClaim (some #[forgedNatZeroCertEntry]) with
      | .ok (some msg) => msg.contains "is not allowlisted" | _ => false) &&
    (match Ix.Cli.ClaimPolicy.refusalLinkedClaim exactLinkedAllowPolicy forgedMyPropClaim (some #[forgedMyPropEntry]) with
      | .ok (some msg) => msg.contains "is not allowlisted" | _ => false) &&
    -- H2: Forged (myTrue, myFalse, MyProp) with certConst=Nat.zero cannot pass under either Tier-1 or Mode-3a allowlist.
    (match Ix.Cli.ClaimPolicy.refusalLinkedClaim tier1AllowPolicy forgedMyTrueMyFalseClaim (some #[forgedMyTrueMyFalseEntry]) with
      | .ok (some _) => true | _ => false) &&
    (match Ix.Cli.ClaimPolicy.refusalLinkedClaim exactLinkedAllowPolicy forgedMyTrueMyFalseClaim (some #[forgedMyTrueMyFalseEntry]) with
      | .ok (some msg) => msg.contains "is not allowlisted" | _ => false) &&
    -- Undischarged eval assumptions are refused even when allowlisted.
    (match Ix.Cli.ClaimPolicy.refusalLinkedClaim exactLinkedAllowPolicy dlLinkedClaimWithEvals (some #[dlEntry]) with
      | .ok (some msg) => msg.contains "undischarged eval assumptions" | _ => false) &&
    -- Missing preimages are refused even when allowlisted.
    (match Ix.Cli.ClaimPolicy.refusalLinkedClaim exactLinkedAllowPolicy dlLinkedClaim none with
      | .ok (some msg) => msg.contains "no LinkedCircuitEntry preimages" | _ => false) &&
    -- Mismatched preimage root is refused.
    (match Ix.Cli.ClaimPolicy.refusalLinkedClaim exactLinkedAllowPolicy dlLinkedClaim (some #[tamperedBindingEntry]) with
      | .ok (some msg) => msg.contains "not the claim's committed linkedCircuits root" | _ => false) &&
    -- Mismatched (spec, binding) inside an entry is refused even if its root matches.
    (match Ix.Cli.ClaimPolicy.refusalLinkedClaim exactLinkedAllowPolicy tamperedBindingClaim (some #[tamperedBindingEntry]) with
      | .ok (some msg) => msg.contains "differs from the claim's" | _ => false) &&
    -- Wrong entryIdx or wrong vkDigest is refused.
    (match Ix.Cli.ClaimPolicy.refusalLinkedClaim wrongEntryAllowPolicy dlLinkedClaim (some #[dlEntry]) with
      | .ok (some msg) => msg.contains "is not allowlisted" | _ => false) &&
    (match Ix.Cli.ClaimPolicy.refusalLinkedClaim wrongVkAllowPolicy dlLinkedClaim (some #[dlEntry]) with
      | .ok (some msg) => msg.contains "is not allowlisted" | _ => false) &&
    -- Malformed --allow-dynamic-circuit specifiers fail closed.
    (Ix.Cli.ClaimPolicy.parseAllowedDynamicCircuit "not-hex").isOk == false &&
    (Ix.Cli.ClaimPolicy.parseAllowedDynamicCircuit s!"{dlVk}:not-a-nat").isOk == false
  -- M6: refusalDynamicLinkStatement enforces bridge.binding/customBinding and codec arities.
  let dlStmtCustomBinding : Ix.DynamicLink.DynamicLinkStatement :=
    { dlStmt with bridge? := some { dlBridge with binding := dlCustomBinding } }
  let dlStmtBadPairArity : Ix.DynamicLink.DynamicLinkStatement :=
    { dlStmt with
      pubInputs := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
      pubOutputs := #[]
      bridge? := some { dlBridge with codec := .ixonAddrPair } }
  let dlStmtGoodPairArity : Ix.DynamicLink.DynamicLinkStatement :=
    { dlStmt with
      pubInputs := #[1, 2, 3, 4, 5, 6, 7, 8]
      pubOutputs := #[9, 10, 11, 12, 13, 14, 15, 16]
      bridge? := some { dlBridge with codec := .ixonAddrPair } }
  let dlStmtBadSingleArity : Ix.DynamicLink.DynamicLinkStatement :=
    { dlStmt with
      pubInputs := #[1, 2, 3, 4, 5, 6, 7, 8]
      pubOutputs := #[9]
      bridge? := some { dlBridge with codec := .ixonAddrSingle } }
  let dlStmtGoodSingleArity : Ix.DynamicLink.DynamicLinkStatement :=
    { dlStmt with
      pubInputs := #[1, 2, 3, 4, 5, 6, 7, 8]
      pubOutputs := #[]
      bridge? := some { dlBridge with codec := .ixonAddrSingle } }
  let tier1CustomBindingAllowPolicy : Ix.Cli.ClaimPolicy.Policy :=
    { tier1AllowPolicy with customBinding := true }
  let dynamicLinkStatementPolicyChecks : Bool :=
    -- Default role binding + allowlisted (vk, entry) accepted for rawWords, 8+8 ixonAddrPair, 8+0 ixonAddrSingle.
    (Ix.Cli.ClaimPolicy.refusalDynamicLinkStatement tier1AllowPolicy dlStmt).toOption == some none &&
    (Ix.Cli.ClaimPolicy.refusalDynamicLinkStatement tier1AllowPolicy dlStmtGoodPairArity).toOption == some none &&
    (Ix.Cli.ClaimPolicy.refusalDynamicLinkStatement tier1AllowPolicy dlStmtGoodSingleArity).toOption == some none &&
    -- Custom bridge.binding rejected without --allow-custom-binding or tableAdmitted.
    (match Ix.Cli.ClaimPolicy.refusalDynamicLinkStatement tier1AllowPolicy dlStmtCustomBinding with
      | .ok (some msg) => msg.contains "--allow-custom-binding" | _ => false) &&
    -- Accepted when tableAdmitted or --allow-custom-binding is set.
    (Ix.Cli.ClaimPolicy.refusalDynamicLinkStatement tier1AllowPolicy dlStmtCustomBinding (tableAdmitted := true)).toOption == some none &&
    (Ix.Cli.ClaimPolicy.refusalDynamicLinkStatement tier1CustomBindingAllowPolicy dlStmtCustomBinding).toOption == some none &&
    -- Wrong codec arities rejected (16-in/0-out predicate cannot pose as ixonAddrPair; 8-in/1-out cannot pose as ixonAddrSingle).
    (match Ix.Cli.ClaimPolicy.refusalDynamicLinkStatement tier1AllowPolicy dlStmtBadPairArity with
      | .ok (some msg) => msg.contains "8 pubInputs and 8 pubOutputs" | _ => false) &&
    (match Ix.Cli.ClaimPolicy.refusalDynamicLinkStatement tier1AllowPolicy dlStmtBadSingleArity with
      | .ok (some msg) => msg.contains "8 pubInputs and 0 pubOutputs" | _ => false)
  -- M6: VerifyCmd CLI dispatch fails closed on <vk> wildcards and routes --dynamic-claim through ClaimPolicy.
  let verifyCmdDynamicDispatchChecks ← do
    let tmpDir ← IO.FS.createTempDir
    try
      let linkedClaimFile := tmpDir / "linked.claim"
      let evalClaimFile := tmpDir / "eval.claim"
      let customDlFile := tmpDir / "custom-dl.claim"
      let entryFile := tmpDir / "entry.bin"
      IO.FS.writeBinFile linkedClaimFile dlLinkedBytes
      IO.FS.writeBinFile evalClaimFile dlEvalBytes
      IO.FS.writeBinFile customDlFile (Ix.DynamicLink.serDynamicLink dlStmtCustomBinding)
      IO.FS.writeBinFile entryFile dlEntryBytes
      let rcWildcard ← verifyCmd.validate ["--allow-dynamic-circuit", s!"{dlVk}"]
      let rcDefaultLinked ← verifyCmd.validate ["--dynamic-claim", linkedClaimFile.toString, "--linked-entry", entryFile.toString]
      let rcTier1OnLinked ← verifyCmd.validate ["--dynamic-claim", linkedClaimFile.toString, "--linked-entry", entryFile.toString, "--allow-dynamic-circuit", s!"{dlVk}:7"]
      let rcEvalAssumed ← verifyCmd.validate ["--dynamic-claim", evalClaimFile.toString]
      let rcCustomBinding ← verifyCmd.validate ["--dynamic-claim", customDlFile.toString, "--allow-dynamic-circuit", s!"{dlVk}:7"]
      pure (rcWildcard != 0 && rcDefaultLinked != 0 && rcTier1OnLinked != 0 &&
        rcEvalAssumed != 0 && rcCustomBinding != 0)
    finally
      IO.FS.removeDirAll tmpDir

  lspecIO (.ofList [("ix-aggr-semantics", [
    test "recursion FRI cache encoding is the pinned 40-byte layout"
      defaultFriEncodingStable,
    test "FRI and commitment overrides independently change recursion identity"
      recursionParametersIndependent,
    test "aggregate cache version is 2" (Aggr.aggregateCacheVersion == 2),
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
    test "CheckEnvTrees.ofClaim rejects overlapping subjects and assumptions"
      ofClaimRejectsSelfAssumption,
    test "host join helpers do not self-discharge assumptions"
      hostJoinRejectsSelfDischarge,
    test "manifest tree lowers to post-order binary slots"
      (manifestPlan == expectedPlan),
    test "manifest parser exposes its validated bisection tree" parsedManifestPlan,
    test "manifest parser rejects repeated aggregation leaves"
      malformedManifestRejected,
    test "coverage accepts legacy zero-constant manifest leaves" singleCoverage,
    test "empty manifest leaves contract and retained ids remap densely"
      emptyPruningCorrect,
    test "one retained shard reconstructs one value-based root" singletonValueRoot,
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
    test "dated Mathlib Stage 2 proof is pinned and rejected by the current protocol"
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
    test "CodecTag has no custom aliasing for tags 0/1/2" codecTagNoAliasing,
    test "DynamicLinkStatement with (spec, binding) BridgeBinding round-trips and is rejected by Claim.de"
      dlStmtRoundTripsAndDisjoint,
    test "LinkedCircuitEntry (0xE8 0x0F, with evalType) round-trips and is rejected by Claim.de"
      dlEntryRoundTripsAndDisjoint,
    test "Shape 18 Mode 3a cannot emit validator 3/4 or erase linkedCircuits"
      mode3aCannotEmitValidator3Or4,
    test "ClaimPolicy rejects linkedCircuits != none (validators 12/13) by default"
      defaultPolicyRefusesLinked,
    test "ClaimPolicy.refusalDynamicBytes rejects LinkedClaim, EvalAssumedClaim, and DynamicLinkStatement by default"
      defaultPolicyRefusesDynamicBytes,
    test "ClaimPolicy enforces no wildcard, separate Mode-3a allowlist, full tuple pinning, and rejects forged (myTrue, myFalse, MyProp)"
      allowlistPolicyChecks,
    test "ClaimPolicy.refusalDynamicLinkStatement enforces bridge.binding/customBinding and codec arities"
      dynamicLinkStatementPolicyChecks,
    test "VerifyCmd CLI fails closed on <vk> wildcards and routes --dynamic-claim through ClaimPolicy"
      verifyCmdDynamicDispatchChecks
  ])]) []

def convergedSuite : IO UInt32 := semanticSuite

end Tests.Aggr

end
