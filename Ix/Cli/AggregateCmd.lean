/-
  `ix aggregate --ixe E --ixes M <shard-proof>...`

  Bind persisted shard proof wrappers to every nonempty shard in a manifest,
  lift each IxVM proof into the Multi-STARK recursion system, then execute/prove
  any binary joins in the manifest's bisection-tree order. Small joins use flat
  canonical subjects; joins above `--structural-above` use an O(1)
  root-of-roots subject fold plus assumption-membership paths. The final
  persisted wrapper carries the aggregate `CheckEnv` claim and recursive proof
  bytes.

  The host driver remains serial, but every completed lift/join is persisted in
  a verified, content-addressed resume cache. Parallel slot scheduling remains
  a follow-up optimization rather than a protocol change.
-/
module
public import Cli
public import Ix.Cli.CheckCmd
public import Ix.IxVM
public import Ix.IxVM.ClaimHarness
public import Ix.MultiStark
public import Ix.Store

public section

namespace Ix.Cli.AggregateCmd

open IxVM.ClaimHarness

structure PreparedShard where
  claim : Ix.Claim
  statement : MultiStark.CheckEnvTrees

structure AggregateSlot where
  statement : MultiStark.CheckEnvTrees
  subjectCount : Nat
  outerClaim : Array Aiur.G
  proof : Aiur.Proof
  proofAddress? : Option Address
  /-- Preimages needed when this slot is decoded by its parent. A lift exposes
  its inner claims plus `CheckEnv`; a join exposes only its output `CheckEnv`. -/
  openPreimages : Array ByteArray

/-- Everything claim-derived about a slot, computed for the whole fold before
the first cache lookup or proof. -/
structure AggregateSlotSpec where
  statement : MultiStark.CheckEnvTrees
  subjectCount : Nat
  outerClaim : Array Aiur.G
  cacheKey : Address

structure CachedAggregateProof where
  proof : Aiur.Proof
  address : Address

inductive AggregateCacheAddress where
  | miss
  | hit (address : Address)
  | invalid (reason : String)
  deriving Repr

/-- A manifest fold operation annotated with the cumulative subject count and
the monotone flat/structural choice used by the prover. -/
structure ScheduledFold where
  op : Ix.Cli.CheckCmd.AggregationTree.FoldOp
  subjectCount : Nat
  structural : Bool
  deriving BEq, Repr

def defaultStructuralAbove : Nat := 4096

/-- Bump when aggregate advice framing changes without changing the recursion
verifying key. Encoded as `u64` little-endian in every cache key. -/
def aggregateCacheVersion : Nat := 1

/--
`blake3(version ‖ recursion_vk_digest ‖ fri_params_ser ‖ outer_claim_bytes)`.

`serializeClaims #[outerClaim]` is the canonical, length-delimited outer-claim
encoding. The expected outer claim already commits to the entrypoint and public
input; joins therefore transitively pin the allowed blob and output statement.
-/
def aggregateCacheKey (recursionVk : ByteArray)
    (recursionParameters : MultiStark.RecursionParameters)
    (outerClaim : Array Aiur.G) (version : Nat := aggregateCacheVersion) : Address :=
  let recursionVkDigest := (Address.blake3 recursionVk).hash
  let outerClaimBytes := MultiStark.serializeClaims #[outerClaim]
  Address.blake3 ⟨MultiStark.u64le version ++ recursionVkDigest.data ++
    recursionParameters.cacheFriBytes.data ++ outerClaimBytes.data⟩

/-- Resolve the global aggregate cache or a hermetic test root. -/
def aggregateCacheDir (cacheRoot : Option System.FilePath := none) : IO System.FilePath := do
  match cacheRoot with
  | some root =>
    let dir := root / "aggregate"
    IO.FS.createDirAll dir
    pure dir
  | none => StoreIO.toIO (Store.cacheDir "aggregate")

/-- Read an untrusted cache-index entry without turning malformed content into
a command failure. Store loading and proof verification happen separately. -/
def readAggregateCacheAddress (dir : System.FilePath) (key : Address) :
    IO AggregateCacheAddress := do
  let path := dir / toString key
  if !(← path.pathExists) then return .miss
  try
    let raw ← IO.FS.readFile path
    match Address.fromString raw.trimAscii.toString with
    | some address => return .hit address
    | none => return .invalid "index content is not a 64-character store address"
  catch e =>
    return .invalid s!"index read failed: {e}"

/-- Atomically replace one derived cache-index entry. -/
def writeAggregateCacheAddress (dir : System.FilePath) (key address : Address) :
    IO Unit := do
  let tmp := dir / s!"{key}.tmp"
  IO.FS.writeFile tmp s!"{address}\n"
  IO.FS.rename tmp (dir / toString key)

/-- A cached wrapper is reusable only when both its bundled `CheckEnv` claim
and its proof under the exact expected outer Aiur claim validate. -/
def validateAggregateCacheWrapper (recursionSystem : Aiur.AiurSystem)
    (expectedClaim : Ix.Claim) (expectedOuterClaim : Array Aiur.G)
    (wrapper : Ixon.Proof) : Except String Aiur.Proof := do
  if wrapper.claim != expectedClaim then
    throw s!"bundled claim {wrapper.claim} does not match expected {expectedClaim}"
  let proof ← Aiur.Proof.ofBytesChecked wrapper.proof
  recursionSystem.verify expectedOuterClaim proof
  pure proof

/-- Resolve subject counts and the structural threshold once, before proving.
Because parent counts only grow, `count > structuralAbove` makes the mode
monotone: a flat join is never scheduled above a structural child. -/
def schedulePlan (plan : Array Ix.Cli.CheckCmd.AggregationTree.FoldOp)
    (shardCounts : Array Nat) (structuralAbove : Nat) :
    Except String (Array ScheduledFold) := do
  let mut scheduled : Array ScheduledFold := #[]
  for op in plan do
    match op with
    | .leaf shard =>
      let some count := shardCounts[shard]?
        | throw s!"aggregate plan references missing shard {shard}"
      scheduled := scheduled.push { op, subjectCount := count, structural := false }
    | .join left right =>
      let some leftSlot := scheduled[left]?
        | throw s!"aggregate plan references missing left slot {left}"
      let some rightSlot := scheduled[right]?
        | throw s!"aggregate plan references missing right slot {right}"
      let count := leftSlot.subjectCount + rightSlot.subjectCount
      scheduled := scheduled.push {
        op, subjectCount := count, structural := count > structuralAbove
      }
  pure scheduled

/-- Derive every slot statement, outer claim, and cache key before proving.
This makes resume independent of execution order and lets manifest changes
invalidate only the claim-changed subtree. -/
def buildAggregateSlotSpecs (plan : Array ScheduledFold)
    (prepared : Array PreparedShard) (ixvmVk recursionVk allowed : ByteArray)
    (verifyIdx liftIdx joinIdx structuralJoinIdx : Aiur.Bytecode.FunIdx)
    (recursionParameters : MultiStark.RecursionParameters) :
    Except String (Array AggregateSlotSpec) := do
  let mut specs : Array AggregateSlotSpec := #[]
  for item in plan do
    match item.op with
    | .leaf shard =>
      let some preparedShard := prepared[shard]?
        | throw s!"aggregate plan references missing prepared shard {shard}"
      if preparedShard.claim != preparedShard.statement.claim then
        throw s!"prepared shard {shard} claim and statement disagree"
      if preparedShard.statement.subjectCount != item.subjectCount then
        throw s!"prepared shard {shard} has {preparedShard.statement.subjectCount} \
          subjects, but the schedule records {item.subjectCount}"
      let claimBytes := Ix.Claim.ser preparedShard.claim
      let verifyInput := IxVM.ClaimHarness.packedDigestKey
        (Address.blake3 claimBytes)
      let innerClaim := Aiur.buildClaim verifyIdx verifyInput #[]
      let innerClaimsBytes := MultiStark.serializeClaims #[innerClaim]
      let pubInput := MultiStark.verifierPubInput ixvmVk innerClaimsBytes
      let outerClaim := Aiur.buildClaim liftIdx pubInput #[]
      specs := specs.push {
        statement := preparedShard.statement
        subjectCount := item.subjectCount
        outerClaim
        cacheKey := aggregateCacheKey recursionVk recursionParameters outerClaim
      }
    | .join leftIdx rightIdx =>
      let some left := specs[leftIdx]?
        | throw s!"aggregate plan references missing left spec {leftIdx}"
      let some right := specs[rightIdx]?
        | throw s!"aggregate plan references missing right spec {rightIdx}"
      if left.subjectCount + right.subjectCount != item.subjectCount then
        throw "aggregate plan has inconsistent joined subject counts"
      let output := if item.structural then
          left.statement.joinStructural right.statement
        else
          left.statement.join right.statement
      if output.subjectCount != item.subjectCount then
        throw s!"aggregate join reconstructs {output.subjectCount} subjects, \
          but the schedule records {item.subjectCount}"
      let outputClaimBytes := Ix.Claim.ser output.claim
      let pubInput := MultiStark.joinPubInput allowed outputClaimBytes
      let joinFunIdx := if item.structural then structuralJoinIdx else joinIdx
      let outerClaim := Aiur.buildClaim joinFunIdx pubInput #[]
      specs := specs.push {
        statement := output
        subjectCount := item.subjectCount
        outerClaim
        cacheKey := aggregateCacheKey recursionVk recursionParameters outerClaim
      }
  pure specs

private def addrOfHex (label value : String) : Except String Address :=
  match Address.fromString value with
  | some address => .ok address
  | none => .error
    s!"{label}: expected a 64-character address, got {value.length} characters"

private def prepareShard (env : Ixon.Env) (blocks : Array Address) :
    Except String PreparedShard := do
  let owned := Ix.Cli.CheckCmd.ownedConstsForBlocks env blocks
  let (claim, trees) ← IxVM.ClaimHarness.shardCheckEnvClaimTrees env owned
  let statement ← MultiStark.CheckEnvTrees.ofClaim claim trees
  pure { claim, statement }

private def compileToplevel (label : String)
    (source : Except Aiur.Global Aiur.Source.Toplevel) :
    IO (Except String Aiur.CompiledToplevel) := do
  match source with
  | .error e => return Except.error s!"{label} toplevel merge failed: {e}"
  | .ok top => match top.compile with
    | .error e => return Except.error s!"{label} compilation failed: {e}"
    | .ok compiled => return Except.ok compiled

def loadCachedAggregateProofWith
    (readStore : Address → IO ByteArray) (dir : System.FilePath) (slotIdx : Nat)
    (spec : AggregateSlotSpec) (recursionSystem : Aiur.AiurSystem) :
    IO (Option CachedAggregateProof) := do
  match ← readAggregateCacheAddress dir spec.cacheKey with
  | .miss => return none
  | .invalid reason =>
    IO.println s!"[aggregate] slot {slotIdx}: cache miss ({reason})"
    return none
  | .hit address =>
    try
      let bytes ← readStore address
      if Address.blake3 bytes != address then
        IO.println s!"[aggregate] slot {slotIdx}: cache miss \
          (store object {address} has a different content digest)"
        return none
      let wrapper ← match Ixon.Proof.de bytes with
        | .ok wrapper => pure wrapper
        | .error e =>
          IO.println s!"[aggregate] slot {slotIdx}: cache miss \
            (wrapper {address} does not decode: {e})"
          return none
      match validateAggregateCacheWrapper recursionSystem spec.statement.claim
          spec.outerClaim wrapper with
      | .ok proof =>
        IO.println s!"[aggregate] slot {slotIdx}: cache hit {address}"
        return some { proof, address }
      | .error e =>
        IO.println s!"[aggregate] slot {slotIdx}: cache miss \
          (wrapper {address} rejected: {e})"
        return none
    catch e =>
      IO.println s!"[aggregate] slot {slotIdx}: cache miss \
        (cannot load wrapper {address}: {e})"
      return none

private def loadCachedAggregateProof (dir : System.FilePath) (slotIdx : Nat)
    (spec : AggregateSlotSpec) (recursionSystem : Aiur.AiurSystem) :
    IO (Option CachedAggregateProof) :=
  loadCachedAggregateProofWith (fun address => StoreIO.toIO (Store.read address))
    dir slotIdx spec recursionSystem

private def persistAggregateCacheProof (dir : System.FilePath) (slotIdx : Nat)
    (spec : AggregateSlotSpec) (proof : Aiur.Proof) : IO (Option Address) := do
  try
    let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser spec.statement.claim))
    let wrapper : Ixon.Proof := { claim := spec.statement.claim, proof := proof.toBytes }
    let address ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
    writeAggregateCacheAddress dir spec.cacheKey address
    IO.println s!"[aggregate] slot {slotIdx}: cached proof {address}"
    return some address
  catch e =>
    IO.eprintln s!"[aggregate] slot {slotIdx}: warning: could not persist cache entry: {e}"
    return none

private def printPlan (plan : Array ScheduledFold) (shardIds : Array Nat)
    (structuralAbove : Nat) : IO Unit := do
  let lifts := plan.countP fun item => match item.op with
    | .leaf _ => true
    | .join _ _ => false
  let structural := plan.countP (·.structural)
  IO.println s!"[aggregate] plan: {lifts} lifts + {plan.size - lifts} binary joins \
    ({structural} structural; threshold > {structuralAbove} subject leaves)"
  for (item, slot) in plan.mapIdx fun slot item => (item, slot) do
    match item.op with
    | .leaf shard =>
      let originalShard := (shardIds[shard]?).getD shard
      IO.println s!"  slot {slot}: lift shard {originalShard} ({item.subjectCount} subjects)"
    | .join left right =>
      let mode := if item.structural then "structural" else "flat"
      IO.println s!"  slot {slot}: {mode} join slots {left}, {right} \
        ({item.subjectCount} subjects)"

/-- Aggregate with an explicit recursion-proof configuration. The CLI wrapper
below supplies `defaultRecursionParameters`; keeping this seam explicit lets a
future policy or cache layer select a recursion configuration without changing
the canonical IxVM proof parameters. -/
def runAggregateCmdWith (recursionParameters : MultiStark.RecursionParameters)
    (p : Cli.Parsed) : IO UInt32 := do
  let some ixePath := (p.flag? "ixe").map (·.as! String) | do
    p.printError "error: aggregate requires --ixe <env.ixe>"
    return 1
  let some manifestPath := (p.flag? "ixes").map (·.as! String) | do
    p.printError "error: aggregate requires --ixes <manifest.ixes>"
    return 1

  let rawView ← match Ix.Cli.CheckCmd.parseIxesManifest
      (← IO.FS.readBinFile manifestPath) with
    | .error e => IO.eprintln s!"manifest parse failed: {e}"; return 1
    | .ok view => pure view
  let env ← match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
    | .error e => IO.eprintln s!"deserialize {ixePath} failed: {e}"; return 1
    | .ok env => pure env
  if !(← Ix.Cli.CheckCmd.shardsCover env rawView.shards) then return 1
  let (view, shardCounts) ← match rawView.pruneEmpty env with
    | .error e => IO.eprintln e; return 1
    | .ok pruned => pure pruned
  let prunedCount := rawView.shards.size - view.shards.size
  if prunedCount != 0 then
    IO.println s!"[aggregate] pruned {prunedCount} zero-constant manifest shard(s)"

  let structuralAbove := ((p.flag? "structural-above").map (·.as! Nat)).getD
    defaultStructuralAbove
  let plan ← match schedulePlan view.aggregationTree.foldPlan shardCounts structuralAbove with
    | .error e => IO.eprintln e; return 1
    | .ok plan => pure plan
  printPlan plan view.shardIds structuralAbove
  if p.hasFlag "plan-only" then return 0

  let proofHexes := (p.variableArgsAs! String).toList
  if proofHexes.length != view.shards.size then
    IO.eprintln s!"aggregate requires exactly {view.shards.size} shard proofs; got {proofHexes.length}"
    return 1

  -- Reconstruct every shard statement/tree from the environment once. This
  -- both binds proof wrappers to shard ids and supplies canonical join advice.
  let mut prepared : Array PreparedShard := #[]
  let mut digestToShard : Std.HashMap Address Nat := {}
  for (blocks, shard) in view.shards.mapIdx fun shard blocks => (blocks, shard) do
    let originalShard := (view.shardIds[shard]?).getD shard
    let item ← match prepareShard env blocks with
      | .error e => IO.eprintln s!"prepare shard {originalShard}: {e}"; return 1
      | .ok item => pure item
    let digest := Address.blake3 (Ix.Claim.ser item.claim)
    if digestToShard.contains digest then
      IO.eprintln s!"duplicate reconstructed shard claim digest {digest} \
        (manifest shard {originalShard})"
      return 1
    digestToShard := digestToShard.insert digest shard
    prepared := prepared.push item

  -- Proof arguments may be in any order. Match them by their bundled claim and
  -- reject duplicates/missing shards before starting an expensive lift.
  let mut proofsByShard : Std.HashMap Nat Ixon.Proof := {}
  for proofHex in proofHexes do
    let proofAddress ← match addrOfHex "shard proof" proofHex with
      | .error e => IO.eprintln e; return 1
      | .ok address => pure address
    let wrapper ← match Ixon.Proof.de (← StoreIO.toIO (Store.read proofAddress)) with
      | .error e => IO.eprintln s!"decode shard proof {proofAddress}: {e}"; return 1
      | .ok wrapper => pure wrapper
    let digest := Address.blake3 (Ix.Claim.ser wrapper.claim)
    let some shard := digestToShard.get? digest | do
      IO.eprintln s!"proof {proofAddress} claim {digest} matches no manifest shard"
      return 1
    let some expected := prepared[shard]? | do
      IO.eprintln s!"internal: missing prepared shard {shard}"
      return 1
    let originalShard := (view.shardIds[shard]?).getD shard
    if wrapper.claim != expected.claim then
      IO.eprintln s!"proof {proofAddress} hit a claim-digest collision for shard {originalShard}"
      return 1
    if proofsByShard.contains shard then
      IO.eprintln s!"more than one proof supplied for shard {originalShard}"
      return 1
    proofsByShard := proofsByShard.insert shard wrapper
  if proofsByShard.size != view.shards.size then
    IO.eprintln "not every manifest shard has a supplied proof"
    return 1

  let ixvmCompiled ← match ← compileToplevel "IxVM" IxVM.ixVM with
    | .error e => IO.eprintln e; return 1
    | .ok compiled => pure compiled
  let recursionCompiled ← match ← compileToplevel "MultiStark recursion"
      MultiStark.multiStark with
    | .error e => IO.eprintln e; return 1
    | .ok compiled => pure compiled
  let verifyIdx := ixvmCompiled.getFuncIdx `verify_claim |>.get!
  let liftIdx := recursionCompiled.getFuncIdx `verify_multi_stark_proof |>.get!
  let joinIdx := recursionCompiled.getFuncIdx `join_two |>.get!
  let structuralJoinIdx := recursionCompiled.getFuncIdx `join_two_structural |>.get!
  let ixvmSystem := Aiur.AiurSystem.build ixvmCompiled.bytecode
    Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  let recursionSystem := MultiStark.buildRecursionSystem recursionCompiled.bytecode
    recursionParameters
  let ixvmVk := ixvmSystem.vkBytes
  let recursionVk := recursionSystem.vkBytes
  let allowed := MultiStark.allowedBlob ixvmVk verifyIdx recursionVk liftIdx
    joinIdx structuralJoinIdx
  let specs ← match buildAggregateSlotSpecs plan prepared ixvmVk recursionVk allowed
      verifyIdx liftIdx joinIdx structuralJoinIdx recursionParameters with
    | .error e => IO.eprintln s!"prepare aggregate slots: {e}"; return 1
    | .ok specs => pure specs
  let cacheDir? ← if p.hasFlag "no-cache" then
      IO.println "[aggregate] cache disabled (--no-cache)"
      pure none
    else
      pure (some (← aggregateCacheDir))

  let mut slots : Array AggregateSlot := #[]
  for (item, slotIdx) in plan.mapIdx fun slotIdx item => (item, slotIdx) do
    let some spec := specs[slotIdx]? | do
      IO.eprintln s!"internal: missing prepared aggregate slot {slotIdx}"
      return 1
    match item.op with
    | .leaf shard =>
      let originalShard := (view.shardIds[shard]?).getD shard
      let some wrapper := proofsByShard.get? shard | do
        IO.eprintln s!"internal: no proof for shard {originalShard}"
        return 1
      let some preparedShard := prepared[shard]? | do
        IO.eprintln s!"internal: no statement for shard {originalShard}"
        return 1
      let claimBytes := Ix.Claim.ser preparedShard.claim
      let verifyInput := IxVM.ClaimHarness.packedDigestKey
        (Address.blake3 claimBytes)
      let innerClaim := Aiur.buildClaim verifyIdx verifyInput #[]
      let innerProof := Aiur.Proof.ofBytes wrapper.proof
      match ixvmSystem.verify innerClaim innerProof with
      | .error e =>
        IO.eprintln s!"shard {originalShard} proof fails native verification: {e}"
        return 1
      | .ok () => pure ()
      let innerClaimsBytes := MultiStark.serializeClaims #[innerClaim]
      let cached? ← match cacheDir? with
        | none => pure none
        | some dir => loadCachedAggregateProof dir slotIdx spec recursionSystem
      let (proof, proofAddress?) ← match cached? with
        | some cached => pure (cached.proof, some cached.address)
        | none =>
          let pubInput := MultiStark.verifierPubInput ixvmVk innerClaimsBytes
          IO.println s!"[aggregate] lifting shard {originalShard} into slot {slotIdx}"
          (← IO.getStdout).flush
          let (outerClaim, proof) := recursionSystem.proveMultiStark liftIdx pubInput
            wrapper.proof ixvmVk innerClaimsBytes
          if outerClaim != spec.outerClaim then
            IO.eprintln s!"internal: lift slot {slotIdx} produced an unexpected outer claim"
            return 1
          let proofAddress? ← match cacheDir? with
            | none => pure none
            | some dir => persistAggregateCacheProof dir slotIdx spec proof
          pure (proof, proofAddress?)
      slots := slots.push {
        statement := spec.statement
        subjectCount := spec.subjectCount
        outerClaim := spec.outerClaim
        proof
        proofAddress?
        openPreimages := #[innerClaimsBytes, claimBytes]
      }
    | .join leftIdx rightIdx =>
      let some left := slots[leftIdx]? | do
        IO.eprintln s!"invalid aggregate plan: missing left slot {leftIdx}"
        return 1
      let some right := slots[rightIdx]? | do
        IO.eprintln s!"invalid aggregate plan: missing right slot {rightIdx}"
        return 1
      let output := spec.statement
      let outputClaimBytes := Ix.Claim.ser output.claim
      let cached? ← match cacheDir? with
        | none => pure none
        | some dir => loadCachedAggregateProof dir slotIdx spec recursionSystem
      let (proof, proofAddress?) ← match cached? with
        | some cached => pure (cached.proof, some cached.address)
        | none =>
          let pubInput := MultiStark.joinPubInput allowed outputClaimBytes
          let leftClaimsBytes := MultiStark.serializeClaims #[left.outerClaim]
          let rightClaimsBytes := MultiStark.serializeClaims #[right.outerClaim]
          let preimagesBlob := MultiStark.joinPreimagesBlob
            (left.openPreimages ++ right.openPreimages)
          let trees := if item.structural then
              MultiStark.CheckEnvTrees.structuralAdviceTrees
                left.statement right.statement output
            else
              MultiStark.CheckEnvTrees.adviceTrees
                left.statement right.statement output
          let treesBlob := MultiStark.joinTreesBlob trees
          let pathsBlob := if item.structural then
              MultiStark.joinPathsBlob
                (MultiStark.CheckEnvTrees.structuralPathAdvice
                  left.statement right.statement output)
            else
              MultiStark.joinPathsBlob #[]
          let joinFunIdx := if item.structural then structuralJoinIdx else joinIdx
          let mode := if item.structural then "structural" else "flat"
          IO.println s!"[aggregate] {mode}-joining slots {leftIdx}, {rightIdx} into {slotIdx}"
          (← IO.getStdout).flush
          let result := recursionSystem.proveMultiStarkJoin joinFunIdx pubInput
            left.proof.toBytes right.proof.toBytes recursionVk
            leftClaimsBytes rightClaimsBytes outputClaimBytes allowed
            preimagesBlob treesBlob pathsBlob
          let (outerClaim, proof) ← match result with
            | .error e => IO.eprintln s!"join slot {slotIdx}: {e}"; return 1
            | .ok result => pure result
          if outerClaim != spec.outerClaim then
            IO.eprintln s!"internal: join slot {slotIdx} produced an unexpected outer claim"
            return 1
          let proofAddress? ← match cacheDir? with
            | none => pure none
            | some dir => persistAggregateCacheProof dir slotIdx spec proof
          pure (proof, proofAddress?)
      slots := slots.push {
        statement := output
        subjectCount := spec.subjectCount
        outerClaim := spec.outerClaim
        proof
        proofAddress?
        openPreimages := #[outputClaimBytes]
      }

  let some root := slots.back? | do
    IO.eprintln "aggregate plan produced no root slot"
    return 1
  let some envTree := IxVM.ClaimHarness.envCanonicalTree env | do
    IO.eprintln "cannot aggregate an empty environment"
    return 1
  let some canonicalRoot := Ix.AssumptionTree.canonical root.statement.subjects.leaves | do
    IO.eprintln "aggregate root subject tree has no real leaves"
    return 1
  if canonicalRoot.root != envTree.root then
    IO.eprintln s!"aggregate root subjects canonicalize to {canonicalRoot.root}, not env root {envTree.root}"
    return 1
  if root.statement.assumptions.isSome then
    IO.eprintln s!"aggregate root retains undischarged assumptions {root.statement.assumptions.map (·.root)}"
    return 1
  match recursionSystem.verify root.outerClaim root.proof with
  | .error e => IO.eprintln s!"aggregate root proof failed native verification: {e}"; return 1
  | .ok () => pure ()

  let proofAddress ← match root.proofAddress? with
    | some address => pure address
    | none =>
      let claim := root.statement.claim
      let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
      let wrapper : Ixon.Proof := { claim, proof := root.proof.toBytes }
      StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
  IO.println s!"[aggregate] root proof: {proofAddress}"
  return 0

def runAggregateCmd (p : Cli.Parsed) : IO UInt32 :=
  runAggregateCmdWith MultiStark.defaultRecursionParameters p

end Ix.Cli.AggregateCmd

open Ix.Cli.AggregateCmd in
def aggregateCmd : Cli.Cmd := `[Cli|
  aggregate VIA runAggregateCmd;
  "Lift shard proofs and fold multi-shard manifests into one recursive aggregate"

  FLAGS:
    "ixe" : String;  "Path to the serialized environment whose shards were proven."
    "ixes" : String; "Path to the shard manifest; its bisection tree determines join order."
    "plan-only";     "Validate coverage and print the lift/join slot plan without loading or proving shard proofs."
    "no-cache";      "Bypass aggregate cache reads and intermediate cache writes; the root wrapper is still persisted."
    "structural-above" : Nat; "Use structural joins when a node contains more than N subject leaves (default 4096; 0 means every join)."

  ARGS:
    ...proofs : String; "Persisted shard-proof wrapper addresses, in any order (exactly one per nonempty shard unless --plan-only)."
]

end
