/-
  `ix aggregate --ixe E --ixes M <shard-proof>...`

  Bind persisted shard proof wrappers to every nonempty shard in a manifest,
  lift each IxVM proof into the Multi-STARK recursion system, then execute/prove
  any binary joins in the manifest's bisection-tree order. Small joins use flat
  canonical subjects; joins above `--structural-above` use an O(1)
  root-of-roots subject fold plus assumption-membership paths. The final
  persisted wrapper carries the aggregate `CheckEnv` claim and recursive proof
  bytes.

  This first host driver is intentionally serial and cache-free. Its slot
  model and content-addressed inputs make parallel scheduling and resumable
  cache entries follow-up optimizations rather than protocol changes.
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
  /-- Preimages needed when this slot is decoded by its parent. A lift exposes
  its inner claims plus `CheckEnv`; a join exposes only its output `CheckEnv`. -/
  openPreimages : Array ByteArray

/-- A manifest fold operation annotated with the cumulative subject count and
the monotone flat/structural choice used by the prover. -/
structure ScheduledFold where
  op : Ix.Cli.CheckCmd.AggregationTree.FoldOp
  subjectCount : Nat
  structural : Bool
  deriving BEq, Repr

def defaultStructuralAbove : Nat := 4096

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

private def addrOfHex (label value : String) : Except String Address :=
  match Address.fromString value with
  | some address => .ok address
  | none => .error
    s!"{label}: expected a 64-character address, got {value.length} characters"

private def prepareShard (env : Ixon.Env) (blocks : Array Address) :
    Except String PreparedShard := do
  let owned := Ix.Cli.CheckCmd.ownedConstsForBlocks env blocks
  let (claim, _, trees) ← IxVM.ClaimHarness.shardCheckEnvClaim env owned
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

  let mut slots : Array AggregateSlot := #[]
  for (item, slotIdx) in plan.mapIdx fun slotIdx item => (item, slotIdx) do
    match item.op with
    | .leaf shard =>
      let originalShard := (view.shardIds[shard]?).getD shard
      let some wrapper := proofsByShard.get? shard | do
        IO.eprintln s!"internal: no proof for shard {originalShard}"
        return 1
      let some preparedShard := prepared[shard]? | do
        IO.eprintln s!"internal: no statement for shard {originalShard}"
        return 1
      if preparedShard.statement.subjectCount != item.subjectCount then
        IO.eprintln s!"internal: shard {originalShard} has {preparedShard.statement.subjectCount} \
          reconstructed subjects, but the schedule records {item.subjectCount}"
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
      let pubInput := MultiStark.verifierPubInput ixvmVk innerClaimsBytes
      IO.println s!"[aggregate] lifting shard {originalShard} into slot {slotIdx}"
      (← IO.getStdout).flush
      let (outerClaim, proof) := recursionSystem.proveMultiStark liftIdx pubInput
        wrapper.proof ixvmVk innerClaimsBytes
      slots := slots.push {
        statement := preparedShard.statement
        subjectCount := item.subjectCount
        outerClaim
        proof
        openPreimages := #[innerClaimsBytes, claimBytes]
      }
    | .join leftIdx rightIdx =>
      let some left := slots[leftIdx]? | do
        IO.eprintln s!"invalid aggregate plan: missing left slot {leftIdx}"
        return 1
      let some right := slots[rightIdx]? | do
        IO.eprintln s!"invalid aggregate plan: missing right slot {rightIdx}"
        return 1
      if left.subjectCount + right.subjectCount != item.subjectCount then
        IO.eprintln s!"internal: join slot {slotIdx} has inconsistent scheduled subject counts"
        return 1
      let output := if item.structural then
          left.statement.joinStructural right.statement
        else
          left.statement.join right.statement
      if output.subjectCount != item.subjectCount then
        IO.eprintln s!"internal: join slot {slotIdx} reconstructed {output.subjectCount} \
          subjects, but the schedule records {item.subjectCount}"
        return 1
      let outputClaimBytes := Ix.Claim.ser output.claim
      let pubInput := MultiStark.joinPubInput allowed outputClaimBytes
      let leftClaimsBytes := MultiStark.serializeClaims #[left.outerClaim]
      let rightClaimsBytes := MultiStark.serializeClaims #[right.outerClaim]
      let preimagesBlob := MultiStark.joinPreimagesBlob
        (left.openPreimages ++ right.openPreimages)
      let trees := if item.structural then
          MultiStark.CheckEnvTrees.structuralAdviceTrees
            left.statement right.statement output
        else
          MultiStark.CheckEnvTrees.adviceTrees left.statement right.statement output
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
      slots := slots.push {
        statement := output
        subjectCount := item.subjectCount
        outerClaim
        proof
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

  let claim := root.statement.claim
  let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
  let wrapper : Ixon.Proof := { claim, proof := root.proof.toBytes }
  let proofAddress ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
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
    "structural-above" : Nat; "Use structural joins when a node contains more than N subject leaves (default 4096; 0 means every join)."

  ARGS:
    ...proofs : String; "Persisted shard-proof wrapper addresses, in any order (exactly one per nonempty shard unless --plan-only)."
]

end
