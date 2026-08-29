/-
  `ix aggr --ixe E --ixes M <shard-proof>...`

  Fold persisted IxVM shard proofs into one recursive `ix_aggr` proof of the
  whole environment. There is no lift stage: shard proofs enter the recursion
  system directly as `ix_aggr` join children, and the tree is a balanced
  bisection over the manifest's nonempty shards. Because the statement fold is
  canonical (sorted-set union/difference), the root claim is independent of
  the fold order; a single-shard environment is closed with one wrap so the
  persisted root is always an `ix_aggr` proof.

  This first host driver is intentionally serial and cache-free. Its slot
  model and content-addressed inputs make parallel scheduling and resumable
  cache entries follow-up optimizations rather than protocol changes.
-/
module
public import Cli
public import Ix.Aggr
public import Ix.Cli.CheckCmd
public import Ix.IxVM
public import Ix.IxVM.ClaimHarness
public import Ix.Store

public section

namespace Ix.Cli.AggrCmd

structure PreparedShard where
  claim : Ix.Claim
  statement : Aggr.CheckEnvTrees

/-- One aggregation slot: either a raw shard proof (`kind = .ixvm`, the
IxVM `verify_claim` wrapper) or an `ix_aggr` output (`kind = .aggr`). Proofs
stay compact as `Aiur.Proof` values between folds and are expanded only at a
recursive advice boundary. `claimsBytes` are the serialized claims a parent
feeds to IO channel 2. -/
structure Slot where
  kind : Aggr.ChildKind
  statement : Aggr.CheckEnvTrees
  outerClaim : Array Aiur.G
  proof : Aiur.Proof
  claimsBytes : ByteArray

/-- Everything a fold step needs, resolved once before proving. -/
structure Backend where
  ixvmSystem : Aiur.AiurSystem
  aggrSystem : Aiur.AiurSystem
  aggrIdx : Aiur.Bytecode.FunIdx
  ixvmVk : ByteArray
  aggrVk : ByteArray
  allowed : ByteArray

private def addrOfHex (label value : String) : Except String Address :=
  match Address.fromString value with
  | some address => .ok address
  | none => .error
    s!"{label}: expected a 64-character address, got {value.length} characters"

private def prepareShard (env : Ixon.Env) (blocks : Array Address) :
    Except String PreparedShard := do
  let owned := Ix.Cli.CheckCmd.ownedConstsForBlocks env blocks
  let (claim, trees) ← IxVM.ClaimHarness.shardCheckEnvClaimTrees env owned
  let statement ← Aggr.CheckEnvTrees.ofClaim claim trees
  pure { claim, statement }

private def compileToplevel (label : String)
    (source : Except Aiur.Global Aiur.Source.Toplevel) :
    Except String Aiur.CompiledToplevel := do
  match source with
  | .error e => throw s!"{label} toplevel merge failed: {e}"
  | .ok top => match top.compile with
    | .error e => throw s!"{label} compilation failed: {e}"
    | .ok compiled => pure compiled

/-- The serialized `verify_claim` claims of one shard wrapper — what the
IxVM prover's Fiat-Shamir transcript observed, and what a parent decodes. -/
private def shardClaimsBytes (verifyIdx : Aiur.Bytecode.FunIdx)
    (claim : Ix.Claim) : ByteArray :=
  let digestKey := IxVM.ClaimHarness.packedDigestKey
    (Address.blake3 (Ix.Claim.ser claim))
  MultiStark.serializeClaims #[Aiur.buildClaim verifyIdx digestKey #[]]

private def kindLabel : Aggr.ChildKind → String
  | .ixvm => "shard"
  | .aggr => "fold"

/-- Expand one compact child proof into the per-query transport consumed by
the recursive verifier. The child kind selects the verifying system whose
wire codec must be used. -/
private def proofAdviceBytes (backend : Backend) (slot : Slot) :
    Except String ByteArray :=
  let system := match slot.kind with
    | .ixvm => backend.ixvmSystem
    | .aggr => backend.aggrSystem
  system.proofToAdviceBytes slot.outerClaim slot.proof

/-- Prove one pair fold and natively verify its output. -/
private def proveJoin (backend : Backend) (left right : Slot) :
    IO (Except String Slot) := do
  let output := left.statement.join right.statement
  let outputClaimBytes := Ix.Claim.ser output.claim
  let shape := Aggr.shapeCode (left.kind, some right.kind)
  let pubInput := Aggr.pubInput backend.allowed outputClaimBytes
  let preimages := Aggr.preimagesBlob
    #[Ix.Claim.ser left.statement.claim, Ix.Claim.ser right.statement.claim]
  let trees := Aggr.treesBlob
    (Aggr.CheckEnvTrees.adviceTrees left.statement right.statement output)
  IO.println s!"[aggr] folding {kindLabel left.kind} + {kindLabel right.kind} \
    ({output.subjectCount} subjects)"
  (← IO.getStdout).flush
  let leftProofAdvice ← match proofAdviceBytes backend left with
    | .error e => return .error s!"left {kindLabel left.kind} proof advice encoding failed: {e}"
    | .ok bytes => pure bytes
  let rightProofAdvice ← match proofAdviceBytes backend right with
    | .error e => return .error s!"right {kindLabel right.kind} proof advice encoding failed: {e}"
    | .ok bytes => pure bytes
  let result := backend.aggrSystem.proveIxAggr backend.aggrIdx pubInput shape
    leftProofAdvice rightProofAdvice backend.ixvmVk backend.aggrVk
    left.claimsBytes right.claimsBytes outputClaimBytes backend.allowed
    preimages trees
  let (outerClaim, proof) ← match result with
    | .error e => return .error s!"fold proving failed: {e}"
    | .ok result => pure result
  match backend.aggrSystem.verify outerClaim proof with
  | .error e => return .error s!"fold output failed native verification: {e}"
  | .ok () => pure ()
  return .ok {
    kind := .aggr
    statement := output
    outerClaim
    proof
    claimsBytes := MultiStark.serializeClaims #[outerClaim]
  }

/-- Prove one wrap of an IxVM shard slot (single-shard environments), so the
persisted root is always an `ix_aggr` proof. -/
private def proveWrap (backend : Backend) (child : Slot) :
    IO (Except String Slot) := do
  let outputClaimBytes := Ix.Claim.ser child.statement.claim
  let shape := Aggr.shapeCode (child.kind, none)
  let pubInput := Aggr.pubInput backend.allowed outputClaimBytes
  IO.println s!"[aggr] wrapping single {kindLabel child.kind}"
  (← IO.getStdout).flush
  let childProofAdvice ← match proofAdviceBytes backend child with
    | .error e => return .error s!"{kindLabel child.kind} proof advice encoding failed: {e}"
    | .ok bytes => pure bytes
  let result := backend.aggrSystem.proveIxAggr backend.aggrIdx pubInput shape
    childProofAdvice ByteArray.empty backend.ixvmVk backend.aggrVk
    child.claimsBytes ByteArray.empty outputClaimBytes backend.allowed
    (Aggr.preimagesBlob #[]) (Aggr.treesBlob #[])
  let (outerClaim, proof) ← match result with
    | .error e => return .error s!"wrap proving failed: {e}"
    | .ok result => pure result
  match backend.aggrSystem.verify outerClaim proof with
  | .error e => return .error s!"wrap output failed native verification: {e}"
  | .ok () => pure ()
  return .ok {
    kind := .aggr
    statement := child.statement
    outerClaim
    proof
    claimsBytes := MultiStark.serializeClaims #[outerClaim]
  }

/-- Balanced bisection fold over `slots[lo:hi]`. Canonical set folds make the
root claim independent of this shape; balance minimizes depth. -/
private partial def foldRange (backend : Backend) (slots : Array Slot)
    (lo hi : Nat) : IO (Except String Slot) := do
  if hi - lo == 1 then
    let some slot := slots[lo]?
      | return .error s!"internal: fold range references missing slot {lo}"
    return .ok slot
  let mid := lo + (hi - lo) / 2
  let left ← match ← foldRange backend slots lo mid with
    | .error e => return .error e
    | .ok slot => pure slot
  let right ← match ← foldRange backend slots mid hi with
    | .error e => return .error e
    | .ok slot => pure slot
  proveJoin backend left right

def runAggrCmd (p : Cli.Parsed) : IO UInt32 := do
  let some ixePath := (p.flag? "ixe").map (·.as! String) | do
    p.printError "error: aggr requires --ixe <env.ixe>"
    return 1
  let some manifestPath := (p.flag? "ixes").map (·.as! String) | do
    p.printError "error: aggr requires --ixes <manifest.ixes>"
    return 1

  let env ← match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
    | .error e => IO.eprintln s!"deserialize {ixePath} failed: {e}"; return 1
    | .ok env => pure env
  let allShards ← match Ix.Cli.CheckCmd.parseIxesAllShards
      (← IO.FS.readBinFile manifestPath) with
    | .error e => IO.eprintln s!"manifest parse failed: {e}"; return 1
    | .ok shards => pure shards
  if !(← Ix.Cli.CheckCmd.shardsCover env allShards) then return 1

  -- Reconstruct every nonempty shard's statement from the environment once.
  -- This binds proof wrappers to shards and supplies canonical fold advice.
  let mut prepared : Array (Nat × PreparedShard) := #[]
  let mut digestToSlot : Std.HashMap Address Nat := {}
  for (blocks, shard) in allShards.mapIdx fun shard blocks => (blocks, shard) do
    if (Ix.Cli.CheckCmd.ownedConstsForBlocks env blocks).isEmpty then
      IO.println s!"[aggr] skipping zero-constant manifest shard {shard}"
      continue
    let item ← match prepareShard env blocks with
      | .error e => IO.eprintln s!"prepare shard {shard}: {e}"; return 1
      | .ok item => pure item
    let digest := Address.blake3 (Ix.Claim.ser item.claim)
    if digestToSlot.contains digest then
      IO.eprintln s!"duplicate reconstructed shard claim digest {digest} \
        (manifest shard {shard})"
      return 1
    digestToSlot := digestToSlot.insert digest prepared.size
    prepared := prepared.push (shard, item)
  if prepared.isEmpty then
    IO.eprintln "manifest contains no nonempty shard"
    return 1

  let depth := Nat.log2 (2 * prepared.size - 1)
  let wrapNote := if prepared.size == 1 then " + 1 wrap" else ""
  IO.println s!"[aggr] plan: {prepared.size} shard leaves, \
    {prepared.size - 1} pair folds{wrapNote} (balanced bisection, depth {depth})"
  if p.hasFlag "plan-only" then return 0

  let proofHexes := (p.variableArgsAs! String).toList
  if proofHexes.length != prepared.size then
    IO.eprintln s!"aggr requires exactly {prepared.size} shard proofs; \
      got {proofHexes.length}"
    return 1

  -- Proof arguments may be in any order. Match them by their bundled claim
  -- and reject duplicates/collisions before starting expensive proving.
  let mut proofsBySlot : Std.HashMap Nat Ixon.Proof := {}
  for proofHex in proofHexes do
    let proofAddress ← match addrOfHex "shard proof" proofHex with
      | .error e => IO.eprintln e; return 1
      | .ok address => pure address
    let wrapper ← match Ixon.Proof.de (← StoreIO.toIO (Store.read proofAddress)) with
      | .error e => IO.eprintln s!"decode shard proof {proofAddress}: {e}"; return 1
      | .ok wrapper => pure wrapper
    let digest := Address.blake3 (Ix.Claim.ser wrapper.claim)
    let some slot := digestToSlot.get? digest | do
      IO.eprintln s!"proof {proofAddress} claim {digest} matches no manifest shard"
      return 1
    let some (shard, expected) := prepared[slot]? | do
      IO.eprintln s!"internal: missing prepared slot {slot}"
      return 1
    if wrapper.claim != expected.claim then
      IO.eprintln s!"proof {proofAddress} hit a claim-digest collision for shard {shard}"
      return 1
    if proofsBySlot.contains slot then
      IO.eprintln s!"more than one proof supplied for shard {shard}"
      return 1
    proofsBySlot := proofsBySlot.insert slot wrapper
  if proofsBySlot.size != prepared.size then
    IO.eprintln "not every nonempty manifest shard has a supplied proof"
    return 1

  let ixvmCompiled ← match compileToplevel "IxVM" IxVM.ixVM with
    | .error e => IO.eprintln e; return 1
    | .ok compiled => pure compiled
  let aggrCompiled ← match compileToplevel "ixAggr" Aggr.ixAggr with
    | .error e => IO.eprintln e; return 1
    | .ok compiled => pure compiled
  let verifyIdx := ixvmCompiled.getFuncIdx `verify_claim |>.get!
  let aggrIdx := aggrCompiled.getFuncIdx `ix_aggr |>.get!
  let ixvmSystem := Aiur.AiurSystem.build ixvmCompiled.bytecode
    Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  let aggrSystem := Aiur.AiurSystem.build aggrCompiled.bytecode
    Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  let ixvmVk := ixvmSystem.vkBytes
  let aggrVk := aggrSystem.vkBytes
  let backend : Backend := {
    ixvmSystem, aggrSystem, aggrIdx, ixvmVk, aggrVk
    allowed := Aggr.allowedBlob ixvmVk verifyIdx aggrVk aggrIdx
  }

  -- Natively pre-verify every shard proof before any expensive fold, and
  -- decode proof bytes through the checked constructor: wrappers come from
  -- the store, an untrusted boundary.
  let mut slots : Array Slot := #[]
  for (item, slot) in prepared.mapIdx fun slot item => (item, slot) do
    let (shard, preparedShard) := item
    let some wrapper := proofsBySlot.get? slot | do
      IO.eprintln s!"internal: no proof for shard {shard}"
      return 1
    let proof ← match Aiur.Proof.ofBytesChecked wrapper.proof with
      | .error e => IO.eprintln s!"shard {shard} proof decode failed: {e}"; return 1
      | .ok proof => pure proof
    let digestKey := IxVM.ClaimHarness.packedDigestKey
      (Address.blake3 (Ix.Claim.ser preparedShard.claim))
    let innerClaim := Aiur.buildClaim verifyIdx digestKey #[]
    match ixvmSystem.verify innerClaim proof with
    | .error e =>
      IO.eprintln s!"shard {shard} proof fails native verification: {e}"
      return 1
    | .ok () => pure ()
    slots := slots.push {
      kind := .ixvm
      statement := preparedShard.statement
      outerClaim := innerClaim
      proof
      claimsBytes := shardClaimsBytes verifyIdx preparedShard.claim
    }

  let folded ← match ← foldRange backend slots 0 slots.size with
    | .error e => IO.eprintln e; return 1
    | .ok slot => pure slot
  -- A single-shard environment still gets an `ix_aggr` root via one wrap.
  let root ← match folded.kind with
    | .aggr => pure folded
    | .ixvm => match ← proveWrap backend folded with
      | .error e => IO.eprintln e; return 1
      | .ok slot => pure slot

  let some envTree := IxVM.ClaimHarness.envCanonicalTree env | do
    IO.eprintln "cannot aggregate an empty environment"
    return 1
  if root.statement.subjects.root != envTree.root then
    IO.eprintln s!"aggregate root subjects are {root.statement.subjects.root}, \
      not env root {envTree.root}"
    return 1
  if root.statement.assumptions.isSome then
    IO.eprintln s!"aggregate root retains undischarged assumptions \
      {root.statement.assumptions.map (·.root)}"
    return 1

  let claim := root.statement.claim
  let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
  let wrapper : Ixon.Proof := { claim, proof := root.proof.toBytes }
  let proofAddress ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
  IO.println s!"[aggr] root proof: {proofAddress}"
  return 0

end Ix.Cli.AggrCmd

open Ix.Cli.AggrCmd in
def aggrCmd : Cli.Cmd := `[Cli|
  aggr VIA runAggrCmd;
  "Fold IxVM shard proofs into one recursive ix_aggr proof of the whole environment"

  FLAGS:
    "ixe" : String;  "Path to the serialized environment whose shards were proven."
    "ixes" : String; "Path to the shard manifest defining the shard partition."
    "plan-only";     "Validate coverage and print the fold plan without loading or proving shard proofs."

  ARGS:
    ...proofs : String; "Persisted shard-proof wrapper addresses, in any order (exactly one per nonempty shard unless --plan-only)."
]

end
