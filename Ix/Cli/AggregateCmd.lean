/-
  `ix aggregate --ixe E --ixes M <shard-proof>...`

  Bind persisted shard proof wrappers to every shard in a manifest, lift each
  IxVM proof into the Multi-STARK recursion system, then execute/prove binary
  joins in the manifest's bisection-tree order. The final persisted wrapper
  carries the aggregate `CheckEnv` claim and recursive proof bytes.

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
  outerClaim : Array Aiur.G
  proof : Aiur.Proof
  /-- Preimages needed when this slot is decoded by its parent. A lift exposes
  its inner claims plus `CheckEnv`; a join exposes only its output `CheckEnv`. -/
  openPreimages : Array ByteArray

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

private def printPlan (plan : Array Ix.Cli.CheckCmd.AggregationTree.FoldOp) : IO Unit := do
  let leaves := plan.countP fun op => match op with
    | .leaf _ => true
    | .join _ _ => false
  IO.println s!"[aggregate] plan: {leaves} lifts + {plan.size - leaves} binary joins"
  for (op, slot) in plan.mapIdx fun slot op => (op, slot) do
    match op with
    | .leaf shard => IO.println s!"  slot {slot}: lift shard {shard}"
    | .join left right => IO.println s!"  slot {slot}: join slots {left}, {right}"

def runAggregateCmd (p : Cli.Parsed) : IO UInt32 := do
  let some ixePath := (p.flag? "ixe").map (·.as! String) | do
    p.printError "error: aggregate requires --ixe <env.ixe>"
    return 1
  let some manifestPath := (p.flag? "ixes").map (·.as! String) | do
    p.printError "error: aggregate requires --ixes <manifest.ixes>"
    return 1

  let view ← match Ix.Cli.CheckCmd.parseIxesManifest
      (← IO.FS.readBinFile manifestPath) with
    | .error e => IO.eprintln s!"manifest parse failed: {e}"; return 1
    | .ok view => pure view
  let env ← match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
    | .error e => IO.eprintln s!"deserialize {ixePath} failed: {e}"; return 1
    | .ok env => pure env
  if !(← Ix.Cli.CheckCmd.shardsCover env view.shards) then return 1
  if view.shards.size < 2 then
    IO.eprintln "aggregate currently requires at least two shards (single-shard lift packaging is not yet exposed)"
    return 1
  if view.shards.any (·.isEmpty) then
    IO.eprintln "aggregate currently requires non-empty shards; regenerate or prune empty manifest leaves"
    return 1

  let plan := view.aggregationTree.foldPlan
  printPlan plan
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
    let item ← match prepareShard env blocks with
      | .error e => IO.eprintln s!"prepare shard {shard}: {e}"; return 1
      | .ok item => pure item
    let digest := Address.blake3 (Ix.Claim.ser item.claim)
    if digestToShard.contains digest then
      IO.eprintln s!"duplicate reconstructed shard claim digest {digest}"
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
    if wrapper.claim != expected.claim then
      IO.eprintln s!"proof {proofAddress} hit a claim-digest collision for shard {shard}"
      return 1
    if proofsByShard.contains shard then
      IO.eprintln s!"more than one proof supplied for shard {shard}"
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
  let ixvmSystem := Aiur.AiurSystem.build ixvmCompiled.bytecode
    Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  let recursionSystem := Aiur.AiurSystem.build recursionCompiled.bytecode
    Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  let ixvmVk := ixvmSystem.vkBytes
  let recursionVk := recursionSystem.vkBytes
  let allowed := MultiStark.allowedBlob ixvmVk verifyIdx recursionVk liftIdx joinIdx

  let mut slots : Array AggregateSlot := #[]
  for (op, slotIdx) in plan.mapIdx fun slotIdx op => (op, slotIdx) do
    match op with
    | .leaf shard =>
      let some wrapper := proofsByShard.get? shard | do
        IO.eprintln s!"internal: no proof for shard {shard}"
        return 1
      let some item := prepared[shard]? | do
        IO.eprintln s!"internal: no statement for shard {shard}"
        return 1
      let claimBytes := Ix.Claim.ser item.claim
      let verifyInput := IxVM.ClaimHarness.packedDigestKey
        (Address.blake3 claimBytes)
      let innerClaim := Aiur.buildClaim verifyIdx verifyInput #[]
      let innerProof := Aiur.Proof.ofBytes wrapper.proof
      match ixvmSystem.verify innerClaim innerProof with
      | .error e =>
        IO.eprintln s!"shard {shard} proof fails native verification: {e}"
        return 1
      | .ok () => pure ()
      let innerClaimsBytes := MultiStark.serializeClaims #[innerClaim]
      let pubInput := MultiStark.verifierPubInput ixvmVk innerClaimsBytes
      IO.println s!"[aggregate] lifting shard {shard} into slot {slotIdx}"
      (← IO.getStdout).flush
      let (outerClaim, proof) := recursionSystem.proveMultiStark liftIdx pubInput
        wrapper.proof ixvmVk innerClaimsBytes
      slots := slots.push {
        statement := item.statement
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
      let output := left.statement.join right.statement
      let outputClaimBytes := Ix.Claim.ser output.claim
      let pubInput := MultiStark.joinPubInput allowed outputClaimBytes
      let leftClaimsBytes := MultiStark.serializeClaims #[left.outerClaim]
      let rightClaimsBytes := MultiStark.serializeClaims #[right.outerClaim]
      let preimagesBlob := MultiStark.joinPreimagesBlob
        (left.openPreimages ++ right.openPreimages)
      let treesBlob := MultiStark.joinTreesBlob
        (MultiStark.CheckEnvTrees.adviceTrees left.statement right.statement output)
      IO.println s!"[aggregate] joining slots {leftIdx}, {rightIdx} into {slotIdx}"
      (← IO.getStdout).flush
      let result := recursionSystem.proveMultiStarkJoin joinIdx pubInput
        left.proof.toBytes right.proof.toBytes recursionVk
        leftClaimsBytes rightClaimsBytes outputClaimBytes allowed
        preimagesBlob treesBlob
      let (outerClaim, proof) ← match result with
        | .error e => IO.eprintln s!"join slot {slotIdx}: {e}"; return 1
        | .ok result => pure result
      slots := slots.push {
        statement := output
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
  if root.statement.subjects.root != envTree.root then
    IO.eprintln s!"aggregate root {root.statement.subjects.root} does not match env root {envTree.root}"
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

end Ix.Cli.AggregateCmd

open Ix.Cli.AggregateCmd in
def aggregateCmd : Cli.Cmd := `[Cli|
  aggregate VIA runAggregateCmd;
  "Lift shard proofs and fold them into one recursive aggregate along a `.ixes` bisection tree"

  FLAGS:
    "ixe" : String;  "Path to the serialized environment whose shards were proven."
    "ixes" : String; "Path to the shard manifest; its bisection tree determines join order."
    "plan-only";     "Validate coverage and print the lift/join slot plan without loading or proving shard proofs."

  ARGS:
    ...proofs : String; "Persisted shard-proof wrapper addresses, in any order (exactly one per shard unless --plan-only)."
]

end
