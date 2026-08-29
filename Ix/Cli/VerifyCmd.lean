/-
  `ix verify <proof-hex>`: read a persisted `Ixon.Proof` wrapper from
  the content-addressed store, extract the inner claim + opaque ZK
  proof bytes, reconstruct the Aiur-level public input, and run the
  Aiur backend's `verify`. Exits 0 on success, 1 with an error
  message otherwise.

  The wrapper carries the claim, so this command takes only the proof
  hex — no separate claim arg.
-/
module
public import Cli
public import Ix.Address
public import Ix.Aiur.Compiler
public import Ix.Aiur.Protocol
public import Ix.Claim
public import Ix.Common
public import Ix.IxVM
public import Ix.IxVM.Toplevel
public import Ix.IxVM.ClaimHarness
public import Ix.MultiStark
public import Ix.Store
public import Ix.Cli.AggregateCmd
public import Ix.Cli.CheckCmd

public section

open System (FilePath)

namespace Ix.Cli.VerifyCmd

private def addrOfHex! (label : String) (s : String) : IO Address := do
  match Address.fromString s with
  | some a => pure a
  | none =>
    throw <| IO.userError
      s!"error: {label}: expected 64-char hex (32-byte address), got {s.length}-char {s}"

/-- Same parameters as `ix prove` (the shared canonical defaults).
    Mismatch makes verification fail silently with no useful diagnostic,
    so these MUST match the proving side until they migrate into the
    proof header. -/
private def commitmentParameters : Aiur.CommitmentParameters :=
  Aiur.defaultCommitmentParameters

private def friParameters : Aiur.FriParameters :=
  Aiur.defaultFriParameters

/-- Verify one persisted `Ixon.Proof` wrapper (by store address) against its
    bundled claim, using an already-built Aiur backend. -/
def verifyOneProof (aiurSystem : Aiur.AiurSystem) (compiled : Aiur.CompiledToplevel)
    (proofAddr : Address) : IO UInt32 := do
  let bytes ← StoreIO.toIO (Store.read proofAddr)
  let wrapper ← IO.ofExcept (Ixon.Proof.de bytes)
  let proof ← match Aiur.Proof.ofBytesChecked wrapper.proof with
    | .ok proof => pure proof
    | .error e =>
      IO.eprintln s!"error: proof {proofAddr} does not decode: {e}"
      return 1
  -- `verify_claim` takes the packed 8-G blake3 digest of the serialized
  -- claim (4 LE bytes per element; see `ClaimHarness.packedDigestKey`).
  let claimDigest := Address.blake3 (Ix.Claim.ser wrapper.claim)
  let funIdx ← match compiled.getFuncIdx `verify_claim with
    | some i => pure i
    | none =>
      IO.eprintln "error: `verify_claim` entrypoint missing from compiled toplevel"
      return 1
  let input : Array Aiur.G := IxVM.ClaimHarness.packedDigestKey claimDigest
  let aiurClaim := Aiur.buildClaim funIdx input #[]
  match aiurSystem.verify aiurClaim proof with
  | .ok () =>
    IO.println s!"ok: proof {proofAddr} verifies claim {claimDigest}"
    return 0
  | .error e =>
    IO.eprintln s!"error: verification failed: {e}"
    return 1

/-- Build the Aiur backend (toplevel → compile → system), matching the proving
    side. Shared by every proof-verifying path. -/
def buildBackend : IO (Except String (Aiur.AiurSystem × Aiur.CompiledToplevel)) := do
  match IxVM.ixVM with
  | .error e => return .error s!"toplevel merging failed: {e}"
  | .ok toplevel => match toplevel.compile with
    | .error e => return .error s!"compilation failed: {e}"
    | .ok compiled =>
      return .ok (Aiur.AiurSystem.build compiled.bytecode commitmentParameters friParameters, compiled)

structure AggregateBackend where
  system : Aiur.AiurSystem
  ixvmVk : ByteArray
  verifyClaimIdx : Aiur.Bytecode.FunIdx
  liftIdx : Aiur.Bytecode.FunIdx
  flatJoinIdx : Aiur.Bytecode.FunIdx
  structuralJoinIdx : Aiur.Bytecode.FunIdx
  allowed : ByteArray

inductive AggregateRootKind where
  | lift
  | flat
  | structural
  deriving BEq, Repr

structure ExpectedAggregate where
  claim : Ix.Claim
  kinds : Array AggregateRootKind

/-- Build the two deterministic systems whose identities are committed by an
aggregate root: the IxVM vk and the combined lift/join recursion vk. -/
private def buildAggregateBackend
    (recursionParameters : MultiStark.RecursionParameters) :
    IO (Except String AggregateBackend) := do
  let ixvmCompiled ← match IxVM.ixVM with
    | .error e => return .error s!"IxVM toplevel merging failed: {e}"
    | .ok top => match top.compile with
      | .error e => return .error s!"IxVM compilation failed: {e}"
      | .ok compiled => pure compiled
  let recursionCompiled ← match MultiStark.multiStark with
    | .error e => return .error s!"recursion toplevel merging failed: {e}"
    | .ok top => match top.compile with
      | .error e => return .error s!"recursion compilation failed: {e}"
      | .ok compiled => pure compiled
  let verifyIdx := ixvmCompiled.getFuncIdx `verify_claim |>.get!
  let liftIdx := recursionCompiled.getFuncIdx `verify_multi_stark_proof |>.get!
  let joinIdx := recursionCompiled.getFuncIdx `join_two |>.get!
  let structuralJoinIdx := recursionCompiled.getFuncIdx `join_two_structural |>.get!
  let ixvmSystem := Aiur.AiurSystem.build ixvmCompiled.bytecode
    commitmentParameters friParameters
  let recursionSystem := MultiStark.buildRecursionSystem recursionCompiled.bytecode
    recursionParameters
  let ixvmVk := ixvmSystem.vkBytes
  let recursionVk := recursionSystem.vkBytes
  let allowed := MultiStark.allowedBlob ixvmVk verifyIdx
    recursionVk liftIdx joinIdx structuralJoinIdx
  return .ok {
    system := recursionSystem
    ixvmVk
    verifyClaimIdx := verifyIdx
    liftIdx
    flatJoinIdx := joinIdx
    structuralJoinIdx
    allowed
  }

private def shardStatement (env : Ixon.Env) (blocks : Array Address) :
    Except String MultiStark.CheckEnvTrees := do
  let owned := Ix.Cli.CheckCmd.ownedConstsForBlocks env blocks
  let (claim, trees) ← IxVM.ClaimHarness.shardCheckEnvClaimTrees env owned
  MultiStark.CheckEnvTrees.ofClaim claim trees

/-- Reproduce the lift/flat/structural statement fold from a coverage-validated
manifest. Zero-constant leaves are pruned exactly as in `ix aggregate`; no proof
data is needed. -/
def expectedFromManifest (env : Ixon.Env)
    (view : Ix.Cli.CheckCmd.IxesManifestView) (structuralAbove : Nat) :
    Except String (MultiStark.CheckEnvTrees × AggregateRootKind) := do
  let (view, counts) ← view.pruneEmpty env
  let plan ← Ix.Cli.AggregateCmd.schedulePlan view.aggregationTree.foldPlan
    counts structuralAbove
  let mut slots : Array MultiStark.CheckEnvTrees := #[]
  for item in plan do
    match item.op with
    | .leaf shard =>
      let some blocks := view.shards[shard]?
        | throw s!"aggregate plan references missing shard {shard}"
      slots := slots.push (← shardStatement env blocks)
    | .join left right =>
      let some leftStatement := slots[left]?
        | throw s!"aggregate plan references missing left slot {left}"
      let some rightStatement := slots[right]?
        | throw s!"aggregate plan references missing right slot {right}"
      slots := slots.push <| if item.structural then
        leftStatement.joinStructural rightStatement
      else
        leftStatement.join rightStatement
  let some root := slots.back? | throw "aggregate manifest produced no root"
  let some rootPlan := plan.back? | throw "aggregate manifest produced no root slot"
  let kind := match rootPlan.op with
    | .leaf _ => AggregateRootKind.lift
    | .join _ _ => if rootPlan.structural then .structural else .flat
  pure (root, kind)

/-- Reconstruct the exact outer claim of a single-shard lift from the bundled
`CheckEnv` statement. This is the verification-side inverse of the leaf arm in
`ix aggregate`: the wrapper claim determines the nested IxVM `verify_claim`,
whose serialized singleton list determines the lift public input. -/
def aggregateLiftOuterClaim (ixvmVk : ByteArray)
    (verifyClaimIdx liftIdx : Aiur.Bytecode.FunIdx) (claim : Ix.Claim) : Array Aiur.G :=
  let claimBytes := Ix.Claim.ser claim
  let verifyInput := IxVM.ClaimHarness.packedDigestKey (Address.blake3 claimBytes)
  let innerClaim := Aiur.buildClaim verifyClaimIdx verifyInput #[]
  let innerClaimsBytes := MultiStark.serializeClaims #[innerClaim]
  Aiur.buildClaim liftIdx (MultiStark.verifierPubInput ixvmVk innerClaimsBytes) #[]

private def aggregateRootKindLabel : AggregateRootKind → String
  | .lift => "lift"
  | .flat => "flat"
  | .structural => "structural"

private def verifyAggregateProof (backend : AggregateBackend)
    (expected? : Option ExpectedAggregate) (proofAddr : Address) : IO UInt32 := do
  let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read proofAddr)))
  let .checkEnv _ _ := wrapper.claim | do
    IO.eprintln s!"error: aggregate proof {proofAddr} does not bundle a CheckEnv claim"
    return 1
  match expected? with
  | some expected =>
    if wrapper.claim != expected.claim then
      IO.eprintln s!"error: aggregate claim {wrapper.claim} does not match expected {expected.claim}"
      return 1
  | none => pure ()
  let proof ← match Aiur.Proof.ofBytesChecked wrapper.proof with
    | .ok proof => pure proof
    | .error e =>
      IO.eprintln s!"error: aggregate proof {proofAddr} does not decode: {e}"
      return 1
  let claimBytes := Ix.Claim.ser wrapper.claim
  let joinPubInput := MultiStark.joinPubInput backend.allowed claimBytes
  let outerClaim : AggregateRootKind → Array Aiur.G
    | .lift => aggregateLiftOuterClaim backend.ixvmVk backend.verifyClaimIdx
        backend.liftIdx wrapper.claim
    | .flat => Aiur.buildClaim backend.flatJoinIdx joinPubInput #[]
    | .structural => Aiur.buildClaim backend.structuralJoinIdx joinPubInput #[]
  let kinds := expected?.map (·.kinds) |>.getD
    #[.lift, .flat, .structural]
  let mut errors : Array String := #[]
  for kind in kinds do
    match backend.system.verify (outerClaim kind) proof with
    | .ok () =>
      IO.println s!"ok: {aggregateRootKindLabel kind} aggregate proof \
        {proofAddr} verifies {wrapper.claim}"
      return 0
    | .error e =>
      errors := errors.push s!"{aggregateRootKindLabel kind}: {e}"
  IO.eprintln s!"error: aggregate verification failed: \
    {String.intercalate "; " errors.toList}"
  return 1

/-- Shard-aware verification (parity with `check`/`prove`):
    - `--shard K`, no proof: print shard K's reconstructed `CheckEnv` claim
      digest (the public input its proof must commit).
    - `--shard K` + proof(s): verify each proof AND bind it to shard K (its
      bundled claim must equal shard K's reconstructed claim).
    - no `--shard`, no proof: off-circuit coverage verdict (disjoint cover).
    - no `--shard` + proofs: composed verdict — coverage, every proof bound to a
      shard, and every shard covered by a valid proof. -/
def verifyShardComposition (ixePath manifestPath : String) (shardK? : Option Nat)
    (proofs : List String) : IO UInt32 := do
  let (ixonEnv, shards) ← match (← Ix.Cli.CheckCmd.loadEnvAndShards manifestPath ixePath) with
    | .error e => IO.eprintln e; return 1
    | .ok r => pure r
  let digestOf (k : Nat) : IO (Option Address) := do
    match shards[k]? with
    | none => IO.eprintln s!"shard {k} out of range ({shards.size} shards)"; pure none
    | some blocks => match Ix.Cli.CheckCmd.shardClaimDigest ixonEnv blocks with
      | .error e => IO.eprintln s!"reconstruct shard {k} claim failed: {e}"; pure none
      | .ok d => pure (some d)
  let claimDigestOfProof (hex : String) : IO (Address × Address) := do
    let proofAddr ← addrOfHex! "proof" hex
    let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read proofAddr)))
    pure (proofAddr, Address.blake3 (Ix.Claim.ser wrapper.claim))
  match shardK? with
  | some k =>
    let some expected ← digestOf k | return 1
    if proofs.isEmpty then
      IO.println s!"shard {k} CheckEnv claim digest: {expected}"
      return 0
    let (aiurSystem, compiled) ← match (← buildBackend) with
      | .error e => IO.eprintln e; return 1
      | .ok b => pure b
    let mut rc : UInt32 := 0
    for hex in proofs do
      let (proofAddr, d) ← claimDigestOfProof hex
      if d != expected then
        IO.eprintln s!"[verify] FAIL: proof {proofAddr} (claim {d}) is not shard {k} (claim {expected})"
        rc := 1
      else if (← verifyOneProof aiurSystem compiled proofAddr) != 0 then rc := 1
    return rc
  | none =>
    if !(← Ix.Cli.CheckCmd.shardsCover ixonEnv shards) then return 1
    if proofs.isEmpty then return 0
    let mut digestToShard : Std.HashMap Address Nat := {}
    for k in [0:shards.size] do
      let some d ← digestOf k | return 1
      digestToShard := digestToShard.insert d k
    let (aiurSystem, compiled) ← match (← buildBackend) with
      | .error e => IO.eprintln e; return 1
      | .ok b => pure b
    let mut covered : Std.HashSet Nat := {}
    let mut rc : UInt32 := 0
    for hex in proofs do
      let (proofAddr, d) ← claimDigestOfProof hex
      match digestToShard.get? d with
      | none => IO.eprintln s!"[verify] FAIL: proof {proofAddr} (claim {d}) matches no shard"; rc := 1
      | some k =>
        if (← verifyOneProof aiurSystem compiled proofAddr) != 0 then rc := 1
        else covered := covered.insert k
    let missing := (List.range shards.size).filter (fun k => !covered.contains k)
    if !missing.isEmpty then
      IO.eprintln s!"[verify] FAIL: shards lacking a valid proof: {missing}"
      rc := 1
    if rc == 0 then
      IO.println s!"[verify] OK: composed verdict — all {shards.size} shards proven + disjoint cover"
    return rc

/-- Verify with an explicit aggregate-recursion configuration. Ordinary IxVM
proof verification remains pinned to its independent canonical parameters. -/
def runVerifyCmdWith (recursionParameters : MultiStark.RecursionParameters)
    (p : Cli.Parsed) : IO UInt32 := do
  let proofs := (p.variableArgsAs! String).toList
  if p.hasFlag "aggregate" then
    if proofs.isEmpty then
      p.printError "error: --aggregate requires at least one aggregate proof address"
      return 1
    let ixePath? := (p.flag? "ixe").map (·.as! String)
    let manifestPath? := (p.flag? "ixes").map (·.as! String)
    if manifestPath?.isSome && ixePath?.isNone then
      p.printError "error: aggregate verification with --ixes also requires --ixe"
      return 1
    let structuralAbove := ((p.flag? "structural-above").map (·.as! Nat)).getD
      Ix.Cli.AggregateCmd.defaultStructuralAbove
    let expected? ← match ixePath?, manifestPath? with
      | none, none => pure none
      | some ixePath, none =>
        let env ← match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
          | .error e => IO.eprintln s!"deserialize {ixePath} failed: {e}"; return 1
          | .ok env => pure env
        let some expectedTree := IxVM.ClaimHarness.envCanonicalTree env | do
          IO.eprintln "error: cannot verify an aggregate against an empty environment"
          return 1
        pure (some {
          claim := .checkEnv expectedTree.root none
          kinds := #[.lift, .flat]
        })
      | some ixePath, some manifestPath =>
        let env ← match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
          | .error e => IO.eprintln s!"deserialize {ixePath} failed: {e}"; return 1
          | .ok env => pure env
        let view ← match Ix.Cli.CheckCmd.parseIxesManifest
            (← IO.FS.readBinFile manifestPath) with
          | .error e => IO.eprintln s!"manifest parse failed: {e}"; return 1
          | .ok view => pure view
        if !(← Ix.Cli.CheckCmd.shardsCover env view.shards) then return 1
        let (statement, kind) ← match expectedFromManifest env view structuralAbove with
          | .error e => IO.eprintln e; return 1
          | .ok expected => pure expected
        if statement.assumptions.isSome then
          IO.eprintln s!"error: expected aggregate root retains assumptions \
            {statement.assumptions.map (·.root)}"
          return 1
        pure (some { claim := statement.claim, kinds := #[kind] })
      | none, some _ => unreachable!
    let backend ← match ← buildAggregateBackend recursionParameters with
      | .error e => IO.eprintln e; return 1
      | .ok backend => pure backend
    let mut rc : UInt32 := 0
    for hex in proofs do
      let proofAddr ← addrOfHex! "aggregate proof" hex
      if (← verifyAggregateProof backend expected? proofAddr) != 0 then
        rc := 1
    return rc
  match (p.flag? "ixe").map (·.as! String), (p.flag? "ixes").map (·.as! String) with
  | some ixe, some manifest =>
    verifyShardComposition ixe manifest ((p.flag? "shard").map (·.as! Nat)) proofs
  | _, _ =>
    if proofs.isEmpty then
      p.printError "error: must specify <proof-hex>... (or --ixe + --ixes for a shard partition)"
      return 1
    let (aiurSystem, compiled) ← match (← buildBackend) with
      | .error e => IO.eprintln e; return 1
      | .ok b => pure b
    let mut rc : UInt32 := 0
    for hex in proofs do
      let proofAddr ← addrOfHex! "proof" hex
      if (← verifyOneProof aiurSystem compiled proofAddr) != 0 then rc := 1
    return rc

def runVerifyCmd (p : Cli.Parsed) : IO UInt32 :=
  runVerifyCmdWith MultiStark.defaultRecursionParameters p

end Ix.Cli.VerifyCmd

open Ix.Cli.VerifyCmd in
def verifyCmd : Cli.Cmd := `[Cli|
  verify VIA runVerifyCmd;
  "Verify STARK proof(s) against their bundled claims, or a `.ixes` shard partition"

  FLAGS:
    "ixe"  : String; "Path to a serialized `.ixe` env (with --ixes). With no proof args and no --shard: verify the partition off-circuit (every constant owned by exactly one shard)."
    "ixes" : String; "Path to a `.ixes` shard manifest (with --ixe). For aggregate roots, reproduces the manifest-relative hybrid structural root."
    "shard" : Nat;   "0-based shard index K (with --ixe + --ixes). No proof: print shard K's reconstructed CheckEnv claim digest. With proof(s): bind each to shard K and verify."
    "aggregate";      "Interpret proofs as aggregate-first roots. With --ixe alone, accepts a single lift or all-flat canonical root; add --ixes for the exact lift/flat/structural manifest root."
    "structural-above" : Nat; "For --aggregate + --ixes, reproduce structural joins above N subject leaves (default 4096; must match proving)."

  ARGS:
    ...proofs : String; "32-byte hex address(es) of persisted `Ixon.Proof` wrappers in `~/.ix/store/`. Omit when using --ixe + --ixes."
]

end
