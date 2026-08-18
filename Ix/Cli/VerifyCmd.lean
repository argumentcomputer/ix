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
public import Ix.Store
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
  let proof := Aiur.Proof.ofBytes wrapper.proof
  -- `verify_claim` takes the 32-G blake3 digest of the serialized claim.
  let claimDigest := Address.blake3 (Ix.Claim.ser wrapper.claim)
  let funIdx ← match compiled.getFuncIdx `verify_claim with
    | some i => pure i
    | none =>
      IO.eprintln "error: `verify_claim` entrypoint missing from compiled toplevel"
      return 1
  let input : Array Aiur.G := claimDigest.hash.data.map .ofUInt8
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

/-- Shard-aware verification (parity with `check`/`prove`):
    - `--shard K`, no proof: print shard K's reconstructed `CheckEnv` claim
      digest (the public input its proof must commit).
    - `--shard K` + proof(s): verify each proof AND bind it to shard K (its
      bundled claim must equal shard K's reconstructed claim).
    - no `--shard`, no proof: off-circuit coverage verdict (disjoint cover).
    - no `--shard` + proofs: composed verdict — coverage, every proof bound to a
      shard, and every shard covered by a valid proof.

    A shard owning no blocks has no `CheckEnv` claim and owns no constants, so
    it needs no proof and is not counted against the composed verdict. -/
def verifyShardComposition (ixePath manifestPath : String) (shardK? : Option Nat)
    (proofs : List String) : IO UInt32 := do
  let (ixonEnv, shards) ← match (← Ix.Cli.CheckCmd.loadEnvAndShards manifestPath ixePath) with
    | .error e => IO.eprintln e; return 1
    | .ok r => pure r
  let claimDigestOfProof (hex : String) : IO (Address × Address) := do
    let proofAddr ← addrOfHex! "proof" hex
    let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read proofAddr)))
    pure (proofAddr, Address.blake3 (Ix.Claim.ser wrapper.claim))
  match shardK? with
  | some k =>
    let some blocks := shards[k]?
      | IO.eprintln s!"shard {k} out of range ({shards.size} shards)"; return 1
    if blocks.isEmpty then
      -- Degenerate work unit: nothing owned, so no claim exists and no proof
      -- can bind to it. Saying so beats reporting an empty-owned-set failure
      -- from deep inside claim reconstruction.
      if proofs.isEmpty then
        IO.println s!"shard {k} owns no blocks: no CheckEnv claim, nothing to prove"
        return 0
      IO.eprintln s!"[verify] FAIL: shard {k} owns no blocks — no proof can bind to it"
      return 1
    let expected ← match Ix.Cli.CheckCmd.shardClaimDigest ixonEnv blocks with
      | .error e => IO.eprintln s!"reconstruct shard {k} claim failed: {e}"; return 1
      | .ok d => pure d
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
    -- One env pass for every shard's digest.
    let digests ← match Ix.Cli.CheckCmd.shardClaimDigests ixonEnv shards with
      | .error e => IO.eprintln s!"reconstruct shard claims failed: {e}"; return 1
      | .ok d => pure d
    let mut digestToShard : Std.HashMap Address Nat := {}
    -- An empty shard owns no constants, so the other shards' proofs still
    -- cover the whole env: it starts out satisfied rather than missing.
    let mut covered : Std.HashSet Nat := {}
    let mut empties : Nat := 0
    for (d?, k) in digests.mapIdx (fun k d? => (d?, k)) do
      match d? with
      | some d => digestToShard := digestToShard.insert d k
      | none => empties := empties + 1; covered := covered.insert k
    if empties != 0 then
      IO.println s!"[verify] {empties} shard(s) own no blocks: no claim, no proof required"
    let (aiurSystem, compiled) ← match (← buildBackend) with
      | .error e => IO.eprintln e; return 1
      | .ok b => pure b
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

def runVerifyCmd (p : Cli.Parsed) : IO UInt32 := do
  let proofs := (p.variableArgsAs! String).toList
  let env? := (p.flag? "env").map (·.as! String)
  let shards? := (p.flag? "shards").map (·.as! String)
  let shard? := (p.flag? "shard").map (·.as! Nat)
  match env?, shards?, shard? with
  | some ixe, some manifest, shard? =>
    verifyShardComposition ixe manifest shard? proofs
  | some _, none, _ =>
    p.printError "error: --env requires --shards <path.ixes>"
    return 1
  | none, some _, _ =>
    p.printError "error: --shards requires --env <path.ixe>"
    return 1
  | none, none, some _ =>
    p.printError "error: --shard requires --env <path.ixe> and --shards <path.ixes>"
    return 1
  | none, none, none =>
    if proofs.isEmpty then
      p.printError "error: must specify <proof-hex>... (or --env + --shards for a shard partition)"
      return 1
    let (aiurSystem, compiled) ← match (← buildBackend) with
      | .error e => IO.eprintln e; return 1
      | .ok b => pure b
    let mut rc : UInt32 := 0
    for hex in proofs do
      let proofAddr ← addrOfHex! "proof" hex
      if (← verifyOneProof aiurSystem compiled proofAddr) != 0 then rc := 1
    return rc

end Ix.Cli.VerifyCmd

open Ix.Cli.VerifyCmd in
def verifyCmd : Cli.Cmd := `[Cli|
  verify VIA runVerifyCmd;
  "Verify STARK proof(s) against their bundled claims, or a `.ixes` shard partition"

  FLAGS:
    "env"  : String; "Path to a serialized `.ixe` env (with --shards). With no proof args and no --shard: verify the partition off-circuit (every constant owned by exactly one shard)."
    "shards" : String; "Path to a `.ixes` shard manifest (with --env), e.g. from `ix shard`."
    "shard" : Nat;   "0-based shard index K (with --env + --shards). No proof: print shard K's reconstructed CheckEnv claim digest. With proof(s): bind each to shard K and verify."

  ARGS:
    ...proofs : String; "32-byte hex address(es) of persisted `Ixon.Proof` wrappers in `~/.ix/store/`. Omit when using --env + --shards."
]

end
