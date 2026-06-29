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

/-- Same parameters as `ix prove`. Mismatch makes verification fail
    silently with no useful diagnostic, so these MUST match the
    proving side until they migrate into the proof header. -/
private def commitmentParameters : Aiur.CommitmentParameters :=
  { logBlowup := 1, capHeight := 0 }

private def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 20
  queryProofOfWorkBits := 0
}

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

def runVerifyCmd (p : Cli.Parsed) : IO UInt32 := do
  let proofs := (p.variableArgsAs! String).toList
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

end Ix.Cli.VerifyCmd

open Ix.Cli.VerifyCmd in
def verifyCmd : Cli.Cmd := `[Cli|
  verify VIA runVerifyCmd;
  "Verify STARK proof(s) against their bundled claims, or a `.ixes` shard partition"

  FLAGS:
    "ixe"  : String; "Path to a serialized `.ixe` env (with --ixes). With no proof args and no --shard: verify the partition off-circuit (every constant owned by exactly one shard)."
    "ixes" : String; "Path to a `.ixes` shard manifest (with --ixe)."
    "shard" : Nat;   "0-based shard index K (with --ixe + --ixes). No proof: print shard K's reconstructed CheckEnv claim digest. With proof(s): bind each to shard K and verify."

  ARGS:
    ...proofs : String; "32-byte hex address(es) of persisted `Ixon.Proof` wrappers in `~/.ix/store/`. Omit when using --ixe + --ixes."
]

end
