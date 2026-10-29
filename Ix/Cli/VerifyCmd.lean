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
public import Ix.Cli.Compression
public import Ix.Address
public import Ix.Aiur.Compiler
public import Ix.Aiur.Protocol
public import Ix.Claim
public import Ix.Common
public import Ix.IxVM
public import Ix.IxVM.Toplevel
public import Ix.IxVM.ClaimHarness
public import Ix.Aggr
public import MultiStark
public import Ix.Store
public import Ix.Aggr.Backend
public import Ix.Aggr.Verification
public import Ix.Shard.Environment
public import Ix.Cli.ShardProofIndex

public section

open System (FilePath)

namespace Ix.Cli.VerifyCmd
open Aggr

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
  | .ok toplevel => match toplevel.compileWithGroups IxVM.functionGroups with
    | .error e => return .error s!"compilation failed: {e}"
    | .ok compiled =>
      return .ok (Aiur.AiurSystem.build compiled.bytecode commitmentParameters friParameters, compiled)

structure ExpectedAggregate where
  claim : Ix.Claim
  constantCount : Nat

private def verifyAggregateProof (getBackend : IO (Except String Aggr.VerificationBackend))
    (expected? : Option ExpectedAggregate) (proofAddr : Address)
    (devSrs : Bool := false) : IO UInt32 := do
  let bytes ← StoreIO.toIO (Store.read proofAddr)
  let wrapper ← match decodeAggregateWrapperAt proofAddr bytes with
    | .ok wrapper => pure wrapper
    | .error e => IO.eprintln s!"error: {e}"; return 1
  let .checkEnv _ assumptions? := wrapper.claim | do
    IO.eprintln s!"error: aggregate proof {proofAddr} does not bundle a CheckEnv claim"
    return 1
  match expected? with
  | some expected =>
    if wrapper.claim != expected.claim then
      IO.eprintln s!"error: aggregate claim {wrapper.claim} does not match expected {expected.claim}"
      return 1
  | none => pure ()
  if Compression.isCompressed wrapper.proof then
    return ← Compression.verifyProof proofAddr wrapper devSrs
  let proof ← match Aiur.Proof.ofBytesChecked wrapper.proof with
    | .ok proof => pure proof
    | .error e =>
      IO.eprintln s!"error: aggregate proof {proofAddr} does not decode: {e}"
      return 1
  let backend ← match ← getBackend with
    | .error e => IO.eprintln e; return 1
    | .ok backend => pure backend
  let outerClaim := Aggr.aggregateOuterClaim
    backend.allowed backend.aggrIdx wrapper.claim
  let verifyStarted ← IO.monoMsNow
  match backend.system.verify outerClaim proof with
  | .ok () =>
    IO.println s!"[verify] aggregate Aiur proof: {(← IO.monoMsNow) - verifyStarted}ms"
    IO.println s!"ok: aggregate proof {proofAddr} verifies {wrapper.claim}"
    if let some base := assumptions? then
      IO.println s!"[verify] conditional: the claim holds only provided every \
        constant under {base} is well-typed; it is not a standalone certificate"
    if let some expected := expected? then
      IO.println s!"[verify] aggregate coverage: {expected.constantCount}/\
        {expected.constantCount} environment constants committed exactly once"
      match assumptions? with
      | none =>
        IO.println s!"[verify] all {expected.constantCount} included constants \
          certified well-typed; 0 undischarged assumptions"
      | some base =>
        IO.println s!"[verify] all {expected.constantCount} included constants \
          certified well-typed provided the base {base} is"
    return 0
  | .error e =>
    IO.eprintln s!"error: aggregate verification failed: {e}"
    return 1

/-- Shard-aware verification (parity with `check`/`prove`):
    - `--shard K`, no proof: print shard K's reconstructed `CheckEnv` claim
      digest (the public input its proof must commit).
    - `--shard K` + proof(s): verify each proof AND bind it to shard K (its
      bundled claim must equal shard K's reconstructed claim).
    - no `--shard`, no proof: off-circuit coverage verdict (disjoint cover).
    - no `--shard` + proofs: composed verdict — coverage, every proof bound to a
      shard, and every shard covered by a valid proof.

    A nonempty `baseIxe` makes the partition an extension of that base: its
    constants are external, owned by no shard, and each shard claim assumes
    its edges to them, so the verdict is conditional on the base. -/
def verifyShardComposition (ixePath manifestPath : String) (shardK? : Option Nat)
    (proofs : List String) (record : Bool := false)
    (recursionParameters : Aggr.RecursionParameters := Aggr.defaultRecursionParameters)
    (baseIxe : String := "") :
    IO UInt32 := do
  let (ixonEnv, shards) ← match (← Ix.Shard.loadEnvAndShards manifestPath ixePath) with
    | .error e => IO.eprintln e; return 1
    | .ok r => pure r
  -- `--record`: a proof that binds to its shard and verifies is indexed
  -- under its claim digest, for `ix prove --skip-proven` / `ix shard refine`.
  let indexDir? ← if record then some <$> Ix.Cli.ShardProofIndex.indexDir else pure none
  let recordProof (digest proofAddr : Address) : IO Unit := do
    if let some dir := indexDir? then
      Ix.Cli.ShardProofIndex.writeAddress dir digest proofAddr
      IO.println s!"[verify] recorded {proofAddr} for claim {digest} in the shard-proof index"
  let digestOf (k : Nat) : IO (Option Address) := do
    match shards[k]? with
    | none => IO.eprintln s!"shard {k} out of range ({shards.size} shards)"; pure none
    | some blocks => match Ix.Shard.shardClaimDigest ixonEnv blocks with
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
      else recordProof d proofAddr
    return rc
  | none =>
    let mut external : Std.HashSet Address := {}
    if !baseIxe.isEmpty then
      match Ixon.deEnvAnon (← IO.FS.readBinFile baseIxe) with
      | .error e => IO.eprintln s!"deserialize {baseIxe} failed: {e}"; return 1
      | .ok base =>
        for (addr, _) in base.consts do
          external := external.insert addr
    if !(← Ix.Shard.shardsCover ixonEnv shards external) then return 1
    if proofs.isEmpty then return 0
    -- Composed verdict through the native Stage 2 import: Rust reconstructs
    -- every shard claim from the manifest (the Lean reconstruction above is
    -- one shard at a time on one core — ~15 s per Mathlib shard, an hour for
    -- the manifest), binds each proof to its shard by claim digest and
    -- verifies all proofs in parallel, requiring exactly one valid proof per
    -- shard.
    let (ixvmSystem, compiled) ← match (← buildBackend) with
      | .error e => IO.eprintln e; return 1
      | .ok b => pure b
    let verifyIdx := compiled.getFuncIdx `verify_claim |>.get!
    let backend ← match ← Aggr.buildVerificationBackend recursionParameters with
      | .error e => IO.eprintln e; return 1
      | .ok backend => pure backend
    let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
      | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {e}"; return 1
      | .ok handle => pure handle
    let proofHexes := String.intercalate "\n" proofs
    let verdict ← IO.lazyPure fun _ =>
      ixvmSystem.aggregateStage2 backend.system envHandle manifestPath proofHexes
        verifyIdx backend.aggrIdx 0 0 Aggr.defaultStructuralAbove 0
        true false recursionParameters.cacheFriBytes false false false 0 false 1 true 0
        false baseIxe
    match verdict with
    | .error e => IO.eprintln s!"[verify] FAIL: {e}"; return 1
    | .ok _ => pure ()
    for hex in proofs do
      let (proofAddr, d) ← claimDigestOfProof hex
      recordProof d proofAddr
    return 0

private def verifyDevelopmentInputs (p : Cli.Parsed) : IO UInt32 := do
  try
    unless p.hasFlag "verifier-bundle" && p.hasFlag "verifier-bundle-blake3" do
      throw <| IO.userError "--verifier-bundle and --verifier-bundle-blake3 must be supplied together"
    unless p.hasFlag "dev-srs" do
      throw <| IO.userError "development verifier requires --dev-srs"
    for flag in #["ixe", "ixes", "shard", "aggregate", "record", "structural-above", "base-ixe", "base-ixes", "base-structural-above"] do
      if p.hasFlag flag then
        throw <| IO.userError s!"--verifier-bundle cannot be combined with --{flag}"
    let inputs := p.variableArgsAs! String
    if inputs.isEmpty then
      throw <| IO.userError "expected a final proof file or store address"
    let path := p.flag! "verifier-bundle" |>.as! String
    let pin := p.flag! "verifier-bundle-blake3" |>.as! String
    let bundle ← IO.FS.readBinFile path
    for input in inputs do
      let (addr, wrapper) ← Compression.readProofInput input
      let claim := Ix.Claim.ser wrapper.claim
      let setup ← Compression.verifyDevelopment wrapper.proof claim bundle pin true
      unless setup == "development" do
        throw <| IO.userError s!"unexpected development verification setup: {setup}"
      IO.println s!"ok: development proof {addr} verifies claim {Address.blake3 claim} under the pinned verifier (not production-secure)"
    return 0
  catch error =>
    IO.eprintln s!"verify: {error}"
    return 1

/-- Verify with an explicit aggregate-recursion configuration. Ordinary IxVM
proof verification remains pinned to its independent canonical parameters. -/
def runVerifyCmdWith (recursionParameters : Aggr.RecursionParameters)
    (p : Cli.Parsed) : IO UInt32 := do
  if p.hasFlag "verifier-bundle" || p.hasFlag "verifier-bundle-blake3" then
    return ← verifyDevelopmentInputs p
  let proofs := (p.variableArgsAs! String).toList
  if !p.hasFlag "aggregate" && (p.hasFlag "base-ixes" || p.hasFlag "base-structural-above") then
    p.printError "error: --base-ixes and --base-structural-above apply to --aggregate; \
      shard-level verification takes --base-ixe alone"
    return 1
  if p.hasFlag "aggregate" then
    if proofs.isEmpty then
      p.printError "error: --aggregate requires at least one aggregate proof address"
      return 1
    let ixePath? : Option String := (p.flag? "ixe").map (·.as! String)
    let manifestPath? : Option String := (p.flag? "ixes").map (·.as! String)
    if manifestPath?.isSome && ixePath?.isNone then
      p.printError "error: aggregate verification with --ixes also requires --ixe"
      return 1
    let structuralAbove := ((p.flag? "structural-above").map (·.as! Nat)).getD
      Aggr.defaultStructuralAbove
    let baseIxe := ((p.flag? "base-ixe").map (·.as! String)).getD ""
    let baseIxes := ((p.flag? "base-ixes").map (·.as! String)).getD ""
    if (baseIxe.isEmpty != baseIxes.isEmpty) || (!baseIxe.isEmpty && manifestPath?.isNone) then
      p.printError "error: --base-ixe and --base-ixes go together, with --ixe and --ixes"
      return 1
    let baseStructuralAbove? := (p.flag? "base-structural-above").map (·.as! Nat)
    if baseIxe.isEmpty == baseStructuralAbove?.isSome then
      p.printError "error: --base-structural-above is required with, and only with, --base-ixe"
      return 1
    let expected? ← match ixePath?, manifestPath? with
      | none, none => pure none
      | some ixePath, none =>
        let env ← match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
          | .error e => IO.eprintln s!"deserialize {ixePath} failed: {e}"; return 1
          | .ok env => pure env
        let some expectedTree := IxVM.ClaimHarness.envCanonicalTree env | do
          IO.eprintln "error: cannot verify an aggregate against an empty environment"
          return 1
        let statement : Aggr.CheckEnvTrees := {
          subjects := expectedTree
          assumptions := none
        }
        let constantCount ← match auditAggregateConstants env statement with
          | .error e => IO.eprintln s!"error: {e}"; return 1
          | .ok count => pure count
        pure (some { claim := statement.claim, constantCount })
      | some ixePath, some manifestPath =>
        let started ← IO.monoMsNow
        let envHandle ← match ← IO.lazyPure fun _ => Aiur.EnvHandle.fromIxe ixePath with
          | .error e =>
            IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {e}"
            return 1
          | .ok handle => pure handle
        let native ← match ← IO.lazyPure fun _ =>
            Aiur.AiurSystem.aggregateExpected envHandle manifestPath structuralAbove
              baseIxe baseIxes (baseStructuralAbove?.getD 0) with
          | .error e =>
            IO.eprintln s!"native aggregate manifest audit failed: {e}"
            return 1
          | .ok expected => pure expected
        let claim ← match Ixon.runGet Ix.Claim.get native.claimBytes with
          | .error e =>
            IO.eprintln s!"native aggregate root claim decode failed: {e}"
            return 1
          | .ok claim => pure claim
        IO.println s!"[verify] native manifest audit: {native.constantCount} constants in \
          {(← IO.monoMsNow) - started}ms"
        pure (some { claim, constantCount := native.constantCount })
      | none, some _ => unreachable!
    let backendRef ← IO.mkRef (none : Option (Except String Aggr.VerificationBackend))
    let getBackend : IO (Except String Aggr.VerificationBackend) := do
      if let some result ← backendRef.get then
        return result
      let backendStarted ← IO.monoMsNow
      let result ← Aggr.buildVerificationBackend recursionParameters
      backendRef.set (some result)
      if let .ok _ := result then
        IO.println s!"[verify] aggregate backend setup: \
          {(← IO.monoMsNow) - backendStarted}ms"
      return result
    let mut rc : UInt32 := 0
    for hex in proofs do
      let proofAddr ← addrOfHex! "aggregate proof" hex
      if (← verifyAggregateProof getBackend expected? proofAddr
          (p.hasFlag "dev-srs")) != 0 then
        rc := 1
    return rc
  match (p.flag? "ixe").map (·.as! String), (p.flag? "ixes").map (·.as! String) with
  | some ixe, some manifest =>
    verifyShardComposition ixe manifest ((p.flag? "shard").map (·.as! Nat)) proofs
      (p.hasFlag "record") recursionParameters
      (((p.flag? "base-ixe").map (·.as! String)).getD "")
  | _, _ =>
    if proofs.isEmpty then
      p.printError "error: must specify <proof-hex>... (or --ixe + --ixes for a shard partition)"
      return 1
    let mut backend? := none
    let mut rc : UInt32 := 0
    for hex in proofs do
      let proofAddr ← addrOfHex! "proof" hex
      let wrapper ← Compression.readProof proofAddr
      if Compression.isCompressed wrapper.proof then
        if (← Compression.verifyProof proofAddr wrapper (p.hasFlag "dev-srs")) != 0 then
          rc := 1
      else
        let (aiurSystem, compiled) ← match backend? with
          | some b => pure b
          | none =>
            let b ← IO.ofExcept (← buildBackend)
            backend? := some b
            pure b
        if (← verifyOneProof aiurSystem compiled proofAddr) != 0 then rc := 1
    return rc

def runVerifyCmd (p : Cli.Parsed) : IO UInt32 :=
  runVerifyCmdWith Aggr.defaultRecursionParameters p

end Ix.Cli.VerifyCmd

open Ix.Cli.VerifyCmd in
def verifyCmd : Cli.Cmd := `[Cli|
  verify VIA runVerifyCmd;
  "Verify proof(s) against their bundled claims, or a `.ixes` shard partition"

  FLAGS:
    "dev-srs"; "Allow development compressed proofs; these are not production-secure."
    "verifier-bundle" : String; "Explicitly trusted development final-verifier JSON. Requires --verifier-bundle-blake3 and --dev-srs; accepts proof-wrapper files or store addresses."
    "verifier-bundle-blake3" : String; "Independent BLAKE3 pin for --verifier-bundle; do not obtain it from an untrusted proof."
    "ixe"  : String; "Path to a serialized `.ixe` env (with --ixes). With no proof args and no --shard: verify the partition off-circuit (every constant owned by exactly one shard)."
    "ixes" : String; "Path to a `.ixes` shard manifest (with --ixe). For aggregate roots, reproduces the manifest-relative hybrid structural root."
    "shard" : Nat;   "0-based shard index K (with --ixe + --ixes). No proof: print shard K's reconstructed CheckEnv claim digest. With proof(s): bind each to shard K and verify."
    "aggregate";      "Interpret proofs as single-entrypoint aggregate roots. With --ixe, audit every environment constant and bind the canonical claim; add --ixes for the exact manifest-relative hybrid root."
    "structural-above" : Nat; "For --aggregate + --ixes, reproduce structural joins above N subject leaves (default 4096; must match proving)."
    "base-ixe" : String; "With --ixe + --ixes: the environment extends this base library, whose constants are external (owned by no shard). Without --aggregate: the coverage and composed shard verdicts accept them as external, conditional on the base. With --aggregate (and --base-ixes, --base-structural-above): expect the rebased root `CheckEnv(R, some R_base)` that `ix prove --base-ixe` produces, covering exactly the constants outside the base; such a root is conditional on the base."
    "base-ixes" : String; "With --base-ixe: the base's `.ixes` manifest, from which its root is rebuilt."
    "base-structural-above" : Nat; "Required with --base-ixe: the structural threshold the base root was aggregated with, as passed to `ix prove --base-structural-above`."
    "record";         "With --ixe + --ixes and proof(s): after a proof binds to its shard and verifies, record it in the shard-proof index (`~/.ix/cache/shard-proofs/<claim-digest>` → address) so `ix prove --skip-proven` and `ix shard refine` reuse it. How already-proved leaves are imported before a refinement."

  ARGS:
    ...proofs : String; "32-byte hex addresses of persisted Ixon.Proof wrappers. With --verifier-bundle, proof-wrapper file paths are also accepted. Omit for --ixe + --ixes partition auditing."
]

end
