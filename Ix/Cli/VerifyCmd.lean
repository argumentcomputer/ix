/-
  `ix verify <proof-hex>`: read a persisted `Ixon.Proof` wrapper from
  the content-addressed store, extract the inner claim + opaque ZK
  proof bytes, reconstruct the Aiur-level public input, and verify the
  proof against the IxVM program compiled by the verified Aiur compiler.
  Exits 0 on success, 1 with an error message otherwise.
-/
module
public import Cli
public import Ix.Cli.Compression
public import Ix.Cli.FormalAiur
public import Ix.Cli.FormalAggregate
public import Ix.Cli.CatalogAggregate
public import Ix.Cli.ClaimPolicy

public section

namespace Ix.Cli.VerifyCmd

private def verifyDevelopmentInputs (p : Cli.Parsed) : IO UInt32 := do
  try
    unless p.hasFlag "verifier-bundle" && p.hasFlag "verifier-bundle-blake3" do
      throw <| IO.userError "--verifier-bundle and --verifier-bundle-blake3 must be supplied together"
    unless p.hasFlag "dev-srs" do
      throw <| IO.userError "development verifier requires --dev-srs"
    for flag in #["ixe", "ixes", "shard", "aggregate", "record", "structural-above", "binding-proof",
        "l3-verifier", "l3-verifier-blake3"] do
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
      let statement ← ClaimPolicy.admit p wrapper.claim (route := .compressed)
      let claim := Ix.Claim.ser wrapper.claim
      let setup ← Compression.verifyDevelopment wrapper.proof claim bundle pin true
      unless setup == "development" do
        throw <| IO.userError s!"unexpected development verification setup: {setup}"
      IO.println s!"ok: development proof {addr} verifies claim {Address.blake3 claim} under the pinned verifier (not production-secure)"
      IO.println statement
    return 0
  catch error =>
    IO.eprintln s!"verify: {error}"
    return 1

private def readBytesInput (input : String) : IO ByteArray := do
  if let some addr := Address.fromString input then
    let bytes ← StoreIO.toIO (Store.read addr)
    let actual := Address.blake3 bytes
    if actual != addr then
      throw <| IO.userError s!"store object {addr} hashes to {actual}"
    return bytes
  IO.FS.readBinFile input

private def verifyL3Inputs (p : Cli.Parsed) : IO UInt32 := do
  try
    unless p.hasFlag "l3-verifier" && p.hasFlag "l3-verifier-blake3" do
      throw <| IO.userError "--l3-verifier and --l3-verifier-blake3 must be supplied together"
    for flag in #["verifier-bundle", "verifier-bundle-blake3", "aiur-gl", "aiur-gl-blake3",
        "aiur-chain", "aiur-chain-blake3", "aiur-kzg-key", "aiur-kzg-key-blake3",
        "ixc", "shard", "record", "binding-proof", "dynamic-claim"] do
      if p.hasFlag flag then
        throw <| IO.userError s!"--l3-verifier cannot be combined with --{flag}"
    let inputs := p.variableArgsAs! String
    if inputs.isEmpty then
      throw <| IO.userError "expected an L3 proof file or store address"
    let bundlePath := p.flag! "l3-verifier" |>.as! String
    let bundlePin := p.flag! "l3-verifier-blake3" |>.as! String
    let allowDev := p.hasFlag "dev-srs"
    let (expected, tableEnvs) ← FormalAggregate.expectedClaimForVerify p
    for input in inputs do
      let (addr, wrapper) ← Compression.readProofInput input
      unless expected.all (· == wrapper.claim) do
        throw <| IO.userError "L3 proof does not match the requested environment/manifest"
      let statement ← ClaimPolicy.admit p wrapper.claim (envs := pure tableEnvs)
        (route := .compressed)
      let .checkEnv .. := wrapper.claim
        | throw <| IO.userError s!"L3 proof {addr} must bundle a CheckEnv claim"
      unless FormalAggregate.isL3Proof wrapper.proof do
        throw <| IO.userError s!"proof {addr} is not an Aiur L3 proof envelope (expected IXL3BN1 or IXL3BL1)"
      let claimBytes := Ix.Claim.ser wrapper.claim
      let info ← FormalAggregate.verifyL3Bundle wrapper.proof claimBytes bundlePath bundlePin allowDev
      let [curve, setup] := info.splitOn "\t"
        | throw <| IO.userError s!"unexpected L3 verifier response: {info}"
      match setup with
      | "development" =>
        unless allowDev do
          throw <| IO.userError "development L3 proof accepted without --dev-srs"
        IO.println s!"ok: development L3 {curve} PLONK proof {addr} verifies claim {Address.blake3 claimBytes} under pinned bundle (not production-secure)"
      | "ignition" =>
        IO.println s!"ok: L3 {curve} PLONK proof {addr} verifies claim {Address.blake3 claimBytes} under the Aztec Ignition powers of tau"
      | "filecoin" =>
        IO.println s!"ok: L3 {curve} PLONK proof {addr} verifies claim {Address.blake3 claimBytes} under the Filecoin powers of tau"
      | other =>
        throw <| IO.userError s!"unsupported L3 verification setup: {other}"
      IO.println statement
    return 0
  catch error =>
    IO.eprintln s!"verify: {error}"
    return 1

/-- Policy-check and verify dynamic-linking claims (`DynamicLinkStatement` `0xE8 0x0D`,
Mode-3a `LinkedClaim` validators `12`/`13`, or `EvalAssumedClaim` validators `10`/`11`)
paired with `IXAGGR2` aggregate proof(s). Enforces `ClaimPolicy.admitDynamicBytes`
(`refusalDynamicBytes` / `refusalLinkedClaim` / `refusalDynamicLinkStatement`) BEFORE
invoking the STARK verifier. -/
def verifyDynamicInputs (p : Cli.Parsed) : IO UInt32 := do
  try
    for flag in #["ixe", "ixes", "shard", "ixc", "record", "structural-above", "distributed",
        "verifier-bundle", "verifier-bundle-blake3", "l3-verifier", "l3-verifier-blake3",
        "binding-proof"] do
      if p.hasFlag flag then
        throw <| IO.userError s!"--dynamic-claim cannot be combined with --{flag}"
    let claimInput := p.flag! "dynamic-claim" |>.as! String
    let claimBytes ← readBytesInput claimInput
    let rawEntryInputs := (p.flag? "linked-entry").map (·.as! (Array String)) |>.getD #[]
    let linkedEntries? : Option (Array Ix.DynamicLink.LinkedCircuitEntry) ←
      if rawEntryInputs.isEmpty then
        pure none
      else do
        let mut entries : Array Ix.DynamicLink.LinkedCircuitEntry := #[]
        for entryInput in rawEntryInputs do
          let ebytes ← readBytesInput entryInput
          let entry ← IO.ofExcept (Ix.DynamicLink.deLinkedCircuitEntry ebytes)
          entries := entries.push entry
        pure (some entries)
    let statement ← ClaimPolicy.admitDynamicBytes p claimBytes linkedEntries?
    let inputs := p.variableArgsAs! String
    if inputs.isEmpty then
      throw <| IO.userError "expected an IXAGGR2 aggregate proof file or store address for --dynamic-claim"
    let ctx ← FormalAggregate.context p
    let claimDigest := Address.blake3 claimBytes
    for input in inputs do
      let proofBytes ← readBytesInput input
      let raw ← FormalAggregate.rawProof .aggr proofBytes
      let _ ← ctx.aggrSystem.verify "MultiStark::ix_aggr"
        ((Aggr.pubInput ctx.allowed claimBytes).map (·.val)) raw
      IO.println s!"ok: aggregate proof {input} verifies dynamic claim {claimDigest}"
      IO.println statement
    return 0
  catch error =>
    IO.eprintln s!"verify: {error}"
    return 1

def runVerifyCmd (p : Cli.Parsed) : IO UInt32 := do
  if let .error err := ClaimPolicy.ofParsedChecked p then
    IO.eprintln s!"verify: {err}"
    return 1
  if p.hasFlag "dynamic-claim" then
    return ← verifyDynamicInputs p
  if p.hasFlag "l3-verifier" || p.hasFlag "l3-verifier-blake3" then
    return ← verifyL3Inputs p
  if AiurCompression.selected p && !p.hasFlag "aggregate" then
    throw (IO.userError "Aiur compression verification requires --aggregate")
  if AiurCompression.selected p && p.hasFlag "ixc" then
    throw (IO.userError "Aiur compression currently accepts CheckEnv proofs, not --ixc catalog proofs")
  if AiurCompression.selected p then
    let _ ← AiurCompression.options p
  if p.hasFlag "verifier-bundle" || p.hasFlag "verifier-bundle-blake3" then
    return ← verifyDevelopmentInputs p
  if p.hasFlag "aggregate" then
    if let some ixc := (p.flag? "ixc").map (·.as! String) then
      return ← CatalogAggregate.verifyCatalog p ixc
    return ← FormalAggregate.verify p
  for input in p.variableArgsAs! String do
    if let .ok (addr, wrapper) ← (Compression.readProofInput input).toBaseIO then
      if FormalAggregate.isL3Proof wrapper.proof then
        IO.eprintln s!"verify: L3 compressed proof {addr} requires --l3-verifier <bundle> --l3-verifier-blake3 <pin>"
        return 1
  FormalAiur.verify p (FormalAggregate.verifyShrunkProof p)

end Ix.Cli.VerifyCmd

open Ix.Cli.VerifyCmd in
def verifyCmd : Cli.Cmd := `[Cli|
  verify VIA runVerifyCmd;
  "Verify proof(s) against their bundled claims, or a `.ixes` shard partition, and print each claim's kind, subject, the theorem that covers it (or that none does) and its conditions. By default only unconditional typing claims (check, check-env) under this build's specifications and the default role table, or a table the kernel's executable admission admits, are accepted; the --allow-* flags accept more. A catalog claim needs --aggregate --ixc."

  FLAGS:
    "aiur-chain" : String; "Trusted GL-to-BN chain manifest; verification needs no proving powers."
    "aiur-chain-blake3" : String; "Independent BLAKE3 pin for the exact --aiur-chain manifest bytes."
    "aiur-gl" : String; "Use the Aiur CompressGL KZG stage with this independently trusted compiler artifact."
    "aiur-gl-blake3" : String; "Independent BLAKE3 pin for --aiur-gl."
    "aiur-kzg-key" : String; "Independently trusted CompressGL KZG verifier key."
    "aiur-kzg-key-blake3" : String; "Independent BLAKE3 pin for --aiur-kzg-key."
    "aiur-max-log-height" : Nat; "Fixed public Aiur trace-height bound (default 24)."
    "aiur-quotient-degree" : Nat; "Fixed public Aiur quotient-degree budget (default 2)."
    "aiur-artifact" : String; "Trusted exported formal IxVM artifact; otherwise compile/cache local sources."
    "aiur-artifact-digest" : String; "Refuse an IxVM artifact whose BLAKE3 digest is not this one."
    "aggr-artifact" : String; "Trusted formal aggregation artifact; otherwise compile/cache local sources."
    "aggr-artifact-digest" : String; "Refuse an aggregation artifact whose BLAKE3 digest is not this one."
    "verifier-artifact" : String; "Trusted formal recursive verifier artifact for IXSTARK6 proofs; otherwise compile/cache local sources."
    "verifier-artifact-digest" : String; "Refuse a recursive verifier artifact whose BLAKE3 digest is not this one."
    "dev-srs"; "Allow development compressed proofs; these are not production-secure."
    "verifier-bundle" : String; "Explicitly trusted development final-verifier JSON. Requires --verifier-bundle-blake3 and --dev-srs; accepts proof-wrapper files or store addresses."
    "verifier-bundle-blake3" : String; "Independent BLAKE3 pin for --verifier-bundle; do not obtain it from an untrusted proof."
    "l3-verifier" : String; "Explicitly trusted Aiur L3 verifier bundle JSON (ix-l3-verifier-v1). Requires --l3-verifier-blake3; accepts proof-wrapper files or store addresses."
    "l3-verifier-blake3" : String; "Independent BLAKE3 pin for --l3-verifier; do not obtain it from an untrusted proof."
    "ixe"  : String; "Path to a serialized `.ixe` env (with --ixes). With no proof args and no --shard: verify the partition off-circuit (every constant owned by exactly one shard)."
    "ixes" : String; "Path to a `.ixes` shard manifest (with --ixe). For aggregate roots, reproduces the manifest-relative hybrid structural root."
    "binding-proof" : String; "A proof of the binding claim (`ix prove-binding`) verified with the IxVM typing proofs: with --ixe/--ixes the environment's role table (the shard proofs may assume it, `ix prove --ixes --assume-binding`), otherwise the table the binding claim names. Each typing claim must be a check or check-env claim under that table, or it is refused. IxVM.Refinement.Endpoint.circuitComposed then covers each claim with no user axioms, no typing assumptions and no literal class; no theorem states shard claims with assumption trees or the composition of a partition."
    "shard" : Nat;   "0-based shard index K (with --ixe + --ixes). No proof: print shard K's reconstructed CheckEnv claim digest. With proof(s): bind each to shard K and verify."
    "aggregate";      "Interpret proofs as single-entrypoint aggregate roots. With --ixe, audit every environment constant and bind the canonical claim; add --ixes for the exact manifest-relative hybrid root."
    "ixc" : String;   "For --aggregate: a .ixc catalog directory. Recompute the catalog's root claim from its manifest and pieces (`ix aggregate --ixc`'s plan), check that each proof states it, verify it, and print every member's statement: label, toolchain, binding, literal class, specification digest and subjects."
    "structural-above" : Nat; "For --aggregate + --ixes, reproduce structural joins above N subject leaves (default 0; must match proving)."
    "record";         "With --ixe + --ixes and proof(s): after a proof binds to its shard and verifies, record it in the shard-proof index (`~/.ix/cache/formal-shard-proofs/<claim-digest>` → address) so `ix prove --skip-proven` and `ix shard refine` reuse it."
    "binding-env" : String; "An `.ixe` whose role binding is the claim's table, with the records it binds and its evidence theorems: the kernel admits the table over them (once per table; recorded in `~/.ix/cache/table-admission`). --ixe serves when its binding is the claim's; a catalog's pieces serve their members."
    "dynamic-claim" : String; "Path or 64-hex store address of raw dynamic claim bytes (DynamicLinkStatement 0xE8 0x0D, LinkedClaim validator 12/13, or EvalAssumedClaim validator 10/11) to admit via ClaimPolicy and verify against IXAGGR2 aggregate proof(s)."
    "linked-entry" : Array String; "Path or 64-hex store address of a canonical LinkedCircuitEntry (0xE8 0x0F) preimage required to audit a validator 12/13 LinkedClaim passed via --dynamic-claim."
    "allow-custom-binding"; "Accept a claim relative to a role binding other than the default role table that the kernel does not admit here, or to a literal class (which no theorem covers)."
    "allow-eval-claim"; "Accept an eval claim (an output is its input's normal form), which no theorem states."
    "allow-axioms"; "Accept a claim that depends on axioms beyond the standard three."
    "allow-assumed-binding"; "Accept a claim that assumes its role binding meets the specifications, with no binding proof."
    "allow-assumptions"; "Accept a claim conditional on typing assumptions (assumed leaves) that no verified proof discharges."
    "allow-reveal-claim"; "Accept a reveal claim (fields of a committed constant), which states no typing."
    "allow-contains-claim"; "Accept a contains claim (a leaf of a merkle tree), which states no typing."
    "allow-binding-claim"; "Accept a binding claim (a role table meets this build's specifications) verified on its own; --binding-proof needs no flag."
    "allow-dynamic-circuit" : Array String; "Allowlist a Tier-1 standalone DynamicLinkStatement circuit (<vk-hex>:<entry-idx>:<nin>:<nout>; VK-wide wildcards and unpinned I/O arities are forbidden); does NOT authorize validator 12/13 LinkedClaim proofs."
    "allow-linked-circuit" : Array String; "Allowlist a Mode-3a equality-bridge circuit (<vk-hex>:<entry-idx>:<target-hex>:<cert-hex>:<eval-type-hex> or with :ixonAddrPair: codec) for validator 12/13 LinkedClaim proofs; refused by default."

  ARGS:
    ...proofs : String; "32-byte hex addresses of persisted Ixon.Proof wrappers. With --verifier-bundle or --l3-verifier, proof-wrapper file paths are also accepted. Omit for --ixe + --ixes partition auditing."
]

end
