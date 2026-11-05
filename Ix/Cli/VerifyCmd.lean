/-
  `ix verify <proof-hex>`: read a persisted `Ixon.Proof` wrapper from
  the content-addressed store, extract the inner claim + opaque ZK
  proof bytes, reconstruct the Aiur-level public input, and run the
  certified Aiur backend's `verify`. Exits 0 on success, 1 with an error
  message otherwise.
-/
module
public import Cli
public import Ix.Cli.FormalAiur
public import Ix.Cli.FormalAggregate
public import Ix.Cli.CatalogAggregate
public import Ix.Cli.Compression

public section

namespace Ix.Cli.VerifyCmd

private def verifyDevelopmentInputs (p : Cli.Parsed) : IO UInt32 := do
  try
    unless p.hasFlag "verifier-bundle" && p.hasFlag "verifier-bundle-blake3" do
      throw <| IO.userError "--verifier-bundle and --verifier-bundle-blake3 must be supplied together"
    unless p.hasFlag "dev-srs" do
      throw <| IO.userError "development verifier requires --dev-srs"
    for flag in #["ixe", "ixes", "shard", "aggregate", "record", "structural-above",
        "compression-vk", "compression-vk-blake3"] do
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

/-- Whether any proof argument names a stored compressed proof. -/
private def anyCompressed (p : Cli.Parsed) : IO Bool := do
  for hex in p.variableArgsAs! String do
    let some addr := Address.fromString hex | continue
    try
      if Compression.isCompressed (← Compression.readProof addr).proof then return true
    catch _ => pure ()
  return false

def runVerifyCmd (p : Cli.Parsed) : IO UInt32 := do
  if p.hasFlag "verifier-bundle" || p.hasFlag "verifier-bundle-blake3" then
    return ← verifyDevelopmentInputs p
  let _ ← FormalAiur.selected p
  -- A compressed proof carries an aggregate CheckEnv claim.
  if p.hasFlag "aggregate" || (← anyCompressed p) then
    if let some ixc := (p.flag? "ixc").map (·.as! String) then
      return ← CatalogAggregate.verifyCatalog p ixc
    return ← FormalAggregate.verify p
  FormalAiur.verify p

end Ix.Cli.VerifyCmd

open Ix.Cli.VerifyCmd in
def verifyCmd : Cli.Cmd := `[Cli|
  verify VIA runVerifyCmd;
  "Verify STARK or compressed proof(s) against their bundled claims, or a `.ixes` shard partition"

  FLAGS:
    "legacy"; "Retired legacy Aiur backend flag."
    "formal"; "Compatibility alias for the default certified Aiur backend; conflicts with --legacy."
    "aiur-artifact" : String; "Trusted exported formal IxVM artifact; otherwise compile/cache local sources."
    "aggr-artifact" : String; "Trusted formal aggregation artifact; otherwise compile/cache local sources."
    "ixe"  : String; "Path to a serialized `.ixe` env (with --ixes). With no proof args and no --shard: verify the partition off-circuit (every constant owned by exactly one shard)."
    "ixes" : String; "Path to a `.ixes` shard manifest (with --ixe). For aggregate roots, reproduces the manifest-relative hybrid structural root."
    "binding-proof" : String; "With --ixes: the shard proofs assume the env's role binding (`ix prove --ixes --assume-binding`); this proof of the binding claim (`ix prove-binding`) is verified with them, so the composed verdict holds unconditionally."
    "shard" : Nat;   "0-based shard index K (with --ixe + --ixes). No proof: print shard K's reconstructed CheckEnv claim digest. With proof(s): bind each to shard K and verify."
    "aggregate";      "Interpret proofs as single-entrypoint aggregate roots. With --ixe, audit every environment constant and bind the canonical claim; add --ixes for the exact manifest-relative hybrid root."
    "ixc" : String;   "For --aggregate: a .ixc catalog directory. Recompute the catalog's root claim from its manifest and pieces (`ix aggregate --ixc`'s plan), check that each proof states it, verify it, and print every member's statement: label, toolchain, binding, literal class, specification digest and subjects."
    "structural-above" : Nat; "For --aggregate + --ixes, reproduce structural joins above N subject leaves (default 0; must match proving)."
    "record";         "With --ixe + --ixes and proof(s): after a proof binds to its shard and verifies, record it in the shard-proof index (`~/.ix/cache/shard-proofs/<claim-digest>` → address) so `ix prove --skip-proven` and `ix shard refine` reuse it."
    "dev-srs"; "Allow development compressed proofs; these are not production-secure."
    "compression-vk" : String; "Recursive verifying key a compressed aggregate verifies under, such as `ix compress derive-vk` derives. Requires --compression-vk-blake3."
    "compression-vk-blake3" : String; "Independent BLAKE3 pin of --compression-vk; do not obtain it from an untrusted proof."
    "verifier-bundle" : String; "Explicitly trusted development final-verifier JSON. Requires --verifier-bundle-blake3 and --dev-srs; accepts proof-wrapper files or store addresses."
    "verifier-bundle-blake3" : String; "Independent BLAKE3 pin for --verifier-bundle; do not obtain it from an untrusted proof."

  ARGS:
    ...proofs : String; "32-byte hex address(es) of persisted `Ixon.Proof` wrappers in `~/.ix/store/`. Omit when using --ixe + --ixes."
]

end
