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
    for flag in #["ixe", "ixes", "shard", "aggregate", "record", "structural-above"] do
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
      let statement ← ClaimPolicy.admit p wrapper.claim
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

def runVerifyCmd (p : Cli.Parsed) : IO UInt32 := do
  if p.hasFlag "verifier-bundle" || p.hasFlag "verifier-bundle-blake3" then
    return ← verifyDevelopmentInputs p
  if p.hasFlag "aggregate" then
    if let some ixc := (p.flag? "ixc").map (·.as! String) then
      return ← CatalogAggregate.verifyCatalog p ixc
    return ← FormalAggregate.verify p
  FormalAiur.verify p

end Ix.Cli.VerifyCmd

open Ix.Cli.VerifyCmd in
def verifyCmd : Cli.Cmd := `[Cli|
  verify VIA runVerifyCmd;
  "Verify proof(s) against their bundled claims, or a `.ixes` shard partition, and print each claim's kind, subject and conditions. By default only unconditional typing claims (eval, check, check-env) under this build's specifications and the default role table, or a table the kernel admits, are accepted; the --allow-* flags accept more. A catalog claim needs --aggregate --ixc."

  FLAGS:
    "aiur-artifact" : String; "Trusted exported formal IxVM artifact; otherwise compile/cache local sources."
    "aiur-artifact-digest" : String; "Refuse an IxVM artifact whose BLAKE3 digest is not this one."
    "aggr-artifact" : String; "Trusted formal aggregation artifact; otherwise compile/cache local sources."
    "aggr-artifact-digest" : String; "Refuse an aggregation artifact whose BLAKE3 digest is not this one."
    "dev-srs"; "Allow development compressed proofs; these are not production-secure."
    "verifier-bundle" : String; "Explicitly trusted development final-verifier JSON. Requires --verifier-bundle-blake3 and --dev-srs; accepts proof-wrapper files or store addresses."
    "verifier-bundle-blake3" : String; "Independent BLAKE3 pin for --verifier-bundle; do not obtain it from an untrusted proof."
    "ixe"  : String; "Path to a serialized `.ixe` env (with --ixes). With no proof args and no --shard: verify the partition off-circuit (every constant owned by exactly one shard)."
    "ixes" : String; "Path to a `.ixes` shard manifest (with --ixe). For aggregate roots, reproduces the manifest-relative hybrid structural root."
    "binding-proof" : String; "With --ixes: the shard proofs assume the env's role binding (`ix prove --ixes --assume-binding`); this proof of the binding claim (`ix prove-binding`) is verified with them, so the composed verdict holds unconditionally."
    "shard" : Nat;   "0-based shard index K (with --ixe + --ixes). No proof: print shard K's reconstructed CheckEnv claim digest. With proof(s): bind each to shard K and verify."
    "aggregate";      "Interpret proofs as single-entrypoint aggregate roots. With --ixe, audit every environment constant and bind the canonical claim; add --ixes for the exact manifest-relative hybrid root."
    "ixc" : String;   "For --aggregate: a .ixc catalog directory. Recompute the catalog's root claim from its manifest and pieces (`ix aggregate --ixc`'s plan), check that each proof states it, verify it, and print every member's statement: label, toolchain, binding, literal class, specification digest and subjects."
    "distributed";    "Bind one default-backend distributed proof to the whole environment. Requires --ixe and --ixes; the manifest must cover the environment exactly."
    "structural-above" : Nat; "For --aggregate + --ixes, reproduce structural joins above N subject leaves (default 4096; must match proving)."
    "record";         "With --ixe + --ixes and proof(s): after a proof binds to its shard and verifies, record it in the shard-proof index (`~/.ix/cache/formal-shard-proofs/<claim-digest>` → address) so `ix prove --skip-proven` and `ix shard refine` reuse it."
    "binding-env" : String; "An `.ixe` whose role binding is the claim's table, with the records it binds and its evidence theorems: the kernel admits the table over them (once per table; recorded in `~/.ix/cache/table-admission`). --ixe serves when its binding is the claim's; a catalog's pieces serve their members."
    "allow-custom-binding"; "Accept a claim relative to a role binding the kernel does not admit here, or to a literal class (outside the IxVM consistency theorem)."
    "allow-axioms"; "Accept a claim that depends on axioms beyond the standard three."
    "allow-assumed-binding"; "Accept a claim that assumes its role binding meets the specifications, with no binding proof."
    "allow-assumptions"; "Accept a claim conditional on typing assumptions (assumed leaves) that no verified proof discharges."
    "allow-reveal-claim"; "Accept a reveal claim (fields of a committed constant), which states no typing."
    "allow-contains-claim"; "Accept a contains claim (a leaf of a merkle tree), which states no typing."
    "allow-resource-claim"; "Accept a resource claim, which the IxVM consistency theorem does not cover."
    "allow-binding-claim"; "Accept a binding claim (a role table meets this build's specifications) verified on its own; --binding-proof needs no flag."

  ARGS:
    ...proofs : String; "32-byte hex addresses of persisted Ixon.Proof wrappers. With --verifier-bundle, proof-wrapper file paths are also accepted. Omit for --ixe + --ixes partition auditing."
]

end
