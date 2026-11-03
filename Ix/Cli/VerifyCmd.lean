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

public section

namespace Ix.Cli.VerifyCmd

def runVerifyCmd (p : Cli.Parsed) : IO UInt32 := do
  let _ ← FormalAiur.selected p
  if p.hasFlag "aggregate" then
    if let some ixc := (p.flag? "ixc").map (·.as! String) then
      return ← CatalogAggregate.verifyCatalog p ixc
    return ← FormalAggregate.verify p
  FormalAiur.verify p

end Ix.Cli.VerifyCmd

open Ix.Cli.VerifyCmd in
def verifyCmd : Cli.Cmd := `[Cli|
  verify VIA runVerifyCmd;
  "Verify STARK proof(s) against their bundled claims, or a `.ixes` shard partition"

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
    "distributed";    "Bind one default-backend distributed proof to the whole environment. Requires --ixe and --ixes; the manifest must cover the environment exactly."
    "structural-above" : Nat; "For --aggregate + --ixes, reproduce structural joins above N subject leaves (default 4096; must match proving)."
    "record";         "With --ixe + --ixes and proof(s): after a proof binds to its shard and verifies, record it in the shard-proof index (`~/.ix/cache/shard-proofs/<claim-digest>` → address) so `ix prove --skip-proven` and `ix shard refine` reuse it."

  ARGS:
    ...proofs : String; "32-byte hex address(es) of persisted `Ixon.Proof` wrappers in `~/.ix/store/`. Omit when using --ixe + --ixes."
]

end
