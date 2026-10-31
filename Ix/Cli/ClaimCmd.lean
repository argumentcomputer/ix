/-
  `ix claim <subcommand>`: build an `Ix.Claim` value and persist its
  canonical serialization to the content-addressed store at
  `~/.ix/store/`. Each subcommand prints the resulting blake3 hex on
  stdout — that hex IS the public input the kernel's `verify_claim`
  entrypoint will compare against.

  Wired variants: `check`, `check-env`, `contains`, `eval`, `catalog`,
  `binding`.

  TODO(reveal): wire `ix claim reveal <comm-hex> --info <json-file>`
  once a JSON schema for `Ix.RevealConstantInfo` is settled. The
  variant is rich (per-`ConstantInfo`-arm option fields:
  Defn/Axio/Recr/Quot/IPrj/CPrj/RPrj/DPrj/Muts), so encoding it as
  CLI flags balloons fast — JSON is the cleanest input shape.
-/
module
public import Cli
public import Ix.Common
public import Ix.Claim
public import Ix.ClaimContext
public import Ix.Store
public import Ix.Cli.CatalogCmd
public import Ix.Aggr.Host

public section

open System (FilePath)

namespace Ix.Cli.ClaimCmd

/-- Parse a 64-character hex string into an `Address` or fail with a
    descriptive `IO` error. -/
private def addrOfHex! (label : String) (s : String) : IO Address := do
  match Address.fromString s with
  | some a => pure a
  | none =>
    throw <| IO.userError
      s!"error: {label}: expected 64-char hex (32-byte address), got {s.length}-char {s}"

/-- Persist `claim` to the content-addressed store. Returns the
    digest; serialized bytes blake3 = the claim digest used by
    `verify_claim`. -/
private def persistClaim (claim : Ix.Claim) : IO Address := do
  let bytes := Ix.Claim.ser claim
  StoreIO.toIO (Store.write bytes)

/-- The context a typing claim is relative to: the role binding named by
    `--binding`, or else the default role table's, with this specification
    set and no axiom beyond the standard three. -/
private def contextOf (p : Cli.Parsed) : IO Ix.ClaimContext := do
  match p.flag? "binding" with
  | some flag =>
    let binding ← addrOfHex! "binding" (flag.as! String)
    IO.ofExcept (Ix.ClaimContext.ofBinding binding)
  | none => IO.ofExcept Ix.ClaimContext.ofDefaultTable

/-- `contextOf`, assuming the binding meets the specifications when
    `--assume-binding` is set (`check` and `check-env` only). -/
private def assumableContextOf (p : Cli.Parsed) : IO Ix.ClaimContext := do
  let ctx ← contextOf p
  return { ctx with bindingAssumed := p.hasFlag "assume-binding" }

/-! ## `ix claim check` -/

def runClaimCheck (p : Cli.Parsed) : IO UInt32 := do
  let some addrArg := p.positionalArg? "addr"
    | p.printError "error: must specify <addr-hex>"; return 1
  let const ← addrOfHex! "addr" (addrArg.as! String)
  let asm ← match p.flag? "asm" with
    | none => pure none
    | some flag => do
      let root ← addrOfHex! "asm" (flag.as! String)
      pure (some root)
  let claim := Ix.Claim.check (← assumableContextOf p) const asm
  let digest ← persistClaim claim
  IO.println (toString digest)
  return 0

def claimCheckCmd : Cli.Cmd := `[Cli|
  check VIA runClaimCheck;
  "Build and persist a `Check` claim: the constant at <addr-hex> is well-typed (optionally modulo an assumption tree)."

  FLAGS:
    asm : String; "32-byte hex address of an assumption-tree merkle root. The tree must already live in `~/.ix/store/` (build it with `ix tree canonical`). When set, the claim asserts well-typedness modulo the assumed leaves."
    binding : String; "32-byte hex binding hash of the role table the claim reads primitives through (default: the default role table of the compiled Init)."
    "assume-binding"; "Assume the role binding meets the specifications instead of validating its roles in this claim's proof (validator erased-lean-v2-assumed). The claim then holds if the `binding` claim for its binding does, which aggregation discharges once."

  ARGS:
    addr : String; "32-byte hex address of the constant being claimed well-typed."
]

/-! ## `ix claim check-env` -/

def runClaimCheckEnv (p : Cli.Parsed) : IO UInt32 := do
  let some rootArg := p.positionalArg? "root"
    | p.printError "error: must specify <env-root-hex>"; return 1
  let root ← addrOfHex! "root" (rootArg.as! String)
  let asm ← match p.flag? "asm" with
    | none => pure none
    | some flag => do
      let r ← addrOfHex! "asm" (flag.as! String)
      pure (some r)
  let claim := Ix.Claim.checkEnv (← assumableContextOf p) root asm
  let digest ← persistClaim claim
  IO.println (toString digest)
  return 0

def claimCheckEnvCmd : Cli.Cmd := `[Cli|
  "check-env" VIA runClaimCheckEnv;
  "Build and persist a `CheckEnv` claim: every constant in the env merkle-rooted at <env-root-hex> is well-typed (optionally modulo an assumption tree). The env tree itself must already live in the store (`ix tree env <ixe>`); same goes for the asm tree if set."

  FLAGS:
    asm : String; "32-byte hex address of an assumption-tree merkle root (typically the env's axiom leaves). The tree must already live in `~/.ix/store/`."
    binding : String; "32-byte hex binding hash of the role table the claim reads primitives through (default: the default role table of the compiled Init)."
    "assume-binding"; "Assume the role binding meets the specifications instead of validating its roles in this claim's proof (validator erased-lean-v2-assumed). The claim then holds if the `binding` claim for its binding does, which aggregation discharges once."

  ARGS:
    root : String; "32-byte hex address of the env's canonical merkle root (build with `ix tree env <ixe>`)."
]

/-! ## `ix claim contains` -/

def runClaimContains (p : Cli.Parsed) : IO UInt32 := do
  let some treeArg := p.positionalArg? "tree"
    | p.printError "error: must specify <tree-root-hex>"; return 1
  let some targetArg := p.positionalArg? "target"
    | p.printError "error: must specify <target-hex>"; return 1
  let tree ← addrOfHex! "tree" (treeArg.as! String)
  let target ← addrOfHex! "target" (targetArg.as! String)
  let claim := Ix.Claim.contains tree target
  let digest ← persistClaim claim
  IO.println (toString digest)
  return 0

def claimContainsCmd : Cli.Cmd := `[Cli|
  contains VIA runClaimContains;
  "Build and persist a `Contains` claim: <target-hex> is a leaf in the merkle tree rooted at <tree-root-hex>. The tree itself must already live in `~/.ix/store/` (build with `ix tree canonical`)."

  ARGS:
    tree   : String; "32-byte hex address of the merkle tree's root."
    target : String; "32-byte hex address claimed to be present as a leaf in the tree."
]

-- TODO(reveal): `ix claim reveal <comm-hex> --info <json-file>` —
-- build/persist a `Reveal` claim. Blocked on a JSON schema for
-- `Ix.RevealConstantInfo`. Once that lands, the impl mirrors
-- `runClaimCheck`: parse hex + decode JSON → `Ix.Claim.reveal …`
-- → `persistClaim`.

/-! ## `ix claim eval` -/

def runClaimEval (p : Cli.Parsed) : IO UInt32 := do
  let some inputArg := p.positionalArg? "input"
    | p.printError "error: must specify <input-hex>"; return 1
  let some outputArg := p.positionalArg? "output"
    | p.printError "error: must specify <output-hex>"; return 1
  let input ← addrOfHex! "input" (inputArg.as! String)
  let output ← addrOfHex! "output" (outputArg.as! String)
  let asm ← match p.flag? "asm" with
    | none => pure none
    | some flag => do
      let r ← addrOfHex! "asm" (flag.as! String)
      pure (some r)
  let claim := Ix.Claim.eval (← contextOf p) input output asm
  let digest ← persistClaim claim
  IO.println (toString digest)
  return 0

def claimEvalCmd : Cli.Cmd := `[Cli|
  eval VIA runClaimEval;
  "Build and persist an Eval claim: typecheck the input and normalize its body to a safe output definition with the same type, optionally assuming input dependencies are well-typed."

  FLAGS:
    asm : String; "32-byte hex address of an assumption-tree merkle root. The tree must already live in `~/.ix/store/`."
    binding : String; "32-byte hex binding hash of the role table the claim reads primitives through (default: the default role table of the compiled Init)."

  ARGS:
    input  : String; "32-byte hex address of the input constant."
    output : String; "32-byte hex address of the output constant."
]

/-! ## `ix claim catalog` -/

def runClaimCatalog (p : Cli.Parsed) : IO UInt32 := do
  let args : Array String := p.variableArgsAs! String
  if args.isEmpty then
    p.printError "error: must specify <member-claim>..."
    return 1
  let mut members : Array Ix.Claim := #[]
  for hex in args do
    let digest ← addrOfHex! "member claim" hex
    let bytes ← StoreIO.toIO (Store.read digest)
    match Ix.Claim.de bytes with
    | .ok claim => members := members.push claim
    | .error e => IO.eprintln s!"error: {hex}: not a claim: {e}"; return 1
  let catalog ← match Aggr.CatalogTrees.ofMembers members with
    | .ok catalog => pure catalog
    | .error e => IO.eprintln s!"error: {e}"; return 1
  StoreIO.toIO (Store.writeAt catalog.members.root (Ix.AssumptionTree.ser catalog.members))
  let digest ← persistClaim catalog.claim
  IO.println (toString digest)
  return 0

def claimCatalogCmd : Cli.Cmd := `[Cli|
  catalog VIA runClaimCatalog;
  "Build and persist a `Catalog` claim over persisted member claims: every one of them holds. Each member is an unconditional `CheckEnv` claim that validates its binding or names a literal class, so members may come from different Lean toolchains. The members tree is persisted under its root. A catalog claim is proven by aggregating its members (`ix aggregate --ixc`)."

  ARGS:
    ...members : String; "32-byte hex digests of persisted member claims in `~/.ix/store/`."
]

/-! ## `ix claim binding` -/

def runClaimBinding (p : Cli.Parsed) : IO UInt32 := do
  let ctx ← contextOf p
  let digest ← persistClaim (Ix.Claim.binding ctx.spec ctx.binding)
  IO.println (toString digest)
  return 0

def claimBindingCmd : Cli.Cmd := `[Cli|
  binding VIA runClaimBinding;
  "Build and persist a `Binding` claim: the role table binds every role and each bound constant meets its specification in this specification set. Prove it once (`ix prove-binding <ixe>`) to discharge the claims that assume their binding (`--assume-binding`; `ix aggregate --binding-proof`, `ix prove --lanes --binding-proof`)."

  FLAGS:
    binding : String; "32-byte hex binding hash of the role table (default: the default role table of the compiled Init)."
]

/-! ## Top-level `ix claim` -/

def runClaim (p : Cli.Parsed) : IO UInt32 := do
  p.printHelp
  return 0

end Ix.Cli.ClaimCmd

open Ix.Cli.ClaimCmd in
def claimCmd : Cli.Cmd := `[Cli|
  claim VIA runClaim;
  "Build and persist an `Ix.Claim` to `~/.ix/store/`"

  SUBCOMMANDS:
    claimCheckCmd;
    claimCheckEnvCmd;
    claimContainsCmd;
    claimEvalCmd;
    claimCatalogCmd;
    claimBindingCmd
]

end
