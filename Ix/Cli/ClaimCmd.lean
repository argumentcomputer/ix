/-
  `ix claim <subcommand>`: build an `Ix.Claim` value and persist its
  canonical serialization to the content-addressed store at
  `~/.ix/store/`. Each subcommand prints the resulting blake3 hex on
  stdout — that hex IS the public input the kernel's `verify_claim`
  entrypoint will compare against.

  Wired variants: `check`, `check-env`, `contains`, `eval`.

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
public import Ix.Store

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
  let claim := Ix.Claim.check const asm
  let digest ← persistClaim claim
  IO.println (toString digest)
  return 0

def claimCheckCmd : Cli.Cmd := `[Cli|
  check VIA runClaimCheck;
  "Build and persist a `Check` claim: the constant at <addr-hex> is well-typed (optionally modulo an assumption tree)."

  FLAGS:
    asm : String; "32-byte hex address of an assumption-tree merkle root. The tree must already live in `~/.ix/store/` (build it with `ix tree canonical`). When set, the claim asserts well-typedness modulo the assumed leaves."

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
  let claim := Ix.Claim.checkEnv root asm
  let digest ← persistClaim claim
  IO.println (toString digest)
  return 0

def claimCheckEnvCmd : Cli.Cmd := `[Cli|
  "check-env" VIA runClaimCheckEnv;
  "Build and persist a `CheckEnv` claim: every constant in the env merkle-rooted at <env-root-hex> is well-typed (optionally modulo an assumption tree). The env tree itself must already live in the store (`ix tree env <ixe>`); same goes for the asm tree if set."

  FLAGS:
    asm : String; "32-byte hex address of an assumption-tree merkle root (typically the env's axiom leaves). The tree must already live in `~/.ix/store/`."

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
  let claim := Ix.Claim.eval input output asm
  let digest ← persistClaim claim
  IO.println (toString digest)
  return 0

def claimEvalCmd : Cli.Cmd := `[Cli|
  eval VIA runClaimEval;
  "Build and persist an `Eval` claim: <input-hex> evaluates to <output-hex> (optionally modulo an assumption tree). NOTE: the IxVM `verify_claim` `run_eval` arm is currently a placeholder (`assert_eq!(0, 1)`); proving an Eval claim will fail at execution time until the kernel implements eval semantics."

  FLAGS:
    asm : String; "32-byte hex address of an assumption-tree merkle root. The tree must already live in `~/.ix/store/`."

  ARGS:
    input  : String; "32-byte hex address of the input constant."
    output : String; "32-byte hex address of the output constant."
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
    claimEvalCmd
]

end
