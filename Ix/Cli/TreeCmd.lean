/-
  `ix tree <subcommand>`: build and persist `Ix.AssumptionTree`
  values into the content-addressed store. Trees are stored under
  their merkle root (NOT under `blake3(bytes)`), so callers that
  reference a tree by `root` in a claim's `--asm` field can resolve
  the tree blob with a straight `Store.read root` lookup.

  MVP: only `ix tree canonical <addrs>` (sorted+padded merkle tree
  over a leaf set).
-/
module
public import Cli
public import Ix.Address
public import Ix.AssumptionTree
public import Ix.Common
public import Ix.IxVM.ClaimHarness
public import Ix.Ixon
public import Ix.Store

public section

open System (FilePath)

namespace Ix.Cli.TreeCmd

private def addrOfHex! (label : String) (s : String) : IO Address := do
  match Address.fromString s with
  | some a => pure a
  | none =>
    throw <| IO.userError
      s!"error: {label}: expected 64-char hex (32-byte address), got {s.length}-char {s}"

/-- Parse a comma-separated list of hex addresses. Whitespace ignored;
    empty entries dropped. -/
private def parseAddrList (raw : String) : IO (Array Address) := do
  let chunks := (raw.splitOn ",").map (fun s =>
    s.trimAscii.toString) |>.filter (fun s => !s.isEmpty)
  let mut acc : Array Address := #[]
  for c in chunks do
    acc := acc.push (← addrOfHex! "leaf" c)
  pure acc

def runTreeCanonical (p : Cli.Parsed) : IO UInt32 := do
  let some leavesArg := p.positionalArg? "leaves"
    | p.printError "error: must specify <comma-separated leaf hex>"; return 1
  let leaves ← parseAddrList (leavesArg.as! String)
  if leaves.isEmpty then
    IO.eprintln "error: empty leaf set; cannot build a tree"
    return 1
  let some tree := Ix.AssumptionTree.canonical leaves
    | IO.eprintln "error: canonical tree build returned none (post-dedup empty)"
      return 1
  let bytes := Ix.AssumptionTree.ser tree
  StoreIO.toIO (Store.writeAt tree.root bytes)
  IO.println (toString tree.root)
  return 0

/-- Build the canonical merkle tree over every `Ixon.Env` constant
    address and persist it at `~/.ix/store/<root>`. Same shape as
    `IxVM.ClaimHarness.envCanonicalTree`; the root is what
    `Claim.checkEnv root _` expects. -/
def runTreeEnv (p : Cli.Parsed) : IO UInt32 := do
  let some ixeArg := p.positionalArg? "ixe"
    | p.printError "error: must specify <ixe-path>"; return 1
  let ixePath := ixeArg.as! String
  let bytes ← IO.FS.readBinFile ixePath
  let ixonEnv ← match Ixon.rsDeEnv bytes with
    | .error e =>
      IO.eprintln s!"error: failed to deserialize {ixePath}: {e}"; return 1
    | .ok env => pure env
  let some tree := IxVM.ClaimHarness.envCanonicalTree ixonEnv
    | IO.eprintln s!"error: {ixePath} has no consts; cannot build env tree"
      return 1
  let tbytes := Ix.AssumptionTree.ser tree
  StoreIO.toIO (Store.writeAt tree.root tbytes)
  IO.println (toString tree.root)
  return 0

def runTree (p : Cli.Parsed) : IO UInt32 := do
  p.printHelp
  return 0

end Ix.Cli.TreeCmd

open Ix.Cli.TreeCmd in
def treeCanonicalCmd : Cli.Cmd := `[Cli|
  canonical VIA runTreeCanonical;
  "Build the canonical sorted+padded merkle tree over the listed leaf addresses and persist it at `~/.ix/store/<merkle-root-hex>`. Prints the merkle root hex on stdout — that root is what `--asm` arguments on claims reference."

  ARGS:
    leaves : String; "Comma-separated 64-char hex leaf addresses (e.g. `<addr1>,<addr2>,...`)."
]

open Ix.Cli.TreeCmd in
def treeEnvCmd : Cli.Cmd := `[Cli|
  env VIA runTreeEnv;
  "Compute the canonical merkle tree over every constant in a `.ixe` and persist it at `~/.ix/store/<env-root-hex>`. Prints the env root hex — that root is what `ix claim check-env <root>` expects."

  ARGS:
    ixe : String; "Path to a serialized Ixon env (`.ixe`)."
]

open Ix.Cli.TreeCmd in
def treeCmd : Cli.Cmd := `[Cli|
  tree VIA runTree;
  "Build and persist `Ix.AssumptionTree` values to `~/.ix/store/`"

  SUBCOMMANDS:
    treeCanonicalCmd;
    treeEnvCmd
]

end
