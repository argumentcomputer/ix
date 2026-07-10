/-
  `ix name-of <64-hex-addr> --ixe <path>`: resolve a content address
  back to its Lean name(s) in an on-disk env.

  A single address can carry MANY names: structurally equivalent
  constants collapse to the same content address, and every such name
  is registered against it in the env's `named` table. All of them are
  printed, one per line.

  If the address is not directly named (e.g. an anonymized Muts
  block), scan the env for projection constants whose block field
  points at it and print those projections' names — any of them
  fast-repros the block via `ix check --ixe <path> <name>`.
-/
module
public import Cli
public import Std.Internal.UV.System
public import Ix.Address
public import Ix.Common
public import Ix.Environment
public import Ix.Ixon
public import Ix.Meta
public import Ix.Cli.NameResolve

public section

open Ix.Cli.NameResolve

namespace Ix.Cli.NameOfCmd

/-- Address → name(s). Direct hits come from filtering the env's
    `named` table (the `addrToName` reverse index keeps only one name
    per address, so it would silently drop structurally-equivalent
    aliases); the projection scan is the fallback for unnamed blocks. -/
def nameLookup (ixonEnv : Ixon.Env) (addr : Address) : IO UInt32 := do
  let mut found := 0
  for (n, named) in ixonEnv.named do
    if named.addr == addr then
      IO.println (toString (ixNameToLeanName n))
      found := found + 1
  if found > 0 then
    return 0
  IO.eprintln s!"{addr} is not a named constant; \
    scanning for projections into it..."
  for (caddr, lc) in ixonEnv.consts do
    let some c := lc.get? | continue
    let blk? := match c.info with
      | .iPrj p => some p.block
      | .cPrj p => some p.block
      | .rPrj p => some p.block
      | .dPrj p => some p.block
      | _ => none
    if blk? == some addr then
      let nm := match ixonEnv.getName? caddr with
        | some n => toString (ixNameToLeanName n)
        | none => s!"<unnamed {caddr}>"
      IO.println nm
      found := found + 1
  if found == 0 then
    IO.eprintln s!"error: no name or projection found for {addr}"
    return 1
  return 0

def runNameOfCmd (p : Cli.Parsed) : IO UInt32 := do
  -- Suppress Rust-side `[compile_env]` scheduler noise; the only
  -- signal this command emits is the name list on stdout.
  Std.Internal.UV.System.osSetenv "IX_QUIET" "1"
  let some addrArg := p.positionalArg? "addr"
    | p.printError "error: must specify a 64-char hex address"; return 1
  let argStr := addrArg.as! String
  let some addr := Address.fromString argStr
    | IO.eprintln s!"error: `{argStr}` is not a 64-char hex address"
      return 1
  let some path := (p.flag? "ixe").map (·.as! String)
    | IO.eprintln "error: name-of requires --ixe <path>"
      return 1
  let bytes ← IO.FS.readBinFile path
  let ixonEnv ← match Ixon.deEnvAnon bytes with
    | .error e =>
      IO.eprintln s!"error: failed to deserialize {path}: {e}"; return 1
    | .ok env => pure env
  nameLookup ixonEnv addr

end Ix.Cli.NameOfCmd

open Ix.Cli.NameOfCmd in
def nameOfCmd : Cli.Cmd := `[Cli|
  "name-of" VIA runNameOfCmd;
  "Resolve a content address back to its Lean name(s) in a `.ixe` env (may print several: structurally equivalent constants share an address)"

  FLAGS:
    "ixe" : String; "Path to a serialized `.ixe` env to resolve the address in (required)."

  ARGS:
    addr : String; "64-char hex content address to resolve. Prints every Lean.Name registered for it, one per line; for unnamed Muts blocks, prints the names of projection constants into the block instead."
]

end
