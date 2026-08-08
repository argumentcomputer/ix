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

/-- Batch resolution: one env decode + one pass building both reverse
    indexes (address → names, block → projection names), then O(1) per
    address — the single-address path's per-call full scans cost ~90 s
    each at FLT scale, which forbids inventories of tens of thousands.
    Each address resolves to `<name>[,<name>…]` (`prj:` prefix for
    projection fallbacks into unnamed blocks, `<unresolved>` for
    misses). -/
def resolveAddrs (ixonEnv : Ixon.Env) (addrs : Array Address) :
    Array (Address × String) := Id.run do
  let mut byAddr : Std.HashMap Address (Array String) := {}
  for (n, named) in ixonEnv.named do
    byAddr := byAddr.insert named.addr
      ((byAddr.getD named.addr #[]).push (toString (ixNameToLeanName n)))
  let mut byBlock : Std.HashMap Address (Array String) := {}
  for (caddr, lc) in ixonEnv.consts do
    let some c := lc.get? | continue
    let blk? := match c.info with
      | .iPrj p => some p.block
      | .cPrj p => some p.block
      | .rPrj p => some p.block
      | .dPrj p => some p.block
      | _ => none
    if let some blk := blk? then
      let nm := match ixonEnv.getName? caddr with
        | some n => toString (ixNameToLeanName n)
        | none => s!"<unnamed {caddr}>"
      byBlock := byBlock.insert blk ((byBlock.getD blk #[]).push nm)
  let mut out : Array (Address × String) := #[]
  for a in addrs do
    let disp := match byAddr.get? a with
      | some ns => String.intercalate "," ns.toList
      | none => match byBlock.get? a with
        | some ns => s!"prj:{String.intercalate "," ns.toList}"
        | none => "<unresolved>"
    out := out.push (a, disp)
  return out

def batchLookup (ixonEnv : Ixon.Env) (addrs : Array Address) : IO UInt32 := do
  let resolved := resolveAddrs ixonEnv addrs
  let mut missing := 0
  for (a, disp) in resolved do
    IO.println s!"{a} {disp}"
    if disp == "<unresolved>" then
      missing := missing + 1
  if missing > 0 then
    IO.eprintln s!"[name-of] {missing} address(es) unresolved"
  return 0

def runNameOfCmd (p : Cli.Parsed) : IO UInt32 := do
  let some path := (p.flag? "ixe").map (·.as! String)
    | IO.eprintln "error: name-of requires --ixe <path>"
      return 1
  let batchFile := (p.flag? "addrs-file").map (·.as! String)
  let addrArgs := p.variableArgsAs! String
  if batchFile.isNone && addrArgs.isEmpty then
    p.printError "error: pass a 64-char hex address or --addrs-file"
    return 1
  let bytes ← IO.FS.readBinFile path
  let ixonEnv ← match Ixon.deEnvAnon bytes with
    | .error e =>
      IO.eprintln s!"error: failed to deserialize {path}: {e}"; return 1
    | .ok env => pure env
  match batchFile with
  | some file =>
    let mut addrs : Array Address := #[]
    for line in (← IO.FS.readFile file).splitOn "\n" do
      let line := line.trimAscii.toString
      if line.isEmpty || line.startsWith "#" then
        continue
      let some a := Address.fromString line
        | IO.eprintln s!"error: `{line}` is not a 64-char hex address"
          return 1
      addrs := addrs.push a
    batchLookup ixonEnv addrs
  | none =>
    let argStr := addrArgs[0]!
    let some addr := Address.fromString argStr
      | IO.eprintln s!"error: `{argStr}` is not a 64-char hex address"
        return 1
    nameLookup ixonEnv addr

end Ix.Cli.NameOfCmd

open Ix.Cli.NameOfCmd in
def nameOfCmd : Cli.Cmd := `[Cli|
  "name-of" VIA runNameOfCmd;
  "Resolve a content address back to its Lean name(s) in a `.ixe` env (may print several: structurally equivalent constants share an address)"

  FLAGS:
    "ixe"        : String; "Path to a serialized `.ixe` env to resolve the address in (required)."
    "addrs-file" : String; "Batch mode: file of 64-char hex addresses (one per line; `#` comments and blanks ignored). One env decode resolves them all — output `<addr> <name>[,…]` per line, `prj:` prefix for projection fallbacks."

  ARGS:
    ...addr : String; "64-char hex content address to resolve (omit when using --addrs-file). Prints every Lean.Name registered for it, one per line; for unnamed Muts blocks, prints the names of projection constants into the block instead."
]

end
