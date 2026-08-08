/-
  `ix addr-of <Lean.Name> [--ixe <path>] [--ixes <manifest>]`: resolve a
  Lean.Name to its 32-byte content address. Without `--ixe`, the lookup
  compiles the name's transitive closure from the compiled-in Lean env
  (via `IxVM.ClaimHarness.loadIxonEnv` → `lookupAddr`). With `--ixe`, the
  lookup reads the env from disk and dispatches `Ixon.Env.getAddr?`.

  Prints the resulting address hex on stdout (one line, no prefix), so
  the output can be piped into `ix claim check $(ix addr-of …)` etc.
  With `--ixes` (requires `--ixe`), a second line reports which shard of
  the manifest's partition owns the name's check-schedule block — the
  shard whose prove type-checks this constant.
-/
module
public import Cli
public import Ix.Address
public import Ix.Common
public import Ix.Environment
public import Ix.IxVM.ClaimHarness
public import Ix.Ixon
public import Ix.Meta
public import Ix.Cli.CheckCmd
public import Ix.Cli.NameResolve

public section

open Ix.Cli.NameResolve

namespace Ix.Cli.AddrOfCmd

def runAddrOfCmd (p : Cli.Parsed) : IO UInt32 := do
  let some nameArg := p.positionalArg? "name"
    | p.printError "error: must specify <Lean.Name>"; return 1
  let argStr := nameArg.as! String
  let name := parseName argStr
  let ixePath : Option String :=
    (p.flag? "ixe").map (·.as! String)
  match ixePath with
  | some path =>
    let bytes ← IO.FS.readBinFile path
    let ixonEnv ← match Ixon.rsDeEnv bytes with
      | .error e =>
        IO.eprintln s!"error: failed to deserialize {path}: {e}"; return 1
      | .ok env => pure env
    match resolveIxeAddr ixonEnv argStr with
    | none =>
      IO.eprintln s!"error: {name} not found in {path}"; return 1
    | some addr =>
      IO.println (toString addr)
      if let some manifestPath := (p.flag? "ixes").map (·.as! String) then
        -- Owning-shard lookup: the constant's check-schedule block (a
        -- projection collapses to its SCC/Muts wrapper), searched in the
        -- manifest's owned-block lists.
        let c? : Option Ixon.Constant := Id.run do
          for (a, lc) in ixonEnv.consts do
            if a == addr then return lc.get?
          return none
        let some c := c?
          | IO.eprintln s!"error: {addr} has no parseable constant in {path}"
            return 1
        let block := Ix.Cli.CheckCmd.blockAddrOf addr c
        match Ix.Cli.CheckCmd.parseIxesShards
            (← IO.FS.readBinFile manifestPath) with
        | .error e =>
          IO.eprintln s!"error: {manifestPath}: {e}"; return 1
        | .ok shards =>
          match (shards.mapIdx (fun k s => (s, k))).find?
              (fun (s, _) => s.blocks.contains block) with
          | some (s, k) =>
            IO.println s!"block {block} → shard {k} \
              ({s.blocks.size} blocks, cost {s.cost})"
          | none =>
            IO.println s!"block {block} → no owning shard \
              (excluded from the partition)"
      return 0
  | none =>
    let env ← get_env!
    if !env.constants.contains name then
      IO.eprintln s!"error: {name} not found in compiled-in Lean env"
      return 1
    let ixonEnv ← IxVM.ClaimHarness.loadIxonEnv name env
    let addr ← IxVM.ClaimHarness.lookupAddr ixonEnv name
    IO.println (toString addr)
    return 0

end Ix.Cli.AddrOfCmd

open Ix.Cli.AddrOfCmd in
def addrOfCmd : Cli.Cmd := `[Cli|
  "addr-of" VIA runAddrOfCmd;
  "Resolve a Lean.Name to its content address (in a `.ixe` or in the compiled-in env)"

  FLAGS:
    "ixe" : String; "Path to a serialized `.ixe` env to resolve the name in. Without this, the name is looked up in the compiled-in Lean env (via `loadIxonEnv` → `lookupAddr`)."
    "ixes" : String; "Path to a `.ixes` shard manifest (requires --ixe): also report which shard owns the name's check-schedule block — the shard whose prove type-checks this constant."

  ARGS:
    name : String; "Fully-qualified Lean.Name to resolve (e.g. `Nat.add_comm` or `Tests.Ix.Kernel.TutorialDefs.basicDef`)."
]

end
