/-
  `ix addr-of <Lean.Name> [--ixe <path>]`: resolve a Lean.Name to its
  32-byte content address. Without `--ixe`, the lookup compiles the
  name's transitive closure from the compiled-in Lean env (via
  `IxVM.ClaimHarness.loadIxonEnv` → `lookupAddr`). With `--ixe`, the
  lookup reads the env from disk and dispatches `Ixon.Env.getAddr?`.

  Prints the resulting address hex on stdout (one line, no prefix), so
  the output can be piped into `ix claim check $(ix addr-of …)` etc.
-/
module
public import Cli
public import Std.Internal.UV.System
public import Ix.Address
public import Ix.Common
public import Ix.Environment
public import Ix.IxVM.ClaimHarness
public import Ix.Ixon
public import Ix.Meta

public section

namespace Ix.Cli.AddrOfCmd

private def parseName (arg : String) : Lean.Name :=
  arg.splitOn "." |>.foldl (init := .anonymous)
    fun acc s => match s.toNat? with
      | some n => Lean.Name.mkNum acc n
      | none   => Lean.Name.mkStr acc s

def runAddrOfCmd (p : Cli.Parsed) : IO UInt32 := do
  -- Suppress Rust-side `[compile_env]` scheduler noise; the only
  -- signal this command emits is the address on stdout.
  Std.Internal.UV.System.osSetenv "IX_QUIET" "1"
  let some nameArg := p.positionalArg? "name"
    | p.printError "error: must specify <Lean.Name>"; return 1
  let name := parseName (nameArg.as! String)
  let ixePath : Option String :=
    (p.flag? "ixe").map (·.as! String)
  match ixePath with
  | some path =>
    let bytes ← IO.FS.readBinFile path
    let ixonEnv ← match Ixon.rsDeEnv bytes with
      | .error e =>
        IO.eprintln s!"error: failed to deserialize {path}: {e}"; return 1
      | .ok env => pure env
    match ixonEnv.getAddr? (Ix.Name.fromLeanName name) with
    | none =>
      IO.eprintln s!"error: {name} not found in {path}"; return 1
    | some addr =>
      IO.println (toString addr); return 0
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

  ARGS:
    name : String; "Fully-qualified Lean.Name to resolve (e.g. `Nat.add_comm` or `Tests.Ix.Kernel.TutorialDefs.basicDef`)."
]

end
