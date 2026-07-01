/-
  `ix name-of <hex> --ixe <path>`: reverse-lookup — given a 32-byte
  content address hex, print the fully-qualified Lean name of the
  named const stored under that address in the `.ixe` env. Prints
  nothing + exits 1 if no named const matches (the address might be
  an unnamed intermediate constant or a blob).
-/
module
public import Cli
public import Std.Internal.UV.System
public import Ix.Address
public import Ix.Common
public import Ix.Ixon
public import Ix.Meta
public import Ix.Cli.NameResolve

open Ix.Cli.NameResolve

public section

namespace Ix.Cli.NameOfCmd

def runNameOfCmd (p : Cli.Parsed) : IO UInt32 := do
  Std.Internal.UV.System.osSetenv "IX_QUIET" "1"
  let some hexArg := p.positionalArg? "hex"
    | p.printError "error: must specify <32-byte hex address>"; return 1
  let hexStr := hexArg.as! String
  let some target := Address.fromString hexStr
    | IO.eprintln s!"error: {hexStr} is not a valid 64-char hex address"; return 1
  let some ixePath := (p.flag? "ixe").map (·.as! String)
    | IO.eprintln "error: --ixe <path> is required"; return 1
  let bytes ← IO.FS.readBinFile ixePath
  let ixonEnv ← match Ixon.deEnvAnon bytes with
    | .error e =>
      IO.eprintln s!"error: failed to deserialize {ixePath}: {e}"; return 1
    | .ok env => pure env
  let hit :=
    ixonEnv.named.toArray.find? (fun (_, named) => named.addr == target)
  match hit with
  | some (ixName, _) =>
    IO.println (toString (ixNameToLeanName ixName))
    return 0
  | none =>
    IO.eprintln s!"error: no named const at {hexStr} in {ixePath} \
      (may be an unnamed intermediate or a blob)"
    return 1

end Ix.Cli.NameOfCmd

open Ix.Cli.NameOfCmd in
def nameOfCmd : Cli.Cmd := `[Cli|
  "name-of" VIA runNameOfCmd;
  "Reverse-lookup a Lean.Name from its content address in a `.ixe` env."

  FLAGS:
    "ixe" : String; "Path to a serialized `.ixe` env. Required."

  ARGS:
    hex : String; "32-byte content address as a 64-char hex string."
]

end
