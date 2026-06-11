/-
  `ix refs-of <Lean.Name> --ixe <path>`: print the direct constant
  references of a constant — its `Constant.refs` entries that resolve to
  constants in the env (literal blobs are skipped: they are pinned by
  content-addressing and are not well-typedness obligations).

  Prints a comma-separated list of 64-char hex addresses on stdout, the
  exact shape `ix tree canonical` expects, so a frontier assumption tree
  for a single constant is:

      ix tree canonical $(ix refs-of <name> --ixe env.ixe)
-/
module
public import Cli
public import Ix.Address
public import Ix.Common
public import Ix.Ixon

public section

namespace Ix.Cli.RefsOfCmd

def parseName (arg : String) : Lean.Name :=
  arg.splitOn "." |>.foldl (init := .anonymous)
    fun acc s => match s.toNat? with
      | some n => Lean.Name.mkNum acc n
      | none   => Lean.Name.mkStr acc s

def runRefsOfCmd (p : Cli.Parsed) : IO UInt32 := do
  let some nameArg := p.positionalArg? "name"
    | p.printError "error: must specify <name>"; return 1
  let name := parseName (nameArg.as! String)
  let some ixeFlag := p.flag? "ixe"
    | p.printError "error: --ixe is required"; return 1
  let path := ixeFlag.as! String
  let bytes ← IO.FS.readBinFile path
  let ixonEnv ← match Ixon.rsDeEnv bytes with
    | .error e =>
      IO.eprintln s!"error: failed to deserialize {path}: {e}"; return 1
    | .ok env => pure env
  let some addr := ixonEnv.getAddr? (Ix.Name.fromLeanName name)
    | IO.eprintln s!"error: {name} not found in {path}"; return 1
  let some c := ixonEnv.getConst? addr
    | IO.eprintln s!"error: constant for {name} missing from env"; return 1
  let mut seen : Std.HashSet String := {}
  let mut out : Array String := #[]
  for r in c.refs do
    if (ixonEnv.getConst? r).isSome then
      let s := toString r
      if !seen.contains s then
        seen := seen.insert s
        out := out.push s
  IO.println (String.intercalate "," out.toList)
  return 0

end Ix.Cli.RefsOfCmd

open Ix.Cli.RefsOfCmd in
def refsOfCmd : Cli.Cmd := `[Cli|
  "refs-of" VIA runRefsOfCmd;
  "Print a constant's direct constant references (comma-separated hex), the leaf list for a frontier assumption tree"

  FLAGS:
    "ixe" : String; "Path to a serialized `.ixe` env (required)."

  ARGS:
    name : String; "Fully-qualified Lean.Name (e.g. `Nat.add_comm`)."
]

end
