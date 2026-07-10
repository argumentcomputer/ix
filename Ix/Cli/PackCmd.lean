/-
  `ix pack <env.ixe> <name>`: prune a serialized env to the self-contained
  bundle pinning one named constant, and write it as a standalone `.ixe`.

  A bundle is an `.ixe` whose `main` points at a distinguished constant;
  because a constant's address is a merkle root over its whole dependency
  DAG, `main`'s 32 bytes alone pin the value — the bundle is the
  data-availability artifact that ships the bytes. `--assume` declares
  trust-boundary cut-points: reached cut-points are recorded in the
  bundle's `assumptions` instead of being carried (thin bundles).

  The heavy lifting is `Env::prune_to_closure` (3-edge value closure of
  `main`, display metadata carried to fixpoint) followed by
  `Env::validate_closed` — the same check a receiver runs — so a written
  bundle is closed by construction.

  Different from `ix shard extract`: extract produces a general sub-env
  for the kernel-check pipeline (no `main`, no `assumptions`, anon-work
  block closure); pack produces a verified bundle with a root and an
  explicit trust boundary.
-/
module
public import Cli
public import Ix.Ixon
public import Ix.Cli.ConstsFile

public section

namespace Ix.Cli.PackCmd

def runPackCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a source .ixe file"
      return 1
  let envPath := pathArg.as! String
  let some nameArg := p.positionalArg? "name"
    | p.printError "error: must specify <name> of the bundle root constant"
      return 1
  let mainName := nameArg.as! String
  let assume ← Ix.Cli.ConstsFile.gather p "assume" "assume-file"
  let outPath : String :=
    match p.flag? "out" with
    | some flag => flag.as! String
    | none => s!"{mainName}.ixe"
  let anon := p.hasFlag "anon"
  let verbose := p.hasFlag "verbose"
  try
    Ixon.rsPackEnv envPath mainName assume outPath anon verbose
    let mode := if anon then " [anon]" else ""
    IO.println s!"[pack] wrote {outPath} (main {mainName}, \
      {assume.size} assumption cut(s) declared){mode}"
    return (0 : UInt32)
  catch e =>
    IO.eprintln s!"error: {e.toString}"
    return (1 : UInt32)

end Ix.Cli.PackCmd

open Ix.Cli.PackCmd in
def packCmd : Cli.Cmd := `[Cli|
  pack VIA runPackCmd;
  "Prune a `.ixe` env to the self-contained bundle pinning one constant (sets `main`; validated closed)"

  FLAGS:
    anon;                   "Pack only anonymous structure — no names or metadata (§4/§5 empty; §3 hints still carried). The minimal artifact a receiver needs to typecheck/evaluate the pinned value."
    assume        : String; "Comma-separated cut-point constants — displayed names or 64-hex addresses. Reached cut-points are recorded in the bundle's `assumptions` instead of carried (thin bundle)."
    "assume-file" : String; "Additionally read cut-points from a file (one per line; `#` comments and blank lines ignored). Unions with --assume."
    out           : String; "Output `.ixe` path. Defaults to `<name>.ixe` (e.g. `Nat.add.ixe`)."
    verbose;                "Print pack details (source stats, kept counts, bytes written) to stderr."

  ARGS:
    path : String; "Path to the source `.ixe` (e.g. from `ix compile`)."
    name : String; "Displayed name of the bundle root constant (e.g. `Nat.add`)."
]

end
