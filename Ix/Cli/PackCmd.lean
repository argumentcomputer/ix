/-
  `ix pack <env.ixe> <name>`: prune a serialized env to the self-contained
  bundle pinning one named constant, and write it as a standalone `.ixe`.

  A bundle is an `.ixe` whose `main` points at a distinguished constant;
  its constant address pins the explicit value dependency DAG. A bound
  artifact also carries its exact role binding and the reader/evidence support
  needed to interpret it. `--assume` declares
  trust-boundary cut-points: reached cut-points are recorded in the
  bundle's `assumptions` instead of being carried (thin bundles).

  The bundle carries the root's transitive reference closure and, when bound,
  its binding's members/proofs and required reader support, never its
  compilation unit: a bundle carries what is needed to check or
  evaluate the root, and units exist for compilation parallelism over the
  DAG (owner, 2026-10-07). The closure is computed by Rust by address
  (`Env::prune_to_closure`, through `Ixon.rsPackEnv`: the 3-edge value
  closure of `main`, display metadata carried to fixpoint) followed by
  `Env::validate_closed`. Bound pruning also checks support availability and
  refuses assumption cuts through mandatory support. Neither packing nor
  value-closure checking is semantic role/proof admission. The `pack-units` runner
  (`Tests.Ix.Compile.PackUnits`) checks that a root's bundle omits a unit
  member the root does not reference.

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
  "Pack one constant's value closure and bound checker support into a `.ixe` bundle"

  FLAGS:
    anon;                   "Pack anonymous structure, binding and checker support, without named/original metadata; anonymous hints remain."
    assume        : String; "Comma-separated ordinary cut-points — displayed names or 64-hex addresses. Reached cuts become assumptions; mandatory bound reader/evidence support cannot be cut."
    "assume-file" : String; "Additionally read cut-points from a file (one per line; `#` comments and blank lines ignored). Unions with --assume."
    out           : String; "Output `.ixe` path. Defaults to `<name>.ixe` (e.g. `Nat.add.ixe`)."
    verbose;                "Print pack details (source stats, kept counts, bytes written) to stderr."

  ARGS:
    path : String; "Path to the source `.ixe` (e.g. from `ix compile`)."
    name : String; "Displayed name of the bundle root constant (e.g. `Nat.add`)."
]

end
