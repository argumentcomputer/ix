/-
  `ix pack <env.ixe> <name>`: prune a serialized env to the self-contained
  bundle pinning one named constant, and write it as a standalone `.ixe`.

  A bundle is an `.ixe` whose `main` points at a distinguished constant;
  because a constant's address is a merkle root over its whole dependency
  DAG, `main`'s 32 bytes alone pin the value — the bundle is the
  data-availability artifact that ships the bytes. `--assume` declares
  trust-boundary cut-points: reached cut-points are recorded in the
  bundle's `assumptions` instead of being carried (thin bundles); a declared
  cut point the walk does not reach is skipped.

  The bundle is the root's transitive reference closure, including the
  compiler-introduced constants it references (Pass 3's `_ix` constants,
  `PProd`, …), and never its compilation unit: a bundle carries only what is
  needed to check or evaluate the root, and units exist for compilation
  parallelism over the DAG (owner, 2026-10-07). The closure is computed by
  Rust by address (`Env::prune_to_closure`, through `Ixon.rsPackEnv`: the
  3-edge value closure of `main`, display metadata carried to fixpoint)
  followed by `Env::validate_closed` — the same check a receiver runs — so a
  written bundle is closed by construction. Lean's implementation of the
  same closure is the test oracle (`Tests.Ix.Compile.PackParity.packOracle`,
  byte for byte, `pack-units` and `pass3-rust-parity`).

  History: from M1-h to M6R slice 6 the bundle carried the whole logical
  unit of every block it reached (`packWholeUnits`, one Rust pack per
  missing member merged in Lean; slice 5's `--rust-units`, one Rust prune;
  `--no-units` kept the value closure). Slice 6 (2026-10-07) removed the
  completion, its flags and the compiled-environment unit view it read.

  Different from `ix shard extract`: extract produces a general sub-env
  for the kernel-check pipeline (no `main`, no `assumptions`, anon-work
  block closure); pack produces a verified bundle with a root and an
  explicit trust boundary.
-/
module
public import Cli
public import Ix.Ixon
public import Ix.Cli.ConstsFile
public import Ix.Common

public section

namespace Ix.Cli.PackCmd

def ixToLeanName : Ix.Name → Lean.Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (ixToLeanName p) s
  | .num p i _ => .num (ixToLeanName p) i

def readIxe (path : String) : IO Ixon.Env := do
  match Ixon.rsDeEnv (← IO.FS.readBinFile path) with
  | .ok e => pure e
  | .error e => throw (IO.userError s!"pack: cannot read {path}: {e}")

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
  "Prune a `.ixe` env to the self-contained bundle pinning one constant: its reference closure (sets `main`; validated closed)"

  FLAGS:
    anon;                   "Pack only anonymous structure — no names or metadata (§4/§5 empty; §3 hints still carried). The minimal artifact a receiver needs to typecheck/evaluate the pinned value."
    assume        : String; "Comma-separated cut-point constants — displayed names or 64-hex addresses. Reached cut-points are recorded in the bundle's `assumptions` instead of carried (thin bundle); unreached ones are skipped."
    "assume-file" : String; "Additionally read cut-points from a file (one per line; `#` comments and blank lines ignored). Unions with --assume."
    out           : String; "Output `.ixe` path. Defaults to `<name>.ixe` (e.g. `Nat.add.ixe`)."
    verbose;                "Print pack details (source stats, kept counts, bytes written) to stderr."

  ARGS:
    path : String; "Path to the source `.ixe` (e.g. from `ix compile`)."
    name : String; "Displayed name of the bundle root constant (e.g. `Nat.add`)."
]

end
