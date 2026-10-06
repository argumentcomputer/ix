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

  Whole units (M1-h): the bundle carries, for every block it reaches, the
  block's whole logical unit (eager and on-demand auxiliaries, design
  document §6.3), as the other closure producers do since M1-d
  (`packWholeUnits`); `--no-units` keeps the bare value closure.

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

/-! ## Whole logical units (M1-h)

A bundle carries, for every block it reaches, the block's whole logical unit
(design document §6.3, the rule M1-d gave the other closure producers): every
name of the source whose constant the bundle carries brings the members of
its unit (`Lean.UnitView.members`, the definition `Lean.unitMembers` uses,
read here from the compiled environment's names and metadata,
`ixonUnitView`). The value closure itself stays Rust's (`rsPackEnv`): each
missing member is packed from the same source with the same cut and merged
into the bundle, to a fixpoint. Every merged piece is a closed bundle of the
same source, so the union is closed, and every constant keeps the source's
bytes (they are content-addressed and copied, never recompiled). -/

def ixToLeanName : Ix.Name → Lean.Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (ixToLeanName p) s
  | .num p i _ => .num (ixToLeanName p) i

/-- The units of a compiled environment, read from its `Named` metadata: an
inductive's `all` and the members' `ctors`, a constructor's inductive, a
definition's `all` (`Lean.unitRoots` over the Lean declarations). -/
def ixonUnitView (env : Ixon.Env) : Lean.UnitView :=
  let byName : Std.HashMap Lean.Name Ixon.Named :=
    env.named.fold (fun m n nd => m.insert (ixToLeanName n) nd) {}
  let nameOf (a : Address) : Option Lean.Name := (env.names.get? a).map ixToLeanName
  let info (n : Lean.Name) : Ixon.ConstantMetaInfo :=
    match byName.get? n with
    | some nd => nd.constMeta.info
    | none => .empty
  let ofInduct (all : Array Address) : List Lean.Name :=
    let ms := all.toList.filterMap nameOf
    ms ++ ms.flatMap fun m => match info m with
      | .indc _ _ ctors _ _ _ _ => ctors.toList.filterMap nameOf
      | _ => []
  let orSelf (o : Lean.Name) (l : List Lean.Name) := if l.isEmpty then [o] else l
  { kind? := fun n => match info n with
      | .indc .. => some .induct
      | .ctor .. => some .ctor
      | .defn .. => some .defn
      | _ => none
    roots := fun o => match info o with
      | .indc _ _ _ all _ _ _ => orSelf o (ofInduct all)
      | .ctor _ _ induct _ _ => match (nameOf induct).map info with
        | some (.indc _ _ _ all _ _ _) => orSelf o (ofInduct all)
        | _ => [o]
      | .defn _ _ all _ _ _ _ => orSelf o (all.toList.filterMap nameOf)
      | _ => [o]
    contains := byName.contains
    names := fun _ => byName.toList.map (·.1) }

/-- `b` added to `a` (two bundles of one source; `a`'s root stays). -/
def mergeBundle (a b : Ixon.Env) : Ixon.Env :=
  { a with
    consts := b.consts.fold (·.insert · ·) a.consts
    named := b.named.fold (·.insert · ·) a.named
    blobs := b.blobs.fold (·.insert · ·) a.blobs
    names := b.names.fold (·.insert · ·) a.names
    comms := b.comms.fold (·.insert · ·) a.comms
    addrToName := b.addrToName.fold (·.insert · ·) a.addrToName
    assumptions := b.assumptions.fold (·.insert ·) a.assumptions
    anonHints := b.anonHints.fold (·.insert · ·) a.anonHints }

def readIxe (path : String) : IO Ixon.Env := do
  match Ixon.rsDeEnv (← IO.FS.readBinFile path) with
  | .ok e => pure e
  | .error e => throw (IO.userError s!"pack: cannot read {path}: {e}")

/-- The members of the units of the carried names that the bundle does not
carry (neither as a constant nor as a declared cut point). -/
def missingUnitMembers (src : Ixon.Env) (view : Lean.UnitView) (idx : Lean.UnitIndex)
    (bundle : Ixon.Env) : Array (Lean.Name × Address) := Id.run do
  let addrOf : Std.HashMap Lean.Name Address :=
    src.named.fold (fun m n nd => m.insert (ixToLeanName n) nd.addr) {}
  let held (a : Address) := bundle.consts.contains a || bundle.assumptions.contains a
  let mut out : Array (Lean.Name × Address) := #[]
  let mut seen : Std.HashSet Lean.Name := {}
  for (n, nd) in src.named.toList do
    unless bundle.consts.contains nd.addr do continue
    for m in view.members idx (ixToLeanName n) do
      if seen.contains m then continue
      seen := seen.insert m
      if let some a := addrOf.get? m then
        unless held a do out := out.push (m, a)
  return out

/-- `ix pack` with whole units: Rust's bundle of `mainName`, then every
missing unit member's bundle merged in, to a fixpoint. Returns the number of
rounds and of members packed. -/
def packWholeUnits (envPath mainName : String) (assume : Array String) (outPath : String)
    (anon verbose : Bool) : IO (Nat × Nat) := do
  Ixon.rsPackEnv envPath mainName assume outPath anon verbose
  let src ← readIxe envPath
  let view := ixonUnitView src
  let idx := view.index
  let mut bundle ← readIxe outPath
  let ixNameOf : Std.HashMap Lean.Name Ix.Name :=
    src.named.fold (fun m n _ => m.insert (ixToLeanName n) n) {}
  let tmp := outPath ++ ".unit.tmp"
  let mut rounds := 0
  let mut packed := 0
  repeat
    let missing := missingUnitMembers src view idx bundle
    if missing.isEmpty then break
    rounds := rounds + 1
    for (m, a) in missing do
      if bundle.consts.contains a || bundle.assumptions.contains a then continue
      let some ixn := ixNameOf.get? m | continue
      Ixon.rsPackEnv envPath ixn.pretty assume tmp anon false
      bundle := mergeBundle bundle (← readIxe tmp)
      packed := packed + 1
    if verbose then
      IO.eprintln s!"[pack] unit round {rounds}: {missing.size} missing member(s)"
  if packed > 0 then
    IO.FS.writeBinFile outPath (Ixon.rsSerEnv bundle)
    try IO.FS.removeFile tmp catch _ => pure ()
  return (rounds, packed)

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
  let units := !p.hasFlag "no-units"
  try
    let (rounds, packed) ← if units then
        packWholeUnits envPath mainName assume outPath anon verbose
      else do
        Ixon.rsPackEnv envPath mainName assume outPath anon verbose
        pure (0, 0)
    let mode := if anon then " [anon]" else ""
    let unitNote := if units then s!", whole units: {packed} member bundle(s) merged in {rounds} round(s)"
      else ", units not completed"
    IO.println s!"[pack] wrote {outPath} (main {mainName}, \
      {assume.size} assumption cut(s) declared{unitNote}){mode}"
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
    "no-units";             "Do not complete the logical units (the 3-edge value closure only, as before M1-h)."
    verbose;                "Print pack details (source stats, kept counts, bytes written) to stderr."

  ARGS:
    path : String; "Path to the source `.ixe` (e.g. from `ix compile`)."
    name : String; "Displayed name of the bundle root constant (e.g. `Nat.add`)."
]

end
