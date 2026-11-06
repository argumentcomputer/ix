module
public import Ix.DecompileM
public import Ix.IndFlags
public import Ix.CanonM
public import Ix.GraphM

/-!
  Ix.DecompileDriver: kernel-free decompilation of stored source records.

  The stored source declarations are selected (original addresses, metadata
  and hints) and decoded in parallel; their inductive flags are then
  recomputed from the decoded declarations. No auxiliary is regenerated or
  recompiled.
-/

public section

namespace Ix.DecompileM

/-- Restore Lean-faithful inductive flags. Ixon deliberately
    does not store `numNested`/`isRec`/`isReflexive` (they are derivable),
    so `decompileInductive` stubs them; this pass recomputes them per
    original mutual group FROM THE DECOMPILED CONSTANTS
    (`Ix.IndFlags.computeLeanIndFlags`).

    Groups key on `all[0]` (every member carries the same `all`, so
    first-seen insertion order is irrelevant). The flags computation runs
    in `CompileM` over a synthetic `CompileEnv` whose source env IS the
    decompiled map. -/
def fixupInductiveFlags (decompiled : Std.HashMap Ix.Name Ix.ConstantInfo)
    : Except String (Std.HashMap Ix.Name Ix.ConstantInfo) := Id.run do
  let mut groups : Std.HashMap Ix.Name (Array Ix.Name) := {}
  for (_, info) in decompiled do
    if let .inductInfo v := info then
      if let some first := v.all[0]? then
        if !groups.contains first then
          groups := groups.insert first v.all
  let cenv := Ix.CompileM.CompileEnv.new { consts := decompiled }
  let mut result := decompiled
  for (key, all) in groups do
    let blockEnv : Ix.CompileM.BlockEnv :=
      { all := {}, current := key, mutCtx := default, univCtx := [] }
    match Ix.CompileM.CompileM.run cenv blockEnv {}
        (Ix.IndFlags.computeLeanIndFlags all) with
    | .error e =>
      return .error s!"ind-flags fixup for block '{key.pretty}': {e}"
    | .ok (flags, _) =>
      for member in all do
        if let some (.inductInfo v) := result.get? member then
          result := result.insert member (.inductInfo { v with
            numNested := flags.numNested
            isRec := flags.isRec
            isReflexive := flags.isReflexive })
  return .ok result

/-- Read source records without changing canonical reference resolution. -/
private def decompileOriginals (ixonEnv : Ixon.Env) (numWorkers : Nat)
    : Std.HashMap Ix.Name Ix.ConstantInfo × Array (Ix.Name × String) × Unit :=
  let (decoded, errors) := decompileAllParallel (originalView ixonEnv) numWorkers
  match fixupInductiveFlags decoded with
  | .ok fixed => (fixed, errors, ())
  | .error err => (decoded, errors.push (Ix.Name.mkAnon, err), ())

/-- Full source decompile: read every stored record, then restore inductive
    flags. The historical sharing-limit/source-oracle arguments and triple
    shape remain for callers; decoding uses neither argument, and the retired
    regeneration state is now `Unit`. A missing record is an error and never
    triggers a kernel fallback. -/
def decompileEnvFull (ixonEnv : Ixon.Env)
    (sharingLimits : Ix.Sharing.Exact.Limits)
    (origEnv? : Option (Std.HashMap Ix.Name Ix.ConstantInfo) := none)
    : Std.HashMap Ix.Name Ix.ConstantInfo × Array (Ix.Name × String) × Unit :=
  let _ := sharingLimits
  let _ := origEnv?
  decompileOriginals ixonEnv 32

/-- IO wrapper with the existing worker override. `0` selects one decoding
    chunk; all settings use the same checked original-record reader. -/
def decompileEnvFullParallel (ixonEnv : Ixon.Env)
    (origEnv? : Option (Std.HashMap Ix.Name Ix.ConstantInfo) := none)
    (numWorkers : Nat := 16)
    (sharingLimits : Ix.Sharing.Exact.Limits := Ix.CompileM.compilerSharingLimits)
    : IO (Std.HashMap Ix.Name Ix.ConstantInfo × Array (Ix.Name × String) × Unit) := do
  let _ := origEnv?
  let _ := sharingLimits
  let numWorkers := ((← IO.getEnv "IX_DECOMPILE_WORKERS").bind (·.toNat?)).getD numWorkers
  return decompileOriginals ixonEnv (max 1 numWorkers)

/-- Select the source view of a decompiled environment (`import_ixe`).
    `only` empty selects every name; otherwise the requested names, which must
    be present in `decompiled`, and their reference closure. The reference
    closure is checked for a full selection too, so a broken source
    reconstruction is refused: every reference must be a present name. -/
def materializedSourceNames (decompiled : Std.HashMap Ix.Name Ix.ConstantInfo)
    (only : Array Lean.Name := #[]) : Except String (Array Ix.Name) := do
  let roots : Array Ix.Name :=
    if only.isEmpty then decompiled.toArray.map (·.1)
    else only.map Ix.Name.fromLeanName
  let mut seen : Ix.Set Ix.Name := {}
  let mut worklist : Array Ix.Name := #[]
  for root in roots do
    unless decompiled.contains root do
      throw s!"requested source constant '{root.pretty}' not found"
    unless seen.contains root do
      seen := seen.insert root
      worklist := worklist.push root
  while !worklist.isEmpty do
    let name := worklist.back!
    worklist := worklist.pop
    let some decl := decompiled.get? name
      | throw s!"source constant '{name.pretty}' disappeared during selection"
    let (refs, _) := Ix.GraphM.run { consts := {} } .init (Ix.graphConst decl)
    for ref in refs do
      unless seen.contains ref do
        unless decompiled.contains ref do
          throw s!"source constant '{name.pretty}' references missing source constant '{ref.pretty}' — broken closure"
        seen := seen.insert ref
        worklist := worklist.push ref
  return seen.toArray

/-- Read, verify, and decompile a `.ixe` from disk in pure Lean, returning the
    selected source constants as `Lean.ConstantInfo` pairs sorted by name.
    Empty `only` returns every decompiled constant; nonempty returns the
    requested source constants plus their reference closure. Fails on anonymous
    envs, thin bundles, broken source closures, and absent requested names. -/
def decompileEnvConsts (path : String) (only : Array Lean.Name := #[])
    : IO (Array (Lean.Name × Lean.ConstantInfo)) := do
  let bytes ← IO.FS.readBinFile path
  let parts ← match Ixon.deEnvVerifiedLazy bytes with
    | .ok p => pure p
    | .error e => throw <| IO.userError s!"decompile {path}: {e}"
  if parts.namedRows.isEmpty then
    throw <| IO.userError
      s!"decompile {path}: anonymous env (empty named section); decompile needs names"
  if !parts.env.assumptions.isEmpty then
    throw <| IO.userError
      s!"decompile {path}: thin bundle ({parts.env.assumptions.size} assumptions); decompile needs a self-contained env"
  let ixonEnv ← match parts.materializeAll with
    | .ok env => pure env
    | .error e => throw <| IO.userError s!"decompile {path}: {e}"
  let (decompiled, errors, _) ← decompileEnvFullParallel ixonEnv
  if !errors.isEmpty then
    let (firstName, firstErr) := errors[0]!
    throw <| IO.userError s!"decompile {path}: {firstName.pretty}: {firstErr}"
  let selected ← match materializedSourceNames decompiled only with
    | .ok names => pure names
    | .error e => throw <| IO.userError s!"decompile {path}: {e}"
  let uncanoned : Array (Lean.Name × Lean.ConstantInfo) :=
    ((selected.mapM fun name => do
      let some info := decompiled.get? name
        | unreachable!
      let name' ← Ix.CanonM.uncanonName name
      let info' ← Ix.CanonM.uncanonConst info
      pure (name', info')).run {}).1
  return uncanoned.qsort (fun a b => Lean.Name.lt a.1 b.1)

end Ix.DecompileM
