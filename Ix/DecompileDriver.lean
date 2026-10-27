/-
  Ix.DecompileDriver: kernel-free decompilation of stored source records.

  Pass 1 selects original addresses, metadata and hints, then decodes each
  source declaration in parallel. Pass 1.5 recomputes inductive flags from
  those decoded declarations. No auxiliary is regenerated or recompiled.
-/
module
public import Ix.DecompileM
public import Ix.AuxGen.Nested
public section

namespace Ix.DecompileM

/-- Pass 1.5: restore Lean-faithful inductive flags. Ixon deliberately
    does not store `numNested`/`isRec`/`isReflexive` (they are derivable),
    so `decompileInductive` stubs them; this pass recomputes them per
    original mutual group FROM THE DECOMPILED CONSTANTS via the aux-gen
    expansion machinery — mirroring Rust `decompile_env`'s Pass 1.5
    (decompile.rs:5030-5058), which calls the same
    `compute_lean_ind_flags` (ported as `Ix.AuxGen.computeLeanIndFlags`,
    nested.rs:1416).

    Groups key on `all[0]` (every member carries the same `all`, so
    first-seen insertion order is irrelevant). The flags computation runs
    in `CompileM` over a synthetic `CompileEnv` whose source env IS the
    decompiled map — the same self-referential view Rust passes. -/
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
        (Ix.AuxGen.computeLeanIndFlags all) with
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

end Ix.DecompileM
