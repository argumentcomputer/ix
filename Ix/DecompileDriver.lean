/-
  Ix.DecompileDriver: decompilation driver passes above the per-constant
  core (`Ix.DecompileM`) — the Lean mirror of `decompile_env`'s pass
  structure (crates/compile/src/decompile.rs:4973-5330).

  Like `Ix.CompileDriver`, this sits ABOVE `Ix.AuxGen` (the per-constant
  core stays a leaf; the driver passes need the aux-gen machinery):

    Pass 1    parallel per-constant decompile — `Ix.DecompileM`
    Pass 1.5  Lean-faithful inductive flags (this module, D0)
    Pass 2    aux-original recovery — D3, not yet ported

  Definitions live in namespace `Ix.DecompileM` so call sites read
  uniformly with the core (same layout convention as `Ix.CompileDriver`
  defining into `Ix.CompileM`).
-/
module
public import Ix.Common
public import Ix.Environment
public import Ix.Ixon
public import Ix.DecompileM
public import Ix.CompileM
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

end Ix.DecompileM
