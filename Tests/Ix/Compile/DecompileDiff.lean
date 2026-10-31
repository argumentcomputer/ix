/-
  Cross-compiler decompilation inventory for the decompiler.

  Rust-compiles the shared fixture corpus (`validateAuxClosure`), decompiles
  the resulting Ixon env with the pure-Lean `Ix.DecompileM`, and compares
  every reconstructed constant against the SOURCE `Ix.Environment` by full
  structural equality (`ConstantInfo` BEq — hash-based at the
  Name/Level/Expr leaves, so this is Rust `check_decompile`'s `get_hash`
  comparison at full fidelity).

  The gate is total: no mismatch, no decompile error, no decompiled constant
  outside the source and no source constant missing from the decompile.

  Invoked via `lake test -- --ignored decompile-diff`.
-/
import Ix.Common
import Ix.CompileM
import Ix.DecompileM
import Ix.DecompileDriver
import Lean
import LSpec
import Tests.Ix.Compile.ValidateAux

namespace Tests.Compile.DecompileDiff

private def sample (xs : Array Ix.Name) (n : Nat := 12) : String :=
  ", ".intercalate ((xs.toList.take n).map (·.pretty))

def run (env : Lean.Environment) : IO UInt32 := do
  IO.println "[decompile-diff] collecting fixture closure..."
  let filtered := validateAuxClosure env
  IO.println s!"[decompile-diff] {filtered.length} constants"

  IO.println "[decompile-diff] Rust compile (rsCompilePhases)..."
  let raw ← Ix.CompileM.rsCompilePhasesFFI filtered
  let rawEnv := raw.rawEnv.toEnvironment
  let rustEnv := raw.compileEnv.toEnv
  IO.println s!"[decompile-diff] Rust: {rustEnv.named.size} named, {rustEnv.consts.size} consts"

  IO.println "[decompile-diff] Lean decompile (full driver)..."
  let t0 ← IO.monoMsNow
  let origView : Std.HashMap Ix.Name Ix.ConstantInfo := rawEnv.consts
  -- The limits the Rust compile above read (`IX_SHARING_LIMITS`).
  let sharingLimits ← IO.ofExcept (← Ix.CompileM.compilerSharingLimitsFromEnv)
  let (decompiled, errors, _) ←
    Ix.DecompileM.decompileEnvFullParallel rustEnv (some origView)
      (sharingLimits := sharingLimits)
  IO.println s!"[decompile-diff]   {decompiled.size} constants, {errors.size} errors in {(← IO.monoMsNow) - t0}ms"

  -- Forward comparison: every decompiled constant vs the source env.
  let mut matched := (0 : Nat)
  let mut mismatched : Array Ix.Name := #[]
  let mut notInSource : Array Ix.Name := #[]
  for (name, info) in decompiled do
    match rawEnv.consts.get? name with
    | none => notInSource := notInSource.push name
    | some orig =>
      if info == orig then matched := matched + 1
      else mismatched := mismatched.push name

  -- Reverse coverage: source constants never reconstructed. Errored names
  -- are already counted above; exclude them here so the buckets partition
  -- cleanly.
  let mut errNames : Ix.Set Ix.Name := {}
  for (n, _) in errors do
    errNames := errNames.insert n
  let mut missing : Array Ix.Name := #[]
  for (name, _) in rawEnv.consts do
    if !decompiled.contains name && !errNames.contains name then
      missing := missing.push name

  IO.println ""
  IO.println s!"[decompile-diff] decompiled {decompiled.size} constants, {errors.size} errors"
  IO.println s!"[decompile-diff]   {matched} matched, {mismatched.size} mismatched (must be 0)"
  if !mismatched.isEmpty then
    IO.println s!"[decompile-diff]     mismatch e.g. {sample mismatched}"
  IO.println s!"[decompile-diff]   errors: {errors.size} (must be 0)"
  for (n, e) in errors.toList.take 8 do
    IO.println s!"[decompile-diff]     {n.pretty}: {e.take 300}"
  IO.println s!"[decompile-diff]   decompiled-not-in-source: {notInSource.size} (must be 0)"
  if !notInSource.isEmpty then
    IO.println s!"[decompile-diff]     e.g. {sample notInSource}"
  IO.println s!"[decompile-diff]   missing from decompile: {missing.size} (must be 0)"
  if !missing.isEmpty then
    IO.println s!"[decompile-diff]     e.g. {sample missing}"

  let gateOk := mismatched.isEmpty && errors.isEmpty && notInSource.isEmpty && missing.isEmpty
  IO.println ""
  IO.println s!"[decompile-diff] fidelity gate: {if gateOk then "PASS" else "FAIL"}"
  return if gateOk then 0 else 1

end Tests.Compile.DecompileDiff
