/-
  Cross-compiler decompilation inventory — D0 of the decompiler port.

  Rust-compiles the shared aux fixture corpus (`validateAuxClosure` — the
  same corpus the aux-gen-diff gates run on), decompiles the resulting
  Ixon env with the pure-Lean `Ix.DecompileM`, and compares every
  reconstructed constant against the SOURCE `Ix.Environment` by full
  structural equality (`ConstantInfo` BEq — hash-based at the
  Name/Level/Expr leaves, so this is Rust `check_decompile`'s
  `get_hash` comparison at full fidelity).

  Failures are classified into the port's milestone buckets:

    - `callsite` errors — bodies with surgered call-site metadata the
      pure-Lean decompiler cannot replay yet (D1);
    - `aux` names (`isAuxGenSuffix`) — decompiled from the REGENERATED
      canonical constants, expected to mismatch the source's Lean-native
      originals until Pass 2 recovery lands (D3);
    - `plain` mismatches / other errors — the D0 gate: must be ZERO.

  Coverage is checked in both directions: decompiled-but-not-in-source
  (synthetic/alias artifacts) and in-source-but-not-decompiled (skipped
  kinds), each bucketed aux/plain.

  Invoked via `lake test -- --ignored decompile-diff`.
-/
import Ix.Common
import Ix.CompileM
import Ix.DecompileM
import Ix.DecompileDriver
import Ix.CallSiteSurgery
import Lean
import LSpec
import Tests.Ix.Compile.ValidateAux

namespace Tests.Compile.DecompileDiff

private def sample (xs : Array Ix.Name) (n : Nat := 12) : String :=
  ", ".intercalate ((xs.toList.take n).map (·.pretty))

/-- Aux-family by LINEAGE: the name itself carries an aux-gen suffix, or
    any ancestor does — covering the constructors of synthesized `.below`
    inductives (`Even.below.zero`), which Rust's Pass 2 recovers together
    with their parent. -/
private partial def isAuxLineage (n : Ix.Name) : Bool :=
  if Ix.AuxGen.isAuxGenSuffix n then
    true
  else
    match n with
    | .str parent _ _ => isAuxLineage parent
    | .num parent _ _ => isAuxLineage parent
    | .anonymous _ => false

def run (env : Lean.Environment) : IO UInt32 := do
  IO.println "[decompile-diff] collecting fixture closure..."
  let filtered := validateAuxClosure env
  IO.println s!"[decompile-diff] {filtered.length} constants"

  IO.println "[decompile-diff] Rust compile (rsCompilePhases)..."
  let raw ← Ix.CompileM.rsCompilePhasesFFI filtered
  let rawEnv := raw.rawEnv.toEnvironment
  let rustEnv := raw.compileEnv.toEnv
  IO.println s!"[decompile-diff] Rust: {rustEnv.named.size} named, {rustEnv.consts.size} consts"

  IO.println "[decompile-diff] Lean decompile (parallel)..."
  let (decompiledRaw, errors) ← Ix.DecompileM.decompileAllParallelIO rustEnv
  -- Pass 1.5: Lean-faithful inductive flags (decompile.rs:5030-5058).
  let decompiled ← match Ix.DecompileM.fixupInductiveFlags decompiledRaw with
    | .ok d => pure d
    | .error e =>
      IO.println s!"[decompile-diff] Pass 1.5 FAILED: {e}"
      pure decompiledRaw

  -- Error classification.
  let mut callSiteErrs : Array Ix.Name := #[]
  let mut auxErrs : Array Ix.Name := #[]
  let mut otherErrs : Array (Ix.Name × String) := #[]
  for (n, e) in errors do
    if (e.splitOn "call-site surgery").length > 1 then
      callSiteErrs := callSiteErrs.push n
    else if isAuxLineage n then
      auxErrs := auxErrs.push n
    else
      otherErrs := otherErrs.push (n, e)

  -- Forward comparison: every decompiled constant vs the source env.
  let mut plainMatch := (0 : Nat)
  let mut auxMatch := (0 : Nat)
  let mut plainMismatch : Array Ix.Name := #[]
  let mut auxMismatch : Array Ix.Name := #[]
  let mut notInSource : Array Ix.Name := #[]
  for (name, info) in decompiled do
    match rawEnv.consts.get? name with
    | none => notInSource := notInSource.push name
    | some orig =>
      if info == orig then
        if isAuxLineage name then
          auxMatch := auxMatch + 1
        else
          plainMatch := plainMatch + 1
      else
        if isAuxLineage name then
          auxMismatch := auxMismatch.push name
        else
          plainMismatch := plainMismatch.push name

  -- Reverse coverage: source constants never reconstructed. Errored
  -- names are already counted above; exclude them here so the buckets
  -- partition cleanly.
  let mut errNames : Ix.Set Ix.Name := {}
  for (n, _) in errors do
    errNames := errNames.insert n
  let mut missingAux : Array Ix.Name := #[]
  let mut missingPlain : Array Ix.Name := #[]
  for (name, _) in rawEnv.consts do
    if !decompiled.contains name && !errNames.contains name then
      if isAuxLineage name then
        missingAux := missingAux.push name
      else
        missingPlain := missingPlain.push name

  IO.println ""
  IO.println s!"[decompile-diff] decompiled {decompiled.size} constants, {errors.size} errors"
  IO.println s!"[decompile-diff]   plain: {plainMatch} matched, {plainMismatch.size} mismatched  (D0 gate — must be 0)"
  if !plainMismatch.isEmpty then
    IO.println s!"[decompile-diff]     mismatch e.g. {sample plainMismatch}"
  IO.println s!"[decompile-diff]   aux-family: {auxMatch} matched, {auxMismatch.size} mismatched  (red until D3 original recovery)"
  if !auxMismatch.isEmpty then
    IO.println s!"[decompile-diff]     mismatch e.g. {sample auxMismatch}"
  IO.println s!"[decompile-diff]   callsite errors: {callSiteErrs.size}  (D1 gate — must be 0)"
  if !callSiteErrs.isEmpty then
    IO.println s!"[decompile-diff]     e.g. {sample callSiteErrs}"
  IO.println s!"[decompile-diff]   aux errors: {auxErrs.size}  (red until D3)"
  if !auxErrs.isEmpty then
    IO.println s!"[decompile-diff]     e.g. {sample auxErrs}"
  IO.println s!"[decompile-diff]   other errors: {otherErrs.size}  (D0 gate — must be 0)"
  for (n, e) in otherErrs.toList.take 8 do
    IO.println s!"[decompile-diff]     {n.pretty}: {e.take 200}"
  IO.println s!"[decompile-diff]   decompiled-not-in-source: {notInSource.size}"
  if !notInSource.isEmpty then
    IO.println s!"[decompile-diff]     e.g. {sample notInSource}"
  IO.println s!"[decompile-diff]   missing from decompile: {missingAux.size} aux, {missingPlain.size} plain"
  if !missingPlain.isEmpty then
    IO.println s!"[decompile-diff]     plain e.g. {sample missingPlain}"

  let gateOk := plainMismatch.isEmpty && otherErrs.isEmpty
    && notInSource.isEmpty && missingPlain.isEmpty
    && callSiteErrs.isEmpty
  IO.println ""
  IO.println s!"[decompile-diff] D0+D1 gate (plain fidelity + callsite replay): {if gateOk then "PASS" else "FAIL"}"
  return if gateOk then 0 else 1

end Tests.Compile.DecompileDiff
