/-
  Rust decompilation tests.
  Tests the Rust FFI endpoint for decompilation by compiling with Rust,
  decompiling with Rust, and comparing against the original environment.
-/

import Ix.Ixon
import Ix.Environment
import Ix.Address
import Ix.Common
import Ix.Meta
import Ix.CompileM
import Ix.DecompileM
import Lean
import LSpec
import Tests.Ix.Fixtures

open LSpec

namespace Tests.RustDecompile

/-- Test Rust decompilation: compile → rsDecompileEnv → hash comparison -/
def testRustDecompile : TestSeq :=
  .individualIO "Rust Decompilation Roundtrip" (do
    let leanEnv ← get_env!
    let totalConsts := leanEnv.constants.toList.length

    IO.println s!"[Test] Rust Decompilation Roundtrip Test"
    IO.println s!"[Test] Environment has {totalConsts} constants"
    IO.println ""

    -- Step 1: Run Rust compilation pipeline
    IO.println s!"[Step 1] Running Rust compilation pipeline..."
    let rustStart ← IO.monoMsNow
    let phases ← Ix.CompileM.rsCompilePhases leanEnv
    let rustTime := (← IO.monoMsNow) - rustStart
    IO.println s!"[Step 1]   Rust: {phases.compileEnv.constCount} compiled in {rustTime}ms"
    IO.println s!"[Step 1]   names={phases.compileEnv.names.size}, named={phases.compileEnv.named.size}, consts={phases.compileEnv.consts.size}, blobs={phases.compileEnv.blobs.size}"
    IO.println ""

    -- Step 2: Decompile with Rust
    IO.println s!"[Step 2] Decompiling with Rust (rsDecompileEnv)..."
    let decompStart ← IO.monoMsNow
    let decompiled ← match Ix.DecompileM.rsDecompileEnv phases.compileEnv with
      | .ok env => pure env
      | .error e => do
        IO.println s!"[Step 2] FAILED: {toString e}"
        return (false, some (toString e))
    let decompTime := (← IO.monoMsNow) - decompStart
    IO.println s!"[Step 2]   {decompiled.size} constants decompiled in {decompTime}ms"
    IO.println ""

    -- Count by constant type
    let mut nDefn := (0 : Nat); let mut nAxiom := (0 : Nat)
    let mut nInduct := (0 : Nat); let mut nCtor := (0 : Nat)
    let mut nRec := (0 : Nat); let mut nQuot := (0 : Nat)
    let mut nOpaque := (0 : Nat); let mut nThm := (0 : Nat)
    for (_, info) in decompiled do
      match info with
      | .defnInfo _ => nDefn := nDefn + 1
      | .axiomInfo _ => nAxiom := nAxiom + 1
      | .inductInfo _ => nInduct := nInduct + 1
      | .ctorInfo _ => nCtor := nCtor + 1
      | .recInfo _ => nRec := nRec + 1
      | .quotInfo _ => nQuot := nQuot + 1
      | .opaqueInfo _ => nOpaque := nOpaque + 1
      | .thmInfo _ => nThm := nThm + 1
    IO.println s!"[Types] defn={nDefn}, thm={nThm}, opaque={nOpaque}, axiom={nAxiom}, induct={nInduct}, ctor={nCtor}, rec={nRec}, quot={nQuot}"
    IO.println ""

    -- Step 3: Hash-based comparison against original Ix.Environment
    let ixEnv := phases.rawEnv
    IO.println s!"[Step 3] Original Ix.Environment has {ixEnv.consts.size} constants"
    IO.println s!"[Compare] Hash-comparing {decompiled.size} decompiled constants..."
    let compareStart ← IO.monoMsNow

    let mut nMatch := (0 : Nat); let mut nMismatch := (0 : Nat); let mut nMissing := (0 : Nat)
    let mut firstMismatches : Array (Ix.Name × String) := #[]
    for (name, decompInfo) in decompiled do
      match ixEnv.consts.get? name with
      | some origInfo =>
        let decompTyHash := decompInfo.getCnst.type.getHash
        let origTyHash := origInfo.getCnst.type.getHash
        if decompTyHash != origTyHash then
          nMismatch := nMismatch + 1
          if firstMismatches.size < 10 then
            firstMismatches := firstMismatches.push (name, s!"type hash mismatch")
        else
          let valMismatch := match decompInfo, origInfo with
            | .defnInfo dv, .defnInfo ov => dv.value.getHash != ov.value.getHash
            | .thmInfo dv, .thmInfo ov => dv.value.getHash != ov.value.getHash
            | .opaqueInfo dv, .opaqueInfo ov => dv.value.getHash != ov.value.getHash
            | _, _ => false
          if valMismatch then
            nMismatch := nMismatch + 1
            if firstMismatches.size < 10 then
              firstMismatches := firstMismatches.push (name, s!"value hash mismatch")
          else
            nMatch := nMatch + 1
      | none =>
        nMissing := nMissing + 1
        if firstMismatches.size < 10 then
          firstMismatches := firstMismatches.push (name, "not in original")

    let compareTime := (← IO.monoMsNow) - compareStart
    IO.println s!"[Compare] Matched: {nMatch}, Mismatched: {nMismatch}, Missing: {nMissing} ({compareTime}ms)"
    if !firstMismatches.isEmpty then
      IO.println s!"[Compare] First mismatches:"
      for (name, diff) in firstMismatches do
        IO.println s!"  {name}: {diff}"
    IO.println ""

    let success := nMismatch == 0 && nMissing == 0
    if success then
      return (true, none)
    else
      return (false, some s!"{nMismatch} mismatches, {nMissing} missing")
  ) .done

/-! ## Test Suite -/

def rustDecompileSuiteIO : List TestSeq := [
  testRustDecompile,
]

end Tests.RustDecompile
