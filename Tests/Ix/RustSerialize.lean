/-
  Rust serialization/deserialization tests.
  Tests the Rust FFI endpoints for Ixon.Env serialization and deserialization
  by roundtripping through Rust and comparing with the Lean serializer.
-/

import Ix.Ixon
import Ix.Common
import Ix.Meta
import Ix.CompileM
import Lean
import LSpec
import Tests.Ix.Fixtures

open LSpec

namespace Tests.RustSerialize

/-- Test Rust serde roundtrip: compile → rsSerEnv → rsDesEnv → Lean serEnv → byte compare -/
def testRustSerdeRoundtrip : TestSeq :=
  .individualIO "Rust Serialize/Deserialize Roundtrip" none (do
    let leanEnv ← get_env!
    let totalConsts := leanEnv.constants.toList.length

    IO.println s!"[Test] Rust Serialize/Deserialize Roundtrip Test"
    IO.println s!"[Test] Environment has {totalConsts} constants"
    IO.println ""

    -- Step 1: Compile with Rust to get an Ixon.Env
    IO.println s!"[Step 1] Running Rust compilation pipeline..."
    let compileStart ← IO.monoMsNow
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    let compileTime := (← IO.monoMsNow) - compileStart
    IO.println s!"[Step 1]   Compiled: {ixonEnv.constCount} constants in {compileTime}ms"
    IO.println ""

    -- Step 2: Canonical Lean serialization (deterministic, sorted by key)
    IO.println s!"[Step 2] Serializing with Lean (serEnv)..."
    let leanSerStart ← IO.monoMsNow
    let leanBytes := Ixon.serEnv ixonEnv
    let leanSerTime := (← IO.monoMsNow) - leanSerStart
    IO.println s!"[Step 2]   {leanBytes.size} bytes in {leanSerTime}ms"
    IO.println ""

    -- Step 3: Serialize with Rust
    IO.println s!"[Step 3] Serializing with Rust (rsSerEnv)..."
    let rustSerStart ← IO.monoMsNow
    let rustBytes := Ixon.rsSerEnv ixonEnv
    let rustSerTime := (← IO.monoMsNow) - rustSerStart
    IO.println s!"[Step 3]   {rustBytes.size} bytes in {rustSerTime}ms"
    IO.println ""

    -- Step 4: Deserialize Rust bytes with Rust
    IO.println s!"[Step 4] Deserializing Rust bytes with Rust (rsDesEnv)..."
    let rustDesStart ← IO.monoMsNow
    let roundtrippedFromRust ← match Ixon.rsDesEnv rustBytes with
      | .ok env => pure env
      | .error e => do
        IO.println s!"[Step 4] FAILED: {e}"
        return (false, 0, 0, some e)
    let rustDesTime := (← IO.monoMsNow) - rustDesStart
    IO.println s!"[Step 4]   {roundtrippedFromRust.constCount} constants in {rustDesTime}ms"
    IO.println ""

    -- Step 5: Re-serialize the roundtripped env with Lean (deterministic)
    IO.println s!"[Step 5] Re-serializing roundtripped env with Lean..."
    let reserStart ← IO.monoMsNow
    let roundtrippedBytes := Ixon.serEnv roundtrippedFromRust
    let reserTime := (← IO.monoMsNow) - reserStart
    IO.println s!"[Step 5]   {roundtrippedBytes.size} bytes in {reserTime}ms"
    IO.println ""

    -- Step 6: Byte-exact comparison
    IO.println s!"[Step 6] Comparing Lean serialization vs roundtripped..."
    if leanBytes == roundtrippedBytes then
      IO.println s!"[Step 6]   Byte-exact match! ({leanBytes.size} bytes) ✓"
      IO.println ""
      return (true, 0, 0, none)
    else
      IO.println s!"[Step 6]   MISMATCH: {leanBytes.size} bytes vs {roundtrippedBytes.size} bytes"
      -- Find first diff
      let minLen := min leanBytes.size roundtrippedBytes.size
      let mut firstDiff := minLen
      for i in [:minLen] do
        if leanBytes.get! i != roundtrippedBytes.get! i then
          firstDiff := i
          break
      IO.println s!"[Step 6]   First difference at byte {firstDiff}"
      IO.println ""
      return (false, 0, 0, some s!"Bytes differ at offset {firstDiff} (original {leanBytes.size} vs roundtripped {roundtrippedBytes.size})")
  ) .done

/-! ## Test Suite -/

def rustSerializeSuiteIO : List TestSeq := [
  testRustSerdeRoundtrip,
]

end Tests.RustSerialize
