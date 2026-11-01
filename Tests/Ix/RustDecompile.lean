import Ix.Common
import Ix.Meta
import Ix.CompileM
import Ix.CompileCertified
import Ix.DecompileM
import Ix.DecompileDriver
import Ix.Ixon
import LSpec

/-!
  Serialized decompile roundtrip test.

  Exercises `Lean env → compile → serialize → deserialize → decompile →
  Lean` — the `ix decompile` pipeline over the serialized `.ixe`
  boundary (demoted-at-parse metadata load, `Named.original` recovery
  for shape-divergent aux blocks, expression interning) — and
  compares every constant against the original.
  `kernel-ixon-roundtrip` covers the kernel ingress/egress leg instead.
-/

open LSpec

namespace Tests.RustDecompile

/-- Run the serialized decompile roundtrip and collect per-constant
    diff messages. Empty array = decompile agrees with the original Lean
    env. -/
def rsDecompileRoundtripFFI
    (consts : List (Lean.Name × Lean.ConstantInfo)) : IO (Array String) := do
  let rawEnv := Ix.CompileM.canonInput consts.toArray 32
  let (compiledEnv, _) ← IO.ofExcept (Ix.Cert.compileReport rawEnv)
  let bytes ← IO.ofExcept (Ixon.rsSerEnv compiledEnv)
  let parsedEnv ← IO.ofExcept (Ixon.rsDeEnv bytes)
  let (decompiled, errors, _) ←
    Ix.DecompileM.decompileEnvFullParallel parsedEnv (some rawEnv.consts)
      (sharingLimits := Ix.CompileM.compilerSharingLimits)
  let mut msgs : Array String := #[]
  for (n, e) in errors do
    msgs := msgs.push s!"{n.pretty}: decompile error: {e}"
  for (n, info) in decompiled do
    match rawEnv.consts.get? n with
    | none => msgs := msgs.push s!"{n.pretty}: decompiled constant not in source"
    | some orig =>
      if info != orig then
        msgs := msgs.push s!"{n.pretty}: constant-info mismatch"
  return msgs

def testRoundtrip : TestSeq :=
  .individualIO "rust decompile roundtrip" none (do
    let leanEnv ← get_env!
    let errors ← rsDecompileRoundtripFFI leanEnv.constants.toList
    if errors.isEmpty then
      return (true, 0, 0, none)
    else
      IO.println s!"[rust-decompile] {errors.size} errors:"
      for msg in errors[:min 20 errors.size] do
        IO.println s!"  {msg}"
      return (false, 0, 0, some s!"{errors.size} roundtrip mismatches")
  ) .done

def rustDecompileSuiteIO : List TestSeq := [testRoundtrip]

end Tests.RustDecompile
