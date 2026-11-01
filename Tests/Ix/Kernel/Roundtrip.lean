/-
  Kernel ixon roundtrip test.

  Exercises
  `Lean env → compile → ixon_ingress → kenv → ixon_egress → decompile → Lean`
  on the full current environment and compares each constant (by content
  hash) against the original, through `ixon_egress + decompile_env` (the
  validated decompile path) rather than a second ad-hoc `KEnv → Lean`
  decompiler.

  If `kernel-ixon-roundtrip` passes but `kernel-tutorial` fails, the bug
  is in the check side.
-/
import Ix.Common
import Ix.Meta
import Ix.CompileM
import Ix.CompileCertified
import Ix.DecompileM
import Ix.DecompileDriver
import LSpec
-- Level-spelling fixtures (canonicity §10.6): mk*-reducible spellings
-- must survive the kernel leg via the Rust spelling decorations —
-- imported so `get_env!` (this file's module closure) carries them.
import Tests.Ix.Compile.LevelSpellings

open LSpec

namespace Tests.Ix.Kernel.Roundtrip

/-- Run the compile + decompile roundtrip and collect per-constant diff messages.
    Empty array = roundtrip agrees with the original Lean env. -/
def rsKernelRoundtripFFI
    (consts : List (Lean.Name × Lean.ConstantInfo)) : IO (Array String) := do
  let rawEnv := Ix.CompileM.canonInput consts.toArray 32
  let (compiledEnv, _) ← IO.ofExcept (Ix.Cert.compileReport rawEnv)
  let (decompiled, errors, _) ←
    Ix.DecompileM.decompileEnvFullParallel compiledEnv (some rawEnv.consts)
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
  .individualIO "kernel ixon roundtrip" none (do
    let leanEnv ← get_env!
    let errors ← rsKernelRoundtripFFI leanEnv.constants.toList
    if errors.isEmpty then
      return (true, 0, 0, none)
    else
      IO.println s!"[kernel-ixon-roundtrip] {errors.size} errors:"
      for msg in errors[:min 20 errors.size] do
        IO.println s!"  {msg}"
      return (false, 0, 0, some s!"{errors.size} roundtrip mismatches")
  ) .done

def suite : List TestSeq := [testRoundtrip]

end Tests.Ix.Kernel.Roundtrip
