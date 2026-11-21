module

public import Benchmarks.FormalAiur.Types

/-!
Typed manifest for the formal Aiur trace-profile measurements
(`docs/formal-aiur-trace-profile.md`).
Replaces `docs/benchmarks/formal-aiur-trace-profile/manifest.json`.
-/

@[expose] public section

namespace Benchmarks.FormalAiur.TraceProfile

structure Manifest where
  date : String
  baseRevision : String
  phaseThreads : Nat
  phaseSamples : Nat
  natSamples : Nat
  warmups : Nat
  natThreads : Array Nat
  reuseExecution : Bool
  hostLookups : Bool
  thpDisabled : Bool
  rustflags : String
  profileFeatures : String
  profiledBinarySha256 : String
  artifactInputSha256 : Array NamedSha256
  validation : Array String
  notes : Array String
  deriving BEq, Repr, Inhabited

def manifest : Manifest := {
  date := "2026-10-28"
  baseRevision := "1a19788bc051528aa59d37756d405752b166e012"
  phaseThreads := 64
  phaseSamples := 3
  natSamples := 5
  warmups := 2
  natThreads := #[1, 8, 32, 64]
  reuseExecution := true
  hostLookups := true
  thpDisabled := true
  rustflags := "-Ctarget-cpu=native"
  profileFeatures := "parallel,aiur/trace-profile"
  profiledBinarySha256 := "1b3c052fbe957172bbbf4cf8705e3b4ae545cdadf094bc18f04bd3d955489f95"
  artifactInputSha256 := #[
    { name := ".lake/formal-integration/ixvm-tuned.json", sha256 := "1f8c10da7b10587e985d5166b26ad0c7edd4f4cbdfe0978c7deb237cf6683d9a" },
    { name := ".lake/formal-integration/recursion-tuned.json", sha256 := "40e88dd1f84e4f119626189e83f8eb181f6ef9875c190f33cdd7853e83c5afe1" },
    { name := ".lake/formal-comparison/final/ixvm-input.json", sha256 := "2733974cdf8d687799f678140ab967d3ab2c5a9f8768c8c3455bc86b5281a7b8" },
    { name := ".lake/formal-comparison/final/environment-input.json", sha256 := "14a147c1d6141721547092a9a835249969aa1f82c8f57f9ed0a2b0522f7aaa56" },
    { name := ".lake/formal-comparison/final/new-environment-grouped.json.inner/input.json", sha256 := "2ecf2051d112503637b9d3c1a6201bd66f91df4568a95faff3cef068e3f96a1a" }
  ]
  validation := #[
    "Profiled Nat.add_comm proof verifies (5478175 bytes, same size as unprofiled)",
    "Grouped trace/proof regression passes with trace-profile enabled",
    "Clippy passes with warnings denied for the profiled comparison example"
  ]
  notes := #[
    "Phase timings are sequential wall-clock checkpoints; per-circuit spans overlap and cannot be summed",
    "Profile logging is outside the reported profile total and inside the outer benchmark timer",
    "The Nat frontier scaling sweep used the ordinary binary before enabling profiling"
  ]
}

end Benchmarks.FormalAiur.TraceProfile
