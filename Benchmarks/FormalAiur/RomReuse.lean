module

public import Benchmarks.FormalAiur.Types

/-!
Typed manifest for the formal Aiur ROM-reuse measurements
(`docs/formal-aiur-rom-reuse.md`).
Replaces `docs/benchmarks/formal-aiur-rom-reuse/manifest.json`.
-/

@[expose] public section

namespace Benchmarks.FormalAiur.RomReuse

structure Validation where
  serialTests : TestSuiteRun
  parallelTests : TestSuiteRun
  clippyProfiledComparison : Bool
  proofs : Array ProofValidation
  natProofByteIdentical : Bool
  clippyDefaultAllTargets : Bool
  formatting : Bool
  ordinaryBinaryRestored : Bool
  deriving BEq, Repr, Inhabited

structure Manifest where
  date : String
  baseRevision : String
  rustflags : String
  features : String
  profileInstrumentation : Bool
  codegen : Bool
  warmups : Nat
  hostLookups : Bool
  thpDisabled : Bool
  affinity : String
  lscpu : Array LscpuField
  artifactInputSha256 : Array NamedSha256
  binarySha256 : Array NamedSha256
  sourceSha256 : Array NamedSha256
  notes : Array String
  profiledBinarySha256 : String
  profileThreads : Nat
  profileSamples : Nat
  profileFeatures : String
  validation : Validation
  deriving BEq, Repr, Inhabited

def manifest : Manifest := {
  date := "2026-10-28"
  baseRevision := "5502287489c5a954ef23ad8b766611122c877e3e"
  rustflags := "-Ctarget-cpu=native"
  features := "parallel"
  profileInstrumentation := false
  codegen := false
  warmups := 2
  hostLookups := true
  thpDisabled := true
  affinity := "CPUs 0 through (threads - 1)"
  lscpu := xeon6975pcLscpu
  artifactInputSha256 := #[
    { name := ".lake/formal-integration/ixvm-tuned.json", sha256 := "1f8c10da7b10587e985d5166b26ad0c7edd4f4cbdfe0978c7deb237cf6683d9a" },
    { name := ".lake/formal-integration/recursion-tuned.json", sha256 := "40e88dd1f84e4f119626189e83f8eb181f6ef9875c190f33cdd7853e83c5afe1" },
    { name := ".lake/formal-comparison/final/ixvm-input.json", sha256 := "2733974cdf8d687799f678140ab967d3ab2c5a9f8768c8c3455bc86b5281a7b8" },
    { name := ".lake/formal-comparison/final/environment-input.json", sha256 := "14a147c1d6141721547092a9a835249969aa1f82c8f57f9ed0a2b0522f7aaa56" },
    { name := ".lake/formal-comparison/final/new-environment-grouped.json.inner/input.json", sha256 := "2ecf2051d112503637b9d3c1a6201bd66f91df4568a95faff3cef068e3f96a1a" }
  ]
  binarySha256 := #[
    { name := "before", sha256 := "fab48b6e03dd59c5a5335c89be2686cbaf4e1d60123d4bb547f430b9222facfc" },
    { name := "after", sha256 := "5bd2b2fad615d6ccac5d68bc36c716bb26ba35667e31ebe170a99d0783cfe736" },
    { name := "legacy", sha256 := "becd57658a2d232dc158fada7fc977bdff27ae8834e6a80f5db82f18dea05024" }
  ]
  sourceSha256 := #[
    { name := "crates/aiur/src/memory.rs", sha256 := "c3f7cf99ff4f7ad2050575b3a692e5262d13044f27e540655c47e6f054da6f13" },
    { name := "crates/aiur/src/execute.rs", sha256 := "5e5b2bd5b0848c99ef509d03baace69f61c282eabdf330a5ae422436b3be8f77" },
    { name := "crates/aiur/src/trace.rs", sha256 := "e9928c4875ed041cc93040fa18f50a50d7ecce3784c523873da23da57b397443" },
    { name := "crates/aiur/src/trace/plan.rs", sha256 := "ba27c6fb8f514cc2503af28d23c405fffcdb4c2505185c5b664df49e2305e7f0" },
    { name := "crates/aiur/src/trace/stark.rs", sha256 := "8f4bb1b92fe8d32593244bb3c6be041ab19a2442b33a7275495449fbf3713865" },
    { name := "crates/aiur/src/trace/stark/rom.rs", sha256 := "c5481deb55dc05566eee2a11e9179be7da5c982f5fa2db46f9d193496f13d411" },
    { name := "crates/aiur/src/trace/stark/witness.rs", sha256 := "2aa09d84232e939cdb452fd48732ed1c53e0f86b041ab37eb60937d14b2ee984" }
  ]
  notes := #[
    "Primary trace runs reuse one execution record, with five measured traces after two warmups; single-thread controls use seven samples.",
    "Execution controls reexecute every iteration: seven measured samples for environment, three for recursion, after two warmups.",
    "Peak RSS comes from /usr/bin/time -v and covers the whole benchmark process, not just its trace timer.",
    "All new-Aiur circuit statistics, heights, cells and FFT estimates are identical before/after and across thread counts for each workload.",
    "The final before execution controls and single-thread control were repeated immediately before their after run. Earlier controls and implementation experiments remain in .lake/trace-rom-reuse.",
    "Additional phase profile has three samples after two warmups. Per-circuit spans overlap and are not isolated CPU times; primary benchmarks are uninstrumented."
  ]
  profiledBinarySha256 := "11ffc2ba1bf1ff156b3d119da59ddbd1332b9e83d964167e8e2b987a0a804961"
  profileThreads := 64
  profileSamples := 3
  profileFeatures := "parallel,aiur/trace-profile"
  validation := {
    serialTests := { command := "cargo test --release --locked -p aiur --features stark", passed := 82 }
    parallelTests := { command := "cargo test --release --locked -p aiur --features parallel,trace-profile", passed := 82 }
    clippyProfiledComparison := true
    proofs := #[
      { name := "nat-proof-before", bytes := 5478175, proveIncludingTraceSeconds := 0.228871069, verified := true, sha256 := "536879768e52b1a611089656e5466fdc27db5b281ef729c2296e4a2f389cba28" },
      { name := "nat-proof-after", bytes := 5478175, proveIncludingTraceSeconds := 0.232060764, verified := true, sha256 := "536879768e52b1a611089656e5466fdc27db5b281ef729c2296e4a2f389cba28" },
      { name := "recursion-proof-after", bytes := 3168863, proveIncludingTraceSeconds := 35.192673799, verified := true, sha256 := "e1a67b6847c7770f1f4340253bf5fe8a9c7f1aaa69cca175a9b6e42db6450590" }
    ]
    natProofByteIdentical := true
    clippyDefaultAllTargets := true
    formatting := true
    ordinaryBinaryRestored := true
  }
}

end Benchmarks.FormalAiur.RomReuse
