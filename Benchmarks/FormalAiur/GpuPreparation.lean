module

public import Benchmarks.FormalAiur.Types

/-!
Typed manifest for the formal Aiur GPU-preparation measurements
(`docs/formal-aiur-gpu-preparation.md`).
Replaces `docs/benchmarks/formal-aiur-gpu-preparation/manifest.json`.
-/

@[expose] public section

namespace Benchmarks.FormalAiur.GpuPreparation

structure Validation where
  parallelRustTestsPassed : Nat
  serialAiurTestsPassed : Nat
  cpuParityReport : String
  controllerReport : String
  cudaBuild : String
  cudaHardwareValidated : Bool
  leanSourcesChanged : Bool
  deriving BEq, Repr, Inhabited

structure Manifest where
  revision : String
  threads : Nat
  affinity : Array Nat
  gpuAvailable : Bool
  cpu : String
  rustc : String
  cudaHardwareValidated : Bool
  environment : Array EnvVar
  flags : String
  measurement : String
  baselineChanges : String
  localRawDirectory : String
  binarySha256 : Array NamedSha256
  inputSha256 : Array NamedSha256
  identities : Array WorkloadIdentity
  proofKeyClaimAndCircuitShapesIdentical : Bool
  validation : Validation
  deriving BEq, Repr, Inhabited

def manifest : Manifest := {
  revision := "e2326c95d746c345e9a2ecc8b19197a4f2a2e043"
  threads := 16
  affinity := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  gpuAvailable := false
  cpu := "Intel Xeon 6975P-C"
  rustc := "rustc 1.98.1 (48a229cea 2026-09-01)"
  cudaHardwareValidated := false
  environment := #[
    { name := "RAYON_NUM_THREADS", value := "16" },
    { name := "IX_BENCH_NO_THP", value := "1" },
    { name := "IX_BENCH_REUSE_EXECUTION", value := "1" },
    { name := "AIUR_TRACE_ONLY_LOOKUPS", value := "0" }
  ]
  flags := "--release; -Ctarget-cpu=native; features parallel,aiur/trace-profile"
  measurement := "CPU trace generation, batch proving and verification. Execution and setup excluded. Same lookup/copy instrumentation in both binaries. Three process runs per workload/version, each with two trace warmups."
  baselineChanges := "e2326c95 plus optional phase timers only"
  localRawDirectory := ".lake/gpu-followup-20261030"
  binarySha256 := #[
    { name := "baseline", sha256 := "e27d665db9f1154fbd5f39161e1289b8ed26d7b65f56dbec97a7492a531fc251" },
    { name := "fixed", sha256 := "6d1385fd36d2ddc9264b3049a4ae49c0d1a4a4aedb6db1c4c23df86e9ec217f3" }
  ]
  inputSha256 := #[
    { name := ".lake/formal-integration/ixvm-tuned.json", sha256 := "1f8c10da7b10587e985d5166b26ad0c7edd4f4cbdfe0978c7deb237cf6683d9a" },
    { name := ".lake/formal-integration/recursion-tuned.json", sha256 := "40e88dd1f84e4f119626189e83f8eb181f6ef9875c190f33cdd7853e83c5afe1" },
    { name := ".lake/formal-comparison/final/environment-input.json", sha256 := "14a147c1d6141721547092a9a835249969aa1f82c8f57f9ed0a2b0522f7aaa56" },
    { name := ".lake/formal-comparison/final/new-environment-grouped.json.inner/input.json", sha256 := "2ecf2051d112503637b9d3c1a6201bd66f91df4568a95faff3cef068e3f96a1a" }
  ]
  identities := #[
    { workload := "environment", proofSha256 := "68c9ab5d23678f921a6af89d2a65dd76356f50b1218d823c2913849b8a708072", keySha256 := "50760291ae2c66b2564f7c494f81a31cf377cc125fbbd9382d86d4c370378143", claimsSha256 := "3bf7b58d3da6199546ac0ac885d60323969d3867c08bbfc5ac0e12dacb46a4c9" },
    { workload := "recursion", proofSha256 := "e1a67b6847c7770f1f4340253bf5fe8a9c7f1aaa69cca175a9b6e42db6450590", keySha256 := "21083c7b19de3e0a83c647e5a5420d34c2df2aab618aa7de327cf96670fc0121", claimsSha256 := "b86c6d532256574ab4f3c0d757b301215be733dd5943d105371cd35147907f64" }
  ]
  proofKeyClaimAndCircuitShapesIdentical := true
  validation := {
    parallelRustTestsPassed := 104
    serialAiurTestsPassed := 88
    cpuParityReport := ".lake/orchestration-final/cuda-check-7g951y0z/report.json"
    controllerReport := ".lake/orchestration-final/controller-check-67ry6a6t/report.json"
    cudaBuild := "CUDA 13.3.1 development container; SM 80; ixvm-proof, stark-verifier, ix-prover release build/link and all-target Clippy"
    cudaHardwareValidated := false
    leanSourcesChanged := false
  }
}

end Benchmarks.FormalAiur.GpuPreparation
