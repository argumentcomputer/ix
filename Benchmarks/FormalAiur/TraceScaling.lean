module

public import Benchmarks.FormalAiur.Types

/-!
Typed manifest for the formal Aiur trace-scaling sweep
(`docs/formal-aiur-trace-scaling.md`).
Replaces `docs/benchmarks/formal-aiur-trace-scaling/manifest.json`.
-/

@[expose] public section

namespace Benchmarks.FormalAiur.TraceScaling

structure Manifest where
  date : String
  baseRevision : String
  cpus : Array Nat
  threads : Array Nat
  samples : Nat
  warmups : Nat
  lscpu : Array LscpuField
  reusedExecution : Bool
  hostLookups : Bool
  thpDisabled : Bool
  artifactInputSha256 : Array NamedSha256
  binarySha256 : Array NamedSha256
  commands : Array (Array String)
  cpuQuota : String
  timingScope : String
  validation : Array String
  sourceSha256 : Array NamedSha256
  deriving BEq, Repr, Inhabited

def manifest : Manifest := {
  date := "2026-10-28"
  baseRevision := "5de73a2353f593ec0d9c4b2bf657f6a39da84081"
  cpus := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
  threads := #[8, 64, 1, 32]
  samples := 3
  warmups := 2
  lscpu := xeon6975pcLscpu
  reusedExecution := true
  hostLookups := true
  thpDisabled := true
  artifactInputSha256 := #[
    { name := ".lake/formal-integration/ixvm-tuned.json", sha256 := "1f8c10da7b10587e985d5166b26ad0c7edd4f4cbdfe0978c7deb237cf6683d9a" },
    { name := ".lake/formal-comparison/final/environment-input.json", sha256 := "14a147c1d6141721547092a9a835249969aa1f82c8f57f9ed0a2b0522f7aaa56" },
    { name := ".lake/formal-integration/recursion-tuned.json", sha256 := "40e88dd1f84e4f119626189e83f8eb181f6ef9875c190f33cdd7853e83c5afe1" },
    { name := ".lake/formal-comparison/final/new-environment-grouped.json.inner/input.json", sha256 := "2ecf2051d112503637b9d3c1a6201bd66f91df4568a95faff3cef068e3f96a1a" },
    { name := ".lake/formal-integration/ixvm-checked.json", sha256 := "114311f43f6fb39a2d5ccc5c4e6fb279d4eb6c08655cd08731c949e7e537fabf" },
    { name := ".lake/formal-integration/recursion-checked.json", sha256 := "ae96efa2ce33a07bd79fc5100395aa09a7f3d5f436ae04ee7be2f6bcd71e2afa" }
  ]
  binarySha256 := #[
    { name := "legacy", sha256 := "becd57658a2d232dc158fada7fc977bdff27ae8834e6a80f5db82f18dea05024" },
    { name := "new", sha256 := "19c3e08f05bbe44f1ec217829c0f62d3c11c032dc89760fe394dfa7ece71bb5d" }
  ]
  commands := #[
    #["taskset", "-c", "0,1,2,3,4,5,6,7", ".lake/build/bin/bench-compare-aiur", "ixvm", ".lake/formal-comparison/final/environment-input.json", ".lake/trace-scaling/sweep/environment-legacy-8.json", "3"],
    #["taskset", "-c", "0,1,2,3,4,5,6,7", "target/release/examples/compare", ".lake/formal-integration/ixvm-tuned.json", ".lake/formal-comparison/final/environment-input.json", ".lake/trace-scaling/sweep/environment-new-8.json", "3"],
    #["taskset", "-c", "0,1,2,3,4,5,6,7", "target/release/examples/compare", ".lake/formal-integration/recursion-tuned.json", ".lake/formal-comparison/final/new-environment-grouped.json.inner/input.json", ".lake/trace-scaling/sweep/recursion-real-new-8.json", "3"],
    #["taskset", "-c", "0,1,2,3,4,5,6,7", ".lake/build/bin/bench-compare-aiur", "recursion", ".lake/formal-comparison/final/new-environment-grouped.json.inner/input.json", ".lake/trace-scaling/sweep/recursion-real-legacy-8.json", "3"],
    #["taskset", "-c", "0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63", "target/release/examples/compare", ".lake/formal-integration/ixvm-tuned.json", ".lake/formal-comparison/final/environment-input.json", ".lake/trace-scaling/sweep/environment-new-64.json", "3"],
    #["taskset", "-c", "0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63", ".lake/build/bin/bench-compare-aiur", "ixvm", ".lake/formal-comparison/final/environment-input.json", ".lake/trace-scaling/sweep/environment-legacy-64.json", "3"],
    #["taskset", "-c", "0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63", ".lake/build/bin/bench-compare-aiur", "recursion", ".lake/formal-comparison/final/new-environment-grouped.json.inner/input.json", ".lake/trace-scaling/sweep/recursion-real-legacy-64.json", "3"],
    #["taskset", "-c", "0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63", "target/release/examples/compare", ".lake/formal-integration/recursion-tuned.json", ".lake/formal-comparison/final/new-environment-grouped.json.inner/input.json", ".lake/trace-scaling/sweep/recursion-real-new-64.json", "3"],
    #["taskset", "-c", "0", ".lake/build/bin/bench-compare-aiur", "ixvm", ".lake/formal-comparison/final/environment-input.json", ".lake/trace-scaling/sweep/environment-legacy-1.json", "3"],
    #["taskset", "-c", "0", "target/release/examples/compare", ".lake/formal-integration/ixvm-tuned.json", ".lake/formal-comparison/final/environment-input.json", ".lake/trace-scaling/sweep/environment-new-1.json", "3"],
    #["taskset", "-c", "0", "target/release/examples/compare", ".lake/formal-integration/recursion-tuned.json", ".lake/formal-comparison/final/new-environment-grouped.json.inner/input.json", ".lake/trace-scaling/sweep/recursion-real-new-1.json", "3"],
    #["taskset", "-c", "0", ".lake/build/bin/bench-compare-aiur", "recursion", ".lake/formal-comparison/final/new-environment-grouped.json.inner/input.json", ".lake/trace-scaling/sweep/recursion-real-legacy-1.json", "3"],
    #["taskset", "-c", "0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31", "target/release/examples/compare", ".lake/formal-integration/ixvm-tuned.json", ".lake/formal-comparison/final/environment-input.json", ".lake/trace-scaling/sweep/environment-new-32.json", "3"],
    #["taskset", "-c", "0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31", ".lake/build/bin/bench-compare-aiur", "ixvm", ".lake/formal-comparison/final/environment-input.json", ".lake/trace-scaling/sweep/environment-legacy-32.json", "3"],
    #["taskset", "-c", "0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31", ".lake/build/bin/bench-compare-aiur", "recursion", ".lake/formal-comparison/final/new-environment-grouped.json.inner/input.json", ".lake/trace-scaling/sweep/recursion-real-legacy-32.json", "3"],
    #["taskset", "-c", "0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31", "target/release/examples/compare", ".lake/formal-integration/recursion-tuned.json", ".lake/formal-comparison/final/new-environment-grouped.json.inner/input.json", ".lake/trace-scaling/sweep/recursion-real-new-32.json", "3"],
    #["taskset", "-c", "0-63", "target/release/examples/compare", ".lake/formal-integration/ixvm-checked.json", ".lake/formal-comparison/final/environment-input.json", ".lake/trace-scaling/sweep/environment-new-before-64.json", "3"],
    #["taskset", "-c", "0-63", "target/release/examples/compare", ".lake/formal-integration/recursion-checked.json", ".lake/formal-comparison/final/new-environment-grouped.json.inner/input.json", ".lake/trace-scaling/sweep/recursion-real-new-before-64.json", "3"]
  ]
  cpuQuota := "No quota: cpu.max is max 100000 at the session and both parent cgroups"
  timingScope := "Trace planning, main rows and host lookup buffers; excludes execution, compilation, key/setup and destruction. Reuses one immutable execution record per process; still regenerates every trace."
  validation := #[
    "Both record-reuse smoke proofs verify with the same circuit shapes as normal execution",
    "Circuit heights, widths and cell counts invariant under thread count for each backend/workload",
    "Nullable execution sample summaries supported",
    "Clippy passes with warnings denied for the new comparison example and legacy FFI library"
  ]
  sourceSha256 := #[
    { name := "crates/ffi/src/aiur/benchmark.rs", sha256 := "1a9008c899ef6dea39d298e2728c709298d3265532b9a1fa6d42dfbb43256fb5" },
    { name := "crates/stark-verifier/examples/compare.rs", sha256 := "2b3522f834df44149a50088631656859a02659198d12aa4a3771b4113f60f4c0" },
    { name := "tools/ixvm/compare-results.py", sha256 := "b640f1a1ff0ad339c60ac39ffca1fd04635f283da0c31c5e4f39605a48de0645" },
    { name := "tools/ixvm/trace-scaling.py", sha256 := "cbf37fd568710e30893e925f89b21914824daa8a5a603ab002f4a964ad63a7ff" }
  ]
}

end Benchmarks.FormalAiur.TraceScaling
