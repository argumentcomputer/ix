# Removing redundant batch preparation from formal Aiur

Historical record: measured 2026-10-30 against `e2326c95`. This fixes work in
the batch adapter shared by the CPU and CUDA provers. It does not change Aiur
programs, certified circuits, grouping, cryptographic parameters, or proof
formats.

## What the GPU report exposed

The hardware review reported the following three-run medians on an RTX PRO
6000 Blackwell with 96 GB VRAM and 16 CPU threads. Times include trace
generation, proving and verification, excluding execution and setup:

| Workload | Formal CUDA | Formal GPU lookups |
|---|---:|---:|
| `Nat.add_comm` frontier | 0.200 s | 0.186 s |
| 342-constant environment | 1.286 s | 0.680 s |
| Large recursive verifier | 20.288 s | 8.330 s |

These are the user's hardware measurements, not locally reproduced GPU
results. The review directory was not available in the measuring checkout, and
the measuring machine had no NVIDIA device. `AIUR_TRACE_ONLY_LOOKUPS=1` removes
the host lookup buffers in the last column.

There were three concrete inefficiencies in the formal adapter:

1. `generate_stage_1` produces rows efficiently, but batch proving then called
   `SystemWitness::from_stage_1` to reconstruct every lookup buffer. That
   evaluator processes circuits and rows sequentially, interprets the graph,
   and copies arguments even for zero-multiplicity messages. The existing
   `Backend::generate` benchmark measured a different path: fused rows and the
   compiled, parallel lookup writer. It missed this later serial pass.
2. Even a one-shard retained proof copied every stage-one matrix and kept the
   originals for the proof's lifetime. The recursive fixture has 937,960,213
   cells: that copy alone allocates approximately 6.99 GiB.
3. Selecting device-derived lookups unconditionally forced commitment
   regeneration. A single shard therefore repeated its upload, LDE and Merkle
   commitment despite the caller requesting retention. A single shard has no
   other commitments to release between rounds; retaining it needs the same
   peak proving workspace.

Missing generated execution kernels do not explain these measured preparation
costs: execution is outside this timer.

## Changes

Batch lookup reconstruction uses the existing compiled lookup writer,
parallel across circuits and row batches. That writer is compiled from the
actual constraint graph and rejects nonlocal lookup expressions. Shard
boundary selectors in the adapter occur in constraints, not lookup
messages. Tests compare the resulting stage-two witnesses and accumulators
with the independent graph evaluator, including sliced ROMs, fixed-table
padding, inactive circuits, and zero multiplicities.

For a single retained shard, the supplier moves the owned matrices into the
prover. Multi-shard proofs and explicit regeneration still slice their source
matrices. GPU lookup mode honors retention for one shard, including in the
streamed API and resource planner. Multiple GPU shards still regenerate to
bound device residency. Explicit single-shard regeneration remains available
for parity checks.

At `e2326c95`, full host lookup buffers remained the default because they
support the backend's memory-pressure fallback, and `AIUR_TRACE_ONLY_LOOKUPS=1`
was the faster CUDA option when graph evaluation is available. (The
[hardware validation](formal-aiur-gpu-validation.md) later made device lookups
the CUDA default.) Verification and key export ignore this prover-only setting.

## Local measurements

Same environment and real recursive fixtures used in the earlier grouping
measurements; 16 Rayon threads pinned to CPUs 0–15 on an Intel Xeon 6975P-C.
Both binaries use native release builds, identical optional timers and disabled
transparent huge pages. Each number is a median of three independent process
runs. Two trace warmups precede the measured proof in each process. These are
**CPU** measurements of the shared adapter and CPU prover, not new CUDA timings.

| Workload and phase | Before | After |
|---|---:|---:|
| Environment: stage-one population | 0.0332 s | 0.0331 s |
| Environment: source trace copy | 0.1168 s | removed |
| Environment: batch host lookups | 0.7073 s | 0.0491 s |
| Environment: trace + proof + verification | 2.5379 s | 1.7410 s |
| Recursion: stage-one population | 0.8779 s | 0.8821 s |
| Recursion: source trace copy | 2.7461 s | removed |
| Recursion: batch host lookups | 13.0554 s | 0.9287 s |
| Recursion: trace + proof + verification | 40.4244 s | 24.7873 s |

The full measured CPU path improves by 31.4% for the environment and 38.7%
for recursion. Stage-one population is unchanged. The new move-only supplier
takes roughly 1–2 microseconds; the table labels the eliminated matrix copy
as removed. Independently computed phase medians need not sum to the total.

Both saved proofs, verifying keys and claims are byte-identical before and
after, and every circuit statistic is unchanged. All twelve benchmark proofs
verified. The environment proof is 6,557,454 bytes; recursion is 3,168,863 bytes.
Subtracting these CPU timings from the reported GPU totals would not be a valid
GPU measurement.

## Reproduction and validation

[Summary](benchmarks/formal-aiur-gpu-preparation/summary.csv),
[individual runs](benchmarks/formal-aiur-gpu-preparation/runs.json), and
[manifest](benchmarks/formal-aiur-gpu-preparation/manifest.json) preserve the
measurements, binary/input hashes and proof identities.

```sh
cargo build --release --locked -p stark-verifier \
  --features parallel,aiur/trace-profile --example compare
RAYON_NUM_THREADS=16 IX_BENCH_NO_THP=1 IX_BENCH_REUSE_EXECUTION=1 \
  AIUR_TRACE_ONLY_LOOKUPS=0 taskset -c 0-15 target/release/examples/compare \
  .lake/formal-integration/recursion-tuned.json \
  .lake/formal-comparison/final/new-environment-grouped.json.inner/input.json \
  /tmp/recursive-proof.json 1 --prove --save-proof
```

The two `.lake` paths are locally exported artifacts and inputs, not checked-in
files. `aiur/trace-profile` also emits `aiur_prover_profile` events for
`shard_copy` and `shard_lookups`. These timers compile out of normal builds.
For GPU timing, build the same example in a separate target directory with
`parallel,cuda,aiur/trace-profile`, and compare lookup modes 0 and 1.

The hardware gate in `tools/ixvm/check-cuda.py` adds single-shard graph-lookup
retention/regeneration proofs for IxVM, recursion and aggregation, each checked
against a CPU reference. It asserts the requested retention policy was honored.
The existing multi-shard cases remain. Run it through `IX_TEST_CUDA=1
tools/ixvm/check-formal.sh` on the GPU host.

Validation at `e2326c95` passed: 104 targeted Rust tests with parallel
generation and 88 Aiur tests with serial generation; Clippy with warnings
denied; CPU retained, regenerated and single-shard proof/key parity for all
three applications; and the controller gate including complete aggregation.
All three CUDA hosts compiled and linked, and all affected CUDA targets passed
Clippy in the CUDA 13.3.1 development image for SM 80. That was build
validation only. No Lean source, theorem, axiom, or correctness certificate
changed.

The 2026-10-31 [hardware validation](formal-aiur-gpu-validation.md) ran these
single-shard paths on a GPU: proofs and keys match the CPU byte for byte, and
the large recursive verifier takes 4.17 s (host lookups) and 2.72 s (graph
lookups) on CUDA.
