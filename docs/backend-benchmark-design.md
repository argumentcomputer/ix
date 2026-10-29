# Lean checking backend comparison

Compare Ix/Aiur, SP1 and Zisk on one AWS `g7e.8xlarge` instance with a single
NVIDIA RTX PRO 6000 Blackwell Server Edition GPU. Start with `Nat.add_comm`
and its dependency closure, then all of Init. Measure a fresh proof through
the terminal PLONK stage, then independently verify it against the expected
workload. Include zkPi only as a published-results reference. Mathlib and
multi-GPU scaling are later extensions outside the initial matrix.

This is the benchmark protocol and implementation plan. The comparison runner
and restored zkVM adapters are not implemented or validated yet. No timings in
this document are new measurements.

These instructions do not authorize provisioning, builds or benchmark runs.
Execution requires a separate request and agreement on the machine-time budget.

## Source pins and reusable code

| Component | Inspected revision | Role |
| --- | --- | --- |
| Ix `kzg-bn254` | `cfc35206eed4502ef171e6892debb145e1be5aea` | Base of `bench/lean-backend-comparison`; current Rust kernel and complete CUDA proof pipeline |
| Ix `archive/sp1-zisk` | `67fe4edd275b06092b3dfd690b17b7782ba6f83a` | Preserved `sp1/` and `zisk/` workspaces, guests, hosts, sharding and aggregation |
| SP1 upstream | `a094cb0a44e29b6075219bf5d8626ec3a01aef0b` | Inspected SDK version 6.10.0; CUDA and terminal PLONK APIs |
| Zisk upstream | `1e22630bb7e143c30705a1603ed87cfd3da8c6ec` | Inspected SDK version 1.3.2-alpha; CUDA, PLONK and BLAKE3 precompile |

The upstream revisions are research candidates, not tested dependency pins.
Freeze the versions actually validated by the pilot, including toolchains,
guest ELFs, CUDA libraries, verifier artifacts and every lockfile.

The integrations were removed in `b4fea97635f1b357b479dd625789eefcd306bbad`
(PR #652). Recover the backend workspaces selectively from the archive;
reverting that entire commit would also restore obsolete CI, Nix and kernel
changes. Keep the current `crates/kernel`, `crates/ixon` and `crates/common`
shared by the native reference and the two zkVM guests.

Useful archive entry points:

- `sp1/guest/src/main.rs`: anon-mode `IxonChecker`, work enumeration and
  committed checking result.
- `sp1/host/src/main.rs`: execution/proving, dependency-closure extraction,
  JSON rows and verification. It currently requests `.compressed()`.
- `zisk/guest/src/main.rs`: anon-mode checking with explicit work selection.
- `zisk/host/src/main.rs` and `zisk/agg-guest/src/main.rs`: manifest-based
  sharding, proof aggregation, coverage checks and guest-key restrictions.
- `Ix/Cli/BenchCmd.lean` at the archive revision: former registry and command
  dispatch. Port its backend entries into the current registry.

## Workloads and proof contract

| Workload | Input | Required coverage |
| --- | --- | --- |
| `nat-add-comm` | `Benchmarks/Compile/CompileInit.lean`, compiled with `--consts Nat.add_comm` | Entire compiled dependency closure, including mutual blocks |
| `init` | `Benchmarks/Compile/CompileInit.lean`, compiled without a selector | Every kernel-checkable declaration in Init |

`InitStd` is a different workload: its existing fixture imports Std and adds
local definitions. Do not relabel its counts or timings as Init. Both initial
workloads use the import-only `Benchmarks/Compile/CompileInit.lean` fixture.

Prepare each `.ixe` once, record its digest and byte length, and feed those
exact bytes to every backend. Keep Lean elaboration/export outside the main
proving clock and report its cost separately. Initial preparation commands,
after building the appropriate binaries and dependencies, are:

```sh
ix compile Benchmarks/Compile/CompileInit.lean --consts Nat.add_comm --out nat-add-comm.ixe
ix compile Benchmarks/Compile/CompileInit.lean --out init.ixe
```

At the base revision, both toolchains select Lean `v4.34.1`. Use that pin for
the initial workloads, subject to successful artifact preparation. A later
Mathlib comparison can use `Benchmarks/Compile/CompileMathlib.lean`; the base
compilation workspace pins Mathlib to
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Its current Aiur benchmark cell
selects individual constants and does not prove the whole environment.

The manifest must pin Lean, Ix, the dependency lockfiles, source fixture, `.ixe` digest,
canonical subject-address set, axiom inventory, work-item count and covered
constant count. Record work items separately from covered addresses: one
mutual-block check covers several addresses. An axiom declaration passing its
typing rules does not prove the axiom; the admitted axiom inventory remains
part of the workload's meaning.

Require zero checking failures and no unresolved dependencies outside the
declared workload policy. Exclude `--skip-deps`, proof-store reuse and altered
claim semantics from the main comparison. Native `ix check-rs` provides the
reference verdict and counts; a proof must also bind to the independently
expected statement and pinned guest/verifier identity.

Sharding may differ by backend to fit guest and prover memory. Record the
partition and require complete coverage with all cross-shard assumptions
resolved inside the verified aggregate. Ix supports structural and canonical
Merkle roots: compare independently reconstructed expected statements for
the same subject set, not raw root bytes produced by different tree layouts.
Any conversion to a shared final statement belongs inside the timed pipeline.

For Init, distinguish an oversized dependency closure from an oversized
individual check. Environment sharding can distribute dependencies; an atomic
check exceeding guest RAM or retained-trace limits needs a different remedy.
The inspected Zisk ASM implementation has 512 MiB guest RAM and a 32 GiB
trace-mapping ceiling. Size its environment shards independently of Aiur's
partition, and test the largest individual work items before attempting full
coverage. More environment shards alone cannot resolve an atomic limit.
See [Zisk's memory and trace constants](https://github.com/0xPolygonHermez/zisk/blob/1e22630bb7e143c30705a1603ed87cfd3da8c6ec/emulator-asm/src/constants.hpp).

## Measurement boundaries

| Measurement | Start and finish |
| --- | --- |
| `prepare` | Input export, backend planning, circuit/key preparation and parameter acquisition; retain separate sub-times |
| `execute` | Decode the prepared input, run the checker and construct its committed result, without proving |
| `prove-plonk` | Fresh host process through saved terminal proof, including input loading, witness generation, all leaf proofs, aggregation and wrapping |
| `verify` | Separate verifier process reading the saved proof and expected statement, with pinned verifier artifacts |

The headline uses `prove-plonk` with prepared keys and fresh proof state.
Report complete verifier-process wall time separately from any in-memory
verification microbenchmark. If the prover performs internal verification,
keep that work inside its process time. Do not subtract a separately timed
execution run from proving or add overlapping internal phase times together.

Backend endpoints:

- Ix: fresh checking proofs and aggregate root, FRI compression, first KZG,
  recursive KZG, terminal BN254 PLONK. Build both the Ix CUDA backends and
  the terminal helper (`IX_CUDA` and `IX_PLONK_CUDA` are independent).
- SP1: `client.prove(...).plonk()`, followed by verification of the saved
  proof and its public values. A compressed SP1 proof is an intermediate
  diagnostic, not the terminal comparison result.
- Zisk: leaf proofs and any guest aggregation, then PLONK wrapping of the
  final result. Keep intermediate proofs in the format accepted by its
  recursive verifier; do not wrap each leaf merely to wrap the root again.

Use the supported optimized hashing path in each release and record it.
The archived SP1 BLAKE3 fork requires `WITHOUT_VK_VERIFICATION=1`; exclude
that configuration from the headline comparison. Upstream SP1 is the first
porting target. A custom-precompile variant needs compatible authenticated
recursion keys and separate labeling. Upstream Zisk now has BLAKE3 support,
but routing the Rust dependency through it still needs explicit integration.

Record the security parameters and setup provenance of every backend. The
shared PLONK endpoint alone does not establish equal soundness or identical
zero-knowledge guarantees. Use ordinary supported parameters, authenticated
Ix Ignition setup and authorized verifier keys. Development SRS, reduced FRI
queries and verifier bypasses are excluded from published measurements.

## Cache and hardware policy

Reuse immutable SRS, compiled circuits, fixed preprocessing and proving keys.
Start every repetition without workload-specific proofs, joins or resumable
checkpoints. For Ix this includes a unique `AIUR_LANES_CACHE_DIR`, fresh
compression outputs and `--no-index`; inspect all resume paths before running.
The common content-addressed store need not be deleted. If isolation needs a
new path override, implement it explicitly rather than changing `HOME`.

Report first-use preparation separately. With prepared artifacts, launch a
fresh process for each measured repetition; record that OS page-cache state
is uncontrolled. If measuring a persistent warm server, give that a separate
row and charge its startup to the first-use result. Include backend subprocesses
and GPU servers in resource accounting.

Use the same `g7e.8xlarge` instance for all three backends. AWS lists the
following allocation in its [G7e specifications](https://aws.amazon.com/ec2/instance-types/g7e/):

| Resource | Allocation |
| --- | --- |
| GPU | 1 × NVIDIA RTX PRO 6000 Blackwell Server Edition |
| GPU memory | 96 GB |
| vCPUs | 32 |
| Host memory | 256 GiB |
| Local instance storage | 1 × 1.9 TB NVMe |

Run backend trials sequentially, with exclusive use of the GPU. Use one Aiur
GPU lane and select device 0 for KZG and the other GPU backends. Leave CPU
thread counts at their defaults. Fix host-memory and time limits before
measurement, allowing headroom within the 256 GiB allocation; account for
child processes and shared-memory traces under the same limit.

Record the instance type, region/AZ, AMI, actual CPU/GPU identification,
reported memory, driver/toolkit, storage and power settings. Place run outputs
and proving caches on the local NVMe and record free space before a run.
Archive results to durable storage after measurement. Record backend scheduling
choices explicitly. The initial comparison uses no additional GPUs or remote
proving capacity.

After an approved feasibility pilot, aim for three measured repetitions per
feasible cell and report median plus min/max. Rotate backend order. If a
large workload justifies only one run, label it `n=1`. Choose time and memory
limits before runs; preserve timeout, OOM, unsupported and verification-failure
outcomes. A missing result is not a zero and is not a speedup denominator.

## Results and integration

Extend `ix bench` and its JSON row contract, keeping the benchmarks local and
on demand initially. Add a true whole-environment scope and a `prove-plonk`
mode; the existing per-constant `aiur prove` cell has a different endpoint.
The following is the intended interface, not an implemented command:

```text
ix bench run --backend <aiur|sp1|zisk> --env <workload> --mode prove-plonk
```

Retain raw rows, commands, logs and proof artifacts beneath a unique run
directory. Attach provenance outside the existing numeric metric map.
Required result fields are:

- Backend/revision, workload digest, statement identity, proof format,
  configuration digest, repetition and outcome.
- Wall seconds for preparation, execution, complete proving and independent
  verification; diagnostic phase seconds where available.
- Process-tree peak host memory and per-device sampled peak VRAM, including
  sampling interval. Do not sum sequential process peaks or present sampled
  VRAM as an exact allocation maximum.
- Final proof bytes, public-input bytes and complete transport-envelope bytes
  as separate fields; optionally verification-transaction gas measured under
  identical EVM settings.
- Unique covered constants, shards, leaf/join counts, cache policy and links
  to verification evidence. Cycles and FFT costs are backend diagnostics,
  not a common throughput unit.

Main report layout:

| Workload | Backend | GPUs | Status / n | Prove PLONK median [min, max] | Host peak | VRAM peak | Proof / public bytes | Verify wall |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Nat.add_comm + closure | Ix / SP1 / Zisk, separate rows | 1 | unmeasured | | | | | |
| Init, whole environment | Ix / SP1 / Zisk, separate rows | 1 | unmeasured | | | | | |

This is six initial cells: two workloads across three backends, all on
`g7e.8xlarge`. Mathlib and multi-GPU rows require a later scope extension.

## zkPi: published reference only

[Laufer, Ozdemir and Boneh, zkPi, §7.2 and Figures 10–12](https://eprint.iacr.org/2024/267.pdf)
report 1,000 sampled theorems per library on GCP `e2-highmem-8` (described as
8 cores, 64 GB), with a 30-minute limit per attempt including setup.

| Published workload | Success | Proving time among successes |
| --- | ---: | --- |
| stdlib sample | 57.9% | Up to approximately 4.5 minutes per theorem |
| mathlib sample | 14.1% | Up to approximately 4.5 minutes per theorem |

The library experiments prove each theorem from first principles; most of
the attempt limit is spent in setup. Figure 10's separate examples report
240-byte proofs; `and.comm` takes 23.28 s to prove and 0.15 s to verify,
excluding setup. Those examples use some custom definitions and public axioms.

Treat these as historical context. They measure individual theorems rather
than one aggregate proof of a whole library. No new zkPi runs or direct
speedup ratios are planned. The ePrint PDF download returned HTTP 403 during
inspection; the figures above were available in its indexed text, with
coverage also confirmed by the [ePrint abstract](https://eprint.iacr.org/2024/267).

## Implementation sequence and run gate

1. Restore the two isolated backend workspaces and port them to the current
   kernel/Ixon types and selected SDK revisions. Keep dependency resolution
   scoped; do not run a blanket `cargo update`.
2. Make the guests commit complete expected checking results. Validate native
   parity and rejection of changed inputs, nonzero failures, wrong guest keys
   and missing/duplicated shard coverage. Audit Zisk's recursive key binding
   while porting its existing aggregation guest.
3. Add final-proof persistence, independent verification and PLONK selection.
   Integrate process timing, cache isolation and whole-environment runs into
   `ix bench`; preserve existing CI behavior.
4. Validate command construction and result accounting without proving. For a
   separately authorized execution phase, estimate the narrow build and a
   Nat.add_comm pilot for each backend on `g7e.8xlarge`, and obtain agreement
   on that budget before running them. The pilot must reach PLONK and pass
   independent verification with the full dependency closure.
5. Budget an Init feasibility pass using the pilot's observed execution,
   memory and setup costs. Profile the pinned Init workload and check its
   largest individual work items and mutual blocks before choosing backend
   partitions. Account for dependencies proved in other shards; subject-only
   diagnostics do not count as complete workload results.
6. Once the outliers fit, estimate the six-cell matrix and repetitions on the
   single GPU. Obtain machine-time approval before the Init feasibility pass
   or full runs. Preserve incomplete coverage and resource-limit failures in
   the report. Do not infer current feasibility from archived cost models or
   extrapolate zkVM cycles into published proving times.

Existing [Init compression measurements](proof-benchmark-comparison.md)
start from a saved FRI proof and exclude the initial checking/aggregation
path. The [GPU proving measurements](aiur-gpu-proving.md) stop at the aggregate
root. They are useful for sizing stages, but cannot be combined across
different machines/revisions into a measured E2E result.
