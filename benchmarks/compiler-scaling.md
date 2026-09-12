# Compiler scaling protocol, version 1

This measures the executable compiler and its checked artifacts under the
existing default policies. It supplies a baseline for modular source
certification (I3); it does not increase the 512-candidate limit or add a source
certificate cache. No timing threshold is enforced in CI.

## Workloads and endpoints

`Benchmark.ScalingSources` creates canonical Ixon constants and retains their
actual serialized bytes, content addresses, literal inputs, and fixed policy.
Every replay decodes those bytes and checks them against the generator. Source
checking, erasure, certification, addressing, HPT, ownership lowering, native
selection, encoding, and ELF writing use the ordinary checked APIs.

If canonical source construction itself exceeds the default compression
budget, retain the requested family/size and exact rejection in a separate
input format. Such a row has a `source-construction` measurement and no
canonical source or downstream compilation claim. The branch matrix includes
adjacent sizes 453/454 at this earlier boundary.

| Family | Parameter | Expected runtime result | Endpoint |
| --- | --- | --- | --- |
| declarations | independent scalar declarations beside an exported identity | argument | ELF, or first compiler rejection |
| call-depth | leaf plus a chain of callers, listed before their dependencies | argument | ELF, or first compiler rejection |
| branches | nested, nonrecursive predecessor recursors | saturating `argument - size` | ELF, or first compiler rejection |
| allocations | calls that construct and consume one leaf each | argument | ELF, or first compiler rejection |
| candidates | minimal canonical inductive projections | not executed | source preflight only |
| joins | sequential diamonds with converging ownership edges | saturating `argument - size` | ELF through size 8; native lowering above size 8 |

The call-depth edit changes one leaf projection from field 1 to field 0. Both
fields contain the runtime argument. The result is unchanged, while the leaf
and its callers receive new source/IR identities. A separate identity function
and the data declarations stay unchanged. The checker compares the exact
intersection, new keys, and removed keys in the HPT stores.

The ordinary Ixon recursor lowering emits terminal alternatives and these
source families have no converging joins. The supplementary `joins` family
therefore starts at **checked IxIR₂**, with explicit separate provenance. It
has no source or HPT measurements. The endpoint after native lowering for sizes
above eight is a fixed experiment bound on encoder cost, not a compiler
rejection or an altered compiler limit. Its actual target block/instruction
counts and selector rejection are retained.

The allocation family stops at size 128 in the frozen reference matrix.
Setup probes at 256 spent about 21 seconds constructing canonical input;
size 512 hit the 120-second process CPU guard during construction. Retain
those setup process records separately. The latter is a generator resource
failure, not a compiler rejection or a timed reference sample. No completed
sample from the frozen reference schedule is dropped or retried.

The candidate family isolates the inclusive candidate preflight limit from
the combined source-node charge. Acceptance there is **preflight only**; it
does not assert that the complete compiler can certify 512 such declarations.
The other families include adjacent source-work and native admission cases.
All exact inputs, sizes, edit variants, and order are defined by
`Benchmark.CompilerScaling.cases`; the matrix is checked on every replay.

## Measurements

Each sample runs one workload/cache row in a fresh process on one pinned Linux
CPU. The full profile has three consecutive sessions, each containing three
complete blocks. A block includes every row once. Its Fisher–Yates order uses
seed `2930098127 + block * 104729`, retained in `freeze.json` before any samples
are collected. The smoke profile has one session and one block. Sessions are
consecutive batches on the same shared host, not independent machines/days.

Workers set `LEAN_NUM_THREADS=1`, `MALLOC_ARENA_MAX=1`, and `LC_ALL=C`. The
launcher applies 4 GiB address-space, 120-second soft/125-second hard CPU, and
180-second wall limits, with a five-second termination grace period. A failed
process stops the run; partial stage journals, process logs and completed
samples remain. Core dumps are disabled; recorded process RSS above 2 GiB
fails validation. The virtual-address allowance accommodates runtime thread
reservations and is distinct from resident memory. No failed/slow sample is
silently removed or retried.

`IO.monoNanosNow` surrounds one invocation at each public boundary. Two hundred
empty clock pairs establish an observed minimum; it is never subtracted.
Stages shorter than 100 such pairs are flagged in the analysis. This is a
latency/scaling experiment, not the native-throughput protocol's 100 ms loop.
Small phase estimates can be dominated by clock and scheduling noise.

| Stage | Scope |
| --- | --- |
| source-construction | repeat a request rejected by canonical source addressing; rejected-input rows only |
| source-preflight | explicit structural admission; repeated inside the frontend |
| source-to-ixir1 | full validated source frontend, including usage/address checks, erasure, source certificates, and IxIR₁ lowering/addressing |
| diagnostic-coverage-discovery | fresh rerun of dependency-order discovery over the actual erased program |
| diagnostic-source-certificate | fresh erasure/coverage/member certification in that order; proof terms are erased at runtime |
| cache-decode | decode retained HPT store bytes; empty initialization in cold runs |
| hpt-cache-produce-check | cache scheduling, hit validation, missing evidence production, and checked materialization |
| hpt-certificate-check | separate replay of the HPT certificate checker |
| sidecars | ordinary sidecar assembly from that exact checked HPT production |
| ixir2-lower-check | ownership lowering, validation, and trace checks |
| snapshot-ownership-check | initial checked-IxIR₂ admission, join inputs only |
| snapshot-encode-check | canonical wire encoding with bounded-fit checking |
| snapshot-decode-check | bounded addressed decode and ownership validation |
| native-export / native-select / native-lower | export resolution, physical interface selection, and checked native lowering |
| x86-encode-check / elf-write-check | checked instruction stream encoding and checked ELF construction |

The source diagnostic phases rerun work already included in the frontend.
The primary-stage sum omits these diagnostics, explicit source preflight, HPT
certificate replay, and snapshot replay. It is a sum of measured worker
boundaries, not the whole-process latency of another compiler entry point.
GNU `time` and an external monotonic envelope separately record the complete
worker, including startup, input loading/generation checks, diagnostics and
artifact IO. No subtraction is used to attribute phase costs.

Linux `/proc/self/status` records resident memory before/after each stage and
the **reported process high-water RSS** through that point. These include
earlier phases, diagnostics, retained artifacts, and IO. They are not isolated
per-stage allocation counts or incremental peaks. GNU `time` also records the
complete process peak. Raw `VmHWM` observations are preserved without forcing
monotonicity: this measurement host occasionally reports a slightly lower
value at a later boundary. All memory units are explicit (KiB, or MiB in tables).

Cold means no HPT evidence. Warm means loading the prior canonical HPT store
in a fresh process and validating each hit against the current program. It
does not mean a flushed OS page cache, a durable directory-cache benchmark, or
cached source certification. Input file reading is outside the internal
phase clocks; store decoding is measured. Artifact dumping is outside those
clocks and remains in the process envelope. Warm cache write statistics count
logical missing/rejected cache records, not the separately retained full dump.

Source certificates retain executable address databases but erase their proof
terms. Report database counts and deterministic work charges, not invented
proof byte sizes. HPT candidate JSON byte counts describe the actual retained
JSON; canonical HPT store, IxIR₂ snapshot, and ELF byte counts describe their
retained binary formats. Count actual emitted declarations, instructions,
branches, joins, and allocation/call sites as well as the source parameter.

Analysis retains all samples and reports medians, quartiles, extrema, and
paired cold/warm ratios within each block. HPT ratios include decoding plus
cache production/checking. Primary-stage and whole-process ratios are separate.
With three consecutive sessions on a shared host, no confidence interval,
causal speedup claim, or dedicated-machine performance guarantee is made.
Affinity, CPU/tool identities, governor/turbo observations, kernel, load, and
environment are retained. Stable environment changes fail the run.
If sandboxed CI lacks sysfs topology, retain the `lscpu` failure as unavailable
diagnostic data; required CPU affinity and process observations still run.

## Correctness and replay

The gate checks the reviewed smoke golden, every actual artifact and stage
identity, and cold/warm byte equality. A fresh ordinary source compilation
must reproduce the phased pipeline's IxIR₁, HPT evidence, and IxIR₂ bytes.
The independent tool-side IxIR₂ decoder checks the complete wire/JSON view.
Source and physical evaluators check four boundary inputs. Complete ELF cases
also replay parsed bytes and link an independent C harness: 31 boundary/random
inputs, two or three capacity rejections, exact arena counters/reclamation,
saved registers, caller frames, and a bounded workspace with guard pages.
Join rows ending after lowering execute the typed target instead of claiming
an unproduced object. Regressions corrupt source/policy, snapshot, HPT evidence,
ELF, phase inventories and timing records.

Retained bundles include canonical inputs/artifacts, raw stage/process records,
the frozen schedule, tool hashes/versions, compiler/orchestrator binaries,
the source archive with its exact file inventory, and the available Nix
closure. Reproduction extracts and checks that source archive, uses an empty
environment plus recorded build variables, and reruns artifact construction
and correctness with the retained hashed compiler seeds. It **does not rebuild
the compiler executable from Lean**. Installed tools must match recorded
hashes. Fresh compilation timings may differ; original performance samples
are reanalyzed and the summary/report must match byte for byte.

```sh
lake build benchmark compiler-scaling
benchmark=.lake/build/bin/benchmark
"$benchmark" compiler-scaling-build benchmarks/runs/scaling/build --profile full
"$benchmark" compiler-scaling-verify benchmarks/runs/scaling/build benchmarks/runs/scaling/correctness
# CORE must be an allowed CPU; the build's environment.json records one.
"$benchmark" compiler-scaling-measure benchmarks/runs/scaling/build benchmarks/runs/scaling/correctness benchmarks/runs/scaling/measured CORE
"$benchmark" compiler-scaling-analyze benchmarks/runs/scaling/build benchmarks/runs/scaling/measured benchmarks/runs/scaling/measured/analysis
"$benchmark" compiler-scaling-reproduce benchmarks/runs/scaling/build benchmarks/runs/scaling/measured benchmarks/runs/scaling/reproduced
"$benchmark" compiler-scaling-smoke /tmp/compiler-scaling-smoke
```

The explicit `compiler-scaling-golden BUILD OUTPUT` command writes a candidate
golden for review. Verification never updates the checked-in golden itself.
