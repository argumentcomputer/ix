# Bounded compiler scaling

This PERF3 reference measures **67 cases, 114 workload/cache rows, and 1,026
fresh-process samples** under unchanged compiler defaults. It covers source
declarations, call depth, branches, allocation work, supplementary checked
IxIR₂ joins, and source admission boundaries. Collection ran from **2026-09-12T18:50:37Z**
to **2026-09-12T19:01:02Z**, with three consecutive sessions of three shuffled blocks.

The [generated report](report.md) contains every case and cache comparison;
the [summary](summary.json) contains every stage's distribution and artifact
counts. All nine blocks completed without failed, retried, or discarded
reference samples. Larger setup probes are retained separately.

## Compiler costs

The independent-declaration family adds closed scalar definitions beside an
unchanged exported identity. The frontend and analysis process the supplied
union; native selection reaches the identity, so the ELF stays 1,240 bytes.
Times below are medians in milliseconds across nine fresh processes.

| Added declarations | IxIR₁ declarations | Source frontend ms | HPT production/check ms | IxIR₂ lowering/check ms |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 4 | 0.14 | 0.07 | 0.07 |
| 32 | 66 | 7.23 | 8.24 | 6.40 |
| 128 | 258 | 101.65 | 133.33 | 96.21 |
| 256 | 514 | 398.24 | 543.39 | 384.13 |
| 352 | 706 | 753.18 | 918.17 | 728.50 |

Several whole-graph phases grow substantially while the selected object size
stays fixed. At 352 added declarations, separate coverage discovery and source
certificate reruns take **20.70 ms**
and **41.80 ms**. Those diagnostics
repeat work already included in the **753.18 ms**
frontend. They do not establish that certificate construction alone dominates
the frontend, and they must not be added to its time.

With all **706 HPT entries** available, the declaration-352 paired cold/warm
median ratio is **1.179** for HPT decoding plus
production/checking, **1.055** for
the primary-stage sum, and **1.039**
for the whole worker. Ratios above one favor the warm run. The complete table
retains small, neutral and adverse comparisons; no overall speedup is claimed.

Warm processes validate persisted HPT evidence against the current graph.
They repeat source certification and subsequent lowering. The leaf-edit
experiments retain exactly **two HPT keys** and rebuild the changed leaf and
its dependent callers: 1, 4, 16, 32, 128, or 318 entries. Cold and warm edited
artifacts match exactly. This demonstrates HPT reuse, not modular source
certificate reuse.

## Evidence and output growth

Source proof terms are erased in the executable. The source coverage database
count is reported separately from actual serialized HPT evidence; no source
proof byte size is invented.

| Added declarations | Source candidates | Source bytes | HPT store bytes | HPT candidate JSON bytes | IxIR₂ snapshot bytes | ELF bytes |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 3 | 161 | 889 | 844 | 450 | 1240 |
| 128 | 130 | 6003 | 57024 | 54438 | 17469 | 1240 |
| 352 | 354 | 16307 | 156032 | 148966 | 47485 | 1240 |

The supplementary join family starts from checked IxIR₂ because ordinary
Ixon recursor lowering emits terminal alternatives in these fixtures. Its
source/HPT columns are absent. Sequential diamonds have linear input growth,
while the current native tree representation duplicates shared continuations.
The emitted target grows quickly:

| Joins | IxIR₂ snapshot bytes | x86 blocks | x86 instructions | Encode/check ms | ELF bytes |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 315 | 28 | 102 | 6.64 | 1760 |
| 4 | 407 | 112 | 378 | 96.04 | 4272 |
| 6 | 499 | 448 | 1482 | 1466.12 | 14304 |
| 8 | 591 | 1792 | 5898 | 23115.97 | 54432 |
| 9 | 637 | 3584 | 11786 | — | — |

Nine joins end after checked native lowering by the fixed experiment policy;
no object was requested there. Ten joins fail native selection. The public
selector reports no admitted scalar interface; the exact message is retained.
The observed expansion and encoding cost justify investigating native CFG
sharing before simply increasing the selector's bounds.

## Admission boundaries

These are boundaries of the named families, not universal declaration limits.

| Family | Accepted boundary | Next observed rejection |
| --- | --- | --- |
| Independent declarations | 352 additions, 354 source candidates, complete ELF | 353 additions: combined source-certificate work 135,287,305 exceeds 134,217,728 |
| Caller chain, source checking | Depth 318 reaches checked IxIR₂, with 322 source candidates | Depth 319: combined source-certificate work 135,413,228 exceeds 134,217,728 |
| Caller chain, native | Depth 32 emits ELF | Depth 33: native call graph exceeds 32 functions |
| Source branches, native | 31 branches emit ELF | 32 branches: native call graph exceeds 32 functions |
| Source branches, canonical construction | 453 branches construct canonical source and reach IxIR₂ | 454 branches: compression input 4,097 exceeds 4,096 units |
| Allocation work, native | Eight construct/consume calls emit ELF | Nine: no admitted scalar interface |
| Candidate count, preflight only | 512 canonical candidates pass structural preflight | 513 exceeds the candidate cap of 512 |
| Checked-IxIR₂ joins | Nine pass selection/lowering; full ELF measured through eight | Ten: no admitted scalar interface |

The candidate fixtures do not claim successful source certification at 512.
A rejected source-construction request retains its family, size and precise
failure; it has no fabricated canonical source or downstream compilation.
Other sampled rejections, including structural native limits, remain in the
full report.

## Measurement and validation

The [versioned protocol](../../../benchmarks/compiler-scaling.md) fixes inputs,
policies, cache states, nine block orders and endpoints before collection.
Each stage sample times one actual public compiler/checker invocation with
`IO.monoNanosNow`. Empty clock pairs are recorded without subtraction; tiny
stages near that control are flagged in the JSON. These are descriptive
medians, quartiles and extrema on one shared host, without confidence intervals
or a CI performance threshold.

The frontend includes checking, erasure, source certification and IxIR₁
lowering. Repeated source diagnostics, HPT certificate replay and snapshot
replay have their own timings. The primary-stage sum omits those repeats and
explicit preflight, which the frontend already performs. It is a sum of the
worker's measured boundaries, not another compiler entry point's latency.

The whole worker includes startup, fixture regeneration/input validation and
artifact IO. Those costs can be large: at allocation size 128, its cold median
is **2818.88 ms**, versus **34.29 ms** for the primary-stage sum.
This envelope must not be attributed to compiler passes. In setup, constructing
size 256 took about 21 CPU seconds; size 512 hit the 120-second CPU guard
before producing canonical source. The frozen allocation matrix stops at 128.
Those setup records remain separate from reference samples and compiler
rejections.

Memory records raw process RSS and reported `VmHWM` at stage boundaries plus
GNU time's final process peak. They include earlier phases, retained artifacts,
diagnostics and IO; they are not isolated per-stage allocation peaks. Raw
`VmHWM` is preserved even when this host reports a small decrease. Across all
reference workers, the largest final process peak was **84.93 MiB**.

The host is an AMD Ryzen 9 7950X3D running Linux 7.1.2/NixOS, microcode
`0xa60120a`, with worker CPU 0 and uncontrolled SMT sibling CPU 16. The recorded
governor is `powersave` under `amd-pstate-epp`, with boost enabled. Workers use
one Lean thread, one malloc arena, a 4 GiB address-space guard, a 2 GiB recorded
RSS ceiling, and CPU/wall limits. Nix validation finished before reference
collection. Other tenants, thermal state and system services remain uncontrolled.

All **27 x86_64 Linux Nix checks** passed, including the new 46-row scaling
smoke gate and its fresh-source replay. Full correctness covers all 67 cases,
ordinary pipeline replay, independently decoded snapshots, four modeled
boundary inputs, parsed ELF execution, and **1,169 independently linked C
calls** across 35 objects. The native harness checks values, saved registers,
caller frames, exact counters, reclamation, guarded workspace and capacity
rejection. Eight artifact/input/stage corruptions and four measurement-record
corruptions are rejected, including changed records with updated outer hashes.

The [reproduction result](reproduction.json) checks exact artifacts, cache reuse,
correctness and reanalysis of the original measurements from a fresh extracted
source directory. It uses an empty environment plus recorded variables and
retained hashed compiler/orchestrator seeds and installed tool identities.
**The compiler executable itself is not rebuilt from Lean by this replay.**
The source archive contains the frozen executable sources and predates the
final results prose and roadmap updates.

## Follow-up

I3 modular source certification is next before increasing monolithic limits.
Its units must bind exact source/dependency roots and policies, independently
check evidence, compose the closed-program preservation result, and reuse only
unaffected evidence after an edit. The present HPT cache supplies a comparison
baseline, not those source-level composition proofs.

The timings also call for separating whole-graph checking/lookup costs from
source certificate work, and for investigating native join sharing. This
experiment changes neither compiler admission defaults nor native lowering
policy.

## Retention and replay

The complete bundle is retained locally as
[the addressed archive](../../../benchmarks/runs/847d192c5cb9793ca05ebdb43e1867b002da823acbc2feaf64b87029326cc9ea.tar.gz),
**314,849,251 bytes**, SHA-256
**`847d192c5cb9793ca05ebdb43e1867b002da823acbc2feaf64b87029326cc9ea`**. It contains **36,455 files**;
`reference/SHA256SUMS` covers 36,454, and the archive digest also
covers that inventory. The archive is excluded from Git. Copy the complete
archive when moving the evidence to another host or storage service.

The [retention record](retention.json) confirms a fresh extraction, every file
checksum, and byte-identical report/summary generation by the relocated runner.
[Validation](validation.json) records the full checks and replay;
[setup probes](setup-probes.json) describe the larger allocation inputs and
their separate resource failure. Full logs and raw observations are in the bundle.

From the repository root with the recorded Nix tools available:

```sh
archive=benchmarks/runs/847d192c5cb9793ca05ebdb43e1867b002da823acbc2feaf64b87029326cc9ea.tar.gz
printf '%s  %s\n' 847d192c5cb9793ca05ebdb43e1867b002da823acbc2feaf64b87029326cc9ea "$archive" | sha256sum --check -
mkdir /tmp/compiler-scaling-retrieved
tar --no-same-owner --no-same-permissions -xzf "$archive" -C /tmp/compiler-scaling-retrieved
/tmp/compiler-scaling-retrieved/reference/run.sh verify-bundle
/tmp/compiler-scaling-retrieved/reference/run.sh analyze /tmp/compiler-scaling-analysis
/tmp/compiler-scaling-retrieved/reference/run.sh reproduce /tmp/compiler-scaling-reproduction
```
