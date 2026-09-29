# Shared native emission reference — 2026-09-12

Eight converging joins produce **47 x86 blocks instead of 1,792**, and a
**2,448-byte ELF instead of 54,432 bytes**. The three-process median for x86
encoding and checking falls from **23,674.764 ms to 21.480 ms**. This measures
the same encoder and checker receiving a smaller program.

The physical heap source and snapshot object APIs now default to shared
emission. The original tree emitter remains selectable. Both use the existing
execution, argument-transfer, ownership, workspace, and ELF proof contracts.
[Implementation and API](https://github.com/argumentcomputer/Compilatr.ix/blob/jcb/ixby-archive/docs/native-sharing.md).

## Fixed comparison

The workload is the unchanged `compiler-scaling-joins/1` checked IxIR₂ fixture
from the [earlier scaling reference](../compiler-scaling-2026-09-12/README.md).
It has `3n + 1` input blocks and no heap allocation in the selected function.
Both modes use identical snapshot bytes, input identities, function profiles,
control bounds, and compiler limits. At eight joins the snapshot is 591 bytes.
The export adapter accounts for the same dead closure prefix in both modes.

This is an IxIR₂-origin join experiment; it makes no source-compilation claim
for converging joins. Five ordinary source and four allocating physical CFG
fixtures separately exercise shared emission, with calls and ownership.

| Joins | Tree blocks | Shared blocks | Tree ELF bytes | Shared ELF bytes | Tree encode/check ms | Shared encode/check ms |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 28 | 17 | 1,760 | 1,464 | 6.887 | 3.080 |
| 3 | 56 | 22 | 2,600 | 1,624 | 26.224 | 5.082 |
| 4 | 112 | 27 | 4,272 | 1,792 | 99.149 | 7.369 |
| 5 | 224 | 32 | 7,616 | 1,952 | 381.395 | 10.118 |
| 6 | 448 | 37 | 14,304 | 2,120 | 1,510.545 | 13.599 |
| 7 | 896 | 42 | 27,680 | 2,280 | 6,042.828 | 17.459 |
| 8 | 1,792 | 47 | 54,432 | 2,448 | 23,674.764 | 21.480 |
| 9 | — | 52 | — | 2,608 | — | 25.981 |

Times are medians of three fresh complete worker processes. Shared-only nine
extends the ELF endpoint; the historical tree comparison stops at eight.
There is no baseline-nine ELF timing in this report. Ten still passes snapshot
ownership validation and fails native selection under the unchanged depth-128,
work-4,096 limits. The rejection is retained verbatim in
[summary.json](summary.json).

For this fixture, shared output grows by five blocks and 18 instructions per
join. At eight joins, instructions fall from 5,898 to 177 and text from 53,579
to 1,596 bytes. Input/output observations and executed byte-step counts match
between modes. Linked execution is a correctness check, not a throughput
measurement.

## Costs and limits

At eight joins, median stage times are:

| Stage | Tree ms | Shared ms |
| --- | ---: | ---: |
| Selection | 0.277 | 0.278 |
| Native emission | 0.387 | 0.325 |
| Native certificate check | 0.510 | 0.425 |
| x86 encoding/checking | 23,674.764 | 21.480 |
| ELF writing/checking | 0.076 | 0.067 |

The three encoding/checking samples span
23,637.696–23,750.052 ms for tree emission and
21.397–21.989 ms for shared emission.
Every raw stage sample is retained in [summary.json](summary.json).

The selector, emitter, and native plan checker still process the unfolded
tree. At shared nine, emission takes 0.671 ms and
native certificate checking 0.880 ms,
roughly twice their shared-eight costs. Linear **emitted code** for this family
does not establish linear compiler work or admission of larger CFGs.

Hash-table work can cost more on small inputs. At three joins, median emission
rises from 12.122 µs to
18.475 µs; encoding/checking still improves.
The allocating `shared-pair` fixture is a neutral artifact case: both modes
produce the same 11 blocks, 540 text bytes, and 1,392-byte ELF. Its compilation
timing was not measured here. These data do not establish a speedup for every
input or compiler phase.

## Method and validation

Measurement ran from **2026-09-12T22:07:55.392408+00:00** to
**2026-09-12T22:09:46.447633+00:00** on an AMD Ryzen 9 7950X3D, Linux 7.1.2,
x86-64. Each worker was pinned to CPU 0 with `LEAN_NUM_THREADS=1`,
`MALLOC_ARENA_MAX=1`, and `LC_ALL=C`. The governor was `powersave`, driver
`amd-pstate-epp`, and boost enabled. The final Nix suite finished before the
measurements. Host load and frequency were otherwise uncontrolled.

The three process wall times were 36.96, 36.88, and 37.19 seconds. GNU time
reported peak RSS of 78,272, 78,884, and 79,368 KiB (maximum 77.508 MiB).
These cover the **complete 15-case worker**: all stages, default-API replay,
semantic and mutation checks, retained artifacts, report hashing, and IO.
They do not isolate either emitter or a compiler phase, and are unrelated to
the generated program's workspace requirement.

Cases ran in increasing join count, tree then shared. Each named stage has one
`IO.monoNanosNow` interval per process. The ordering is fixed, with no
randomization, confidence interval, or per-stage process isolation. Timings
exclude fixture construction, default-API replay, semantic/mutation checks,
report hashing, JSON, and file writes. Do not add medians to infer an end-to-end
latency. [Commands and protocol](https://github.com/argumentcomputer/Compilatr.ix/blob/jcb/ixby-archive/benchmarks/native-sharing.md).

Validation passed on the final implementation:

- All **29 x86-64 Linux Nix checks**, including the unchanged historical
  scaling artifacts and the new shared-emission gate.
- Three workers with identical reports, snapshots, objects, and per-case
  records; all 15 cases match the reviewed reference inventory.
- Physical, typed x86, and parsed-ELF results for six boundary inputs per case;
  every shared emitted block is unique, and 560 instruction/control/coverage
  mutations are rejected per reference worker.
- Independent decoding and ELF inspection, 90 artifact/metadata corruptions,
  15 exact persisted-only recompilations, and **495 linked calls**, using the
  unchanged guarded scaling harness and GCC 14.3.0.
- Both heap modes: 95 source applications, 171 ELF input cases, nine persisted
  reloads, 182 independent corruptions, 36 reload rejections, and 774 linked
  calls each. Shared heap compilation performs 436 certificate checks,
  including mutations to every emitted block.
- A second independent replay from a fresh frozen-source directory, checking
  all **747 source-file identities**, the executable seed, and all 15 objects;
  its 495 linked calls also pass.

`checkCandidate_program` adds an exact-proposal theorem with only `propext`
and `Quot.sound`. Existing physical execution, simultaneous-copy, source,
ownership, and capacity axiom fences remain unchanged. No new native interface
or axiom is introduced. [Validation record](validation.json).

## Provenance and retained replay

The frozen source is base commit `8d46aa231fb7e3ae4350a5cd499c16b762cb675d` plus the
uncommitted implementation captured in `source.tar.gz`. All 747 source files
and 619 recorded code identities remained unchanged through measurement. This
performance documentation was added afterwards. Runtime tools, versions,
linkage, 139 Nix closure paths, commands, process observations, and timestamps
are recorded in the raw data and summarized in [provenance.json](provenance.json).

- Frozen source archive: **3,535,478 bytes**,
  SHA-256 `aee5236d1ae03872bfdd20626eaecc5587eedab526765e2d622cab66158c7e6e`.
- Retained raw archive: **107,845,184 bytes**,
  SHA-256 `28326a7622433f3577c8943e9ea883bc324d6a89149977f74093066246ea84b3`.

| Executable seed | Bytes | SHA-256 |
| --- | ---: | --- |
| `check-native-sharing` | 120,360,800 | `a4fbe615abcefac9fdbc5362b2d16fb1e3fb89e0553a405d079e6d3773a53857` |
| `heap-snapshot-object` | 123,399,240 | `8ad832138d1ae6b021e69430e28da86daa8526227e2601f4da25fcadb42da6d1` |
| `native-sharing` | 124,519,376 | `5ebfa336fefdce3b4dda1756b3d1f07a699a4307759b5d51d89d720005144686` |

The raw archive is stored locally at
`benchmarks/runs/native-sharing-2026-09-12.tar.gz`, ignored by version control
and **not uploaded**. It contains all three runs, inventories, source snapshot,
executable seeds, correctness/replay evidence, build logs, and `collect.py`.
The collector uses Python's standard library only for measurement and archive
orchestration; compilation, certificates, semantic checks, and independent
artifact/native gates are the Lean programs in the repository.

To inspect the retained seed replay, unpack into a fresh location and run:

```sh
tar -xzf benchmarks/runs/native-sharing-2026-09-12.tar.gz -C /tmp
python3 /tmp/native-sharing-reference-001/collect.py replay \
  --raw /tmp/native-sharing-reference-001
```

Replay verifies source and seed identities, extracts a fresh source directory,
and reconstructs the exact objects using the persisted-only consumer and the
recorded runtime tools. This is **seed replay**, not a rebuild of Lean or the
compiler. Reproducing from current source uses the ordinary Lake/Nix commands
in the protocol. The archive and its recorded Nix runtime closure are needed
for the retained-seed command above.
