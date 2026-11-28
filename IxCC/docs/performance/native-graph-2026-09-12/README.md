# Shared selection and certificate reference — 2026-09-12

Eight converging joins use **33 selected nodes and 33 native certificate rows**,
down from **1,276** of each in the previous shared emitter. Median selection
takes **0.404 → 0.068 ms**;
native certificate checking takes **0.418 → 0.026 ms**.
The emitted ELF is identical. Graph compilation admits **42 joins**; the
previous selector still rejects ten under its original expansion budget.

Physical heap source and snapshot object APIs now default to `.graph`.
The `.shared` and `.tree` paths remain available. Existing physical and
source-to-ELF statements and proof assumptions remain in force.
Implementation, APIs, and limits (`docs/native-graph.md` on the archive branch of the pre-merge Compilatr.ix repository).

## Fixed comparison and representation

The unchanged `compiler-scaling-joins/1` family begins at checked IxIR₂ and has
`3n + 1` source blocks. Both modes share canonical snapshots, source identities,
native templates, block interning, observations, and executed byte-step counts.
Each overlapping pair produces identical text and ELF bytes. The fixture
allocates no heap cells in the selected function. Five ordinary source and
four allocating physical fixtures exercise the graph compiler separately.

The baseline is the previous `.shared` emitter with tree selection and native
certificates. The reference matrix contains both modes at joins 2 through 9,
then graph-only 10, 12, 16, 24, 32, 40, and 42: 23 objects per process.

| Joins | Baseline nodes/rows | Graph nodes/rows | Graph edges | Depth | x86 blocks | ELF bytes |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 16 | 9 | 10 | 7 | 17 | 1,464 |
| 4 | 76 | 17 | 20 | 13 | 27 | 1,792 |
| 6 | 316 | 25 | 30 | 19 | 37 | 2,120 |
| 8 | 1,276 | 33 | 40 | 25 | 47 | 2,448 |
| 9 | 2,556 | 37 | 45 | 28 | 52 | 2,608 |
| 16 | — | 65 | 80 | 49 | 87 | 3,760 |
| 32 | — | 129 | 160 | 97 | 167 | 6,384 |
| 42 | — | 169 | 210 | 127 | 217 | 8,024 |

This family has `4n + 1` graph nodes and native certificate rows, `5n` graph
edges, and depth `3n + 1`. The baseline logical tree has `5 × 2^n − 4` nodes.
Both emitted programs have `5n + 7` native blocks. At eight joins, both have
177 instructions, 1,596 text bytes, and a 2,448-byte ELF.

At eight joins, selected representation inspection shrinks from
**734,613 to 21,675 bytes**;
native certificate inspection shrinks from
**905,849 to 1,528 bytes**.
At 42 joins these are 112,243 and 7,311 bytes. These retained JSON files measure
diagnostic representations, not memory usage. They are not stable certificate
codecs or proof recovery inputs; replay starts from canonical IxIR₂ bytes.

## Phase costs and remaining limits

Median stage times at eight joins, across three fresh complete processes:

| Stage | Baseline ms | Graph ms |
| --- | ---: | ---: |
| Selection | 0.404 | 0.068 |
| Native emission | 0.325 | 0.027 |
| Native certificate check | 0.418 | 0.026 |
| x86 encoding/checking | 20.033 | 20.120 |
| ELF writing/checking | 0.066 | 0.066 |

The three eight-join selection samples span
0.370–0.467 ms for the baseline and
0.068–0.070 ms for graph mode.
All eight stages, individual samples, medians, and ranges are retained in
[summary.json](summary.json).

| Graph joins | Selection ms | Emission ms | Native check ms | x86 encode/check ms |
| ---: | ---: | ---: | ---: | ---: |
| 8 | 0.068 | 0.027 | 0.026 | 20.120 |
| 9 | 0.065 | 0.030 | 0.027 | 24.291 |
| 10 | 0.077 | 0.036 | 0.034 | 29.339 |
| 16 | 0.102 | 0.044 | 0.045 | 68.312 |
| 24 | 0.137 | 0.061 | 0.059 | 143.289 |
| 32 | 0.194 | 0.066 | 0.074 | 248.773 |
| 40 | 0.209 | 0.084 | 0.081 | 380.608 |
| 42 | 0.278 | 0.098 | 0.099 | 418.976 |

Selection, emission, and native checking avoid path expansion on this family.
Encoding/checking still dominates and grows much faster than graph size over
this range. Its input and output bytes are unchanged between modes on common
cases. These data do not establish linear whole-compiler complexity or a
runtime throughput improvement; native execution is tested for correctness.

There is a small-input cost. At two joins, median selection is
16.852 µs for the baseline and
43.031 µs for graph mode. The graph selection
inspection is also larger: 5,739 versus 5,542 bytes. The nine allocating heap
fixtures are neutral artifact cases: all text hashes, sizes, entries, and
source identities match the previous shared goldens. Their compile times were
not measured here.

Default per-profile graph bounds are 4,096 nodes, 8,192 edges, and depth 128.
The 42-join graph passes exact limits of 169 nodes, 210 edges, and depth 127.
Reducing each limit by one fails both proposer and checker. A longer cached
path is separately rejected by the checker. Forty-three joins pass wire and
ownership validation but have 130 source blocks, exceeding the unchanged
128-block source limit. Existing profile, slot, credit, allocation, control,
call-order, ownership, and workspace limits remain. Legacy recursive tree/plan
inspectors can still expand the logical trees stored with shared children.

## Method and validation

Measurement ran from **2026-09-13T01:04:50.456908+00:00** to
**2026-09-13T01:05:35.455108+00:00** on an AMD Ryzen 9 7950X3D, Linux 7.1.2, x86-64.
The report date is local America/New_York; the recorded timestamps are UTC.
Each worker was pinned to CPU 0 with `LEAN_NUM_THREADS=1`, `MALLOC_ARENA_MAX=1`,
and `LC_ALL=C`. The governor was `powersave`, driver `amd-pstate-epp`, and boost
enabled. Nix checks finished before timing. Host load and frequency were
otherwise uncontrolled.

Process wall times were **15.03, 14.97, 14.96 seconds**; GNU time peak RSS was
**92,064, 92,320, 91,316 KiB**, with a maximum of **90.156 MiB**. This covers the complete
23-case worker, including all stages, default-API replay, semantic/mutation
tests, budget/context tests, diagnostic formatting, hashing, and file IO.
It does not isolate a phase or mode and is separate from native workspace.

Each stage has one `IO.monoNanosNow` interval per process. Sizes ascend, with
baseline then graph on common cases. There is no randomization, confidence
interval, or per-stage process isolation. Fixture construction, API replay,
semantic/mutation tests, budget/context tests, inspection formatting, hashing
reported artifacts, and file writes are outside the stage intervals. Medians
must not be added to infer end-to-end latency.
Commands and protocol (`benchmarks/native-graph.md` on the archive branch of the pre-merge Compilatr.ix repository).

Validation on the final implementation passed:

- All **30 x86-64 Linux Nix checks**, including graph, shared, and tree heap
  gates and unchanged historical scaling artifacts.
- Three byte-identical reference inventories: 23 snapshots, objects, and
  per-case inspection/observation records each, matching reviewed goldens.
- Physical, typed native, and parsed-ELF execution for six boundary inputs
  per case; 2,700 source-graph and 3,925 native mutations per reference worker.
  The separate owning/scalar join test checks two distinct contexts, four
  executions, 29 source mutations, and 48 native mutations.
- Independent wire/ELF inspection, **184 corruptions**, **23 exact persisted
  recompilations**, and **759 guarded linked calls**, using GCC 14.3.0.
- Each heap mode: 95 source applications, 171 ELF cases, nine reloads,
  182 independent corruptions, 36 reload rejections, and 774 linked calls.
  Graph mode performs 1,824 certificate checks; it retains eighteen admission
  rejections and admits the former thirteen-join expansion failure. The legacy
  nineteen-rejection audit still runs.
- Fresh source-directory seed replay verifies all **769 source
  identities** and the seeds, repeats the independent checks and 759 linked
  calls, and reproduces every object. The raw archive inventory is verified.

The graph selection and exact-native-proposal fences use `propext`,
`Classical.choice`, and `Quot.sound`, the existing physical proof basis.
Existing execution, ownership, simultaneous-copy, source, and capacity fences
remain unchanged. No axiom or native interface is added.
[Validation record](validation.json).

## Provenance and retained replay

Frozen source is the base commit of that date (pre-merge history, not kept by the squash) plus the complete uncommitted
implementation in `source.tar.gz`. All 769 source files and
632 code identities remained unchanged through measurement.
This performance documentation was added afterwards. Tools, versions, linkage,
139 Nix closure paths, host policy, commands, resource observations,
and timestamps are retained and summarized in [provenance.json](provenance.json).

- Frozen source archive: **3,584,994 bytes**,
  SHA-256 `8916f81198a21d6d2c119aa5c20cb4596eba07a54909551597b571f7de4e9e9b`.
- Raw archive: **108,763,217 bytes**,
  SHA-256 `671c60a683ea13c5e31b57e41f4424aaffaf30fd8240492cb2fcbf0689686b96`.

| Executable seed | Bytes | SHA-256 |
| --- | ---: | --- |
| `check-native-graph` | 120,422,248 | `6be3ec248043828649ee9914348ea718e93b0d3bbaa7353d1b1c520af01f2704` |
| `heap-snapshot-object` | 123,579,240 | `6b55f7cb9e53fe748edb1e54308f3cbbd8c7ebec50d526d833cad6415d314fb1` |
| `native-graph` | 125,008,792 | `c130583bb883cb5ed382e119b06f42befbec571d48a3748c465bd7b3a1ede810` |

The raw archive is local at `benchmarks/runs/native-graph-2026-09-12.tar.gz`,
ignored by version control and not uploaded. It contains all three runs,
source and file inventories, executable seeds, build/validation logs, and
`collect.py`. Python's standard library only orchestrates measurement and
retention; compilation, proof checking, semantic tests, and independent
artifact/native gates are Lean programs.

Unpack the archive into a fresh directory and replay with its retained seeds:

```sh
tar -xzf benchmarks/runs/native-graph-2026-09-12.tar.gz -C /tmp
python3 /tmp/native-graph-reference-001/collect.py replay \
  --raw /tmp/native-graph-reference-001
```

Replay verifies identities, extracts a fresh source directory, and rebuilds
objects through the persisted-only consumer. This is seed replay, not a Lean
or compiler rebuild. The recorded runtime closure must be available. Ordinary
Lake/Nix commands in the protocol rebuild from current repository source.
