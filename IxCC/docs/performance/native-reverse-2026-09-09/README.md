# PERF1 and C3 reference, 2026-09-09

PERF1 is delivered for `native-reverse/1` on the recorded x86_64 Linux host.
C3 is delivered for the unchanged `applyClosed` and `letClosed` upstream
computations, including native selection, measurements, and retained evidence.
The [generated report](report.md) and [machine-readable summary](summary.json)
are byte-identical to the independent replay. This review records their
interpretation, artifact scopes, retrieval procedure, and follow-up decisions.

Collection ran from **2026-09-09 19:12:38 UTC to 2026-09-10 11:38:38 UTC**.
All **30 paired blocks in three sessions** passed on their first attempt:
20,520 reversal samples and 180 closed upstream call samples. Every one of the
38 reversal rows includes all six implementations. There are no missing or
failed published rows, retries, or discarded slow observations. Pilot and
instrumented diagnostics are separate from these samples.

## Reversal results

The domain is independently owned lists of 0–64 exact unsigned 64-bit payloads.
Primary rows cycle through six patterns below `2^30`. The consuming Lean and
CakeML programs are language/runtime comparisons. CompCert, GCC, and Clang
compile the same arena C source and form the matched C comparison.
IxCC retains its existing validation and counter work in both profiles.

At length 64 with primary payloads, times below are nanoseconds per operation:
the median across 30 block medians, followed by its 95% bootstrap interval.

| Implementation | Entry + bounded handoff | Fresh allocation lifecycle |
| --- | ---: | ---: |
| IxCC | 237.60 [237.17, 238.63] | 418.38 [417.30, 420.90] |
| Lean 4 | 92.23 [91.71, 92.94] | 455.16 [452.99, 459.82] |
| CakeML | 180.27 [175.91, 186.88] | 2,879.84 [2,857.91, 2,908.12] |
| CompCert | 74.94 [74.65, 75.37] | 263.41 [262.78, 264.70] |
| GCC | 72.99 [72.80, 73.52] | 252.28 [250.81, 254.47] |
| Clang | 50.63 [50.46, 50.92] | 234.35 [232.77, 240.27] |

Entry timing includes the call and bounded output handoff. Fresh inputs are
prepared and fully checked/released between timed chunks. Lifecycle includes
list construction, reversal, an order-sensitive result digest, and normal
memory management. Immutable scalar datasets are prepared before either
profile. These boundaries are specified in the protocol (`benchmarks/protocol.md` on the archive branch of the pre-merge Compilatr.ix repository).

The paired baseline/IxCC ratios at length 64 are:

| Comparison | Entry ratio [95% interval] | Lifecycle ratio [95% interval] |
| --- | ---: | ---: |
| Lean / IxCC | 0.3880 [0.3859, 0.3904] | 1.0865 [1.0785, 1.0982] |
| CakeML / IxCC | 0.7579 [0.7403, 0.7789] | 6.8679 [6.7993, 6.9297] |
| CompCert / IxCC | 0.3150 [0.3144, 0.3161] | 0.6295 [0.6275, 0.6312] |
| GCC / IxCC | 0.3068 [0.3064, 0.3074] | 0.6015 [0.5992, 0.6066] |
| Clang / IxCC | 0.2128 [0.2122, 0.2135] | 0.5616 [0.5571, 0.5664] |

Ratios above one favor IxCC. They are medians of within-block ratios;
dividing independently aggregated time medians need not give the same number.
IxCC's primary lifecycle time is about 8% below Lean's and substantially
below CakeML's here. Its entry time is about 2.58 times Lean's and 4.70 times
Clang's. All three C variants have lower lifecycle times as well.

The length dependence matters. Lean's primary lifecycle is faster at the
measured lengths 0–8; IxCC is faster at 16–64. For example, the respective
times are 12.89 and 24.34 ns at length 1, versus 112.81 and 100.82 ns at length 16.
The report retains all measured lengths and the adverse small-input cases.

Payload representation changes the lifecycle comparison:

| Repeated payload at length 64 | IxCC ns | Lean ns | CakeML ns |
| --- | ---: | ---: | ---: |
| `2^63-1` | 418.58 | 454.49 | 2,888.33 |
| `2^63` | 420.08 | 3,216.88 | 2,902.60 |
| `2^64-1` | 418.90 | 3,254.13 | 2,910.99 |

The paired Lean/IxCC lifecycle ratios for the latter two rows are
7.6463 [7.6129, 7.6987] and 7.7489 [7.6894, 7.8040]. Lean entry times change
much less: 91.58–95.42 ns across these stress rows. This pattern is consistent
with payload representation and lifetime/consumption costs outside reversal;
the experiment does not isolate one cause. IxCC and the C variants use
exact words throughout this bounded domain. These stress cases do not establish
performance or correctness for unbounded Nat arithmetic.

## Memory and native code

At length 64, each fresh arena reserves `80 + 32*(64+2) = 2,192` bytes.
Entry chunks retain at most 4,096 independent lists: 8,978,432 arena bytes plus
slots and allocator overhead. Lifecycle retains one list allocation at a time.
The source/physical reversal records `n+2` logical cell allocations, `n` reuses,
zero RC operations, peak `n+2` live cells, and complete release. Logical cell
counts are distinct from the native arena's one system allocation per list.
Lean's independent diagnostic verifies exclusive input spines and reused cons
addresses. CakeML collections occur during its timed allocating work.

| Implementation | Median ready RSS KiB | Sample RSS range KiB | Maximum recorded `ru_maxrss` KiB |
| --- | ---: | ---: | ---: |
| IxCC | 2,028 | 2,192–2,464 | 11,104 |
| Lean | 7,342 | 7,300–15,720 | 15,716 |
| CakeML | 2,540 | 68,060–68,108 | 67,896 |
| CompCert / GCC / Clang, each | 2,024 | 2,188–2,460 | 11,100 |

RSS comes from `/proc/self/statm`, and the high-water observation comes from
`getrusage`. These Linux counters use different accounting and sampling paths;
their values are retained directly, including small apparent discrepancies.
They include runtime/allocator reservation and do not measure live source heap.
A small fork launcher prevents the large controller's pre-exec high-water mark
from being inherited by timed workers.

The separate CakeML diagnostic exercised **11,258 natural collections across
20 lifecycle samples**, covering all four length-64 payload domains. Every
sample recorded 348,952 bytes after its last collection, below the frozen 8 MiB
bound in the 64 MiB heap. The separately timed terminal collection took 74,990 ns
and retained 347,640 bytes. Event counts cover instrumented sample envelopes;
they are not substituted for primary timings. `perf` was unavailable in the
recorded environment, so no hardware-counter totals are claimed.

| Retained object scope | Sum of `.text` and `.text.*` bytes |
| --- | ---: |
| IxCC reversal | 1,036 |
| IxCC release | 231 |
| Lean generated module, including initialization | 665 |
| CakeML program, driver and basis | 106,564 |
| CompCert arena kernel | 679 |
| GCC arena kernel | 596 |
| Clang arena kernel | 776 |

Lean's 665 bytes comprise reversal 349, exported wrapper 10, and module
initialization 306. Its literal `.text` section is empty; the generated report's
zero in that column does not mean the object has no code. This table includes
its named `.text.*` sections. Object scopes differ, especially CakeML's driver
and basis. Complete section tables, executable sizes, and dynamic dependency
records remain in the bundle.

The single observed reversal producer envelope was 13,502.26 ms; its independent
fixture gate was 31,847.57 ms. These commands include fixture/certification work
and differ from a standalone C kernel compilation. They are diagnostics, not a
statistical compiler-speed comparison. All named command arguments, wall/CPU
time, peak RSS, and the comparison compiler envelopes are retained.

## C3: unchanged upstream computations

Original source bytes, roots, the pinned writer, and six-constant closures are
preserved. Both entries pass source erasure certification, checked physical
execution and full result reclamation, then structural native selection and
actual object execution. Successor instructions and four direct calls remain.

| Entry | Result | Native text bytes | ELF bytes | Median ns/call [95% interval] |
| --- | ---: | ---: | ---: | ---: |
| `applyClosed` | 3 | 84 | 936 | 5.2040 [5.1994, 5.2115] |
| `letClosed` | 4 | 91 | 944 | 5.2028 [5.1967, 5.2121] |

| Entry | Produce ms / peak RSS KiB | Check ms / peak RSS KiB | Packed source bytes | Snapshot bytes | Encoded IxIR₀ / IxIR₁ / HPT bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| `applyClosed` | 54.37 / 53,980 | 36.53 / 49,588 | 662 | 45,040 | 318 / 337 / 788 |
| `letClosed` | 62.78 / 56,004 | 42.42 / 49,760 | 670 | 47,629 | 356 / 377 / 788 |

Compiler/checker costs are single process envelopes. Snapshot sizes include
serialized IR and execution observations; they do not estimate Lean proof-term
allocation. Each entry has six encoded IxIR₀ declarations, four IxIR₁ artifacts,
and four HPT certificates. The complete section-by-section snapshot sizes are
in `summary.json` under `diagnostics.upstream_artifact_growth`.

The physical baselines finish complete release with five allocations/frees and
seven RC operations for `applyClosed`, and six allocations/frees and eight RC
operations for `letClosed`. Native results occupy one eight-byte word and use
zero heap allocation/free/RC operations. The native traces write 48 stack bytes
below the caller return slot, using 64 supplied writable bytes. They take no
runtime arguments. Four supplied-state certificates and linked ABI tests retain
their scope; open calls, branches/joins, general stack sufficiency, the reference
ISA bridge, and system linker/loader behavior remain separate obligations.

`captureClosed` keeps its checked physical fallback (`capturedPap`). Addition,
recursion and the Std slice retain the source-certification boundaries in
source coverage (`docs/source-coverage.md` on the archive branch of the pre-merge Compilatr.ix repository); equal erased-block reuse does not
claim their eventual source acceptance.

## Follow-up decision

The entry-time gap against the matched arena C kernels makes the existing
runtime-input reversal the first target for a PERF3 paired lowering experiment.
Inspect redundant scalar/address/control work, propose one bounded rewrite,
and require its checked semantics and the same validation/counter contract.
Retain the current artifact as fallback and measure the complete input matrix,
including short lists, large payloads, rejection cases, compiler/checker cost,
and code growth. The present data identifies the target; it does not identify
or validate a particular profitable rewrite. M2d's scalar-peephole work can
start when that concrete candidate and side conditions exist.

General PAP specialization, field deletion and unboxing remain deferred: these
two closed C3 entries already allocate no native heap, and the experiment has
no generic-versus-specialized native pair. The next C3/N3 extension should admit
runtime scalar arguments and direct calls with explicit exact-Word range and
call/stack contracts. Broader upstream recursion waits for its missing source
certificates and the N3/F1 requirements. Neither the small call timings nor the
reversal fixture-gate time justifies bypassing those gates or increasing source
certificate budgets.

No dedicated performance-regression threshold is set from this run. Collect
independent history on a controlled host before choosing one. PERF2's broader
families and OCaml baseline, and PERF3's paired optimization/compiler scaling,
remain distinct deliverables.

## Host, statistics and validation

The host was an AMD Ryzen 9 7950X3D, microcode `0xa60120a`, Linux 7.1.2/NixOS.
The worker used CPU 2, the controller CPU 0, and NUMA node 0. SMT was enabled;
CPU 18 was the worker's unreserved sibling. `amd-pstate-epp`, the `powersave`
governor, boost enabled, and the `tsc` clocksource were observed throughout.
The host, thermal state and other tenants were not controlled. Timing used
`CLOCK_MONOTONIC_RAW` with identical frozen counts across all six implementations.
Every measured sample passed the 100 ms floor and the clock/chunk/resource checks.

The compiled benchmark toolchain is Lean 4.33.0, CakeML v3479, CompCert 3.16,
GCC 14.3.0 and Clang 21.1.2, with exact revisions, flags, binaries and dependency
paths retained. The original upstream exports retain their separate pinned
writer/toolchain; they were not regenerated for this experiment.

Statistics use three samples per block, 30 blocks in three consecutive sessions,
and a 60-second idle interval between sessions. The same 10,000 hierarchical
bootstrap draws resample sessions then paired blocks for every row. Seed
2671931027 and linear `(n-1)*p` quantiles are frozen. Only three session clusters
limit interval precision and any inference about different days or machines.
The generated Markdown rounds to hundredths even when trailing zeros are shown;
use the JSON summary for full retained numerical precision. These lengths and
payload domains are one workload, not independent application benchmarks.

Before measurement, all 805 Lake jobs, 17 compiled validation commands, and
19 x86_64 Linux Nix checks passed. Other platforms were not run. Full correctness
checked all 585 cases and the 19,305 arena case/capacity combinations, malformed
datasets, exact results and reclamation, the existing ABI cases, 228 smoke rows,
72 corrupt schedules, sample-schema rejection, and real GC smoke behavior.

Independent reproduction extracted and checked 479 source files, used retained
hashed compiler/checker seeds in a fresh directory and empty process environment,
rebuilt identical artifacts/executables, reran full correctness, and regenerated
both report and summary byte for byte. It used the same physical host and pinned
Nix runtime. It replays retained timing observations; it does not demand a new
timing run produce identical clock readings. The separate Nix gate rebuilt the
proof/project sources. See [reproduction.json](reproduction.json).

## Retention and replay

The full bundle is retained locally at
`benchmarks/runs/c76bfd89e1388bda877e020d4a415473a9aeb7cb0a323b7886317e6c06ebebac.tar.gz` (on the archive branch of the pre-merge Compilatr.ix repository),
SHA-256 **`c76bfd89e1388bda877e020d4a415473a9aeb7cb0a323b7886317e6c06ebebac`**, **566812498 bytes**.
Copy that complete archive when moving the reference to another storage service.
Its retained runner, raw process records, source/toolchain inventories, original
and rebuilt objects, correctness results, diagnostics and validation logs are
covered by `reference/SHA256SUMS`. The extraction and relocated analysis check
are recorded in [retention.json](retention.json).

From the repository root, using fresh paths:

```sh
archive=benchmarks/runs/c76bfd89e1388bda877e020d4a415473a9aeb7cb0a323b7886317e6c06ebebac.tar.gz
printf '%s  %s\n' c76bfd89e1388bda877e020d4a415473a9aeb7cb0a323b7886317e6c06ebebac "$archive" | sha256sum --check -
mkdir /tmp/ixcc-reference-retrieved
tar --no-same-owner -xzf "$archive" -C /tmp/ixcc-reference-retrieved
/tmp/ixcc-reference-retrieved/reference/run.sh verify-bundle
/tmp/ixcc-reference-retrieved/reference/run.sh analyze /tmp/ixcc-analysis-replay
/tmp/ixcc-reference-retrieved/reference/run.sh reproduce /tmp/ixcc-artifact-replay
```

The installed pinned Nix closure is required. Exact paths and the successful
supplementary dependency query are in `reference/validation/nix-closure.txt`
and `nix-closure-query.json`; the original sandbox-unavailable query is preserved
under `build/`. CakeML's compiler and basis bridge are retained in the archive.
The source archive contains `flake.lock`, the compiler lock and bootstrap
retrieval instructions. The protocol (`benchmarks/protocol.md` on the archive branch of the pre-merge Compilatr.ix repository) documents
building the runner and a new artifact set.

To collect a new full session against the retained artifacts on this host,
after finishing other build/network work and choosing available physical cores:

```sh
/tmp/ixcc-reference-retrieved/reference/run.sh measure /tmp/ixcc-new-reference 2 0
```

This creates fresh correctness, pilot, measurement, diagnostics and analysis
directories. It takes about 16.5 hours at the recorded pace and preserves this
reference. Completion is `measured/measurement.json` with `status: "complete"`;
the incremental `progress.json` keeps its initial `complete: false` field.

The measured build manifest's BLAKE3 is
`0a3c7757fa3b6c3634c75d247c65b5da92b04692429376d77a278aa8edab1046`;
the dirty source archive's BLAKE3 is
`39e952a5fa971fe09f3fbda2b2337d1a96909f79e392136fa9fadb9fd9e4a58b`.
That source snapshot precedes these result documents; the measured compiler,
harness, protocol and integrity ledger stayed frozen throughout collection.
