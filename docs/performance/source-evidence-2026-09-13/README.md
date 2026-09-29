# Reused source preparation reference — 2026-09-13

For the fully reachable **611-declaration source closure in 11 units**, median
source-certificate construction falls from **1,362.834 to 499.178 ms**;
unchanged reuse falls from **474.603 to 41.441 ms**.
Independent retained-unit checking falls from **925.913 to 489.265 ms**.
Complete source recipes, certificate stores, artifacts, cache decisions,
execution results, and admission limits are unchanged. These are three fresh
observations per compiler on one shared host.

The change removes repeated canonical-address validation. A checked unit
retains an erased proof for its exact owned entries; completed preparation
is shared within production and independent record checking. Current imports,
dependencies, usage, literals, ownership, and resource checks still run.
Lean proves equality with the full fresh result, including rejection behavior.
Retained records reconstruct canonical evidence afresh. The existing eraser,
coverage validation, and source-preservation certificates remain in place.
[Implementation and proof scope](https://github.com/argumentcomputer/Compilatr.ix/blob/jcb/ixby-archive/docs/modular-source.md#checked-cache-and-retained-records).

## Identical before/after workload

The baseline executable was freshly rebuilt from commit
`4878b0252ec531b54a15bc342fe79583bb8d1e82`, which already includes indexed
whole-program assembly. All **796 extracted repository files**
were checked against its archive after the build. The pinned Blake3 package
cache was shared. The optimized executable uses the frozen working source
in [provenance.json](provenance.json).

Both executables run the identical existing six-case `source-modular` matrix.
All 25 source, certificate, artifact, deterministic-summary, and report files
match between variants; the reviewed modular report is unchanged. For the
611-declaration case, the artifact remains **1,281,788 bytes** and the certificate
store **279,203 bytes**. These clocks cover source evidence; assembly is separate.
All entries below are median milliseconds. In the six-case table, the two
edit rows measure rebuilding from the baseline cache; the other build rows
start cold. The unchanged columns then reuse each case's completed cache.

| Source evidence at 611 declarations | Baseline ms | Prepared ms | Ratio |
| --- | ---: | ---: | ---: |
| Cold construction | 1,362.834 | 499.178 | 2.7× |
| Unchanged reuse | 474.603 | 41.441 | 11.5× |
| Retained-unit checking | 925.913 | 489.265 | 1.9× |

| Case | Source declarations | Build baseline ms | Build prepared ms | Unchanged baseline ms | Unchanged prepared ms |
| --- | ---: | ---: | ---: | ---: | ---: |
| Baseline graph | 4 | 0.666 | 0.465 | 0.345 | 0.241 |
| Dependency edit | 4 | 0.580 | 0.415 | 0.338 | 0.249 |
| Literal-premise edit | 4 | 0.576 | 0.337 | 0.336 | 0.240 |
| Mutual groups | 4 | 0.886 | 0.498 | 0.382 | 0.188 |
| Width 32 | 34 | 30.582 | 11.234 | 10.564 | 1.026 |
| Width 600 | 611 | 1,362.834 | 499.178 | 474.603 | 41.441 |

The three-sample ranges for the largest case are:

| Source evidence | Baseline range ms | Prepared range ms |
| --- | ---: | ---: |
| Cold construction | 1,361.401–1,389.161 | 497.770–502.523 |
| Unchanged reuse | 467.221–479.272 | 40.894–44.094 |
| Retained-unit checking | 910.396–926.105 | 482.882–490.983 |

Including assembly, the median of each sample's non-overlapping named clocks
is **1,503.664 → 626.921 ms** cold and
**602.930 → 170.810 ms** unchanged.
Recovery, including store decoding, unit checking, and assembly, is
**1,058.337 → 621.590 ms**.
These subtotals are calculated per sample before taking the median; they are
not whole-process times. Every phase sample and range is in
[summary.json](summary.json).

## Preparation components

Three additional fresh processes run the fixed five-width diagnostic profile.
The unit-level calls use exact inputs and already checked immutable imports
from a cold build. All fresh, reused, prepared, restored, and independently
checked results agree on their complete unit data. Values are median milliseconds.

| Source declarations | Units | Fresh preparation | Preparation with canonical facts | Fresh record checking | Prepared record checking |
| --- | ---: | ---: | ---: | ---: | ---: |
| 34 | 2 | 9.928 | 0.245 | 10.934 | 0.479 |
| 66 | 2 | 48.229 | 0.652 | 49.806 | 1.092 |
| 131 | 3 | 97.961 | 1.255 | 101.909 | 2.442 |
| 261 | 5 | 197.660 | 2.669 | 202.857 | 5.535 |
| 611 | 11 | 449.656 | 6.194 | 466.598 | 16.896 |

At 611 declarations, canonical-address checks alone take
**438.127 ms**. Preparation with their proved results takes
**6.194 ms** while retaining current context checks.
Prepared record checking takes **16.896 ms** and prepared production
**28.367 ms**; both receive completed preparation.
The producer still runs discovery and sends its result through the independent
checker, which reruns the actual eraser and validates complete output and coverage.

Checked-unit lookup takes **7.459 ms**, interface encoding
**1.368 ms**, input encoding **0.629 ms**,
and observations **2.141 ms**. The measurements identified canonical
validation as the main preparation cost, so query serialization and lookup
retain their existing implementations. Aggregate preflight alone takes
**9.785 ms**. Fresh canonicalization and repeated aggregate/context
work remain follow-up opportunities; this series does not establish general
compiler complexity or measure the compiler's complete source closure.

The eighteen diagnostic clocks **overlap and must not be summed**. Cold,
unchanged, and retained builds include preparation, scheduling, and aggregate
checks; subsequent calls repeat selected operations. Fresh preparation precedes
preparation with canonical facts; fresh checking precedes prepared checking.
There is no per-stage warm-up or randomization, and shared inputs can affect
caches. Ordinary assembly is repeated separately. The
[protocol](https://github.com/argumentcomputer/Compilatr.ix/blob/jcb/ixby-archive/benchmarks/source-evidence.md) defines the exact scopes.

## Correctness and process observations

All **32 x86_64-linux Nix checks** pass, including the full proof fence and
runtime tests, new independent preparation gate, existing modular and assembly
gates, and native endpoints. The 38 new preparation cases include 15 exact
address-evidence lookups and 23 fresh/prepared result comparisons (five accepted,
18 rejected). They cover modified source bodies, reference/sharing tables,
stale and forged records, ownership, literals, dependencies, fuel, and bounds.
The independent gate rejects five persisted-file mutations through public
replay. The existing modular gate retains its 40 certificate/resource rejections
and six file mutations. [Validation evidence](validation.json).

The five smaller modular cases still match complete monolithic compilation.
The 611-declaration closure still rejects monolithic admission at the original
512-candidate bound. Both dependency and literal-premise edits reuse the
unaffected unit and rebuild the three dependent certificates, matching cold
compilation exactly. A literal edit preserves source addresses and may reuse
canonical facts while invalidating the changed certificate premises.
Source, raw/addressed IxIR₀, and IxIR₁ execution agree, including full store
reclamation. The query and record formats, resource budgets, axiom basis,
native symbols, and external contracts are unchanged.

| Whole process | Wall seconds, all three runs | Peak RSS KiB, all three runs |
| --- | --- | --- |
| Baseline six-case matrix | 6.14, 6.21, 6.19 | 90420, 90784, 90964 |
| Prepared six-case matrix | 4.42, 4.46, 4.44 | 91496, 90696, 90580 |
| Additional diagnostic profile | 11.41, 11.45, 11.47 | 84288, 91544, 90712 |

The comparable six-case process median is
**6.19 → 4.44 seconds**.
Each process includes multiple compilations, recovery, execution, serialization,
full artifact comparisons, and IO. RSS describes the whole process and does
not isolate preparation or cache memory. The extra profile performs additional
work and has a separate process envelope.

Runs used CPU 0 on an AMD Ryzen 9 7950X3D, Linux 7.1.2, Lean 4.33.0,
`LEAN_NUM_THREADS=1`, `MALLOC_ARENA_MAX=1`, and `LC_ALL=C`. The recorded CPU
policy was `amd-pstate-epp`/`powersave` with boost enabled before and after
measurement. Builds and correctness checks had finished; the host was shared.
Comparison order was baseline/prepared, prepared/baseline, baseline/prepared,
followed by three diagnostic processes. Host snapshots, tools, linkage, and
runtime closure are in [reproduction.json](reproduction.json). There is no
timing threshold or statistical significance claim.

## Retention and replay

The machine-local, ignored archive is
`benchmarks/runs/source-evidence-2026-09-13.tar.gz` (**187,612,339 bytes**),
SHA-256 `9804bffcf0e6f1df3a59dfc2995b8c7496576be46fa398342f0311848d2be362`.
It has not been uploaded. Its **412 inventoried files** include all
raw observations and artifacts, the collector and fixed plan, process resources,
validation logs, baseline source/build evidence, current source snapshot, five
executable seeds, and tool/runtime identities. Exploratory diagnostics are
separately labeled and are excluded from the reported fixed-plan results.
Every inventory entry was independently verified from the completed archive.
[Retention record](retention.json).

Replay extracted and verified all **803 frozen source files** into a new
directory, checked the retained executable identities, independently checked
certificates, and reproduced all profile and modular artifact bytes. Both
independent preparation and modular gates passed from that extracted directory.
Replay uses retained executable seeds; it does not rebuild the executables or
require clock readings to match. [Replay record](replay-verification.json).

After unpacking the archive, run the retained seed with a new output directory.
Replace the two paths below. Recorded Nix runtime/tool store paths must remain
available. Extract `source.tar.gz` separately for the exact source and fixtures.

```sh
source_bundle=/path/to/source-evidence-reference-001
source_output=/path/to/new-source-evidence-replay
taskset -c 0 env LEAN_NUM_THREADS=1 MALLOC_ARENA_MAX=1 LC_ALL=C \
  "$source_bundle/seed/source-evidence" replay \
  "$source_bundle/profile-1" "$source_output"
```

The [benchmark protocol](https://github.com/argumentcomputer/Compilatr.ix/blob/jcb/ixby-archive/benchmarks/source-evidence.md) supplies fresh
build, producer, checker, and replay commands. Exact source and seed identities
and the fixed collection plan are in [provenance.json](provenance.json).
