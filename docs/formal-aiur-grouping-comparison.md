# Function grouping, primitive acceleration, and CUDA integration

Measured 2026-10-26 on branch `migration/formal-aiur` in Ix. Both execution
paths use bytecode. Native codegen remains deferred to the future macro backend.

## What changed

- Both application exports now group distinct functions into shared physical
  circuits. The application policies translate legacy's measured function
  groups after physical deduplication. Missing or inlined members are skipped;
  entrypoints remain separate. `--ungrouped` retains the comparison baseline.
- Shared data columns coexist with private selector/branch columns. Inactive
  private values are constrained to zero. Polynomial silence checks avoid
  raising cubic constraints to degree four. Quadratic lookup arguments that
  need another selector are materialized in private columns. Consequently,
  maximum constraint degree stays three and lookup degree stays two.
- The prepared trace writer fills the grouped row directly, preserving each
  function's logical call identity. Shard planning, multiplicities, fixed tables,
  and ROM placement use the resulting physical circuit order.
- Legacy's nonrecursive helpers called only with `@` now pass through Aiur's
  proved inliner. Recursive helpers and helpers with ordinary or unconstrained
  calls retain their call boundaries. The adapter does not generate native code.
- The ordinary U8 module computes AND/OR from XOR and less-than from subtraction,
  matching current legacy's primitive table sharing. Lean proves the arithmetic
  identities over fields in which two is nonzero. This reduces the pair table
  from ten multiplicity columns to seven. Legacy's eight include its U16 check.
- Fixed tables pair lookup messages when the known height makes the saved
  stage-two FFT work exceed the additional quotient work. The pair table's
  stage-two width falls from fourteen to eight, at unchanged global blowup.
  This uses multi-stark's existing lookup grouping, not a new Aiur operation.
- U32 decomposition/subtraction/comparison and U64 decomposition use generic
  fixed-arity hint closures. Existing byte table overrides return output plus
  row index. Opaque U8/U32 values still enter through checked library code.

## Correctness and CUDA boundaries

Grouping now has a checked equivalence theorem for the layout that is actually
exported. `Grouping.compile` returns a `Checked` result: finite polynomial and
structural checks certify the heuristic's output before it can reach JSON.
The exporter also certifies the complete partition with `Grouping.preparePlan`,
including functions that remain separate. A failed check rejects the export.

`Checked.localRule_iff` proves that a finite grouped row, with exactly the
exported width, implements precisely one of the original function row rules,
in both directions. Selector Booleanity and exclusivity, inactive private
zeros, and lifted argument equations follow from the emitted constraints.
Source memory validity follows from the actual shared lookup words; it is no
longer an extra premise supplied to the grouping theorem.

`Checked.packet_sound` and `Checked.packet_complete` additionally cover every
raw lookup word, including numeric channel/function IDs, memory widths, enables,
unused slots, and zero-padded tails. `Checked.zero_padding` proves the all-zero
row satisfies the equations and emits no lookup messages.
`Plan.derives_iff` lifts row equivalence to whole-program finite derivations.
`Physical.Prepared.grouped_native_heap_sound` composes this with the existing
compiler theorem to obtain source evaluation and heap representation.

These proofs introduce no `sorry`, new axioms, or `native_decide` obligations.
Their axiom audit uses only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. They retain the existing finite-derivation/acyclicity and ROM
contract. Rust's multi-stark lowering, serialization, and the cryptographic
backend remain outside this Lean correctness theorem. The checks happen during
export; they add no execution, trace-population, or proving operations.

The regression fixture is exported by Lean and checked for freshness. Its Lean
audit rejects changed packet tags and memory addresses, extra enabled sends,
undersized physical rows, and omitted source functions. The Rust test covers
shared branch/ROM rows, reference versus direct population, zero padding,
sharding, a proof round trip, and rejection of forged selectors and inactive
providers. The targeted Rust packages pass 90 tests. Clippy passes with warnings
denied. Byte/word checks cover every byte pair, fixed-table versus accelerated
outputs, invalid domains, dishonest hints, and real U64/Blake3 proof round trips.

Validation of the complete grouping certificate rebuilt the full proof graph,
passed the fixture freshness/rejection checks and grouped Rust proof test, and
passed `tools/ixvm/check-formal.sh` (IxVM claims, recursive proving, all thirteen
aggregation shapes, and malformed-input rejection). Re-exporting IxVM, the
recursive verifier, and aggregation with all certificate checks enabled produced
byte-identical artifacts, verified by SHA-256, so the column counts and measured
runtime circuits below are unchanged.

Both CUDA hosts compile and link with CUDA 13.3.1 in the NVIDIA development
container. Stage-one trace population remains on the CPU. The optional
`AIUR_TRACE_ONLY_LOOKUPS=1` mode uses multi-stark's CUDA graph evaluation instead
of allocating host lookup messages, and selects batch regeneration. The default
retains host messages to support CPU fallback under GPU memory pressure. The
shape-only path fails explicitly if such fallback tries to read missing data.
The hardware integration gate covers both modes and CPU verification.
**No GPU timing or runtime validation is available on this host:** it has no
NVIDIA device or driver. CUDA image digest:
`sha256:8cf42b8dc4c34d47fb42ffb0923f8a5e363469a7149181c094da336d311bb466`.

## Measurement method

Intel Xeon 6975P-C, Linux x86-64, Lean 4.34.1, Rust 1.98.1. Release builds use
`-Ctarget-cpu=native` on both backends. The final matrix sets
`RAYON_NUM_THREADS=8`; interpreters remain sequential. Two warmups precede five
execution/trace samples, or three for the larger recursive input. Tables report
medians; raw samples are saved. Proving is one verified run and includes trace
regeneration and verification, but excludes execution and system setup.

`IX_BENCH_NO_THP=1` disables transparent huge pages for each benchmark process,
without changing the machine policy. Legacy requests huge pages for its query
arenas. On the small recursive fixture, allowing those pages inflated execution
from about 4 ms to 163 ms. The same process setting is used on both backends.

The compiled programs, hint preparation, stream construction, and system/key
setup occur outside the execution timer. Trace timing includes planning,
populating main matrices, fixed-table and ROM counts, padding, and lookup
messages. Both provers use Goldilocks, blowup two, 64 queries, binary FRI,
zero-height caps, and one retained trace shard. FFT cost uses the exact same
operation-count model as `LegacyAiur.Statistics`, including stage-two columns;
it is a work estimate, not wall-clock time. Cells below count padded stage-one
main matrices, not preprocessed matrices or host lookup buffers.

The workloads are:

1. `ixvm`: the production `verify_claim` entry, checking `Nat.add_comm` with
   its frontier assumptions. Both receive identical claim streams.
2. `environment`: the self-contained 342-constant environment containing that
   theorem, with no frontier assumptions.
3. `recursion`: the same small, natively verified multi-stark fixture.
4. `recursion-real`: both generic recursive verifiers check the exact same
   proof of the self-contained IxVM environment, produced by the new grouped
   backend. This is much larger than the synthetic fixture.

The programs retain documented semantic differences: new Aiur uses structural
comparisons rather than pointer identity, constrained calls rather than legacy
unconstrained helpers, and generic checked hint/library interfaces. This is a
comparison of the faithful source port and its legacy counterpart, not a proof
that both programs have identical cost or formal semantics.

## Results

All times below use eight Rayon threads and bytecode execution. Proving includes
trace regeneration and verification. The small claim/fixture and large production
workloads are shown separately to expose fixed overheads.

| Workload | Backend | Execute (ms) | Trace + lookups (ms) | Prove (s) | Proof bytes |
|---|---|---:|---:|---:|---:|
| Nat.add_comm frontier | legacy | 8.81 | 11.53 | 0.294 | 5,669,347 |
| Nat.add_comm frontier | new | 5.80 | 6.47 | 0.306 | 6,320,763 |
| 342-constant environment | legacy | 397.74 | 84.35 | 2.450 | 6,854,018 |
| 342-constant environment | new | 360.53 | 154.15 | 3.632 | 7,227,058 |
| Small recursive fixture | legacy | 4.07 | 10.91 | 0.194 | 3,446,443 |
| Small recursive fixture | new | 2.39 | 4.70 | 0.214 | 3,585,743 |
| Real recursive verifier | legacy | 8,821.55 | 2,255.25 | 43.336 | 3,706,823 |
| Real recursive verifier | new | 7,957.46 | 3,562.85 | 55.065 | 3,845,899 |

The large recursive input is a fixed **7,232,210-byte IxVM proof**. Both
verifiers receive identical key, claim, and proof streams. All reported outer
proofs verify. Real-input ungrouped execution/trace/cost measurements are in
the CSVs; outer proving for that large ungrouped case was not measured.

### Physical circuit sizes

Widths include the function provider multiplicity and all ROM/fixed-table
circuits. Stage-two widths are base-field columns (two limbs per extension).

| Application | Grouping | Legacy circuits | New circuits | Legacy stage 1 | New stage 1 | Legacy stage 2 | New stage 2 |
|---|---|---:|---:|---:|---:|---:|---:|
| ixvm | ungrouped | 794 | 799 | 21,351 | 20,887 | 9,962 | 9,948 |
| ixvm | grouped | 222 | 235 | 9,163 | 9,650 | 3,616 | 4,194 |
| recursion | ungrouped | 197 | 203 | 6,359 | 6,285 | 2,754 | 2,816 |
| recursion | grouped | 84 | 91 | 3,880 | 4,109 | 1,590 | 1,630 |

Function circuits alone shrink **778 → 214** for new IxVM and **189 → 77**
for the new verifier. Legacy has 202 and 71 grouped function circuits,
respectively. New Aiur is slightly narrower before grouping; the remaining
extra width is predominantly in the grouping layout, rather than ROM metadata.

The ROM widths match exactly: 18 chips / 424 columns for IxVM, and 11 chips /
179 columns for the verifier. New fixed tables use three chips / ten main
columns; legacy uses two / eleven. Both use fourteen stage-two table columns
after cost-aware lookup pairing.

### Cells and FFT work

| Grouped workload | Backend | Stage-one cells | Estimated FFT work |
|---|---|---:|---:|
| Nat.add_comm frontier | legacy | 1,257,336 | 99,854,452 |
| Nat.add_comm frontier | new | 1,322,458 | 100,644,448 |
| 342-constant environment | legacy | 45,169,839 | 3,617,041,155 |
| 342-constant environment | new | 46,656,479 | 3,527,936,909 |
| Small recursive fixture | legacy | 860,644 | 77,849,696 |
| Small recursive fixture | new | 826,803 | 74,587,165 |
| Real recursive verifier | legacy | 985,571,600 | 97,838,278,046 |
| Real recursive verifier | new | 1,005,868,035 | 89,271,866,275 |

### Remaining gaps

New bytecode execution is faster on both substantial workloads. The large
environment and recursive traces are still slower, as is proving. On the real
recursive input, new Aiur has about 2.1% more main cells and 8.8% less estimated
FFT work, yet trace generation is about 58% slower and proving about 27% slower.
Cell counts and FFT estimates therefore do not explain the remaining elapsed
time by themselves. This run does not isolate constraint evaluation, lookup
evaluation, allocation, or memory traffic inside the prover.

Two concrete layout outliers are:

| Shared policy group | Legacy main columns | New main columns | New lifted lookup arguments |
|---|---:|---:|---:|
| `ixvm_group_08` | 166 | 238 | 67 |
| `verifier_group_12` | 238 | 378 | 161 |

The verifier group contains `Blake3::finish`, `bytes_to_block`,
`compress_block`, `read_sys_circuits_n`, `ch_sample8`, and `ood_loop`.
The current conservative transform materializes quadratic message arguments
before selecting a member, keeping degree at most three. That accounts for
67 extra columns in `finish` and 84 in `compress_block` within this group.
These are layout costs, not additional semantic operations or malformed traces.

The next optimization to try is including quadratic message expressions in
private-column selection, then choosing whichever valid layout is narrower.
Zeroing a few shared factors may silence many arguments and remove their
individual materialization columns. The existing silence checker and grouping
lemmas can validate that choice. Another measurable candidate is preparing the
remaining group-write expressions once: `Placement::finish` currently evaluates
those polynomial trees per row. Neither improvement is claimed implemented here.

## Saved data

The checked-in [summary CSV](benchmarks/formal-aiur-grouping/summary.csv)
contains all grouped and ungrouped timings, cells, and FFT estimates.
[The per-circuit CSV](benchmarks/formal-aiur-grouping/circuits.csv) includes
**every circuit**, its name, height, and separate stage-one/stage-two widths.
[The manifest](benchmarks/formal-aiur-grouping/manifest.json) records the code
revision, configuration, artifact hashes, and recursive input hashes. Adjacent
[`runs.json`](benchmarks/formal-aiur-grouping/runs.json) retains all raw samples
and proof sizes. Large generated artifacts
and proof inputs remain under `.lake/formal-comparison/final/` locally.

The code is in commit `9bd5d3ce` on `migration/formal-aiur`.

## Reproduction

```sh
RAYON_NUM_THREADS=8 IX_BENCH_NO_THP=1 \
  bash tools/ixvm/compare-backends.sh .lake/formal-comparison/run
```

The script exports both artifacts unless `IX_AIUR_ARTIFACT` and
`IX_RECURSION_ARTIFACT` are supplied. Set `IX_BENCH_RECURSIVE_PROVE=1` to prove the
large recursive traces too. The small recursive fixture always gets proved.
`tools/ixvm/compare-results.py` produces `summary.csv`, `circuits.csv` (every
circuit, stage one and stage two separately), and the artifact-hash manifest.

