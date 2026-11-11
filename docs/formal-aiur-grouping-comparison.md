# Function grouping, primitive acceleration, and CUDA integration

Historical record: measured 2026-10-26 on branch `migration/formal-aiur` at
`9bd5d3ce`. Execution uses bytecode; native codegen was deferred to a later
macro backend.

The [2026-10-27 grouping tuning](formal-aiur-grouping-tuning.md) supersedes the
grouped sizes below, reducing IxVM to 8,018 main columns and the recursive
verifier to 3,199. This report retains the original baseline data.

## What changed

- Both application exports group distinct functions into shared physical
  circuits. The first policies were a direct translation of the retired legacy
  backend's measured function groups after physical deduplication. Missing or
  inlined members are skipped; entrypoints remain separate. `--ungrouped`
  retains the ungrouped baseline.
- Shared data columns coexist with private selector/branch columns. Inactive
  private values are constrained to zero. Polynomial silence checks avoid
  raising cubic constraints to degree four. Quadratic lookup arguments that
  need another selector are materialized in private columns. Consequently,
  maximum constraint degree stays three and lookup degree stays two.
- The prepared trace writer fills the grouped row directly, preserving each
  function's logical call identity. Shard planning, multiplicities, fixed tables,
  and ROM placement use the resulting physical circuit order.
- Nonrecursive helpers called only with `@` pass through Aiur's proved
  inliner. Recursive helpers and helpers with ordinary or unconstrained calls
  retain their call boundaries. The adapter does not generate native code.
- The ordinary U8 module computes AND/OR from XOR and less-than from
  subtraction. Lean proves the arithmetic identities over fields in which two
  is nonzero. This reduces the pair table from ten multiplicity columns to
  seven.
- Fixed tables pair lookup messages when the known height makes the saved
  stage-two FFT work exceed the additional quotient work. The pair table's
  stage-two width falls from fourteen to eight, at unchanged global blowup.
  This uses multi-stark's existing lookup grouping, not a new Aiur operation.
- U32 decomposition/subtraction/comparison and U64 decomposition use generic
  fixed-arity hint closures. Existing byte table overrides return output plus
  row index. Opaque U8/U32 values still enter through checked library code.

## Correctness and CUDA boundaries

Grouping has a checked equivalence theorem for the layout that is actually
exported. `Grouping.compile` returns a `Checked` result: finite polynomial and
structural checks certify the heuristic's output before it can reach JSON.
The exporter also certifies the complete partition with `Grouping.preparePlan`,
including functions that remain separate. A failed check rejects the export.

`Checked.localRule_iff` proves that a finite grouped row, with exactly the
exported width, implements precisely one of the original function row rules,
in both directions. Selector Booleanity and exclusivity, inactive private
zeros, and lifted argument equations follow from the emitted constraints.
Source memory validity follows from the actual shared lookup words; it is not
an extra premise supplied to the grouping theorem.

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
providers. The targeted Rust packages passed 90 tests. Clippy passed with
warnings denied. Byte/word checks cover every byte pair, fixed-table versus
accelerated outputs, invalid domains, dishonest hints, and real U64/Blake3
proof round trips.

Validation of the complete grouping certificate rebuilt the full proof graph,
passed the fixture freshness/rejection checks and grouped Rust proof test, and
passed `tools/ixvm/check-formal.sh` (IxVM claims, recursive proving, all thirteen
aggregation shapes, and malformed-input rejection). Re-exporting IxVM, the
recursive verifier, and aggregation with all certificate checks enabled produced
byte-identical artifacts, verified by SHA-256, so the column counts and measured
runtime circuits below are unchanged.

Both CUDA hosts compiled and linked with CUDA 13.3.1 in the NVIDIA development
container. Stage-one trace population stayed on the CPU. The optional
`AIUR_TRACE_ONLY_LOOKUPS=1` mode uses multi-stark's CUDA graph evaluation instead
of allocating host lookup messages, and selects batch regeneration. At
`9bd5d3ce` the default retained host messages to support CPU fallback under GPU
memory pressure, and the shape-only path failed explicitly if such fallback
tried to read missing data. The hardware integration gate covers both modes and
CPU verification. **No GPU timing or runtime validation was available on the
measuring host:** it had no NVIDIA device or driver. CUDA image digest:
`sha256:8cf42b8dc4c34d47fb42ffb0923f8a5e363469a7149181c094da336d311bb466`.

## Measurement method

Intel Xeon 6975P-C, Linux x86-64, Lean 4.34.1, Rust 1.98.1. Release builds use
`-Ctarget-cpu=native`. The final matrix sets `RAYON_NUM_THREADS=8`; the
interpreter remains sequential. Two warmups precede five execution/trace
samples, or three for the larger recursive input. Tables report medians; raw
samples are saved. Proving is one verified run and includes trace regeneration
and verification, but excludes execution and system setup.

`IX_BENCH_NO_THP=1` disables transparent huge pages for each benchmark process,
without changing the machine policy.

The compiled programs, hint preparation, stream construction, and system/key
setup occur outside the execution timer. Trace timing includes planning,
populating main matrices, fixed-table and ROM counts, padding, and lookup
messages. The prover uses Goldilocks, blowup two, 64 queries, binary FRI,
zero-height caps, and one retained trace shard. FFT cost is an operation-count
model including stage-two columns; it is a work estimate, not wall-clock time.
Cells below count padded stage-one main matrices, not preprocessed matrices or
host lookup buffers.

The workloads are:

1. `ixvm`: the production `verify_claim` entry, checking `Nat.add_comm` with
   its frontier assumptions.
2. `environment`: the self-contained 342-constant environment containing that
   theorem, with no frontier assumptions.
3. `recursion`: a small, natively verified multi-stark fixture.
4. `recursion-real`: the recursive verifier checks a proof of the
   self-contained IxVM environment, produced by the grouped backend. This is
   much larger than the synthetic fixture.

## Results

All times below use eight Rayon threads and bytecode execution. Proving includes
trace regeneration and verification. The small claim/fixture and large production
workloads are shown separately to expose fixed overheads.

| Workload | Execute (ms) | Trace + lookups (ms) | Prove (s) | Proof bytes |
|---|---:|---:|---:|---:|
| Nat.add_comm frontier | 5.80 | 6.47 | 0.306 | 6,320,763 |
| 342-constant environment | 360.53 | 154.15 | 3.632 | 7,227,058 |
| Small recursive fixture | 2.39 | 4.70 | 0.214 | 3,585,743 |
| Real recursive verifier | 7,957.46 | 3,562.85 | 55.065 | 3,845,899 |

The large recursive input is a fixed **7,232,210-byte IxVM proof**. All
reported outer proofs verify. Real-input ungrouped execution/trace/cost
measurements are in the CSVs; outer proving for that large ungrouped case was
not measured.

### Physical circuit sizes

Widths include the function provider multiplicity and all ROM/fixed-table
circuits. Stage-two widths are base-field columns (two limbs per extension).

| Application | Grouping | Circuits | Stage 1 | Stage 2 |
|---|---|---:|---:|---:|
| ixvm | ungrouped | 799 | 20,887 | 9,948 |
| ixvm | grouped | 235 | 9,650 | 4,194 |
| recursion | ungrouped | 203 | 6,285 | 2,816 |
| recursion | grouped | 91 | 4,109 | 1,630 |

Function circuits alone shrink **778 → 214** for IxVM and **189 → 77** for the
verifier. ROMs use 18 chips / 424 columns for IxVM, and 11 chips / 179 columns
for the verifier. Fixed tables use three chips / ten main columns.

### Cells and FFT work

| Grouped workload | Stage-one cells | Estimated FFT work |
|---|---:|---:|
| Nat.add_comm frontier | 1,322,458 | 100,644,448 |
| 342-constant environment | 46,656,479 | 3,527,936,909 |
| Small recursive fixture | 826,803 | 74,587,165 |
| Real recursive verifier | 1,005,868,035 | 89,271,866,275 |

### Layout outliers

Cell counts and FFT estimates do not determine elapsed trace or proving time by
themselves. This run does not isolate constraint evaluation, lookup evaluation,
allocation, or memory traffic inside the prover.

Two concrete layout outliers are:

| Shared policy group | Main columns | Lifted lookup arguments |
|---|---:|---:|
| `ixvm_group_08` | 238 | 67 |
| `verifier_group_12` | 378 | 161 |

The verifier group contains `Blake3::finish`, `bytes_to_block`,
`compress_block`, `read_sys_circuits_n`, `ch_sample8`, and `ood_loop`.
The conservative transform materializes quadratic message arguments
before selecting a member, keeping degree at most three. That accounts for
67 extra columns in `finish` and 84 in `compress_block` within this group.
These are layout costs, not additional semantic operations or malformed traces.

The next optimization identified was including quadratic message expressions
in private-column selection, then choosing whichever valid layout is narrower.
Zeroing a few shared factors may silence many arguments and remove their
individual materialization columns. The existing silence checker and grouping
lemmas can validate that choice. The
[grouping tuning](formal-aiur-grouping-tuning.md) implements this. Another
candidate is preparing the remaining group-write expressions once:
`Placement::finish` evaluated those polynomial trees per row.

## Saved data

The checked-in [summary CSV](benchmarks/formal-aiur-grouping/summary.csv)
contains all grouped and ungrouped timings, cells, and FFT estimates.
[The manifest](benchmarks/formal-aiur-grouping/manifest.json) records the code
revision, configuration, artifact hashes, and recursive input hashes. The
per-circuit table and raw samples are not kept in the repository. Large
generated artifacts and proof inputs were kept outside it, under
`.lake/formal-comparison/final/`.

The code is in commit `9bd5d3ce` on `migration/formal-aiur`.

## Reproduction

This is a historical comparison. Its driver, `tools/ixvm/compare-backends.sh`,
ran the legacy backend through `bench-compare-aiur`, and both were removed with
the legacy backend, together with the `compare-results.py` summarizer; they
remain in the history of the migration branch. The formal side of each
measurement is still `target/release/examples/compare` (`cargo build --release
--locked -p stark-verifier --features parallel --example compare`), run on an
exported artifact and a claim input.

