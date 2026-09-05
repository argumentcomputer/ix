# Ix Flock Stage 3

This workspace implements the no-RISC-V Stage 3 compressor:

```text
Stage 2 Aiur recursive-FRI root
  -> Flock proof of statement + AIR/logUp + PCS + FRI verification
  -> Stage 4 terminal SNARK
```

The backend uses Flock `Fast128` over `F128`, BLAKE3 Merkle commitments, and
chained-BLAKE3 Fiat-Shamir. The upstream revision is pinned to
`b310f35f35f68095537150a1c8c0a43caca9a29e`; changing it is a protocol change.

## Current status

`FlockStage3Backend::prove_stage2` now generates a complete Stage 3 proof.
The production path:

1. validates canonical Aiur verifier-key, claim, and proof encodings;
2. expands the compact multiproof into the typed verifier witness;
3. admits its table/buffer geometry, compiles and evaluates the specialised
   fixed-shape relation, and validates the concrete PCS configuration;
4. proves it under the production Stage 3 transcript domain;
5. binds the compiled circuit, Flock configuration, Stage 2 key, witness
   layout, exact witness shape, and completed phase mask in
   `Stage3RelationManifestV1`;
6. verifies the generated Flock bundle against that same relation; and
7. returns a strict, versioned `Stage3ArtifactV1`.

`FlockStage3Backend::verify_stage2` requires an externally expected
`Stage3StatementV1`. It reconstructs the relation from the canonical Stage 2
transport, checks the expected root and relation-manifest digest, and verifies
the Flock bundle. The relation digest therefore has to be pinned by the
deployment; accepting a relation digest supplied only by the prover would not
specialise the verifier key.

`verify_stage2_for_root` is the operational verification path: it derives the
expected statement from an external persisted aggregate root, requires the
artifact's embedded compact transport to match it, and reuses that one
validation/relation build for cryptographic verification.

`prepare_stage2[_with_limits]` returns an explicitly owned
`Stage3PreparedRootV1`. Inspect `report()` before calling `prove_with_timings()`;
`verify()` can reuse that same admitted relation. Dropping the handle releases
the root transport and relation. Production calls no longer retain an
exact-witness relation in a global cache. Invariant R1CS/lincheck tables remain
shared; the older standalone manifest/conformance helpers still have their
own exact-witness cache.

Capacity admission runs the same constraint emitter with a lightweight row
counter before constructing R1CS tables or wiring. It chooses the smallest
power-of-two capacity fitting the busiest table, subject to the existing
minimum. The finished circuit must match every counted table's rows and I/O
arity. This replaces the sum of independently rounded regional budgets.

Arithmetic data zero is kept separate from assertion outputs. Bounded groups
of at most 256 residuals are anchored by constrained `canonical(0,0)` outputs.
This avoids quadratic wiring compilation and a pinned-builder hazard where
later inputs appended to an already merged zero wire could become detached
from its fixed-public class. Regression tests inspect the actual wiring
classes as well as native evaluation and cryptographic proofs.

These capacity/wiring changes alter compiled circuit and relation-manifest
digests. Regenerate Stage 3 artifacts and deliberately update deployment pins
when adopting this compiler; existing Stage 2 roots are unchanged. The Flock
dependency and configuration pins have not changed.

The single relation constrains all eleven registered verifier phases:

- typed witness shape, sparse activation, and active trace heights;
- specialised Aiur verifying-key/AIR metadata;
- all 18 canonical Goldilocks claim words and the 224-byte Stage 2 statement;
- lookup-message inversion, intermediate logUp accumulators, and final balance;
- exact chained-BLAKE3 transcript replay;
- Goldilocks and degree-two extension arithmetic;
- first/last/transition selectors and compiled AIR DAG evaluation;
- alpha-folded OOD composition and quotient recombination;
- every multi-matrix, multi-height PCS opening and BLAKE3 MMCS path;
- every binary FRI beta, grinding draw, query index, fold, roll-in, and final
  polynomial check; and
- one published BLAKE3 Stage 2 root shared by the statement and proof checks.

PCS leaves use the full BLAKE3 tree hasher, including rows wider than one block
and messages beyond one 1,024-byte chunk. Transcript field sampling follows
Plonky3 rejection sampling across the current digest plus one constrained
chained refill. The bounded circuit fails closed only if fewer than two values
are canonical among eight candidates, or among seven after a raw commit-PoW
draw. The latter probability is below roughly `2^-189`.

The manifest is deliberately exact-shape: the current compiler does not pad a
smaller proof into a reusable capacity. All transport/profile words and the
full nested typed-witness layout, activation values and active trace heights
must match. Changing claim values with unchanged specialization preserves the
relation identity. A capacity-based deployment would
require explicit in-relation padding and a new manifest version.

Before witness generation, the production circuit zero-initializes every
recycled Flock slot buffer. This preserves deterministic dummy rows and padding
across heterogeneous relation shapes instead of making proof validity depend
on allocator contents. Deterministically poisoned-buffer tests cover all eleven
production generators across growing, shrinking and empty row sets. The serial
real-proof CI suite exercises all 13
cryptographic vectors in one process specifically to retain this regression.

## Measured integration proof

The integration regression fixture is a real canonical multi-STARK proof with
an inactive leading circuit, active circuits at heights 8 and 4, an active
preprocessed matrix, an 18-word claim lookup, nontrivial first-row/transition
constraints, and two FRI queries.

The release regression produces a **343,867-byte artifact** with a
**343,741-byte production payload**. Exact sizing first reduced its capacity
from `nu=16` to `nu=13`; query-point/denominator reuse now lowers it to `nu=12`
and **192 MiB** padded z/a/b. A standalone local 2026-09-05 run measured
1.46 s of preparation, 1.12 s of proving (including initial lincheck setup and
row evaluation), and 0.012 s of self-verification. Canonicality packing keeps
the same capacity here: 2,173 addition rows now determine it. Before query sharing it was
368,163 bytes / 384 MiB padded. Across compiler versions, fewer rows do not
guarantee smaller proofs when PCS geometry changes. These are diagnostic
timings, not performance guarantees.

Verification costs depend critically on what is reused:

| Verification path | Local elapsed time |
| --- | ---: |
| Explicit prepared-root handle, no rebuilding | 0.011 s |
| Fresh relation in the same process, invariant tables warm | 1.21 s |
| Separate process, no prior Flock preparation/proving | 2.49 s |

The old ~13 ms external-root figure was warm exact-witness cache reuse, **not
standalone verification**. The regression now persists the artifact and
separate external root inputs, then verifies them in a fresh child process.
It also tests the reused handle and fresh-relation paths independently. This
artifact is the off-chain Stage 3 proof, not the sub-kilobyte Ethereum proof.

Run the exact regression with:

```sh
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  -p flock-stage3-host \
  real_stage2_integration_artifact_round_trip -- --ignored --nocapture
```

The ordinary suite exercises relation construction and native/circuit
differential checks without paying the full proving cost:

```sh
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace --lib
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  -p flock-stage3-host --lib -- --ignored --test-threads=1
cargo clippy --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace --all-targets -- -D warnings
```

Print the selected Flock configuration and digest with:

```sh
cargo run --release --locked --manifest-path flock-stage3/Cargo.toml \
  -p flock-stage3-host --bin flock-stage3-config
```

## Production aggregate preflight

Build the optional root connector and compile/evaluate the complete Stage 3
relation for a persisted `ix_aggr` root without starting the Flock prover:

```sh
IX_FLOCK=1 nix develop --command lake exe ix flock-root ROOT_ADDRESS \
  --mode preflight
```

Preflight applies bounded host admission first, natively verifies and expands
the compact Stage 2 proof, constructs the typed AIR/PCS/FRI witness, evaluates
every Flock gate, and prints the Stage 2 advice geometry, `nu`, table capacity,
relation/public sizes, per-gate row counts, union and PCS buffer geometry,
phase timings, process lifetime peak RSS, effective admission limits, and
content-addressed relation/statement digests. The expansion bound is checked
before native proof expansion; table capacity and padded z/a/b bytes are
checked before wiring compilation. These are not total process RSS limits:
compiler, lincheck, PCS and allocator scratch are additional.

Preflight is the mandatory gate before a production-sized
proof. The ordinary suite generates and natively verifies a canonical transport
with the deployed blowup-two, 100-query, 20-bit query-PoW parameters and lowers
its complete typed AIR/PCS/FRI witness. It does not replace a full
production-root Flock proof vector.

Collect a corpus as versioned JSONL (one result per requested root):

```sh
.lake/build/bin/ix flock-root ROOT_A ROOT_B --mode preflight --jsonl
.lake/build/bin/ix flock-root --roots-file roots.txt --jsonl > roots.jsonl
.lake/build/bin/ix flock-root --root-file root.ixon-proof --jsonl
```

`roots.txt` accepts one address per line, blank lines, and whole-line `#`
comments. Batches continue after individual failures and exit nonzero if any
root fails. `prove` and `verify` require one root. Address-mode reads rehash the
wrapper and never create store directories; file mode derives its address
from the bounded input. The historical Mathlib wrapper in `Tests/Fixtures`
is intentionally rejected by the current protocol and is not a usable
production corpus.

Stdout JSONL uses `ix.flock-stage3.root` version 1, with `status`, `source`,
`mode`, and either `error` or `result`. A successful result contains
`details.preflight` (`ix.flock-stage3.preflight` version 1). Reports include
key/proof hashes, activation/heights/layout, protocol provenance, and timing
units in field names. Progress and the successful pre-prove report go to
stderr. RSS is a process lifetime high-water mark, so use separate processes
for individual-root memory comparisons. The operation-level RSS record also
includes proving/verification after preflight.

Flock backend failures cross the Rust/Lean boundary as an `Except` payload
inside `IO`; Lean constructs the actual `IO.Error`. This avoids the pinned
`lean-ffi` helper's incompatible `IO.Error.userError` constructor tag, which
previously produced bogus OS error codes. Exact error regressions cover this
path. Other users of that helper in the kernel/catalog/compiler FFI remain a
separate compatibility-cleanup task; this change does not repair them.

Resource overrides are `--max-advice-mib` (default 256),
`--max-witness-mib` (default 32768, only the padded z/a/b buffers), and
`--max-table-capacity` (default 4194304). Raising a limit changes admission,
not the cryptographic configuration or proof shape, and does not guarantee
that a proof will fit in memory.

Set `IX_FLOCK_TIMING=1` to also retain the count-only diagnostic on stderr
(`ix.flock-stage3.shape-count`, version 1). It reports exact per-gate rows,
capacity, padded-buffer bytes, count time, and process peak RSS **before**
admission. Thus rejected corpus roots can be measured without wiring
compilation. `compiled: false` is intentional: this is not a successful
preflight, evaluated relation, or deployment-owned circuit digest.

Once preflight succeeds, retain the expensive verified artifact explicitly:

```sh
IX_FLOCK=1 nix develop --command lake exe ix flock-root ROOT_ADDRESS \
  --mode prove --output root.stage3.flock
```

The prove command performs preflight, proving, and self-verification through a
single validated witness/relation path. It prints preflight before starting
the prover and does not repeat native Stage 2 verification between phases.

The output is durably installed through an exclusive temporary file and is
never allowed to overwrite an existing artifact. The temporary destination,
directory writability and hard-link support are checked before native
validation/compilation. An abandoned reservation is removed; installation
still fails safely if another writer claims the final name. Artifact framing
is streamed once instead of allocating an extra full encoded copy.
Verify it later against the
persisted aggregate root, which independently derives the expected Stage 3
statement and relation digest:

```sh
IX_FLOCK=1 nix develop --command lake exe ix flock-root ROOT_ADDRESS \
  --mode verify --artifact root.stage3.flock
```

The binary-FRI lowering supports the full height-derived schedule: the prior
eight-round implementation ceiling is gone, with evaluated regressions at 9,
16, and the current 30-round maximum. The isolated Stage 3 workspace's fast
relation/differential suite and serial real cryptographic proof vectors are
both required pull-request CI checks.

## First current-protocol persisted-root measurement

The retained [singleton aggregate fixture](../Tests/Fixtures/Aggregate/singleton-2026-09-05/PROVENANCE.md)
uses the real IxVM and `ix_aggr` circuits, with the production 100-query,
20-bit grinding parameters. It certifies one well-formed axiom declaration,
has 175 active aggregate circuits, and passes fresh-process native
verification. Its 8.6 MB wrapper took 75.8 s to prove at 25.3 GiB sampled RSS.
The fixture generator never accesses the personal store or cache.

After sharing PCS constraints, weighted quotients, query points and denominators,
then packing two canonicality requests per row,
its Flock cost is still much larger than the toy integration fixture:

| Exact Flock count | Toy fixture | Persisted singleton `ix_aggr` |
| --- | ---: | ---: |
| Largest table rows | 33,661 (addition) | 3,162,519 (canonicality) |
| Canonicality rows | 32,857 | 3,162,519 |
| Uniform capacity | `nu=16` | `nu=22` |
| Padded z/a/b | 3 GiB | **192 GiB** |
| Flock proof completed | Yes | No: refused before wiring compilation |

The real-root count took 0.155 s with a 350 MiB process peak RSS. Its capacity
now fits the default `2^22` table limit, but the unchanged 32 GiB padded-witness
guard still rejects it. A `2^21` table override exercises the capacity guard. No Flock
prover was started and no admission defaults were relaxed. See the
[current paired-profile measurement](measurements/packed-canonicality-2026-09-05.json).
The original [3 TiB / 62.9-million-row measurement](measurements/persisted-singleton-2026-09-05.json)
is retained unchanged: this is a 16x padded-buffer reduction on exactly the same
native root, not a smaller or weaker proof fixture.

Recheck the persisted native certificate and collect its count safely:

```sh
IX_FLOCK=1 lake build ix bench-flock-root-fixture
.lake/build/bin/bench-flock-root-fixture \
  --verify Tests/Fixtures/Aggregate/singleton-2026-09-05
(
  ulimit -v 16777216
  IX_FLOCK_TIMING=1 RAYON_NUM_THREADS=8 .lake/build/bin/ix flock-root \
    --root-file Tests/Fixtures/Aggregate/singleton-2026-09-05/root.ixon-proof \
    --jsonl
)
```

The last command intentionally exits 1. CI checks both admission failures
and the stderr/stdout distinction, alongside fresh native fixture verification.
The harness also supports `--output NEW_DIRECTORY [--prove]`; generation
requires a finite Linux address-space cap of at most 64 GiB and refuses
existing directories. See its provenance for reproduction details.

**Next priority:** measure real-root compilation/proving on a suitably bounded
high-memory host, while preserving all constraints and interleaving soundness
review. The 192 GiB estimate covers only padded z/a/b, not peak RAM; a 512 GiB
machine has substantially more headroom now but remains untested. Do not treat
the toy's 3 GiB result as evidence that production aggregates fit. More activation/height
shapes remain necessary before selecting a capacity policy or freezing Stage 4.

## Stage 2 lookup-packing experiment

An explicit `AiurSystem.buildMinOpeningWidth` profile reduces the number of
Stage 2 columns opened by Stage 3. It searches the pinned protocol's existing
circuit-local lookup groups (`k=1..8`), minimizing accumulator **plus quotient**
width within the existing PCS blowup. This accounts for the extra quotient
columns that larger groups can require. Only strict improvements are used;
ties retain the original key. User constraints, lookup order, preprocessed
commitments, FRI queries and grinding parameters do not change.

This changes the aggregate verifying key, allowed-key digest, outer claim and
root. It is experimental and opt-in: default system construction and the
production CLI still use the original keys. The
[new retained fixture](../Tests/Fixtures/Aggregate/singleton-min-opening-2026-09-05/PROVENANCE.md)
contains the **same byte-identical IxVM child**, environment and CheckEnv claim
as the original singleton. Its 175 active circuit heights are unchanged.
The following paired measurement predates query-point/denominator sharing:

| Singleton measurement | Default Stage 2 packing | Minimum-opening-width profile |
| --- | ---: | ---: |
| Sum of active committed column widths | 9,025 | 8,367 (−7.29%) |
| Native root wrapper bytes | 8,565,030 | 8,002,662 (−6.57%) |
| Native aggregate proving, sampled peak RSS | 25.26 GiB | 22.61 GiB |
| Native aggregate proving | 75.813 s | 75.386 s |
| Native aggregate verification | 0.121 s | 0.228 s |
| Stage 3 canonicality rows | 12,792,346 | 12,580,880 (−1.65%) |
| Stage 3 padded z/a/b | 768 GiB (`nu=24`) | 768 GiB (`nu=24`) |

These are single local runs, not throughput guarantees. Smaller native proofs
do not imply proportionally smaller Stage 3 relations: both counts remain in
the same capacity bucket, and native verification was slower in this run.
Neither real aggregate was compiled, evaluated or proven with Flock. The
[measurement](measurements/stage2-lookup-packing-2026-09-05.json) retains both
profiles, all per-gate counts and changed circuit widths. The original fixture
and measurement JSON remain unchanged. The subsequent query-sharing compiler
reduced these same roots to 6,283,484 / 6,072,018 canonicality rows and 384 GiB
padded z/a/b each. Canonicality packing now counts 3,162,519 / 3,056,107 rows
and 192 GiB each; the Stage 2 profile is still explicit opt-in.

Recheck and count the experimental fixture with explicit profile selection:

```sh
.lake/build/bin/bench-flock-root-fixture --min-opening-width \
  --verify Tests/Fixtures/Aggregate/singleton-min-opening-2026-09-05
(
  ulimit -v 16777216
  IX_FLOCK_TIMING=1 RAYON_NUM_THREADS=8 .lake/build/bin/bench-flock-root-fixture \
    --min-opening-width --count Tests/Fixtures/Aggregate/singleton-min-opening-2026-09-05
)
```

The count mode deliberately sets a **one-byte** witness limit and reports
success only after the expected admission refusal. It writes the shape count
to stderr and one `ix.flock-stage3.fixture-count` JSON record to stdout; it
cannot compile wiring or start a Flock prover. The same mode supports the
original fixture without the profile flag. Generation supports
`--min-opening-width --output NEW_DIRECTORY --prove` under the existing 64 GiB
process cap; it never replaces an existing directory.

Tests cover native proof/key round trips, old-key and wrong-claim rejection,
four-message grouped lookups in the recursive verifier (interpreter and
generated code), and a compiled/evaluated Stage 3 relation. CLI regressions
reject implicit experimental-key selection. The native RAM model also now
uses the field's actual extension degree, not an inference from packed lookup
widths; its historical calibration is still approximate and does not replace
process memory caps. An independent soundness review remains outstanding.

## Shared PCS constraints and exact weighted quotients

The compiler now constrains alpha powers, transcript-bound OOD weighted sums,
opening points and commitment bindings once, sharing those wires across
queries. It preserves the PCS's independent exponent counter per matrix
height, including batch, matrix, point and column order. Sharing uses explicit
metadata indices, never `Wire` identity: the count-only emitter intentionally
returns one placeholder wire for every expression.

For each matrix/query, base-field row values use constrained duplicated lanes
for both hashing and scalar multiplication. One weighted row sum feeds all
opening points. For each point, the relation constrains `D + x = z`,
`D * inverse = 1`, and `D * Q + row_sum = opened_sum`, then accumulates
`alpha^offset * Q` into the height bucket. Since `D` is nonzero, these equations
uniquely determine the same weighted quotient as the original columnwise
division. This is exact elimination of auxiliary quotients, using the existing
PCS challenge; it does not replace checks with a new probabilistic combination.
Every source field word remains canonical and bound to its original
authentication/transcript constraints. The Boolean table schemas and arithmetic
output-canonicality checks are unchanged.

Differential tests compare grouped and columnwise reductions across interleaved
heights, repeated matrices, empty/odd/wide column sets, and alpha edge cases.
Compiled-gate tests bypass native prevalidation and public-vector comparison
to reject altered/noncanonical denominators, inverses and quotients, including
a coordinated zero-denominator attack that satisfies both other equations.
The 75 fast tests and 13 serial cryptographic vectors pass; these are not an
independent soundness audit. Circuit, public-layout and relation digests change,
so deployment adoption requires regenerated artifacts and explicit pin updates.

## Shared query points and denominators

Within one PCS query, every matrix at the same LDE height uses the same query
point. The compiler now declares its fixed bit-reversed subgroup factors once
per height and computes one point per distinct height/query, using the correct
suffix of the transcript-derived index bits. Those operands are constrained
base-field embeddings `[x, 0]`, so lane-wise multiplication replaces the
extension multiplication expansion. Arithmetic residuals and canonical outputs
remain constrained; the Merkle authentication and PCS alpha ordering do not
change.

The denominator `D = point - x` and its inverse are shared only within one
query and one `(height, opening-point-kind)` key. The key distinguishes `zeta`
from `zeta * g`, including the generator's log degree. Each distinct denominator
is still canonical, bound by `D + x = point`, and nonzero via `D * inverse = 1`,
including empty column sets. Each matrix/point retains its own weighted quotient
and reconstruction equation. The caches are keyed by explicit metadata, never
wire identities or coincident witness values. Point/denominator caches reset
for each query; only the fixed factors and other query-independent wires are shared.

On the unchanged default aggregate, query-point sharing alone removes 5.50
million canonicality rows; denominator sharing removes another 1.01 million.
The combined count falls from 12,792,346 to 6,283,484 rows, halving padded z/a/b
from 768 to **384 GiB**. The experimental Stage 2 profile also halves to 384 GiB.
At this query-sharing step both remained count-only admission failures, not
evaluated or proven aggregate relations. See the
[paired census and toy proof](measurements/pcs-query-sharing-2026-09-05.json).

Compiled tests use an independent exponentiation oracle for interleaved heights
through 32, repeated heights, distinct query indices and both bit-order extremes.
They reject changed index bits, non-Boolean selectors and wrong coordinate
values/upper lanes without native PCS validation or public-vector comparison.
The same emission is checked with the all-placeholder counting builder. Existing
denominator/inverse/quotient and zero-denominator adversarial tests remain in
place. That query-sharing change retained Boolean table schemas, Flock
configuration and Stage 2 keys, while changing circuit and relation identities
and requiring deliberate artifact/pin regeneration before deployment adoption.

## Packed canonicality checks

The busiest table now packs two `F128` requests (four Goldilocks limbs) into
one row. Its layout uses 256 input bits, 128 independent violation bits and
124 high-bit AND-chain intermediates: **508 columns**, still within the old
512-column table. Every limb retains the exact `value < 2^64 - 2^32 + 1`
check. No probabilistic combination or omitted range constraint is involved.

Requests are paired by emission order, never wire identity or witness value.
Both the count pass and compiled emission explicitly flush an odd final request
against fixed data zero. Zero-residual anchors remain separate output-only
classes with at most 256 assertions. Transcript sampling and the small statement
conformance relation use the same table, with a zero or duplicate second word.

On the unchanged default aggregate, canonicality rows fall from 6,283,484 to
3,162,519. The experimental Stage 2 root falls from 6,072,018 to 3,056,107.
All other table row counts are unchanged, and both roots now fit `nu=22`,
halving padded z/a/b from **384 to 192 GiB**. These remain count-only results,
not real-root compilation, evaluation or Flock proofs. See the
[paired census and standalone toy proofs](measurements/packed-canonicality-2026-09-05.json).

Tests reject noncanonical values in all four limbs, independently recompute
all 128 violation bits in Boolean R1CS, and mutate every requested word across
empty/even/odd batches and assertion-group boundaries. Count/compiled arities,
actual zero-wiring classes and poisoned recycled buffers are checked. All 75
fast tests, 13 serial cryptographic vectors and the separate 100-query full
proof pass. These tests are not an independent soundness audit.

The canonicality table schema, compiled circuit and relation identities change.
Deployment adoption requires regenerated Stage 3 artifacts and deliberate pin
updates. Native roots, Stage 2 keys, FRI parameters, Flock configuration and
admission defaults are unchanged.

## Toy production-parameter sizing and proof

The small integration fixture at the deployed blowup-two, 100-query,
20-bit query-PoW parameters now compiles, proves, persists, and verifies in a
fresh process under the default admission limits. It is still a small native
multi-STARK fixture, **not a persisted `ix_aggr` corpus root**.

| Compiler | Capacity | Largest table rows | Padded z/a/b | Census, no prover |
| --- | ---: | ---: | ---: | ---: |
| Original | `nu=21` | 248,886 | 96 GiB | 653.60 s |
| Exact counting + bounded assertions | `nu=18` | 251,484 | 12 GiB | 2.62 s |
| Shared PCS + weighted quotients | `nu=17` | 103,160 | 6 GiB | 2.01 s |
| Shared query points + denominators | `nu=16` | 65,268 | 3 GiB | 1.84 s |
| Packed canonicality checks | `nu=16` | 33,661 (addition) | 3 GiB | 1.80 s |

The current count/admission pass took 2.69 ms. Slot declaration took 788 ms,
query emission 24 ms, and builder finalization 873 ms in the standalone
census. Useful dense witness is approximately 94 MiB and the PCS codeword
188 MiB: reducing virtual capacity does not eliminate all other memory costs.
Canonicality rows fell to 32,857, but 33,661 addition rows still require
`nu=16`; the toy therefore does not share the real root's latest halving.

The separate full proof produced a **478,483-byte artifact**, with 1.68 s of
preparation, 2.26 s of proving including initial lincheck setup, 0.018 s of
self-verification, and 2.61 s of fresh-process external-root verification.
The proving process reached **5.1 GiB peak RSS**, greater than the 3 GiB
padded-buffer estimate. Explicit verifier reuse took 0.018 s; fresh relation
verification with warm invariant tables took 1.44 s. The prior PCS compiler
measured 3.18 s proving and 8.4 GiB peak RSS. Its artifact was 461,635 bytes:
the current artifact is still larger despite fewer rows, reflecting changed
PCS geometry (47 lanes instead of 35). Timings are local diagnostics, not
guarantees. See the retained
[baseline](measurements/production-parameters-2026-09-05.json) and
[exact-count measurement](measurements/production-parameters-exact-2026-09-05.json),
the [PCS measurement](measurements/production-parameters-pcs-2026-09-05.json),
the [query-sharing census/proof](measurements/pcs-query-sharing-2026-09-05.json),
and the [current packed-canonicality census/proof](measurements/packed-canonicality-2026-09-05.json).

The census is opt-in and never invokes a prover. It also checks acceptance
at exactly 3 GiB / `2^16` rows and rejection one byte/row below those limits:

```sh
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  -p flock-stage3-host --features production-measurements \
  production_parameter_relation_census -- --ignored --nocapture
```

Run the high-memory proof separately, with sufficient headroom for compiler,
PCS, lincheck and allocator scratch beyond the padded-buffer estimate:

```sh
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  -p flock-stage3-host --features production-measurements \
  production_parameter_artifact_round_trip -- --ignored --nocapture
```

Both proof fixtures persist an artifact and separate trusted root transport,
verify in a fresh child process, and reject wrong relation statements and
corrupted proof bundles. The default serial proof suite remains 13 vectors;
the 100-query proof requires explicit opt-in.

## Scope and remaining work

The current relation is deliberately specialised to the configuration used by
Ix: 18 claim words, binary FRI, cap height zero, and an exact activation/height
shape. Host deserialization is witness generation rather than trusted
acceptance; every lowered value reaches a verifier constraint. Native
prevalidation remains an ergonomics and cost guard.

Before freezing a production deployment, Stage 3 still needs:

- a practical memory representation for real aggregate relations: the first
  persisted singleton still requires 192 GiB padded z/a/b after PCS and
  canonicality-packing optimizations (down from 3 TiB), with real proving
  peak RSS unmeasured;
- exact-shape measurements over the intended aggregate-proof corpus rather
  than one small fixture, followed by a decision to freeze one shape or add
  explicitly constrained padding;
- full proof vectors for persisted, production-sized Aiur roots at 100 queries
  and 20-bit query grinding; the small fixture now covers these parameters;
- an independent review of the local Boolean R1CS tables and pinned Flock
  soundness profile; and
- a canonical export of the fixed Flock verifier inputs for Stage 4 witness
  generation.

Design the [Stage 4 verifier boundary](STAGE4-BOUNDARY.md) alongside these
measurements, but do not freeze its relation or exporter until the capacity
policy and production vectors are established. The formalization workspace is
not incorporated into this work.
