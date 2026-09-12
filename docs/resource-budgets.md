# Structural resource budgets

Ixon budget policy reviewed 2026-08-26; IxIR₂ snapshot limits added 2026-09-12.

Corpus-facing execution uses deterministic structural budgets rather than
wall-clock timeouts.  A timeout depends on the host and can interrupt after an
expensive allocation has already happened; these checks derive a charge from
the stored syntax and fail before entering the known superlinear operation.
Limits are inclusive.  Every rejection names a stable metric and records both
the measured value and limit in `Ixon.Work.Exceeded`.

The proof-facing definitions remain unchanged and total.  In particular,
`Sharing.layer1WF`, `Sharing.compress?`, `Sharing.canonical`,
`Constant.address?`, and `Erase.eraseProgram` remain transparent enough for
their existing proofs.  Untrusted or corpus-sized callers use the bounded
wrappers and pipeline preflight.

The catalog-wide framing, duplicate, root, and aggregate policies are detailed
in the [catalog ingress specification](catalog-ingress.md).

## Per-object ingress and addressing

`DecodeCheck.Limits` bounds one encoded constant:

| Counter | Default |
| --- | ---: |
| encoded bytes | 64 MiB |
| expression depth | 512 |
| universe depth | 512 |
| any counted/flattened sequence | 4096 |
| layer-1 sharing charge | 16,777,216 |

The first four counters are enforced during parsing. After parsing,
`checkConstantWith` computes the layer-1 charge linearly and checks it before
calling the quadratic local sharing predicate. `decodeCheckedWith` and
`encodeCheckedWith` use that boundary. External catalog input uses
`checkIxonV2ConstantWith` / `decodeIxonV2CheckedWith`: it pays the same
conservative structural charge before the pinned-ix exact-image check, while
omitting only the local direct-use rule. Their default forms use the table
above.

For table entry `j`, the layer-1 charge includes one structural scan plus one
scan for every earlier sharing index.  Bodies are charged once for bounds and
once per table entry.  Repeated table-to-list materialization, `drop`, and
range construction/traversal are charged as well.  Invalid inputs may
short-circuit earlier, so this is a conservative charge; it is exact on the
full successful scan up to constant-time boolean operations.

Exact canonical addressing has an additional hazard: a small backward sharing
table may inline to an exponentially larger expression forest before entering
the compressor.  `Work.expandedUnits?` computes that expanded size from the
table's already-computed entry sizes without allocating the expansion.
`Sharing.canonicalWith` and the external-policy
`Sharing.ixonV2CanonicalWith` default to:

| Counter | Default |
| --- | ---: |
| layer-1 sharing charge | 16,777,216 |
| fully expanded compressor input units | 4096 |

An expression unit is one AST constructor plus each universe-instantiation
index traversed by hashing, serialization, and structural comparison.
`Sharing.compressWithLimit` exposes the same input-unit gate for standalone
compression. `Constant.addressCheckedWith` composes wire representability,
bounded local validation, bounded exact local canonicalization, and BLAKE3;
`Constant.addressChecked` uses the defaults. Catalog values use the parallel
`addressIxonV2Checked[With]` wrapper and exact pinned-ix canonicalizer under the
same two limits. The transparent `address?` predicate remains the local
theorem-facing identity API.

## IxIR₂ snapshot ingress

The separately versioned [snapshot codec](ixir2-wire.md) uses inclusive
consumer-supplied `IxIR.Bounded.Limits`:

| Counter | Default |
| --- | ---: |
| complete framed bytes | 16 MiB |
| bytes per LEB128 natural, including lengths | 64 |
| elements in any one sequence | 65,536 |
| bytes in any one blob or UTF-8 string | 1 MiB |

The input cap precedes parsing, and sequence/blob counts are checked before
traversal. The grammar has fixed nesting depth; list readers use an
accumulator. File ingress reads at most the cap plus one byte and rejects
oversize input without depending on a prior file-size observation. Rejections
use `Except String`; the Ixon `Work.Exceeded` record above is unchanged.

`Artifact.Fits` exposes the exact recursive representable domain and total
encoded size for roundtrip proofs. `encodeChecked` checks nested bounds before
encoding and total bytes after constructing the encoding; it does not promise
a total allocation preflight on an already supplied in-memory artifact.
Addressed ingress separately applies the existing ownership checker under
consumer-supplied `IxIR2.Validate.Limits`. Read/check budgets do not change the
canonical snapshot root; caches of acceptance evidence must separately key
their applicable budgets and premises.

## Compilation-unit preflight

`Pipeline.Config.limits` defaults to:

| Counter | Default |
| --- | ---: |
| constants | 16,384 |
| stored expression units | 1,048,576 |
| fully expanded body units | 1,048,576 |
| aggregate layer-1 charge | 67,108,864 |
| erased declarations | 32,768 |
| eraser append cells | 67,108,864 |
| certificate candidates | 512 |
| certificate validation attempts | 131,840 |
| certificate source-node work | 134,217,728 |
| usage-check fuel | 100,000 |
| erasure fuel | 100,000 |
| validation fuel | 100,000 |
| lowering fuel | 100,000 |

`Work.programStats` computes all source-derived counters in one pass.
`Pipeline.preflightCheck`, `preflightCompile`, and `preflightValidated` expose
the staged policy, and `checkProgram`, `compile`, and `compileValidated` run
the corresponding preflight before their first semantic check.

The expanded-body counter uses the same non-allocating backward-table size
calculation as canonical addressing. It matters independently of address
minting: usage checking, evaluation, and erasure follow `.share` references
recursively, so a compact valid table can amplify those stages too. A table
with a forward/out-of-range share has no expansion size; the counter falls back
to its stored body size, and the ordinary semantic checker remains responsible
for rejecting that malformed object.

The append charge describes the current implementation, rather than hiding
its cost: a mutual block with `m` emitted members is charged `m(m-1)/2` list
cells internally, and each program-level append is charged the length of the
already emitted prefix.  This counter can disappear when the eraser is
refactored to a reverse accumulator; until then a monolithic quadratic job is
rejected.

## Certificate scaling decision

The validator constructs a `CoverageDB` of per-declaration proof terms.  It
does not discharge one catalog-wide proposition with kernel `decide`, and it
does not use `native_decide`.  Dependency discovery may validate all remaining
candidates in each round; with `n` candidates, the preflight therefore charges

```text
n(n + 1) / 2 + n
```

attempts: the worst productive fixpoint plus the final dependency-ordered
proof-producing pass.  The combined certificate charge multiplies that count
by all fully expanded source body units.  It is deliberately conservative and
makes candidate count, repeated validation, and program size interact instead
of allowing three individually plausible dimensions to form one enormous
job.

The monolithic entry point accepts at most 512 certificate-bearing declarations
under its default policy, subject also to the attempt and combined-work caps.
A larger monolithic catalog is intentionally rejected. The catalog loader
presents the checked, deduplicated constant union and records member/chunk
boundaries. The separate [modular source API](modular-source.md) now checks
consumer-supplied units and composes their evidence, with per-unit obligations
counting public candidates plus executable mutual members. Its source-node
charge includes each unit's full import closure, and aggregate limits count
repeated imported bindings and work before production/checking and assembly.
Record recovery also bounds bytes, syntax depth, sequences, and naturals.

The modular reference assembles 611 reachable declarations from 11 units while
the monolithic entry point rejects the same source at 512. Whole-program
erasure and lowering keep their existing budgets. Automatic catalog
partitioning and compilation of the compiler's full source closure remain
open; this result does not raise defaults or claim standard-library scale.

The [bounded compiler scaling reference](performance/compiler-scaling-2026-09-12/README.md)
exercises the actual defaults. Its independent-declaration family compiles at
352 added declarations (354 certificate candidates) and rejects at 353 on the
combined charge. Its caller-chain family passes source certification at depth
318 and rejects at 319 on that charge, while native selection already rejects
depth 33. Separate minimal fixtures accept 512 candidates at preflight and
reject 513; they do not claim complete certification of a 512-declaration
program. The branch generator also exposes the earlier canonical compression
boundary at sizes 453/454. These are family-specific boundaries, not a new
universal declaration limit. None of the defaults is raised by the experiment.

## Catalog aggregate ingress

`Catalog.loadWith` layers aggregate limits over the per-object policy. It
bounds manifest/member/dependency/storage framing, total piece and payload
bytes, constants/blobs/assumptions/hints, stored and fully expanded expression
units, layer-1 work, and final union cardinality. Fat-profile overlap counts
once per storage occurrence for ingress work and once in the semantic union;
these are intentionally distinct counters. Defaults and exact duplicate/root
semantics are listed in [catalog ingress](catalog-ingress.md). The bounded
filesystem adapter checks declared and observed file sizes before full reads,
but remains in-memory after those gates.

## HPT certificate preflight

The first IxIR₁ result-shape checker has a separate boundary because its
candidate comes from an analysis producer rather than source ingress.
`IxIR1.HPT.preflight` scans both the already-addressed program and the claim
before fact normalization, abstract interpretation, uniqueness checks, or
hashing. Defaults are 32,768 program/certificate artifacts and members, 256
finite shapes per result or recursively nested field fact, 65,536 total root
plus field shapes, 256 fields per detailed constructor shape, 65,536 total
constructor fields, 64 retained field layers, and an inclusive `2⁶⁴` bound on
root/field constructor coordinates and PAP fill counts. The per-fact bound
contains the current insertion-sort
canonicalizer. The field-vector limits bound scans even when all fields are
scalar, and the coordinate bound prevents an untrusted fact from requesting an
effectively unbounded numeral encoding.

`HPT.runWith` and `Pipeline.Artifact.checkHPTWith` expose configurable limits;
their shorter forms use the defaults. Exact-boundary success and one-below
program-artifact, certificate-member, total-shape, per-constructor/total-field,
field-depth, and coordinate failures are compiled into
`Tests.HPTFixtures.resourceBudgetsOk` and
`Tests.HPTFixtures.recursiveFieldOk`. See the
[HPT certificate specification](hpt-certificates.md) for the analysis and
cache scope.

The deterministic producer adds two independent inclusive work caps: at most
256 transfer rounds in one ordinary/SCC artifact and 65,536 rounds across the
whole dependency-ordered program. It builds the declaration index once and
updates a summary hash index per local round; it does not rescan the complete
program in each SCC iteration. Round exhaustion or a generated finite-shape or
field budget overflow widens only the current artifact's function rows to
`top`, then continues. The resulting candidate still passes through
`HPT.runWith`, so a
resource fallback cannot bypass graph, code, post-fixpoint, or content-address
validation. `Tests.HPTFixtures.producerOk` pins exact nine-round convergence,
both global and per-SCC one-below conservative boundaries, repeatability, and
independent shape/field fallbacks.

## Persistent HPT cache ingress

`IxIR1.HPT.Cache.Limits` embeds the producer/checker policy above and adds five
inclusive counters around untrusted cache storage:

| Counter | Default |
| --- | ---: |
| lookup entries | 32,768 |
| bytes in one record | 4 MiB |
| aggregate record payload bytes | 64 MiB |
| replacement-record bytes emitted by one schedule | 64 MiB |
| complete framed store-file bytes | 72 MiB |

`Store.preflight` performs a linear entry/payload scan and rejects duplicate
lookup keys before indexing. `decodeStoreWith` checks the complete file size
before parsing, checks the entry count before building the result, and checks
each declared record size plus the running payload total before copying that
record. It then requires full consumption, lexicographically canonical key
order, byte-for-byte re-encoding, and duplicate-free keys. The filesystem
adapter instead checks non-symlink regular-file metadata and `maxStoreBytes`
before opening the file, then parses the same domain, canonical bounded LEB
counts, strictly increasing keys, and record payloads incrementally. The
running consumed-byte and payload counters are checked before every variable
allocation, and EOF must coincide with the observed metadata size. Thus the
accepted `Store` still retains its bounded payloads, but ingress does not also
retain a complete framed-file buffer.

`IxIR1.HPT.CacheDirIO.Limits` adds a separate scaling envelope: 1,048,576
canonical chunk paths, 256 GiB of complete framed chunk files, and 64 MiB of
dependency-selected record payloads read in one schedule. Each lowercase
`<cache-key>.hpt` file is inspected as a singleton-store header and represented
by key/length/rejection metadata; payloads remain on disk until
`Cache.runLookupWithM` requests them. Malformed canonical-name chunks are local
rejections, so unrelated keys remain usable. The selected-read cap is charged
against the indexed payload length before lookup. A chunk replaced after
indexing can exceed that charge before the length mismatch is detected; the
[reviewed accounting gap](review-2026-09-09.md#2-p2--a-stale-cache-index-undercharges-the-payload-actually-loaded)
remains open. Individual chunks still obey the embedded 4 MiB record and
72 MiB framed-file caps.

The directory-entry and framed-byte caps are checked during admission, but the
portable Lean `readDir` primitive itself returns one complete entry array.
Consequently this first adapter removes payload-sized store residency but does
not yet provide pre-allocation-bounded enumeration of a hostile directory.
Streaming enumeration, sharding/garbage collection, and multi-directory
scheduling remain explicit follow-on work.

`Store.framedSize` and `prepareStoreWith` enforce individual-record,
aggregate, exact-output-size, and canonical-order policy before staging.
Writes emit the domain, count, keys, lengths, and existing record payloads
separately into a fresh sibling directory, flush, and verify the staged spelling
one record at a time. The ledgered native boundary synchronizes the staged file
and transaction directory before atomic rename, then synchronizes both affected
directories, removes the transaction directory, and synchronizes the parent
again. These barriers add file descriptors and storage latency, not payload-sized
heap scratch. Verification scratch space is at most one bounded record; neither
write nor read-back constructs the concatenated store image. Orphan staging
directories are not cache inputs and do not enlarge any ingress counter.

Per-record decoding uses the embedded HPT fact limits. An oversized or
malformed record in an already constructed in-memory `Store` is rejected as a
cache hit and rebuilt locally; persistent ingress and publication reject an
oversized declared/stored record at the outer boundary instead. If the
canonical rebuilt record itself exceeds the record/output policy, the schedule
fails. Aggregate input/store violations are hard admission errors. The final
mixed hit/rebuild certificate still crosses `HPT.runWith`, so none of these
resource fallbacks bypass semantic checking.

`Tests.HPTFixtures.persistentCacheBudgetsOk`, `cacheStoreCodecOk`,
`cacheBoundedNumeralOk`, `persistentCacheFileOk`, and
`persistentCacheDirectoryOk` pin exact and one-below
entry, record, payload, emitted, and framed-file boundaries, bounded-width
numeral rejection, duplicate rejection, canonical ordering, outer corruption
rejection, pre-read filesystem gating, and non-regular input/output rejection.
The file fixture additionally pins exact parity between streamed output and
the pure canonical encoder, exact framed-size admission, overlong count,
truncated-record, reversed-key, and trailing-byte rejection, staging cleanup,
complete replacement, successful file/directory synchronization, wrong-kind
sync rejection, and the fact that an uncommitted orphan leaves the prior cache
readable. The directory fixture adds exact/one-below index-entry, complete
framed-byte, and selected-read limits; lazy stale-corruption isolation; local
selected-chunk repair; canonical key filenames; and fail-closed namespace
hygiene.

## Regression surface and limits of the claim

Elaboration-time pipeline guards set every limit to one fixture's exact
measured requirement, then lower each field by one and require the precise
structured error.  Compiled tests do the same for decode, compressor,
sharing-expansion, address, and HPT boundaries, including a backward table whose
stored representation grows linearly while its expansion doubles.

These counters are executable policy, not a formal asymptotic-cost theorem.
Fuel bounds recursion depth but not every branch operation, and the compressor
input-unit cap is a deliberately blunt bound around a complex
quadratic-to-higher-order implementation. Catalog framing, address/root
binding, duplicate policy, aggregate accounting, constructor ordinals, and
projection member/constructor bounds are now enforced at ingestion. Full
syntax validation of unused `.ixe` name/metadata/comment sections and a
streaming/mmap adapter remain outside the current nameless in-memory boundary.
