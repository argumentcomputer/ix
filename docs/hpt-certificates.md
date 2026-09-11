# IxIR₁ HPT result-shape certificates

This contract covers bounded result-shape analysis, recursive field facts,
checked optimization consumers, and persistent cache production/repair. It is
not a general heap-points-to analysis: parameters begin at `top`, and facts
forget heap identities across potentially mutating operations.

| Module | Responsibility |
| --- | --- |
| [`HPT.lean`](../Compilatrix/IxIR1/HPT.lean) / [`HPTSound.lean`](../Compilatrix/IxIR1/HPTSound.lean) | Abstract domain, bounded checker, concrete interpretation, and evaluator soundness |
| [`HPTProduce.lean`](../Compilatrix/IxIR1/HPTProduce.lean) | Deterministic SCC-local producer |
| [`HPTCache.lean`](../Compilatrix/IxIR1/HPTCache.lean) | Untrusted records, dependency scheduling, and checked local repair |
| [`HPTCacheIO.lean`](../Compilatrix/IxIR1/HPTCacheIO.lean) / [`HPTCacheDirIO.lean`](../Compilatrix/IxIR1/HPTCacheDirIO.lean) | Bounded single-file snapshots and indexed per-key chunks |
| [`HPTCasePrune.lean`](../Compilatrix/IxIR1/HPTCasePrune.lean) / [`HPTCasePruneProgram.lean`](../Compilatrix/IxIR1/HPTCasePruneProgram.lean) | Local/whole-function consumers and whole-program transport |
| [`HPTPAPFuseProgram.lean`](../Compilatrix/IxIR1/HPTPAPFuseProgram.lean) | Composition of case, fetch, destructor, PAP, and reachability consumers |

`Pipeline.Artifact.checkHPT[With]` fixes checking to the artifact's exact
dependency-ordered graph. The [optimizer harness](optimizer-harness.md) owns
pass policies, reports, and fallback.

## Accepted claim

An untrusted certificate supplies one result fact for every declaration in
every `ReaddressAll.Artifact`, in exact artifact and member order. A fact has:

- `mayScalar`, indicating that the result may be a scalar;
- `unknownHeap`, indicating that any runtime heap shape is possible; and
- a finite canonical set of known heap shapes when `unknownHeap` is false.

The finite shapes distinguish partial applications with an exact function
address and supplied-argument count, plus constructor identities in two forms:

- an identity-only constructor has unknown contents; and
- a detailed constructor has an exact source-order field vector.

Each detailed field carries a recursively nested fact with the same scalar,
unknown-heap, and finite-root alternatives. A field can retain a constructor or
PAP root, and each retained detailed constructor can carry another exact field
vector up to the checked field-depth and aggregate shape/field limits.
`bottom`, `scalar`, a singleton heap fact, and `top` are the useful named
points. Shape lists are sorted and deduplicated; `unknownHeap` facts must omit
their redundant explicit shape list, including inside fields.

The checker builds hash-indexed declaration and candidate-summary
environments, interprets every function once, and requires the inferred result
to be below the claim. It also requires:

- content-addressed input program artifacts;
- exact artifact/member coverage and order;
- unique program, declaration, and summary keys;
- canonical facts; and
- exactly `scalar` for the current scalar-only extern ABI.

Every parameter begins at `top`, so acceptance has no hidden caller-specific
precondition. Literals and erased values are scalar. Allocation produces a
detailed constructor whose fields retain each argument's root fact. Reuse also
produces a detailed constructor, but first forgets every argument's finite heap
identity because an argument may alias the overwritten target. A fetch from a
detailed constructor re-roots the selected field fact; a fetch from an
identity-only or unknown dynamic heap value widens to `top`. Known PAP and
out-of-range alternatives contribute `bottom`, since no successful concrete
fetch can arise from them. `papp`, direct calls, `callSelf`, and
under/exact/over-application propagate finite PAP/result facts. Malformed
static references, arities, PAPs, and variables reject the claim. Case
analysis first resolves the scrutinee fact. For each alternative, detailed
constructor shapes with the matching tag and exact field count contribute
their fields, mapped back to facts and reversed from source order into the
evaluator's de Bruijn binder order. Multiple matching shapes join pointwise.
A matching identity-only constructor or an unknown-heap scrutinee widens every
binder to `top`; wrong tags, PAPs, and arity mismatches contribute `bottom` as
unreachable cases. A possible scalar scrutinee contributes a scalar predecessor
to the unary tag-1 branch when Nat peeling is enabled. Detailed binders preserve
the complete retained recursive fact, so later fetches or nested cases can use
the next constructor layer without introducing a caller-specific assumption.

After every primitive binding, all *older* environment facts forget their
finite heap identities while preserving scalar-only information. This is
required even for apparently local operations: `reuse` may overwrite a
location still named by an older slot, and calls/applications may mutate or
consume passed locations. The newly bound result remains precise. A later
alias/ownership-aware domain may retain more facts, but the result-shape
checker does not assume the program is well-moded in order to be sound.

`Certificate.top` is the universal conservative producer: functions receive
`top` and externs receive `scalar`. The ordinary checker still validates graph
coverage and code well-formedness, so this is a fail-safe candidate rather
than a bypass.

## Concrete meaning and soundness

`HeapShape.Holds`, `FieldShape.Holds`, and `Fact.Holds` interpret facts over an
evaluator declaration environment, output store, and runtime value. A scalar
fact covers literals and `erased`. An identity-only constructor shape requires
a live node with the same
constructor identity. A detailed constructor additionally requires the exact
field-vector length and a pointwise `FieldFact.Holds` witness for every runtime
field; those witnesses recurse through every retained detailed constructor
layer. An exact PAP shape requires a live PAP with the claimed function and
supplied count, with its stored arity equal to that function's declaration
arity and the PAP still strictly under-saturated. PAP arguments remain
undescribed. Identity-only constructors still describe only the root, while a
detailed constructor describes all field layers retained by the bounded fact.

`unknownHeap` covers every location, including a stale or dead alias. That is
necessary because a fact can survive only by forgetting its prior finite shape
when an intervening primitive might mutate, consume, or free the location. It
does not assert that dereferencing such a value will succeed.

`analyzeCode_sound` proves every successful abstract code result against every
successful concrete `runCode` result. `invoke_sound` extends this through
direct/self calls, scalar externs, PAP construction, and under-, exact-, and
over-application. The proof is mutually fuel-indexed with the evaluator and
does not assume well-moded input code. `Fact.caseFields_ctor_holds` and
`Fact.caseFields_natSucc_holds` establish the exact refined environment for
constructor and scalar-Nat alternatives, respectively; the mutual case proof
uses those environments directly. `localPostFixpoint_of_postFixpoint` then
turns the executable checker condition into the propositional premise of that
proof. Consequently, `functionSummary_sound_of_runWith_eq_ok` (and its default
limit specialization) says that every accepted function row covers every
successful saturated invocation for arbitrary arguments, input store, and
fuel, provided the evaluator uses the checked program's declaration
environment.

`Pipeline.Artifact.targetDeclEnv` names that exact environment, and
`functionSummary_sound_of_checkHPTWith_eq_ok` /
`functionSummary_sound_of_checkHPT_eq_ok` expose the same guarantee directly
from the production API.

## Checked consumers

### Case pruning and unary collapse

`HPT.CasePrune.run` recognizes a call followed by a case on its newly bound
result. For a finite heap-only function summary, it keeps alternatives whose
runtime constructor index appears in the fact. Dispatch uses the index, not
constructor-block identity; PAP shapes retain no alternative.

A singleton detailed unary constructor with exactly one matching unary branch
permits replacing the case with `let field := fetch x 0; body`. Both forms
preserve the original scrutinee binder, expose the same field, and consume the
same code fuel. Identity-only, nullary, multi-field, and duplicate matching
branches permit pruning only. Scalar-capable, unknown, missing, extern, and
nonmatching cases stay unchanged.

The unary restriction preserves exact fuel behavior. Removing a nullary case
loses a code step; expanding multiple fields into separate fetches adds steps.
General collapse needs a checked batch projection/tick representation or a
separately specified weaker simulation.

`runWithFacts` propagates facts through the complete function using `analyzeOp`,
`forgetHeap` on older bindings, and refined case-field environments. It supports
non-adjacent producers and fails soft for a subtree on abstract-transfer or
atom-resolution error. `runFunction` seeds parameters at `top` and retains the
owner address for dynamic `callSelf`. `runRecursive` is the fixed-environment
compatibility traversal over supplied code and the synthetic main.

| Theorem/API | Guarantee |
| --- | --- |
| `runCode_run_eq` / `runCode_runWithFacts_eq` | Exact evaluator equality at every fuel, including errors, under the checked post-fixpoint and held environment facts |
| `runCode_runRecursive_eq` | Exact equality through supplied continuations/alternatives |
| `checkAndPruneCase[With]`, `pruneCaseWithProducedHPT`, `pruneCaseWithCachedHPT` | Checked, produced, and cached authority paths for one root |
| `checkAndPruneCasesRecursive[With]` and produced/cached variants | Recursive supplied-code traversal |
| `checkAndPruneMain[With]` and produced/cached variants | Actual synthetic-main execution, including self calls |
| `checkAndPruneProgram[With]` and produced/cached variants | Whole graph rewriting, checked readdressing, and installation |

### Whole-program composition

Owner-sensitive rewriting preserves declaration arity/result/PAP contracts
and extern rows. `EvalRewrite.ExactEnvironment` lifts exact body equality
through direct/self calls, applications, and recursive release. Scalar fetch
forwarding preserves complete results/counters; destructor and PAP rewrites
use their distinct successful-run contracts. Their acceptance rules are in
the [optimizer harness](optimizer-harness.md).

`EvalRewrite.AbstractEnvironment` and `HeapHistoryIso` support changes to
allocation history, dead holes, and counters. `fusePair?_refines` covers
under/exact/over application with scalar captures and an unobservable retired
PAP binder. Arbitrary heap captures cannot be classified as shared from HPT
alone, because IxIR₁ no longer carries parameter modes.

Checked reachability then restricts the rewritten old-keyed graph. Its
`compilatrix/ixir1/reachability-input/1\0` identity commits to ordered rows and
main; the certificate binds exported roots and a retained list in input order.
Roots must exist and be retained, and direct call/PAP edges must remain closed.
A reachable dynamic apply requires the complete graph. Producer disagreement
or missing roots keeps the input. `runMain_filterEntries_eq_of_validate` proves
exact equality for the checked restriction.

Changed bodies receive new addresses through one `ReaddressAll.rebuild`.
Temporary producer names, SCC addressing, ordinary content audits, and an
exact-source audit yield a total old-to-final map. Emitted rows have source
producers, reverse images are isolated from occupied namespaces, and no final-key
aliases are installed. `runMain_exact_of_rebuild_eq_ok` transports the complete
result, including addresses in heap nodes and errors.

`runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle` composes the accepted
consumers, restriction, and rebuild. `installPrunedProgram` composes the
artifact's producer address map with the rebuild map. The retained HPT result
describes the **input graph**; recompute it before analyzing the rewritten root.

## Cache and summary identities

Checked results are materialized at `ReaddressAll.Artifact` granularity:
stable extern, ordinary declaration, or mutual SCC. All declarations in a
recursive SCC share one finite artifact, avoiding a cycle between member
summary addresses.

The cache-query preimage uses the domain
`compilatrix/ixir1/hpt-cache-key/3\0` and commits to:

1. artifact kind;
2. the ordinary declaration or mutual-block program identity; and
3. the sorted, deduplicated addresses of already checked dependency summaries.

The summary preimage uses `compilatrix/ixir1/hpt-summary/3\0` and commits to
the cache key plus every canonical member fact. Both are BLAKE3 addresses and
the returned result reruns their exact preimage audit, uniqueness checks, and
pairwise collision diagnostics. Version 3 is the intentional address roll for
the recursively field-aware fact encoding and ordering semantics; earlier
summary identities are not reinterpreted as version-3 summaries.

A cache key identifies an analysis input, not a uniquely chosen post-fixpoint.
Two valid producers may return a precise and a widened fact under the same
leaf query key; their summary addresses differ. Consequently, every persistent
`cacheKey → summary` record is untrusted input. Downstream cache keys name
dependency *summary addresses*, so changing a fact invalidates its dependent
cone while an unrelated artifact remains stable.

`HPTCache` gives one artifact record the independent domain
`compilatrix/ixir1/hpt-cache-record/2\0`. A record contains the artifact kind,
program identity, dependency summary addresses, cache key, complete member
facts, and claimed summary address. Its strict decoder applies the same fact,
shape, field, field-depth, member, coordinate, and record-byte limits used by
production,
requires full input consumption, and re-encodes byte-for-byte to reject
noncanonical tags, naturals, lists, facts, or trailing data.

The complete store uses
`compilatrix/ixir1/hpt-cache-store/1\0` followed by key/length/record triples
sorted lexicographically by the 32-byte lookup key. Store decoding gates the
outer file, entry count, each declared record length, aggregate record payload,
canonical key order, full consumption, and duplicate keys. Stale unique keys
are allowed so a store can serve more than one program version.

`Cache.runWith` walks the current program's committed dependency order. For
each artifact it derives the query from the current program identity and the
addresses of summaries already accepted in this run. A present record is a hit
only if it:

1. decodes canonically within the configured limits;
2. reproduces that exact query and outer lookup key;
3. passes its content-address/canonicality audit;
4. is an artifact-local post-fixpoint against the current summary environment;
   and
5. fits cumulative shape/field limits without an address collision.

A missing or rejected record is rebuilt only for that artifact by the existing
bounded producer. Later queries automatically observe the accepted or rebuilt
summary address, which makes invalidation follow the dependency cone. The
assembled candidate is finally submitted to the ordinary whole-program
`HPT.runWith` checker, and the returned `Cache.Production` stores that exact
checker equality. Hits therefore introduce no alternate proof or trust path.
Statistics distinguish hits, misses, rejected records, producer rounds,
widening, and emitted replacement bytes; rejection diagnostics retain the key
and reason.

`HPTCacheIO.loadFile[With]`, `loadFileOrEmpty[With]`, `saveFile[With]`, and
`refreshFile[With]` persist the canonical store in one regular, non-symlink
file. Metadata size is checked before opening it. The adapter then reads the
domain, canonical bounded LEB counts, sorted keys, and bounded record payloads
incrementally, requires EOF at the observed byte count, and retains only the
accepted payloads in `Store`; it never constructs a second complete framed
file image. Only the explicitly named `OrEmpty`/`refresh` entries treat an
absent file as a cold cache; existing malformed files fail. Writes pass the
individual-record and aggregate policies, compute the exact framed size, and
canonicalize the outer store first—record blobs remain untrusted until
lookup—and `refreshFileWith`
merges only rebuilt rows. A fresh sibling transaction directory receives the
domain/header/key/record chunks directly. After a runtime-buffer flush, the
adapter verifies that staging file one record at a time against the canonical
store. The ledgered `Compilatrix.DurableSync` boundary then synchronizes the
regular staged file and transaction directory before a POSIX-style atomic
rename. After rename it synchronizes both affected directories, removes the
now-empty transaction directory, and synchronizes the destination parent once
more. Before rename the old destination is unchanged; an orphan transaction
directory is ignored by ingress. On the ledger's x86_64-linux filesystem
baseline, a successful return therefore means the complete replacement is
power-loss durable, conditional on the kernel, filesystem, and device honoring
successful `fsync`. A failure after rename may leave the new file visible, but
is reported rather than misrepresented as a durable commit. Concurrent writers
are valid last-writer-wins snapshots rather than a merged transaction.
`Pipeline.Artifact` exposes the pure `produceHPTCached[With]`, single-file
`produceHPTCachedFile[With]`, and indexed
`produceHPTCachedDirectory[With]` forms.

`HPTCacheDirIO` is the first disk-backed scheduling slice. Each canonical
lowercase `<cache-key>.hpt` path contains exactly one ordinary singleton-store
record. A directory scan reads only file metadata plus the store header, key,
and bounded-length prefix and builds `Address → RecordMeta`; it never retains a
record payload. A malformed canonical-name chunk is indexed as a local
rejection rather than poisoning unrelated keys. `Cache.runLookupWithM` computes
queries in dependency order and opens only selected chunks. Selected bytes
still cross the ordinary artifact decoder, exact query and content audit, local
post-fixpoint check, collision check, and final whole-program checker. Rebuilt
chunks publish independently through the same durable staging protocol, so an
interrupted multi-key refresh is a safe mixture of independently checked old
and new records. Recognizable transaction directories and malformed stale
chunks are ignored unless their key is queried.

The chunk adapter bounds metadata entries, complete framed bytes in the
directory, and selected payload bytes separately. Lean's portable `readDir`
currently returns the directory-entry array as one runtime allocation, so the
entry cap is an admission check after enumeration, not a pre-allocation bound
on a hostile directory. This adapter targets a controlled cache namespace;
streaming directory enumeration, sharding/garbage collection, and
multi-directory scheduling remain the next storage-scale layer.

## Deterministic production

`Compilatrix/IxIR1/HPTProduce.lean` supplies the canonical in-process producer.
It consumes the dependency order already committed to by `ReaddressAll` and
solves one ordinary artifact or mutual SCC at a time. Previously solved
dependency summaries remain fixed. Function rows in the current artifact begin
at `bottom`, extern rows at `scalar`, and synchronous rounds replace every
function row by the join of its previous and newly inferred facts. Equality of
two consecutive rows is the convergence test.

The schedule has both a per-artifact round cap and a total round cap. If either
is exhausted, or an intermediate finite fact crosses a configured shape,
field, field-depth, or coordinate bound, the current artifact's function rows
widen to `top`; externs remain `scalar`. Later artifacts continue against that
conservative result. Malformed code, missing dependencies, and final
graph/order failures are not hidden by this fallback.

`produceCertificateWith` returns the candidate plus deterministic round and
widening statistics. `produceWith` then submits that candidate to the ordinary
untrusted `runWith` boundary. Its `Production` result carries the checked
materialization and an erased equality proving that exact checker call
succeeded. Thus no correctness theorem depends on the producer schedule:
`Production.postFixpoint`, `Production.semanticAudit`, and
`Production.functionSummary_sound` eliminate the stored checker evidence.
`Pipeline.Artifact.produceHPT[With]` fixes production to the compiler artifact's
exact target graph.

## Resource boundary

`HPT.preflight` linearly scans the program graph and candidate before
canonicalization, interpretation, uniqueness checking, or hashing. Defaults
are inclusive:

| Counter | Default |
| --- | ---: |
| program artifacts | 32,768 |
| program members | 32,768 |
| certificate artifacts | 32,768 |
| certificate members | 32,768 |
| shapes in one result or field fact | 256 |
| result plus field-root shapes in the certificate | 65,536 |
| fields in one detailed constructor shape | 256 |
| fields in the certificate | 65,536 |
| recursive field depth | 64 |
| constructor/PAP coordinate | `2⁶⁴` |
| producer rounds in one artifact | 256 |
| producer rounds in one program | 65,536 |
| persistent cache entries | 32,768 |
| bytes in one persistent record | 4 MiB |
| aggregate persistent record payload | 64 MiB |
| rebuilt record bytes emitted by one run | 64 MiB |
| complete framed store-file bytes | 72 MiB |
| indexed chunk-directory entries | 1,048,576 |
| indexed chunk-directory framed bytes | 256 GiB |
| selected chunk payload bytes per run | 64 MiB |

The per-fact cap bounds the current insertion-sort normalization cost and is
applied independently at the result and each field root. Field-root shapes
also consume the total-shape counter. The per-constructor and total-field caps
bound vector traversal even when every field fact is scalar. The depth cap is
checked before descending into a nested field vector and applies equally to
checker, producer, and cache ingress. The coordinate cap applies to both root
and field constructor/PAP coordinates and prevents a candidate from forcing an
effectively unbounded canonical numeral allocation;
it deliberately includes the shared encoding fixture at `2⁶⁴`. `runWith` and
`Pipeline.Artifact.checkHPTWith` accept custom checker limits; `run` and
`checkHPT` use `defaultLimits`.
`produceWith` / `Pipeline.Artifact.produceHPTWith` additionally accept the two
round caps in `ProducerLimits`; their shorter forms use
`defaultProducerLimits`. `Cache.runWith`, the cache codecs, and the file adapter
share `Cache.Limits`, which embeds those producer/checker limits and adds the
five persistent-store limits above. `CacheDirIO.Limits` embeds that policy and
adds the three directory/index limits.

## Checked evidence and proof boundary

`Tests.HPTFixtures` exercises content-addressed scalar, PAP, constructor, and
recursive-SCC programs through the checker, producer, cache, and consumers.

| Boundary | Regression coverage |
| --- | --- |
| Sound facts | Detailed fields, nested fetch/case binders, source-to-de-Bruijn order, pointwise joins, exact PAPs, and successful concrete observations |
| Mutation conservatism | An older alias survives overwrite with a different constructor; an exact old-shape claim rejects and unknown-heap remains sound. |
| Consumer behavior | Unary collapse, pruning-only neighbors, aliases/non-adjacent producers, recursive self calls, exact errors, scalar fetch/destruction, and PAP saturation classes |
| Whole-program rewrite | Changed caller and main edge, producer-map composition, dead SCCs, exported/PAP roots, reachable dynamic apply, and one checked rebuild |
| Production | Deterministic facts/identities, local/global round boundaries, conservative widening, and unaffected dependency summaries |
| Cache codecs and repair | Canonical record/store roundtrips, framing/order/duplicate errors, exact/one-below limits, malformed local repair, and precise-to-widened dependency invalidation |
| Filesystem adapters | Cold/warm reuse, file-size admission, durable staging/barriers, cleanup/orphans, malformed stale chunks, selected framing repair, and metadata/framed/read budgets |
| Resource boundaries | Per-fact/aggregate shapes and fields, coordinates, member counts, recursive depth, payload sizes, and producer caps |

`postFixpoint_of_runWith_eq_ok` exposes the checked post-fixpoint;
`semanticAudit_of_runWith_eq_ok` exposes content addressing and dependency order.
`Production` and cached results retain the exact checker equation. Generic
`invoke_sound` uses ordinary logical axioms; accepted materialized certificates
and digest-bound reachability wrappers retain the
[ledgered native BLAKE3 dependency](trusted-extern-ledger.md). The production,
cache, consumer, destruction, and reachability interfaces are pinned in
[`Fence.lean`](../Compilatrix/Fence.lean).

The single-file adapter retains one bounded in-memory store. The chunk adapter
retains metadata and opens selected records lazily. Its selected-read accounting
currently trusts the indexed length: replacement between indexing and lookup
can load more payload than charged, while individual store limits still apply.
The [reviewed gap](review-2026-09-09.md#2-p2--a-stale-cache-index-undercharges-the-payload-actually-loaded)
is tracked under roadmap Q1.

Durable publication is implemented on the ledgered filesystem baseline.
Controlled power-cut testing is additional platform evidence. Streaming
namespace enumeration, sharding/garbage collection, and cross-store scheduling
remain separate scalability extensions.
