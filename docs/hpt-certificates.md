# IxIR₁ HPT result-shape certificates

Status: active. The bounded result-shape checker, deterministic SCC-local
producer, SCC-granular content-addressed summary format, concrete-evaluator
soundness proof, bounded recursive allocation/fetch/reuse and case-binder
field slice, and persistent checked cache ingress/rebuild paths landed
2026-08-26. The filesystem boundary now offers both a bounded single-file
snapshot and a metadata-only per-key chunk index with dependency-selected lazy
reads. A first proof-sized consumer now propagates accepted facts through each
complete stored function body, prunes impossible alternatives, and collapses
the checked detailed-unary singleton case to one checked fetch even when the
producer and case are not syntactically adjacent. Its whole-program path then
performs a content-addressed graph rebuild; its proofs cover dynamic self calls
and exact transport of the complete evaluator result. Conservative scalar
fetch forwarding, scalar/exact-leaf destruction, and PAP/application fusion
now compose with that consumer through the same owner-sensitive traversal.
Checked rooted declaration
reachability then filters their rewritten old-keyed graph before the shared
content-address rebuild.
This is a semantically justified analysis and optimization boundary, not yet
the full heap-points-to optimization pass.

The executable domain and checker are in `Compilatrix/IxIR1/HPT.lean`; their
concrete interpretation and evaluator proof are in
`Compilatrix/IxIR1/HPTSound.lean`. The production pipeline exposes them through
`Pipeline.Artifact.checkHPT[With]`, which fixes the checked program to the
artifact's exact dependency-ordered IxIR₁ graph. `HPTProduce.lean` implements
canonical local production, `HPTCache.lean` implements pure and effectful
untrusted cache scheduling, `HPTCacheIO.lean` is the bounded one-file adapter,
`HPTCacheDirIO.lean` is the metadata-indexed chunk adapter, and
`HPTCasePrune.lean` implements the checked local, compatibility-recursive, and
owner-sensitive fact-propagating rewrites. `HPTCasePruneProgram.lean` closes
the declaration-environment recursion, content-address rebuild, and exact
whole-program evaluator transport. `HPTFetchForward.lean` implements exact
scalar projection forwarding, `HPTDestroy.lean` implements scalar and exact
all-scalar unique-leaf destruction, and `HPTPAPFuse.lean` implements local
PAP/application fusion. `Reachability.lean` implements the exact rooted graph
restriction and its independent checked certificate. `HPTPAPFuseProgram.lean`
composes all five consumers.
`Optimizer.lean` wraps that bundle in the versioned, deterministic, fail-soft
policy and reporting boundary described in the
[optimizer harness](optimizer-harness.md).

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

## First checked consumer

`HPT.CasePrune.run` recognizes one supplied code root of the form

```text
let x := call f(args); case x of alternatives
```

where the case scrutinizes the newly bound `x`. If `f` is a function and its
row is finite and heap-only (`mayScalar = false` and `unknownHeap = false`),
the pass retains exactly those alternatives whose runtime constructor index
occurs in a constructor shape in the row. Constructor dispatch observes the
index, rather than the constructor block identity; PAP shapes retain no case
alternative. If the row contains exactly one detailed unary constructor and
filtering leaves exactly one unary branch with that index, the pass replaces
the case by `let field := fetch x 0; body`. The fetch and original case are
both non-consuming, retain `x` beneath the field binder, and consume the same
code fuel. The output reports removed alternatives, collapsed cases, and
materialized fetches. Scalar-capable, unknown-heap, missing, extern, and all
nonmatching syntax paths are returned unchanged; identity-only, nullary,
multi-field, and duplicate matching branches remain pruning-only.

The unary restriction is intentional under the current exact fuel-indexed
theorem. Erasing a nullary case removes a code step, while materializing two or
more fields as separate fetches adds code steps. General collapse therefore
waits for a checked batch projection/tick representation or a deliberately
weaker fuel simulation; the optimizer does not blur that semantic choice.

`HPT.CasePrune.runWithFacts` is the whole-function form. It mirrors the HPT
transfer at every program point: `analyzeOp` supplies each new binding fact,
all older facts cross the analyzer's `forgetHeap` mutation boundary, and
`Fact.caseFields` supplies the refined binder environment for each case
alternative. A case may therefore consume a fact propagated through aliases,
allocations, fetches, direct or self calls, PAP construction/application, and
other analyzed primitives rather than requiring an adjacent call. An abstract
transfer or atom-resolution error is fail-soft for that subtree.

`runCode_runWithFacts_eq` proves exact evaluator equality for this general
traversal from a local post-fixpoint, the current function's owner binding, and
a pointwise concrete interpretation of the input fact environment. The public
`analyzeOp_sound` theorem is the operation-level bridge used to extend that
environment after each successful primitive. Case alternatives use the
constructor and scalar-Nat binder soundness lemmas directly. The result covers
every fuel, success, and error without assuming well-moded code.

`runFunction` seeds every parameter with `top`; `rewriteCurrentAt` retains the
function's arity and result-world contract while making its address explicit
for `callSelf`. A strong fuel induction proves both arbitrary-frame equality
and combined rewritten-body/current-frame equality. Recursive self entry uses
the owner-sensitive body theorem at strictly smaller fuel.

`runRecursive` remains the fixed-environment compatibility traversal for a
supplied `Code`, including the top-level main, which has no declaration owner.
It descends through every continuation and alternative body and applies the
adjacent-call `run` form. `rewriteCurrent` and `runMain_runRecursive_eq` account
for the evaluator's synthetic main frame and dynamic `callSelf` re-entry.

`CasePrune.runCode_run_eq` proves exact `runCode` equality for every fuel,
store, environment, current function, success, and error whenever the supplied
summary environment is a local post-fixpoint for the evaluator declaration
environment. HPT soundness ensures that a live constructor's first matching
alternative survives filtering. For collapse, the detailed unary field vector
proves that fetch zero succeeds and produces exactly the branch environment at
the same fuel. `runCode_run_eq_of_runWith_eq_ok` specializes this to an accepted
untrusted certificate. The core theorem uses only the ordinary Lean logical
axioms; its checked specialization inherits exactly the ledgered native digest
dependency already used to materialize HPT summaries.

`CasePrune.runCode_runRecursive_eq` lifts the exact equality through the
complete supplied-code traversal by induction on evaluator fuel. Rewriting
alternatives preserves first-match dispatch, and the selected rewritten body
is equivalent at the smaller fuel. Its accepted-certificate specialization
has the same trust boundary as the one-root form.

The pipeline exposes `checkAndPruneCase[With]` for untrusted certificates,
`pruneCaseWithProducedHPT` for direct proof-carrying production, and
`pruneCaseWithCachedHPT` for checked cache hits/rebuilds. Their evaluator
corollaries are pinned in `Compilatrix/Fence.lean`. The corresponding recursive
APIs are `checkAndPruneCasesRecursive[With]`,
`pruneCasesRecursiveWithProducedHPT`, and
`pruneCasesRecursiveWithCachedHPT`; all three authority paths have separately
pinned exact-evaluator corollaries. For the artifact's actual main,
`checkAndPruneMain[With]`, `pruneMainWithProducedHPT`, and
`pruneMainWithCachedHPT` expose the self-call-aware form and exact `runMain`
corollaries.

`rewriteDeclarationAt`, `rewriteEntries`, and `rewriteCtx` apply the
owner-sensitive traversal to every stored function while preserving extern
declarations, function arities, and result-world contracts. The declaration
address is threaded through both logical environment lookup and concrete list
rebuilding. `HPTCasePruneProgram.lean` proves this logical old-keyed program
an instance of `EvalRewrite.ExactEnvironment`: misses and externs are retained,
calling conventions are stable, and each owner-sensitive rewritten body is
exactly equivalent in the source context. The generic fuel induction then
covers direct calls into rewritten bodies, dynamic `callSelf`,
under/exact/over-application, PAP application, recursive drop entries,
successful stores and values, every error, and instruction counters.

`HPTFetchForward.lean` adds an exact owner-sensitive consumer for the local
shape `let node := alloc/reuse ctor fields; let field := fetch node i; rest`.
When the selected source atom is HPT-proven scalar, it replaces the fetch with
`pure` of that atom lifted across the retained node binder. Both original
binders and the constructor operation remain, so `runCode_forwardHead?_eq`
proves equality of the complete evaluator result, including fuel behavior,
store layout, allocation identities, and counters. The scalar gate is the
syntax-ownership boundary: forwarding a heap-valued field source could
duplicate an owner after installing it in the constructor. Missing facts,
heap-capable sources, and out-of-range fields remain unchanged.

`runCode_runWithFacts_eq_ownerCompatible` lifts the local equality through the
same recursive HPT transfer used by case pruning. It accepts either a real
stored-function owner or the top-level convention that the synthetic owner has
no summary. This supports fresh allocations and successful in-place reuse with
one theorem, while failing closed around ambiguous `main` owners.

`HPTPAPFuse.lean` adds the first O1 consumer. Its executable checker recognizes
an adjacent PAP allocation and application, validates the declaration arity,
proves all captures scalar from the current HPT environment, lowers supplied
operands across the consumed binder, and proves the continuation cannot observe
that binder. It emits a larger PAP, a direct saturated call, or a direct call
plus residual apply. Both binder positions remain in the target syntax, so the
rewrite does not depend on a global de Bruijn substitution.

Removing the source allocation cannot preserve literal `Store` equality: it
changes dead slots, cost counters, and every later numeric allocation index.
`EvalIso.lean` therefore proves all eight mutually recursive evaluator entries
congruent under `HeapHistoryIso`, a finite partial heap bijection which covers
live nodes, may remember dead/dead history, and ignores counter and hole
numbering. `fusePair?_refines` uses that relation to prove every accepted
under-, exact-, and over-saturated decision preserves successful evaluation at
arbitrary fuel. The scalar-capture restriction is the current ownership
boundary: IxIR₁ declarations retain result ownership but not parameter modes,
so HPT cannot certify an arbitrary heap capture as shared.

`EvalRewrite.lean` packages two declaration-environment relations over the same
owner-sensitive calling boundary. `ExactEnvironment` preserves complete
evaluator results and is used by case pruning; `AbstractEnvironment` preserves
successful body runs modulo heap allocation history and is used by PAP fusion.
Their common evaluator arguments cover direct calls, dynamic `callSelf`, PAP
application, and reclamation entries.
`HPTPAPFuseProgram.lean` instantiates those relations for the composed
case/fetch/PAP rewrite, proves top-level main refinement under a fail-closed
synthetic-owner condition, and transports the result through one exact
content-address rebuild. A successful HPT check plus successful rebuild
therefore authorizes
`runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle`; fetch forwarding
version 1, PAP fusion version 1, and reachability version 1 are enabled in
`defaultPolicy`.

`Reachability.lean` checks a second, deliberately small certificate after the
body rewrites and before rebuilding. Its
`compilatrix/ixir1/reachability-input/1\0` digest commits to the exact ordered
old-key declaration rows and exact rewritten main; the certificate also
commits to the exact configured exported-root list and a retained-key list in
input order. A proper subset is accepted only when every root exists and is
retained, and every direct `call` or `papp` edge in main and each retained body
either names no local declaration or names another retained key. `callSelf`
stays inside its retained owner. A reachable dynamic `apply` is conservatively
open-world in version 1, so the checker accepts only the complete declaration
set in that case.

The deterministic closure producer is untrusted and immediately rechecked.
Producer/checker disagreement, including a nonexistent configured root, keeps
the complete graph. `runMain_filterEntries_eq_of_validate` proves exact
evaluator equality for a valid restriction by a simultaneous fuel induction
over code, primitive operations, and invocation; it covers case alternatives,
direct calls, PAP lookup, self calls, externs, and recursive drop/free helpers.
`runMain_run_eq` lifts that result through the fail-soft wrapper. The composed
program proof first rewrites against the complete logical declaration
environment, transports the result to the checked restriction, and only then
uses the existing exact readdress theorem. Thus pruning a declaration or an
entire dead SCC adds no second rebuild and does not weaken the successful-run
history refinement of PAP fusion.

Changed function bytes cannot retain their old content addresses.
`ReaddressAll.rebuild` therefore alpha-renames function producers into a
domain-separated temporary namespace, runs the ordinary SCC-aware address
pass, and exposes only the final graph and the composed old-to-final map. It
fails closed unless both the ordinary content-address audit and an
exact-source audit pass. The latter checks the rewritten main and every source
row under the total `rebuildRename`, rejects reverse images that are not holes
in the emitted environment, and requires every emitted declaration to have a
source producer. `runMain_exact_of_rebuild_eq_ok` then transports from the
exact old-keyed declaration environment, without installing final-key aliases.

The composed optimizer joins that rebuild to the logical HPT theorems and
reports declaration removals, alternative removals, collapses, materialized
fetches, forwarded fetches, and PAP fusion classes across the main and all
retained declarations. The pipeline exposes
`checkAndPruneProgram[With]`, `pruneProgramWithProducedHPT`, and
`pruneProgramWithCachedHPT`; `installPrunedProgram` installs the result while
composing the artifact's original `targetAddressMap` through the rebuild map.
The returned HPT analysis still describes the input graph and is deliberately
documented as stale for the rebuilt graph. The checked theorem transports the
complete `RunResult` through `Readdress.mapRunResult`, including addresses in
heap nodes and errors, rather than proving only equality of a scalar result.

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

`Tests.HPTFixtures` uses a content-addressed program containing a stable
extern, a scalar target, PAP construction plus exact application, a constructor
with one scalar field, and a genuine two-function SCC. One SCC branch allocates
that constructor and fetches its field. `fieldSensitiveOk` checks the detailed
produced row, precise/unknown/out-of-range fetch transfers, the concrete stored
field, and the concrete projected scalar;
`detailedConstructorAcceptedFact_sound` instantiates the accepted-row theorem
at that detailed result. The fixture freezes five version-3 cache keys and five
summary addresses. A precise/widened pair proves executable
dependency-cone invalidation; underclaim, noncanonical, wrong-identity,
reordered, and over-budget candidates fail closed. The exact structural limit
fixture counts one field and succeeds; one-below field, shape, member, and
coordinate limits fail. A separate deliberately ill-moded alias/reuse fixture
allocates constructor A, aliases its unique location, reuses it as constructor
B, and returns the older alias. The exact-A claim is rejected, the unknown-heap
claim is accepted, concrete execution observes B, and
`aliasReuseAcceptedFact_sound` instantiates the semantic theorem at that
boundary. `casePruneOk` checks the first consumer at a real two-alternative
call-result case: the accepted detailed unary row removes the impossible
branch, collapses the remaining case to one fetch, and preserves the exact
scalar result and store observations. It also pins pruning-only behavior for
identity-only, nullary, binary, duplicate-match, and universal facts, plus a
singleton collapse whose removed-alternative count is zero.
`recursiveCasePruneOk` nests that redex in both bodies of an outer case: the
one-root API changes nothing, recursive traversal removes two alternatives,
collapses two cases (including the unexecuted outer branch), materializes two
fetches, both executable paths agree, and the checked universal row again
changes nothing.
`callSelfCasePruneOk` runs a one-argument current body that recursively peels
`3` to zero, enters the rewritten base branch through three dynamic self calls,
and confirms that original and rewritten current/body pairs return the same
scalar and store after the impossible alternative is removed and the unary
case is collapsed.
`pipelineCallSelfMainPruneOk` crosses the checked artifact-main pipeline on a
zero-argument self-loop and confirms that the original and pruned mains have
the same exact finite-fuel `.fuel` result.
`declarationGraphCasePruneOk` crosses the complete checked program API: it
rewrites a stored caller, removes one impossible alternative, collapses its
case with one materialized fetch, changes the caller's content address,
rewrites the main edge, passes both ordinary and exact rebuild audits,
preserves the detailed concrete result/store, and checks that artifact
installation composes the original producer address map to the new caller.
`reachabilityCertificateOk` starts from four content-addressed functions: main
reaches a caller and leaf while a two-function mutual SCC is dead. The checked
closure retains exactly the first two rows; exporting either SCC member retains
both; a standalone PAP root retains its target; and reachable dynamic apply
retains the complete graph. A nonexistent root fails soft to the input.
Separate candidates with a stale input digest, substituted root list, and
canonical-but-unclosed retained list are rejected. Original and filtered
execution both return Nat `42`.
`reachabilityHarnessOk` crosses HPT production, the default optimizer, and the
single rebuild. It reports two removed declarations and four-to-two functions,
removes the mutual artifact, preserves content-address audits and execution,
honors the exported-root policy, and selects the original graph for an
unsupported reachability version.
The destruction decision guard accepts scalar `drop`/`dropU` and one exact
constructor with a complete all-scalar field vector, while rejecting shared
constructor destruction, heap-valued fields, identity-only facts, multiple
shapes, widening, unresolved variables, and unrelated operations. The native
pipeline fixture crosses HPT production and the one-rebuild optimizer on a
sentinel-owned main, attributes one scalar-drop elimination and one unique
leaf specialization, changes static `dropU` to `free`, preserves the exact
Nat result and allocation/free/live observations, and reports an unchanged
second run; an unsupported destruction version fails soft to the input graph.
The adjacent recursive-fuel guard pins the current IR boundary with two
successful-source counterexamples: inline `fetch`/`free` expansion exhausts
continuation fuel, and the equivalent stored helper exhausts call-entry fuel.
Consequently deeper unique plans and the shared RC-zero branch are staged with
the fuel-neutral consuming-destructure/reset primitive rather than encoded as
ordinary IxIR₁ `Code`.
The pipeline integration suite separately compiles a usage-checked Ixon
constructor main alongside six stored functions with only one runtime-reachable
target. The default optimizer removes the other five and preserves the exact
shared constructor result, so declaration removal is pinned on compiler output
as well as the hand-written IxIR₁ graph.
Deterministic production reproduces the hand-written precise
certificate and all five frozen summary identities in nine rounds. Repeating
it returns the same candidate/result. Nine rounds is the exact global fixture
boundary; either an eight-round global cap or a two-round local cap widens only
the recursive SCC and remains accepted. Zero-shape and zero-field checker
budgets independently force only the constructor artifact to `top` and also
remain accepted. Persistent-cache regressions pin a five-miss cold run, a
five-hit warm run, deterministic store bytes under reversed insertion order,
record and store roundtrips, noncanonical/trailing-byte rejection, duplicate
keys, bounded-width count/coordinate numeral rejection, every exact and
one-below byte/count boundary, local repair of one
malformed record, and a precise-to-widened dependency-cone rekey with unrelated
hits preserved. Temporary-file tests cross both the generic and pipeline file
APIs, including absent-file creation, warm reuse, pre-read file-size rejection,
outer framing corruption, local persisted-record repair, complete atomic
replacement, successful file/directory barriers, wrong-kind barrier rejection,
staging cleanup, and an ignored interrupted-write orphan while the prior
destination remains readable.

The chunk-directory fixtures additionally pin absent-directory creation,
pipeline cold/warm reuse, canonical lowercase key filenames, exact and
one-below metadata-entry/framed-byte/selected-read budgets, malformed stale
chunk isolation, selected outer-framing repair, per-key transaction cleanup,
and rejection of names outside the controlled cache namespace.

`caseBinderFieldOk` uses a separate content-addressed caller so the five frozen
cache identities remain unchanged. It checks source-to-de-Bruijn reversal,
pointwise joining of multiple detailed shapes, wrong-tag filtering,
identity-only and unknown widening, alias-forgotten field conservatism, and Nat
successor recovery. Both the ordinary checker and deterministic producer infer
the caller's scalar result, direct inference agrees, and concrete execution
returns Nat `7` with one live allocation. `caseBinderAcceptedFact_sound`
instantiates the accepted-row semantic theorem for that result.

`recursiveFieldOk` adds a depth-two constructor fixture. It checks exact
two-step fetch precision, nested case-binder precision, deterministic
production, and concrete Nat `11` execution for both paths. Exact depth-two
checker/cache limits accept the artifact, one-below depth limits reject it,
the recursive record/store codecs round-trip it canonically, and a shallow
producer widens conservatively while retaining its post-fixpoint and semantic
guarantees.

The file/directory durability barriers are implemented and ledgered. Controlled
power-cut fault injection remains desirable platform evidence, not a missing
step in the commit protocol. The single-file adapter still returns one bounded
in-memory `Store`; the chunk-directory adapter instead retains metadata and at
most one selected bounded record payload at the storage boundary. Streaming
directory enumeration, sharding/garbage collection, and cross-store scheduling
remain broader scalability work.

`postFixpoint_of_runWith_eq_ok` exposes the exact executable post-fixpoint
gate; `semanticAudit_of_runWith_eq_ok` exposes the returned content-address
and dependency-order audit. Default-limit specializations are provided under
the corresponding `run_eq_ok` names. Their axiom cones are pinned in
`Compilatrix/Fence.lean`, including the ledgered native BLAKE3 exception used
by materialization. The generic `invoke_sound` evaluator theorem stays within
the ordinary `propext`/`Classical.choice`/`Quot.sound` set; composing it with an
accepted, materialized certificate adds exactly that already-ledgered native
hash axiom. Both direct-production and persistent-cache result layers,
together with the one-root and recursive pipeline corollaries, are
mechanically pinned. The two public reachability equalities are pinned as
well. The destruction fence separately pins the accepted local arbitrary-fuel
refinement and its owner-sensitive recursive traversal. Reachability's
restriction induction is semantic, while its public validation
premise exposes the same ledgered native BLAKE3 axiom because it commits to the
exact reachability input digest.

Record-streamed, power-loss-durable publication and the first disk-backed,
per-artifact lazy chunk schedule are landed on the ledgered filesystem
baseline. Cross-store scheduling, streaming/sharded index maintenance, and
controlled power-cut recovery testing remain future scaling/platform evidence.
