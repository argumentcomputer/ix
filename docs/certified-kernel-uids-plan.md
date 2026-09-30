# Certified kernel UID and performance plan

Date: 2026-09-30. Status: design proposal; the UID backend and receipt API
described here are not implemented. Work belongs in an isolated jj workspace,
with completed changes from the original workspace integrated at explicit
checkpoints.

Use compact, arena-local UIDs for expression, universe, and reference identity
inside the certified checker. Keep BLAKE3 `Address` values at Ixon, storage,
commitment, and public API boundaries. Connect the runtime representation to
the existing annotated syntax with proved views, so the checker continues to
produce the existing semantic claims and consistency theorems.

This plan also covers type-level optional presentation metadata, reuse of
successful anonymous declaration checks, sharing-preserving transformations,
cache scope, and the other optimizations needed to make InitStd practical.
UIDs remove repeated identity work; they do not by themselves remove repeated
substitution, validation, or context construction. Full InitStd completion,
accepted-declaration coverage, and performance relative to Con-Leche are
separate release criteria.

## 1. Starting point and evidence

The current certified implementation uses recursive `AExpr` syntax with
existing heap sharing, semantic claims attached to successful results, and
per-frame caches whose candidates are confirmed by structural equality. Its
model remains the specification.
The Rust kernel already separates internal node UIDs from external content
addresses; the earlier `Ix.Tc` implementation supplies a useful pattern for
type-level metadata modes. Neither implementation is a soundness oracle for
the certified checker.

The certified checker does not currently hash every expression with BLAKE3.
Its expected UID gains come from eliminating repeated structural comparison
and preserving sharing. Smaller internal reference keys are an additional
benefit; comparing a 32-byte address is already constant-size work.

| Area | State at this plan's checkpoint | Consequence |
| --- | --- | --- |
| Model and admission | `TypingClaim`, `ConvClaim`, `ReductionClaim`, `AdmissionClaim`, exact ingress readings, and installed type/body fidelity are present. | Preserve these contracts through representation views. |
| Runtime identity | `AExpr` has structural `DecidableEq`. Cache hashes inspect eight levels of shape; public inference wrappers currently supply a constant reference hash. | Both expensive equality and poor bucket discrimination deserve measurement. |
| Existing performance work | Delayed annotation contexts, bounded spine congruence, neutral-spine normalization, height-guided delta, proof-value shortcuts, zero-shift substitution, and a narrow known-formed inference path are present in the performance workspace. | Measure and build on these changes; do not list them as unimplemented UID benefits. |
| Original workspace | Completed coverage changes through `c1ad7afc` have been synchronized. Additional structural metadata/equality work there is separate work in progress. | Coordinate its integration instead of implementing competing versions. |
| Combined validation | The synchronized native build and focused fixtures passed. The latest combined tree has not yet completed the full model/lint/test gate. | Establish a validated, frozen baseline before promoting further code. |
| Address authentication | Certified `Ix.Ixon.Admission.checkBytes` treats supplied addresses as keys. | Add an explicit authenticated boundary if the caller needs a BLAKE3-to-bytes binding; do not assume it already exists. |

Retained measurements motivate this work but do not establish UID gains:

| Experiment | Result | Limit |
| --- | --- | --- |
| Frozen `a22e4d26` versus `c56020f4`, 4,300 primary InitStd records, three measured pairs | 4,375 emitted rows; accepts 2,193 → 2,202 with no lost accepts; median process wall time 31.193 → 26.871 seconds; peak RSS 3,922,600 → 3,923,324 KiB, about 3.74 GiB on both sides. | Coverage changed. This is a supported-profile prefix comparison, not equal-work full-corpus throughput. |
| Full census at `c56020f4` | 24 GiB OOM after 5,707 emitted rows; `List.attach_cons` is next in the retained order. | Incomplete run. |
| Pre-sync focused `List.attach_cons` diagnostic | Annotation finished; body inference accumulated about 1.259 billion structural-equality node visits before timeout. | Instrumented run; generic inference counters missed specialized call sites. It identifies repeated structural work, not its exact caller distribution. |
| Post-sync focused census | 15-second timeout, 85 rows, last emitted `List.pmap_congr_left`; `List.attach_cons` is next in the retained order. | No target START/phase marker. The stalled phase is unestablished. Corrected instrumentation was prepared but not run. |
| Earlier Ix.Tc and Rust on the same 50,540-byte dependency closure | Ix.Tc reported 99/99 in 250 ms; Rust reported 99 accepted in 251 ms. | Diagnostic single runs, with different checking/proof obligations. Not matched certified-kernel speedups. |

The published prefix methodology and fingerprints are in
[the benchmark guide](../Benchmarks/Kernel/README.md). Additional diagnostic
artifacts are retained locally under `plans/review/certified-perf/`; these are
not portable build dependencies. The local Con-Leche reference uses Lean
4.33.0 and a different export format; this InitStd export uses Lean 4.34.0.
Full InitStd certification and matched Con-Leche parity remain unestablished.

## 2. Identity and boundary decisions

Use distinct types for the following identities. Do not reuse the name
`Address` for a runtime UID.

| Identity | Meaning and scope | Equality establishes |
| --- | --- | --- |
| Source `Address` | External anonymous constant/block or blob key. Persistent Ixon identity uses the existing BLAKE3 serialization scheme. | The same key. Exact payload identity additionally requires a unique immutable-store binding. |
| `ExprId` | An expression slot in a particular arena state. | Equal annotated views when both handles belong to that state or a proved common extension. |
| Raw syntax identity | A raw node before annotation, in a validated raw arena or an exact source-table interpretation. | The same raw view, not the same context-dependent annotation. |
| `LevelId` | A structurally interned universe slot. | Equal universe syntax; universe equivalence remains a separate proved relation. |
| `RefId` | A slot holding one exact `ConstRef Address`, including member/constructor positions. | The same resolved reference under the reference-table invariant. |
| `ContextId` | A frame in a context arena, introduced after expression UIDs. | The same context view, including every field used by lookup/reduction. |
| Environment/reduction-view identity | The exact semantic environment and execution policy used by a cache. | A compatible cache scope only with the corresponding invariant or transport proof. |
| Table hash | A cheap noncryptographic hash of a shallow key. | A candidate bucket, never semantic equality. |
| Presentation occurrence | Names, binder information, decorations, and source layout associated with a particular use of a core node. | Presentation identity only. |

The first expression-arena implementation may leave `Address` values in
reference leaves. Replacing those leaves with `RefId` is an independent,
smaller boundary migration. The final runtime environment should use dense
reference indices where useful, with a proved lookup agreement to the
existing `Environment Address`. Model expressions can continue to be
`AExpr Address` throughout.

### External addresses stay stable

Keep the existing canonical Ixon bytes, block/member ownership rules, blob
addresses, projection addresses, Merkle leaves, and proof-store interfaces.
Do not derive a new external address from a UID, allocation order, pointer,
or an erased `AExpr`. Erasure omits layout information retained by the wire
contract; structurally equal model expressions need not identify the same
original serialization.

At a new authenticated interface, verify the existing BLAKE3 address scheme
over the exact retained bytes, using the pure implementation and boundary
proofs. This establishes `hash(bytes) = address`; it does **not** establish
hash injectivity. Within a snapshot, reject conflicting payloads at one key,
including conflicting blob bindings. When a caller supplies new bytes at an
already-seen address, compare the payload exactly before reusing anything.
When a caller supplies only an alias into an already validated immutable
store, reuse the store's exact lookup binding without rereading or rehashing
the same record.

Persistent digest lookup selects candidates. If a cache substitutes cached
content for supplied content, it must establish exact agreement; a verified
digest alone cannot justify substituting a different colliding payload.
Cryptographic commitments may retain their explicitly stated cryptographic
assumptions at the protocol boundary, but kernel consistency must not acquire
a BLAKE3-injectivity axiom.

## 3. Pure arenas with proved views

### Logical API

Keep the existing model syntax unchanged. Introduce a pure arena of shallow
nodes and a total view into `AExpr Address`. Separate expression, level, and
reference IDs prevent accidental mixing. The following is schematic, not a
proposed compiling declaration:

```lean
structure Arena where
  nodes   : Array Node
  levels  : Array LevelNode
  refs    : Array (ConstRef Address)
  valid   : ArenaWellFormed nodes levels refs

structure Handle (a : Arena) where
  slot : ExprId
  live : slot.val < a.nodes.size

def view (a : Arena) (h : Handle a) : AExpr Address
def Ext (a b : Arena) : Prop := -- b preserves a's complete tables

-- Smart constructors return an extended arena, a valid handle,
-- and an equation for the new handle's model view.
-- Existing handles transport along Ext without changing their slot.
```

Index handles logically by the **concrete arena state**, not merely a phantom
session parameter. Pure code can fork one state and append different nodes
at the same next numeric slot in both forks. A session tag alone does not
prevent this. Comparing across states requires transport into a proved
common extension, or an import that re-interns nodes and proves view
preservation.

Start with `Nat` IDs: ordinary small values have a compact runtime
representation, and allocation cannot wrap. Consider checked `UInt64`
packing only after measuring it. Exhaustion of a packed representation must
decline before allocating; it must never wrap or silently truncate.

### Required invariants

1. Every live expression child precedes its parent; universe children obey
   the analogous ordering. Referenced level/reference slots are valid. This
   gives an acyclic DAG and total decoding.
2. Allocation appends at the previous length. Existing slots are never
   overwritten, reordered, or recycled while handles can survive.
3. A node key contains its constructor, child IDs, and every semantic field.
   This includes `PropWhen`, exact references and positions, universe
   arguments, projection fields, let components, and literal meanings.
4. Intern-table hashes select buckets. Reusing a slot requires exact key
   equality with a proved relationship to its view. Forced hash collisions
   must only hurt performance.
5. Extension preserves all old lookups and views. All result and cache
   handles remain valid in the current extension.
6. Derived metadata is computed by safe constructors and has proved
   equations or sufficient bounds. No unchecked input flag controls a
   semantic shortcut.

Initially, retain the intern index for the arena's lifetime. Exact interning
should aim to prove canonicality by induction from canonical children and
canonical ID-bearing leaves: levels, references, and any interned level
vectors must also give one ID to each structural value. Duplicate equal
references or levels otherwise break expression view-to-ID injectivity.
Correctness need not wait for that stronger theorem: equality of valid IDs
in one arena already implies equality of views. Unequal IDs require a
structural fallback unless canonicality is established, and even canonical
syntactic inequality does not imply failure of definitional equality.

Clearing an ordinary result cache causes misses. Clearing only the intern
index can create multiple IDs for equal syntax, so it loses canonicality
unless the index is restored completely. Reclaiming arena storage requires
either discarding every affected handle/cache or proving a root-preserving
remapping into a new arena. An epoch number is useful runtime bookkeeping;
its validity still needs an invariant.

### Runtime layout and allocation discipline

The executable representation should contain compact slot IDs, arrays,
shallow keys, and result IDs. Well-formedness and cache-validity proofs erase.
Use raw cache payloads independent of the arena, with an erased
`CacheValid arena entries context payload` invariant. Prove
`cache_valid_extend` for the identical payload after arena extension; this
transports evidence without mapping entries. Avoid retaining an old arena
value in every cache entry. Check the compiled representation and allocation
profile to confirm both properties.

A transition implementation may retain one shared `AExpr` view per node.
Construct each view once using existing child views, so it preserves DAG
sharing; account for the extra representation in memory measurements. The
eventual hot path must operate on handles. Rebuilding a complete model tree
on every lookup or proof-carrying result would defeat the design. Pure model
views used only in propositions should not be evaluated at runtime.

Import a legacy AST root once at an explicit boundary, rather than
re-interning it for each cache query. A bare pure `AExpr` has no inspectable
sharing identity: this compatibility importer can still visit expanded
occurrences even if the host object graph shares nodes. Budget and measure
that adapter. Direct ingress from Ixon's explicit sharing tables can avoid
this traversal and should move earlier if import becomes the bottleneck.

Thread one arena forward through speculative branches. A failed search may
discard its result caches while keeping allocated slots. Do not roll back
the allocator and let handles from the abandoned branch escape. Independently
forked arenas merge through proved import/re-interning, not integer-ID union.
Pure arrays permit efficient updates when references are unique; that is a
runtime property to measure, not a consequence of the logical extension
theorem.

For reference IDs, use an exact finite table, with inverse laws on allocated
or reachable references. There is no need for a global `Address ↔ Nat`
bijection. [ReferenceMap](../Ix/Kernel/Model/ReferenceMap.lean) already proves
reference restoration on used references, plus erasure, interpretation,
scope, lifting, and substitution transport. With views still in
`AExpr Address`, the immediate obligation is exact reference-table decoding
and environment lookup agreement, plus published-fact and installed-fidelity
lemmas. A full change of the model's reference type is optional; those
existing transport lemmas support it if later needed.

## 4. Proof contracts and equality

The UID implementation must produce the same kinds of semantic evidence as
the present checker, about the views of its inputs and outputs:

| Operation | Required contract |
| --- | --- |
| Intern a constructor | `view` is exactly that constructor applied to the child views. |
| Extend/import an arena | Every retained/imported handle has its previous model view. |
| Compare identical IDs | Equal valid slots in a common arena give propositional equality of views. |
| Structural fallback | A positive result proves view equality. Any negative equality decision needs a proof of structural inequality. |
| Lift/substitute/instantiate universes | `view_lift`, `view_inst`, and `view_instL` agree with the existing operations, at every cutoff. |
| Read raw input | Erasure of the annotated view is exactly the supplied raw term; scope and reference conditions are retained. |
| Infer | Return a result handle with the existing `TypingClaim` about the input/result views. |
| Normalize | Return a result handle and `ReductionClaim`, retaining completion status. |
| Convert | Return `ConvClaim`; its conditional well-denotedness premises remain unchanged. |
| Install | Return `AdmissionClaim` and exact installed source readings, preserving old entries. |

Preserve the public statements of `check_has_model`,
`checkDecls_has_model`, `no_proof_of_False`, and `annotate_erase`, together
with the byte/ingress acceptance and reading contracts. The model's
`PropWhen` annotations remain checked semantic data; they are not optional
display metadata.

A direct proof-carrying UID implementation does not need to simulate the old
search algorithm step for step. It does need the same successful-result
claims and fidelity contracts. If replacing an API with an existing exact
acceptance-domain theorem, either prove compatibility or explicitly update
that domain theorem and its tests. Different fuel accounting and search
order may change declines; measure those changes rather than asserting
algorithmic equivalence.

Use UID equality as the cheapest positive equality path. A stored structural
hash can rule out exact syntax equality only with a proved congruence
property: equal syntax must have equal hashes. Hash equality never supplies
equality. A shallow hash built from noncanonical child IDs does not provide
that congruence for two equal views with different IDs. Do not use it for
negative equality until the missing invariant is proved.

If structural fallback remains costly, compare DAG node pairs with a visited
pair table, carrying soundness of successful comparisons. Bound traversal
work; an exhausted comparison returns unknown/exhausted, not a fabricated
disequality or conversion failure. Keep structural level identity separate
from the existing proved universe-equivalence procedure.

## 5. Optional presentation metadata

Provide a small pure mode type with the same useful shape as `Ix.Tc.Mode`:

```lean
inductive Mode where | anon | meta

def Mode.Field : Mode → Type → Type
  | .anon, _ => Unit
  | .meta, α => α

-- Conceptual wrapper; the core handle is independent of presentation.
structure Presented (m : Mode) (a : Arena) where
  core    : Handle a
  details : m.Field Presentation
```

Use lazy `fieldWith`/`fieldWithM` builders, so anonymous mode does not perform
name resolution or metadata traversal and then throw the result away. Place
the minimal abstraction where it preserves the standalone kernel import
boundary; importing today's `Ix.Tc.Mode` directly would pull in
`Ix.Environment`.

Separate the following categories:

| Data | Storage and checking |
| --- | --- |
| `PropWhen`, references, levels, literal meanings | Mandatory semantic core in both modes. |
| Loose-variable bounds, parameter-presence flags, structural hashes | Mandatory or selectively enabled performance fields with proved correctness; unrelated to presentation mode. |
| Names, binder display information, source positions, user metadata | Optional occurrence data. Anonymous mode can skip their construction. |
| Wire tables, universe spelling, binder/let layout fields needed for exact reconstruction | Retained source/egress information according to the public fidelity contract, even when erased from typing. |

Several named occurrences may point to one core UID. Do not attach one name
to a globally interned semantic node and let the first name win. Likewise,
universe decorations that affect egress must remain attached to the correct
occurrence or retained record. A sidecar can preserve byte-exact layout
without contaminating semantic identity.

Prove that dropping presentation preserves the core view and semantic
results. Metadata-specific validity rules, such as name uniqueness when
required by a named interface, remain separate checks. A successful anonymous
receipt must not bypass them. Anonymous mode may promise semantic checking
without named reconstruction; an API promising exact reconstruction must
retain the necessary source bytes or sidecars.

## 6. Safe declaration reuse by anonymous address

The desired fast path is: check each distinct anonymous declaration once in
a session, then attach additional presentation aliases without repeating
semantic admission. The existing anonymous census already enumerates unique
constant addresses, so this alone will not improve its one-pass throughput.
Its primary benefits are named aliases, repeated queries, and incremental
sessions.

Introduce a session API separate from the current duplicate-rejecting
`checkEnv`/`checkBytes` APIs. The session owns an immutable source snapshot,
the certified environment, arenas, presentation aliases, and successful
admission receipts.

A receipt needs more than `Address → Bool` and more than
`Block.Installed`. Its logical contract should retain:

1. The exact immutable source snapshot and complete admission request,
   including every consumed physical record and blob interpretation.
2. Exact source-reading evidence, including block ownership, member and
   constructor positions, paired recursors, primitive references, and
   relevant incoming height hints.
3. Evidence that the complete admission procedure succeeded on that request
   in its original environment, or an equivalent strengthened validated
   request predicate constructed only by that procedure.
4. `AdmissionClaim before after`, including model extension and preservation
   of old entries, plus `Block.Installed` for every consumed block.

Item 3 is essential. Today's
[installed-fidelity relation](../Ix/Kernel/Fidelity.lean) retains universe
counts, erased types, bodies, and positions. Admission also checks safety,
definition kind, recursor rules/metadata, and other supplied fields, but
`Block.Installed` alone does not retain all those checks. Bind the receipt to
the complete successful request; do not accidentally weaken the admission
policy when designing the cache.

For inductive/recursor pairing, a receipt covers both physical records and
their exact pairing. A family address or display-family key alone is
insufficient. Distinguish the request's owner from derived projections, and
retain exact literal/blob bindings. An immutable snapshot means frozen bytes
with deterministic decoding and unique lookups, not a mutable file path or
a digest obtained before a later read.

On an alias hit in the same session, verify the exact request binding and
that the current environment preserves the receipt's installed entries.
`Block.Installed.mono` provides part of this transport. Adding only a
presentation alias is a semantic no-op with a reflexive admission claim;
there is no need to reinstall the declaration. Keep proof dependencies from
retaining whole historical runtime environments unnecessarily.

Replaying into a different environment is a later feature. It requires
proved dependency/environment agreement and a valid installation transition,
including published facts and reduction policy. Matching dependency digests
or syntax UIDs is not that proof. Cross-process persistence must store a
certificate checked on load, or replay admission: erased Lean proof fields
cannot be recovered from a serialized success bit.

## 7. Cache scope and lifetime

Start by replacing keys inside the existing per-frame cache. Keep its exact
environment and context fixed by the cache's logical type. Only then broaden
its lifetime.

| Cache | Complete identity or fixed scope | Evidence on a hit |
| --- | --- | --- |
| Annotation | Validated raw syntax identity, exact annotation-context view, environment, and ingress interpretation | Exact erasure/reading agreement and any separately established scope facts; annotation is not typing evidence. |
| Inference | Expression UID, exact context, exact environment/reduction view | Ordinary `TypingClaim` for the requested expression and returned type. |
| WHNF | Expression UID, context/environment, reduction strategy/options | `ReductionClaim` and complete normalization status. |
| Conversion | Both expression UIDs, context/environment, relevant policy | `ConvClaim`; canonicalizing pair order requires symmetry transport. |
| Lift | Expression UID, amount, cutoff | Exact view equation. |
| Substitution | Expression UID, replacement UID, cutoff | Exact view equation. A per-operation table may fix the replacement in its scope. |
| Expression universe instantiation | Expression UID and complete actual level vector | Exact instantiated view. |
| Constant payload instantiation | Reference UID, exact environment/entry, actual level vector, and payload selector such as type/body/rule index | Exact instantiated payload; a separate cache can fix the selector and environment in its scope. |
| Scope/reference validation | Expression UID plus universe arity, binder depth, and environment as applicable | The exact validated predicate. |
| Admission receipt | Exact immutable request, original success, compatible current environment | Full receipt contract from section 6. |

The same `bvar 0` UID can have different types in different contexts.
Context identity cannot be replaced by expression closedness heuristics or
an unproved context digest. The older
[context-digest review](tc-context-digest-collision-boundary.md) documents
precisely why expression-hash assumptions do not prove context identity.

Annotation needs its own discipline: the same raw lambda subtree can receive
different `PropWhen` conditions under different local domains. Raw source
table indices are meaningful only with their record/snapshot and exact
reference/blob interpretation. Do not cache annotation solely by a raw
subtree's address or index.

A context arena can later intern persistent frames such as
`(parentContextId, domainExprId)`, with any let value/transparency data that
its executable lookup consumes. Prove its view agrees with the current
`Context.push` and lookup behavior. De Bruijn contexts require shifts;
sharing frame structure does not make those shifts disappear automatically.

For cross-frame reuse, first add a positive cache whose claims were actually
proved at `[]`. Such claims can be used in any context by supplying
`Context.valid_nil`. Cache the exact result/type handles and their scope
facts. Syntactic closedness does **not** let us move an arbitrary claim from
`Γ` to `[]`: an impossible `Γ` can make a semantic claim vacuous. Produce
the certificate at `[]`, or prove a suitable strengthening theorem first.

Cross-declaration reuse comes later, with an explicit environment transport
theorem. An environment extension may add reduction facts or change an
execution view; semantic positive-result transport and reuse of a search
failure have different requirements. Initially keep negative results local,
and never promote exhaustion, failed speculation, or partial WHNF into a
complete result. Distinguish full typing evidence from weaker formedness or
conditional claims wherever their result types differ.

Bound cache retention and make eviction equivalent to a miss. Clearing a
cache does not reclaim the nodes retained by its arena. Measure both costs
before choosing session-global interning or cache lifetimes.

## 8. Other optimizations in priority order

### A. Improve discrimination and measure the real equality callers

Immediately supply a real reference hash at the concrete driver boundary,
retaining exact equality on every cache hit. Current public wrappers use
`fun _ => 0`, and `shapeHash` omits some discriminating fields. Include
reference identity and binder annotations in improved hashes where cheap.
This is a contained change that can precede UIDs.

Instrument actual specialized native call sites to separate cache-bucket
comparisons, direct reflexivity checks, application-domain comparisons, and
other structural walks. Measure bucket lengths as well as hit rates. The
existing billion-visit diagnostic does not yet attribute those visits.
Integrate the original workspace's reviewed structural metadata work before
building a competing implementation.

### B. Preserve sharing through structural operations

Cache loose-variable bounds and universe-parameter presence at construction.
Prove sufficient bounds for early returns. A lift by zero is identity; a
lift or substitution below which all variables are locally bound can reuse
the node. Absence of the variable being substituted is insufficient by
itself: higher de Bruijn indices still decrement. Universe-parameter
metadata must include `PropWhen` conditions. `instL []` is not generally
identity because missing parameters default to zero.

Implement `liftN`, `inst`, and `instL` over the DAG with complete memo keys
and smart constructors. Check cheap metadata before memo-table traffic.
Preserve unchanged child handles, and prove each operation's view equation.
Intern universe vectors if their repeated comparison becomes significant.

A dedicated constant-type/body instantiation cache keyed by reference and
actual levels is a small early slice. Constant inference currently repeats
`entry.type.instL ls` and is excluded from the ordinary inference cache.
Apply the same sharing discipline to ingress, annotation, scope checks, and
reference validation; moving only equality to UIDs leaves those tree walks.

### C. Reuse formedness without weakening input validation

Extend the existing narrow `inferFormedC` path only where the exact input
already has a `FormedClaim` in the exact environment/context. Examples are
re-inferring a type obtained from a successful inference, proof-value
analysis, and annotation fallback. Retain `.formedType` evidence rather
than discarding it and reconstructing it.

The current `.never` application shortcut uses domain uniqueness via
`TypingClaim.appFormedNever`; its result is an ordinary `Typed` and can use
the ordinary positive inference cache. Preserve full front-door checking and
the argument checks/residue required at possibly-Prop binders. A conditional
reduction claim does not establish unconditional formedness. Do not copy an
unchecked internal inference mode into a public input-checking path.

### D. Keep one checking state across a declaration

Start with singleton definitions. Their annotation, type inference, sort
normalization, body inference, and final conversion currently start multiple
public runs and reset caches. Thread one KM/arena state across these phases
under the same reduction view; move annotation fallback into that state.
Add the empty-context positive cache from section 7 before widening scope
across declarations.

Separate recursion-depth fuel, total declaration work, and allocation
limits. Audit charging in `whnfCoreC`, recursive lazy delta, spine loops, and
large structural walks: a counter at inference entry is not a memory bound.
Guard integer output sizes before arithmetic evaluation as well: one
multiplication or exponentiation can allocate a huge result while spending
one call. An exponent ceiling alone does not bound the size of a large-base
power. Use conservative bit-size bounds and an explicit resource decline;
do not immediately enter an equally expensive fallback after that decline.
Maintain bounded speculative congruence and reserve a usable delta fallback.
Staged inductive admission changes environments, requiring either explicit
cache resets or proved transport. Earlier exhaustion is a coverage change,
not a performance win.

### E. Infer application spines and substitute in groups

Peel the application spine into one worklist and defer telescope
substitutions. Accumulate substitutions, instantiate each domain when
needed, and instantiate the remaining codomain once per group. Discharge
accumulated substitutions when normalization exposes a new telescope.
Ordinary recursive application inference already descends to the head once;
the expected savings are fewer intermediate-prefix traversals, codomain
substitutions, normalizations, and cache operations. First implement this
with all current argument checks; then use the same machinery at
known-formed sites and in beta peeling.

Prove bulk substitution agrees with repeated `inst`, and construct the same
typing/reduction claims. Con-Leche's `inferSpineI` and `inferLamsLeafI` are
useful algorithmic references; its separate full/internal checking
distinction must be justified by our own model. Require gains on dependent
telescopes and real proof applications, beyond synthetic spine examples.

### F. Retain typed rule endpoints

Projection iota, structure eta, and rule reduction currently re-infer some
endpoints. Validate and publish typed endpoints once at admission where the
existing facts support it. Prove their environment transport and preserve
exact supplied rule validation.

If profiling still points to `applyTypedC`, develop a conditional internal
application claim: use well-denotedness/domain uniqueness at `.never`
binders, with the full necessary residue elsewhere. This is a separate
proof development, not permission to skip all argument validation. Extend
arithmetic reductions only through checked semantic identities and
certified primitive recognition.

### G. Extend delayed contexts and control retained memory

Reuse annotation's depth-relative context idea in inference behind proved
lookup/view lemmas, avoiding repeated lifting of every old context entry.
Only consider a complete move to free variables or closures after this
narrower change is measured; those representations add context and
substitution proof obligations.

Retain existing input-expansion guards until all relevant traversals respect
sharing. Replace them incrementally with bounded DAG traversal and dynamic
work/allocation limits. A tiny input can still generate large intermediate
work. Introduce arena compaction or declaration-local scratch arenas only
with explicit roots, re-interning, and cache-remapping invariants. Compare
global sharing against per-declaration retention rather than assuming a
global table always saves memory.

## 9. Execution foundations and audit policy

The initial UID design uses ordinary total Lean functions, arrays, exact
maps, `Nat`, and erased proofs. It needs no new axiom, cryptographic
injectivity assumption, process-global counter, or project FFI.

| Technique | Plan |
| --- | --- |
| Pure arena and proved smart constructors | Baseline implementation. Preserve the existing axiom/import/runtime audit boundaries. |
| Proved metadata stored in nodes | Baseline. Inspect compiled layout and avoid repeated model-view evaluation. |
| Computed fields, pointer equality, `csimp`, persistence marking | Optional separate changes with an explicit account of compiler/runtime behavior and measured benefit. Integrate existing work only after its audit implications are reviewed. |
| Unchecked mutable arena, project FFI equality, trusted Rust verdict | Excluded from the initial design. A reference backend can aid differential tests, not supply semantic claims. |
| BLAKE3 verification | Boundary computation over exact bytes. No injectivity axiom in kernel proofs. |

The current [runtime audit](../Ix/Kernel/Audit/Runtime.lean) inspects compiled
closures after proof erasure and execution replacements. It rejects
project-level replacements outside its allowed module prefixes, including
project `csimp` registrations. A mathematically proved replacement still
needs an explicit audit-policy decision under this implementation.
Computed-field machinery may also introduce `implemented_by` behavior; check
the actual compiler output rather than assuming it is audit-neutral.

Do not make a broad allowlist exception or edit expected counts merely to
silence failures. Record the exact new reachable primitives/replacements,
their justification, and the measured closure. Preserve negative audit
controls, standalone-package import isolation, provenance, and the concrete
set-theory consistency audit. Any optional execution-foundation change is
separate from the pure UID representation's mathematical proof.

## 10. Implementation sequence and reviewable commits

Proposed file names below are organizational suggestions, not existing APIs.
Keep model files stable and put representation proofs beside their runtime
operations under `Ix/Kernel/Runtime/`. Each production integration commit
must preserve successful-result claims and pass its applicable gates.

Three supporting slices can proceed after U0 while arena development runs
in parallel. They do not logically require UIDs:

| Slice | Concrete change | Exit criterion |
| --- | --- | --- |
| P1 | Pass a real reference hash at concrete entry points; instrument specialized equality callers and buckets. | Collision controls pass; caller distribution and bucket effects measured. |
| P2 | Retain exact formedness in `inferProofValueC`, `proofIrrelevanceC`, and lambda-annotation fallback where their preceding typing claims supply it. | Existing `Typed` result claims; fewer repeated checks; malformed front-door and possibly-Prop cases still checked. |
| P3 | One state across singleton-declaration phases, with explicit budget/reset semantics. Keep changes to accounting separately measurable. | Exact fixed environment/context; cache reuse measured; resource declines and coverage reported. |

Avoid duplicating these implementations when introducing handles: factor
claim combinators and state boundaries so their proofs can be reused.

| Stage | Deliverable and likely modules | Depends on | Exit criterion |
| --- | --- | --- | --- |
| U0 | Consolidate reviewed original/performance work; freeze source, toolchain, binaries, and corpus. Correct specialized diagnostic coverage. | Current sync | Full combined gate passes; repeatable baseline with complete outcome accounting. |
| U1 | `Runtime/Id`, `Arena`, `LevelArena`, and view/extension lemmas. Pure append-only allocation, exact shallow interning, and the raw-payload/erased-validity representation contract. | U0 | Constructor/view equations, same-arena UID equality, fork separation, collision controls, and measured representation size. |
| U2 | Proved metadata plus sharing-preserving lift/substitution/level-instantiation modules; bounded existing-AST import adapter. | U1 | Operation equations and exact erasure; arena-native transformation work tracks distinct relevant node/parameter pairs, accounting for key/vector/collision costs. Report legacy importer cost separately. |
| U3 | UID keys in per-frame inference/WHNF/conversion caches and equality fast paths; handle-based result wrappers and `cache_valid_extend`. | U1, then U2 for transformed terms | Existing semantic claims, unchanged cache payloads on arena extension, no subtree walk on a UID hit, no lost accepts on matched focused/prefix inputs. |
| U4 | `Runtime/RefTable`, environment lookup bridge, direct ingress to shared nodes, exact boundary/egress restoration. | U1; U2/U3 for direct checker use | Complete source readings and installed fidelity; external bytes/addresses unchanged; no hot-path AST reconstruction. |
| U5a | Integrate P2/P3 with handles and add the empty-context positive cache. | U3, P2/P3 | Explicit context/environment evidence, improved reuse, bounded retention, stable coverage. |
| U5b | Delayed inference contexts with a proved lookup/view bridge. | U3; can proceed beside U5a | Fewer context lifts with identical lookup semantics and claims. |
| U5c | Deferred application/beta spines with bulk substitution proofs. | U2/U3 | Required domain/Prop checks; fewer intermediate substitutions on real dependent telescopes. |
| U5d | Typed rule endpoints, followed only if useful by conditional internal application. | U3 for integration; endpoint proof work is independent | Complete endpoint formedness/admission validation; measured reduction in repeated inference. |
| U6 | Pure metadata mode, presentation sidecars, immutable snapshot and `Session`/`Receipt` alias API. | U4 for reference/source binding; mode prototype can start earlier | One semantic admission per unique request, exact alias/metadata behavior, conflicting-payload rejection, unchanged legacy duplicate policy. |
| U7 | Environment-wide positive caches, bounded retention/compaction; worker and persistence prototypes only where justified. | U5a/U6 and transport proofs | Memory/lifetime invariants, validated imports/certificates, full accounting across resets and worker boundaries. |
| U8 | Promote the UID backend behind public entry points and publish matched corpus results. | Required preceding stages | Full proof/model/import/runtime gates; documented coverage; completed full InitStd runs and honest comparison scope. |

U1's first commit should be small: one arena, append extension, view, smart
constructors, and the handle-equality theorem. Do not start with a global
checker rewrite. Follow with metadata/transformations and cache integration
as independent, reviewable slices. Keep the existing structural backend as
a differential reference during migration; fallback may return only claims
that the fallback itself actually proves.

U5b–U5d are separately promotable, profile-driven changes. Parallel checking
and persistence in U7 are optional for the first InitStd release; do not make
them prerequisites if the simpler backend meets the target. Coverage gaps
in declaration shapes remain admission work with their own model proofs;
UIDs cannot turn an unsupported declaration into a justified acceptance.

Useful parallel work after agreeing on U1's API:

- Arena/view/structural-operation proofs, owned separately from inference.
- Reference tables, metadata wrappers, immutable-source and receipt design.
- Baselines and specialized profiling, then cache/formedness integration
  against the agreed arena interface.

Use separate jj workspaces for edits. Integrate completed checkpoints from
the original workspace without modifying its active working copy. Agree on
shared types before touching inference signatures. Avoid running builds or
censuses concurrently with timing measurements. Do not merge unreviewed
audit-policy changes as an incidental prerequisite of performance work.

## 11. Validation and adversarial cases

Proofs establish soundness; tests exercise executable integration,
serialization fidelity, and resource behavior. Use generated small DAGs and
targeted regressions, not tests that merely repeat constructor definitions.

| Area | Required cases |
| --- | --- |
| Arena identity | Duplicate nodes, different insertion orders, forced constant bucket hashes, same slot in divergent forks, cross-arena handles, stale handles after reset, invalid child indices, checked packed-ID exhaustion if introduced. |
| Equality | Same core with different presentation; same erasure with different `PropWhen`; equal syntax with duplicate UIDs after index clearing; unequal terms that are definitionally equal; universe-equivalent but structurally distinct levels. |
| Transformations | Zero/nonzero shifts and cutoffs, nested binders, capture avoidance, absent substituted variable with higher indices, repeated shared children, universe parameters occurring only in annotations, missing/zero/successor level arguments. |
| Cache scope | Same `bvar 0` under different domains; same raw subtree with different annotation contexts; equal source-table indices in different records; different let lookup data; changed reduction views/opacity/hints; different universe vectors; failed speculation followed by successful delta; partial WHNF, exhaustion, eviction; impossible contexts versus empty-context claims. |
| Formedness reuse | Large already-formed proof/type expressions and corresponding malformed front-door inputs; possibly-Prop binders retain their checks. |
| Source/receipt fidelity | Same key with changed body/type/universes/safety/rules or definition/theorem/opaque kind; conflicting literal blobs; mismatched family/recursor; member/constructor/projection ownership; missing dependencies; duplicate physical records; aliases with invalid presentation metadata. |
| Egress | Byte-exact round trips with differing names, binder layouts, universe spellings, unused side tables, and multiple occurrences sharing one core UID. |
| Lifetime and resources | Cache clearing, arena rollover/compaction, deep shared DAGs, allocation pressure, large-base arithmetic exceeding output-bit limits, cancellation, watchdog timeouts, worker restart, invalid UID rebasing. |
| Persistence, if implemented | Corrupt/truncated candidates, digest collisions/conflicting candidates, incompatible versions, fresh certificate validation; no deserialized success-bit acceptance. |

Retain the existing annotation-context, substitution-sharing,
conversion-spine, and proof-irrelevance fixtures. Add meaningful focused tests
for each new invariant and check the required provenance registrations.
Run the project's full promotion gates in the configured environment:

```text
lake run check-kernel --with-model
lake lint -- --wfail
lake test --wfail
```

Inspect and update audit expectations only from the actual compiled closure.
Verify the standalone kernel package and concrete model through their
existing gates. Native diagnostics must use separate binaries and must not
alter production axioms or silently replace production code in a benchmark.

## 12. Performance protocol and promotion criteria

Freeze source revision plus working-tree fingerprint, executable hash,
toolchain, build flags, corpus hash/order, fuel/work limits, size guards,
height-hint policy, worker count, and machine/resource settings. Rebuild both
baseline and candidate from these manifests. Record budget charging
semantics, including charged operations and per-call versus per-declaration
reset boundaries; identical numeric limits need not mean identical budgets.
Separate budget-policy changes from algorithm comparisons where possible.
An isolated `c1ad7afc`-only baseline and the combined synchronized candidate
binaries have been prepared locally; they are not yet a new paired result.

Warm each binary, then run at least three alternating measured pairs without
concurrent builds/censuses. Use a fixed memory cap and no swap; 24 GiB is the
existing experiment cap, not a claim of acceptable steady-state memory.
Report full process wall time and peak RSS, separating load/decode, arena
construction, annotation, checking, and output where instrumented. A single
cold run, a warm in-process cache hit, and persisted-certificate replay are
different experiments.

Progress through focused structural workloads and the tiny
`List.attach_cons` closure, the established 4,300-primary prefix, a prefix
beyond the blocker, and full InitStd. Then broaden to Lean/Ix and Mathlib.
For every corpus, retain accepted, rejected, declined, blocked, and
incomplete sets by stable source identity. Check missing/duplicate rows and
paired-admission accounting. Summed row timings are not process wall time:
family/recursor admission can be represented in more than one row.

Measure the mechanisms as well as elapsed time:

- Arena nodes and bytes, live roots, intern-index size, peak retained bytes,
  and allocation/reclamation rates.
- UID equality hits, structural fallback visits, bucket lengths,
  hash-collision comparisons, cache hits/misses/evictions by operation.
- Distinct nodes visited by substitution/instantiation, context shifts,
  inferred arguments, repeated type validation, and rule-endpoint inference.
- Anonymous-mode metadata extraction calls and allocations; semantic
  admissions versus presentation aliases.
- Per-declaration and phase latency, tail cases, budget exhaustion, RSS, and
  corpus loading cost. Similar approximately 3.74 GiB process peaks can mask
  checker-only savings; measure phase memory before inferring a setup floor.

Use these promotion conditions:

1. Required proof, model, runtime, import, lint, and test gates pass with no
   unexplained new foundations or weakened fidelity contracts.
2. All baseline accepted declarations remain accepted on the matched corpus.
   Explain changed declines/rejections and report common-accepted work
   separately from additional coverage. More blocked/skipped work cannot be
   reported as a speedup.
3. UID equality/cache hits perform no recursive subtree comparison. Shared
   DAG microbenchmarks track relevant distinct nodes/parameter pairs rather
   than expanded-tree occurrences. This is not a universal linear-time bound
   on type checking.
4. Anonymous mode does no presentation extraction. For M aliases of N exact
   requests in one compatible session, perform N semantic admissions and
   account separately for alias checks and any new-byte authentication.
5. Show stable wall-time and memory improvements on the targeted bottleneck
   and no unexplained end-to-end regressions. Establish acceptable numerical
   thresholds from baseline variance; do not invent a parity claim from
   historical plan targets.
6. A full-corpus claim requires a completed run accounting for every requested
   record. A completed census with declines/blocked declarations is not the
   same claim as successful admission of the whole environment.

For comparisons with Con-Leche, Ix.Tc, and Rust, prepare matching source
declarations/export versions and comparable toolchains, supported features,
hint policy, and timing boundaries. Report differences in certification and
dependency treatment. The Rust documentation's historical per-node hashing
cost concerns a Zisk guest; it is not a measurement of this Lean backend.

## 13. Parallelism and persistence boundaries

Do not introduce a process-global atomic UID allocator into the proof core.
Workers can share an immutable arena prefix; new nodes live in separate
extensions. Even when workers allocate the same integer slot, their handles
belong to different states. Merge by validated import/re-interning with a
proved view-preserving remap. A dependency scheduler must install only
results whose admission claims transport into the actual destination
environment.

In-process proof-carrying results and serialized worker replies have
different trust boundaries. A reply containing IDs or an `accepted` flag is
not proof. Cross-process workers need a checkable certificate or trusted-core
replay before installation. Parallelize untrusted preparation independently
where useful, but count certificate/replay cost in performance reports.

Persistent formats contain canonical source structure/content addresses and
versioned certificates, never pointers or local UIDs. Version the codec,
certificate schema, checker semantics, annotation representation, and
reduction policy. Format-local DAG indices are fine if decoding validates
them and rebases them into fresh runtime handles; they are not portable
runtime identity. Fresh processes build fresh arenas. Defer persistent
normalization/inference caches until the certificate and environment
transport story is implemented and measured.

## 14. Main trade-offs and decisions to revisit

| Choice | Benefit | Cost and decision rule |
| --- | --- | --- |
| Local UIDs versus per-node BLAKE3 | Small keys, cheap positive equality, no cryptographic hashing for transient nodes. | Interning/storage overhead and explicit lifetime invariants. Keep BLAKE3 at boundaries. |
| Canonical interning | Maximizes sharing and makes structural equality an ID comparison. | Stronger completeness invariant; eviction complicates it. Begin sound with a fallback, prove canonicality before relying on negative ID comparisons. |
| Global versus declaration-local arenas | Global sharing benefits repeated types and dependencies. | Retains intermediates; may increase peak RSS. Measure and introduce proved compaction or scratch arenas if needed. |
| Stored model views during migration | Easier reuse of existing claim APIs. | Extra allocation/retention. Remove hot-path reconstruction and measure dual storage before promotion. |
| Per-frame versus broader caches | Broad caches reuse repeated closed work. | Context/environment transport and retention costs. Widen one scope at a time. |
| Occurrence metadata versus metadata in intern keys | Shares semantics across names while retaining accurate presentation. | Requires sidecars and explicit egress contracts. Prefer this split over losing presentation fidelity. |
| Pure node metadata versus compiler-supported computed fields | Both can make structural facts cheap. | Different execution audit implications. The UID plan must remain viable with the pure implementation. |
| Deferred contexts/spines versus a full closure/free-variable rewrite | Targets current allocation with smaller proofs. | May leave other costs. Escalate only when profiles justify the larger representation change. |

The first success criterion is a proved, practical internal identity layer
with preserved external bytes and semantic contracts. The next is removing
the measured structural and repeated-validation bottlenecks. Completion of
this project requires the full InitStd coverage/performance evidence and
audits above; the design alone does not establish either.

## 15. Source map

The implementation links below are the primary references for this plan.
Historical documents describe their own backends/checkpoints; inspect code
before carrying their assumptions into the certified kernel.

| Topic | Sources |
| --- | --- |
| Certified claims and public consistency | [Claims](../Ix/Kernel/Claims.lean), [Consistency](../Ix/Kernel/Consistency.lean), [Check](../Ix/Kernel/Check.lean), [Env](../Ix/Kernel/Env.lean) |
| Model syntax, contexts, and reference transport | [Annotated](../Ix/Kernel/Model/Annotated.lean), [Context](../Ix/Kernel/Model/Context.lean), [ContextTransport](../Ix/Kernel/Model/ContextTransport.lean), [ReferenceMap](../Ix/Kernel/Model/ReferenceMap.lean) |
| Current checking and caches | [Infer](../Ix/Kernel/Infer.lean), [Annotate](../Ix/Kernel/Annotate.lean), [Certified levels](../Ix/Kernel/Certified/Level.lean) |
| Exact boundaries | [Ingress](../Ix/Kernel/Ingress.lean), [Fidelity](../Ix/Kernel/Fidelity.lean), [Byte admission](../Ix/Ixon/Admission.lean), [Admission proofs](../Ix/Ixon/Verify/Admission.lean), [Projection](../Ix/Ixon/Projection.lean), [Ixon format](Ixon.md) |
| Rust identity and interning | [Identity design](kernel_identity.md), [Rust environment](../crates/kernel/src/env.rs), [Rust expressions](../crates/kernel/src/expr.rs) |
| Earlier metadata modes | [Ix.Tc.Mode](../Ix/Tc/Mode.lean), [Ix.Tc.Id](../Ix/Tc/Id.lean), [Ix.Tc.Expr](../Ix/Tc/Expr.lean) |
| Prior cache caveat | [Context digest collision boundary](tc-context-digest-collision-boundary.md) |
| Audits and evidence | [Runtime audit](../Ix/Kernel/Audit/Runtime.lean), [Axiom audit](../Ix/Kernel/Audit/Axioms.lean), [Benchmark guide](../Benchmarks/Kernel/README.md), [Certified roadmap](../plans/ix-certified-roadmap.md) |

The local, unvendored Con-Leche checkout at `plans/refs/con-leche` is an
additional algorithm/proof reference, especially `ConLeche/Cached/CoreC.lean`
(`inferSpineI`, `inferLamsLeafI`) and its verification companions. Local
competitive-kernel and ontology/performance plans contain further ideas;
their proposed trust changes and historical timings are not adopted merely
by reference. This document states the required invariants and gates without
depending on those ignored files.
