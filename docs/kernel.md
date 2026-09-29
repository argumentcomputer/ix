# Certified Lean kernel

`Ix.Kernel.check` checks an ordered list of anonymous declarations and returns
an environment only when it can construct its model extension. The three
public consistency theorems apply to this executed function. `Ix.Kernel` is
being developed to replace `Ix.Tc`; the runtime consumer migration remains
pending. D01 removed lean4ix and the legacy verification machinery.

The implementation sequence and remaining gates are in
[`plans/ix-certified-roadmap.md`](../plans/ix-certified-roadmap.md). This page
records the current contract and the disposition of the old verification
system. It does not certify the Lean-to-Ixon compiler, Rust checker, or IxVM.

## Data and evidence

| Layer | Meaning | Established by |
| --- | --- | --- |
| `Decl`, `Block`, `Const`, `VExpr`, `VLevel`, `ConstRef` | The supplied declarations, member/constructor positions, terms, and positional universes | Input data, without a typing assumption |
| `Ix.Ixon.Types`, `Ingress.Context`, `ExprReads`, `BlockReads` | Pure production Ixon data and its exact reading after table, projection, sharing, and literal resolution | `readExpr_reading`, `readBlock_reading`, and reading determinism |
| `Egress.Record`, expression/declaration layouts | Raw payloads plus the sharing, table, and let-spelling choices needed to reconstruct the source | Checked writer readings and `records_roundtrip`, with exact list equality |
| `Ix.Ixon.Codec`, `Ix.Ixon.Wire`, `Ix.Ixon.Verify` | Production anonymous byte grammar, representable counts/address widths, and cursor/append laws | All-variant serializer inverses, exact constant framing, and separate codec audits |
| `Ix.Ixon.Bounded.Universe` | Universe decoding with explicit byte and expanded-constructor limits | Exact budget accounting, production-decoder agreement, round trips within limits, and wire validity below the wire count capacity |
| `Ix.Ixon.Bounded.Constant`, `WireCheck`, `Canonical` | Complete-record input/expansion limits, wire validity, and canonical byte spelling | Success iff the record is wire-well-formed, re-encodes to the supplied bytes, and fits both limits |
| `Ix.Ixon.Bounded.Size`, `Verify.ReaderBounds`, `Verify.ConstantBounds` | Structural constructors and table slots in successful production reads | At most two structural units per consumed byte, plus the separate expanded-universe budget; no additional runtime traversal |
| `Ix.Ixon.Admission`, `Verify.Admission.RecordsRead` | Ordered canonical record bytes, unchanged address keys, exact literal blobs, and batch limits | Exact decoding/acceptance domains, installed readings, model existence, and preservation of kernel outcomes |
| `Ix.Ixon.Projection`, `ProjectionProofs` | Projection records derived from physical mutual blocks and addressed with pure BLAKE3 | Complete reconstruction, exact input preservation, primary order, bounded requests, and byte-admission/model contracts |
| `AExpr`, `PropWhen` | A reading with a condition at each binder describing when its codomain is a proposition | `annotate_erase` proves exact erasure; separate scope checks include annotation conditions |
| `Typed`, `TypedSort`, `Reduced`, `Conv` | Search results with erased semantic evidence for this environment and context | `inferA`, normalization, conversion, and the declaration checkers |
| Admission candidate | An ordinary inductive shape, structure description, or standard primitive interface | A reader proposes it; validation and exact generated-block comparison justify installation |
| `Certified.Ordinary.Stage` | The family/constructor stage, optionally extended with a supplied recursor at its actual reference | Each stage constructs its model and constructor reading; Nat and structure facts share this interface |
| `Env`, `ConstantEntry`, `Environment` | Concrete storage and its functional lookup view, including types, bodies, equations, and facts | Admission constructs `AdmissionClaim` and exact `Block.Installed` readings |
| `Model`, `SetTheory`, interpretation | A simultaneous realization of the installed entries in an explicit set theory | Model extension and the closed acceptance theorem |

An annotation is not a typing certificate. Its erasure theorem says exactly
which raw expression was read; `inferA` checks binder conditions. Similarly,
recognizing a familiar inductive name or shape is not admission evidence.

`StepClaim` extends realizability and well-formedness. `AdmissionClaim` also
preserves every old lookup. The separate fidelity theorems
`checkDecl_installed`, `checkDecls_installed`, and `check_installed` establish
the supplied universes, erased types and definition bodies at their exact
references, including nested constructors. They do not reconstruct bytes or
authenticate addresses. Specialized publication lemmas describe the additional
equations and facts. `ConvClaim` is conditional on formed inputs; composing
it requires a formed intermediate term.

## Supported profile

The current checked input is a list of `Decl β`, for any `β` with decidable
equality. `checkAddressed` specializes it to opaque `Address` keys.
`checkEnv` reads ordered production Ixon constant pairs and literal blobs
through the pure `Ix.Ixon.Types` boundary. `Ix.Ixon.Admission.checkBytes`
accepts ordered canonical record bytes with explicit input limits and uses
the same checker; host transport framing and scheduling remain outside it.

| Input | Current behavior |
| --- | --- |
| Single safe definition, theorem, or opaque | Check its declared type and body; theorems must have a propositional type |
| Variables, universes, constants, applications, lambdas, Pi types, lets | Check scope, universe arity, typing, and binder conditions |
| Ordinary inductive family | Check the family and constructors independently; validate positivity, universe constraints, and the complete supplied declarations |
| Supplied ordinary recursor | Associate by the major premise; check its complete type, metadata, rules, elimination, and freshness at its own reference |
| Structure-shaped ordinary block | Publish projection typing, iota, and eta when the field and Prop restrictions hold; otherwise try ordinary admission |
| Natural numbers | Recognize the natural-number interface; literals name their admitted family; literal/constructor conversion and recursor iota are supported |
| Equality | Ordinary admission plus K-like reduction through checked constructor synthesis and proof irrelevance |
| Quotient | Check the four primitive declarations and soundness against the admitted Eq/quotient interfaces; prove lift and eliminator computation |
| `propext`, `Classical.choice` | Check the generated types against admitted Eq/Iff/Nonempty interfaces and construct their realizations |
| Arbitrary axioms, unsafe/partial declarations, general mutual or nested inductives | Decline outside the supported profile |
| String literals, full Lean universe conversion, full Mathlib | Not a current coverage guarantee |

The tracked positive fixtures include False, True, And, Or, Nat, List, Eq,
Prod, dependent subtypes, standard axioms, and quotient computation. Each
feature has malformed or unsupported controls. Passing those fixtures is a
supported-profile check, not a completeness theorem about Lean.

Declarations must arrive in dependency order. References to unavailable
constants and duplicate addresses are rejected. An inductive block's own
members are handled by its admission construction. Ixon ingress preserves
physical member and constructor references. Production stores an inductive
family and its recursor separately; the driver consumes an associated pair
together and checks all intervening records afterward in their relative
order. Every external reference must resolve against the checked prefix.
The existing combined family/recursor fixture layout remains supported.

`Ix.Tc` and Rust discover a recursor's owner through its major premise and
compare the complete generated candidate. The certified ordinary reader
uses the same association, restricted to syntactic telescopes in its current
profile; it never normalizes an open peeled body in an empty context.
Association cannot authorize acceptance. A missing recursor admits only the
family and constructors, with Nat or structure facts when applicable. It
does not generate a replacement recursor. Mutual/nested auxiliary recursors
and adding a separate recursor later through single-declaration admission
remain outside this interface.

`checkEnv_reading` establishes `Ingress.Installed`: unique constant and blob
keys, exact source readings, and each primary record installed at its own
reference. Projection records must name the proper owner, member kind, and
position and have empty tables. Sharing edges must decrease; indexes resolve
without narrowing. `checkEnv_has_model` applies to this executed Ixon entry
point. Nat payloads are little-endian; strings and nonstandard binder modes
decline. Address authentication, wire canonicality, and unused table entries
are outside this reading contract.

`Egress.readRecords` retains the layout choices that expanded raw terms lose.
`Egress.writeRecords` reconstructs declaration payloads from those terms,
checks their complete readings against the retained tables, and validates
each reconstructed projection's actual variant and owner. It preserves every
address, record position, declaration field, sharing node, repeated or unused
table slot, and let nondependency hint. Numeric reconstruction rejects values
outside `UInt64`; constructor and rule lists cannot silently truncate.

`Egress.records_roundtrip` proves exact source recovery after any successful
read at the same fuel and with the same reference/blob context. The writer
uses a blank `Context.source`; it does not copy the original primary record.
Its retained sharing and universe tables still carry source layout. The
reading/writing operations do not establish typing, dependency order, key
uniqueness, byte canonicality, or address authentication; use `checkEnv` for
declaration admission. Unused table entries remain outside validation. The
serializer profile includes all declaration variants with ordinary Lean
expression modes; the admission profile remains the smaller one above.

The certified environment retains the checked body of every definition-like
declaration, including theorem and opaque declarations. Delta reduction can
unfold such a stored body. This is the current kernel transparency policy;
host reducibility hints and a theorem/opaque opacity policy are not inputs
to this API. Consumer parity must record any operational differences this
causes.

The recursor K flag is also an explicit policy difference. Ix.Kernel rejects
`k = true` for a shape without K support, but permits `k = false` for an
eligible shape and can still derive a K-like step from typing and proof
irrelevance. Ix.Tc requires the flag to equal its computed eligibility. The
differential suite uses canonical flags for its shared positive corpus and
retains noncanonical Eq/True flags and a forged Nat flag as separate controls.

## Outcomes and fuel

Acceptance carries the model theorem. `Error.rejected` records an
independently established input defect, such as bad scope, a missing
reference, a duplicate address, wrong universe arity, or a sort used as a
function. `Error.declined` records exhausted fuel, an unsupported form, or
conversion that search did not establish. An unsuccessful conservative
conversion procedure does not prove that two terms are unequal.

`Config.fuel` is a recursive depth bound, not an operation budget. Nested
checks retain exhaustion. Normalization returns any proved reduction along
with its stopping cause; a partial reduction can still support a successful
conversion. Failure of an optional strategy does not block a subsequent
proved success. There is no fallback whose Ix.Tc or Rust result is labeled
certified.

`checkAgainst` reuses evidence that the expected type is formed in the exact
current context. Rule checkers establish the common type once and use it for
both endpoints. `checkType_acceptance` proves that obtaining formation first
preserves successful `checkType` results at the same fuel; the first failure
reported can differ when both independent checks fail.

## Mathematical and execution boundary

`check_has_model` and `checkDecls_has_model` are relative to an explicit
`SetTheory V`. It supplies the set-theoretic operations and a countable tower
of Grothendieck universes. `no_proof_of_False` rules out an accepted
inhabitant of a type interpreted as empty. The separate
[`Models/SetTheory`](../Models/SetTheory) package constructs the model with
Mathlib under its stated `OmegaInaccessibles` hypothesis.

The frozen roots permit exactly Lean's standard logical axioms (`propext`,
`Classical.choice`, `Quot.sound`), without `sorryAx`, `Lean.ofReduceBool`, or
project axioms. Type/body/constructor dependency traversal, frozen theorem
statements, import auditing, and compiled runtime auditing are independent
checks. Axiom sets alone do not establish that theorem premises are useful.

The execution foundation is Lean's kernel, compiler, runtime, and core data
representations. At this K3 checkpoint the public runtime closure contains 920 compiled
functions, 16 inherited externs, one inherited unsafe declaration, and no
`implemented_by` or `csimp` replacement. The allowed inherited operations
are listed and explained in
[`Ix/Kernel/Audit/Roots.lean`](../Ix/Kernel/Audit/Roots.lean). No project FFI,
Rust checker, or BLAKE3 operation is reached by the certified checker. An
address is only a key inside this boundary; it is never hashed there. The
Ixon ingress closure contains 962 compiled functions, 23 inherited externs,
two inherited unsafe array accessors, and no `implemented_by` or `csimp`.
The separate reader/writer closure contains 202 compiled functions, 21
inherited externs, and the same two array accessors, also without project
replacements. Its bounded conversions additionally use `UInt64.ofNat`.

`Ix.Ixon.Codec` now owns the production anonymous encoders and total decoders;
`Ix.Ixon` reexports them for host consumers. `Ix.Ixon.Wire` describes the
lossless wire domain independently of compiler/source semantics. The eight
retained proof modules under `Ix.Ixon.Verify` prove universe, full expression
spine, and all-variant constant inverses, including arbitrary representable
side tables. `deConstant` retains prefix behavior; `deConstantExact` consumes
the whole buffer, with round-trip and nonempty-suffix rejection theorems.

The pure codec/data import closure uses only Lean core. The proof closure
additionally uses Lean/Std tactics, including checked bit-vector proofs;
it imports no host code or Lean4Lean. `Ix.Ixon.Audit` freezes theorem types,
axiom sets, both import boundaries, and the codec's execution closure: 331
compiled functions, 52 inherited externs, two inherited unsafe array
accessors, and no `implemented_by`, `csimp`, or project replacement. The
new extern is Init's `ByteArray.decEq` (`lean_sarray_dec_eq`), used for exact
re-encoding equality. The existing kernel and egress closures remain unchanged.

`Ix.Ixon.Bounded.Universe` adds a separate universe entry point with a byte
limit and a shared budget for expanded constructors. It reserves the tag's
charge before reading children or constructing a compressed successor chain;
binary children spend the same budget sequentially. Success preserves the
production value and cursor and spends exactly the expanded node count.
Conversely, every successful production read whose node count fits also
succeeds with that budget. Full-buffer round trips and suffix rejection are
proved; a node limit below `UInt64.size` establishes the universe wire
invariant. The limits count input bytes and tree constructors, not runtime
heap bytes or elapsed time.

The strict standalone fixtures cover exact/insufficient limits, binary
budget sharing, truncation, suffixes, and a ten-byte encoding that requests
`UInt64.max` successors. The latter is rejected at the end of its tag, before
reading the base or constructing the chain. The host suite also checks
generated values with the existing Rust serialization oracle.

`Bounded.Constant` now spends one universe budget across the whole table.
The shared `getConstantWithUnivs` grammar preserves the production decoder
on every input and state. The bounded record API accepts exactly its
successful full-buffer reads that fit the byte and aggregate universe-node
limits, with all-variant round trips and suffix rejection.

`Verify.ReaderBounds` and `Verify.ConstantBounds` now prove structural bounds
for the original readers, including arbitrary successful byte spellings and
nonzero starting cursors. `Span` records an unchanged buffer, a monotone
in-bounds cursor, and at most two structural units per consumed byte. The
units count expression/declaration constructors and variable table slots;
reference universe-index vectors count too. Compressed application spines
can exceed one constructor per byte, which is why the bound uses two.
Universe trees retain their separate expanded-node budget.

For exact records, `constant.resourceSize ≤ 2 * bytes.size`; bounded records
add the expanded universe count to obtain a limit of
`2 * maxBytes + maxUnivNodes`. No parser implementation changes or extra
validation traversal are needed. A counted-array failure is a successful
prefix followed by the first failing element; when each successful element
consumes a byte, that prefix has at most the available byte count. This
bounds array iterations, not the work inside an element reader. These are
structural and prefix bounds, not heap-byte or wall-clock guarantees.

`Verify.Work` through `WorkRecord` additionally bound complete bounded-record
parser work, including work inside a failed element. Their ghost interpreter
erases exactly to production, preserving successful values, error strings,
buffers, and cursors on every outcome. Byte potential and transferable credits
fund construction and collection work without trusting declared counts. Nested
binds share one terminal-failure allowance. Universe expansion reserves work
before descending, with one budget across the whole table, so a later failure
cannot erase earlier work or restart the allowance.

The bound is `16 * input.size + 2 * universeBudget + 3` per attempted record.
`WorkAdmission` preserves the complete canonical parser-stage result and proves
an aggregate bound of
`16 * maxTotalBytes + maxRecords * (2 * maxRecordUnivNodes + 3)` without assuming
success. Preflight failure performs no parsing, and canonical failure stops
before subsequent records. The production decoder executes no counters.
These abstract units count byte attempts/copies, tag and structural construction,
collection work, telescope folds, reserved expansion, and record framing/checks.
They do not measure heap bytes, wall time, or arithmetic bit complexity;
canonical validation/re-encoding, batch administration, projection hashing,
ordering, literal interpretation, ingress, and checking are outside the metric.

`WireCheck.validConstant` decides the complete `Constant.wireWF` predicate.
Its recursive checks carry telescope counts, avoiding repeated scans of
long application, binder, and successor chains. `Canonical.deConstant`
combines the bounded parser, this validator, and exact re-encoding equality.
Its successful-domain theorem is an iff: the result must be wire-well-formed,
serialize to precisely the input bytes, and fit both limits. Tests exercise
alternate spellings accepted by the production decoder, large truncated
counts, aggregate budget exhaustion, 4,096-entry tables and application
spines, and generated values compared against Rust serialization.

`Ix.Ixon.Admission.checkBytes` connects canonical records to `checkEnv`.
Before decoding, a short-circuiting preflight checks separate record/blob
counts and one total payload-byte budget shared by both lists. Address keys
and outer transport framing are excluded from that byte count. Explicit
per-record limits cap bytes and the entire universe table; together with
the record-count limit they bound aggregate universe expansion. The
tail-recursive decoder preserves every key, record position, and side table.
Decode failures identify the original zero-based position and address;
kernel failures retain their exact rejection/decline reason.

`Verify.Admission.RecordsRead` describes each canonical payload without
referring to a decoder. `decodeRecords_ok_iff` proves its exact successful
domain; `checkBytes_ok_iff` composes it with the actual checker at the same
configuration and literal family. `checkBytes_of_reading` preserves all
kernel outcomes on bounded canonical input. `checkBytes_reading` ties that
same ordered reading to the installed declarations, and
`checkBytes_has_model` establishes the accepted environment's model.
Uniqueness of both key lists is proved from successful byte admission.
`checkBytes_resources` ties the same installed reading to a decoded-record
bound of `2 * maxTotalBytes + maxRecords * maxRecordUnivNodes`. The measure
includes unused side tables and expanded universe nodes; it does not measure
blob interpretation, host keys, or later ingress/checker expansion.
Literal blobs retain their exact supplied bytes and the existing natural
number interpretation; this does not require a canonical spelling of blobs.

The adapter lives outside `Ix.Kernel` and imports no verification modules.
Its independent `Admission.Audit` checks data/proof import closures, exact
axiom sets and theorem statements, and 1,250 compiled functions reaching
56 inherited externs, two inherited unsafe array accessors, and no project
replacement. A set-difference check confirms that these primitives all
already occur in the kernel/codec closures. Their narrower allowlists and
existing public contracts remain unchanged.

`Ix.Ixon.Projection.checkBytes` now accepts the same canonical record format
with projection records optionally omitted. It derives definition,
inductive, recursor, and constructor projections from physical mutual-block
positions, writes them with the certified projection writer, and hashes their
complete production encodings with `Address.blake3Pure`. Standalone
definitions and recursors retain their primary address. Owner keys in
projection payloads must be 32 bytes, and positions must fit UInt64.

Reconstruction reuses an identical existing projection or prepends a new one
at a fresh key; a conflicting payload fails. The proofs characterize the
exact successful extension, establish every requested projection's presence
and every added record's structural origin, preserve all supplied records,
lookups, and primary declaration order, and bound output count by input count
plus `maxProjections`. This separate limit counts requests, including reused
records, and is spent before writing/hashing. Request enumeration itself
visits the supplied block arrays; the byte entry point bounds those inputs.
The byte-reading and installed-declaration relation use the same expanded
store as the executed checker. All kernel outcomes are preserved for that
store, and accepted environments have models.

The new hash adapter has its own audit and is built in the root package,
where the pinned Blake3 package is available. The standalone kernel/codec
package remains dependency-free. Data imports allow exactly `Blake3` and
`Blake3.Pure`, plus their permitted Lean-core/Std dependencies; C/Rust hash
backends and proof-module imports are excluded. Its measured runtime closure
has 1,381 functions, 70 inherited externs, two inherited unsafe accessors, and
no project replacement. The additional primitives are 14 standard array and
integer operations used by pure BLAKE3. Reconstruction assumes no hash
injectivity: conflicting payloads are rejected. Primary keys, supplied alias
keys, and blob keys remain unauthenticated until K5.

`Ix.Ixon.BlockOrder.checkBytes` adds canonical mutual-block order to that
path. It computes member/constructor projection keys, retains physical
external alias addresses, compares literal values, and rebuilds universes
through the shared ingress rules. Stable merge sort and consecutive grouping
refine one address-seeded class; acceptance requires the original ordered
singletons after an observed unchanged pass. Explicit comparison-descent and
refinement-pass limits report exhaustion without accepting unfinished work.
This does not typecheck unused expression branches: complete semantic
admission still comes from the final kernel invocation.

The successful refinement loop is equivalent to a finite counted derivation;
its output is a fixed point and remains the same at larger refinement fuel.
Block and byte acceptance have exact iff contracts, and the composed path
retains exact readings, installed declarations, model existence, and every
final kernel outcome/reason on ordered inputs. The implementation follows
Rust's lexicographic vector comparison (the old Ix.Tc mirror was length-first)
and uses full refinement without the native strong-order/hash-equality fast
path. No compiler ordering metadata is trusted. Differential agreement is
not a formal equivalence theorem about the Rust implementation.

Its separate audit admits the pure shared universe reducer and block-order
adapter without widening any prior boundary. The measured runtime closure
has 1,509 functions, 77 inherited externs, two inherited unsafe accessors, and
no project replacement. Seven added externs are standard string/UTF-8,
UInt64, and array operations; no unsafe accessor was added.

K4's byte contracts, reconstruction, ordering, and abstract parser-work
accounting are implemented and validated. The canonical
record API establishes byte spelling; semantic admission still has K3's
supported profile. Existing production callers use the original decoders
pending D02. Supplied primary, alias, and blob keys are not authenticated
hashes, and the theorem does
not certify the compiler or host container loader. K5 will connect
authenticated subjects and receipts.

## Validation

```sh
lake -d IxKernel build --wfail
lake -d IxKernel exe kernel-provenance
lake run check-kernel --with-model
```

The standalone package reads the repository's kernel sources and has no
external packages. Its default strict build checks all kernel modules,
frozen audits (including negative controls), the isolated codec proof chain,
and twelve fixture modules, including byte-admission adversarial controls.
Provenance validates the port inventory, inspected target hashes, source
pins, headers, and license files. `--source PATH` additionally checks the
old source checkout against the recorded source hashes.

The host-only `kernel-differential` executable compares 38 cases against
Ix.Tc: shared positive inputs for every K2 route, corrupted variants, and
explicit differences for search outcomes, ordering, duplicate storage,
unsupported declarations, K metadata, and opaque transparency. It checks
raw declarations through a test adapter, not production Ixon ingress. The
adapter assigns synthetic reference identities, uses Ix.Tc's homogeneous
storage groups, preserves the source K flag, and configures the fixture
primitive references. Neither its translation nor the oracle is a premise
of a certified theorem.

The host-only `kernel-ingress` executable compiles tutorial declarations with
`Ix.CompileM`, serializes and reloads them through the production codec, and
runs both `checkEnv` and `Ix.Ixon.Admission.checkBytes`. Its 26 cases cover eight ordinary families, definition and
reduction examples, family-only dependencies, and mutations of recursor
rules, field counts, metadata, and K flags. The compiler, loader, and host
ordering remain untrusted producers. Each case checks that canonical record
decoding preserves the complete ordered input and that byte admission has
the same outcome and reason as in-memory admission. It also passes through the
certified reader and writer, comparing complete records and exact production
Ixon bytes; this includes cases whose declarations are declined or rejected.
Pure egress fixtures cover layout duplication, unused entries, sharing,
projection variants, numeric overflow, count mismatches, and changed raw
payloads behind retained table slots. Exact Ixon bytes and outcomes are
retained in `.lake/build/kernel-ingress.jsonl`, together with byte limits,
checker fuel, the literal-family reference, byte outcomes/reasons, and the
exact-decoding result. Pure byte-admission
fixtures cover preflight rejection before decoding, zero-byte entries,
shared total budgets across records and blobs, exact/insufficient limits,
duplicate keys, order-sensitive references, fuel exhaustion, noncanonical
encodings, successor expansion bombs, every proper record prefix, and every
single-byte suffix.

The host-only `kernel-codec` runner executes the existing production codec
unit/property suite, including Rust serialization comparisons for universes,
expressions, constants, and environments. It links the `test-ffi` Rust
archive; no such dependency enters the standalone package. Results are
retained in `.lake/build/kernel-codec.log`. Pure codec fixtures additionally
cover all constant variants, binder modes, integer/tag boundaries, every
proper prefix of a representative record, and exact suffix rejection.

`lake run check-kernel` writes exact raw input trees, outcomes and reasons
to `.lake/build/kernel-differential.jsonl`. The CI job **Certified Lean
kernel** runs the host/standalone/provenance/model gate and uploads that
file and the ingress JSONL. The 2026-09-29 K2 release run passed in a fresh jj workspace with no
project Lean artifacts: 134 standalone jobs, 144 host fixture/provenance
jobs, 342 differential build jobs, 38 comparison cases, and 975 model jobs
including its full axiom audit. That run reused pinned third-party package
caches and unchanged Rust artifacts. No dependency revision changed.
The later K3 incremental full gate passed 144 standalone jobs, 154 host
fixture/provenance jobs, 457 runner build jobs, all 38 differential and 26
ingress cases, and the 975-job model gate. Provenance covers 97 ported,
35 authored modules, and four license files. This run was not a clean build.
Native performance commands and retained
operation counts are documented in
[`Benchmarks/Kernel/README.md`](../Benchmarks/Kernel/README.md). Diagnostic
tracing runs in disposable source copies and is excluded from the certified
runtime. Timings use uninstrumented native executables.

The K4 byte-admission checkpoint passed the incremental full gate on
2026-09-29: 176 standalone jobs, 184 host fixture/provenance jobs, 541 runner
build jobs, and 975 model jobs. All 38 differential cases and all 26 compiler
ingress/byte-admission/exact-egress cases passed, as did the codec suite.
The byte route preserved 20 accepted, five declined, and one rejected outcome,
including their exact reasons. Twelve new exact axiom checks cover batch
accounting, exact byte readings, aggregate expansion, admission fidelity,
key uniqueness, model existence, and the executable entry point. Provenance
covers 97 ported and 64 authored/reorganized modules plus four license files.
The retained inputs include every byte-admission argument. Evidence is in
`plans/review/k4-byte-admission/summary.json`; its tested source is
`d8f5ca265ed496b060c197dfaedf87a77cd4ce47`. This was an incremental run, not
whole-corpus parity or the D02 runtime cutover.

The subsequent K4 reader-resource checkpoint passed the incremental full
gate on 2026-09-29: 179 standalone, 187 host fixture/provenance, 543 runner,
and 975 model jobs; all 38 differential and 26 compiler cases retain their
outcomes. The codec suite adds generated expression-resource checks with
nonzero cursors and Rust serialization comparisons, and checks the combined
record/universe bound. Thirteen new exact axiom checks cover successful
reader bounds, counted-array failure prefixes, and the accepted batch's
resource theorem. All parser implementations, import allowlists, and audited
runtime closures are unchanged. Provenance covers 97 ported and 67
authored/reorganized modules plus four license files. Evidence is in
`plans/review/k4-reader-bounds/summary.json`; tested source:
`e34c8cc3aad3f7d13fbc65a3c4f20351be3352e5`. At that checkpoint, complete
parser-work accounting and whole-corpus parity remained open.

The K4 projection-reconstruction checkpoint passed the incremental full gate
on 2026-09-29: 179 standalone, 197 host fixture/provenance, 550 runner, and
975 model jobs, with all 38 differential and 26 compiler cases passing.
Fifteen compiler cases omitted a total of 44 projection records. Pure
reconstruction recovered every original key/value store and primary order;
all 26 cases preserved their verdict and exact reason. The retained inputs
include the projection-free record sequence and request limit. Directed
fixtures compare all four variants and UInt64 tag boundaries with Rust hashes
and cover reuse, conflicts, index/owner-width errors, limits, and constructor
metadata validation. Sixteen new exact axiom checks cover the new contracts;
provenance covers 97 ported, 70 authored/reorganized modules, and four license
files. Tested source: `19313f7ea597202ed3d544980d898ea6f5d8ba7c`; evidence:
`plans/review/k4-projection-reconstruction/summary.json`. This completes pure
projection reconstruction. Canonical ordering and complete parser-work
accounting remained open at that checkpoint and were completed in the two
checkpoints below. The D02 consumer cutover remains open.

The canonical-block-order checkpoint passed the incremental full gate on
2026-09-29: 179 standalone, 202 host fixture/provenance, 607 runner, and 975
model jobs. All 38 host differential cases, 26 compiler cases, the codec
suite, and 1,117 Rust canonical-order comparisons pass. The compiler cases
run the new order-aware byte entry point with identical prior verdicts and
reasons. Forty-four directed controls cover permutations, weak refinement,
alpha-equivalent self/cyclic references, constructor offsets, unequal-length
universe vectors, normalized levels, sharing, literal values, limits, and
byte-admission outcomes. The independent test-only Rust oracle computes its
own projection keys and uses native ingress/comparison/refinement. Thirteen
exact axiom checks and six frozen signatures cover the new contracts;
provenance covers 97 ported, 74 authored/reorganized modules, and four license
files. Tested source: `d0377deba61b6b57fe24b6a72bacaeb0b1098990`; evidence:
`plans/review/k4-block-order/summary.json`. At that checkpoint K4 still needed
complete parser-work accounting, including nested failure paths and
element-reader cost.

The parser-work checkpoint passed the incremental full gate on 2026-09-29:
188 standalone, 211 host fixture/provenance, 621 runner, and 975 model jobs.
All 38 differential cases, 26 compiler cases, 1,117 Rust order comparisons,
and the codec suite pass. Thirty-seven parser guard groups pin operation
counts and cover malformed/truncated readers, huge declared counts, failed
array elements, shared universe budgets, and admission short-circuiting.
Eighteen exact axiom checks and eight frozen contracts cover complete outcome
erasure and record/batch work bounds. The prior import/runtime boundaries are
unchanged; nine production files are byte-identical to the preceding checkpoint.
Provenance covers 97 ported, 82 authored/reorganized modules, and four license
files. Tested source: `5079c6edf77b88e2c267186a169998c36646b7e5`; evidence:
`plans/review/k4-parser-work/summary.json`. K4 is complete under the stated
parser metric and supported admission profile. K5, P04–P12, D02 consumer
migration and Ix.Tc deletion, whole-corpus Rust parity, and K7 remain open.

## Removal ledger: lean4ix and Ix.Tc

D01 removed both dependency paths on 2026-09-29: the root Lake package
`lean4lean` fetched `argumentcomputer/lean4ix` at
`a4188d7c2979378d85c6bb41fdd96c3a48a71371`, and TruthMines independently
fetched `digama0/lean4lean` at `e0e3f6bcccb840cb0ea6f11c2b274ada93a12e00`.
The old verification trees and their consumers are gone. Runtime `Ix.Tc`
remains until D02's consumer and corpus-parity gates are satisfied.

| Retired or remaining surface | Replacement or disposition | Status |
| --- | --- | --- |
| `Ix/Tc/Verify/**` checker statements and proof frontier | Executed `Ix.Kernel` acceptance/model/fidelity roots and adversarial fixtures; behavior outside the supported profile remains in runtime tests | D01 complete |
| `Ix/Tc/Verify/Audit/{Basic,Completed,Conditional,Statements,SorryFrontier}.lean` | Kernel axiom/import/runtime audits supply strict checks and negative controls; obsolete upstream/native/sorry allowances were deleted | D01 complete |
| `Ix/Compile/Verify/{Codec,ExprCodec,ExprSpineCodec,ConstantCodec,ConstantTablesCodec,NonrecursiveConstantCodec,RecursorConstantCodec,MutualConstantCodec}.lean` | Preserved under `Ix/Ixon/Verify`, with complete wire domains, frozen contracts, and independent audits | D01 complete; old copies deleted |
| `Ix/Compile/Verify/{Catalog,IxonValue,SourceValue,Reference}.lean` | Structural predicates live in `Ix/Ixon/Wire`; K3 exact readings cover resolved values; the old semantic square is retired | D01 complete |
| Remaining `Ix/Compile/Verify/**`, including `Compile*`, `Arena`, `Sharing`, `Statements`, and its audits | Retired compiler/specification machinery; no Ix.Kernel compiler-correctness theorem is claimed | D01 complete |
| Root `lakefile.lean` / `lake-manifest.json` | Removed dependency, proof libraries, replay benchmark, proof loader, and `build-all` exception; Lake regenerated the manifest | D01 complete; all 24 remaining targets build strictly |
| `ix_ffi_dyn`, `crates/ffi-dyn`, workspace `Cargo.toml` / `Cargo.lock` | Removed the proof-only crate and loader; ordinary runtime FFI remains | D01 complete; Cargo regenerated the lockfile |
| `Benchmarks/Lean4Lean.lean`, `Benchmarks/Lean4LeanMain.lean`, `Tests/Ix/Lean4Lean.lean`, `Tests/Main.lean` | Removed replay library, executable, smoke runner and registration; fixture dispositions below | D01 complete |
| `Ix/Cli/BenchCmd.lean`, `Ix/BenchConstants.lean`, `docs/benchmarking.md` | Removed backend registry, dispatch, help, and active commands; measurements use the existing certified harness and Rust driver | D01 complete; removed backend exits 2 as unknown |
| `Benchmarks/TruthMinesSpec/{Catalog,Spec}.lean` | Removed package/member at the generator source | D01 complete; generator checks pass |
| `Benchmarks/TruthMines/{lakefile.lean,lake-manifest.json,Drivers/Lean4Lean.lean}` | Regenerated configuration without the independent upstream dependency; deleted the generated driver | D01 complete; 78 retained package entries |
| `Benchmarks/Compile/{lake-manifest.json,TruthMines/lake-manifest.json,TruthMines/Members/Lean4Lean.lean}` | Removed inherited package entries and generated member; retained unrelated pins | D01 complete; 24 and 80 retained package entries |
| `.github/workflows/merge-tests.yml`, `.github/workflows/ci.yml` | Removed old proof jobs and runner; the certified kernel/model/provenance/differential job covers PRs and merge groups; temporary runtime parity jobs remain | D01 complete |
| `flake.nix` | Removed dependency override; added the retirement source check and Python to development shells | D01 complete; native x86_64-linux Nix gate passes |
| `docs/ffi.md`, `docs/tc-k0-backedge-audit.md`, this ledger | Obsolete active commands retired; historical audit labeled explicitly; replacement guarantees stated below | D01 complete |
| `Ix/Tc.lean`, remaining `Ix/Tc/**`, `Tests/Ix/Tc/**`, CLI, AuxGen, IxVM claim harness, and validation round trips | Move consumers and behavior tests to their new owners; switch differential testing to Rust; delete Ix.Tc last | D02 pending after K3/K4 and K6 consumer parity |
| Kernel/model LICENSE and NOTICE; explanatory attribution in Rust, IxVM, tests and historical documentation | Retained; historical mentions are outside the active-reference guard | Preserved |

The final consumer scan confirmed that the proof loader was the only Lake
consumer of `ix_ffi_dyn`. The ordinary Rust `unsigned` implementation and
its runtime symbols remain in `ix-ffi`.

The retired dependency smoke test replayed `Nat.add_comm` and submitted an
axiom whose type was the natural-number literal zero. `Nat.add_comm` remains
the normal CI compiler/zkVM fixture; the certified suite separately covers
natural-number recursion/literals, non-type declared types, and unsupported
axioms. The arbitrary-axiom route declines under the current certified
profile, so this retirement does not claim the old smoke test's exact
acceptance/rejection behavior or full `Nat.add_comm` certified parity.

### Preserved and retired compiler contracts

| Old contract | Selected replacement | Explicit limits |
| --- | --- | --- |
| `deUniv_serUniv` | `Ix.Ixon.Verify.deUniv_serUniv` (implemented) | Compressed-successor and UInt64 wire bounds retained |
| `deExpr_serExpr` | `Ix.Ixon.Verify.deExpr_serExpr` (implemented) | Wire-sized vectors, spine counts, binder bits, and whole-buffer consumption retained |
| `deConstant_serConstant` | `Ix.Ixon.Verify.deConstant_serConstant`, plus `deConstantExact_serConstant` (implemented) | All variants and arbitrary side tables retained with count/address/table bounds |
| `Reads` / `Writes` | `Ix.Ixon.Verify.Codec` cursor and append laws (implemented) | Codec behavior only; exact consumption and suffix rejection added in `Verify.Framing` |
| `ExprTableWF`, decreasing sharing bounds, reference/universe table resolution | K3 checked resolution plus exact erasure to the supplied Ixon declaration | Detect bad indexes, missing payloads, sharing cycles/forward entries, and unsupported modes before certification |
| Binder-mode erasure relation | K3 explicit accepted mode policy and exact reading; K7 for nonstandard semantic modes | No Lean4Lean interpretation is retained as a hidden premise |
| Production compiler refinement/value-preservation and end-to-end semantic square | Retired as part of D01; a separate compiler-correctness project would need new source semantics and proofs | Ix.Kernel acceptance does not prove that the compiler preserved the original Lean declaration |

The retained codec chain imports the pure structural `wireWF` predicates,
so the former `ExprSpineCodec → Catalog → IxonValue → Lean4Lean` dependency
is gone. The temporary old copies have been deleted. Retained codec roots
use only the three standard axioms; native hash/name allowances from the
old compiler proofs are not inherited. K4's resource bounds, validity,
canonicality, and byte-admission composition remain open.

### D01 validation and recurrence guard

`python3 scripts/check-kernel-retirement.py` runs before `check-kernel`
and as a Nix check. It checks tracked Lean code (including `public import`,
`import all`, and multiline imports), every tracked Lake manifest, and
active build/CI/Nix/Cargo/generator configuration. Nested Lean comments,
historical documentation, and legal attribution are preserved. Negative
controls cover import forms, aliased repository URLs, stale target/crate
names, retired paths, and malformed manifests. A source-export walk covers
Nix builds without VCS metadata.

Validation used a fresh jj workspace with no project Lean artifacts and no
Lean4Lean package. Only retained pinned third-party package caches and the
Rust artifact cache were reused. All 24 host library/executable targets
passed `lake lint -- --wfail`; default tests (including TruthMines records,
benchmark measures, runtime Tc, and FFI), CLI tests, generator checks, and
the explicit removed-backend/help checks passed. The regenerated TruthMines
Lake configuration compiled. Lake's manifest reader/writer removed the
three nested entries while retaining every other entry and revision; no
unrelated package pin changed. This validates corpus configuration, not a
build or parity sweep of all retained corpus packages.

`lake run check-kernel --with-model` passed: 164 standalone, 173 host
fixture/provenance, 529 runner, and 975 model jobs; 38 differential cases,
26 compiler ingress/exact-egress cases, and the production codec property
tests with Rust comparisons. Provenance remains 97 ported, 53 authored or
reorganized modules, and four license files. Public statements and audit
allowlists are unchanged.

The x86_64-linux Nix gate used immutable source snapshot
`a829f6d86f49dec0acb9447da014bf76b32ab9ec`, with no workspace caches in the
source. The library, packaged Lean tests, retirement guard, clippy, nextest,
and distributable CLI smoke check passed. Nextest ran 1,533 tests with
1,533 passes and 14 skips. Other operating systems were not tested.
The final checkpoint differs from that tested snapshot only in this ledger
and the roadmap's completion notes.
The remaining Rust workspace also passed the local locked release
all-target build and clippy checks with `parallel,net,test-ffi` enabled,
and the default-feature workspace tests and doc tests.

D02 still requires no active `Ix.Tc` dependency and the documented consumer
parity corpus, including the ordered-reference policy. Dependency
retirement does not complete the runtime cutover.
