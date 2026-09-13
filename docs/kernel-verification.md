# Kernel verification

`Ix.Kernel` is the production Lean checker. `Ix.Kernel.Verify` contains its
implementation proofs; `Ix.Compile.Verify` contains the Lean-to-Ixon compiler
proofs. Their named specification and reference implementation lemmas are local
under `Ix.Theory.Named`. Building or checking them requires no external
formalization repository.

The named development retains the 104 source modules needed by the existing
proof dependency graph, including the inductive fixtures consumed by Ix.
Standalone applications, benchmarks, and unrelated tests are excluded. Its
original source hashes and attribution are recorded in `Ix/Theory/Named/NOTICE`
and `Tests/Theory/NamedManifest.lean`; the Apache license is preserved alongside
the sources. The added axiom-audit helper is authored in Ix.

## Connection to the consistency model

The name-indexed specification and the set model use the same
`Ix.Theory.VLevel`. The set model and its foundational audit remain independent
of the named development. Mathlib is confined to the separate
[set-theory model package](../Models/SetTheory/README.md).

`Ix.Kernel.Verify.Consistency` proves the following direct connections:

- Production universe equality and ordering agree with model evaluation,
  under the existing finite address-faithfulness and arithmetic bounds.
- A structural reader maps kernel expressions to model syntax, resolves
  addresses to explicit store references, preserves projections and natural
  literals, and substitutes let values. Free variables, unresolved addresses,
  and string literals are outside the current reader's domain.
- Hash equality and intern-table reuse preserve that reading under their
  stated address/key collision assumptions. Metadata cannot change it.
- `inferUncached_sort_sound` interprets an actual successful execution of the
  production sort-inference branch. It proves the model typing postcondition
  for the returned type, including intern-table reuse.
- `ModelTyping.no_false` rules out a closed model-typed kernel expression at
  primitive False when its environment has been admitted by the certified
  interface and the set-theory assumption has an instance.

The last theorem assumes semantic typing; it does not assume or prove that
arbitrary checker success supplies it. A complete checker consistency theorem
still requires the remaining inference/conversion cases, cache invariants,
address-to-store resolution, and declaration admission to establish that
postcondition for `checkEnvAnon`. The existing named-calculus proofs are retained
to support this refinement, rather than being treated as a set-model proof.

## Trust checks

The audits traverse checked declaration types and bodies, including inductive
constructors. They compare exact axiom sets and record direct origins of
`sorryAx`; they do not rely on cached imported axiom summaries. During the
migration, full traversal of the original sources exposed two wrapper reports
that listed 3 axioms but depended on 30. Their boundaries now include the
existing implementation assumptions and unfinished metatheory. All 441 retained
named-specification assertions use the original full dependency graphs as their
migration baseline.

The same traversal covers 2,034 kernel manifest roots. Thirteen entries omitted
logical or native dependencies through constructor fields; their corrected
boundaries were checked against freshly compiled pre-migration sources. Direct
dependency lookups are cached within a fixed environment, while each root's
reachable declarations, axioms, and proof-hole origins are computed separately.

`Ix.Kernel.Frontier.Pending` quarantines the remaining explicit metatheory
axioms. Completed roots cannot depend on that namespace. Named-specification
proof holes and implementation bridge axioms are tracked separately from
Lean's logical axioms and generated native proofs. No direct consistency root
permits a proof hole or a metatheory/implementation bridge axiom. Both the
context hash and content-address hash now use kernel-checked proofs of their
32-byte output bounds on both platform sizes. Their former generated native
assumptions have been removed from the affected exact audits.

Run:

```sh
lake build IxKernelVerify IxCompileVerify
lake build --wfail IxKernelConsistency
lake run check-theory
lake test --wfail -- tc-unit
```

The consistency target checks 18 exact theorem boundaries. Its remaining
native assumptions are explicitly named proofs reached through production
smart-constructor code; the model's no-False theorem itself uses only
`propext`, `Classical.choice`, and `Quot.sound`, with set theory as a hypothesis.

## Certified host adapters

The cumulative C2–C7 source and claim adapters are maintained under
`Ix.Certified`, with explicit certified entry points in `Ix.Kernel`.
`ClaimCommand.run_meaning` connects successful source validation to the exact
versioned envelope and its semantic meaning. A closed logical receipt
constructs its model and excludes a checked subject of the profile's false
type under the set-theory hypothesis.

Run `lake run check-certified` for the exact 86-root foundation audit and
native/CLI regressions against the locally preserved C7 evidence. The audit
permits only the three standard Lean axioms in these roots and inventories
the separate BLAKE3 and native execution boundaries. See
[the command interface, theorem contracts and evidence](certified-checking.md).

These host results do not cover the full production inference dispatcher or
prove that an Aiur public verifier executes the C5–C7 validator. The imported
C2 VM pilot still uses host-decoded inputs and declines modeled witnesses.

## Aiur lookup activity

Aiur's function and memory circuits require inactive rows to have zero lookup
multiplicity. The function constraint uses the sum of the circuit's member
selectors, so it covers both singleton and grouped circuits:

```text
return_multiplicity * (1 - circuit_activity) = 0
memory_multiplicity * (1 - is_real) = 0
```

Lookup multiplicities remain linear. Active rows retain their previous
behavior. Without the function constraint, a supplied inactive row could
disable multiplication constraints while providing an incorrect public result.
The regression in `crates/aiur/src/synthesis/tests/acceptance.rs` constructs
trace rows independently of the honest evaluator, produces a proof of
`3 * 5 = 16`, and requires `AiurSystem::verify` to reject it. Additional tests
cover each grouped member, inactive rows, zero padding and memory widths
1, 4 and 8, including positive and negative field multiplicities. Honest
grouped and memory executions must still verify.

The new constraint roots change serialized verification keys. Deployments
must regenerate their keys and update permitted key identities, including
recursive aggregation. An old serialized key still describes the old
constraints; rebuilding application code does not repair that key.

Run `cargo test --locked --release -p aiur -- --test-threads=1` to exercise
the repair. This closes the activity/multiplicity counterexample; full
compiler/AIR reflection and public acceptance-to-model soundness remain open.

## Aiur call order

Function lookups also bind a 48-bit rank. Each active row supplies six
little-endian bytes, checked against the preprocessed Bytes2 table. A
constrained call supplies the callee's rank and six range-checked gap bytes:

```text
callee_rank - caller_rank - 1 - gap = 0
```

The caller and callee ranks and the gap are below 2^48. These bounds prevent
field wraparound and force strict increase along constrained calls. The
return lookup includes the row's packed rank, so the callee must use the
rank requested by its caller. The public entry rank is zero; the lookup
fingerprint's existing trailing-zero padding preserves the public message
encoding.

This closes a separate circular-justification case: an active row for
`f(x) = f(x)` could previously supply both its own call and a public result,
despite having no finite execution. Supplied-witness tests require self-calls
and mutual cycles to reject, including grouped circuits and out-of-range
rank or gap bytes. Honest finite recursion, shared callees and promotion of
unconstrained calls still verify.

The honest executor assigns ranks from reverse function completion order,
with the final entrypoint at rank zero. It records one extra eight-byte
timestamp per function query and permits at most 2^48 completion events.
Function rows require six extra auxiliary columns and three byte-range
lookups; each constrained call requires seven extra columns and three extra
byte-range lookups. Grouped members share the row-rank columns. Verification
keys must be regenerated for these constraints.

`Ix.Aiur.Proofs.CallOrder` proves the byte-packing bound, strict field order
and well-foundedness of any call relation satisfying the bounded constraint.
These are arithmetic and relation theorems.

`Ix.Aiur.Proofs.Lookup` recovers the byte bounds from exact lookup balance
against the fixed 256-by-256 byte table, with arbitrary field multiplicities
in the table. It proves that every unit-weight query has a nonzero provider
when the total number of queries is below the field characteristic, then
uses the three byte-pair queries for each rank to establish strict call
order. The count bound is necessary: a separate theorem shows that exactly
one characteristic's worth of identical queries has zero field weight even
without any providers.

Exact message balance, query-count bounds and identification of these
mathematical queries with the native emitter remain explicit premises.
Extracting them from public verifier acceptance remains part of full C8.

## Aiur compiler and verifier components

`Ix.Aiur.BoundVerifier` binds verification to a caller-selected source program,
explicit circuit grouping, entrypoint and function index, input arity, expected
output, commitment/FRI parameters, and complete verification key bytes. It
compiles that selection and checks the actual system's key. Submitted proof
bytes pass through checked parsing before the stored system verifies the
caller's statement. Environment grouping overrides cannot change this path.
Construction also checks constrained-call and continuation-yield arities and
checks every entrypoint return against the selected success output size.

Zero-padded function messages need these arity checks because inputs, outputs
and the final call-order rank have no length separators. A supplied native
trace for an empty return at rank seven previously verified against a public
claim containing one output, seven. The message for that empty return was
identical to the claimed output followed by the omitted zero root rank.
The native verifier now validates the claim's channel, function visibility
and input/output widths before checking the proof. Native construction and
the selected-key builder also reject incompatible constrained-call arities.
The regression now rejects the supplied claim. This validation repair adds
no AIR columns or constraints.

The proofs under `Ix.Aiur.Proofs` establish these component contracts:

- The field activity constraint forces inactive-row multiplicity to zero.
  This arithmetic theorem does not establish all Rust AIR constraints.
- The Goldilocks modulus is prime, proved from 32 kernel-checked modular
  squarings and a divisor argument. No native-evaluation axiom or external
  primality oracle is used. Products have no zero divisors, so selector and
  `eq_zero` polynomial equations imply their semantic values. Active case and
  default equations imply equality and disequality of the matched key.
- A boolean selector sum activates at most one branch when its number of
  summands is below the characteristic. An active sum contains exactly one
  active occurrence, and an inactive sum contains none. A full-characteristic
  cancellation counterexample shows why the size bound is needed.
- The range-bounded call-order constraint forces strict rank increase and
  a well-founded call relation.
- Exact lookup balance with bounded query counts supplies matching providers
  and recovers the rank-byte bounds from the fixed byte table.
- Zero padding preserves exact message balance when the channel and function
  arities determine each active message's length. Zero-weight providers need
  no shape condition. Channel filtering preserves balance, and function and
  memory encodings recover the typed requests. A checked counterexample
  demonstrates the output/rank ambiguity when arities differ.
- The total return-size validator implies the output arity of every local
  execution, including early returns from match arms. The call-shape
  validator implies that every emitted constrained call uses its callee's
  input and return widths. The selected backend retains both validation
  proofs and produces public claims of the checked shape.
- Exact byte-chip lookup balance supplies both input ranges and operation
  outputs for all 13 byte channels. Addition and subtraction also recover the
  virtual carry/borrow outputs omitted from their lookup messages. The step
  theorems produce the corresponding relational bytecode operations.
- The four-byte comparison gadget's range and boolean-carry equations imply
  its strict unsigned comparison result. Its proof derives an integer carry
  identity and both input bounds, including equality and wraparound cases.
- Locally interpreted function rows, exact function/byte lookup balance and
  bounded query counts imply finite relational executions for every public
  request. Matching callees are derived from nonzero providers, and the rank
  equations justify induction; callee termination is not assumed. The local
  row interpretation and shared memory facts still need extraction from the
  native AIR.
- One mixed, padded lookup pool now supplies function providers, immutable
  memory facts and all 13 byte operations. Its channels separate the four
  provider families; structural return checks prevent padding aliases without
  requiring a uniform arity table for functions that never return. Checked
  call shapes propagate along reachable calls. Rank and gap bounds from the
  same pool then give finite executions for the selected backend's success
  request. Circuit witnesses now supply the locally valid function rows.
  Native row reflection, padded balance, and the global consumer count and
  message-width bounds remain explicit obligations.
- The native verifier checks a conservative global consumer budget: one
  public claim plus every lookup slot in every active trace row. It checks
  active-position degree indexing, sequence lengths and arithmetic overflow,
  and requires the sum below the characteristic. The total Lean model proves
  this count bound and its converse. It also proves that version-five keys'
  16-bit circuit/slot limits fit the budget at the maximum Goldilocks trace
  height of `2^32`; the guard preserves proofs within those existing limits.
  Canonical circuit traces now derive the number of emitted unit consumers
  within those slots. Each active trace has exactly `2^degree` row assignments,
  and its bitmap and degrees follow canonical and active order respectively.
  The checked global budget supplies the count bound used by backend
  execution. Native accepted-proof metadata and trace extraction remain open.
- Shared lookup arguments recover the uniquely selected padded message even
  when inactive branches contribute different message lengths. Continuation
  merge equations similarly recover the selected yield's values. The
  branchless optimization now requires one function with terminal control
  and one selector. Its single-writer property is proved from that check.
- Selector equations computed over the actual bytecode tree conserve returns
  and escaping yields through nested continuations. Each continuation consumes
  its nearest yields; early returns bypass it. With the existing shape check,
  the function has no escaping yields, and a nonzero provider multiplicity
  selects one return under the terminal-count bound. The emitter gates a
  continuation with its yield sum; a separate proof uses the link equation
  to identify these actual return gates with the leaf selectors. Native
  expression, argument-value and layout reflection remain obligations.
- Active case/default equations select a matching arm of the actual bytecode,
  retaining its selector constraints for recursive extraction. The number of
  arms must be below the field characteristic.
- Valued emission of all 34 operation forms tracks logical values, expression
  degrees, constant folding, auxiliary columns, polynomial values and raw
  lookup contributions. Active satisfying emissions give relational operation
  steps and sequences using the global pool's byte and memory facts. Every
  recorded constrained call retains its function query, gap range queries and
  rank-order equation. Native expression reflection and index/layout validity
  remain explicit obligations.
- Whole-block valued emission composes those operation steps with case/default
  selection, early returns and nonempty continuation merges. Its selector
  equations follow from the emitted polynomials. The resulting execution
  preserves the original function inputs and tracks every selected call's
  query and rank constraints. Function extraction derives local row validity
  and identifies the combined return message with the same semantic call.
  Count bounds and valid layouts remain explicit; these are theorems about the
  valued model, with native refinement still open.
- Shared lookup slots have at most one active query. The proof follows their
  allocated intervals, branch selector equations and continuation cursors.
  Slot multiplicity is zero or one; each active combined message equals the
  uniquely decoded query after padding. Decoding preserves exact padded
  balance and emits at most one query per slot. Function-row validity uses
  this computed query pool without a separate raw-query membership premise.
  The circuit count validator establishes the single-return condition;
  the checked branchless predicate establishes unique consumer-slot writers.
- The complete valued circuit model includes member selector offsets, shared
  multiplicity and rank columns, header constraints and the physical return
  slot. A satisfying circuit with nonzero multiplicity selects an actual
  program function and yields a valid function row. Its inputs, rank and
  multiplicity agree with the circuit, its padded return message encodes
  that same call, and all selected call and rank-byte queries occur in the
  computed circuit pool. This covers singleton and grouped circuits, with
  native refinement and the explicit shape/layout conditions still open.
- Total control counts bound branch arities, continuation joins and return
  counts for every selector assignment. Both native system construction and
  the Lean binding builder check circuit membership and these count bounds,
  including consumed yields in the selector budget. A constructed backend
  retains the successful check. It discharges the four count/single-return
  premises of the circuit execution theorem; physical column, index and
  lookup-cursor correctness remain separate.
- Complete circuit witnesses now produce the locally valid function table
  used by finite execution extraction. A preliminary provider-only table
  supplies byte and memory facts; the final table's row validity is proved
  from each circuit's equations. Matching nonzero padded provider messages
  preserve global balance through both constructions, including arbitrary
  field multiplicities and zero-weight rows.
- Encoded circuit consumer slots have the same padded messages and count as
  the decoded pool. Their message widths bound decoded widths. Together with
  physical return providers, this gives execution of the selected public
  success call from valued circuit witnesses and encoded lookup balance.
  Native witness extraction and cryptographic reduction remain separate.
- Memory-table activity and pointer-increment constraints give a unique
  contents value for each width and pointer when table height is below the
  field characteristic. Exact lookup balance then makes store/load requests
  consistent. Initial pointers may be arbitrary and may wrap in the field.
  The separate query-count bound prevents cancellation of requests; a checked
  full-cycle counterexample shows why the height bound cannot be discarded.
  The polynomial interface derives boolean selectors from their equations.
- Successful compilation returns the exact artifact built from its actual
  inlining, checking/simplification, concretization and lowering stages.
- Total recursive bytecode comparison reflects exact syntax equality,
  including layout metadata and nested continuations. This supplies lawful
  keys for the deduplication hash maps.
- Tail-match restoration preserves the complete source evaluator result,
  including errors, early returns, memory and I/O, at unchanged call fuel.
  The helper and the source evaluator's memory-key hash are total definitions.
  Inlining expansion and let hoisting still need their own proofs.
- Splitting and combining leading let frames preserves the complete source
  result. Moving a return across those frames and sequencing I/O, assertion
  and debug continuations with wildcard lets also preserve it. Call modes
  have identical source evaluator meaning. These identities do not establish
  fresh-name correctness or preservation of the complete normalization pass.
- Deduplication validates every proposed function renaming against the full
  rewritten bodies, layouts and call domains. Invalid candidates retain the
  original program. The pass preserves and reflects successful reference
  execution at every fuel, including memory, I/O and early returns; its proof
  makes no correctness assumption about partition refinement.
- Final reachability metadata and circuit partition construction preserve
  reference bytecode execution. Their combination with checked deduplication
  preserves success at the actual remapping of each original function index.
- Successful explicit grouping preserves the source, name map, function
  array and memory sizes. It therefore preserves reference execution for
  every function, input, initial I/O state and fuel value, including errors
  and final I/O state.
- `BoundVerifier.Backend.execution_reflects_raw` combines grouping, final
  metadata and checked deduplication: successful reference execution of the
  selected backend reflects to the same named function in the actual lowering
  output. The proof recovers its original index from the compiler's name map.
- `BoundVerifier.verify_success` extracts input-arity agreement, successful
  checked proof parsing, and acceptance of the selected statement by the
  stored native verifier.

Run `lake run check-aiur` to build the component proofs and native tests with
warnings treated as errors, compare the complete audit report against
`Tests/Aiur/backend-foundation.txt`, and exercise the native verifier binding.
CI runs the same check. Native bytecode comparison and hashing must reproduce
the output captured from the original compiler derivations: 395 fixtures,
156,025 comparisons and every operation constructor. Deduplication tests
retain complete original syntax and index-map snapshots for 23 programs,
reject 14 altered candidates with the original program as fallback, and
exercise merged execution through early returns, continuations, memory and
I/O. Explicit default lookups avoid native panic diagnostics for invalid
callee indices. Native tail-match restoration reproduces 281 original syntax
snapshots, and source-value hashing reproduces 99 original hash values.
Nine compiler regressions compare both source evaluators with reference and
native bytecode execution. They cover argument and continuation effect order,
lexical shadowing, and the call boundary of an inlined callee with an explicit
return. Argument normalization uses distinct local names and sequences each
argument completely; callees containing explicit returns retain normal calls.
The source reference also evaluates debug arguments before their continuations,
preserving their effects and early returns.
These repairs have regression coverage; their full preservation proofs remain
open.
The binding tests accept
multiplication and grouped programs and reject 15 mutations of the selected
program, statement, grouping, parameters, key or proof bytes.
Supplied native equality-test witnesses accept zero and nonzero inputs with
correct outputs and reject three forged outputs. Direct native expression
checks cover 108 combinations of input, selector, output and inverse advice,
including unconstrained inactive rows and nonboolean function/memory selectors.
The component gate also compares every native preprocessed byte-chip column,
lookup argument and multiplicity-column mapping with Lean: 65,792 rows,
656,128 lookup messages and 34,664,621 bytes, generated in a temporary
directory. Native tests exhaust all 131,072 addition/subtraction input pairs
and accept seven supplied 32-bit comparison witnesses while rejecting three
that isolate carry, decomposition and byte-range constraints.
The gate also compares 21,556 native and Lean structural checks across return
sizes, constrained and advice calls, nested continuations, visibility and
public-claim widths. All 54 parallel release Rust tests pass, including the
supplied rank/output ambiguity regression; release Clippy denies warnings.

The audit checks 1,123 roots by traversing checked types, bodies and inductive
constructors. Thirty-three roots use no axioms; one uses only `Quot.sound`;
184 depend only on `propext`; 288 use exactly `propext` and `Quot.sound`;
the other 617 use exactly
`propext`, `Classical.choice` and `Quot.sound`. The combined closure
has 18,654 logical declarations and 19,435 declarations after following runtime
workers and replacements. The frozen report records four native runtime entry points,
three partial opaque sources and all 173 Ix recursion worker implementations.
Bytecode comparison/hashing, tail-match restoration and source-value hashing
use total definitions. Type hashing and type/pattern formatting remain partial.
These remaining implementations and
foreign runtime are inventoried without a refinement proof. Lean/Std runtime
primitives remain outside this project-specific runtime inventory. The report
also freezes the rank bound, packing, polynomial, compiler layout, exact
lookup balance, byte-table definitions, bytecode comparison/hash instances,
the checked deduplication definitions, tail-match restoration and source-value
hash instance, and the argument normalization and inlining entry points.
It also freezes the relational operation/control semantics and the function
row, request, provider and byte-query definitions.
The memory row/transition, validity, provider and immutable-fact definitions
and the symbolic full-cycle counterexample are frozen too.
The modular-squaring certificate, both selector polynomial forms, selector
summation order and memory polynomial interface are also frozen.
The byte channels, fixed rows, lookup messages/providers, bytecode operation
mapping, inverse-of-256 constant and four-byte carry-chain definitions are
frozen as well. Padding, channel-width schemas, typed message encodings and
all structural validator definitions are frozen. The backend constructor is
strengthened by checked entrypoint return arity, program lookup shapes and
circuit control counts;
the mixed lookup provider table, balance/count/width interface and range-query
encoding are frozen too, together with the total slot-sum and query-budget
definitions. The shared-message, selector-flow, return-gate, valued operation
emission, call-inventory and branch-polynomial definitions are also frozen.
The whole-block emitter, projection, execution premises, input preservation
and function-row interface are frozen as well, together with slot intervals,
active counts, message combination/decoding and the computed query pool.
The circuit/member emitter, physical lookup encoding, circuit query pool,
source-membership interface and layout-width definition are frozen too.
Control-count definitions, the guarded backend builder, provider-table
construction and circuit witnesses are also frozen, together with the
branchless predicate, unique-writer interface and encoded circuit pool.
Canonical circuit traces, their metadata and emission are frozen, together
with four recursion workers whose safe source definitions are checked.
Compiler and grouping invariants establish that every circuit member is a
constrained function. These discharge witness shape validity from the selected
backend's checked program. `LookupLayout` also proves that the compiler's
physical lookup allocation equals the valued emitter's extent, including
nested branches and continuations. Renaming and deduplication preserve the
count; singleton and grouped circuit layouts bound every member. The backend
trace execution theorem therefore requires no separate witness-shape or
lookup-limit hypothesis. The singleton circuit constructor, membership and
lookup-bound predicates, and total lookup-count definitions are frozen as well.
`MemoryColumns` decodes the native memory layout, four polynomial equations
and selector-scaled lookup. Satisfied canonical memory traces supply valid
rows and equivalent weighted providers. Compilation gives distinct canonical
memory widths; the checked global trace budget bounds table heights and
establishes functional memory. `Backend.memory_trace_execution` therefore
requires no independent memory-validity or canonical-width premise. The
memory comparison checks 1,800 native/Lean assignments over five widths and
five heights, including empty tables, cyclic next-row openings, final-row
transition gates, wrapping pointers, invalid selectors and inactive advice.
`ByteColumns` identifies all thirteen physical byte lookup slots with the
logical fixed-table providers, including their differing enumeration order.
The native Aiur verifier now checks that fixed preprocessed tables are active
and have the exact committed heights before entering the cryptographic
verifier. Its total Lean counterpart recovers byte degrees 8 and 16 from
canonical and active-order metadata. All 17,910 guard comparisons match;
the exhaustive byte corpus now evaluates the physical column lookup model.
The guard adds no AIR expression or key-format change. `SystemTraces` combines
function, memory and byte columns with their exact metadata and global budget.
`Backend.column_trace_execution` derives the selected public execution from
satisfaction and padded balance of these columns. Native extraction must still
establish those conditions for an accepted proof.
`ExpressionGraph` models the native node syntax and checked graph layout.
Valid layouts have bounded leaf/root indices, children before parents and no
stage-two column reads in the lookup prefix. Both forward sweeps are defined;
their shared values and extracted lookups agree. Unfolding produces expression
trees with the same evaluation for arbitrary working operations. The codec's
root-derived lookup prefix may be shorter than the compiler's stored prefix
after constant folding; the native corpus checks that both give the same
lookup values. All 88,228 layout cases and 240 assignments across ten actual
native graphs match Lean, including all 8,016 node values, constraint roots
and lookup messages. The corpus uses the existing v5 node encoding.
The native key decoder now validates graph reads before degree recomputation,
checks degree overflow and verifies the combined maximum degree. Its focused
regression originally panicked on a self-reference and now returns an error.
This decoder currently has no production callers in the workspace; key
serialization is the connected path. The parser, Rust execution, frontend
compilation and acceptance-to-satisfaction reduction still require refinement.
That checkpoint preserved all 308 earlier root statements and axiom sets,
318 premise definitions and 146 worker bodies byte for byte; it added 30 roots,
58 frozen definitions and four safe-source graph workers. The preceding branchless
repair's reviewed emitter change remains frozen. The concrete failures and
repairs are recorded in the [Aiur bug inventory](aiur-bug-inventory.md).
`FrontendExpressions` models the native smart constructors and proves their
evaluation laws, including constant folding and double-negation cancellation.
The proof works for any compatible working operations; the algebra laws are
proved for Goldilocks. A preserved check excludes negated constant children,
which is needed to identify syntactic constant flags after subtraction.
Expression degrees remain independent of those flags.
The addition, subtraction, multiplication and equality-test emitters now reflect
the valued operation model, including output metadata, allocated columns and
every equation. The reflection theorems require reads only from allocated
columns. The native corpus compares 1,752 exact smart-constructor trees and
9,804 actual scalar emissions at four assignments each, for 46,224 matching
evaluations. It includes raw negated constants outside the invariant and
degree metadata zero, one and two. That 388-root audit preserved all 338 earlier
root statements and axiom sets, 376 frozen definitions and 150 worker bodies.
It added 50 roots, 23 definitions/constructors and the total negation-check worker.
`GraphCompilation` extends reflection through the native base graph's structural
sharing, sorted commutative operands, equal-id subtraction and constant folds.
Every compilation step preserves previously assigned node values. Successful
base compilation preserves constraint satisfaction in both directions, including
dropped zero constants and sorted, deduplicated roots. Compiled lookup
multiplicities and arguments equal the original expressions in their original
order. These results hold for compatible working algebras, with the additional
commutativity and self-subtraction laws proved for Goldilocks.
The native corpus compares all nodes, degrees, root ids and stored lookup
prefixes in 1,484 actual base graphs. All 38 rejected source specifications,
11,872 assignments and 86,680 node values match Lean. Invalid children remain
rejected even inside raw multiplication by zero or equal-expression subtraction.
The 425-root audit preserves all 388 earlier statements and axiom sets, all 399
frozen definitions and all 151 prior workers. It adds 37 roots, 31 frozen
definitions/constructors and four total recursion workers. The native release
suite passes 63 tests and release Clippy; the strict 140-job proof/test build
and complete component gate pass with fourteen native comparison corpora.
The graph model uses natural-number indices and a linear structural interner.
Rust execution and hash-table refinement, machine bounds, extension-coordinate
expansion and native acceptance-to-satisfaction
reduction remain open. Aiur's native system builder supplies no user extension
constraints: its function, memory and byte circuits all use the base graph.

`OperationExpressions`, `OperationReflection` and `OperationSequences` cover all
34 operation forms and complete operation lists. Successful symbolic emission
and evaluation of the incoming value map derive the entire valued emission:
output expressions and tracked metadata, fresh-column cursor, equations, raw
queries, and call records with their six rank-gap expressions. The normal-form
invariant is preserved across every output and sequence. Fresh reads are
required only for allocated columns, with the sequence theorem requiring
exactly the consumed interval. Selector values need not be Boolean for this
reflection. Checked incoming indices still have to be connected to the native
store's reads after its pointer is appended.

`LookupExpressions` proves selector gating and argument accumulation evaluate
to the existing physical-slot multiplicity and message definitions. It covers
unequal message widths, empty slots and repeated writers, in emission order.
Its expression lookups feed the checked base-graph compiler. The native corpus
provides the actual operations, incoming trees and assignments; all 1,752
sequences, 7,008 assignments and 438 cases with shared slots match. It checks
exact output and constraint trees, independent degree metadata, both cursors,
and the full combined lookup expressions under both gating modes.
The 520-root audit preserves every prior 425 statement and axiom set, all 430
frozen definitions and all 155 worker bodies. It adds 95 roots, 44 definitions
and constructors, and two inspected total recursion workers. The strict build,
64 parallel release Rust tests, release Clippy and the component gate with
fifteen native comparison corpora pass. This checkpoint changes no native AIR,
compiler output or verification-key format.

`BlockSelectors`, `BlockExpressions` and `BlockReflection` extend symbolic
reflection through recursive control and complete blocks. The proof derives
the valued equations, logical maps, cursors, raw queries, returns, escaping
yields and gated calls. It accounts for branch column reuse, default inverse
advice, continuation merge columns and consumed yields. Selector tables are
finite; incoming gates need not equal block entries or be Boolean. Required
fresh reads cover only the consumed column interval. `BlockLookups` handles
the shared return channel without adding to its multiplicity. All 384 actual
native control trees and 1,536 assignments match, including zero-width merges
and preserved outer yields. The test transports Rust's operations and control
trees instead of generating corresponding Lean fixtures.

`CircuitExpressions` and `CircuitReflection` compose grouped members with
consecutive selector regions, shared rank and multiplicity columns, the three
rank-byte queries, and every physical lookup slot. Successful symbolic emission
and reads from its finite header/member allocation derive complete valued
circuit emission. The read bound is explicit and must fit the supplied trace;
the proof does not assume equation values or lookup messages. All 96 actual
native circuit builds and 384 assignments match exact expression trees,
layouts, branchless decisions and evaluated results, including empty circuits
and empty branches that emit lookups. All corpus read bounds fit native widths.

`CompiledCircuitRows.compileCircuit_reflects` connects this emission to the
checked base-graph compiler. It derives a valued circuit row and a defined
graph sweep, proves graph-root satisfaction equivalent to all valued equations
vanishing, and identifies the entire physical lookup vector. The circuit
corpus also checks this composition for every assignment. This establishes
the composition for the Lean emitter and compiler models; refinement of the
Rust execution and the accepted-proof boundary remains open.

The 586-root audit preserves all 520 earlier statements and axiom sets, all 474
frozen definitions and all 157 worker bodies. It adds 66 roots, 54 definitions
and constructors, and five inspected total recursion workers. The new native
release suite passes 66 tests and release Clippy. The strict 283-job build and
complete component gate pass with seventeen native comparison corpora.
Native AIR, compiler output
and verification-key formats are unchanged. Earlier compiler-pass reflection,
runtime refinement and the certified semantic/cryptographic endpoint remain
separate obligations.

`OperationDegrees` and `BlockDegrees` prove that tracked degree zero implies a
constant expression, starting from advice inputs and surviving every operation,
branch and continuation. Positive tracked degrees may accompany folded
constants. This distinction justifies the compiler's zero-column equality-test
case without excluding conservative metadata used by native emission.
`OperationAllocation` and `CompilerAllocation` identify the actual compiler's
logical output degrees and auxiliary allocation for all 34 operations.
`EmissionAllocation`, `CompilerBranches` and `BlockAllocation` prove agreement
with successful symbolic emission through complete operation sequences and
recursive blocks. The proofs account for degree-based multiplication allocation,
word packing and carries, branch reuse, default inverse columns and continuation
advice. They do not assume equality of compiler and emitter allocation.

The allocation comparisons reuse the native expression corpora. All 1,168
sequences whose inputs satisfy the degree-zero invariant, all 384 block layouts
and all 48 function layouts agree with the actual compiler. The remaining 584
operation sequences deliberately contain degree-zero nonconstant inputs; all
their earlier expression and value comparisons still run. The 647-root audit
preserves all 586 earlier statements and axiom sets, 528 frozen definitions and
162 worker bodies, adding 61 roots and nine definitions/constructors. The strict
297-job build and complete component gate pass with seventeen native comparison
corpora. This checkpoint adds no native behavior change.

`CompilerLayout` proves input-width preservation, exact leaf-selector allocation,
monotonic auxiliary allocation, and preservation of the entire computed layout
state under function renaming. `FunctionLayout` carries the exact layout through
successful lowering, deduplication and final compilation to the checked backend.
`CircuitLayout` proves that singleton and grouped circuits contain every member's
input and auxiliary columns, including the seven reserved header columns.
These facts combine with the existing checked row counts in `CircuitAllocation`
to bound consecutive member selector regions and every symbolic read by the
physical circuit width.

`Backend.compileCircuit_reflects` now derives the valued row from the supplied
physical columns, with graph-root satisfaction and the complete lookup vector.
It has no independent read-bound premise. Successful symbolic compilation,
the graph-width binding and values fitting those widths remain explicit;
Rust execution and cryptographic acceptance are not assumed proved. All 96
native circuit layouts satisfy the column and selector bounds, and all 384
assignments pass the complete symbolic-circuit/base-graph composition.
The 687-root audit adds 40 roots and four definitions while preserving all 647
prior statements and axiom sets, 537 frozen definitions and 162 worker bodies.
The strict 305-job build and full component gate pass with seventeen native
comparison corpora. No native implementation changes. Deriving successful symbolic compilation,
earlier compiler-pass reflection, runtime refinement and the certified
semantic/cryptographic endpoint remain open.

`GraphCompletion` proves that defined reads supply expression and lookup
compilation, and that a satisfying assignment excludes rejection of nonzero
constant constraints. The constant interpretation must be injective; Goldilocks
satisfies that requirement. `InactiveRows` proves that zero selectors satisfy
every successfully emitted block for arbitrary logical values and advice.
It also proves that every successfully emitted circuit has a satisfying
all-zero row. This is a construction witness for the circuit equations; it
does not supply an active public call or an accepted proof.

`CircuitCompletion` uses that row and the physical bounds to construct the
base graph. `Backend.emittedCircuit_reflects` derives graph construction, a
valued circuit row, graph-root satisfaction and every lookup value from
successful symbolic emission and physical column values. It no longer assumes
base-graph compilation succeeds. The canonical base-graph widths are derived
from the circuit. Successful symbolic emission itself, refinement of native
execution, proof acceptance and source/claim meaning remain open.
The native builder and Lean both satisfy the zero-row check for all 96 circuit
fixtures; all 384 transported assignments continue to match. The 719-root
audit adds 32 roots and three definitions while preserving all 687 prior
statements and axiom sets, 541 frozen definitions and 162 worker bodies.
All 66 Rust release tests, release Clippy and formatting checks pass. There
are no native production-code changes. The strict 311-job build and full
component gate pass with all seventeen comparison corpora.

`EmissionChecks` validates the incoming logical scope of every emitted read,
the exact output count of all 34 operations, every terminal selector and
the widths of words, assertions and continuation yields. Branches restore
their incoming scope; continuations append only merge values. Virtual carries
count as logical outputs. Native scope additions use checked arithmetic, and
the Lean check uses the same 64-bit bound. Advice and I/O operands that the
constraint builder does not read impose no additional AIR requirement.
Both `BoundVerifier.build` and native system construction enforce the check.
A malformed one-input `Add(0, 1)` function previously passed the earlier guards
and panicked during constraint construction; it now rejects at the new guard.
No false-claim acceptance was demonstrated for this failure.

`EmissionInputs`, `EmissionControls` and `BlockCompletion` prove that the checks
supply operation and recursive block emission, including scoped yields.
`CheckedCircuit` carries the result through constrained circuit membership.
`Backend.circuit_graph_reflects` constructs the symbolic circuit, physical base
graph and valued row for column values fitting the circuit's derived widths.
It proves graph-root satisfaction equivalent to all valued equations vanishing
and identifies every lookup value. There is no separate emission-success,
graph-construction-success or physical read-bound premise. Native runtime
refinement, accepted-proof extraction, source semantics and the certified
semantic/cryptographic endpoint remain open.

The new comparison matches 1,365 operation checks, 1,157 sequences and 6,500
control scopes, including invalid reads, missing selectors, branch-local
values, nested continuations, wrong widths and machine boundaries. The 96
native circuit fixtures also pass the new guard. All 72 Rust release tests,
release Clippy and formatting checks pass. The 749-root audit preserves all
719 previous statements and axiom sets, 542 frozen definitions and 162 worker
bodies. The backend constructor and builder now record and enforce the check;
30 roots, 11 definitions and three inspected total recursion workers are added.
The strict 324-job build and full component gate pass with all eighteen native
comparison corpora. All 1,345 broader Aiur assertions pass. The C2 VM recheck
passes with 12 accepted packets, 16 rejections, the same two documented profile
exclusions and no unexpected errors. The guard preserves the emitted equations,
layouts and key bytes of programs that pass it.

`KeyCodec` supplies a total host decoder and encoder for the complete native
v5 key: all seven parameters, circuit metadata, every node tag, constraint
roots, lookup records, preprocessed Merkle cap and circuit indices. Checked
decoding validates graph reads, node-degree arithmetic, the combined user and
logUp degree, lookup grouping and the cap's power-of-two root count. Derived
widths and constraint counts retain the pass-through accumulator even for a
circuit with no lookups. Parsing consumes the complete byte array.

The codec proofs establish round trips within the wire bounds, including
arbitrary surrounding bytes, and injectivity of canonical encoding. Accepted
decoding supplies valid graphs and a well-shaped cap. The optional canonical
gate rejects the native decoder's alternative representations of constants.
`BoundVerifier.build` enforces that gate on the selected key, retains its
decoded value and checks all parameters against the deployment selection.
`Backend.key_graph_reflects` supplies full and lookup-prefix sweeps of each
decoded graph and identifies their roots and messages with expression
evaluation. It takes neither a parsing-success nor a graph-validity premise.
It does not identify that graph with the compiler model or prove native
verifier execution. Parameter admissibility, preprocessed commitment meaning,
accepted-proof extraction and the remaining certified semantic/cryptographic
endpoint remain separate obligations.

The new native comparison covers 4,536 full-key byte cases: 509 accepted keys,
22 accepted noncanonical encodings and 517 decoded circuit records. It checks
exact canonical bytes, every derived metadata field and every node degree.
Cases include all tags, truncations, suffixes, malformed graph reads, degree
overflow, all supported lookup group sizes, empty circuits and maximum wire
fields. The existing ten-graph evaluation corpus now uses this checked codec.
An empty Merkle cap exposed a native constructor panic; zero and non-power-of-two
cap sizes now return an error. The native decoder still has no production
callers in the workspace, and no false-claim acceptance was shown.

The 796-root audit preserves all 749 prior theorem statements and axiom sets,
553 frozen definitions and 165 worker bodies. Its two reviewed definition
changes are the backend constructor and builder; 47 roots, 49 definitions and
four inspected total codec workers are added. All 74 Rust release tests and
release Clippy pass, as do the canonical-key comparisons and the existing
two accepted/fifteen rejected native binding cases. The strict 332-job build
and full component gate pass with all nineteen native corpora. Native AIR expressions,
layouts and serialized keys are unchanged.

`BoundVerifier.buildCompiled` now checks the entire decoded circuit list
against a total compiler model and returns a `CompiledBackend` retaining that
check. Function circuits appear in compilation order, followed by the memory
widths and both byte tables. Equality covers every graph node, constraint
root, ordered lookup, matrix dimension, degree, grouping choice and
preprocessed index. The existing generic `build` remains available.

Successful graph compilation is unchanged when additional columns are
available. This connects the function compiler's physical main width to the
key's complete layout, including stage-two and public-input columns. The
memory and byte expression builders evaluate to their physical column models.
The `CompiledBackend` graph-reflection theorems use the enforced comparison
to supply graph equality, compilation success and dimensions for every circuit
family. They derive the same equations and ordered weighted messages from
values fitting the selected key. No independent graph-equality or read-bound
premise is required. Native verifier execution, preprocessed commitment
meaning, parameter admissibility and cryptographic acceptance remain open.

Native comparison covers twelve complete systems, 180 circuits and 720
assignments to all matrix families, public values and row selectors. It
compares the actual encoded keys and emitted equations and lookups with the
checked compiler and physical models. All 168 altered keys retain valid
canonical syntax and fail the new circuit-binding guard. The ordinary and
grouped backend tests now use `buildCompiled`: two valid proofs are accepted
and fifteen altered cases are rejected. All 75 parallel Rust release tests
and release Clippy pass. The 831-root audit adds 35 roots and twenty frozen
definitions; every prior statement, axiom set, definition and all 169 worker
bodies are unchanged. The strict 346-job build and complete component gate
pass with all twenty native corpora. Native production code and key bytes
are unchanged.

`BoundVerifier.verifyShaped` now decodes the accepted bytes into a complete
proof artifact and checks its opening dimensions against a `CompiledBackend`.
The total codec retains every commitment, quadratic extension coordinate,
FRI round, opened value and Merkle authentication digest. Its proofs establish
round trips, injective canonical encoding, complete consumption, u64 vector
length bounds and 32-byte digest bounds. Native bincode permits a trailing
suffix; this host entry point requires exact canonical framing.

The checked proof records are indexed by the actual activation bitmap and
the selected key's canonical circuit order. They retain both opening points,
quotient slices and accumulators, with checked column widths and domain
bounds. Acceptance also supplies fixed trace heights and the strict global
lookup budget. The wrapper then verifies the same bytes and the selected
public statement through the existing native interface. Its theorem provides
these framing and shape facts directly from success; it does not yet derive
authenticated polynomials, satisfying traces or cryptographic failure bounds.
Native execution refinement and the certified release remain open.

The proof codec comparison covers 3,636 native/Lean byte cases, all fields of
twenty decoded records and eight native-accepted suffixes rejected by the
host framing gate. Four original proofs pass full native verification. The
shape comparison checks 4,696 cases across four systems, including every u8
degree and independent changes to activation, matrices, opening points and
columns. Native and Lean agree on 510 accepted shapes; 266 also meet the
fixed-height and budget guards. These shape fixtures deliberately omit PCS
data and make no cryptographic acceptance claim. The ordinary and grouped
backend tests use `verifyShaped`, accepting two valid proofs and rejecting
seventeen altered cases. All 78 parallel Rust release tests and release
Clippy pass. The 884-root audit adds 53 roots and 65 frozen definitions and
constructors, preserving all prior statements, axiom sets, definitions and
169 worker bodies. The strict 364-job build and complete component gate pass
with all twenty-two native corpora.
Native production behavior and serialized proof/key bytes are unchanged.

`Extension` gives the proof codec's two canonical coordinates their pinned
arithmetic meaning, with basis `1, u` and `u² = 7`. It implements addition,
subtraction, negation, multiplication, conjugation, norm, scalar multiplication,
binary exponentiation and checked inversion. `GoldilocksAlgebra` proves the
ring laws through an injective residue map, and relates the existing
64-bit repeated-squaring routine to mathematical powers.
`GoldilocksInverse` proves Fermat's theorem by permuting the nonzero residues
and cancelling their product. The enumeration is a noncomputable proof
definition and generates no runtime initialization code.

`ExtensionField` proves that seven has no square root using a
kernel-evaluated Euler certificate and the proved Fermat theorem. It derives
the absence of zero divisors, the nonzero norm of every nonzero extension
value, and correctness and uniqueness of the concrete inverse formula.
Checked inversion returns a value exactly when its product with the input
is one; zero returns `none`. The extension ring laws instantiate the same
working-operation interface used by the existing expression reflection.

The native comparisons cover sixteen base inverses, 384 extension values,
7,680 powers and 147,456 ordered operand pairs. Exponents include both field
boundaries, `2^64`, the quadratic-field inverse exponent, and `2^128 - 1`.
All 240 extension assignments and 8,016 node values from ten actual compiled
graphs agree with both graph sweeping and expression evaluation. The audit
adds 71 roots, 32 definitions and instances, and two inspected recursion
workers; all 884 prior statements and axiom sets, 689 definitions and 169
worker bodies are unchanged. Native field-instruction refinement and the
connection to verifier acceptance remain open.
All 80 parallel Rust release tests, release Clippy with warnings denied and
formatting pass. The strict 379-job build and complete component gate pass
with all twenty-four native corpora and the unchanged two accepted and
seventeen rejected backend cases.

`LookupCoordinates` retains the two separate coordinates checked by native
degree-two logUp. Its Karatsuba multiplication has proved ring laws over
any commutative coefficient ring. For base-field trace values, the pair
identifies with the proved native extension field. At an out-of-domain opening,
each coordinate is itself an extension value: combining the pair with the
extension basis loses a constraint. A checked example gives a nonzero pair
`(-u, 1)` that combines to zero. No field or cancellation law is assumed for
that coordinate algebra.

`LogUp` models the direct evaluator with checked node, public, accumulator and
boundary-coordinate reads. It normalizes group size zero to one, rejects sizes
above eight, and covers the empty pass-through, singleton, full-group and tail
cases. `LogUpAlgebra` relates Horner fingerprints and seeded prefix/suffix scans
to the denominator-cleared grouped polynomial. Padding arguments with trailing
zeros preserves the fingerprint. Successful evaluation yields every group's
two polynomial equations in native order, and the graph reflection theorem
connects lookup reads to the corresponding frontend expressions.

`LogUpFractions` proves that, on base-field trace rows with no zero message
denominators, the grouped equation vanishes exactly when the accumulator
difference equals the weighted sum of message inverses. It also proves a
counterexample showing why the denominator condition is necessary.
`LogUpAccumulator` telescopes all groups in a complete checked row, retaining
the last-row injection supplied by the caller. Further ring lemmas sum a
cyclic sequence of rows and a chain of circuit accumulators. The domain
results below supply the selector normalization and cyclic row indexing.
Extracting the corresponding polynomials from authenticated openings, and
excluding poles and compression collisions to obtain exact message balance,
remain obligations.

The comparison corpus checks 4,752 direct native evaluations against the
independent symbolic schoolbook reference and the Lean model, in both the
base and extension fields. It covers all group sizes zero through eight,
22 lookup counts through 65, ten argument widths, field boundaries, zero
denominators and arbitrary extension-valued coordinates and selectors.
The checked Lean reader additionally rejects 42,768 malformed inputs.
Native stage-2 construction matches all partial accumulators and zero equations
in 27 batches, 135 circuits and 513 rows, including variable argument padding,
cyclic next rows and the raw last-row selector with a scaled boundary delta.
These comparisons do not prove Rust implementation refinement or extract
vanishing equations from native verifier acceptance.

The logUp audit adds 95 roots, 36 definitions and instances, and one inspected
structural recursion worker. All 955 prior root statements and axiom sets,
721 definitions and 171 worker bodies are unchanged. The native runtime
entry points and partial opaque sources remain the same. All 82 parallel
Rust release tests, release Clippy with warnings denied, and formatting pass.
The strict 396-job build and complete component gate pass with all twenty-six
native corpora and the unchanged two accepted and seventeen rejected backend
cases.

`Domain` retains all 33 pinned Goldilocks generators and represents rows by
finite indices, without enumerating large domains. Kernel-evaluated bounded
squaring certificates prove the generators' full and half orders and adjacent
square relations. The resulting order theorem proves distinct row points,
cyclic next-row multiplication, and the inverse-generator last point for
every supported size from one through `2^32`. The domain size and the
last-row normalization factor `n * generator` are nonzero in Goldilocks.

`SelectorAlgebra` proves the divided-power polynomial identities underlying
the selectors. `Selectors` proves that the checked rational evaluator is
defined exactly where the vanishing polynomial is nonzero, and agrees there
with the selector polynomials. On trace rows, the first selector equals `n`
only at the first row; the last equals `n * generator` only at the last row.
These facts include the size-one case. `DomainAccumulator` cancels the native
inverse normalization and derives the complete circuit fraction sum from
all cyclic rows' checked lookup equations, with an explicit pole-free premise.
It also extracts the actual lookup values from the node buffers.

`Quotient` rejects incomplete coordinate pairs and recombines every quotient
slice with the native extension basis in ascending powers of `zeta^n`.
The constraint fold uses descending powers of `alpha`, preserving the user
constraints followed by both coordinates of each lookup equation. Successful
arithmetic checking is equivalent to a nonzero vanishing value and
`composition = vanishing * quotient`. This equivalence alone does not prove
that openings come from committed low-degree polynomials or that a random
challenge detects a violated constraint.

The domain corpus directly calls the pinned native polynomial-space methods.
All 33 generators, 966 row samples, 1,987 defined and 125 rejected selector
assignments, and 511 complete small-coset points match Lean. The quotient
corpus reproduces the verifier's private recombination expression with native
basis, power and field operations: 384 accepting and 320 rejecting arithmetic
cases match. Lean additionally rejects odd quotient rows and selector poles
in every case, and rejects 320 altered accepted quotient rows. These are
arithmetic comparisons, not cryptographic proof acceptance tests.

The domain and quotient audit adds 73 roots, 17 definitions, and one inspected
structural coordinate-pairing worker. All 1,050 prior root statements and
axiom sets, 757 definitions and 172 worker bodies are unchanged. The native
entry points and partial opaque sources remain the same. The selector
polynomial is symbolic and has no runtime enumeration or initialization.
All 84 parallel Rust release tests, release Clippy with warnings denied,
formatting, the strict 415-job build and the complete component gate pass.
The gate covers all twenty-eight native corpora and the unchanged two
accepted and seventeen rejected backend cases.

The budget comparison covers
21,964 Rust/Lean cases, including
all byte-sized degree values, field and machine boundaries, inactive circuits
and malformed metadata lengths. The selector comparison covers 1,014 field
assignments across 48 control trees and 3,584 shared-message cases. It compares
the actual native selector expressions, selector polynomial projection,
escaping-yield collection and return arguments, including unsatisfied link
equations and different raw message lengths. The operation comparison covers
6,240 assignments across all 34 constructors and sequences that reuse outputs.
It compares logical values, degree and constant metadata, column and lookup
cursors, all polynomial values and all gated query arguments. A further 768
assignments cover folded constants with positive tracked degree, including
`eq_zero(0 * x)`. Those inputs previously crashed native constraint construction.
The repair emits the ordinary two-column equality test when the tracked degree
is positive, matching the compiler and witness layout. Six source variants
pass at four inputs in singleton and grouped circuits, with eight honest proofs
accepted and eight altered public outputs rejected. The original 6,240 records
are unchanged. The 338-root audit changes only the frozen valued emitter's
`eq_zero` branch; its theorem statements, axiom sets and recursion workers are
unchanged. The native release suite passes 61 tests and release Clippy.
The whole-block
comparison covers 2,028 assignments across 96 fixtures with shared branch
columns and lookup slots, default inverse advice, nonempty yields, early
returns and continuation scope. It compares all emitted equations and lookup
arguments, logical values and their metadata, and escaping yield values,
including on assignments with unsatisfied selector links.
The slot-message and multiplicity definitions used by the extraction proofs
are also used in that native comparison.
The whole-circuit comparison matches 2,022 assignments across 96 fixtures
against the actual Rust circuit builder. It covers singleton, grouped and
empty circuits, different member orders, input and return widths, shared
multiplicity/rank columns and all physical lookup slots, including invalid
selector and rank-byte assignments. It also compares 48 complete control-count
records and 588 native/Lean validator outcomes, including insufficient selector
budgets, missing members, duplicated members and empty circuits. The corpus
now includes empty branches that emit lookups and compares all 96 branchless
decisions. Native
regressions exercise consumed yields, empty matches, machine/field boundaries
and construction-time rejection. All 49 native release tests and Clippy pass.
The branchless repair addresses a supplied-witness counterexample: a function
whose reference result is `1` previously verified the public result `7`.
An inactive empty branch's store message had altered the selected call's
channel because both messages were sent without selector gating. Such
circuits now use gated messages and one lookup per accumulator step. The
invalid result is rejected, while the honest generated proof verifies.
Verification keys must be rebuilt for circuits whose optimization changes.
Padded balance still needs extraction from randomized compression, together
with the Rust refinement connecting the reflected emitter model to execution.

The call-rank repair increases proving cost through its range-checked columns
and lookups. The IxVM FFT estimate for `Nat.add_comm` rises from 321,980,321 to
450,907,517, and for `Array.append_assoc` from 9,591,140,574 to 18,441,968,781.
Replaying the compiler from before the hoisting repair on all 81 pinned
constants gives identical outputs, I/O, query counts, circuit shapes and costs
to the repaired compiler. The hoisting repair adds no cost on that corpus.

These results reach the bytecode produced by lowering. Full C8 requires public
certified verification to imply the claim's intended source meaning, under
the explicit set-theory hypothesis and a quantitative cryptographic failure
bound. The remaining components are:

| Component | Remaining obligation |
| --- | --- |
| Native verifier | Connect the enforced proof codec and shape checks and proved field, grouped lookup, domain and quotient models to native transcript and PCS checks, then extract satisfying committed traces from acceptance. |
| Cryptography | Prove the commitment, polynomial-testing, FRI and Fiat–Shamir guarantees with admissible parameters and explicit failure bounds. |
| Randomized lookups | Derive the exact bounded weighted message balance used by execution extraction, excluding specified compression collisions and denominator failures. |
| Fixed tables | Bind the preprocessed commitments and openings to the proved byte tables and their required dimensions. |
| Compiler | Complete backward execution reflection through lowering and the remaining source transformations. |
| Certified checker | Connect successful execution of the selected checker program to the host checker and claim-semantic results. |
| Public release and runtime | Instantiate that checker, entrypoint, statement encoding, parameters and key in the public path, with the required native/FFI and cache correspondence. |

Satisfying physical function, memory and byte rows already compose with
bounded exact lookup balance to give execution of the selected bytecode
success call. The conditions must still be derived from actual verifier
acceptance, and that execution must be carried back to the certified claim.
Taking these conditions as theorem hypotheses does not discharge them.

The source and bytecode references use uncached calls. Repeated effectful calls
can behave differently in the caching interpreter and native runtime: writes
may occur once instead of twice, and a repeated key insertion may succeed
because its second call is cached. A general native-to-reference theorem for
arbitrary effectful programs therefore needs a different execution model or
proved restrictions on the selected program. Cache refinement remains open.

`Ix.Aiur.Semantics.AIR` supplies the relational model used for AIR extraction.
It covers every bytecode operation, keeps returns separate from continuation
yields, and represents constrained calls as requests for other rows. Advice
is chosen per operation: I/O reads, key information and unconstrained calls
or hints need not equal the runtime's computed values. I/O writes, key
insertion and debugging impose no AIR relation. The four result bytes of
an unconstrained u32 sum are advice, but its carry remains a field expression.
Memory facts relate a width and pointer to contents. `Proofs/Memory.lean`
proves their functionality from the local memory constraints and trace-height
bound, and extracts queried facts from exact balance with bounded query counts.
Extracting these rows and their satisfaction from native verifier acceptance,
along with the selected certified program's checks, remains open.

The component gate exercises 45 operation fixtures, the virtual carry
equation, and checked derivations for shared callees, memory, continuation
scope and early returns. Supplied native trace tests accept unchecked advice
whose purported bytes exceed 255, reject a changed public carry, and reject
an incorrect inverse when the program constrains its product to one. Honest
checked inverse execution also verifies. These tests establish the intended
model boundary; they do not prove the native row-extraction theorem.

The memory regressions additionally accept a supplied native proof whose
memory pointers start at the field's maximum element and wrap to zero. The
same table has a checked local-validity proof in Lean. Local native checks
for widths 1, 4 and 8 reject duplicate consecutive pointers and active rows
after padding. These memory tables need not follow runtime insertion order,
deduplicate equal contents, or represent acyclic data; source reflection must
establish the properties actually needed by the selected certified program.
