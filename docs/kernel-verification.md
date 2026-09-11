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
public-claim widths. All 49 parallel release Rust tests pass, including the
supplied rank/output ambiguity regression; release Clippy denies warnings.

The audit checks 268 roots by traversing checked types, bodies and inductive
constructors. Twenty-two roots depend only on `propext`; sixty-five use exactly
`propext` and `Quot.sound`; the other 181 use exactly
`propext`, `Classical.choice` and `Quot.sound`. The combined closure
has 15,179 logical declarations and 15,876 declarations after following runtime
workers and replacements. The frozen report records four native operations,
three partial opaque sources and all 139 Ix recursion worker implementations.
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
All prior 242 root statements and axiom sets, 262 premise definitions and 137
worker bodies remain byte-for-byte unchanged; two safe-source lookup-count
workers are added. The preceding branchless
repair's reviewed emitter change remains frozen.
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
cursors, all polynomial values and all gated query arguments. The whole-block
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
Padded balance still needs extraction from randomized compression, and the
valued model still needs reflection from the native emitter.

The call-rank repair increases proving cost through its range-checked columns
and lookups. The IxVM FFT estimate for `Nat.add_comm` rises from 321,980,321 to
450,907,517, and for `Array.append_assoc` from 9,591,140,574 to 18,441,968,781.
Replaying the compiler from before the hoisting repair on all 81 pinned
constants gives identical outputs, I/O, query counts, circuit shapes and costs
to the repaired compiler. The hoisting repair adds no cost on that corpus.

These results reach the bytecode produced by lowering. Full C8 still needs
backward reflection through lowering and the earlier compiler passes, execution
extraction from arbitrary satisfying AIR witnesses, certified source/claim
checking inside the selected VM program, enforced certified release/key
selection, and the cryptographic reduction with explicit bad events. The
grouping result concerns reference execution. The valued model now composes
grouped circuit rows; extraction from the actual grouped AIR remains open.

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
Decoding the native memory rows and deriving these conditions from verification,
along with the selected certified program's checks, remain open.

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
