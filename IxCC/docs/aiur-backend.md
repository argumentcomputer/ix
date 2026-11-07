# Aiur backend: trace, wire, execution, and static assignments

The initial Aiur implementation provides a pinned pure target vocabulary and
a checked logical-trace interface. It proves that active, balanced lookup
demands have providers and that a static row certificate yields finite rooted
derivations. The [canonical bytecode boundary](aiur-wire.md) now preserves
the complete pinned toplevel, checks its content root, and invokes the
upstream component checker behind resource guards. The
[witness-heap execution model](aiur-semantics.md) now interprets all pinned
operations and controls and composes checked bytecode rows into finite
executions. The [static assignment checker](aiur-static.md) constructs the
required certificate from ordinary row/rank data and checked metadata.
The [counter-analyzer proof](aiur-counter-analysis.md) establishes the
inferred self-call relation for every successful local body. The
[memory AIR extraction](aiur-memory-air.md) now derives pointer uniqueness
and one coherent heap from the modeled memory polynomials, with checked
activity and exact lookup payloads. The [rank AIR extraction](aiur-rank-air.md)
derives bounded limbs and natural rank increase from scalar-range balance
and complete physical function-message binding. Source lowering and full
extraction from the keyed AIR remain subsequent work.

The source boundary now follows the [ix frontend and Ixon v4](ixon-v4.md),
including independent usage, ownership, relative locality and scoped loans.
Its resource admission consumes the published frontend handoff; erased
typing and contract-preserving Ixon-to-Aiur lowering remain separate work.
The source producer pin is independent of the target snapshot below.

## Reference and module boundaries

[`IxCC/Vendor/upstream.json`](../IxCC/Vendor/upstream.json) pins eleven
Lean modules and both upstream licenses from argumentcomputer/ix at
`a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03`, vendored as modules `IxCC.Vendor.Ix.*`
(upstream `Ix.*`) with declarations under `IxCC.Vendor` (upstream `Aiur.*`,
`IndexMap`, …): an import prefix and a namespace wrapper are their only change.
They supply Goldilocks, the source-to-bytecode IR vocabulary, layout and call-component definitions,
and the existing abstract counter/order lemmas. Their upstream toolchain is
Lean 4.33.1; they build with this repository's pinned Lean 4.34.1.

The vendored modules import no native Aiur FFI. The upstream
bytecode evaluator currently imports its IO types from an FFI module, so it
is deferred until that pure interface is split. No evaluator shim or native
stub is substituted under an upstream module name.

The wire API uses the existing BLAKE3 interface for content roots. Its pure
codec proofs use ordinary logic; addressed wrappers retain the existing
native BLAKE3 axiom exception. The exact grammar, component-check scope,
fixtures, and ix exporter contract are in [aiur-wire.md](aiur-wire.md).

[`IxCC.Aiur`](../IxCC/Aiur.lean) exposes the new production API.
Tests, source-inventory checking, and axiom fences have separate module roots.

## Logical traces and checked facts

[`Trace`](../IxCC/Aiur/Trace.lean) distinguishes exact function
messages (function, inputs, outputs), memory messages (bucket, pointer,
contents), and gadget messages (channel, values). Message equality includes
the complete payload and kind. These constructors are a logical model;
their correspondence to encoded AIR channels and layouts must be proved by
the future extraction adapter.

A row supplies one message with a Goldilocks multiplicity and, when active,
requests a list of unit-weight messages. Public claims add unit demands.
For every exact message, balance means:

```text
G.ofNat(number of active row demands + public demands)
  = sum of all matching provider multiplicities
```

Provider multiplicities may be negative field values. They are not modeled
as natural counts. Activity requires every nonzero provider to be active.
The logical slot budget counts one provider slot per row, all active unit
demands, and public claims, and must be strictly below the characteristic.
The AIR adapter must show this is bounded by the verifier's checked slot
budget, which also counts provider slots and padding rows.

[`Trace.validate`](../IxCC/Aiur/Check.lean) checks activity, complete
message balance, the characteristic bound, and memory coherence. It returns
`Trace.Validated trace` retaining the corresponding proofs. Balance checking
enumerates the finite mentioned-message set; its soundness theorem covers
all messages, including absent ones and unused providers.

The supplied-trace checker has separate structural limits: by default 256
rows, 1,024 total units, and 64 fields per message. Its resource preflight
counts raw demands even on inactive rows. These limits bound the finite
quadratic checks; they are not evaluator fuel or a STARK trace-height policy.
No binary trace parser is included yet.

## One witness heap

[`Memory`](../IxCC/Aiur/Memory.lean) checks that active memory
providers with the same bucket and pointer agree on their contents. It
constructs one heap from those providers and proves that every observed
memory cell agrees with that heap. `Trace.Validated.memory_agrees` applies
this result to a derived memory observation.

There is no prior-store or insertion-order requirement: pointer seven is a
valid observation even if the honest allocator would have chosen zero.
Coherence does not establish valid datatype tags, ranges, pointer-field
layouts, or heap acyclicity. A coherent self-referential memory cell is
therefore deliberately accepted by this boundary. Those stronger properties
need their own constrained representation or source-admission evidence.

The memory AIR checker derives coherence from the four modeled memory
polynomials, distinct bucket identities, and bounded table heights. It proves
pointer uniqueness through field wraparound and checks selector Booleanity
for activity. Its graphs match five frozen outputs of the actual pinned Rust
memory builder. The [memory AIR contract](aiur-memory-air.md) states the exact
extraction and remaining Booleanity, assignment, and key-binding boundaries.

## Static order, counters, and ranks

[`StaticCertificate`](../IxCC/Aiur/WellFounded.lean) records facts
about the extracted rows and a fixed ranked/unranked choice per component.
Each dependency must either advance component order or stay in one
component and:

- increase its natural-number rank, when that component is ranked; or
- advance its Goldilocks counter by one, when it is unranked.

The mixed certificate permits counter, static-order, and ranked edges in one
trace. A cycle cannot advance component order. Within one component it
cannot strictly increase a natural rank, and a unit-counter cycle of length
`0 < m < p` is impossible. A finite-row pigeonhole argument supplies the
short-cycle bound. The bound concerns distinct trace rows, not the size of
the unfolded derivation tree.

`Static.validate` now constructs this certificate: the pinned analyzer
selects counter positions and directions, and the checker verifies every
actual provider dependency. It retains the checked program metadata and
uses separate order numbers when ranked and counter functions share an
upstream component order. All four input/output unit directions, ranked
fallback, and natural rank witnesses are covered by the
[assignment contract](aiur-static.md).

The universal analyzer/body theorem now proves the inferred counter relation
and its four normalized unit directions. Rank extraction now derives each
u16 limb from normalized range lookup balance and the fixed table, then
proves that an ordered call's natural rank increases without field wrap.
The trailing physical rank must remain in provider matching; equality of
logical messages with that field erased is insufficient. Deriving local
bodies, counter observations, component facts, lookup bounds, and the full
rank-preserving projection from the keyed AIR remains work. General nonzero
steps, zero-step sub-orders, and broader output-counter recognition remain
extensions.

## Derivation endpoint and remaining assumptions

[`Trace.Validated.public_derivation`](../IxCC/Aiur/Certificate.lean)
combines the checked trace and static certificate. Well-founded induction
chooses a nonzero active provider for each demanded message and constructs
its finite derivation. The provider-existence proof uses the nonzero field
image of a positive demand count below the characteristic; it does not
assume nonnegative provider multiplicities.

`Derivation.sound` is the generic induction principle for interpreting those
derivations in a row-local semantics. [BytecodeSound](../IxCC/Aiur/BytecodeSound.lean)
now discharges that rule using checked replay of the actual function bodies,
allowed advice, concrete gadget meanings, and the extracted witness heap.
`Trace.Validated.public_bytecode` produces a finite `BytecodeEvalW` execution
under the same static row certificate. `Static.CheckedTrace.public_bytecode`
uses the certificate produced by the combined checker. The [execution contract](aiur-semantics.md)
describes the precise treatment of calls, memory, hints, and continuations.
Identification with a verifier-accepted assignment, the honest-evaluator
refinement, bytecode/descriptor/key binding, primitive AIR conformance, and
source preservation remain explicit work. The cryptographic proof-system
boundary is not replaced by these checkers.

The upstream frontend handoff does not change that order: IxCC will
read addressed mode bytes and primitive identities, validate required typed
facts before erasure, and then recognize the admitted monadic DSL over
the erased source IR. Optional hints can guide checks but cannot authorize lowering or
establish trace acyclicity on their own.

## Validation

```sh
lake build IxCC.Aiur IxCCTests.Aiur.Proofs \
  IxCCTests.Aiur.Execution.Proofs IxCCTests.Fences.Aiur \
  IxCCTests.Aiur.Static.Proofs IxCCTests.Fences.AiurWire \
  IxCCTests.Fences.AiurExecution IxCCTests.Fences.AiurStatic \
  IxCC.Aiur.CounterAnalysis IxCCTests.Aiur.CounterAnalysis.Proofs \
  IxCCTests.Fences.AiurCounterAnalysis \
  IxCC.Aiur.AIR.Memory.Sound IxCC.Aiur.AIR.Memory.Lookup \
  IxCCTests.Fences.AiurMemoryAIR IxCC.Aiur.AIR.Rank.Sound \
  IxCC.Aiur.AIR.Rank.GraphProofs IxCCTests.Fences.AiurRankAIR \
  tests-aiur check-aiur
lake exe tests-aiur
lake exe check-aiur --root .
nix build .#checks.x86_64-linux.ixcc-aiur
```

The 25 runtime regressions cover shared demands, negative multiplicities,
inactive rows, exact outputs/channels, missing and unused providers,
conflicting memory, arbitrary pointer numbering, self-referential memory,
mixed counter/order/rank traces, and structural limits. The self-call and
mutual-call attacks pass message balance but have universal Lean proofs
that no static certificate can justify them. A mixed trace has a positive
finite-derivation proof, and a derived memory observation agrees with the
heap at pointer seven.

The inventory gate checks all pinned bytes and the complete vendor tree,
then rejects changed, missing, extra, and wrong-revision temporary copies.
Thirty-three new exact axiom assertions are registered in the required proof
aggregate. They use only the ordinary logical basis (`propext`,
`Classical.choice`, and `Quot.sound`), with no new axioms or native interface.
The existing required proof/runtime inventory remains required. The `aiur`
Nix check runs both executables through the shared CI artifact build.

The wire extension adds 308 runtime assertions, four complete frozen
preimages, seven fresh-process corruption rejections, and 33 further exact
axiom assertions. Component checking is still separate from proving its
AIR interpretation. The execution extension adds 276 assertions and 39
ordinary-logic axiom fences, including complete counter, ranked-mutual,
memory, gadget, and continuation examples. The static assignment extension
adds 116 runtime assertions and 39 exact fences for construction of public
executions from plain data, normalization/order lemmas, and universal
rejection of cyclic attacks. The analyzer proof adds 19 kernel regressions
and 48 ordinary-logic fences for universal body relations and short-cycle
exclusion. The memory AIR extension adds 52 runtime assertions, 16 kernel
regressions, and 46 ordinary-logic fences for local extraction and checked
heap construction. It compares five frozen Rust graphs in a fresh process
and rejects eight graph mutations. Rank AIR adds 71 runtime assertions,
22 kernel regressions, and 63 ordinary-logic fences. Its six complete Rust
function fixtures and full u16 table projection are checked in a fresh
process with 14 mutation rejections. The upstream evaluator handoff and IxVM
export/constraint dump, function/primitive and full keyed AIR extraction, and
source/DSL lowering remain next. No IxVM performance or production
proof-acceptance claim is made by these milestones.
