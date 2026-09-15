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
Source lowering, universal counter-analyzer soundness, and extraction from
the keyed AIR remain subsequent work.

## Reference and module boundaries

[`vendor/aiur/upstream.json`](../vendor/aiur/upstream.json) pins eleven
unchanged Lean modules and both upstream licenses from argumentcomputer/ix
at `a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03`. They supply Goldilocks,
the source-to-bytecode IR vocabulary, layout and call-component definitions,
and the existing abstract counter/order lemmas. Their upstream toolchain is
Lean 4.33.1; they build unchanged with this repository's pinned Lean 4.33.0.

The `AiurReference` Lake library imports no native Aiur FFI. The upstream
bytecode evaluator currently imports its IO types from an FFI module, so it
is deferred until that pure interface is split. No evaluator shim or native
stub is substituted under an upstream module name.

The wire API uses the existing BLAKE3 interface for content roots. Its pure
codec proofs use ordinary logic; addressed wrappers retain the existing
native BLAKE3 axiom exception. The exact grammar, component-check scope,
fixtures, and ix exporter contract are in [aiur-wire.md](aiur-wire.md).

[`Compilatrix.Aiur`](../Compilatrix/Aiur.lean) exposes the new production API.
Tests, source-inventory checking, and axiom fences have separate module roots.

## Logical traces and checked facts

[`Trace`](../Compilatrix/Aiur/Trace.lean) distinguishes exact function
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

[`Trace.validate`](../Compilatrix/Aiur/Check.lean) checks activity, complete
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

[`Memory`](../Compilatrix/Aiur/Memory.lean) checks that active memory
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

## Static order, counters, and ranks

[`StaticCertificate`](../Compilatrix/Aiur/WellFounded.lean) records facts
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

This is still a theorem about supplied logical rows. Universal analyzer/body
soundness and deriving counter observations, rank limbs, component facts,
and field-step equalities from the keyed AIR remain work. General nonzero
steps, zero-step sub-orders, and broader output-counter recognition remain
extensions.

## Derivation endpoint and remaining assumptions

[`Trace.Validated.public_derivation`](../Compilatrix/Aiur/Certificate.lean)
combines the checked trace and static certificate. Well-founded induction
chooses a nonzero active provider for each demanded message and constructs
its finite derivation. The provider-existence proof uses the nonzero field
image of a positive demand count below the characteristic; it does not
assume nonnegative provider multiplicities.

`Derivation.sound` is the generic induction principle for interpreting those
derivations in a row-local semantics. [BytecodeSound](../Compilatrix/Aiur/BytecodeSound.lean)
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

The upstream frontend handoff does not change that order: Compilatrix will
read addressed mode bytes and primitive identities, validate required typed
facts before erasure, and then recognize the admitted monadic DSL over
IxIR₀. Optional hints can guide checks but cannot authorize lowering or
establish trace acyclicity on their own.

## Validation

```sh
lake build AiurReference Compilatrix.Aiur CompilatrixTests.Aiur.Proofs \
  CompilatrixTests.Aiur.Execution.Proofs CompilatrixTests.Fences.Aiur \
  CompilatrixTests.Aiur.Static.Proofs CompilatrixTests.Fences.AiurWire \
  CompilatrixTests.Fences.AiurExecution CompilatrixTests.Fences.AiurStatic tests-aiur check-aiur
lake exe tests-aiur
lake exe check-aiur --root .
nix build .#checks.x86_64-linux.aiur
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
rejection of cyclic attacks. Universal counter-analyzer soundness, the
upstream evaluator handoff and IxVM export/constraint dump, keyed AIR
extraction, and source/DSL lowering remain next. No IxVM performance or
production proof-acceptance claim is made by these milestones.
