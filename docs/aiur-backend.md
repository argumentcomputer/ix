# Aiur backend foundation and wire boundary

The initial Aiur implementation provides a pinned pure target vocabulary and
a checked logical-trace interface. It proves that active, balanced lookup
demands have providers and that a static row certificate yields finite rooted
derivations. The [canonical bytecode boundary](aiur-wire.md) now preserves
the complete pinned toplevel, checks its content root, and invokes the
upstream component checker behind resource guards. This is the foundation
for the Ixon/DSL → AiurV2 backend; witness-heap bytecode evaluation, source
lowering, and extraction from the keyed AIR remain subsequent work.

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

This is a proposition about row facts, not yet a checker-to-AIR theorem for
the upstream bytecode certificate. Counter positions, rank-limb decoding,
component assignments, and field-step equalities must eventually be derived
from the exact bytecode, layout, and satisfying assignment. General nonzero
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
derivations in a row-local semantics. This implementation does not discharge
that local semantic rule for Aiur bytecode or identify these logical rows
with a verifier-accepted assignment. AIR extraction, witness-heap bytecode
evaluation, bytecode/descriptor/key binding, primitive semantics, and the
source-preservation/backward-soundness results remain explicit work. The
cryptographic proof-system boundary is not replaced by this trace checker.

The upstream frontend handoff does not change that order: Compilatrix will
read addressed mode bytes and primitive identities, validate required typed
facts before erasure, and then recognize the admitted monadic DSL over
IxIR₀. Optional hints can guide checks but cannot authorize lowering or
establish trace acyclicity on their own.

## Validation

```sh
lake build AiurReference Compilatrix.Aiur CompilatrixTests.Aiur.Proofs \
  CompilatrixTests.Fences.Aiur CompilatrixTests.Fences.AiurWire tests-aiur check-aiur
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
AIR interpretation. The production IxVM exporter/constraint dump and
witness-heap evaluator remain next, followed by extraction from the keyed
AIR and source/DSL lowering. No IxVM performance or production
proof-acceptance claim is made by this foundation.
