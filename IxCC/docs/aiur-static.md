# Checked Aiur static assignments

*Part of the [legacy Aiur bytecode model](aiur-backend.md#status-in-the-plan), which
neither Aiur route of the plan uses; frozen, to be retired or re-pinned.*

[`Static.validate`](../IxCC/Aiur/Static/Check.lean) accepts a pinned
bytecode toplevel, an advice policy, a logical trace, one natural rank per
row, and local replay tapes. Successful validation returns a
`Static.CheckedTrace`. Its `public_bytecode` theorem proves a finite
[`BytecodeEvalW`](aiur-semantics.md) execution for each public function claim
against the extracted witness heap. The caller supplies ordinary data;
the checker constructs the static certificate and its proof.

This endpoint checks dependencies in a supplied logical trace. It does not
derive that trace from a verifier-accepted AIR assignment. In particular,
the upstream counter analyzer chooses a column and direction, while this
checker verifies every relevant counter equation on the actual rows.
The [universal analyzer theorem](aiur-counter-analysis.md) now proves those
equations for every successful local body. Extraction from the keyed AIR
remains a separate obligation.

## Program binding

`Static.prepare` first checks the function-count bound and invokes the
[bounded component checker](aiur-wire.md). Its `Program` result retains
the original limits, component acceptance, function bound, and exact
`inferPlans` result. Empty component metadata selects ranked fallback.

For each unranked constrained function with a syntactic self-call,
`inferPlans` invokes the pinned `UnitCounter.find?` once more. The existing
preflight bounds that analysis. Nonrecursive and ranked functions need no
counter analysis. Only steps `+1` and `-1` are admitted. An active nonzero
function provider must name an existing constrained function, match its
input arity, have an in-range component order, and contain any selected
counter column. Missing columns never acquire meaning from a default value.

`Wire.Ingress.validateTrace` reuses an addressed ingress's component evidence
and limits. Its result is indexed by that ingress's exact decoded toplevel.
Trace limits cannot replace the checked program limits. This adapter
inherits the existing native BLAKE3 axiom through the addressed evidence;
the unaddressed static and execution endpoints use only ordinary logic.

## Orders and counter directions

The pinned component checker permits ranked and unranked functions to share
an order number. The assignment therefore refines the original order:

| Provider kind | Assigned order |
| --- | --- |
| Zero multiplicity | `0` |
| Unranked function in component order `k` | `2 * k + 1` |
| Ranked function in component order `k` | `2 * k + 2` |
| Memory or gadget leaf | `2 * number_of_functions + 1` |

Even orders use ranks; odd orders use counters. This preserves every strict
component-order increase and gives memory/gadget leaves an order above all
admitted functions. Zero-weight parents may still demand messages, so they
receive order zero. `Trace.Requires` selects only nonzero providers as
children. Inactive rows remain subject to the independent activity check.

Counter observations follow the analyzer's input or output column:

| Analyzer mode and step | Normalized field counter |
| --- | --- |
| Input, `+1` | Observed input |
| Input, `-1` | Negated observed input |
| Output, `+1` | Negated observed output |
| Output, `-1` | Observed output |

Input steps describe `child = parent + step`; output steps describe
`parent = child + step`. The normalization lemmas prove that each case
gives `child_counter = parent_counter + 1`, including Goldilocks wraparound.
They use the pinned field representation, without a new field-law or
primality axiom. The universal analyzer theorem composes these lemmas with
the inferred body relation. This endpoint still checks actual edge equations
as part of validating the supplied logical trace.

## Dependency and replay checks

`checkAssignment` enumerates every `Trace.Requires child parent` pair,
including every matching provider when messages have duplicate providers.
Each pair must either increase order or stay at the same order and increase
the natural rank, or advance the normalized counter by exactly one,
according to that order's mode. Negative field multiplicities are allowed.
Ranks are bounded natural numbers supplied for every row; there is no
rank-limb decoder or implicit correspondence with physical AIR columns.

Successful checks construct the existing `StaticCertificate`. Together
with the validated trace's characteristic bound, it proves well-foundedness
and excludes short dependency cycles. The combined endpoint also requires
activity, exact-message balance, memory coherence, and successful replay of
each active nonzero provider's actual bytecode body. Its result retains all
four proof objects: checked program, validated trace, assignment, and rows.

Default assignment limits are 65,536 row pairs and ranks at most `2^48 - 1`.
Structural trace limits are checked before pair enumeration. Component,
trace, assignment, and replay budgets are separate admission policies;
they are not execution-time proofs or STARK trace-height limits. No binary
trace, rank, or replay-tape parser is introduced.

## Validation and remaining work

```sh
lake build IxCC.Aiur IxCCTests.Aiur.Static.Proofs \
  IxCCTests.Fences.AiurStatic tests-aiur
lake exe tests-aiur
nix build .#checks.x86_64-linux.ixcc-aiur
```

The suite adds 116 runtime assertions over all four counter directions,
field wraparound, ranked fallback and mutual recursion, mixed ranked/counter
orders, interleaved rows, duplicate providers, zero-weight parents, memory
and gadget leaves, addressed ingress, malformed bindings, limits, incorrect
replays, and balanced cyclic attacks. Kernel examples construct public
executions through the combined checker using reduction and ordinary data.
Universal rejection theorems exclude the self-loop and mutual-loop attacks
for every program, rank array, replay tape, advice policy, and limit setting.
Of the 39 new exact axiom fences, 38 use only the existing logical basis;
the ingress adapter retains the existing native BLAKE3 exception.

The [analyzer/body proof](aiur-counter-analysis.md) is now complete for the
local model. Remaining backend work includes production IxVM bytecode
export and constraint artifacts, extraction of
local and static row facts from the keyed AIR, primitive conformance,
honest-evaluator/allocator refinement, artifact/source/key bindings, and
Ixon/DSL lowering. Checked logical-trace execution does not establish
production proof acceptance or a target cost measurement.
