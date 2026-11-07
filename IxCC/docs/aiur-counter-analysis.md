# Aiur unit-counter analyzer soundness

[`CounterAnalysis.find_body`](../IxCC/Aiur/CounterAnalysis/Sound.lean)
proves universal soundness of the pinned `UnitCounter.find?` against the
actual [`OracleEval.Body`](aiur-semantics.md) relation. Given the exact
function at its toplevel index and a returned candidate, every constrained
self-call demand in every successful body has the inferred field step.
The theorem quantifies over all inputs, outputs, limits, reply tapes,
demands, and advice observations. It requires no honest-hint premise or
caller-supplied affine invariant.

The unchanged analyzer is from argumentcomputer/ix at
`a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03`. These are proofs about its
existing implementation and the existing replay machine; neither is
replaced or extended.

## Public contract

For a demanded message `function self childInputs childOutputs`,
`find_body` proves that the selected parent and child observations both
exist and obey this relation:

| Candidate mode | Proved relation |
| --- | --- |
| Input column `c`, step `s` | `childInputs[c] = inputs[c] + s` |
| Output column `c`, step `s` | `outputs[c] = childOutputs[c] + s` |

`find_spec` proves that an actual search result passed the pinned checker
at depth 256, has step `+1` or `-1`, and selects an existing input column
in input mode. `check_body` exposes the more general checker theorem for
any accepted candidate, depth, and field step, with the input-column bound
as an explicit premise. `find_runFunction` covers concrete successful replay.

`find_body_normalized` composes the raw relation with the existing
[counter normalization](aiur-static.md). All four mode/direction choices
give `child_counter = parent_counter + 1`, including field wraparound.
`find_body_counter_ne` excludes a self-call with an unchanged normalized
counter. `find_body_no_short_cycle` excludes a nonempty chain of such body
executions that returns to the same inputs and outputs in fewer than the
Goldilocks characteristic number of steps.

An output counter's selected observation is promised on a demanded edge.
A leaf with no self-call may return fewer outputs than the selected column.
The kernel regressions include that accepted case and its successful replay.
The [static assignment checker](aiur-static.md) separately requires selected
columns to exist on active nonzero providers and continues to check every
provider dependency. Its executable behavior is unchanged.

## Proof structure

The proof-only aggregate is
[`IxCC.Aiur.CounterAnalysis`](../IxCC/Aiur/CounterAnalysis.lean).
It remains outside the production API's import closure.

1. Affine expressions denote concrete registers, with an existing register
   required for every variable base. Exact pinned Goldilocks arithmetic
   justifies constant addition, subtraction, multiplication, and identity
   multiplication without a field-law or primality axiom.
2. Every successful opcode in the actual replay has its proved register
   and constrained-call effect. Hint, memory, gadget, and other opaque
   outputs contribute values and arities but no invented affine equation.
3. The analyzer's known-register invariant survives every accepted step.
   Input counters track every self-call. Output counters retain the selected
   recursive result's register marker and reject a second self-call along
   a path, as the pinned checker requires.
4. An induction on the actual machine execution follows the chosen branch.
   Acceptance supplies checks for every branch and any fallback, including
   duplicate labels. Returns establish the edge relation. Yield and shared
   continuation controls are rejected by the pinned analyzer.
5. Invariants over the actual search loops establish successful checking,
   unit direction, and the input-column bound. The proof-local decomposition
   of those loops is connected to the pinned definition by kernel-checked
   definitional equality.

## Validation and remaining boundary

```sh
lake build IxCC.Aiur.CounterAnalysis \
  IxCCTests.Aiur.CounterAnalysis.Proofs \
  IxCCTests.Fences.AiurCounterAnalysis
lake build IxCCTests.Proofs
lake exe check-build-graph
nix build .#checks.x86_64-linux.proofs
```

Nineteen public kernel regressions cover arbitrary-input consequences in
all four directions, a second input column and multiple self-calls,
constant arithmetic, identity multiplication, unknown hint/memory outputs,
the second recursive output marker, a short leaf result, and rejected
unknown/nonlinear/missing values, repeated output calls, bad branches,
yield, and shared continuations. Forty-eight exact axiom assertions use
only the existing logical basis and preserve all 2216 prior assertions.
The 725 Aiur runtime assertions and all existing runtime-failure gates
remain required. No native decision procedure or new native interface is
introduced by this proof layer.

The theorem connects the analyzer to the local bytecode model. Keyed AIR
extraction must still identify satisfying rows with these body executions
and bind counter columns, rank limbs, component facts, and lookup budgets.
Production IxVM export/constraint artifacts, primitive AIR conformance,
honest-evaluator and allocator refinement, source/descriptor/key bindings,
and Ixon/DSL lowering remain separate work. This milestone establishes no
production proof-acceptance or target-cost claim.
