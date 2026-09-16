# Aiur rank AIR extraction

[`Rank.ordered_message_of_balance`](../Compilatrix/Aiur/AIR/Rank/Sound.lean)
proves that an ordered call's provider has a strictly larger natural rank.
Its premises retain normalized scalar-u16 lookup balance, the demand-count
bound, the fixed range-table rows, all nine limb demands, and equality of the
complete physical call and provider messages. Rank increase is a conclusion,
not a caller-supplied premise. No field primality or no-zero-divisors axiom
is needed.

The expression fragments follow `crates/aiur/src/constraints.rs` and
`gadgets/bytes2.rs` at ix
`a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03`. Complete small function-circuit
graphs are compared with the actual Rust builder; this is not yet a general
function AIR compiler or extraction of a verifier-accepted IxVM assignment.

## Range and packing

Each rank or gap has three canonical field limbs. The natural value is
`low + middle * 65536 + high * 4294967296`. The corresponding field expression
uses the same order and constants. If all limbs are below 65536, the natural
value is below `2^48`, and the field expression's canonical value is exactly
that natural value.

The physical scalar-u16 channel is 15. At fixed row `i < 65536`, the first
two preprocessed columns are `i / 256` and `i % 256`. The range-table pull
uses main multiplicity column seven with weight `-m` and arguments
`[15, column0 * 256 + column1]`. It therefore provides exactly `[15, i]`.
This differs from physical channel 11's two independent byte arguments.

[`Rank.rangeProvided_iff`](../Compilatrix/Aiur/AIR/Rank/Range.lean) proves that an exact
scalar message has a fixed-table provider if and only if its value is below
65536. The proof covers every table index, not only sampled values.
`RangeBalanced` counts exact requested messages and equates their field count
to the sum of matching table multiplicities. A positive demand count below
the characteristic cannot have a zero provider sum, so a matching provider
exists. Multiplicities may be negative or zero. Duplicate demands count
separately; every fixed-table provider retains a bounded row index.

The expression evaluator now supports current preprocessed columns. Missing
main, next, or preprocessed columns return `none`; main columns cannot stand
in for fixed columns. This model does not parse an assignment or bind a
supplied matrix to a committed preprocessing key.

## Ordered and boundary calls

An ordered call requests rank `parent + 1 + gap`. Both operands are below
`2^48`, so the sum is below `2^49`, below the Goldilocks characteristic.
Equality with the provider's packed rank yields the natural equality
`child = parent + 1 + gap` and hence `parent < child`. Self edges, two-cycles,
and an ordered successor of the maximum rank are impossible.

The other modes retain their separate meanings. A call across components
can bind a ranked callee through one auxiliary without a positive gap; that
callee's rank may be smaller than the caller's. Static component order must
justify that edge. A call to an unranked callee requests zero rank. The public
root's zero rank binds to natural zero when the provider is range-checked.

Selected lookup lemmas cover branchless raw arguments and selector-gated
arguments, complete inputs and outputs, signed provider weights, and the
trailing rank field. They assume the selected selector evaluates to one;
deriving selector Booleanity and exclusivity from the full polynomial system
remains separate work.

## Preserve rank while matching providers

The physical function message is
`[0, function] ++ inputs ++ outputs ++ [rank]`. The theorem deliberately
matches this complete message. Two providers with equal function, inputs,
and outputs but different ranks have different physical messages.

The existing logical `Message.function` omits this extra rank field. Equality
of those erased messages is insufficient to apply the rank theorem to every
logical provider. The full AIR adapter must preserve physical rank identity
through provider selection and prove its projection to the bytecode semantics.
This package does not silently infer that correspondence or construct a whole
static trace certificate from erased messages.

[`Rank.validate`](../Compilatrix/Aiur/AIR/Rank/Check.lean) accepts one supplied
ordered edge: exactly three parent limbs, three gap limbs, and three child
limbs. It checks their ranges and the physical rank equality, returning
`Checked edge`. Its soundness module derives the exact natural equation,
strict increase, child bound, and the existing `Static.Advances` obligation
for a ranked component. No caller-written ordering proof is required. This
fixed-size API has no binary parser, body-replay validation, or key identity.

## Independent conformance and validation

The [optional Rust exporter](../tools/aiur-rank-reference/README.md) calls the
actual pinned constraint builder after its admission checks. Six examples
cover legacy, ordered, bound, zero, unranked-caller, and gated modes, exporting
both complete function circuits in each example. The fixed-table artifact
contains all 65,536 pairs projected from the actual `Bytes2` preprocessing;
the scalar-range lookup is exported from that same implementation.

Required `check-aiur` compares every graph field and all 131,072 projection
bytes, repeats the Lean export in a fresh process, and rejects 14 mutations.
The other nine preprocessed columns, other gadget lookups, grouped circuits,
arbitrary function bodies, full compiled keys, and universal Rust compiler
correctness are outside these fixtures. Expected data are never regenerated
from the Lean model.

```sh
lake build Compilatrix.Aiur.AIR.Rank.Sound Compilatrix.Aiur.AIR.Rank.GraphProofs \
  CompilatrixTests.Aiur.RankAIR.Proofs CompilatrixTests.Fences.AiurRankAIR \
  tests-aiur check-aiur
lake exe tests-aiur
lake exe check-aiur --root .
lake exe check-aiur --dump-rank-air plans/aiur-rank-air
nix build .#checks.x86_64-linux.aiur .#checks.x86_64-linux.proofs
```

The suite adds 71 runtime assertions, 22 public kernel regressions, and 63
exact ordinary-logic axiom fences, preserving all 2310 preceding assertions.
The combined Aiur runtime suite has 848 assertions. The five rank extraction
proof modules remain outside the production API. Full lookup-budget and
assignment/key bindings, selector extraction, remaining function/primitive
AIR, the honest evaluator relation, and source/DSL lowering remain open.
