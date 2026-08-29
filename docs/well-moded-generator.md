# Seeded well-moded IxIR₀ generation

Last reviewed 2026-08-28.

`Compilatrix/IxIR1/WellModedGen.lean` is the deterministic property corpus for
the IxIR₀ → IxIR₁ lowering boundary. It generates closed expressions against
the hand-written `IxIR0.Examples.declList`; there is no ambient randomness or
external property-testing dependency.

The default run is frozen as:

| Field | Value |
| --- | ---: |
| seed | `0x243f6a8885a308d3` |
| cases | 280 |
| positive differential cases | 180 |
| expected static rejections | 100 |
| schema kinds | 28/28 |
| final PRNG state | `1151165198556225096` |
| corpus fingerprint | `6965325113816880105` |

`Tests.lean` checks that summary exactly, then executes every property. A
generator edit therefore needs an explicit fingerprint review, while a
lowerer/evaluator edit is checked against the unchanged corpus.

## Positive fragment

Eighteen schemas generate programs inside the current mode/ownership
contract. They vary constructor-form and literal naturals, recursion through
`Nat.add`, scalar extern calls, repeated and dead shared bindings, shared
projection, list length/append, captured lambdas, dynamic and under-applied
paps, unique constructor trees, exact-once linear bindings, dead affine
bindings, mixed affine/many known calls, and erased application/projection.

Each positive case calls `IxIR1.Lower.diffExpr`, which:

1. lowers the complete example declaration environment and generated main;
2. evaluates the source and target with their independent interpreters;
3. compares first-order readback trees (including constructor address/tag and
   pap shape); and
4. releases the target result according to its runtime world and requires zero
   live nodes.

Thus a passing generated case checks value/error agreement and successful-run
leak freedom, not merely that lowering returned `ok`.

## Mode-adversarial boundary

Ten companion schemas deliberately cross exactly one current policy edge:
freeze-needed unique→shared flow, shared→unique dereliction, duplicate unique
use, dead linear use, projection from a unique value, non-`many` lambda and
known-function paps, a shared declaration result at unique demand, capture of a
unique value by a shared closure, and a unique major supplied to the current
all-shared recursor ABI. They must fail through `lowersErr` with the exact
pinned diagnostic; one arbitrary lowering error cannot satisfy another case.

This negative stream is not counted as well-moded source. It keeps the
generator mode-adversarial and makes the accepted-fragment boundary executable
alongside the positive stream.

## Replay and shrinking

Each generated `Case` carries:

```lean
{ seed : UInt64, index : Nat, state : UInt64 }
```

`WellModedGen.replay token` regenerates the case directly from that token, and
the default corpus checks this equality for every case. A failure report prints
the token, schema payload, original expression, and minimized expression.

Shrinking operates on the schema rather than arbitrary expression subtrees.
Natural payloads move toward zero, lists move toward empty/short/zero-valued
forms, and constructor-form naturals move toward literals. Every candidate
retains the same schema class and expected world or exact diagnostic; the
corpus checks that expectation-preservation property before executing the
case. `minimizeFailure` repeatedly selects a still-failing candidate under a
fixed 128-step bound, producing a deterministic fixture suitable for copying
into a focused regression.

## Scope

This is executable hardening, not a theorem that the templates are well typed
or that all accepted IxIR₀ programs are covered. It currently fixes the
declaration environment and generates mains only. Arbitrary declaration
graphs, recursive rule generation, unique destructuring, one-shot-closure and
unique-capture support, freeze insertion, and malformed/open-term fuzzing
remain separate work. The schema design intentionally follows the lowerer's
present accepted fragment so those future features enter as explicit new kinds
rather than silently changing old replay tokens. The synthetic
under-applied-`recSelf` boundary is checked directly in `Lower.lean`, because
`recSelf` exists only inside a generated recursor-rule environment and cannot
be expressed by a main-only template.
