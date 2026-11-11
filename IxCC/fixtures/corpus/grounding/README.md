# The grounding corpus

The `grounding` family of the [fixture corpora](../../../docs/corpus.md): the subjects of the
grounding suite (`tests-grounding`, [certification design](../../../docs/certification-design.md#the-grounding-library))
that no other family holds, in the role-bound envelope (`0xE5`) that `ix compile` writes by
default. It is a required family: `corpus check` verifies it and `tests-corpus` runs its roots at
every level, as for the other families.

| Closure | Source | Root | Value |
| --- | --- | --- | --- |
| `decide` | [`src/Decide.lean`](src/Decide.lean) | `Grounding.decideFib10 : Bool := decide (K1.fib 10 = 55)` | `true` |

`decide (fib 10 = 55)` is the shape of an evaluation axiom: its run fires `Decidable.casesOn` on a
major that `Nat.decEq` built at another proposition, passes a proof field it never builds, and
reads back `Bool.true`. `K1.fib` is verbatim from `benchmarks/fixtures/fib/Fib.lean`. The suite's
`fib` subject is the role-bound `fib` closure the other families hold.

Licence: Apache-2.0 OR MIT (an original program).

## Regenerating

With this repository's `ix` built (`lake build ix` at the repository root), the manifest's
`producer` fields set to that `ix`, and a directory `FAKE` holding a `lake` stand-in that answers
`lake env printenv LEAN_PATH` with `lean --print-libdir` (the source imports only `Init`), from
`IxCC/`:

```sh
lake exe corpus rebuild fixtures/corpus/grounding/corpus.json \
  --ix ../.lake/build/bin/ix --ix-path FAKE --work WORK
```

The family is registered (`IxCCTests.Corpus.families`), so a refreeze that regenerates every
registered family regenerates it too.
