# The grounding corpus

The `grounding` family of the [fixture corpora](../../../docs/corpus.md): the subjects of the
grounding suite (`tests-grounding`, [certification design](../../../docs/certification-design.md#the-grounding-library))
that no other family holds, in the role-bound envelope (`0xE5`) that `ix compile` writes by
default. It is a required family: `corpus check` verifies it and `tests-corpus` runs its roots at
every level, as for the other families.

| Closure | Source | Root | Value |
| --- | --- | --- | --- |
| `decide` | [`src/Decide.lean`](src/Decide.lean) | `Grounding.decideFib10 : Bool := decide (K1.fib 10 = 55)` | `true` |
| `words` | [`src/Words.lean`](src/Words.lean) | seven roots `Grounding.Words.*` (`add64`, `mulAdd32`, `mix8`, `neg16`, `divMod32`, `convert`, `shift64`), each `Nat → … → Nat` | 30 cases, the interpreter's values |

`decide (fib 10 = 55)` is the shape of an evaluation axiom: its run fires `Decidable.casesOn` on a
major that `Nat.decEq` built at another proposition, passes a proof field it never builds, and
reads back `Bool.true`. `K1.fib` is verbatim from `benchmarks/fixtures/fib/Fib.lean`. The suite's
`fib` subject is the role-bound `fib` closure the other families hold.

`words` is fixed-width word arithmetic only (stage W1 of
[DR2](../../../docs/data-and-roots-design.md#dr2-fixed-width-integers-and-int)): the operations of
`UInt8` to `UInt64` that SrcEval runs as primitives (rule F6w), with no decision, no string and no
`let`. Its closure holds 30 word entries, which between them reach every primitive operation kind at
some width (`add`, `sub`, `mul`, `div`, `mod`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`,
`complement`, `neg`, `ofNat` through `Nat.toUIntN` and literals, `toNat`, and conversions that narrow
and widen). It is the subject of the grounding's word case: until that case is proved, the grounding
check refuses it by its conjunct `noWord` alone (`tests-grounding` asserts every other conjunct of the
widest family true on it). Three cases compute a `UInt64` at or above `2^63` (`add64 (2^63 − 1) 1`,
`shift64 1 63`, `shift64 2^62 2`), which has no tagged word: they are registered with the
`natOverflow` allowance, and the word levels and native code end them with status 3.

Licence: Apache-2.0 OR MIT (an original program).

## Regenerating

[`tools/regenerate.sh`](../../../tools/regenerate.sh) regenerates it with the rest of the
committed fixtures ([Refreezing](../../../docs/corpus.md#refreezing)): it takes every
`corpus.json` under `fixtures/`, so this family is never skipped. For this family alone: with
this repository's `ix` built (`lake build ix` at the repository root, in its dev shell; the
manifest records its version) and a directory `FAKE` holding the `lake` stand-in `regenerate.sh`
writes (any stand-in that answers `lake env printenv LEAN_PATH` will do: the source imports only
`Init`), from `IxCC/`:

```sh
lake exe corpus rebuild fixtures/corpus/grounding/corpus.json \
  --ix ../.lake/build/bin/ix --ix-path FAKE --work WORK
```

The rebuild writes the manifest in its canonical form, the producer record included.
