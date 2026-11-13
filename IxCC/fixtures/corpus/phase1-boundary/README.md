# The Phase 1 boundary corpus

The `phase1-boundary` family of the [fixture corpora](../../../docs/corpus.md)
(phase 1 plan, MT.3; research §9.4.1): the `2⁶³` edge of every `Nat`
primitive, argument position and operand shape, and the layout limits as
Lean sources reach them. [`corpus.json`](corpus.json) records every case's
expectation: the value Lean 4.34's interpreter printed, status 3 where an
argument or the result has no word, and a reviewed `fail: natOverflow` where
an intermediate value does not fit (marked `spurious` where nothing the
source computes reaches `2⁶³`).

| Closure | Source | Roots | Contents |
| --- | --- | ---: | --- |
| `boundary` | [`src/Boundary.lean`](src/Boundary.lean) | 59 | one root per primitive (`+ - * / % ^ gcd &&& \|\|\| ^^^ <<< >>>`, `Nat.beq`/`ble`/`blt`, `decide` of `= ≤ < >`, `!=`, fused `if`, `min`, `max`, `pred`, `succ`), each with a literal operand on the left and on the right; literals of at least `2⁶³` in live code, a dead branch and a `match` arm; intermediate values past `2⁶³` |
| `fields254`, `fields255` | [`src/Fields254.lean`](src/Fields254.lean), [`src/Fields255.lean`](src/Fields255.lean) | 1 + 1 | a structure of 254 `Nat` fields (the most a header counts), allocated and read; 255 fields is declined at `ingress: decode` (`mk255`, which the root reaches, is past the depth budget) |
| `tags16`, `tags17`, `tags125`, `tags126` | [`src/Limits.lean`](src/Limits.lean) | 4 | inductives of 16, 17, 125 and 126 constructors, the last with a field |

Every case also runs with each argument at `2⁶³`, `2⁶⁴ − 1` (the entry
wrapper's check, also on the typed x86 machine and ByteEval) and `2⁶⁴`
(natively), and must return status 3.

## Findings (2026-10-01)

- No miscompile and no level disagreement.
- **Spurious status 3** (a completeness gap of `Rt`, recorded as required so
  a fix shows up): every `<` at `a = 2⁶³ − 1`, because Lean defines
  `Nat.decLt a b` as `Nat.decLe (a + 1) b` and `Nat.blt a b` as
  `Nat.ble (a + 1) b` — `blt`, `decLt` and the fused `ltBranch` at
  `[2⁶³ − 1, b]` for every `b`, `decGt` at `[a, 2⁶³ − 1]`, and `ltK` at
  `2⁶³ − 1`. `≤`, `=`, `==`, `!=`, `min` and `max` have none. **Fixed
  2026-11-13**: the shrink walk turns `Nat.ble (a + 1) b` into `natBlt a b`
  (`Anf.Walk.succBle`), so these 13 cases give Lean's value at every level
  and natively, and `corpus.json` no longer marks them `fail`. `n < 2⁶⁴` still
  fails, on its literal operand.
- **Intermediate status 3** (allowed by the specification): `(a + b) - c`,
  `a * b / c`, `(a <<< b) >>> b`, `a ^ b % m`, `(a + 1).pred`, and
  `n + 1 == 0` guarding a dead literal, each where the intermediate reaches
  `2⁶³`; a literal operand of `2⁶³` (`2⁶³ - n`) or `2⁶⁴` (`n < 2⁶⁴`) fails on
  every argument.
- A literal of `2⁶⁴` in a branch no argument takes does not fail; one of
  `2¹²⁸` in a `match` arm fails exactly when the arm runs.
- Lean's runtime refuses `Nat.pow` and `Nat.shiftLeft` exponents of `2³²` or
  more (`INTERNAL PANIC: … exponent is too big`), where the compiled code
  answers (`0 ^ (2⁶³ − 1) = 0`, `1 ^ 2³² = 1`); the source-level evaluators
  run on the same runtime (and `Src.PrimOp.eval2` computes `a <<< b` as
  `a * 2 ^ b`, so even `0 <<< 2³²` aborts them). These cases are
  `lean_fails`, with hand-computed constants.
- **Layout limits from source:** IxCC's expression-depth budget (256, a
  `share` node a leaf), on the records a root reaches, declines an inductive of
  126 constructors at `ingress: decode` (its `casesOn`, which the `match`
  reaches, is 257 deep; 125's is 255),
  so tags above 124, `Rt.lower`'s `rt.layout` (a tag above `0x7EFF`) and the
  header's full tag are not reachable from Lean sources. Before that, the four-arm wildcard `match` of `tags17`
  keeps its alternatives as closures (`fir: fir.closures`) on 17 or more
  constructors; 16 compile (`tags16`). Lean's own compiler refuses a
  constructor with fields at tag 249 ("tag … is too big, this is a
  limitation of the current runtime").

Licence: Apache-2.0 OR MIT (original programs).

## The field limit (2026-11-12)

A structure of 254 fields is the widest a cell header counts, and it compiles
from source (`fields254`); one of 255 fields is declined at `ingress: decode`
(`fields255`), before `Rt.lower`'s `rt.layout` (`tests-rt` keeps the 254-field
cell, accepted, and the 255-field refusal on synthetic programs). The limit
that declines it is IxCC's expression-depth budget
(`IxCC.Ixon.V3.exprDepthLimit` = 256, a `share` node a leaf) on a record the
root reaches: the definition `mk255`, whose value applies the
constructor to 255 arguments, is 257 deep (`mk254` is 256, the block 255).

Since `ix compile` selects a structure's whole logical unit, the closure of a
program that merely *uses* a structure also holds its recursor, `casesOn`,
`noConfusion`, `mk.inj`, `mk.injEq` and `sizeOf` lemmas. At 254 fields they
are far past the budget (measured before the role-bound refreeze, with a
`share` node a leaf: `mk.injEq` 1,277 deep, `5n + 7` for `n` fields;
`mk.inj` 1,021; `noConfusionType` and `_sizeOf_1` 769; `mk.noConfusion` 771;
`casesOn` 514; `rec` 511; `recOn` 510; `mk.sizeOf_spec` 512; `noConfusion`
519). Ingress reads only the records the root reaches (`Src.Ingress.reach`),
and the root reaches none of them, so they do not refuse it. Between the
role-bound refreeze and that change (2026-11-11 to 2026-11-12) ingress read
every record, and the family held `fields49` and `fields50`, the latter
declined because of its unreached `mk.injEq` (257 deep).

`Fields254.lean` and `Fields255.lean` turn `genInjectivity` off, so Lean
generates no `mk.inj` and `mk.injEq`: at 254 fields `ix compile` spent 714 of
715 seconds of each compile on them (in its certified compile; two compiles per
fixture), against 2.5 seconds for the whole compile without them (2026-11-12).
The rest of the unit stays, past the budget and unreached: in `fields254`'s
closure, with shares expanded, `noConfusionType` is 772 deep, `mk.noConfusion`
771, `_sizeOf_1` 770, `mk.sizeOf_spec` 768, `noConfusion` 521, `casesOn` 514,
`recOn` 513 and `rec` 512, beside `mk254` (256) and the block (255), which the
root reaches.

Every record, reached or not, is still decoded by the kernel's canonical
decoder, bounded by the depth the kernel walks (2,560 with shares expanded,
`IxCC.Ixon.V3.kernelDepthLimit`; the deepest record at 254 fields is
`noConfusionType`, 772, and 1,529 with `mk.injEq`), and accepted by the
certified kernel.
