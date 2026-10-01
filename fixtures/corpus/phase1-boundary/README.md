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
| `fields254`, `fields255` | [`src/Limits.lean`](src/Limits.lean) | 1 + 1 | a structure of 254 `Nat` fields, allocated and read; 255 fields is declined at `ingress: decode` |
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
  `2⁶³ − 1`. `≤`, `=`, `==`, `!=`, `min` and `max` have none.
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
- **Layout limits from source:** the Ixon v3 decoder's expression-depth
  budget (256) declines a structure of 255 fields and an inductive of 126
  constructors at `ingress: decode`, so `Rt.lower`'s `rt.layout` (above 254
  fields, or a tag above `0x7EFF`) and tags above 255 are not reachable from
  Lean sources. Before that, the four-arm wildcard `match` of `tags17`
  keeps its alternatives as closures (`fir: fir.closures`) on 17 or more
  constructors; 16 compile (`tags16`). Lean's own compiler refuses a
  constructor with fields at tag 249 ("tag … is too big, this is a
  limitation of the current runtime").

Licence: Apache-2.0 OR MIT (original programs).
