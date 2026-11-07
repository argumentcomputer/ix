# The Phase 1 ABI and readback matrix

The `phase1-abi` family of the [fixture corpora](../../../docs/corpus.md)
(phase 1 plan, MT.4; research §9.4.5): roots of arity 0–6 returning `Nat`,
`Bool` and `Abi.Tri` (three field-less constructors, read back as `#0`–`#2`),
from [`src/Abi.lean`](src/Abi.lean).

A root of arity `k` mixes its arguments position by position
(`a₀ ^^^ (a₁ >>> 1) ^^^ …`), so a wrong or truncated register changes the
result. Each position takes `0`, `1`, `2³² − 1`, `2⁶²` and `2⁶³ − 1` with the
other positions at distinct marks, all positions take `2⁶³ − 1`, and each
position takes `2⁶³`, `2⁶⁴ − 1` and `2⁶⁴` (status 3 from the wrapper). Every
case runs at every level and natively, where the driver checks the six
callee-saved registers and `rsp`, decodes the result in C, and dumps the
object area so that `Rt.readback` reads the same value in Lean.

Arity 6 (`nat6`, `bool6`, `tri6`) is declined with `rt: rt.params`: the
entry wrapper passes five arguments. The compiler's own readback type covers
`Nat` and `Bool` only (`Recheck.rootTy`); the suite reads `Tri` results with
the manifest's `ctors`.

Licence: Apache-2.0 OR MIT (original programs).
