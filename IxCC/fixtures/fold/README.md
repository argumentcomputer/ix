# Literal folding's front-door input

The input of the fold guard's reproducers (`tests-exe`'s fold-guard part,
`IxCCTests/Exe/FoldGuard.lean`). `Fold.lean` writes twenty-one roots, each `fun x => E + x` with
`E` a primitive applied to literals, for the shrink walk's literal folding (`Anf.Walk.foldable`:
every operand below `2^1024`; `a ^ b` only when `b = 0`, or `b ≤ 1024` and `a < 2^(1024 / b)`;
`a <<< b` only when `b ≤ 1024` and `a < 2^(1024 − b)`):

- both sides of the bound: `2 ^ 512 % 7` and `2 ^ 513 % 7`, `1 ^ 1024` and `1 ^ 1025`,
  `(1 <<< 1023) % 7` and `(1 <<< 1024) % 7`, and `2 ^ 100 % 7` (a wide intermediate a later fold
  reduces);
- exponents at and past `2^32 − 1`, where the runtime's `Nat.pow` aborts the process whatever the
  base: `0`, `1` and `2` to `2^32 − 1` and `2^32`, `1 ^ 2^64`, and `0`, `1`, `2` shifted by
  `2^32 − 1` or `2^32`;
- thirty-two chained squarings of `2^62`, then `% 7` (`mulChain32`);
- a literal of the closure's own text inside and past the bound: `2^1000 % 7` and `2^1100 % 7`,
  written out.

Before the bound (2026-11-13, at the commit before it), `ixcc compile` aborted on every exponent
past `2^32 − 1` (`INTERNAL PANIC: Nat.pow exponent is too big`, exit 1, no certificate), built a
512 MiB literal for `2 ^ (2^32 − 1)`, and ran `mulChain32` for 526 s to a 24 GiB memory cap,
where it was killed. With it, every root compiles and its certificate rechecks to the same object
in well under a second; the executable on `5` prints Lean's value where the result is below
`2^63` and ends with `natOverflow` where the bound leaves a primitive, or a literal operand, past a
native word (`2 ^ 513 % 7`, `2 ^ 2^32`, `mulChain32`, `2^1100 % 7`: Lean's value is a number there;
arbitrary-precision naturals, a later phase, are what make such programs run).

Every root is `noncomputable`: Lean 4.34.1's own code generator folds `Nat.shiftLeft` on literals
without a bound, so `ix compile` aborts (`Nat.shiftl exponent is too big`) on a computable
definition of that shape. The kernel's terms, and so the closure, do not depend on it.

The closure and sidecar are written by the ix of this repository (role-bound) with the commands
`provenance.json` records, by `lake exe refreeze-ixon fold --ix IX --ix-path FAKE`
([`docs/corpus.md`](../../docs/corpus.md), "Refreezing"), which also rewrites
`manifest.sha256`.
