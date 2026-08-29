# Counter-level thesis evidence

This is the first quantitative instrument for the project's mode-directed
performance claim. `Compilatrix/IxIR1/ThesisBench.lean` lowers and runs paired
IxIR₀ programs, records exact IxIR₁ instruction counters, releases each
result, and pins every observation with elaboration-time guards.

The pairs are mechanically the same program modulo modes:
`ThesisBench.eraseModes` removes `Uses` annotations and every report records
`sameProgram = true`. Both executions also decode to the same result digest.

## Results

Counters are `(allocs, reuses, frees, rcops, live)`. "Before" is the returned
store; "after" includes release of the returned value.

| Program | Result | All-shared before | Mode-directed before | All-shared after | Mode-directed after | RC ops saved |
| --- | --- | --- | --- | --- | --- | ---: |
| Pair tree | `(2̂, 3̂)` | `(8, 0, 0, 0, 8)` | `(8, 0, 0, 0, 8)` | `(8, 0, 8, 8, 0)` | `(8, 0, 8, 0, 0)` | 8 |
| Dead tree | `1̂` | `(5, 0, 3, 3, 2)` | `(5, 0, 3, 0, 2)` | `(5, 0, 5, 5, 0)` | `(5, 0, 5, 0, 0)` | 5 |
| Dead parameter | `2̂` | `(5, 0, 2, 2, 3)` | `(5, 0, 2, 0, 3)` | `(5, 0, 5, 5, 0)` | `(5, 0, 5, 3, 0)` | 2 |
| **Total after release** | | | | **`(18, 0, 18, 18, 0)`** | **`(18, 0, 18, 3, 0)`** | **15** |

Thus this suite holds allocation, reclamation, and results fixed while modes
remove 15 of 18 RC instructions (83⅓%). The mixed dead-parameter benchmark
keeps its result shared on both sides; its three surviving mode-directed RC
operations are exactly the returned `2̂` tree's final release. Only the dead
first argument changes from shared to affine.

## Mode-adversarial fixtures

The same module pins static boundaries alongside the measurements:

- duplicating one shared binding is accepted, while the same mode-erased
  linear program is rejected as `unique variable used more than once`;
- dropping an affine binding is accepted, while the same mode-erased linear
  program is rejected as `unused linear binding`;
- shared-at-unique demand and unique-at-shared demand retain their exact
  `dereliction` and `freeze` diagnostics.

## Scope

These are deterministic interpreter instruction counts, not elapsed-time or
native-code measurements. They exercise construction, ownership transfer, and
reclamation. The current restriction wall still forbids destructuring unique
data, and the compiler path does not yet pair free+alloc into `reuse`; both
columns therefore intentionally pin `reuses = 0`.

The next computational-unique benchmark remains list reversal through a case.
It activates with the unique-destructuring lift; reuse measurements activate
with the IxIR₂ pairing pass. This document does not extrapolate the 83⅓% micro
result to general programs or wall-clock speed.
