# The Phase 1 resource corpus

The `phase1-resource` family of the [fixture corpora](../../../docs/corpus.md)
(phase 1 plan, MT.3; research §9.4.2): runs that fail by the driver's own
limits, deterministically, with the statuses of 04 §6 — 1 heap
(`--region`), 2 stack (`--stack`), 4 trap — at every level that models the
failure and natively. Each case's `region` and `stack` set the word levels'
region, the machines' stack budget and the driver's flags.

| Root | Cases | Expectation |
| --- | --- | --- |
| `Resource.heapList n` | `n` cells of two fields (24 bytes each) | in a 4 KiB region, 144 cells fit exactly (`144 × 24 = 4096 − 640`) and 145 fail with status 1; a region of 4095 bytes fails in `cx_init` |
| `Resource.twoVars n` | a `for` loop with two mutable variables | `n + 1` cells of 24 bytes (one per iteration and the initial state): 143 iterations fit 4 KiB, 144 fail (MT.2 finding 5, pinned) |
| `Resource.oneVar n` | the same loop with one variable | allocates nothing: 10,000 iterations in 4 KiB |
| `Resource.depth n` | non-tail recursion | depth 100 in an 8 KiB stack (4 KiB budget); depth 513 must fail (513 return addresses exceed 4096 bytes), and 10,000 in 64 KiB; status 2 on the typed x86 machine, ByteEval and natively, the value at the levels without a stack |
| `Resource.tail n`, `Resource.isEven`, `Resource.isOdd` | tail and mutual tail calls | 10,000 iterations in a 4 KiB budget: tail calls do not grow the stack |
| `Resource.trapEmpty`, `trapFalse`, `trapAbsurd` | `nomatch` on `Empty`, `False.elim`, `absurd rfl h` | status 4: no well-typed call reaches them, but the wrapper passes a word for the empty argument or the proof |

The heap thresholds follow exactly from the immortal layout (`Rt.Layout`:
cells of `8 (k + 1)` bytes from the first 64-byte boundary after the 640-byte
context block); the stack cases need no frame size: one bound must succeed
and the other must fail. Natively the default stack is 256 MiB and the
default region 16 MiB; the word levels' default region is 64 KiB.

Licence: Apache-2.0 OR MIT (original programs).
