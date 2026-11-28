# queue: port of CakeML `queue.cml`

**Source.** CakeML `compiler/benchmarks/cakeml_benchmarks/cakeml/queue.cml`
(`530c7deec135ad421cce7ca768eed2f5801261b2`), vendored byte for byte in
`upstream/`. `Queue.lean` is a translation, reviewed like a total variant.

| CakeML | Lean | Note |
| --- | --- | --- |
| `datatype 'a q = QUEUE ('a list) ('a list)` | `inductive Q (α)` with constructor `queue` | |
| `empty`, `is_empty`, `reverse_aux`, `reverse`, `checkf`, `snoc` | same names in camelCase | same clauses |
| `head q` (only `QUEUE (x::f) r`) | `head [Inhabited α]` | the missing case returns `default`; see below |
| `tail q` (only `QUEUE (x::f) r`) | `tail` | the missing case returns `q` |
| `use_queue n q` (`if n = 0 … else … (n - 1)`) | `useQueue` | structural on `n` (`n + 1` pattern) |
| `run_queue n` | `runQueue n` | |
| `val test = run_queue 5000000` | `entry n := runQueue n` | bench argument 5000000 |

**Partial functions.** CakeML's `head` and `tail` raise `Bind` on an empty
front list. `useQueue n` leaves `n` elements in the queue, so for `n > 0` the
added cases are unreachable. For `n = 0`, the port prints 0 where CakeML would
raise.

**Output.** The CakeML program discards `test`; its I/O is commented out.
The port prints `run_queue n`. `is_empty` is unused in both.

**Twin.** `queue.c`, written for this pack: the same two-list queue over
`malloc`ed cons cells. `reverse_aux` relinks the rear list in place, and
`tail` frees the popped cell. This mirrors Lean's reuse of uniquely owned
cells.
