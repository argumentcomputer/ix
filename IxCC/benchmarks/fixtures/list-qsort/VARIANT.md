# list-qsort: port of CakeML `qsort.cml`

**Source.** CakeML `compiler/benchmarks/cakeml_benchmarks/cakeml/qsort.cml`
(`530c7deec135ad421cce7ca768eed2f5801261b2`), vendored byte for byte in
`upstream/`. `ListQsort.lean` is a translation, reviewed like a total
variant. The fixture is named `list-qsort` to keep it apart from Lean's K4
`qsort` (`Array UInt32`).

| CakeML | Lean | Note |
| --- | --- | --- |
| `part p l (l1, l2)` | `part` | structural on `l` |
| `partition p l` | `partition` | |
| `append l1 l2` | `append` | own definition, not `List.append` |
| `qsort r l` | `qsort r : List α → List α` | well-founded on `l.length`; see below |
| `mk_list n` | `mkList` | structural on `n` |
| `use_qsort n = qsort (fn x => fn y => x <= y) (append (mk_list n) (mk_list n))` | `useQsort n` | `x ≤ y` decided on `Nat` |
| `val test = use_qsort 10000` | `entry n` | bench argument 10000 |

**Termination.** `qsort` recurses on the two halves returned by `partition`,
so it is not structural. The port matches on `partition … t` with an equation
(`match hp : …`) and proves, with `part_length`, that each half is no longer
than `t`. The proofs are erased; the compiled recursion is CakeML's.

**Output.** The CakeML program discards `test`. The port prints the length
and the same order-sensitive checksum as `reverse` (`checksum`, not part of
the CakeML program).

**Twin.** `list_qsort.c`, written for this pack: the same head-pivot
quicksort over `malloc`ed cons cells. `part` relinks cells into the two
halves, the pivot's cell becomes `[h]`, and `append` relinks in place. This
mirrors Lean's reuse of uniquely owned cells.
