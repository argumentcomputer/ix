# reverse: port of CakeML `reverse.cml`

**Source.** CakeML `compiler/benchmarks/cakeml_benchmarks/cakeml/reverse.cml`
(`530c7deec135ad421cce7ca768eed2f5801261b2`), vendored byte for byte in
`upstream/`. `Reverse.lean` is a translation, reviewed like a total variant.

| CakeML | Lean | Note |
| --- | --- | --- |
| `reverse xs` with local `append` and `rev` | `reverse xs := rev xs where append … rev …` | quadratic naive reverse; the local functions become `reverse.append` and `reverse.rev` |
| `mk_list n` (`if n = 0 then [] else n :: mk_list (n - 1)`) | `mkList` | structural on `n` |
| `val test = reverse (mk_list 50000)` | `entry n` | bench argument 50000 |

**Output.** The CakeML program discards `test`; its commented-out I/O would
print every element's digits. The port prints the length and an
order-sensitive checksum, `fold (h * 31 + x) mod 1000000007` from 0 (`checksum`,
not part of the CakeML program). The checksum is linear, so the quadratic
reverse dominates.

**Twin.** `reverse.c`, written for this pack: the same recursion over
`malloc`ed cons cells. `rev` turns the cell of `x :: xs` into `[x]`, and
`append` relinks its first argument in place. This mirrors Lean's reuse of
uniquely owned cells, so the twin allocates only `mk_list`.
