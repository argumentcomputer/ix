# foldl: port of CakeML `foldl.cml`

**Source.** CakeML `compiler/benchmarks/cakeml_benchmarks/cakeml/foldl.cml`
(`530c7deec135ad421cce7ca768eed2f5801261b2`), vendored byte for byte in
`upstream/`. `Foldl.lean` is a translation, reviewed like a total variant.

| CakeML | Lean | Note |
| --- | --- | --- |
| `foldl f e xs` | `foldl f : β → List α → β` | own definition, not `List.foldl`; structural |
| `repeat x n` | `«repeat» x : Nat → List α` | `repeat` is a Lean keyword, hence the guillemets |
| `val test = foldl (fn x => fn y => x + foldl (fn x => fn y => x + y) 0 y) 0 (repeat (repeat 1 40000) 40000)` | `test n` | size as an argument; bench argument 40000 |

**Output.** The CakeML program discards `test`; the port prints it (`n * n`).

**Twin.** `foldl.c`, written for this pack. The outer list holds `n`
references to one shared inner list, as `repeat (repeat 1 n) n` shares its
argument, and folds go through function pointers, as the higher-order
`foldl` does.
