# nqueens: port of Koka `nqueens.kk`

**Source.** Koka `test/bench/koka/nqueens.kk`
(`8b803da69d3941ce1e03173578093aefc41ee548`), vendored byte for byte in
`upstream/`. Lean's suite has no n-queens program, so `NQueens.lean` is a
translation, reviewed like a total variant.

| Koka | Lean | Note |
| --- | --- | --- |
| `alias solution = list<int32>` | `abbrev Solution := List Nat` | `Nat` for `int32`; see below |
| `safe(queen, diag, ^xs)` | `safe queen diag : Solution → Bool` | structural on the list; `&&` short-circuits as in Koka |
| `append-safe(queen, xs, xss)` | `appendSafe : Nat → …` | structural on `queen` (`queen <= 0` becomes the `0` case) |
| `extend(queen, acc, xss)` | `extend queen acc : Solutions → …` | structural on `xss` |
| `find-solutions(n, queen)` | `findSolutions n : Nat → …` | structural on `queen` |
| `queens(n) = find-solutions(n, n).length` | `queens n` | `List.length` |
| `main`: `queens(13).println` | `entry n := queens n`; `main` reads `n` | size from the command line |

**`Nat` for `int32`.** Queens range over `1..n`. The only subtraction is in
`queen != q - diag`: with integers, `q - diag < 1` never equals a queen; with
`Nat`, it truncates to 0, which never equals a queen either. The two programs
therefore compute the same solutions. Koka's `nqueens-int.kk` is the same
program over arbitrary-precision `int`.

**Twin.** `upstream/nqueens.cpp` (Koka `test/bench/cpp/nqueens.cpp`),
unchanged. It reads `n` from `argv[1]` (default 13) and prints the count. It
does not free memory, since sub-solutions are shared.
