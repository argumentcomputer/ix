# rbmap: upstream variant

**Source.** Lean `tests/compile_bench` at v4.34.0 (`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`), `rbmap.lean`, vendored byte for byte in `upstream/`
with its `.init.sh` and `.out.expected`.

**Change.** None to the definitions. The upstream `main` computes the
result inline; `Rbmap.lean` moves that computation into a pure
`entry : Nat → Nat` and keeps a `main` that prints the value exactly as
upstream does, so `upstream/rbmap.lean.out.expected` applies unchanged. The
checker verifies that the upstream text before `def main` occurs verbatim in
`Rbmap.lean`.

```diff
--- upstream/rbmap.lean
+++ Rbmap.lean
@@ -1,4 +1,14 @@
 /-
+Compilatr.ix fixture `rbmap` (upstream variant) of Lean
+`tests/compile_bench/rbmap.lean` (leanprover/lean4 v4.34.0,
+293d5d0c0c3f3dded4688b3ccd6a33939ac5102b; Apache-2.0, see
+`benchmarks/fixtures/LICENSES/lean4-LICENSE`). Modified for Compilatr.ix:
+the upstream `main` is replaced by a pure `entry` and a `main` that
+prints its result in the upstream format; the definitions above `entry`
+are unchanged. See `VARIANT.md`.
+-/
+
+/-
 Copyright (c) 2017 Microsoft Corporation. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: Leonardo de Moura, Sebastian Ullrich
@@ -62,7 +72,9 @@
 def mkMap (n : Nat) :=
   mkMapAux n .leaf
 
+/-- The pure benchmark entry: the value `main` prints. -/
+def entry (n : Nat) : Nat :=
+  fold (fun _ v r => if v then r + 1 else r) (mkMap n) 0
+
 def main (xs : List String) : IO Unit :=
-  let m := mkMap xs.head!.toNat!
-  let v := fold (fun _ v r => if v then r + 1 else r) m 0
-  IO.println (toString v)
+  IO.println (toString (entry xs.head!.toNat!))
```

**Twin.** `upstream/rbtree.cpp` (Koka `test/bench/cpp/rbtree.cpp`),
unchanged: a `std::map<int, bool>` filled by descending insertion, then a
count of the `true` values. Lean's own `tests/bench/rbmap_cpp_std.cpp` is
the same program over `lean::nat` keys. It includes `util/nat.h` from
Lean's source tree and needs Lean's C++ runtime (`libleanrt`, built against
libc++), so it does not build with plain `clang++ -O2 -std=c++17` against the
installed toolchain; it is vendored in `upstream/` for reference only.
