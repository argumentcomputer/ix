# rbmap_fbip: upstream variant

**Source.** Lean `tests/compile_bench` at v4.34.0 (`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`), `rbmap_fbip.lean` (the zipper-based insertion from
Lorenzen and Leijen, "Reference Counting with Frame Limited Reuse"), vendored
byte for byte in `upstream/` with its `.init.sh` and `.out.expected`.

**Change.** None to the definitions; `main` is split into a pure
`entry : Nat → Nat` and a printing `main`, as for `rbmap`. The fixture is
kept for later comparison with annotated (ix contract) variants.

```diff
--- upstream/rbmap_fbip.lean
+++ RbmapFbip.lean
@@ -1,4 +1,14 @@
 /-
+Compilatr.ix fixture `rbmap_fbip` (upstream variant) of
+Lean `tests/compile_bench/rbmap_fbip.lean` (leanprover/lean4
+v4.34.0, 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b; Apache-2.0, see
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
@@ -58,7 +68,9 @@
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

**Twin.** The `rbmap` twin, `../rbmap/upstream/rbtree.cpp` (Koka
`test/bench/cpp/rbtree.cpp`), unchanged.
