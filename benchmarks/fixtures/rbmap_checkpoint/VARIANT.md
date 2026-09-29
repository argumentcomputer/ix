# rbmap_checkpoint: upstream variant

**Source.** Lean `tests/compile_bench` at v4.34.0 (`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`), `rbmap_checkpoint.lean`, vendored byte for byte in
`upstream/` with its `.init.sh` and `.out.expected`.

**Change.** None to the definitions. The upstream `main` parses `n` and
`freq`, replaces `freq = 0` by 1, and prints `myLen` and the fold of the
newest checkpoint. `entry : Nat → Nat → Nat × Nat` performs everything after
parsing (including the `freq` default); `main` parses and prints the pair
in the upstream format.

```diff
--- upstream/rbmap_checkpoint.lean
+++ RbmapCheckpoint.lean
@@ -1,4 +1,14 @@
 /-
+Compilatr.ix fixture `rbmap_checkpoint` (upstream variant) of Lean
+`tests/compile_bench/rbmap_checkpoint.lean` (leanprover/lean4
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
@@ -71,11 +81,15 @@
   | _ :: xs,        r => myLen xs r
   | [],             r => r
 
-def main (xs : List String) : IO Unit := do
-  let [n, freq] ← pure xs | throw <| IO.userError "invalid input"
-  let n     := n.toNat!
-  let freq  := freq.toNat!
+/-- The pure benchmark entry: the pair `main` prints. The `freq` default is
+the upstream `main`'s. -/
+def entry (n freq : Nat) : Nat × Nat :=
   let freq  := if freq == 0 then 1 else freq
   let mList := mkMap n freq
   let v     := fold (fun _ v r => if v then r + 1 else r) mList.head! 0
-  IO.println s!"{myLen mList 0} {v}"
+  (myLen mList 0, v)
+
+def main (xs : List String) : IO Unit := do
+  let [n, freq] ← pure xs | throw <| IO.userError "invalid input"
+  let (len, v) := entry n.toNat! freq.toNat!
+  IO.println s!"{len} {v}"
```

**Twin.** `rbmap_checkpoint.cpp`, written for this pack. Both candidate
upstream twins are vendored in `upstream/` but not used:

- Lean `tests/bench/rbmap_checkpoint_cpp_std.cpp` needs Lean's in-tree C++
  runtime headers (as `rbmap_cpp_std.cpp` does; see `../rbmap/VARIANT.md`).
- Koka `test/bench/cpp/rbtree-ck.cpp` is self-contained, but its own comment
  says the approach "is too slow", and it exits with status 1 to mark the test
  as not working.

Both checkpoint by copying the whole `std::map` into a list and print only
the count. At the test arguments (100000, 10) that keeps about 5 × 10^8 map
nodes (about 24 GB) alive, and at the bench arguments (2000000, 1) it is
quadratic. The twin keeps the upstream driver (descending insertion, a
checkpoint whenever `n % freq == 0`, the fold of the newest map) but uses a
persistent red-black tree with shared ownership (`std::shared_ptr`, path
copying), whose insertion and balancing cases follow Lean's `ins`,
`balance1` and `balance2`. It prints `myLen` (the non-empty checkpoints)
and the count, as Lean does. Unlike Lean, it never updates a node in place,
even when it is not shared.
