# binarytrees: total variant

**Source.** Lean `tests/compile_bench` at v4.34.0 (`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`), `binarytrees.lean`, vendored byte for byte in
`upstream/` with its `.init.sh` and `.out.expected`. The upstream program
is a recorded rejection: it uses `partial` (`make'`, `sumT`, `depth`),
`Task.spawn`, and computes inside `IO`.

**Change.** Minimal rewrite to a total, single-threaded program:

- `make'` recurses structurally on a `Nat` depth instead of a `UInt32`
  counted down by `partial` recursion. It keeps the extra `n : UInt32`
  argument that defeats common-subexpression elimination, and `make`
  passes `d.toNat`.
- `sumT` recurses structurally on a `Nat` iteration count instead of a
  `UInt32` one, so `depth` passes `n` rather than `.ofNat n`.
- `depth` is well-founded on `m + 1 - d` instead of `partial` (the default
  decreasing tactic proves it), and it stores the `sumT` value directly
  instead of a `Task` spawned for it, so the rows are computed sequentially.
- The computation in `main` moves into a pure `entry`, which returns the
  stretch-tree check, the per-depth rows and the long-lived-tree check. The
  long-lived tree is still built before the rows and checked after them.
  `main` prints them with the upstream `out`, so
  `upstream/binarytrees.lean.out.expected` applies unchanged.

```diff
--- upstream/binarytrees.lean
+++ BinaryTrees.lean
@@ -1,3 +1,16 @@
+/-
+Compilatr.ix fixture `binarytrees` (total variant) of Lean
+`tests/compile_bench/binarytrees.lean` (leanprover/lean4 v4.34.0,
+293d5d0c0c3f3dded4688b3ccd6a33939ac5102b; Apache-2.0, see
+`benchmarks/fixtures/LICENSES/lean4-LICENSE`). Modified for Compilatr.ix:
+`make'` and `sumT` recurse structurally on a `Nat` depth and count instead
+of `partial` recursion on `UInt32`; `depth` is well-founded on
+`m + 1 - d` instead of `partial`; the `Task.spawn` is replaced by the
+direct (single-threaded) value; and the IO `main` is split into a pure
+`entry` and a `main` that prints its result in the upstream format. See
+`VARIANT.md`.
+-/
+
 inductive Tree
   | nil
   | node (l r : Tree)
@@ -5,12 +18,12 @@
 
 -- This function has an extra argument to suppress the
 -- common sub-expression elimination optimization
-partial def make' (n d : UInt32) : Tree :=
-  if d = 0 then .node .nil .nil
-  else .node (make' n (d - 1)) (make' (n + 1) (d - 1))
+def make' (n : UInt32) : Nat → Tree
+  | 0 => .node .nil .nil
+  | d + 1 => .node (make' n d) (make' (n + 1) d)
 
 -- build a tree
-def make (d : UInt32) := make' d d
+def make (d : UInt32) := make' d d.toNat
 
 def check : Tree → UInt32
   | .nil => 0
@@ -22,37 +35,46 @@
   IO.println s!"{s} of depth {n}\t check: {t}"
 
 -- allocate and check lots of trees
-partial def sumT (d i t : UInt32) : UInt32 :=
-  if i = 0 then t
-  else
+def sumT (d : UInt32) : Nat → UInt32 → UInt32
+  | 0, t => t
+  | i + 1, t =>
     let a := check (make d)
-    sumT d (i-1) (t + a)
+    sumT d i (t + a)
 
 -- generate many trees
-partial def depth (d m : Nat) : List (Nat × Nat × Task UInt32) :=
+def depth (d m : Nat) : List (Nat × Nat × UInt32) :=
   if d ≤ m then
     let n := 2 ^ (m - d + minN)
-    (n, d, Task.spawn (fun _ => sumT (.ofNat d) (.ofNat n) 0)) :: depth (d+2) m
+    (n, d, sumT (.ofNat d) n 0) :: depth (d+2) m
   else []
+termination_by m + 1 - d
+
+/-- The pure benchmark entry: the stretch-tree check, the per-depth
+`(iterations, depth, check)` rows, and the long-lived-tree check. -/
+def entry (n : Nat) : UInt32 × List (Nat × Nat × UInt32) × UInt32 :=
+  let maxN := Nat.max (minN + 2) n
+  let stretchN := maxN + 1
+
+  -- stretch memory tree
+  let c := check (make $ UInt32.ofNat stretchN)
+
+  -- allocate a long lived tree
+  let long := make $ UInt32.ofNat maxN
+
+  -- allocate, walk, and deallocate many bottom-up binary trees
+  let vs := (depth minN maxN)
+
+  -- confirm the long-lived binary tree still exists
+  (c, vs, check long)
 
 def main : List String → IO UInt32
   | [s] => do
     let n := s.toNat!
     let maxN := Nat.max (minN + 2) n
     let stretchN := maxN + 1
-
-    -- stretch memory tree
-    let c := check (make $ UInt32.ofNat stretchN)
+    let (c, vs, long) := entry n
     out "stretch tree" stretchN c
-
-    -- allocate a long lived tree
-    let long := make $ UInt32.ofNat maxN
-
-    -- allocate, walk, and deallocate many bottom-up binary trees
-    let vs := (depth minN maxN)  -- `using` (parList $ evalTuple3 r0 r0 rseq)
-    vs.forM (fun (m, d, i) => out s!"{m}\t trees" d i.get)
-
-    -- confirm the long-lived binary tree still exists
-    out "long lived tree" maxN (check long)
+    vs.forM (fun (m, d, i) => out s!"{m}\t trees" d i)
+    out "long lived tree" maxN long
     return 0
   | _ => return 1
```

**Twin.** `binarytrees.cpp`, adapted from Koka
`test/bench/cpp/binarytrees.cpp` (Benchmarks Game C++ #5; vendored in
`upstream/`). Its output format already matches Lean's. The only change:
`run_parallel` uses `BINARYTREES_WORKERS` threads (default 1), to match the
single-threaded Lean variant; `-DBINARYTREES_WORKERS=N` restores parallel
runs. It still allocates from `std::pmr` arenas, as upstream does.

```diff
--- upstream/binarytrees.cpp
+++ binarytrees.cpp
@@ -1,3 +1,12 @@
+// Compilatr.ix twin of Lean `binarytrees`, adapted from Koka `test/bench/cpp/binarytrees.cpp`
+// (koka-lang/koka 8b803da69d3941ce1e03173578093aefc41ee548; Apache-2.0, see
+// benchmarks/fixtures/LICENSES/koka-LICENSE; the program itself is from the Computer
+// Language Benchmarks Game, whose programs are distributed under the 3-Clause BSD licence).
+// Modified for Compilatr.ix: run_parallel uses BINARYTREES_WORKERS threads (default 1,
+// matching the single-threaded total Lean variant; upstream uses hardware_concurrency()).
+#ifndef BINARYTREES_WORKERS
+#define BINARYTREES_WORKERS 1
+#endif
 // Note: this is benchmark #5 which is 2nd after the top C++ benchmark #7.
 // However, #7 relies on TBB which seems to cause trouble on other platforms (it is 2.5x slower than #5 on the M1).
 // Also note that #5 (and #7) parallelize inside the iterations for a specific depth unlike most implementations
@@ -54,7 +63,7 @@
     return root;
 }
 
-int run_parallel(unsigned depth, int iterations, unsigned int workers = std::thread::hardware_concurrency())
+int run_parallel(unsigned depth, int iterations, unsigned int workers = BINARYTREES_WORKERS)
 {
     std::vector<std::thread> threads;
     threads.reserve(workers);
```
