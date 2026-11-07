# const_fold: upstream variant

**Source.** Lean `tests/compile_bench` at v4.34.0 (`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`), `const_fold.lean`, vendored byte for byte in
`upstream/` with its `.init.sh` and `.out.expected`.

**Change.** None to the definitions. Upstream declares `main` as
`unsafe def`, although nothing in it needs `unsafe`. The variant replaces it
with a pure `entry : Nat → Nat × Nat` (build the expression, evaluate it,
reassociate and fold it, evaluate again) and a safe `main` that prints the
pair in the upstream format. `size` and `toStringAux` stay in the file,
unused by `entry`, as upstream. The upstream `.init.sh` sets
`LEAN_STACK_SIZE_KB=4194304` for compiled runs; the manifest records it as
the fixture's environment.

```diff
--- upstream/const_fold.lean
+++ ConstFold.lean
@@ -1,3 +1,13 @@
+/-
+IxCC fixture `const_fold` (upstream variant) of
+Lean `tests/compile_bench/const_fold.lean` (leanprover/lean4
+v4.34.0, 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b; Apache-2.0, see
+`benchmarks/fixtures/LICENSES/lean4-LICENSE`). Modified for IxCC:
+the upstream `unsafe def main` is replaced by a pure `entry` and a safe
+`main` that prints its result in the upstream format; the definitions above
+`entry` are unchanged. See `VARIANT.md`.
+-/
+
 inductive Expr
 | Var : Nat → Expr
 | Val : Nat → Expr
@@ -70,12 +80,16 @@
 
 open Expr
 
-unsafe def main : List String → IO UInt32
+/-- The pure benchmark entry: the pair `main` prints. -/
+def entry (n : Nat) : Nat × Nat :=
+  let e  := mkExpr n 1
+  let v₁ := eval e
+  let v₂ := eval (constFolding (reassoc e))
+  (v₁, v₂)
+
+def main : List String → IO UInt32
 | [s] => do
-  let n := s.toNat!;
-  let e  := (mkExpr n 1);
-  let v₁ := eval e;
-  let v₂ := eval (constFolding (reassoc e));
-  IO.println (toString v₁ ++ " " ++ toString v₂);
+  let (v₁, v₂) := entry s.toNat!
+  IO.println (toString v₁ ++ " " ++ toString v₂)
   pure 0
 | _ => pure 1
```

**Twin.** `cfold.cpp`, adapted from Koka `test/bench/cpp/cfold.cpp`
(vendored in `upstream/`):

- Upstream `const_folding` does not fold subterms before matching, so it
  does less work than Koka's `cfold.kk` and Lean's `constFolding`, both of
  which recurse first. The printed values agree either way, because folding
  preserves `eval`. The twin adds the two recursive calls in each case.
- The size comes from `argv[1]` (upstream: a constant 20, which stays the
  default), and the output is `v1 v2` (upstream: `v1, v2`).

As upstream, the twin never frees nodes. At the bench size (23), `reassoc`
and `const_folding` recurse about 2^23 deep, so both programs need a large
stack (the checker's `--bench` mode raises the stack limit to the hard
limit).

```diff
--- upstream/cfold.cpp
+++ cfold.cpp
@@ -1,3 +1,9 @@
+// IxCC twin of Lean `const_fold`, adapted from Koka `test/bench/cpp/cfold.cpp`
+// (koka-lang/koka 8b803da69d3941ce1e03173578093aefc41ee548; Apache-2.0,
+// see benchmarks/fixtures/LICENSES/koka-LICENSE).
+// Modified for IxCC: const_folding folds its subterms first, as Lean's
+// constFolding and Koka's cfold.kk do (upstream C++ does not recurse); the size is
+// read from argv[1] (default 20, as upstream); the output is "v1 v2", as in Lean.
 #include <math.h>
 #include <string.h>
 #include <iostream>
@@ -98,8 +104,8 @@
 
 static const Expr* const_folding( const Expr* e ) {
   if (e->kind == Add) {
-    const Expr* e1 = ((AddExpr*)e)->left;
-    const Expr* e2 = ((AddExpr*)e)->right;
+    const Expr* e1 = const_folding(((AddExpr*)e)->left);
+    const Expr* e2 = const_folding(((AddExpr*)e)->right);
     if (e1->kind == Val && e2->kind==Val) {
       return new ValExpr( ((ValExpr*)e1)->value + ((ValExpr*)e2)->value );
     }
@@ -118,8 +124,8 @@
     }
   }
   else if (e->kind == Mul) {
-    const Expr* e1 = ((MulExpr*)e)->left;
-    const Expr* e2 = ((MulExpr*)e)->right;
+    const Expr* e1 = const_folding(((MulExpr*)e)->left);
+    const Expr* e2 = const_folding(((MulExpr*)e)->right);
     if (e1->kind == Val && e2->kind==Val) {
       return new ValExpr( ((ValExpr*)e1)->value * ((ValExpr*)e2)->value );
     }
@@ -160,9 +166,9 @@
 
 
 int main(int argc, char ** argv) {
-  const Expr* e = mk_expr(20,1);
+  const Expr* e = mk_expr(argc == 2 ? atol(argv[1]) : 20, 1);
   long v1 = eval(e);
   long v2 = eval(const_folding(reassoc(e)));
-  std::cout << v1 << ", " << v2 << "\n";
+  std::cout << v1 << " " << v2 << "\n";
   return 0;
 }
```
