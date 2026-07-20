import Benchmarks.Lean4Lean

/-!
Exe root for `bench-lean4lean`. `main` lives here, in a module nothing
imports, so the machinery in `Benchmarks.Lean4Lean` stays importable
(the `lean4lean` ignored test runner uses it) without a root-level `main`
collision.
-/

unsafe def main (args : List String) : IO UInt32 :=
  benchLean4LeanCmd.validate args
