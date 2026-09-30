import CompilatrixTests.Fir.Artifacts
import CompilatrixTests.Rt.Cases
import Compilatrix.Cfg.Lower
import Compilatrix.Rt.Lower

/-! Summaries of `Rt.lower`'s output that `CompilatrixTests.Rt.KernelEval`
checks in the kernel, with the table of natively computed values;
`tests-rt` recomputes them natively from the same tables. -/

namespace CompilatrixTests.Rt.Kernel

open Compilatrix

/-- Functions, blocks, statements, backward edges (target at or below the
source: the Lir clock's charges besides calls) and cold blocks. -/
def summaryOf (p : Lir.Program) : Nat × Nat × Nat × Nat × Nat :=
  let fs := p.funcs.toList
  (fs.length,
   fs.foldl (fun n f => n + f.blocks.size) 0,
   fs.foldl (fun n f => n + f.blocks.foldl (fun m b => m + b.body.size) 0) 0,
   fs.foldl (fun n f => n + f.blocks.toList.zipIdx.foldl (fun m (b, l) =>
     m + (b.term.succs.filter (· ≤ l)).length) 0) 0,
   fs.foldl (fun n f => n + (f.blocks.toList.filter (·.cold)).length) 0)

/-- `Rt.lower`'s summary; `none` if it declines. -/
def cfgSummary (C : Cfg.Program) : Option (Nat × Nat × Nat × Nat × Nat) :=
  match Rt.lower {} C with
  | .ok l => some (summaryOf l.program)
  | .error _ => none

/-- `Cfg.ofAnf` then `Rt.lower`; `none` if either declines. -/
def summary (A : Anf.Program) : Option (Nat × Nat × Nat × Nat × Nat) :=
  match Cfg.ofAnf A with
  | .ok C => cfgSummary C
  | .error _ => none

/-- The summaries the kernel checks, by bench entry (computed natively). -/
def expected : List (String × Anf.Program × Nat × Nat × Nat × Nat × Nat) :=
  [("fib", Fir.Artifacts.fib, 5, 37, 108, 2, 9),
   ("sum-loop", Fir.Artifacts.sumLoop, 5, 38, 104, 3, 10),
   ("ackermann", Fir.Artifacts.ackermann, 5, 38, 106, 4, 9),
   ("tak", Fir.Artifacts.tak, 5, 36, 116, 3, 8),
   ("gcd", Fir.Artifacts.gcd, 5, 32, 109, 3, 7)]

/-- Hand-written Cfg programs with what K1 lacks: allocation, projection,
mixed and cell switches, the `Nat` procedures (values); critical edges
(split); a literal without a word and a dead block (pruned). -/
def expectedCfg : List (String × Cfg.Program × Nat × Nat × Nat × Nat × Nat) :=
  [("values", Cases.cfgOf Cases.values', 13, 77, 165, 5, 14),
   ("critical", Cases.critical, 5, 37, 103, 2, 8),
   ("bigEdge", Cases.bigEdge, 4, 30, 103, 2, 8)]

end CompilatrixTests.Rt.Kernel
