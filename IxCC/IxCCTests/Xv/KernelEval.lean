import IxCC.Xv.Select.Driver
import IxCCTests.Lir.Kernels

/-!
# Selection evaluated by the kernel

Selection is on `Recheck.run`'s path, which Lean's kernel must evaluate
(D17). These examples run `Select.run` on the tagged-`Nat`
kernels inside the kernel (`decide +kernel`, no native evaluation) and
check the size of each selected block, so a change that stops selection
reducing (a `HashMap`, well-founded recursion, `implemented_by`) fails to
elaborate here. About 0.6 s of kernel time in all.
-/

namespace IxCCTests.Xv.KernelEval

open IxCC IxCCTests.Lir

/-- The instruction count of each selected block. -/
def shape (p : Lir.Program) : Option (List (List Nat)) :=
  match Xv.Select.run p with
  | .ok (q, _) => some (q.funcs.toList.map fun f => f.blocks.toList.map fun b => b.body.toList.length)
  | .error _ => none

set_option maxRecDepth 100000 in
example : shape (Kernels.program Kernels.natAdd) = some [[1, 0, 0]] := by decide +kernel
set_option maxRecDepth 100000 in
example : shape (Kernels.program Kernels.fib) = some [[0, 0, 5, 0, 0]] := by decide +kernel
set_option maxRecDepth 100000 in
example : shape (Kernels.program Kernels.sumLoop) = some [[2, 0, 1, 0, 1, 0]] := by decide +kernel
set_option maxRecDepth 100000 in
example : shape (Kernels.program Kernels.gcd) = some [[0, 0, 0, 6]] := by decide +kernel
set_option maxRecDepth 100000 in
example : shape (Kernels.program Kernels.natMod) = some [[0, 0, 6]] := by decide +kernel

end IxCCTests.Xv.KernelEval
