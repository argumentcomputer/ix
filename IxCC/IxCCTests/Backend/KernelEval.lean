import IxCC.Backend
import IxCCTests.Backend.Programs

/-!
# Stacking and layout evaluated by the kernel

Stacking (with its frame-layout check) and layout (tunnelling, the order
check and linearisation) are on `Recheck.run`'s path, which Lean's kernel
must evaluate (D17). These examples run them on
hand-written Xl programs inside the kernel (`decide +kernel`, no native
evaluation) and check the instruction count of each laid-out block, so a
change that stops them reducing fails to elaborate here.
-/

namespace IxCCTests.Backend.KernelEval

open IxCC IxCC.Xv IxCCTests.Backend.Programs

/-- The instruction count of each block after stacking and layout, when
every frame layout checks. -/
def shape (p : LProgram) : Option (List Nat) :=
  let layouts := Stacking.produce p
  if (p.funcs.toList.zip layouts).all (fun (f, l) => l.check f.facts) then
    match Stacking.run p layouts with
    | .ok s =>
        let t := X86.Layout.tunnel s.program
        match X86.Layout.run t s.shape (X86.Layout.Order.produce t s.shape) with
        | .ok (q, _) => some (q.blocks.toList.map (·.instructions.size))
        | .error _ => none
    | .error _ => none
  else none

set_option maxRecDepth 100000 in
example : shape leaf = some [14, 12, 2, 1, 9] := by decide +kernel

set_option maxRecDepth 100000 in
example : shape calls = some [13, 11, 1, 11, 9, 1, 1, 9] := by decide +kernel

set_option maxRecDepth 100000 in
example : shape deep = some [14, 12, 1, 3, 1, 1, 5, 0, 0, 0, 2, 1, 1, 1, 1, 9] := by decide +kernel

-- The loop-aware order (loop detection included): the body (3
-- instructions) before the exit (0).
set_option maxRecDepth 100000 in
example : shape loop = some [13, 11, 2, 0, 3, 0, 1, 9] := by decide +kernel

end IxCCTests.Backend.KernelEval
