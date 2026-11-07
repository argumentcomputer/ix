import IxCCTests.Recheck.Artifacts.Fib
import IxCCTests.Recheck.Kernel.Support

/-! The `fib` bench-k1 artifact through the recheck path in the kernel
(M1.K1): on the program, configuration and certificate of
`IxCCTests.Recheck.Artifacts.Fib`, `decide +kernel` evaluates

* `Recheck.runTyped` to the laid-out typed x86 program the native run
  computes (21 blocks, 165 instructions), and
* the whole `Recheck.run` to the object's 2,040 bytes the native run
  writes: selection through stacking and layout, `Program.checkK`, E1
  (`Encode.encodeK`), E2's stream check (`Stream.checkK`) and the ELF
  writer with its validator (`ELF.writeCheckedK`).

A wrong program is told apart (the `≠` example). -/

namespace IxCCTests.Recheck.Kernel.Fib

open IxCC IxCCTests.Recheck.Artifacts.Fib

set_option maxRecDepth 1000000

/-- The recheck path up to the laid-out typed program. -/
example : (Recheck.runTyped cfg program cert).map (·.program) = .ok typed := by decide +kernel

/-- Sanity: the kernel tells a wrong program apart. -/
example : (Recheck.runTyped cfg program cert).map (·.program) ≠ .ok { typed with entry := 1 } := by
  decide +kernel

/-- The whole recheck path: the object's bytes. -/
example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end IxCCTests.Recheck.Kernel.Fib
