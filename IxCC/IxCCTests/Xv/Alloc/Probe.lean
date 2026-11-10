import IxCC.Xv.Validate.Check
import IxCC.Xv.Select.Driver
import IxCCTests.Lir.Kernels

/-!
# The validator evaluated by the kernel

The validator and `Alloc.apply` are on `Recheck.run`'s path (D17), so
Lean's kernel must evaluate them. Each theorem below selects a Lir kernel
and validates and applies its linear-scan allocation (the literal
certificate `Alloc.LinearScan.run` emits) inside the kernel with
`decide +kernel`, with no native evaluation (no `Lean.ofReduceBool`), and
`#guard_msgs` pins each to the three standard axioms (which the definitions
evaluated bring in, not the evaluation). A change that stops the validator reducing (a `HashMap`,
well-founded recursion, `implemented_by`) fails to elaborate here;
`check-regalloc` checks that the allocator still emits these certificates
(`Kernels.probeCertificates`).
-/

namespace IxCCTests.Xv.Alloc.Probe

open IxCC IxCC.Xv IxCCTests.Lir
open IxCC.Xv.Alloc (Output Edit)

/-- The kernel selected (in the kernel too), then its allocation validated
and applied. -/
def accepts (f : Lir.Func) (o : Output) : Bool :=
  match Select.run (Kernels.program f) with
  | .ok (q, _) => (Validate.run {} q [o]).toBool
  | .error _ => false

/-- Selection alone, to separate its kernel time from the validator's. -/
def selects (f : Lir.Func) : Bool := (Select.run (Kernels.program f)).toBool

-- BEGIN CERTIFICATES (generated from the allocator's output)
/-- `natAdd`, allocated by linear scan. -/
def natAddAlloc : Output :=
  { numSlots := 0, blocks := [
    { locs := [[.reg .rdi, .reg .rdi]]
      termLocs := [.reg .rax, .reg .rsi, .reg .rax]
      edits := [(1, .move (.reg .rax) (.reg .rdi))]
      cert := [(.reg .rdi, [0]), (.reg .rsi, [1])] },
    { locs := []
      termLocs := [.reg .rax]
      edits := []
      cert := [(.reg .rax, [3])] },
    { locs := []
      termLocs := []
      edits := []
      cert := [] }] }

/-- `sumLoop`, allocated by linear scan. -/
def sumLoopAlloc : Output :=
  { numSlots := 0, blocks := [
    { locs := [[.reg .rax], [.reg .rcx]]
      termLocs := []
      edits := []
      cert := [(.reg .rdi, [0])] },
    { locs := []
      termLocs := [.reg .rax, .reg .rdi]
      edits := []
      cert := [(.reg .rdi, [0]), (.reg .rcx, [3]), (.reg .rax, [2])] },
    { locs := [[.reg .rcx, .reg .rcx]]
      termLocs := [.reg .rcx, .reg .rax, .reg .rcx]
      edits := []
      cert := [(.reg .rcx, [3]), (.reg .rax, [2]), (.reg .rdi, [0])] },
    { locs := []
      termLocs := [.reg .rax]
      edits := [(0, .move (.reg .rax) (.reg .rcx))]
      cert := [(.reg .rcx, [3])] },
    { locs := [[.reg .rax, .reg .rax]]
      termLocs := []
      edits := []
      cert := [(.reg .rcx, [5]), (.reg .rax, [2]), (.reg .rdi, [0])] },
    { locs := []
      termLocs := []
      edits := []
      cert := [] }] }

/-- `fib`, allocated by linear scan. -/
def fibAlloc : Output :=
  { numSlots := 0, blocks := [
    { locs := []
      termLocs := [.reg .rdi]
      edits := []
      cert := [(.reg .rdi, [0])] },
    { locs := []
      termLocs := [.reg .rax]
      edits := [(0, .move (.reg .rax) (.reg .rdi))]
      cert := [(.reg .rdi, [0])] },
    { locs := [[.reg .rdi, .reg .rdi], [.reg .rdi, .reg .rax], [.reg .rbx, .reg .rdi], [.reg .rdi, .reg .rax], [.reg .rbx, .reg .rbx]]
      termLocs := [.reg .rbx, .reg .rax, .reg .rbx]
      edits := [(0, .move (.reg .rbx) (.reg .rdi)), (3, .move (.reg .rbx) (.reg .rax))]
      cert := [(.reg .rdi, [0])] },
    { locs := []
      termLocs := [.reg .rax]
      edits := [(0, .move (.reg .rax) (.reg .rbx))]
      cert := [(.reg .rbx, [6])] },
    { locs := []
      termLocs := []
      edits := []
      cert := [] }] }

/-- `gcd`, allocated by linear scan. -/
def gcdAlloc : Output :=
  { numSlots := 0, blocks := [
    { locs := []
      termLocs := []
      edits := []
      cert := [(.reg .rdi, [0]), (.reg .rsi, [1])] },
    { locs := []
      termLocs := [.reg .rsi]
      edits := []
      cert := [(.reg .rdi, [2]), (.reg .rsi, [3])] },
    { locs := []
      termLocs := [.reg .rax]
      edits := [(0, .move (.reg .rax) (.reg .rdi))]
      cert := [(.reg .rdi, [2])] },
    { locs := [[.reg .rax, .reg .rax], [.reg .rcx, .reg .rcx], [.reg .rdx], [.reg .rcx, .reg .rax, .reg .rdx, .reg .rax, .reg .rdx], [.reg .rdx, .reg .rdx], [.reg .rdx, .reg .rdx]]
      termLocs := []
      edits := [(0, .move (.reg .rax) (.reg .rdi)), (1, .move (.reg .rcx) (.reg .rsi)), (6, .move (.reg .rdi) (.reg .rsi)), (6, .move (.reg .rsi) (.reg .rdx))]
      cert := [(.reg .rsi, [3]), (.reg .rdi, [2])] }] }

-- END CERTIFICATES

/-- The certificates above, for the check that the allocator still emits
them. -/
def certificates : List (Lir.Func × Output) :=
  [(Kernels.natAdd, natAddAlloc), (Kernels.sumLoop, sumLoopAlloc), (Kernels.fib, fibAlloc),
    (Kernels.gcd, gcdAlloc)]

set_option maxRecDepth 100000

theorem natAdd_selects : selects Kernels.natAdd = true := by decide +kernel
theorem natAdd_valid : accepts Kernels.natAdd natAddAlloc = true := by decide +kernel
theorem sumLoop_selects : selects Kernels.sumLoop = true := by decide +kernel
theorem sumLoop_valid : accepts Kernels.sumLoop sumLoopAlloc = true := by decide +kernel
theorem fib_selects : selects Kernels.fib = true := by decide +kernel
theorem fib_valid : accepts Kernels.fib fibAlloc = true := by decide +kernel
theorem gcd_selects : selects Kernels.gcd = true := by decide +kernel
theorem gcd_valid : accepts Kernels.gcd gcdAlloc = true := by decide +kernel

/-- A wrong certificate is rejected in the kernel too: `fib`'s return block
claiming its result in `rcx`. -/
theorem fib_mutant_rejected :
    accepts Kernels.fib { fibAlloc with blocks := fibAlloc.blocks.set 3 { fibAlloc.blocks[3]! with
      cert := [(.reg .rcx, [6])] } } = false := by decide +kernel

/-- info: 'IxCCTests.Xv.Alloc.Probe.fib_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fib_valid

/-- info: 'IxCCTests.Xv.Alloc.Probe.gcd_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gcd_valid

/-- info: 'IxCCTests.Xv.Alloc.Probe.fib_mutant_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fib_mutant_rejected

end IxCCTests.Xv.Alloc.Probe
