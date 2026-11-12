import Tests.Ix.Kernel.DepthCase

/-! `kernel-depth-case NAME N`: one case of `kernel-depth` (`Tests.Ix.Kernel.Depth`),
in a process of its own, on the stack `LEAN_STACK_SIZE_KB` sets. -/

def main (args : List String) : IO UInt32 :=
  Tests.Ix.Kernel.Depth.runCase args
