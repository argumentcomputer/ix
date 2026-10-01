import Benchmarks.Kernel.Census

/-! Entry point of `kernel-census-intrinsic` (the intrinsic reference kernel's
census; `kernel-census` is con-leche's from L5); see `Benchmarks.Kernel.Census`. -/

def main (args : List String) : IO UInt32 := Benchmarks.Kernel.Census.run args
