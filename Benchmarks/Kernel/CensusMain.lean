import Benchmarks.Kernel.Census

/-! Entry point of `kernel-census`; see `Benchmarks.Kernel.Census`. -/

def main (args : List String) : IO UInt32 := Benchmarks.Kernel.Census.run args
