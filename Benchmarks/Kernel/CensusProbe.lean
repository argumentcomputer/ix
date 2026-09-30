import Benchmarks.Kernel.Census

/-! A second build of the census runner, so a probe (`CENSUS_PROBE=<name>`) can
be built while a census run is using `kernel-census`. -/

def main (args : List String) : IO UInt32 := Benchmarks.Kernel.Census.run args
