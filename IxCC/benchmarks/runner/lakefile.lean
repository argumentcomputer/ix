import Lake

open Lake DSL

/- Optional measurement runner for the benchmark fixtures. It is not a
dependency of the compiler library or of the root flake's checks. -/
package benchmarkRunner

lean_lib Runner

@[default_target]
lean_exe runner where
  root := `Main
