import Lake

open Lake DSL

package compilerComparisons

/- Use the compiler checkout and its pinned dependencies. This package is not
a dependency of the compiler library or its CI checks. -/
require compilatrix from "../.."

lean_lib Comparisons

@[default_target]
lean_exe benchmark where
  root := `Benchmark

@[default_target]
lean_exe «compiler-scaling» where
  root := `CompilerScaling
