import Lake
open Lake DSL

package "Compile" where
  version := v!"0.1.0"

@[default_target]
lean_lib Compile

lean_exe "compile-lean" where
  root := `CompileLean
  supportInterpreter := true

lean_exe "compile-mathlib" where
  root := `CompileMathlib
  supportInterpreter := true

lean_exe "compile-flt" where
  root := `CompileFLT
  supportInterpreter := true

require ix from "../.."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

require flt from git
  "https://github.com/ImperialCollegeLondon/FLT" @ "v4.26.0"
