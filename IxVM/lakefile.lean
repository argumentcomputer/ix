import Lake
open System Lake DSL

package ixvm where
  version := v!"0.1.0"

require aiur from "../Aiur"

/- Program digests (`programDigest`) hash with the same pinned BLAKE3 as the root package. -/
require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @ "3f8b805614a0bae1c033469ff893a8f0ee85f601"

@[default_target]
lean_lib IxVM

lean_exe ixvm where
  root := `IxVM.Main
  supportInterpreter := true

/-- Writes, or with `--check` compares, the checked source's Lean files
(`IxVM/IxVM/Checked/`). -/
lean_exe «ixvm-checked» where
  root := `IxVM.CheckedMain
