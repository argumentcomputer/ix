import Lake
open System Lake DSL

package ixvm where
  version := v!"0.1.0"

require aiur from "../Aiur"

@[default_target]
lean_lib IxVM

lean_exe ixvm where
  root := `IxVM.Main
  supportInterpreter := true
