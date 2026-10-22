import Lake
open System Lake DSL

package multiStark where
  version := v!"0.1.0"

require aiur from "../Aiur"

@[default_target]
lean_lib MultiStark

lean_exe «stark-export» where
  root := `MultiStark.Main
  supportInterpreter := true
