import Lake
open System Lake DSL

package multiStark where
  version := v!"0.1.0"

require aiur from "../Aiur"

/- Program digests (`programDigest`) hash with the same pinned BLAKE3 as the root package. -/
require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @ "3f8b805614a0bae1c033469ff893a8f0ee85f601"

@[default_target]
lean_lib MultiStark where
  globs := #[.andSubmodules `MultiStark]

lean_exe «stark-export» where
  root := `MultiStark.Main
  supportInterpreter := true

lean_exe kzg_xof_fixture where
  root := `Examples.KzgXof
lean_exe kzg_source_fixture where
  root := `Examples.KzgSource
lean_exe compress_gl_export where
  root := `Examples.CompressGL
lean_exe compress_bn_export where
  root := `Examples.CompressBN
