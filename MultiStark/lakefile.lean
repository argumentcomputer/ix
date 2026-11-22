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
lean_exe bn_grouping where
  root := `Examples.BNGrouping
lean_exe compress_final_export where
  root := `Examples.CompressFinal
lean_exe kzg_packed_export where
  root := `Examples.KzgPacked
lean_exe kzg_packed_terminal_export where
  root := `Examples.KzgPackedTerminal
lean_exe compress_final_narrow_export where
  root := `Examples.CompressFinalNarrow
lean_exe tiling_export where
  root := `Examples.TilingExport
lean_exe tiling_export2 where
  root := `Examples.TilingExport2
lean_exe compress_narrow_fixed_export where
  root := `Examples.CompressNarrowFixed
lean_exe compress_gl_fixed_export where
  root := `Examples.CompressGLFixed
lean_exe wide_export where
  root := `Examples.WideExport
lean_exe plonk_check_stage where
  root := `Examples.PlonkCheckStage
lean_exe plonk_beta_test where
  root := `Examples.PlonkBetaTest
lean_exe plonk_export where
  root := `Examples.PlonkExport
lean_exe plonk_entry_fixture where
  root := `Examples.PlonkEntryFixture
