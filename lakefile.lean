import Lake

open System Lake DSL

package compilatrix

/- Blake3 FFI. Keep this revision in lockstep with the flake's
`blake3-lean` input and `lake-manifest.json`. -/
require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @
  "aaf530784082a2c00b0a93648741429d274102ca"

/- The portable Lean filesystem API stops at buffered flush. Compile the
small, ledgered POSIX durability boundary as a normal traced Lake input. -/
target hpt_cache_sync pkg : FilePath := do
  let source ← inputTextFile <| pkg.dir / "native/hpt_cache_sync.c"
  let object := pkg.buildDir / "native" / "hpt_cache_sync.o"
  let includeDir ← getLeanIncludeDir
  let weakArgs := #["-fPIC", "-I", includeDir.toString]
  buildO object source weakArgs #[] "cc" getLeanTrace

@[default_target]
lean_lib Compilatrix where
  roots := #[`Compilatrix]
  moreLinkObjs := #[hpt_cache_sync]

/- Runtime tests (FFI execution cannot run in elaboration-time `#guard`s). -/
lean_exe tests where
  root := `Tests

lean_exe «catalog-contact» where
  root := `CatalogContact
