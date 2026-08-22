import Lake
open System Lake DSL

package ix_sharing_baseline

require ix from "./ix"

/-- The script snapshots ix's `test-ffi` archive here before Lake builds the
default-feature Ix library, because both feature sets use the same Cargo path. -/
target ix_rs_test : FilePath := do
  inputBinFile "./libix_ffi_test.a"

lean_exe parity where
  root := `Main
  supportInterpreter := true
  moreLinkObjs := #[ix_rs_test]
