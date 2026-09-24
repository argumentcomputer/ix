import Lake
open Lake DSL

/-! # The certified kernel as its own package

`ix-kernel` builds `Ix.Kernel` and `Ix.Address.Core` from the repository's
`Ix/` tree (`srcDir := ".."`) with no dependencies beyond the Lean toolchain.
The root `ix` package builds the same modules for its host consumers; this
package is what the certified gate builds (`lake -d IxKernel build --wfail`),
so a kernel module that imports anything outside the kernel fails here even
if it would build inside the root workspace, and it is what
`Models/SetTheory` depends on, so the model's workspace holds Mathlib and the
kernel only. See `plans/ix-certified-roadmap.md`. -/

package «ix-kernel» where
  version := v!"0.1.0"

@[default_target]
lean_lib IxKernel where
  srcDir := ".."
  roots := #[`Ix.Kernel, `Ix.Address.Core]
  globs := #[.andSubmodules `Ix.Kernel, .one `Ix.Address.Core]
