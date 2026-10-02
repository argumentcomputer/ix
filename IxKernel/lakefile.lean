import Lake
open Lake DSL

/-! # The certified kernel as its own package

`ix-kernel` builds the certified Ixon checker from the repository sources
(`srcDir := ".."`) with no dependencies beyond the Lean toolchain: the kernel
`Ix.Kernel` (the checker derived from con-leche, and Ix's
boundary beside it: the certified entry `Ix.Kernel.Admission` with its
theorems, the Ixon reader, pins and prelude, record store, projection
writer, audits), `Ix.Address.Core`, and the pure Ixon types, codecs and
their proofs. Data import closures use Lean core and the kernel only (`Lean` only
at elaboration time, in the kernel's ruled generators); proofs additionally
use Lean/Std proof tooling.
The root `ix` package builds the same modules for its host consumers; this
package is what the certified gate builds (`lake -d IxKernel build --wfail`),
so a kernel module that imports anything outside the kernel fails here even
if it would build inside the root workspace, and it is what
`Models/SetTheory` depends on, so the model's workspace holds Mathlib and the
kernel only. See `docs/kernel.md`. -/

package «ix-kernel» where
  version := v!"0.1.0"

/-- `Ix.Kernel` and every module under `Ix/Kernel/` (as `IxKernelTree` in the
root `lakefile.lean`), with `linter.deprecated` off for the con-leche-derived
sources written for Lean 4.33.0. -/
@[default_target]
lean_lib IxKernelTree where
  srcDir := ".."
  roots := #[`Ix.Kernel]
  globs := #[.andSubmodules `Ix.Kernel]
  leanOptions := #[⟨`linter.deprecated, false⟩]

/-- The pure Ixon types, codecs and their proofs, which the certified entry
decodes with, and the address key. -/
@[default_target]
lean_lib IxKernel where
  srcDir := ".."
  roots := #[`Ix.Address.Core, `Ix.Ixon.Types, `Ix.Ixon.Codec, `Ix.Ixon.Wire,
    `Ix.Ixon.WireCheck, `Ix.Ixon.Bounded.Universe, `Ix.Ixon.Bounded.Constant, `Ix.Ixon.Bounded.Size,
    `Ix.Ixon.Canonical, `Ix.Ixon.Verify, `Ix.Ixon.Audit]
  globs := #[.one `Ix.Address.Core, .andSubmodules `Ix.Ixon.Types,
    .one `Ix.Ixon.Codec, .one `Ix.Ixon.Wire, .one `Ix.Ixon.WireCheck, .submodules `Ix.Ixon.Bounded,
    .one `Ix.Ixon.Canonical, .andSubmodules `Ix.Ixon.Verify, .one `Ix.Ixon.Audit]

/-- Certified fixtures also run without the host package's dependencies: the
Ixon record fixtures, the codec, and the certified entry's byte admission. -/
def kernelFixtureRoots : Array Lean.Name := #[
  `Tests.Ix.Kernel.IxonFixtures, `Tests.Ix.Kernel.Codec,
  `Tests.Ix.Kernel.ByteAdmission, `Tests.Ix.Kernel.ParserWork]

@[default_target]
lean_lib KernelFixtures where
  srcDir := ".."
  roots := kernelFixtureRoots
  globs := kernelFixtureRoots.map (fun root => .one root)
