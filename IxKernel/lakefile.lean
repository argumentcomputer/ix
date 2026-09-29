import Lake
open Lake DSL

/-! # The certified kernel as its own package

`ix-kernel` builds `Ix.Kernel`, `Ix.Address.Core`, and the pure Ixon
types/codecs/proofs from the repository's `Ix/` tree (`srcDir := ".."`) with
no dependencies beyond the Lean toolchain. Kernel/data import closures use
Lean core only; codec proofs additionally use Lean/Std proof tooling.
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
  roots := #[`Ix.Kernel, `Ix.Address.Core, `Ix.Ixon.Types, `Ix.Ixon.Codec, `Ix.Ixon.Wire,
    `Ix.Ixon.WireCheck, `Ix.Ixon.Bounded.Universe, `Ix.Ixon.Bounded.Constant,
    `Ix.Ixon.Canonical, `Ix.Ixon.Verify, `Ix.Ixon.Audit]
  globs := #[.andSubmodules `Ix.Kernel, .one `Ix.Address.Core, .andSubmodules `Ix.Ixon.Types,
    .one `Ix.Ixon.Codec, .one `Ix.Ixon.Wire, .one `Ix.Ixon.WireCheck, .submodules `Ix.Ixon.Bounded,
    .one `Ix.Ixon.Canonical, .andSubmodules `Ix.Ixon.Verify, .one `Ix.Ixon.Audit]

/-- Certified fixtures also run without the host package's dependencies. -/
def kernelFixtureRoots : Array Lean.Name := #[
  `Tests.Ix.Kernel.Fixtures, `Tests.Ix.Kernel.Inductives,
  `Tests.Ix.Kernel.Structures, `Tests.Ix.Kernel.Literals,
  `Tests.Ix.Kernel.Quotients, `Tests.Ix.Kernel.Axioms,
  `Tests.Ix.Kernel.SearchOutcomes, `Tests.Ix.Kernel.Fidelity,
  `Tests.Ix.Kernel.Ingress, `Tests.Ix.Kernel.Egress, `Tests.Ix.Kernel.Codec]

@[default_target]
lean_lib KernelFixtures where
  srcDir := ".."
  roots := kernelFixtureRoots
  globs := kernelFixtureRoots.map (fun root => .one root)

lean_exe «bench-certified-kernel» where
  srcDir := ".."
  root := `Benchmarks.Kernel.Certified

lean_lib KernelProvenance where
  srcDir := ".."
  roots := #[`Tests.Ix.Kernel.ImportManifest]
  globs := #[.one `Tests.Ix.Kernel.ImportManifest]

lean_exe «kernel-provenance» where
  srcDir := ".."
  root := `Tests.Ix.Kernel.Provenance
