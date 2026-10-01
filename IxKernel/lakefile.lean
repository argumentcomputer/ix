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
    `Ix.Ixon.WireCheck, `Ix.Ixon.Bounded.Universe, `Ix.Ixon.Bounded.Constant, `Ix.Ixon.Bounded.Size,
    `Ix.Ixon.Canonical, `Ix.Ixon.Verify, `Ix.Ixon.Audit,
    `Ix.Ixon.Admission, `Ix.Ixon.Admission.Audit, `Ix.Ixon.ConLecheAdmission,
    `Ix.Ixon.ConLecheConsistency, `Ix.Ixon.Consistency]
  globs := #[.andSubmodules `Ix.Kernel, .one `Ix.Address.Core, .andSubmodules `Ix.Ixon.Types,
    .one `Ix.Ixon.Codec, .one `Ix.Ixon.Wire, .one `Ix.Ixon.WireCheck, .submodules `Ix.Ixon.Bounded,
    .one `Ix.Ixon.Canonical, .andSubmodules `Ix.Ixon.Verify, .one `Ix.Ixon.Audit,
    .andSubmodules `Ix.Ixon.Admission, .one `Ix.Ixon.ConLecheAdmission,
    .one `Ix.Ixon.ConLecheConsistency, .one `Ix.Ixon.Consistency]

/-- Certified fixtures also run without the host package's dependencies: the
Ixon record fixtures, the codec, and the certified entry's byte admission
(the intrinsic kernel's fixtures were retired at L6, plan v4). -/
def kernelFixtureRoots : Array Lean.Name := #[
  `Tests.Ix.Kernel.IxonFixtures, `Tests.Ix.Kernel.Codec,
  `Tests.Ix.Kernel.ByteAdmission, `Tests.Ix.Kernel.ParserWork]

@[default_target]
lean_lib KernelFixtures where
  srcDir := ".."
  roots := kernelFixtureRoots
  globs := kernelFixtureRoots.map (fun root => .one root)

lean_lib KernelProvenance where
  srcDir := ".."
  roots := #[`Tests.Ix.Kernel.ImportManifest]
  globs := #[.one `Tests.Ix.Kernel.ImportManifest]

lean_exe «kernel-provenance» where
  srcDir := ".."
  root := `Tests.Ix.Kernel.Provenance

/-- Con-leche's verified checker core, imported verbatim at `ae0c0c4e` (see
the root `lakefile.lean`, which declares the same library). Lean core only;
`linter.deprecated` is off so the 4.33.0-era sources build under `--wfail`
on 4.34.0 unchanged. Not a default target. The glob is the whole subtree,
as in the root `lakefile.lean` (upstream's `ConLeche/Kernel/NatOpPins.lean`
is not ported, int-4). -/
lean_lib ConLeche where
  srcDir := ".."
  roots := #[`ConLeche]
  globs := #[.submodules `ConLeche]
  leanOptions := #[⟨`linter.deprecated, false⟩]
