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
    `Ix.Ixon.Admission, `Ix.Ixon.Admission.Audit, `Ix.Ixon.ConLecheAdmission]
  globs := #[.andSubmodules `Ix.Kernel, .one `Ix.Address.Core, .andSubmodules `Ix.Ixon.Types,
    .one `Ix.Ixon.Codec, .one `Ix.Ixon.Wire, .one `Ix.Ixon.WireCheck, .submodules `Ix.Ixon.Bounded,
    .one `Ix.Ixon.Canonical, .andSubmodules `Ix.Ixon.Verify, .one `Ix.Ixon.Audit,
    .andSubmodules `Ix.Ixon.Admission, .one `Ix.Ixon.ConLecheAdmission]

/-- Certified fixtures also run without the host package's dependencies. -/
def kernelFixtureRoots : Array Lean.Name := #[
  `Tests.Ix.Kernel.Fixtures, `Tests.Ix.Kernel.Inductives,
  `Tests.Ix.Kernel.Structures, `Tests.Ix.Kernel.Literals,
  `Tests.Ix.Kernel.Quotients, `Tests.Ix.Kernel.Axioms,
  `Tests.Ix.Kernel.SearchOutcomes, `Tests.Ix.Kernel.ConversionSpines,
  `Tests.Ix.Kernel.ProofIrrelevance, `Tests.Ix.Kernel.AnnotationContexts,
  `Tests.Ix.Kernel.SubstitutionSharing, `Tests.Ix.Kernel.RuntimeStack,
  `Tests.Ix.Kernel.Fidelity,
  `Tests.Ix.Kernel.Ingress, `Tests.Ix.Kernel.Egress, `Tests.Ix.Kernel.Codec,
  `Tests.Ix.Kernel.ByteAdmission, `Tests.Ix.Kernel.ParserWork]

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

/-- Con-leche's verified checker core, imported verbatim at `ae0c0c4e` (see
the root `lakefile.lean`, which declares the same library). Lean core only;
`linter.deprecated` is off so the 4.33.0-era sources build under `--wfail`
on 4.34.0 unchanged. Not a default target. The globs list every file of the
subtree except `ConLeche/Kernel/NatOpPins.lean`, which is not built (see the
root `lakefile.lean`, whose globs these copy). -/
lean_lib ConLeche where
  srcDir := ".."
  roots := #[`ConLeche]
  globs := #[.submodules `ConLeche.Cached, .one `ConLeche.Denotes, .submodules `ConLeche.Frontend,
    .andSubmodules `ConLeche.Kernel.Basis, .submodules `ConLeche.Kernel.Inductives,
    .one `ConLeche.MainTheorem, .submodules `ConLeche.Model, .submodules `ConLeche.PinGen,
    .submodules `ConLeche.Rules, .submodules `ConLeche.Semantics, .submodules `ConLeche.SetModel,
    .submodules `ConLeche.SetTheory, .submodules `ConLeche.Term, .submodules `ConLeche.Verify] ++
    #[`BasisA, `BasisGen, `Canon, `CheckerBase, `Checker, `CheckerSplit, `CoreDefs, `CoreIO, `Core,
      `DeclCheck, `Env, `Exclusive, `Expr, `ExprOps, `FEnv, `Level, `Name, `NatOpPinSet, `PropRead,
      `PropWhen, `StdAxioms, `TrustAxioms, `TrustPins, `TypeChecker].map
      (fun n => .one (`ConLeche.Kernel ++ n))
  leanOptions := #[⟨`linter.deprecated, false⟩]
