import Lake
open Lake DSL

/-! # The certified kernel as its own package

`ix-kernel` builds the certified Ixon checker from the repository sources
(`srcDir := ".."`) with no dependencies beyond the Lean toolchain: the kernel
`Ix.Kernel` (the checker derived from con-leche, and Ix's
boundary beside it: the Ixon reader, pins and prelude, record store,
projection writer, audits), `Ix.Address.Core`, and the pure Ixon
types/codecs/proofs with the certified API `Ix.Ixon.Admission` and its
theorems. Data import closures use Lean core and the kernel only (`Lean` only
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

@[default_target]
lean_lib IxKernel where
  srcDir := ".."
  roots := #[`Ix.Kernel, `Ix.Address.Core, `Ix.Ixon.Types, `Ix.Ixon.Codec, `Ix.Ixon.Wire,
    `Ix.Ixon.WireCheck, `Ix.Ixon.Bounded.Universe, `Ix.Ixon.Bounded.Constant, `Ix.Ixon.Bounded.Size,
    `Ix.Ixon.Canonical, `Ix.Ixon.Verify, `Ix.Ixon.Audit,
    `Ix.Ixon.Admission, `Ix.Ixon.Admission.Audit, `Ix.Ixon.KernelAdmission,
    `Ix.Ixon.KernelConsistency, `Ix.Ixon.Consistency]
  globs := #[.andSubmodules `Ix.Kernel, .one `Ix.Address.Core, .andSubmodules `Ix.Ixon.Types,
    .one `Ix.Ixon.Codec, .one `Ix.Ixon.Wire, .one `Ix.Ixon.WireCheck, .submodules `Ix.Ixon.Bounded,
    .one `Ix.Ixon.Canonical, .andSubmodules `Ix.Ixon.Verify, .one `Ix.Ixon.Audit,
    .andSubmodules `Ix.Ixon.Admission, .one `Ix.Ixon.KernelAdmission,
    .one `Ix.Ixon.KernelConsistency, .one `Ix.Ixon.Consistency]

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

/-- The vendored con-leche modules under `Ix/Kernel`: every module there except
Ix's boundary (`Ref`, `Search`, `Audit`, `Ingress`, `Egress`, `Ixon`), one glob
per top-level entry (`scripts/vendor-conleche.py lake-globs`). -/
def vendoredKernelGlobs : Array Glob := #[
  -- BEGIN vendored kernel modules (scripts/vendor-conleche.py check-lake)
  .andSubmodules `Ix.Kernel.Basis, .one `Ix.Kernel.BasisA, .one `Ix.Kernel.BasisGen,
  .submodules `Ix.Kernel.Cached, .one `Ix.Kernel.Canon, .one `Ix.Kernel.Checker,
  .one `Ix.Kernel.CheckerBase, .one `Ix.Kernel.CheckerSplit, .one `Ix.Kernel.Core,
  .one `Ix.Kernel.CoreDefs, .one `Ix.Kernel.CoreIO, .one `Ix.Kernel.DeclCheck,
  .one `Ix.Kernel.Denotes, .one `Ix.Kernel.Env, .one `Ix.Kernel.Exclusive, .one `Ix.Kernel.Expr,
  .one `Ix.Kernel.ExprOps, .one `Ix.Kernel.FEnv, .submodules `Ix.Kernel.Frontend,
  .submodules `Ix.Kernel.Inductives, .one `Ix.Kernel.Level, .one `Ix.Kernel.LevelGeran,
  .one `Ix.Kernel.MainTheorem, .submodules `Ix.Kernel.Model, .one `Ix.Kernel.Name,
  .one `Ix.Kernel.NatOpPinSet, .submodules `Ix.Kernel.PinGen, .one `Ix.Kernel.PropRead,
  .one `Ix.Kernel.PropWhen, .submodules `Ix.Kernel.Rules, .submodules `Ix.Kernel.Semantics,
  .submodules `Ix.Kernel.SetModel, .submodules `Ix.Kernel.SetTheory, .one `Ix.Kernel.StdAxioms,
  .submodules `Ix.Kernel.Term, .one `Ix.Kernel.TrustAxioms, .one `Ix.Kernel.TrustPins,
  .one `Ix.Kernel.TypeChecker, .submodules `Ix.Kernel.Verify
  -- END vendored kernel modules
]

/-- Con-leche's verified checker, vendored under `Ix/Kernel/**` (see the root
`lakefile.lean`, which declares the same library, and
`Tests/Ix/Kernel/ImportManifest.lean` for the rewritten, adapted and
Ix-authored files). Lean core only; `linter.deprecated` is off so the
4.33.0-era sources build under `--wfail` on 4.34.0 unchanged. Declared after
`IxKernel`, whose root `Ix.Kernel` can build every `Ix.Kernel.*` module: Lake
gives a module to the last-declared library that can build it. Not a default
target (`IxKernel` builds every module under `Ix/Kernel`). -/
lean_lib IxKernelVendored where
  srcDir := ".."
  roots := #[`Ix.Kernel.MainTheorem]
  globs := vendoredKernelGlobs
  leanOptions := #[⟨`linter.deprecated, false⟩]
