import Lake
open Lake DSL

/-! # The certified kernel as its own package

`ix-kernel` builds the certified Ixon checker with no dependencies beyond the
Lean toolchain: the kernel `IxKernel.Kernel` (the checker derived from
con-leche, and Ix's boundary beside it: the certified entry
`Ix.Kernel.Admission` with its theorems, the Ixon reader, pins and prelude,
record store, projection writer, audits), `IxKernel.Address.Core`, the pure
Ixon types, codecs and their proofs under `IxKernel.Ixon`, and the certified
fixtures under `IxKernel.Fixtures`. Module names live under the `IxKernel`
root so the root package's `Ix` library never shadows them, and the source
root is the repository (`srcDir := ".."`), so this package directory is the
`IxKernel` module directory, as `Ix/` is for the root package; declaration
namespaces (`Ix.Kernel.*`, `Ixon.*`) are unchanged. Data
import closures use Lean core and the kernel only (`Lean` only at elaboration
time, in the kernel's ruled generators); proofs additionally use Lean/Std
proof tooling.
The root `ix` package depends on this package for its host consumers; this
package is what the certified gate builds (`lake -d IxKernel build --wfail`),
so a kernel module that imports anything outside the kernel fails here even
if it would build inside the root workspace, and it is what
`Models/SetTheory` depends on, so the model's workspace holds Mathlib and the
kernel only. See `docs/kernel.md`. -/

package «ix-kernel» where
  version := v!"0.1.0"
  /- `Package.buildDir` is relative to the package directory, so this resolves
  to `<repo>/.lake/kernel` from this package, the root workspace,
  `Models/SetTheory` and `Benchmarks/Compile` alike: one artifact set, which
  `flake.nix` also adds to `LEAN_PATH`. `lake -d IxKernel clean` deletes it
  for every workspace. -/
  buildDir := "../.lake/kernel"
  moreLeancArgs :=
    if (get_config? profile).isSome then #["-fno-omit-frame-pointer"] else #[]

/-- `IxKernel.Kernel` and every module under `IxKernel/Kernel/`, with
`linter.deprecated` off for the con-leche-derived sources written for Lean
4.33.0. The glob, not the root's import closure, is what makes the standalone
build cover every kernel module and audit. -/
@[default_target]
lean_lib IxKernelTree where
  srcDir := ".."
  roots := #[`IxKernel.Kernel]
  globs := #[.andSubmodules `IxKernel.Kernel]
  leanOptions := #[⟨`linter.deprecated, false⟩]

/-- The pure Ixon types, codecs and their proofs, which the certified entry
decodes with, and the address key. A separate library so the kernel's
`linter.deprecated` option does not reach the codec. -/
@[default_target]
lean_lib IxKernel where
  srcDir := ".."
  roots := #[`IxKernel.Address.Core, `IxKernel.Ixon]
  globs := #[.one `IxKernel.Address.Core, .submodules `IxKernel.Ixon]

/-- Certified fixtures that also build without the host package's
dependencies: the Ixon record fixtures, the codec, and the certified entry's
byte admission. The root test library imports them. -/
@[default_target]
lean_lib IxKernelFixtures where
  srcDir := ".."
  roots := #[`IxKernel.Fixtures]
  globs := #[.submodules `IxKernel.Fixtures]
