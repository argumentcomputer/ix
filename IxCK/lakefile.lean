import Lake
open Lake DSL

/-! # The certified kernel as its own package

`ix-ck` builds the certified Ixon checker with no dependencies beyond the
Lean toolchain: the kernel `IxCK.Kernel` (the checker derived from
con-leche, and Ix's boundary beside it: the certified entry
`Ix.Kernel.Admission` with its theorems, the Ixon reader, pins and prelude,
record store, projection writer, audits), `IxCK.Address.Core`, the pure
Ixon types, codecs and their proofs under `IxCK.Ixon`, and the certified
fixtures under `IxCK.Fixtures`. Module names live under the `IxCK`
root so the root package's `Ix` library never shadows them, and the source
root is the repository (`srcDir := ".."`), so this package directory is the
`IxCK` module directory, as `Ix/` is for the root package; declaration
namespaces (`Ix.Kernel.*`, `Ixon.*`) are unchanged. Data
import closures use Lean core and the kernel only (`Lean` only at elaboration
time, in the kernel's ruled generators); proofs additionally use Lean/Std
proof tooling.
The root `ix` package depends on this package for its host consumers; this
package is what the certified gate builds (`lake -d IxCK build --wfail`),
so a kernel module that imports anything outside the kernel fails here even
if it would build inside the root workspace, and it is what
`Models/SetTheory` depends on, so the model's workspace holds Mathlib and the
kernel only. See `docs/kernel.md`. -/

package «ix-ck» where
  version := v!"0.1.0"
  /- `Package.buildDir` is relative to the package directory, so this resolves
  to `<repo>/.lake/kernel` from this package, the root workspace,
  `Models/SetTheory` and `Benchmarks/Compile` alike: one artifact set, which
  `flake.nix` also adds to `LEAN_PATH`. `lake -d IxCK clean` deletes it
  for every workspace. -/
  buildDir := "../.lake/kernel"
  moreLeancArgs :=
    if (get_config? profile).isSome then #["-fno-omit-frame-pointer"] else #[]

/-- `IxCK.Kernel` and every module under `IxCK/Kernel/`, with
`linter.deprecated` off for the con-leche-derived sources written for Lean
4.33.0. The glob, not the root's import closure, is what makes the standalone
build cover every kernel module and audit. -/
@[default_target]
lean_lib IxCK.Kernel where
  srcDir := ".."
  roots := #[`IxCK.Kernel]
  globs := #[.andSubmodules `IxCK.Kernel]
  leanOptions := #[⟨`linter.deprecated, false⟩]

/-- The pure Ixon types, codecs and their proofs, which the certified entry
decodes with, and the address key. A separate library so the kernel's
`linter.deprecated` option does not reach the codec. -/
@[default_target]
lean_lib IxCK.Ixon where
  srcDir := ".."
  roots := #[`IxCK.Address.Core, `IxCK.Ixon]
  globs := #[.one `IxCK.Address.Core, .submodules `IxCK.Ixon]

/-- The hosts' side of the kernel's limits: each field of
`Admission.Limits` as a flag and an `IX_KERNEL_*` variable, the decline
message and the exit codes (`IxCK.Host.Limits`). Outside the certified
closure: no `IxCK.Kernel` module imports it. -/
@[default_target]
lean_lib IxCK.Host where
  srcDir := ".."
  roots := #[`IxCK.Host.Limits]
  globs := #[.submodules `IxCK.Host]

/-- Certified fixtures that also build without the host package's
dependencies: the Ixon record fixtures, the codec, and the certified entry's
byte admission. The root test library imports them. -/
@[default_target]
lean_lib IxCK.Fixtures where
  srcDir := ".."
  roots := #[`IxCK.Fixtures]
  globs := #[.submodules `IxCK.Fixtures]
