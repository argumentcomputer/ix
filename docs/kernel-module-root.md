# Design: moving the certified kernel out of the `Ix.` module namespace

Status: implemented on top of the `ix-kernel` dependency restructuring
(root `lakefile.lean` requires `IxC/`). Two details were settled
during implementation and are not in the plan below: the sharing audits in
`IxSharingVerify/Audit/` accept the `IxSharingVerify` module prefix alongside
`Ix.Sharing`, since their scope was defined by module name; and the
`check-kernel` host step no longer lists the four fixtures, which the
standalone step already builds.

## Problem

The certified kernel package `ix-kernel` owns modules whose names live under
the root package's `Ix.` module root: `Ix.Kernel.*`, `Ix.Address.Core` and
the Ixon codec modules under `Ix.Ixon.*`. Lake resolves a module to the root
package before dependencies and, inside a package, to the last-declared
library that can build it. A library rooted at `` `Ix `` can build every
`Ix.*` module, so the root package cannot declare `lean_lib Ix` with default
roots without shadowing the dependency's modules.

The current workaround is an explicit list of 45 namespace roots for `Ix`,
an `IxImports` umbrella library so the default build stays narrow, an
`IxCertified` library for the root-owned `Ix.Ixon.*` extensions, and a
`roots := #[]` on `IxImports` whose only purpose is to avoid the shadowing.
Nothing checks the list: a new `Ix/Foo.lean` is silently owned by no library.
The standalone kernel package also reads its sources from the repository
root (`srcDir := ".."`), and the four certified fixture modules
`Tests.Ix.Kernel.{IxonFixtures,Codec,ByteAdmission,ParserWork}` lost their
dependency-free build because the root `Tests` library and the dependency
would otherwise own them twice.

Every one of these follows from the kernel sharing the `Ix.` module root
with its consumer.

## Proposal

Move the dependency-owned modules to a module root of their own, `IxC` (Ix
Certified). Module paths change by one prefix substitution,
`Ix.` to `IxC.`, so every module path still mirrors its declaration
namespace. Declaration namespaces and import relationships do not change.

| Today | After |
| --- | --- |
| `Ix.Kernel`, `Ix.Kernel.X` | `IxC.Kernel`, `IxC.Kernel.X` |
| `Ix.Address.Core` | `IxC.Address.Core` |
| `Ix.Ixon.Types`, `Ix.Ixon.Codec`, `Ix.Ixon.Wire`, `Ix.Ixon.WireCheck`, `Ix.Ixon.Bounded.*`, `Ix.Ixon.Canonical`, `Ix.Ixon.Verify.*`, `Ix.Ixon.Audit` | the same under `IxC.Ixon.` |
| `Tests.Ix.Kernel.{IxonFixtures,Codec,ByteAdmission,ParserWork}` | `IxC.Fixtures.{IxonFixtures,Codec,ByteAdmission,ParserWork}` |

### What moves

| Item | Size |
| --- | --- |
| Files to relocate: 513 `.lean`, the four fixtures, `NOTICE`, `LICENSE-CON-LECHE` | 519 |
| Import lines to rewrite, in every form (`import`, `public import`, `import all`, `public meta import`), including kernel-internal ones | 1,298 in 526 files |
| Module-name `Name` literals in the audit allowlists and denylists (`Ix/Kernel/Audit/Roots.lean`, `Ix/Kernel/Admission/Audit.lean`, `Ix/Ixon/Audit.lean`, `Ix/Ixon/Projection/Audit.lean`, `Ix/Ixon/BlockOrder/Audit.lean`, `Ix/Resource/Audit.lean`) and the `#guard` lines that exercise them | about 130 lines |
| Module-name and path strings in the fences (`Tests/Ix/Kernel/{Layering,KernelLayout,TrustSurface}.lean`) | 19 module strings, 13 path strings |
| Module targets in the `check-kernel` script | 13 |
| Documentation: `docs/kernel.md` (about 110), `Models/SetTheory/README.md`, `Benchmarks/Kernel/README.md`, `docs/Ixon.md`, `docs/sharing-minimum*.md`, `README.md`, the pin-gen usage text | about 135 |
| Rust comments | 8 lines in 5 files |

Nothing in `.github/workflows/` or `flake.nix` names these modules; the flake
needs only the `name` change in step 5. No destination path collides with an
existing file, and the eight root-owned modules under `Ix/Ixon/` and
`Ix/Address/` (`Projection*`, `BlockOrder*`, `ReduceUniverse`, `Pure`) stay
where they are.

### Rewrite hazards

- **Every import form.** A count of bare `import` lines finds only 570 of
  the 1,298; `public import` carries 703.
- **Module names next to declaration names.** The audit files hold module
  literals such as `` `Ix.Kernel.Admission `` in the same arrays and
  `#guard`s as declaration literals such as
  `` `Ix.Kernel.Admission.checkBytes_has_model ``. The former change, the
  latter do not, and no regex separates them reliably. Those lists are edited
  by hand against the mapping table, not by the import script.
- **`Ix.KernelCheck`.** The root-owned `Ix/KernelCheck.lean` (35 qualified
  references, 5 path references) shares a prefix with `Ix.Kernel`. Every
  pattern must anchor on `Ix.Kernel` followed by `.`, whitespace, or end of
  name, and on `Ix/Kernel` followed by `/` or `.lean`.
- **The layering fence scans sources by regex.** `Layering.lean` finds
  imports in files under `KernelLayout.root` and compares module names
  against literal `"Ix.Kernel.…"` prefixes; `TrustSurface.lean` keys its
  token allowlist by file path. Both move with the sources and both need
  their strings updated in the same commit, or the fences pass vacuously
  ("no kernel modules under `Ix/Kernel/`; nothing to check").

### What stays put

Declaration namespaces. The kernel tree opens `namespace Ix.Kernel…` 487
times and the codec uses `Ixon` and `Univ`. Lean does not tie a
declaration's namespace to its module name, so `IxC/Kernel/Admission.lean`
keeps `namespace Ix.Kernel.Admission`, and the roughly 9,000 qualified
references to `Ix.Kernel.*` constants across the repository, the axiom pins,
and the `#guard_kernel_axioms` records stay valid.

Import relationships. `Ix/Ixon.lean` and `Ix/Address.lean` are ordinary
root-owned modules (the host-side Ixon metadata and the BLAKE3 address),
not umbrellas. Their imports of the codec and of `Address.Core` are
rewritten like any other; nothing new enters any import closure. In
particular `Ix.Ixon.Projection` and `Ix.Ixon.BlockOrder` keep their current
nine importers and are not added to `Ix.Ixon`, which would pull the certified
checker and pure hashing into `Ix`'s closure.

The Rust side. Its `ix_kernel*` references are explicit FFI symbol names
(`@[export]` and `extern`), which do not derive from module paths.

The con-leche attribution. Only the paths in the NOTICE file change.

### Layout

The package keeps the repository as its source root (`srcDir := ".."`), so
the package directory is the `IxC` module directory, the way `Ix/` is
for the root package:

```
IxC/
  lakefile.lean
  lake-manifest.json
  lean-toolchain
  Kernel.lean                   (was Ix/Kernel.lean)
  Kernel/
    Admission.lean              (was Ix/Kernel/Admission.lean)
    Admission/...
    Audit/...
    NOTICE
    ...
  Address/Core.lean             (was Ix/Address/Core.lean)
  Ixon/
    Types.lean                  (was Ix/Ixon/Types.lean)
    Types/...
    Codec.lean
    ...
  Fixtures/
    IxonFixtures.lean           (was Tests/Ix/Kernel/IxonFixtures.lean)
    Codec.lean
    ByteAdmission.lean
    ParserWork.lean
```

### Libraries in `IxC/lakefile.lean`

Today's two libraries are kept, relocated, plus one for the fixtures. Each
has its own root, and no library globs a root that another library owns, so
ownership never depends on declaration order:

```lean
@[default_target]
lean_lib IxC.Kernel where
  srcDir := ".."
  roots := #[`IxC.Kernel]
  globs := #[.andSubmodules `IxC.Kernel]
  leanOptions := #[⟨`linter.deprecated, false⟩]

@[default_target]
lean_lib IxC.Ixon where
  srcDir := ".."
  roots := #[`IxC.Address.Core, `IxC.Ixon]
  globs := #[.one `IxC.Address.Core, .submodules `IxC.Ixon]

@[default_target]
lean_lib IxC.Fixtures where
  srcDir := ".."
  roots := #[`IxC.Fixtures]
  globs := #[.submodules `IxC.Fixtures]
```

Two points are deliberate:

- **Explicit globs, not default roots.** A library with default globs builds
  only its root module's import closure, and the `Ix.Kernel` umbrella imports
  nine modules, omitting `Admission` and every audit. The `.andSubmodules`
  glob is what makes `lake -d IxC build --wfail` build every kernel
  module and audit, as it does today.
- **Two libraries, not one.** `linter.deprecated := false` exists for the
  con-leche-derived sources and must not extend to the codec, which is
  written for the current toolchain. A single library over the whole package
  would silence deprecation warnings in the codec. The umbrella
  `IxC/Kernel.lean` is owned by `IxC.Kernel` as today.

## Resulting root `lakefile.lean`

- `lean_lib Ix` returns to default roots and globs. The `ixRoots` list,
  `IxImports` and `IxCertified` are deleted. A new `Ix/Foo.lean` is owned by
  `Ix` automatically.
- The root `Tests` library imports the fixtures from `IxC.Fixtures`
  instead of owning them, which restores the standalone fence: a fixture that
  gains a host import fails `lake -d IxC build --wfail` again.
- `IxSharingVerify` (`Ix.Sharing.Verify.*`, 33 files) still overlaps a
  default-rooted `Ix`, exactly as at the branch point, and is owned by it
  only because it is declared later. Giving it a sibling root
  (`IxSharingVerify.*`, same prefix-substitution rule, namespaces unchanged)
  removes the last declaration-order dependency in the root lakefile. This
  is a 33-file rename with 64 internal import lines and no importer outside
  the tree, so it should ride in the same pull request; if it is deferred,
  the lakefile keeps a comment stating the ordering rule for that one
  library.

## Steps

1. `git mv` the 513 files to the layout above, so history follows.
2. Rewrite the imports with a script that matches every import form. The
   mapping is one prefix substitution on the dependency-owned module set, and
   the four fixture modules map to `IxC.Fixtures.*`.
3. Edit by hand, against the mapping table, the places that hold module
   names as data rather than imports: the allowlist and denylist arrays and
   `#guard`s in the six audit files, the module and path strings in
   `Layering.lean`, `KernelLayout.lean` (`root`) and `TrustSurface.lean`,
   the 13 module targets in the `check-kernel` script, the pin-gen usage
   text and output paths, and the directory list in `sourceFingerprint` in
   `Benchmarks/Kernel/CheckIxePaired.lean`.
4. Declare the three libraries above, delete `ixRoots`, `IxImports` and
   `IxCertified`, and point the root tests at `IxC.Fixtures` (today one
   root test, `Tests.Ix.Kernel.Projection`, imports a fixture).
5. In `flake.nix`, set the library derivation's `name` back to `"Ix"`
   (it currently builds `IxImports`). Keep the `buildDir := "../.lake/kernel"`
   override and the `LEAN_PATH` entries until the packaging replacement
   described below exists.
6. Update `docs/kernel.md` (including the `LICENSE-CON-LECHE` path),
   `README.md`, `Models/SetTheory/README.md`, `Benchmarks/Kernel/README.md`,
   the Ixon and sharing docs, the NOTICE file, and the eight Rust comment
   lines.
7. Rebuild and validate every consumer, since every kernel olean changes
   name:
   - `lake run check-kernel --with-model` (standalone gate, host tests,
     model);
   - `lake build ix IxTests` and `lake test` (application and test
     executables link and run);
   - `lake lint` (every library and executable under `--wfail`);
   - `nix build .#ix` and `nix flake check` (packaging, wrappers,
     `LEAN_PATH`);
   - the Benchmarks/Compile and Benchmarks/Kernel workspaces resolve the
     dependency (`lake -d Benchmarks/Compile build` of one target).

## What this does not change

- The nix workaround for path dependencies in `flake.nix` (`removeAttrs` on
  the manifest, the hand-written `package-overrides.json`). That belongs in
  lean4-nix.
- The shared artifact directory. With the sources inside the package
  directory, Lake's default `IxC/.lake/build` is already one location
  for every workspace that requires the package by path. The
  `buildDir := "../.lake/kernel"` override survives until lean4-nix exports
  path dependencies' artifacts and CI caches that directory; it is not
  removed by this change.
- The profile-flag plumbing (`require ... with` and `moreLeancArgs`).

## Migrating a local checkout

A checkout that built the intermediate layout (the root requiring
`ix-kernel` before this move) still holds the old `Ix/` olean tree under
`.lake/kernel/lib/lean/` and `.lake/kernel/ir/`. Lean's module loader takes
the first search-path entry whose root directory exists, and the dependency's
entries precede the root's, so that stale `Ix/` directory shadows every
`Ix.*` module at runtime (`lake test` fails loading `Ix.Common`). Delete
`.lake/kernel` once after switching; a fresh checkout and CI never see it.

## Cost and timing

Roughly a day of scripted work plus one full kernel rebuild to verify. It is a
500-file rename that will conflict with any open branch touching
`Ix/Kernel`, so it should be its own pull request, made right after the
dependency restructuring lands and before further kernel work starts.
Namespaces stay as they are; renaming them would touch the con-leche-derived
proofs and the 9,000 qualified references for no build-system benefit.
