# Contributing to Ix

## Updating the Lean toolchain

When a new Lean version is released, all dependencies must update to this version before Ix, as there is not yet a way of checking for a minimal working Lean version a la [Rust MSRV](https://github.com/foresterre/cargo-msrv).

Once all dependencies are up-to-date, then a new version can be tested with `lake`. However, there must also be a working Nix build for the new toolchain, which will be built and cached by https://github.com/argumentcomputer/lean4-nix/blob/dev/.github/workflows/ci.yml. The Nix CI for Ix will automatically pick up any changes to `lean-toolchain` and attempt to use that Lean version with `nix build`, so if the toolchain doesn't have a Nix build yet the CI job will fail.

TODO: Test the Nix build in each Argument repo in CI
