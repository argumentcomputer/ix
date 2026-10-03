# Compilatr.ix

A certified compiler for [ix](https://github.com/argumentcomputer/ix),
implemented in Lean 4. It compiles Ixon v4, ix's content-addressed Lean
kernel terms, to x86-64. The goal is certified native code that competes
with Lean → Clang. Compilatrix is the project's Lean namespace.

The design combines three ideas:

- **Explicit contracts.** Ixon binders and results record usage,
  ownership, locality and borrowing. The compiler honours them exactly, and
  may prove stronger guarantees where a checker certifies them. They drive
  erasure, reference counting, borrowing and in-place reuse.
- **Kernel-anchored correctness.** Compiled results are meant to equal the
  Lean definition's value in every model of the checked environment.
  Recursion and library replacements go through kernel-checked equation
  theorems.
- **Untrusted heuristics, proved checkers.** Register allocation, reference-
  count placement, inlining and relevance analysis are proposals validated by
  proved checkers, with checked fallbacks.

## Status

The compiler is being rebuilt (2026-09-29); see the
[roadmap](docs/roadmap.md). Main currently holds:
- [Ixon v4 ingress](docs/ixon-v4.md) (through ix's pinned Ixon v4 codec);
- the x86 target model with its certified
  [encoder](docs/x86-encoded-instructions.md) and
  [stream/ELF layer](docs/x86-stream-objects.md);
- the [Aiur target](docs/aiur-backend.md).

The earlier pipeline, the Ixby backend and their measurements are on branch
`jcb/ixby-archive`.

## Build and check

```sh
nix build                          # production library
nix flake check                    # required checks (docs/ci.md)
nix develop -c lake build          # local development build
```

The repository pins Lean in `lean-toolchain` and its dependencies in the Nix
flake. See [development and validation](docs/development-plan.md) for
individual checks and build troubleshooting.

## Documentation

Start with the [documentation guide](docs/README.md):
- [Roadmap](docs/roadmap.md): mission, phases, benchmark rungs and decisions.
- [Compiler design](docs/compiler-design.md): the pipeline being built.
- [Trust ledger](docs/trusted-extern-ledger.md): remaining assumptions.

Pre-alpha research software: interfaces, encodings, and hashes may change
without notice.

## License

Dual-licensed under [Apache 2.0](LICENSE-APACHE) and [MIT](LICENSE-MIT),
matching ix.
