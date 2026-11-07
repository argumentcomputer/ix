# IxCC

A certified compiler for [ix](https://github.com/argumentcomputer/ix),
implemented in Lean 4. It compiles Ixon v4, ix's content-addressed Lean
kernel terms, to x86-64. The goal is certified native code that competes
with Lean → Clang. IxCC is the project's Lean namespace.

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

Reviewed 2026-10-08. The Phase 1 scalar pipeline is implemented, from Src
through register allocation to ELF. `Recheck.sound` proves the accepted
recheck path correct relative to the source evaluator and the native driver
model; the connection to Lean's denotation remains open. See the
[roadmap](docs/roadmap.md) for scope and remaining work. Main includes:
- the scalar compiler, certificate rechecker, proof fences and native suites;
- [Ixon v4 ingress](docs/ixon-v4.md) (through ix's pinned Ixon v4 codec);
- the x86 target model with its certified
  [encoder](docs/x86-encoded-instructions.md) and
  [stream/ELF layer](docs/x86-stream-objects.md);
- the [Aiur target](docs/aiur-backend.md).

Phase 1.5's resource-checker work, final producer repin and consumer integration
remain incomplete. New upstream Lean-to-Ixon certification provides interfaces
to assess for that integration; it does not yet close the source-adequacy or
resource-contract obligations. The next goal combines Phase 1.5 completion
with a first certified RC heap slice for real `List.reverse`.

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
- [Compiler design](docs/compiler-design.md): the pipeline and its correctness boundary.
- [Trust ledger](docs/trusted-extern-ledger.md): remaining assumptions.

Pre-alpha research software: interfaces, encodings, and hashes may change
without notice.

## License

Dual-licensed under [Apache 2.0](LICENSE-APACHE) and [MIT](LICENSE-MIT),
matching ix.
