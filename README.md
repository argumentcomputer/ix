# Compilatr.ix

A certified compiler for [ix](https://github.com/argumentcomputer/ix),
implemented in Lean 4. The long-term goal is a self-hosting toolchain from
Ixon source objects to native and zk targets, bootstrapped from upstream Lean.
Compilatrix is the project's Lean namespace.

The design combines two ideas:

- **Explicit ownership.** Ixon binders record erased, linear, affine, or
  unrestricted use; function results record unique or shared ownership. These
  contracts guide erasure, reference counting, borrowing, and in-place reuse.
- **Content-addressed compilation.** Canonical source and IR objects carry
  dependency identities. Analyses and optimization proposals pass bounded Lean
  checkers before changing an artifact, supporting incremental compilation
  without trusting the analysis producer.

## What works

The validated pipeline compiles the supported Ixon fragment to owned IxIR₁.
Checked attachments extend it to IxIR₂ and selected x86-64 programs.

| Area | Current scope |
| --- | --- |
| Source and identity | Strict Ixon codecs, bounded catalog ingress, checked erasure, cycle-safe IxIR₀/IxIR₁ addressing, and canonical [IxIR₂ snapshots](docs/ixir2-wire.md) |
| Ownership and optimization | Checked shape analysis, shrinking passes, shared and unique reuse, borrowed calls, and resource/reclamation proofs |
| Native code | Source-to-ELF proofs for selected families and physical scalar CFGs, including static Word captures, runtime application, closure reclamation, branches, joins, direct calls, and finite stack proofs |
| Validation | Axiom fences, independent artifact/ABI checks, malformed-input tests, fresh-process reproducibility, and retained performance experiments |

Native support is still bounded. Runtime reversal accepts at most 64 exact
64-bit payloads; physical IxIR₂ selection covers a bounded scalar fragment.
Broader recursion, shared native heaps, and self-hosting remain open. Theorems
retain their stated source, ownership, and environment premises. Reference ISA agreement and
system linker/loader behavior remain explicit assumptions.

See the [roadmap](docs/roadmap.md) for current priorities and delivery scope,
and the [trust ledger](docs/trusted-extern-ledger.md) for remaining assumptions.

## Build and check

```sh
nix build                          # library and elaboration-time tests
nix flake check                    # complete CI validation
nix develop -c lake build          # local development build
lake exe catalog-contact -- DIR    # load a bounded ix catalog
```

The repository pins Lean in `lean-toolchain` and its dependencies in the Nix
flake. See [development and validation](docs/development-plan.md) for individual
checks, platform coverage, and build troubleshooting.

## Documentation

Start with the [documentation guide](docs/README.md), then choose a path:

- [Compiler design](docs/compiler-design.md): architecture, ownership, identity,
  and proof boundaries.
- [Roadmap](docs/roadmap.md): active work, acceptance criteria, and conditional
  extensions.
- [Performance](docs/performance/README.md): native comparisons with Lean 4,
  CakeML, CompCert, GCC, and Clang, plus the checked counter-fold experiment.
- [Benchmark protocol](benchmarks/protocol.md): build, check, measure, and
  reproduce the implemented suite.

Pre-alpha research software: interfaces, encodings, and hashes may change
without notice.

## License

Dual-licensed under [Apache 2.0](LICENSE-APACHE) and [MIT](LICENSE-MIT),
matching ix.
