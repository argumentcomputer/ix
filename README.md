# Navigatr.ix

> Navigation machines, built by Ix to replace the Guild's Navigators.
> *Navigatrix* is the feminine agent noun of *navigator* — computers are
> feminine. Styled **Navigatr.ix**; code namespace `Navigatrix`.

An exploration of a certified toolchain for
[ix](https://github.com/argumentcomputer/ix), aiming to eventually replace
the entire Lean 4 reference implementation with a self-hosting, certified
compiler — in the tradition of [CakeML](https://cakeml.org/) — written in
**pure Lean 4** and bootstrapped from upstream Lean as a one-time seed.

Two ideas carry the design:

- **Substructural modes as first-class data.** Ixon v2 (the ix object
  notation, revised here) puts usage annotations directly on binders:
  `Uses = {erased, linear, affine, many}` on Π and λ, plus result
  ownership `Owned = {unique, shared}` on Π. Vanilla Lean 4 is exactly
  the `many`/`shared` fragment; the extension enables Rust-style
  compilation — erasure, in-place reuse, and ultimately GC-free code —
  without changing the kernel's definitional equality.
- **Content addressing as compiler infrastructure.** Every object is
  addressed by the blake3 hash of its canonical serialization, and
  decoding is strict (byte equality ≡ value equality, no address
  splitting). A closed world of hashes makes whole-program compilation
  compatible with incremental caching: GRIN-style analyses over a
  Merkle DAG, with post-fixpoint certificates instead of trusted
  fixpoint computation.

Certification follows the CompCert discipline: executable passes are
validated against relational specifications, semantics are fueled
functional big-step interpreters (executable *and* proof-friendly), and
every claim is either a theorem, a differential test between two
independent semantics, or an explicitly recorded assumption.

## What is implemented

The full spine from kernel language to erased core IR, with the first
correctness theorem connecting them:

| Piece | Modules | Status |
| --- | --- | --- |
| Ixon v2 datatypes + strict canonical codec | `Navigatrix/Ixon/{Serialize,Univ,Expr,Const}.lean` | done; roundtrip + rejection tests |
| blake3 content addressing | `Navigatrix/Ixon/{Address,Hash}.lean`, `Tests.lean` | done; format-freezing golden vectors |
| Usage checker v0 | `Navigatrix/Ixon/UsageCheck.lean` | whole-value modes: QTT 0-fragment ("ghost") checking, move/freeze, no dereliction |
| Reference evaluator (unerased) | `Navigatrix/Ixon/Eval.lean` | frames, universe instantiation, kernel-shaped ι, neutral constants, store-blob literals |
| IxIR₀: the erased core IR | `Navigatrix/IxIR0/{Basic,Eval,Examples}.lean` | curried CBV λ + ctor/recursor/extern globals; fueled interpreter |
| Fuel monotonicity | `Navigatrix/IxIR0/Mono.lean` | proved for all four interpreter functions |
| Erasure pass | `Navigatrix/Erase.lean` | arity-preserving ◻-erasure; differential tests run both evaluators on the same programs |
| **Erasure simulation, stage 1** | `Navigatrix/Sim.lean` | **proved, sorry-free** (axioms: `propext`, `Quot.sound`): source termination implies erased termination with related values, on the pure λ-fragment |

The road ahead (design notes in the untracked `plans/`): simulation
stage 2 (recursors, constructors, literals — already witnessed by the
differential suite), IxIR₀ˢ specialization, IxIR₁ (GRIN-style,
mode-directed memory operations — where linearity pays), native code
generation, and vendoring a
[lean4lean](https://github.com/digama0/lean4lean)-derived theory as the
kernel specification. Opaque dependencies (GMP, syscalls, …) live on a
per-symbol trusted-extern ledger with retirement milestones.

## Building

```sh
nix build                          # library + elaboration-time test suites
nix flake check                    # + the compiled FFI/blake3 golden tests
nix develop -c lake build          # dev loop (or `direnv allow` once)
```

Most tests are elaboration-time `#guard`s and run on every build; the
blake3 golden tests execute FFI and therefore live in a compiled test
binary (`Tests.lean`, run by the flake's `tests` check). The Lean
toolchain is pinned by `lean-toolchain`; the flake supplies everything
else, including the Rust toolchain the Blake3 dependency builds with.

> :warning: **Pre-alpha exploration; interfaces, encodings, and hashes
> roll without notice. Nothing here should be used for any purpose.**

## License

Dual-licensed under Apache 2.0 and MIT, matching ix.
