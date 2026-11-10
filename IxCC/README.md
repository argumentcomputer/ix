# IxCC

The certified compiler of [ix](../README.md), implemented in Lean 4. It
compiles Ixon v4, ix's content-addressed Lean kernel terms, to x86-64. The
goal is certified native code that competes with Lean → Clang. IxCC is the
project's Lean namespace.

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

Reviewed 2026-11-09. The Phase 1 scalar pipeline and bounded plain-RC compiler
are implemented, from Src through register allocation and the Lir RC runtime to
ELF (`--rc auto|on|off`). `Recheck.sound`, `Recheck.RcReplay.sound`,
`Compiler.compile_sound`, `CompileClaim`, and `Ring0` (`verifyRing0Sip_sound`)
prove the accepted recheck, replay, and claim-verification paths correct
relative to the source evaluator, run on the checked source the front end builds
from the certificate, and the native driver model, on inputs where that source
does not go wrong. Neither the front end's semantic faithfulness to the ingested
program nor the connection to Lean's denotation is proved.

**What compiles today.** First-order Lean programs over `Nat` (below 2^63 at
run time; a larger value is a resource failure) and inductive types, with
recursion through equation theorems. Higher-order code compiles only where
inlining and specialisation remove every closure. Memory is immortal or
bounded plain reference counting (constructors of up to 31 fields). Roots
take at most five `Nat` arguments and return a `Nat`, an enumeration or a
first-order constructor tree. Fixed-width integers at or above 2^63,
arrays, byte arrays, strings, bignums and IO are not supported.

**What is proved.** An accepted object refines the source evaluator on the
checked source program, unless that source goes wrong (gets stuck, traps or
returns a value its type does not read back), under the x86, loader and
driver assumptions of the [trust ledger](docs/trusted-extern-ledger.md). That
the checked source, which the front end builds from the certificate, is
semantically faithful to the ingested program is not proved, and neither is
that it means the Lean definition.

The [roadmap](docs/roadmap.md) states the fragment exactly and plans the
way to a generally useful certified compiler, with two flagship targets.
Main includes:
- the scalar and bounded plain-RC compiler (`Compiler.Proof`, `CompileClaim`,
  `Ring0`), certificate rechecker (`Recheck`, `Recheck.RcReplay`), proof fences
  and native suites;
- [Ixon v4 ingress](docs/ixon-v4.md) (through the Ixon v4 codec of ix's `IxCK`
  package);
- the x86 target model with its certified
  [encoder](docs/x86-encoded-instructions.md) and
  [stream/ELF layer](docs/x86-stream-objects.md);
- a verifier-side model of [Aiur](docs/aiur-backend.md) bytecode, pinned from
  an earlier ix revision; no IxCC IR lowers to it yet.

Phase 1.5's resource-checker work, final producer repin and consumer integration
remain incomplete. New upstream Lean-to-Ixon certification provides interfaces
to assess for that integration; it does not yet close the source-adequacy or
resource-contract obligations. The next goal combines Phase 1.5 completion
with a first certified RC heap slice for real `List.reverse`.

The earlier pipeline, the Ixby backend and their measurements are on branch
`jcb/ixby-archive`.

## Build and check

IxCC lives in ix under `IxCC/`, as its own Lake package (`«ix-cc»`). It
requires the `IxCK` package beside it (`../IxCK`, of which it imports only
the Ixon codec) and Blake3, and nothing of ix's root package. ix's flake
builds it and exposes its required checks as `ixcc-*`:

```sh
nix build .#ixcc                   # production library
nix run .#ixcc -- --help           # the compiler's command line
nix build .#checks.x86_64-linux.ixcc-suites  # one required check (docs/ci.md)
nix develop -c lake build          # local development build, from IxCC/
```

Nix finds ix's `flake.nix` from inside `IxCC/`. `lean-toolchain` must equal
ix's, and the Nix inputs are ix's `flake.lock`; the trust ledger records
both. CI runs every `ixcc-*` check from `.github/workflows/ixcc.yml`. See
[development and validation](docs/development-plan.md) for individual checks
and build troubleshooting.

## Documentation

Start with the [documentation guide](docs/README.md):
- [Roadmap](docs/roadmap.md): mission, phases, benchmark rungs and decisions.
- [Compiler design](docs/compiler-design.md): the pipeline and its correctness boundary.
- [Trust ledger](docs/trusted-extern-ledger.md): remaining assumptions.

Pre-alpha research software: interfaces, encodings, and hashes may change
without notice.

## License

Dual-licensed under [Apache 2.0](../LICENSE-APACHE) and [MIT](../LICENSE-MIT),
as is the rest of ix.
