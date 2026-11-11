# IxCC

The certified compiler of [ix](../README.md), implemented in Lean 4. It
compiles Ixon v4, ix's content-addressed Lean kernel terms, to x86-64. The
goal is end-to-end certification for two back ends, grounded in Ixon and the
certified kernel IxCK: native x86 code that competes with Lean → Clang, and
Aiur, first through a fixed evaluator circuit that runs IxCC's source
evaluator inside a proof system ([end-to-end certification](docs/end-to-end.md)).
IxCC is the project's Lean namespace.

The design combines three ideas:

- **Explicit contracts.** Ixon binders and results record usage,
  ownership, locality and borrowing. The compiler honours them exactly, and
  may prove stronger guarantees where a checker certifies them. They drive
  erasure, reference counting, borrowing and in-place reuse.
- **Kernel-anchored correctness.** Compiled results are meant to equal the
  claimed constant's value in every strong model of the environment the
  certified kernel accepts, with that acceptance and the faithfulness of the
  compiled source to the kernel's reading as premises discharged by proofs.
  Recursion and library replacements go through kernel-checked equation
  theorems.
- **Untrusted heuristics, proved checkers.** Register allocation, reference-
  count placement, inlining and relevance analysis are proposals validated by
  proved checkers, with checked fallbacks.

## Status

Reviewed 2026-11-10. The Phase 1 scalar pipeline and bounded plain-RC compiler
are implemented, from Src through register allocation and the Lir RC runtime to
ELF (`--rc auto|on|off`). `Recheck.sound`, `Recheck.RcReplay.sound`,
`Compiler.compile_sound`, `CompileClaim`, and `Ring0` (`verifyRing0Sip_sound`)
prove the accepted recheck, replay, and claim-verification paths correct
relative to the source evaluator, run on the checked source the front end builds
from the certificate, and the native driver model, on inputs where that source
does not go wrong. Neither the front end's semantic faithfulness to the ingested
program nor the connection to Lean's denotation is proved. The plan to close
both, the *spine* shared by the two back ends, is in the
[certification design](docs/certification-design.md).

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

**Running a compiled program.** `ixcc compile --exe` writes a standalone static
Linux executable, with no C compiler, C library, linker or driver: IxCC lays
out the file and its start-up shell itself, for roots of `Nat` parameters with
a `Nat` or field-less result. The test suites run objects the same way, as
executables IxCC writes with a test shell that serves a host in Lean, so no gate
runs a compiled program through C; C remains in the tree only as test harnesses
for the system linker's acceptance of relocatable objects and for the
processor differential. `ixcc compile --exe --machine` writes a numeric state
machine instead, run by a generic shell that parses and renders nothing: the
program parses its arguments and renders its output in Lean compiled with it
(`lib/IxccExe.lean`). The production shells are trusted code until they are proved,
and effects are planned in stages
([standalone executables](docs/standalone-executables-design.md)).

The [roadmap](docs/roadmap.md) states the fragment exactly, plans the way to
end-to-end certification for both back ends, and keeps the decision register.
Main includes:
- the scalar and bounded plain-RC compiler (`Compiler.Proof`, `CompileClaim`,
  `Ring0`), certificate rechecker (`Recheck`, `Recheck.RcReplay`), proof fences
  and native suites;
- [Ixon v4 ingress](docs/ixon-v4.md) (through the Ixon v4 codec of ix's `IxCK`
  package);
- the x86 target model with its certified
  [encoder](docs/x86-encoded-instructions.md) and
  [stream/ELF layer](docs/x86-stream-objects.md);
- a legacy verifier-side model of an earlier [Aiur](docs/aiur-backend.md)
  bytecode, frozen; neither Aiur route of the plan uses it.

Phase 1.5's resource-checker work, final producer repin and consumer integration
remain incomplete. New upstream Lean-to-Ixon certification provides interfaces
to assess for that integration; it does not yet close the source-adequacy or
resource-contract obligations. The next goal combines Phase 1.5 completion
with a first certified RC heap slice for real `List.reverse`.

The earlier pipeline, the Ixby backend and their measurements are on branch
`jcb/ixby-archive` of the pre-merge `argumentcomputer/Compilatr.ix` repository.

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
- [Roadmap](docs/roadmap.md): mission, milestones, benchmark rungs and the decision register.
- [End-to-end certification](docs/end-to-end.md): the theorems for the x86 and Aiur back ends, and what each trusts.
- [Compiler design](docs/compiler-design.md): the pipeline and its correctness boundary.
- [Trust ledger](docs/trusted-extern-ledger.md): remaining assumptions.

Pre-alpha research software: interfaces, encodings, and hashes may change
without notice.

## License

Dual-licensed under [Apache 2.0](../LICENSE-APACHE) and [MIT](../LICENSE-MIT),
as is the rest of ix.
