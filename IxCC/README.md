# IxCC

The certified compiler of [ix](../README.md), implemented in Lean 4. It
compiles Ixon v5, ix's content-addressed Lean kernel terms, to x86-64. The
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

Reviewed 2026-11-21. The Phase 1 scalar pipeline, general plain-RC compiler
(`Rt.Rc.Gen` + proved ownership checker `Own.Plain.checkOwned`), closed-world
defunctionalisation (P8), standalone executables (`--exe`, `--machine`), and
the certified-kernel front end (`Src.KernelFront`) are implemented, from Src
through register allocation and the Lir RC runtime to ELF (`--rc auto|on|off`).
`Recheck.sound`, `Recheck.RcReplay.sound`,
`Compiler.compile_sound`, `CompileClaim`, and `Ring0` (`verifyRing0Sip_sound`)
prove the accepted recheck, replay, and claim-verification paths correct
relative to the source evaluator, run on the checked source the front end builds
from the certificate, and the native driver model, on inputs where that source
does not go wrong. The grounding library (`IxCCGrounding`, SP-1 in progress)
discharges SrcEval soundness over IxCK's model (`IxCK.Kernel.Model` directly via
`Laws678`) on a growing fragment (45 of 50 committed corpus closures through
the Pc family). The plan to complete the
*spine* shared by the two back ends is in the
[certification design](docs/certification-design.md).

**What compiles today (two distinct paths).**
- **Certified replay path** (`ixcc compile`, `--rc off|on|auto`, `--exe`,
  `--machine`, `--embed-cert`, `check-cert`, `verify-exe`): first-order and
  closed-world higher-order (via P8 defunctionalisation, inlining and
  specialisation) Lean programs over bounded `Nat` (below 2^63 at run time; a
  larger value is a `.natOverflow` resource failure), fixed-width words
  (`UInt8`–`UInt64`, `USize`), and inductive types, with recursion through
  equation theorems. Memory is immortal or general plain reference counting
  (constructors of up to 254 scanned fields, with verified FBIP reset/reuse and
  `@borrowed` inference). Roots take at most five `Nat` arguments and return a
  `Nat`, an enumeration, or a first-order constructor tree. Adding `--opt`
  replays the front-end certificate and then runs the formally validated LIR
  SSA optimizer (`Backend.compileOpt`, proved in `IxCC.Lir.Proof.Opt.Backend`
  on standard axioms); `--emit-cert`/`--embed-cert` currently require `--opt`
  off.
- **Experimental `--bignat` / DR1–DR4 path (uncertified):** `ixcc compile
  --bignat` (optionally with `--opt` and `--bignat-lib`) adds arbitrary-precision
  `Nat` (pure-Lean bootstrap-compiled `IxCC.BigNat.Entry`, zero C/GMP),
  native `Array` / `ByteArray` / `Array UInt64`, and static `String` literals.
  This path routes through `Cli.compileBigNat`, **bypasses certificate replay
  and `DefAsserts`**, and is **not yet covered by an end-to-end composition
  theorem** (`SlowPathEnv`/`BigNatLitEnv` hypotheses, internal library
  `rawNatOverflowCount` blocks, and Layer-3 `SrcEval` array/limb firing remain
  open; see [trusted-externs.json](docs/trusted-externs.json) and
  [bignum-design.md](docs/bignum-design.md)). IO is not supported.

**What is proved.** On the **certified replay path**, an accepted object refines
the source evaluator on the checked source program (and satisfies `DefAsserts`),
unless that source goes wrong (gets stuck, traps or returns a value its type
does not read back), under the x86, loader and driver/platform assumptions of
the [trust ledger](docs/trusted-extern-ledger.md); standalone `--exe` and
`--machine` shells are proved from `Process.{Loaded,Syscall,Step}` and verified
by `verify-exe` for `.ix.cert` v1 trailers. On the **experimental `--bignat`
path**, Layer-1 algorithm correctness, Layer-2 primitive simulations
(parameterized by `SlowPathEnv`/`BigNatLitEnv`), structural zero-`natOverflow`
on user/wrapper code, and Layer-3 model lemmas are proved on standard axioms,
but end-to-end certificate replay and composition are not yet established.
Across both paths, full grounded faithfulness from arbitrary Ixon bytes to
IxCK's model remains in progress (`IxCCGrounding`).

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
- the scalar and general plain-RC compiler (`Compiler.Proof`, `CompileClaim`,
  `Ring0`), certificate rechecker (`Recheck`, `Recheck.RcReplay`,
  `Own.Plain.checkOwned`), P8 defunctionalisation, proof fences and native
  suites;
- [Ixon v5 ingress](docs/ixon-v4.md) and the certified-kernel front end
  (`Src.KernelFront`, through ix's `IxCK` package, with certified N5
  `IxCK.Resource.check` mode gate (`IxCK/Resource/Audit.lean`: `DefaultOk`,
  `ReadsRespectErasure`, `CheckSound`) and L3b `IxCK.Host.Limits`);
- the grounding library (`IxCCGrounding`, SP-1 in progress);
- the x86 target model with its certified
  [encoder](docs/x86-encoded-instructions.md) and
  [stream/ELF layer](docs/x86-stream-objects.md), plus standalone executables
  (`X86.Exe`).

The legacy Aiur bytecode model (`IxCC/Aiur`, `IxCC/Vendor`), IxCC's private v4
resource port (`Ixon/V3/Resource`, `Src/Resource`), and 18 obsolete pre-Gen RC
proof modules have been retired as part of the Ixon v5 migration.

The earlier pipeline, the Ixby backend and their measurements are on branch
`jcb/ixby-archive` of the pre-merge `argumentcomputer/Compilatr.ix` repository.

## Build and check

IxCC lives in ix under `IxCC/`, as its own Lake package (`«ix-cc»`). It
requires the `IxCK` package beside it (`../IxCK`, of which it imports the Ixon
v5 codec, role vocabulary, executable certified kernel, resource mode checker,
host limits, and—for `IxCCGrounding` only—the kernel's model statement, 111
files total) and `Blake3.Pure`, and nothing of ix's root package. ix's flake
builds it and exposes its 16 required checks as `ixcc-*`:

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
