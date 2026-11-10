# Direct FFI for Aiur v2

This document describes the interface between the certified Aiur compiler
(Lean), the compiled-artifact cache and the formal prover (Rust) that `ix`
links.

## Summary

`ix` links the certified compiler and compiles a program in process when
the artifact cache misses, with the same code the standalone exporters run.
The result is an Ixon package (`Aiur.Artifact`, `aiur::artifact`), cached
under its BLAKE3 digest and loaded by the prover through
`aiur::artifact::Package::load`. A command holds each program, its trace
plan and verifying systems in Rust-owned handles that execution, proving and
verification reuse. Configuration and results cross the boundary as typed
records, witnesses and proofs as byte arrays. JSON remains a diagnostic
format for job reports.

## Ownership

| Object | Rust type | Owns | Lifetime |
|---|---|---|---|
| Registry | `ix_prover::system::Registry` | The programs and systems one command selected | One command |
| Program | `ix_prover::system::Program` | Checked bytecode, trace artifact, trace plan, executor, the package digest | Shared by every system of the command |
| System | `ix_prover::system::System` | A program, explicit STARK parameters, the verifying backend and key | Shared by the command's checks, proofs and acceptance checks |
| Lane | `ix_prover::aggregate::Lane`, or a `System::prover` | A device proving backend, worker pools and the shard feed | One controller run or single-claim scope |

Each is an `Arc`; Lean holds opaque external objects (`Ix.FormalProver.Registry`,
`Program`, `System`) whose payloads share it. Releasing the last handle
releases the data after any work that holds a clone finishes.

`TracePlan` and `Backend` read their program and plan through
`aiur::shared::Shared<'a, T>`, which either borrows for `'a` or owns an
`Arc<T>`. Handles build their plans and backends from `Arc`s, so a handle's
`TracePlan<'static>` and `Backend<'static, 'static>` own what they read;
nothing is leaked and no reference is forged. Callers that keep a program on
the stack still lend it.

The registry initializes each entry once: concurrent requests for the same
program (by canonical path) or system (by program identity and parameters)
wait for the first construction, and a failed construction leaves the entry
empty. It is created per command (`FormalProver.Registry.new`) and is not a
process-global cache. `Ix.FormalProver.counters` reports how many programs,
trace plans, systems and proving backends the process constructed.

A program handle exists only after the whole program checked:
`Program::new` checks the bytecode against the Goldilocks field, has its
execution record the call heights the trace's depth circuits read
(`CheckedProgram::track_depth`), builds the trace plan (which validates the
trace artifact) and selects the executor. Verification uses the system's
CPU verifying backend and needs no CUDA context.

## Runtime interface

Lean declarations are in `Ix/FormalProver.lean`; the adapter is
`crates/ffi/src/formal.rs` with its record codecs in
`crates/ffi/src/formal/records.rs`.

```text
Registry.new        : IO Registry
Registry.load       : Registry → Path → IO Program        -- a compiled package
Program.identity    : Program → IO ByteArray              -- the package's BLAKE3 digest
Registry.system     : Registry → Program → ProtocolParameters → IO System
System.key          : System → IO ByteArray
System.identity     : System → (recursive : Bool) → IO (ByteArray × Nat × Nat)
System.verify       : System → Entry → Array UInt64 → ProofBytes → IO Nat
System.check        : System → Request → Threads → (report : Bool) → IO Outcome
System.plan         : System → Request → JobOptions → Threads → Bool → IO Outcome
System.prove        : System → Request → Output → JobOptions → Threads → Bool → IO Outcome
proveLanes          : System → System → EnvHandle → LaneConfig → IO LaneResult
aggregate           : System → System → EnvHandle → AggregateConfig
                      → Option ByteArray → IO (Option (ByteArray × ByteArray))
aggregateCatalog    : System → System → CatalogConfig → IO ByteArray
normalizeRoot       : System → System → NormalizeConfig → Layout → Claim → Proof → IO ByteArray
resources           : IO Resources
```

`ProtocolParameters`, `JobOptions`, `LaneConfig`, `AggregateConfig`,
`CatalogMember`, `CatalogConfig` and `NormalizeConfig` are Lean structures
whose fields are paths, naturals, options, byte arrays, booleans and the
`Retention` enumeration. The adapter declares each with `lean_inductive!`
and its exact layout, checks a value's tag and object-field count against it
before reading any field, and reads the fields through the generated
accessors, so a structure that changes shape fails loudly. Store addresses
travel as 32-byte arrays, claims and binding sections as `Ix.Claim.ser`
bytes, the normalization layout as `.ixl` bytes. A read-only aggregation's
binding proof is the separate `Option ByteArray` argument of `aggregate`.

Results are typed: `Outcome` carries the status, an optional
`PlanSummary` (fit, whether a split can help, the suggested parts and the
estimated peaks) and the JSON report, which Rust renders only when the
command needs it (`--report`, `--json`, `--stats-out`, or the circuit
statistics a single claim prints). `LaneResult` is the root address or the
proven claims; `aggregate` returns nothing for a plan, or the proof's
address and, without persistence, its wrapper.

Lean arguments are borrowed for the call. Rust copies what it keeps
(configuration) or clones handle `Arc`s before scheduling work, so no worker
retains a borrowed Lean pointer. Errors become `IO` errors; the workspace
profiles abort on panic, so a panic never unwinds into Lean.

## In-process compilation

`IxVM.compilePackage` (`IxVM/IxVM/Package.lean`) and
`MultiStark.compilePackage` (`MultiStark/MultiStark/Package.lean`) compile
a program from its Lean constant (`IxVM.source`, `MultiStark.recursionProgram`,
`MultiStark.aggregateProgram`) with its entry and function groups:
`exportExecution`, `Trace.exportPlanParallel` and `Artifact.package`. The
standalone exporters (`ixvm export-claim(-trace)`, `stark-export
export(-trace)`) call them, and so does `Ix/FormalCompiler.lean`, which links
them into `ix`. The bytes therefore equal the exporter's for the same
program and compiler.

Command modules cannot import the compiler's packages, so
`Ix.FormalCompiler` registers itself in `FormalProver.compilerRef` when
initialized: its identity, each target's program digest
(`IxVM.programDigest`, `MultiStark.recursionDigest`,
`MultiStark.aggregateDigest`) and the compile function.
`FormalProver.compiler?` returns it; an executable without it has none.

## Selection and caching

`FormalAiur.compiledArtifact` selects a package for a command:

1. An explicit trusted artifact (`--aiur-artifact`, `--aggr-artifact`,
   `--verifier-artifact` or the `IX_*_ARTIFACT` variables) is admitted
   (`AiurArtifact.admit`).
2. Otherwise `AiurArtifact.cached` looks up `.lake/aiur/{target}-{key}.ref`
   and the package `{target}-{digest}.ixa` it names, and on a miss compiles
   the package, writes it under its digest and records the reference. The
   key is BLAKE3 of the compiler's identity and the program's digest.
3. With `Ix.FormalCompiler` linked, a miss compiles in process and the
   compiler's identity is `Ix.FormalCompiler.identity`. An executable that
   does not link it (the test drivers) runs the standalone exporter, and the
   identity is the BLAKE3 digest of the exporter's binary.

Every selected package is admitted against a pinned digest when one is given
(`--{flag}-digest` or `{env}_DIGEST`, `AiurArtifact.expected`). The prover
loads it by path (`Registry.load`), and `aiur::artifact::read` fails closed
when a content-addressed file name does not match the file's digest.

The compiler identity (`compiler_identity%`, `Ix/FormalCompiler/Identity.lean`)
is computed when `Ix.FormalCompiler` is elaborated: a BLAKE3 digest of the
structural hashes of every constant reachable from `Ix.FormalCompiler.compile`
(the compiler, the package encoder, the programs and their function groups),
plus the Lean version. It changes whenever that code changes and not when
unrelated Rust or Lean code does, so a rebuilt `ix` keeps its cache.

`ix prepare` compiles the three programs into the cache ahead of time, and
`lake build ix` generates the native executors from the same packages
([code generation](formal-aiur-codegen.md)).

## Pinned verifying keys

`tools/formal-aiur.keys` pins, for the IxVM, recursive verifier and
aggregation programs, the program identity and the BLAKE3 digest of the
verifying key under the default STARK parameters, which the file states:

```text
parameters log_blowup 2 num_queries 100
ixvm <identity hex> <key digest hex>
verifier <identity hex> <key digest hex>
aggregation <identity hex> <key digest hex>
```

- **Embedding.** The library `FormalAiurKeys` embeds the file
  (`include_str`); its `needs` names the file as a Lake input, so a change
  rebuilds it and its importers. The flake adds the file to the Lean
  sources.
- **Acceptance.** `Ix.Cli.FormalKeys` parses the pins. `ix verify` of IxVM
  proofs checks the selected IxVM system's key (`checkSystem`), and
  `FormalAggregate.context`, which `accept`, `acceptSlot`, the catalog and
  compression checks use, checks the IxVM and aggregation keys and builds
  the identity blob aggregate proofs commit to (`allowed`) from the pinned
  digests, requiring it to equal the blob of the derived keys
  (`pinnedAllowed`). A mismatch is an error naming the program and both
  digests, whichever artifact was selected.
- **Updating.** `lake exe formal-keys` derives the file from the checkout's
  programs; `tools/check-formal-keys.sh` fails when it differs from the
  committed pins (CI runs it), and `--update` rewrites them. The pin file
  is hashed into the verify-path fingerprint, so a re-pin goes through that
  review as well.

## Identities

A program's identity is the BLAKE3 digest of the package it was loaded
from, as `ix` prints and pins it. Systems are keyed by program identity and
STARK parameters.

Native kernels and CUDA bundles bind by fingerprints over domain-separated
binary encodings:

- `aiur::native::native_fingerprint`, scheme
  `NATIVE_FINGERPRINT_SCHEME = 2`: the domain, scheme, `ABI_VERSION`,
  modulus, the bytecode in Ixon serialization with table rows inline
  (`aiur::artifact::program_bytes`, independent of how a file pools rows) and
  every field of the native plan;
- `PopulationDescription::fingerprint`, scheme
  `DESCRIPTION_FINGERPRINT_SCHEME = 2`: the domain, scheme and every field
  of the population description, polynomials as trees;
  `compiled_fingerprint` covers it with the compiled ABI and seed contracts.

Generated kernels record call heights for depth circuits in the runtime,
so the fingerprints do not cover the trace's SCCs.

## Formalization boundary

The Lean compiler, its theorems and its checked layouts remain the source of
circuits. The package encoder and decoder and the record adapter are trusted
to transfer those results faithfully.

Lean's independent expected-claim computation, role binding, custom-axiom
commitments, manifest coverage and catalog acceptance are unchanged. They
use the system handle the command selected for key derivation and native
verification and never one chosen by the controller's result. The selection
and acceptance entry points changed signature (`compiledArtifact`,
`artifact`, `aggregationArtifact`, `verifierArtifact`,
`FormalAggregate.context`, `FormalAggregate.identity`, `verifyWrapper`), and
`Tests/VerifyPath.lean` adds the linked compiler's roots; the pin needs the
verify-path review.

## Checks

- `aiur::trace::stark::tests::shared_handles_prove_like_borrowed_ones`: a
  backend that shares its plan through `Arc`s proves to the same key and
  bytes as a borrowing one, after its caller's handles are dropped.
- `ix_prover::system` tests: registry entries initialize once and retry
  after a failure.
- `Tests.FFI.Basic`'s `MixedScalars` covers every scalar width of a
  `lean_inductive!` record, read field by field and round-tripped.
- Native and population fingerprint tests cover every encoded field.
