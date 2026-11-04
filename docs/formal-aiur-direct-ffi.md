# Direct FFI for Aiur v2

Status: implemented on `formal-aiur-perf-ffi`. This document describes the
interface between the certified Aiur compiler (Lean) and the formal prover
(Rust) as built.

## Summary

The certified compiler's output reaches Rust directly through typed FFI. A
command holds the resulting program, its trace plan and verifying systems in
Rust-owned handles that execution, proving and verification reuse.
Configuration crosses the boundary as typed records, witnesses and proofs as
byte arrays. Production code moves no program, circuit, witness, proof or
configuration through JSON. Persistent artifacts use a versioned binary
format; JSON remains a diagnostic and fixture format.

Everything runs in `ix`. A cache miss compiles through the compiler linked
into `ix` and hands the image to Rust in memory, with no exporter process
and no temporary JSON file in between.

## Ownership

| Object | Rust type | Owns | Lifetime |
|---|---|---|---|
| Registry | `ix_prover::system::Registry` | The programs and systems one command selected | One command |
| Program | `ix_prover::system::Program` | Checked bytecode, trace artifact, trace plan, executor, content identity | Shared by every system of the command |
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
program (by lookup key) or system (by program identity and parameters) wait
for the first construction, and a failed construction leaves the entry
empty. It is created per command (`FormalProver.Registry.new`) and is not a
process-global cache. `Ix.FormalProver.counters` reports how many programs,
trace plans, systems and proving backends the process constructed.

A program handle exists only after the whole program checked:
`Program::new` computes the content identity, checks the bytecode against
the Goldilocks field, builds the trace plan (which validates the trace
artifact) and selects the executor. Execution-only checks
(`Program.check`) use the program and construct no proving backend;
verification uses the system's CPU verifying backend and needs no CUDA
context.

## Runtime interface

Lean declarations are in `Ix/FormalProver.lean`; the adapter is
`crates/ffi/src/formal.rs` with its record codecs in
`crates/ffi/src/formal/records.rs`.

```text
Registry.new        : IO Registry
Registry.loadBinary : Registry → Path → IO Program        -- trusted .aiur artifact
Registry.loadJson   : Registry → Path → IO Program        -- diagnostic only
FormalCompiler.registryOfImage
                    : Registry → Key → RuntimeImage → IO Program
Program.save        : Program → Path → Name → CompilerId → SourceDigest → IO Unit
Program.identity    : Program → IO ByteArray              -- content digest
Program.compare     : Program → JsonPath → IO String      -- diagnostic
Registry.system     : Registry → Program → ProtocolParameters → IO System
System.key          : System → IO ByteArray
System.identity     : System → (recursive : Bool) → IO (ByteArray × Nat × Nat)
System.verify       : System → Entry → Array UInt64 → ProofBytes → IO Nat
Program.check       : Program → Request → Threads → (report : Bool) → IO Outcome
System.plan         : System → Request → JobOptions → Threads → Bool → IO Outcome
System.prove        : System → Request → Output → JobOptions → Threads → Bool → IO Outcome
proveLanes          : System → System → EnvHandle → LaneConfig → IO LaneResult
aggregate           : System → System → EnvHandle → AggregateConfig
                      → Option ByteArray → IO (Option (ByteArray × ByteArray))
aggregateCatalog    : System → System → CatalogConfig → IO ByteArray
fixedRootLayout     : System → ProofBytes → UInt8 → IO String
normalizeRoot       : System → System → NormalizeConfig → Layout → Claim → Proof → IO ByteArray
resources           : IO Resources
```

`JobOptions`, `LaneConfig`, `AggregateConfig`, `CatalogMember`,
`CatalogConfig` and `NormalizeConfig` are Lean structures whose fields are
typed paths, naturals, options, byte arrays, booleans and the `Retention`
enumeration. The adapter reads them field by field and checks each
record's object-field count, so a structure that changes shape fails
loudly. Store addresses travel as 32-byte arrays, claims and binding
sections as `Ix.Claim.ser` bytes. A read-only aggregation's binding proof
is the separate `Option ByteArray` argument of `aggregate`.

Results are typed: `Outcome` carries the status, an optional
`PlanSummary` (fit, whether a split can help, the suggested parts and the
estimated peaks) and the JSON report, which Rust renders only when the
command writes reports (`--report`, `--json`, `--stats-out`). `LaneResult`
is the root address or the proven claims; `aggregate` returns nothing for a
plan, or the proof's address and, without persistence, its wrapper.

`Request.check`, `Request.shard` and the compact advice buffers are
unchanged. Proofs are bytes; persistence keeps the existing binary proof
format.

Lean arguments are borrowed for the call. Rust copies what it keeps
(configuration, images) or clones handle `Arc`s before scheduling work, so
no worker retains a borrowed Lean pointer. Errors become `IO` errors; a
panic is caught at the boundary or aborts under the workspace's
`panic = "abort"` profiles and never unwinds into Lean.

## Direct compiler handoff

`Aiur/Aiur/Image.lean` defines the runtime image: explicit Lean structures
mirroring the runtime's `aiur::Program` (functions, enums, tables, maps,
entries with IO types) and `aiur::trace::TraceArtifact` (population plans,
physical circuits, function groups). Identifiers and register lists are
naturals below `2^63` and field elements canonical `UInt64`s. Polynomials
share their subexpressions: the trace carries one node pool (`Trace.nodes`,
three little-endian words per node: tag, operand, operand, every operand an
earlier node), built by hash-consing (`Image.Pool`), and each polynomial is
the index of its root node. Shapes and orders are otherwise preserved
exactly. The checks that produce the parts run in parallel; the parts are
then added to the pool in order.

`Aiur.Trace.exportPreparedImage` checks every replayed population plan
against the certified logical layout, column allocation and final
compaction, and the hint sites against the bytecode, before it produces
the trace image; `exportModulesImage` keeps the parallel replay and
`compileParallel`. `modulesImage` adds the bytecode image. The JSON
exporters (`exportPreparedJson`, `exportModulesJson`) render the image as
the diagnostic JSON artifact, so both formats come from the same checked
output.

`Ix/FormalCompiler.lean` links the compiler into `ix`: it imports the IxVM
and MultiStark packages, parses a source bundle with the frontend (whose
syntax it imports from the checkout's build), produces the image with the
same entries and function groups as the standalone exporters, and passes
it to `rs_formal_registry_of_image`. Because command modules cannot import
the compiler's packages, `Ix.FormalCompiler` registers itself in
`FormalProver.compilerRef` when initialized; `FormalProver.compiler`
returns it, and an executable without it reports that no compiler is
linked.

`crates/aiur-ffi` reads the image with `lean-ffi`: one call per image,
checking constructor tags and field counts, scalar naturals, canonical
field elements and the node pool (`aiur::artifact::pool`), and expanding
the runtime's polynomial trees from the pool without recursion, within a
bound on the total expanded size. The generic `aiur` crate does not depend on Lean, and Cargo
never invokes Lake.

## Persistent artifacts

`aiur::artifact` (`crates/aiur/src/artifact.rs`) is the one reader and
writer, shared by the runtime loader, the compiled-program cache, the
build's code generation step and the development binaries; the code
generators take a checked program, not a file. Format version 2:

- header: magic `AIURIMG\0`, version `u32`, flags `u32` (zero), modulus
  `u64`, the producing compiler's identity (a string of at most 1024
  bytes), the uncompressed body length `u64` (at most 1 GiB);
- body: one zstd frame (level 3) holding six sections, in order, each
  `tag u32 ‖ length u64 ‖ payload`: 1 metadata (name, source digest, lookup
  key), 2 rows (the distinct rows of the fixed tables), 3 bytecode (tables
  name rows by index), 4 nodes (the shared polynomial node pool), 5 trace
  and 6 groups (polynomials name their root node);
- a BLAKE3 digest of everything before it, then end of file. It is checked
  before the body is decompressed.

All integers are little-endian; element counts are bounded by the bytes
remaining, strings are validated UTF-8, field elements must be canonical,
every pool node references only earlier nodes (so pools decode iteratively
and have no cycles), polynomials expand to at most `2^28` nodes in total,
types nest at most 256 deep, and every section must be consumed exactly.
Both pools must be canonical: each distinct row and node occurs once, in
the order of first reference, and every entry is referenced, so a program
has exactly one encoding. Trailing bytes, unknown sections, a wrong
decompressed length and a digest mismatch are errors, and a version 1 file
is rejected with that cause. The format does not depend on Lean's heap
layout, Rust's struct layout or pointer width. The module documentation
gives every tag.

| Program | v1 file | v2 body (raw) | v2 file (compressed) |
|---|---|---|---|
| IxVM | 108.1 MB | 19.8 MB | 2.3 MB |
| recursive verifier | 15.6 MB | 8.1 MB | 0.78 MB |
| aggregation | 17.1 MB | 8.9 MB | 0.80 MB |

Files are written atomically (unique temporary file, `fsync`, rename).
`aiur-artifact` (`crates/aiur/src/bin/aiur-artifact.rs`) converts a legacy
JSON package (`convert`), renders diagnostic JSON (`json`), prints a file's
sections and digests (`info`) and reports the first difference between two
artifacts (`compare`). A JSON file given where a binary artifact is expected
is rejected with that conversion command.

## Selection, caching and native builds

`FormalAiur.compiledArtifact` selects a program for a command:

1. An explicit trusted artifact (`--aiur-artifact`, `--aggr-artifact`,
   `--verifier-artifact` or the `IX_*_ARTIFACT` variables) is loaded as a
   binary artifact.
2. Otherwise the lookup key is BLAKE3 over a domain tag, the artifact
   format version, the linked compiler's identity, the target name and the
   source bundle's digest.
   `<target>-<key>.aiur` in the shared cache (`IX_AIUR_CACHE`, default
   `~/.ix/cache/aiur/`) is loaded when present; a file that fails to load is
   an error naming the file and saying to delete it. The key also covers
   the artifact format version (`FormalProver.artifactVersion`), so files
   of another version are never looked up.
3. On a miss the linked compiler compiles the bundle in process, with a
   progress message, registers the image's program and persists it under
   the key. Programs a command needs together compile concurrently from one
   frontend import. The cache is never pruned automatically.

The compiler identity (`Ix.FormalCompiler.identity`) is computed when
`Ix.FormalCompiler` is elaborated: a BLAKE3 digest of the structural hashes
of every constant reachable from the image producer, plus the frontend
modules' constants, plus the Lean version. It changes whenever the compiler
code changes and not when unrelated Rust or Lean code does, so a rebuilt
`ix` keeps its cache. The artifact checksum detects corruption; trust in a
cached artifact rests on its key, and explicitly selected artifacts are
trusted by the caller as before. Proof inputs never select a program or key.

`lake build ix` runs `formal-codegen`, which obtains the three programs
this way and writes the native executors (`aiur_codegen::native_executor`)
and, in a CUDA build, the trace writers (`aiur_tracegen`) into
`.lake/build/formal-generated/`, which `crates/formal-generated` compiles;
Cargo does not run Lean or read an artifact.
See [codegen and caching](formal-aiur-codegen.md).

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

Program identity is the content digest
`aiur::artifact::content_digest`: BLAKE3 over a domain tag and the
canonical, uncompressed rows, bytecode, nodes, trace and groups sections,
independent of metadata, file header and compression settings. A decoded
file's identity is computed from the payloads it holds, which the decoder
has checked are canonical. Systems are keyed by program identity and STARK
parameters.

Native kernels and CUDA bundles bind by fingerprints over canonical,
domain-separated binary encodings instead of JSON:

- `aiur::native::native_fingerprint`, scheme
  `NATIVE_FINGERPRINT_SCHEME = 2`: the domain, scheme, `ABI_VERSION`,
  modulus, the canonical bytecode with its table rows inline
  (`artifact::program_bytes`, unchanged by format version 2) and every
  field of the native plan;
- `PopulationDescription::fingerprint`, scheme
  `DESCRIPTION_FINGERPRINT_SCHEME = 2`: the domain, scheme and every field
  of the population description; `compiled_fingerprint` covers it with the
  compiled ABI and seed contracts.

A bundle generated under the JSON scheme never matches: the domains and
scheme numbers differ. Explicit native mode still rejects a mismatch, and
automatic selection still falls back to the interpreter. These changes
invalidate generated code only; verifying keys, claims and STARK parameters
are unchanged, so proof caches stay valid.

## What remains JSON

- Diagnostic and report output: job reports, `--report`/`--json` files,
  `aiur-artifact json`, `Aiur.Image.RuntimeImage.toJson` and the standalone
  exporters (`ixvm export-claim-trace`, `stark-export export-trace`).
- The legacy JSON loader (`Registry.loadJson`, `aiur-artifact convert`) for
  migration and differential tests.
- Fixtures and test inputs: `crates/aiur/tests/fixtures/grouping.json`,
  recursive invocations (`Request::Invocation`), aggregation test cases.
- The generic Aiur execution and tracing bridge (`Aiur.Execution.FFI`,
  `Aiur.Trace.FFI`), which sends a program and hints as JSON and returns
  JSON results to Lean's examples and checkers. It is diagnostic tooling;
  no `ix` command uses it.
- The compression layout (`ix compress layout`, `fixedRootLayout`), a
  user-facing document of the compression pipeline.
- Planner layout files (`Options.layout_file`) read by benchmarks.

## Formalization boundary

The Lean compiler, its theorems and its checked layouts remain the source of
circuits; the handoff changes only their runtime representation. The image
producer, the `aiur-ffi` reader and the binary codec are trusted to transfer
those results faithfully. A faulty adapter that dropped a constraint would
change what the Rust verifier accepts, so they are guarded by structural
validation and differential tests (below), not by a Lean proof.

Lean's independent expected-claim computation, role binding, custom-axiom
commitments, manifest coverage and catalog acceptance are unchanged. They
use the system handle the command selected for key derivation and native
verification and never one chosen by the controller's result. Proof
decoding and public-input checks are unchanged. The selection and
acceptance entry points changed signature (`compiledArtifact`, `artifact`,
`aggregationArtifact`, `verifierArtifact`, `FormalAggregate.context`,
`FormalAggregate.identity`, `verifyWrapper`), and `Tests/VerifyPath.lean`
adds the linked compiler's roots; the pin needs the verify-path review.

## Checks

- `formal-aiur-tests image fixture`: a small Goldilocks program compiled through
  the independent JSON encoders and through the image; the prover's
  program, the JSON reference and the binary round trip must agree, and so
  must identities and verifying keys.
- `formal-aiur-tests image <ixvm|verifier|aggregation> [reference.json]`:
  the linked compiler's program against a JSON artifact for the same
  source (an exporter's, or `aiur-artifact json` of a stored file), with
  timings of each phase and peak RSS; `formal-aiur-tests image load FILE`
  times one load.
- `aiur::trace::stark::tests::binary_artifact_and_shared_handles_prove_identically`:
  JSON and binary inputs prove to the same bytes and keys, and a backend
  that shares its plan through `Arc`s proves after its caller's handles are
  dropped.
- `aiur::artifact` tests: round trips, malformed and truncated files,
  digest, compression and decompressed length, version 1 rejection,
  trailing bytes, noncanonical values, canonical row and node pools,
  identity independence from metadata and compression, deep polynomials
  and randomized corruption; `aiur-ffi` tests cover the image pool's
  references and depth.
- Native and population fingerprint tests cover every encoded field.

Full Init, Mathlib and GPU runs require separate authorization under the
repository's build and benchmark policy.
