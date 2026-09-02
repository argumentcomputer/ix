# Compilatr.ix

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
- **Content addressing as compiler infrastructure.** Every identity-bearing
  object passes its pinned exact sharing policy, wire-representability, and
  local-semantic checks before its canonical serialization receives a blake3
  address; decoding is
  strict (one accepted byte spelling per value, with no address splitting).
  The current codec enforces this discipline and pins it with proofs,
  rejection tests, exact-byte tests, and deterministic mutation/random-byte
  tests.
  All five top-level codecs have global accepted-byte canonicality;
  `Address` and `Univ` also have global roundtrip, `Expr` and `ConstantInfo`
  roundtrip on their exact u64-count-representable domains, and `Constant`
  roundtrips when it is both count-representable and sharing-valid. A
  closed world of hashes makes whole-program compilation compatible with
  incremental caching: GRIN-style analyses over a Merkle DAG, with
  post-fixpoint certificates instead of trusted fixpoint computation.

Certification follows the CompCert discipline: executable passes are
validated against relational specifications, semantics are fueled
functional big-step interpreters (executable *and* proof-friendly), and
every claim is either a theorem, a differential test between two
independent semantics, or an explicitly recorded assumption.

## What is implemented

The default compilation spine runs from Ixon v2 bytes to IxIR₁, with a
validated forward-simulation interface for the supported source fragment.
A separate checked attachment lowers that artifact to logical IxIR₂.
The implementation includes a strict canonical codec with proved
roundtrip/canonicality laws and a frozen sharing policy
(`Compilatrix/Ixon/`, [wire spec](docs/ixon-v2-wire.md),
[sharing policy](docs/sharing-policy.md)), plus resource-bounded structured
ingress, a checked writer, and an address gate for local table bounds,
universe scope, recursor slicing coherence, wire count bounds, quadratic
sharing work, and pre-allocation sharing expansion; an exact ix `.ixc`/anonymous
`.ixe` catalog boundary with a bounded directory adapter, pinned upstream
sharing-image recognition, deep address/root binding, fat-vs-chunk duplicate
policy, aggregate budgets, and store-wide projection/constructor coherence
([catalog ingress](docs/catalog-ingress.md)), exercised by a byte-exact
production [Std contact](docs/corpus-contact.md); blake3 content addressing,
including versioned IxIR₀/IxIR₁ declaration and mutual-block preimages,
cycle-safe whole-program rekeying at both IR layers, and complete production
provenance maps
([IR addressing](docs/ixir-content-addressing.md)); a bounded initial IxIR₁
result-shape post-fixpoint checker with a kernel-checked evaluator
concretization theorem, a bounded deterministic SCC-local producer,
SCC-granular versioned cache summaries, bounded recursive constructor field
facts with sound allocation/fetch/reuse and case-binder transfers, canonical
resource-bounded persistent cache record/store decoding, checked artifact-local
miss repair, a bounded record-streaming/power-loss-durable single-file adapter,
a metadata-indexed chunk directory that lazily opens only dependency-selected
records and durably repairs them per key, and a first checked consumer that
propagates HPT facts through complete stored function bodies, simplifies cases
beyond syntactically adjacent calls, and then performs an exact
content-addressed graph rebuild: it prunes impossible constructor alternatives
and collapses a certified detailed-unary singleton case to one checked fetch;
its compatibility traversal also handles supplied fragments and the top-level
main; and a versioned fail-soft optimizer harness with deterministic
budgets, static control/heap/call and byte counters, canonical
input/output/certificate roots, per-pass enable/disable, pass-attributed
rewrite counters, and content-addressed before/after reports
([optimizer harness](docs/optimizer-harness.md)). Its
evaluator-preservation theorems cover dynamic self calls and complete-result
address transport, with dependency-cone plus
alias/reuse/corruption regression fixtures
([HPT certificates](docs/hpt-certificates.md));
proved build-once hash indexes for closed-world execution while proofs retain
transparent list lookup; structural compilation-unit budgets for eraser append
cost, output size, requested fuels, and proof-producing certificate scaling
([budget policy](docs/resource-budgets.md)); a
usage-checker gate; a reference evaluator with sharing-inlining coherence and
configured `Quot.mk`/`Quot.lift`/`Quot.ind` reduction;
checked erasure to IxIR₀ with a sorry-free fragment simulation theorem
(`erasure_sim`, `Compilatrix/Sim.lean`) and a proof-producing validator
connecting the executable eraser to it per program
(`Compilatrix/EraseValidator.lean`); mode-directed lowering to IxIR₁ — a
GRIN-style store IR with RC/unique worlds and exact memory counters — under
differential and leak-freedom guards, including a seeded replayable
[well-moded property corpus](docs/well-moded-generator.md); and artifact-facing
ownership, progress, and reclamation theorems for the validated IxIR₁ path
(`Compilatrix/PipelineSound.lean`). The checked IxIR₂ attachment has a
whole-main successful-run theorem to its logical semantics and an exact
interpretation bridge to physical baseline execution
(`Compilatrix/IxIR2/PipelinePhysical.lean`).

IxIR₂ also has checked dynamic-reuse insertion, whole-main preservation from
physical baseline execution, and a checked production fallback. Hot/cold and
recursive PAP-return fixtures exercise the runtime paths. The x86-64
substrate includes local typed semantics, proved scalar selection, encoding,
and ELF emission. A synthetic Ixon scalar now passes the actual validated
compiler, selects its emitted graph, and runs natively with its real addressed
IxIR₁ provenance. The composed theorem preserves its Nat result exactly at the
typed local x86 boundary. Independent checks cover zero, 42, and the largest
64-bit value; larger Nats are rejected. Heap/runtime selection and native FIP
remain later gates in the [development plan](docs/development-plan.md).

The bounded [source coverage gate](docs/source-coverage.md) now records 13
Ixon cases, including accepted direct-call, constructor/Nat dispatch, and
PAP/application paths. Two fresh compiler processes produce identical complete
IxIR₀/IxIR₁ graphs, provenance maps, HPT records, IxIR₂ diagnostics, and native
objects. The production Std rejection remains pinned, with a 17-constant
dependency closure that preserves it.

The first [source-recursion recovery schema](docs/source-recursion.md) turns
an eager Ixon list fold into a direct accumulator loop. Eight source cases
exercise hot/cold reuse and full heap reclamation. The composed source theorem
derives execution of the actual selected physical IxIR₂ after recovery and
preserves the original owned IxIR₁ on literal fallback. The resource extension
proves terminal allocation balance and complete reclamation of shared results
for the actual selection, including checked baseline fallback. The allocation
extension proves `baseline.allocs = selected.allocs + selected.reuses` and the
corresponding free equation for the checked shared baseline, at halt and after
complete release. The cost extension proves that selected RC operations and
peak live nodes do not exceed that baseline, including intermediate execution
states and complete result release. Native heap execution remains a separate
boundary.

The [source-map endpoint](docs/source-call-reuse.md) extends reuse across
non-tail direct and recursive calls under an explicit v1 credit policy.
Caller continuations retain their reservations while callees run with empty
credit files. A checked closed Nat-map specialization feeds the ordinary
compiler; nine source cases cover hot, cold, and mixed ownership. Three
unaliased cons cells use 8 allocations instead of 11 and 4 RC operations
instead of 13, with peak live nodes unchanged at 4. The source theorem includes
checked fallback, complete reclamation, and allocation/free/RC/peak laws.

The [unique-list reversal endpoint](docs/source-unique-reuse.md) checks a
closed Ixon source schema, records recursor worlds in canonical identities,
and emits consuming IxIR₁ followed by validated static IxIR₂ reuse. Reversing
three elements uses 5 allocations, 3 reuses, zero RC operations, and peak 5;
the result reclaims fully. The source theorem covers every finite Nat list
accepted by this schema, including checked optimization fallback.

Per-deliverable status — fragments, frontiers, exclusions, and evidence —
lives in the tracked [roadmap](docs/roadmap.md), the single source of truth
for completion claims; this README deliberately carries no second status
table. Local `plans/` files are forward-looking design notes. The
proof decomposition is recorded in the
[simulation strategy](docs/simulation-strategy.md), the sharing identity
boundary in [canonical sharing](docs/canonical-sharing.md), and every
opaque dependency (BLAKE3 and the narrow durable-sync syscall shim today;
eventually the store and others) in the tracked
[trusted-extern ledger](docs/trusted-extern-ledger.md), which separates
target extern assumptions from the Lean/GMP/Nix Gen-0 seed and records
observable retirement criteria. The public
[lean4ix](https://github.com/argumentcomputer/lean4ix) theory is the planned
kernel-specification bridge.

## Building

```sh
nix build                          # library + elaboration-time test suites
nix flake check                    # + compiled native-boundary/golden tests
nix develop -c lake build          # dev loop (or `direnv allow` once)
lake exe catalog-contact -- DIR    # deep-load one bounded .ixc, then pipeline
```

Most tests are elaboration-time `#guard`s and run on every build; the
blake3 golden tests execute FFI and therefore live in a compiled test
binary (`Tests.lean`, run by the flake's `tests` check). The Lean
toolchain is pinned by `lean-toolchain`; the flake supplies everything
else, including the Rust toolchain the Blake3 dependency builds with.
The GitHub workflow runs `nix flake check` on every push and pull request;
that command also validates the trusted-extern ledger against the actual
source imports, upstream native symbols, Cargo graph, and build/CI pins.
Repository checks are Lean executables in `scripts/`. The encoder and object
checks invoke GNU binutils; the trust audit uses Lake's TOML parser and
`sha256sum`. The flake also runs the source-coverage, source-recursion,
source-call-reuse, and source-unique-reuse artifact comparisons and the trust
auditor's rejection regressions.

> :warning: **Pre-alpha exploration; interfaces, encodings, and hashes
> roll without notice. Nothing here should be used for any purpose.**

## License

Dual-licensed under [Apache 2.0](LICENSE-APACHE) and [MIT](LICENSE-MIT),
matching ix.
