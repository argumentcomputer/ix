# Incremental Ix certificates across commits

Status: design and initial implementation, revised 2026-10-06 for Ixon v4
(PR #658), warm proof caching across commits, existing catalogs and local
builds. The catalog-bound retained-corpus driver is implemented; see
[incremental catalog proving](incremental-catalog-proving.md) for commands,
record format and current limitations. Focused tests simulate the proof
backend; end-to-end proving and performance remain to be validated. Other
proposals below are not implemented unless listed in "What exists".

## 1. Goal

Ix is zkPCC: code carries a succinct proof that the designated checker
accepted its declarations, and a consumer verifies that proof cheaply
without trusting the author or the prover. The certificate is the product.
The immediate product is affordable certification of successive commits:
pay for a baseline proof once, retain its objects and evidence, then prove
newly required content and reuse compatible proofs. A third party verifies
the published logical snapshot without rebuilding or repeating its
typechecking. The source-commit association is authenticated separately (§3).

The target experience, for a project depending on Mathlib and for work on
Mathlib itself:

- use ordinary Mathlib/Lake/Nix caches and local or existing CI builds;
- keep local oleans and the normal incremental elaboration/checking loop;
  no GPU proving is required on edits, builds or debugging;
- export an immutable snapshot to Ixon and record it in a catalog;
- reuse the compatible certified corpus and its shard/aggregate proofs,
  proving only newly required addresses and the necessary joins;
- let recipients verify the artifact's designated checking claim without
  Lean, oleans, a source build or trust in the producer's kernel-check result.

There are three reusable products: declarations, frontend state, and
checking evidence. Oleans supply Lean's existing declaration/frontend
cache; Ix supplies content-addressed logical objects and checking
evidence. Server-side elaboration, remote dependency builds, olean
correspondence auditing and replacement frontend formats are deferred.
Their research remains below, but none is a prerequisite for this demo.
The initial implementation is the incremental proving driver in §7.1,
with catalogs supplying snapshot and corpus inventories (§8).
Use the catalog as the standard snapshot artifact even for a single
library: one member containing its compiled closure is enough. The
proving driver consumes that catalog and attaches its evidence record
within the same catalog system. Multiple libraries and finer pieces can
use the same interface later.

### 1.1 Target: ordinary builds and a persistent proving cache

Lean/Lake and existing CI produce the build and Ixon artifacts. A proving
worker consumes Ixon, retains compatible objects and proofs between jobs,
and generates the next certificate. It need not run a Lean frontend.
Local source edits continue to be elaborated and checked by Lean; their
new zk certificate is produced at publication.

| Event | Developer machine | Service |
|---|---|---|
| Dependency sync | Fetch ordinary cache artifacts through existing tooling | No new elaboration service required |
| Edit/build/debug | Elaborate and check changed modules; retain local oleans and incremental state | No request required for an unchanged dependency snapshot |
| Validate local work | Optionally export/check changed Ixon against certified dependency objects | Optional CPU checking; no zk proof required for ordinary feedback |
| Publish a snapshot | Freeze inputs, export Ixon and publish the current catalog inventory | Plan missing subjects against retained evidence, prove them, aggregate and publish |
| Third-party verification | Verify claim, coverage, checker/profile and axiom policy for the expected artifact | Serve evidence; no need to rerun elaboration for that verifier |

The ordinary local editor remains useful with its normal imports. A
custom LSP integration, a Lake fork and replacement frontend serialization
are not prerequisites. Shared address-keyed storage can still improve
Ixon/proof reuse, while Lake/Nix manage frontend build artifacts.

An optional future Ix importer could distribute interfaces, frontend
entries and executable support in a different format (§9.2–§9.4).
Keep that work separate from establishing the certificate's value.

### 1.2 What the certificate adds

An ordinary cache already avoids dependency elaboration and kernel
checking. A certificate does not make that work disappear a second time.
It adds an independently checkable reason to accept the cached logical
declarations, provided the consumer establishes the artifact-to-proof
correspondence. A certificate placed next to arbitrary oleans is not
sufficient. A later mechanism is a local export-and-hash audit of the
actual artifacts, amortized across unchanged builds (§5.3). That cache
trust product is deferred while warm proving is established.

The second product is portable verification. A reviewer, downstream
library, auditor or other recipient can verify that the designated
checker accepted the selected declarations under the accepted axioms,
without elaborating source or repeating the kernel check. A release
descriptor associates that logical artifact with a commit; proving
faithful source elaboration is a separate claim, not part of this demo.
Program typing also does not establish an arbitrary behavioral
specification unless the certified declarations express and prove it.

It also makes downstream certification incremental: prove new subjects
with their external dependency frontier as assumptions, then discharge
that frontier against existing evidence. The frontier is a set of
declaration addresses, not automatically Mathlib's catalog content root.
The initial driver preserves partitions and reuses exact claims as
described in §7. Neither minutes for delta proving nor milliseconds for the chosen
certificate profile is an established end-to-end bound.

Evidence reuse across a Lean upgrade is conditional on unchanged Ixon
bytes, checker semantics, axiom policy and compatible proof profiles.
Frontend packages and executable support remain toolchain-sensitive and
may need rebuilding even when the logical evidence remains reusable.

### 1.3 First demo: prove a baseline, then a subsequent commit

Build and compile a baseline with the existing tools; retain its catalog,
pieces, final `.ixes` after any budget splits, leaf proofs and aggregate
cache. Repeat the same request to establish a zero-new-proof warm run.

Compile the next commit and compare its complete anonymous address set
with the certified corpus. Preserve existing proof subjects and their
partition; put newly required subjects in fresh shards. Aggregate the
delta with the retained evidence and demonstrate coverage of the current
catalog. The proof may also cover historical declarations; current
snapshot membership must remain explicit (§7.1 and §8).

Test an added theorem, an isolated proof edit, a revert and an edit to a
widely used definition. Report intrinsic edits, address ripple, new leaf
proofs, reused subtrees and host/aggregation cost separately. The goal is
zero re-proving of old subjects solely because the commit or global
partition changed, not an assumed latency bound for every source edit.

Existing `ix compile <file>` is sufficient to begin, although it
elaborates that file's body even with `--no-build`. A compiled-artifact
exporter and per-module compilation cache can reduce that overhead later;
neither is needed to demonstrate reuse of expensive checking proofs.

### 1.4 Deferred: one incremental build graph, local or remote execution

A remote builder runs cache misses in the same dependency graph that a
local incremental build runs. Keeping local oleans is an artifact choice;
executing jobs remotely is a scheduling choice. A remote build can return
oleans for the default local workflow, return Ix frontend packages for an
experimental importer, or retain frontend state for a fully hosted
workflow. The immediate demo keeps elaboration in the existing local/CI
workflow and outsources only proving if desired. The following remote
build protocol is retained as future work.

Keep three jobs and their cache keys distinct:

| Job | Reusable result | Reuse condition | When to run |
|---|---|---|---|
| Elaborate | Module declarations, frontend entries and executable support | Same source, effective imported artifacts, toolchain, options and other tracked inputs | On frontend cache misses, locally or remotely |
| Compile/check Ixon | Addressed declarations and an independent check result | Same declarations and resolved address mappings; compatible compiler/checker, coverage and axiom policy | When declarations or their dependency addresses change, even if elaboration was cached (§7) |
| Certify | Shard proofs and aggregate certificate | Matching claims and compatible checker/proof profile; matching composition inputs (§7) | On an explicit publication request or configured CI job |

A normal edit should return diagnostics and a checked delta without
waiting for GPU proving. A client using hosted elaboration can instead
accept provisional diagnostics and request evidence later (§9.5). At
commit/push time, the same compiled delta feeds a proving job, reusing
compatible dependency evidence. This does not require re-elaboration.

Lake's cache protocol supplies existing outputs, not a remote execution
service. Two mechanisms exist in the pinned Lake version and only the
second is the integration point. `--try-cache` merely overrides
`--no-cache`/`LAKE_NO_CACHE`, and the switch gates one thing: whole-package
prebuilt archives for dependencies (`Package.maybeFetchBuildCache`: a
GitHub release asset under `preferReleaseBuild`, or a Reservoir barrel
for `leanprover`/`leanprover-community` packages), fetched once when the
dependency's build directory does not yet exist, never for the root
package. The per-module artifact cache is separate: each module build
resolves its outputs by input hash from the saved trace or the cache's
input-to-outputs mapping, and downloads any artifact missing from the
local cache directory from the configured service's artifact URL
(`resolveArtifact` in `Build/Common.lean`). Mappings arrive through
`lake cache get` against the revision endpoint; the cache is enabled by
`LAKE_ARTIFACT_CACHE` or the package's `enableArtifactCache?`, and applies
to the root package's modules too. Remote execution
needs a separate request protocol, immutable workspace snapshots, job
status/cancellation and result publication (§9.5). Downstream input hashes
can depend on upstream output bytes, so the wrapper must discover misses
as those outputs arrive or let the server resolve the graph; a source-only
scan cannot always enumerate every miss in advance. See
[Lake's module builder](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Build/Module.lean#L998).

The performance comparison is a warm incremental local build versus a
warm remote build, including uploads, queueing and result fetches. A
remote builder need not improve a one-module edit; its benefits can be
shared cached work, retained server environments and avoiding local
frontend dependencies. Cache reuse across users still requires matching
all relevant inputs and controlling or tracking command effects.

### 1.5 Deferred: establishing the expected statement for remote results

For a theorem, a client can check a remote result against an independently
elaborated expected type without running the theorem's proof script.
This is a useful restricted mode, not a general source-to-artifact proof.
It requires both:

1. An expected statement established using the client's accepted frontend
   environment, including notation, macros, instances and referenced
   definitions. Using the server's unverified frontend state to determine
   both sides of the comparison does not independently establish source
   meaning. A pinned maintainer-authenticated environment makes that
   provenance trust explicit; it does not remove it.
2. The actual certified declaration's type, bound to its full address and
   authenticated coverage. Fetch and hash its full bytes, or use the
   interface-projection protocol in §5.2. A name index plus a certificate
   does not authenticate a claimed type field.

Compare canonical self-contained types with references to the accepted
addresses. Exact equality of already authenticated types can avoid
fetching dependency bodies for the comparison itself. Producing the
expected type still needs frontend data; accepting definitional equality
instead of exact equality can require bodies and conversion checking.

Replacing theorem bodies with `sorry` is not a general implementation of
this mode. Commands can synthesize declarations and alter later frontend
state, types can invoke computation or tactics, and inferred statements
may depend on a body. Start with explicit theorem statements and a
supported command subset; reject unsupported cases or use the chosen
frontend authority. Any temporary placeholders must stay outside the
published proof, with references mapped back to the actual certified
declarations and the accepted axiom policy enforced. A placeholder and
the real proof have different Ixon addresses.

Definitions also require binding their intended bodies: equality of
types alone permits a different implementation, and local elaboration of
definitions is not guaranteed cheap. Neither a successful type comparison
nor the certificate proves that arbitrary commands executed as the user
intended. Fully hosted clients that do no statement elaboration retain
the explicit source-correspondence trust in §3 and §9.5.

### 1.6 Comparison with a Nix binary cache

The useful analogy separates substitution, execution and verification.
Both systems can fetch a cached build result or arrange a build on a
miss. Ix adds evidence about the resulting declarations' typing; it does
not use that evidence to authenticate arbitrary frontend build outputs.

| Concern | Nix | Proposed Ix service |
|---|---|---|
| Reuse unit | Derivation outputs, at the granularity chosen by the build expression | Modules for elaboration, constants for object deduplication, exact claims for proof reuse |
| Keying | Input-addressed store paths, or content-addressed outputs where configured | Lake traces for frontend builds; cryptographic addresses for Ixon objects and claims |
| Substitution | Store metadata and NAR archives from a substituter | Lake-compatible outputs or Ix packages, plus addressed objects and certificates |
| Cache miss | Local or configured remote builder | Local build by default in Lake; proposed wrapper/service for remote execution |
| Integrity and provenance | Archive/content validation and configured signatures; content-addressed objects have distinct acceptance rules | Content hashing, authenticated release descriptors and explicit frontend-tooling trust |
| Logical evidence | Substitution does not establish Lean typechecking | Verify the designated checker's claim, coverage and accepted axioms; source correspondence is separate |
| Build isolation | Configurable sandbox and declared inputs | Service must establish its own isolation and input policy; Lake jobs can also run in a sandbox |
| Local storage | Nix store and garbage collection | Lake cache for compatibility artifacts; proposed machine-wide Ix object store |

See the Nix manuals for
[remote builders](https://nix.dev/manual/nix/2.34/advanced-topics/distributed-builds.html),
[signature requirements](https://nix.dev/manual/nix/2.34/command-ref/conf-file.html#conf-require-sigs)
and [derivations](https://nix.dev/manual/nix/2.34/store/derivation/index.html).
Neither a cache signature nor a typing certificate establishes faithful
execution of arbitrary source elaboration. Reproducibility is something
to test under declared inputs, not an inherent difference between Nix
and Lake.

Two integrations are possible. A Lake service publishes output mappings
and artifacts; a separate wrapper requests remote builds. A Nix package
pins the driver and frontend dependencies, uses substituters, and may
route proving jobs to a remote builder. A `cuda` system feature can select
a builder, but GPU devices, drivers and sandbox access still need to be
configured. Nix packages can distribute certificates as outputs; clients
must still verify them if they want evidence independent of the builder.
A substituted output saying "verified" is not a local verification step.

The pinned lean4-nix builds package targets, not one derivation per Lean
module. Its `lakeArtifacts` option explicitly seeds a build with an
earlier derivation's `.lake` artifacts. The current ix flake uses this to
seed CLI/test builds from the library build in the same graph; it does
not automatically carry mutable state across source revisions. A changed
package source can invalidate the Nix derivation while a seeded Lake
build still reuses unchanged modules. Cross-revision reuse needs explicit
artifact seeds, declared cache artifacts or finer derivations; network
cache access during a build must fit its sandbox/input policy. See
[the pinned package builder](https://github.com/argumentcomputer/lean4-nix/blob/a85438f70bc005863dfac72074485169757f0745/lib/lake.nix#L330).

Both frontends can share a storage backend through separate adapters.
Nix store paths, NAR hashes and `narinfo` metadata are not the raw BLAKE3
Ixon-address protocol; compatibility is an integration task, not a
consequence of both using hashes. See
[Nix store objects](https://nix.dev/manual/nix/2.34/store/store-object.html)
and [store paths](https://nix.dev/manual/nix/2.34/store/store-path.html).

Client downloads depend on where the frontend and independent check run:

| Mode | Dependency oleans | Other dependency data on the client |
|---|---|---|
| Local Lean, current target | Normal cache artifacts for effective imports | Exported Ixon for publication; certificate, coverage and release metadata; olean correspondence audit deferred (§5.3) |
| Hosted frontend, local delta check | Only if also using a local frontend/editor | Certified constants reached by checking, result/name mappings, certificate and coverage evidence |
| Hosted frontend, certificate verification only | None required | Certificate, coverage and result bytes or authenticated interfaces; expected-statement validation adds frontend inputs (§1.5) |
| Experimental Ix frontend | None | Interfaces, entries, executable support and mappings; certified constants as needed; new importer required |

Local Ix checking still needs full constants on checker faults, including
proof bodies used only for type lookup (§5.2). Those objects can come from
the olean audit or from a resolver; a second whole-library download is
not mandatory. A third party can verify the certificate without these
objects, but must establish the expected claim and release association.
The default workflow keeps the ordinary Lean language server and its
imports. New editor integration and the alternate Ix importer are optional.

## 2. What exists

| Capability | Where | Notes |
|---|---|---|
| Content-addressed, alpha-normal constants; references by address | `crates/ixon/src/constant.rs`, `docs/ix_canonicity.md` | Address is blake3 over the serialized constant. Editing a constant re-addresses its whole reverse-dependency cone. |
| Canonical intra-constant sharing (v4) | PR #658, `Ix/Sharing/Exact/`, `crates/ixon/src/sharing_exact/` | The sharing table is part of the canonical bytes and a specified function of the anonymous expressions; phase-1 minimality is machine-checked and Lean/Rust byte parity is tested. Metadata never influences it. No cross-constant subterm dedup. |
| Name/metadata layer separate from identity | `crates/ixon/src/env.rs` (`named`, `names` sections) | Not content-addressed; plays no part in catalog identity; reproducible from source. |
| Portable claims | `crates/ixon/src/proof.rs` | `Check`, `CheckEnv`, `Contains`, `Catalog` bind only Merkle roots over addresses plus an assumption root. No env hash, no file hash. |
| Shard protocol | `crates/kernel/src/claim.rs`, `crates/ixon/src/shard_claim.rs` | A shard's `CheckEnv` owns a set and assumes its thin frontier; joins discharge assumptions by membership. |
| Aggregation | `crates/ffi/src/aiur/aggregate/`, `Ix/Aggr/` | Bisection tree over one `.ixes` manifest of one `.ixe`; flat canonical joins below `--structural-above`, structural root-of-roots above; resume cache keyed by outer claim. Overlapping subject sets are rejected. |
| Shard-proof index | `Ix/Cli/ShardProofIndex.lean` | `~/.ix/cache/shard-proofs/<claim-digest>` → verified proof; drives `ix prove --skip-proven`. |
| Incremental catalog driver | `Ix/Cli/CatalogProveCmd.lean`, `crates/kernel/src/catalog_prove/`, `crates/ffi/src/catalog_prove.rs` | `catalog prove --base`, `--plan-only` and `catalog verify-proof`; retains a cumulative corpus and final partition, reconstructs claims, calls existing proof caches, and publishes `proving.json` only after coverage and aggregate verification. Fat catalogs only; full-binary profile pin; no hosted transport or terminal compression. |
| Structured diff | `crates/ixon/src/diff.rs`, `Ix/Cli/DiffCmd.lean` | Classifies changed constants as root edits vs rippled re-addressing. |
| Catalog | `crates/ixon/src/catalog.rs`, `Ix/Cli/CatalogCmd.lean`, `Benchmarks/TruthMinesSpec/` | `.ixc` directory: manifest with members root and content root over the anonymous union, per-member pins and preimage commitments, self-contained fat pieces. Chunked profile is defined and verified but not produced. `Catalog` claim is defined with no prover. Manifest reserves an aggregation-tree section. |
| Olean-free import | `Ix/ImportIxe.lean` | Materializes constants from a `.ixe` into the elaboration environment via `addDecl` (kernel re-checks today). `only [names]` imports a reference closure. |
| Upstream frontend export hooks | Lean `ModuleData`, `mkModuleData`, `PersistentEnvExtension.exportEntriesFn` | Lean exposes per-module extension entries; Ix extraction, encoding and restoration are proposed in §9.2. |
| Compiled-module input | `Ix/Meta.lean:getCompileEnv`, `Ix/CompileM.lean` | Compiled oleans can supply an environment to the compiler; the current CLI still elaborates its source-file argument. A direct audit of olean bytes, import projections and certificate coverage is proposed in §5.3. |
| Lazy kernel ingress | `crates/kernel/src/tc.rs` (`try_get_const`) | Faults a missing constant in by address when a check discovers it. |
| Thin bundles | `Ix/Cli/PackCmd.lean`, `Env::assumptions`, `validate_closed` | A partially present env with declared cut points is already a valid artifact. |
| Verify without the env | `Ix/Cli/VerifyCmd.lean` | `ix verify <hex>` needs only the proof bytes and the binary. `--ixe --ixes` is needed only to audit whole-env coverage. FRI/commitment parameters are hardcoded to match the prover. |
| GPU proving | PR #644, `docs/aiur-gpu-proving.md`, `docs/aiur-trace-sharding.md` | Trace sharding splits rows of one execution across devices; lanes schedule claims and joins across devices; bisection changes the partition at prove time; `ix compress-root` terminal. |
| Content-addressed store | `Ix/Store.lean`, `crates/compile/src/store.rs` | `~/.ix/store` holds claims, assumption trees, proofs. Constants live in plain `.ixe` files, not in the store. |

Reference sizes, measured on this machine and in PRs #590, #584 and #658:

| Item | Value |
|---|---|
| Mathlib `.ixe`, v3 (constants + names, this machine) | 3.15 GB |
| Mathlib `.ixe`, v4 (`import Mathlib` env, PR #658) | 2.32 GB |
| Mathlib constant bytes, v4 canonical vs v3 heuristic sharing (PR #658) | −21% |
| Mathlib `.olean` exported level (this machine, 4.33.0 build) | 1.83 GB, 8414 files |
| Mathlib `.olean.private` / `.olean.server` levels | 3.57 GB / 0.10 GB |
| Mathlib `.ir` / `.ilean` | 0.23 GB / 0.28 GB |
| Mathlib olean parts with constants stripped (frontend metadata, olean encoding) | 1.15 GB |
| Aggregate root proof (2026-09-09 results) | 9 to 14 MiB |
| Full Mathlib Rust-kernel sweep (PR #590) | 204 s, 6.4 GiB peak |
| TruthMines + Palomar catalog (PR #590, v3) | 97 members, 995,368 unique constants, ~100 GiB fat on disk |

The v4 Ixon for Mathlib is larger than the exported-level oleans alone and
well under half of the full olean data (all three levels) that a cache
download ships. The immediate demo keeps ordinary build artifacts and
exports Ixon for publication. The deferred cache-admission workflow can
derive Ixon locally, avoiding a second full-corpus download (§5.3).
An alternate frontend package would need interfaces, metadata and
executable support as well; Ixon size alone does not establish its total
download size. The v4 sharing improves per-constant storage and transfer,
but constants remain the transfer unit until measurements justify
subterm distribution.

## 3. Trust story

**What the proof binds.** A certificate is a `Proof { claim, proof }`
wrapper whose claim is `CheckEnv { root, assumptions }`: every leaf under
`root` typechecks under the IxVM kernel, conditional on every leaf under
`assumptions`. The checker identity is bound through the aggregate's
allowed-vk blob. The legacy whole-env convention lists axiom leaves as
assumptions, including `sorryAx` when present. In the shard protocol,
assumptions are outstanding dependency-checking obligations: the thin
frontier outside the shard's subjects. Aggregation discharges them as
other subjects are proved. A root with no residual assumptions does not
by itself establish an axiom policy or exclude `sorryAx`, since axiom
declarations can themselves be subjects (`crates/kernel/src/anon_work.rs`
emits a work item per `Axio`). Axiom-policy evidence is a separate
requirement; it must be authenticated to the covered declarations or
explicitly delegated to a trusted auditor. The simplest mechanism is to
change the shard protocol so that axioms are never subjects: treat every
`Axio` as frontier, so a fully discharged root's residual assumptions are
exactly the axiom set, visible in the assumption tree, and a root with no
assumptions means no axioms at all. Until then the consumer needs the
subject bytes, or a separate claim, to know which axioms a root depends
on. Nothing about names, files, or the service is in the typing claim.

**The consumer's check is per constant, not per environment.** The claim is
universally quantified over its leaves, so for any address a consumer can
exhibit a membership path for, the claim covers it. A path is the leaf's
canonical path inside its shard followed by the sibling roots up the
structural tree, which `SubjectTree::merkle_proof` already computes. Paths
can be served by an untrusted party and verify against the root in the
claim. Accepting selected declarations needs no whole-env reconstruction
(`ix verify --ixe --ixes`). Auditing an entire cache instead requires
coverage of its declared logical inventory; a bulk leaf index can
establish that coverage without downloading the producer's `.ixe`.

**Release provenance is a separate trust decision.** A valid certificate
does not establish "this is Mathlib at rev X" or authenticate the name and
frontend metadata layers. Those mappings affect which statements the user
elaborates and intends to prove. The proposed default trusts the repository
maintainer, or a build service explicitly chosen by the user, for that
association while independently verifying typechecking and coverage.

An authenticated release descriptor binds the source pin and toolchain,
cryptographic hashes of the olean/build artifacts, catalog identity,
name-index and frontend-metadata hashes, certificate hash, actual proof
subject root, declared logical scope and verification profile. The consumer
accepts profiles and assumptions according to local policy; a producer
cannot select a different checker merely by publishing its key. A signed
descriptor or a descriptor pinned through the trusted repository is enough;
no central index or consensus protocol is required. Recompiling selected
source is an optional correspondence audit, not a normal consumer step.
Canonical anonymous bytes make the address comparison precise, but do not
make source-to-artifact correspondence a consequence of the typing proof.

**Olean correspondence is an additional check.** The current certificate
binds Ixon addresses, not olean bytes. A release signature authenticates
the producer's pairing of the two but does not prove their equivalence.
The deferred stronger cache-admission policy checks the actual compiled logical
declarations and import views against covered Ixon (§5.3). It retains
provenance trust for source, names and frontend behavior while removing
the producer's typechecking assertion as the authority for the audited
logical scope. Whole-snapshot claims must include a complete inventory;
a proof of an arbitrary subset must not be presented as covering every
declaration in the cache or source tree.

**Coverage can also be delegated, explicitly.** The default checks each
admitted address against the verified subject root, using a membership
path or an authenticated bulk leaf index (§5). An optional trusted-catalog
mode could accept the maintainer's coverage assertion instead. In that
mode the proof still establishes its own claim, but the assertion that the
loaded declarations belong to that claim rests on the maintainer.

**Trust base.** The verifier binary with its compiled-in verifying keys,
blake3, STARK soundness, and the IxVM kernel's faithfulness to Lean (the
`IxTcVerify` programme). For *interpretation* of decompiled statements the
decompiler joins it; the compiler's codec and sharing construction are now
partly machine-checked under `IxCompileVerify`, which shrinks the part of
interpretation that rests on testing alone. The olean-to-Ixon audit and
any Ixon-to-Lean admission bridge must preserve the certified declarations
and their references; correspondence is not yet fully machine-checked.
The prover and object mirrors need not be trusted for the typing claim;
release provenance has the explicit authority described above. Imported
macros, tactics and initializers are executable build tooling: a typing
certificate does not certify their runtime behavior or the fidelity of
their frontend effects. Independent checking must run outside the
frontend process with protected inputs and results. Process separation
alone does not contain malicious native code; either the producer's code
is trusted as ordinary build tooling or execution is isolated from the
verifier and its store. Treating extension entries as logically untrusted
does not make their deserialization or initialization automatically safe.
Gap: the wrapper must carry its parameter profile
and the verifier must check it against local policy, or "useful
independently of the service" is not literally true.

**Tampered frontend outputs.** With the independent checking boundary
above, an olean or Ix frontend package is not the authority for typing.
A cached declaration must match the certified logical content; new Ixon
can also be independently checked against that content. Frontend
tampering can still change what the source means: a substituted instance
can make `a + b` elaborate to multiplication, while a printer using the
same altered environment renders addition. A name index can also be
altered consistently with that substitution. Printing a certified term
through an authenticated index helps inspection, but does not prove the
source-to-term translation. Native code and serialization risks remain
subject to the execution boundary above.

The default provenance policy accepts the chosen release authority.
Independent reproduction can strengthen that policy, but identical
outputs must be demonstrated under declared inputs, not assumed from a
Git revision. A reproduction record should bind the source snapshot,
toolchain and other build inputs, olean/interface/entry/code hashes,
name-index hash, content root and certificate hash. A certificate-only
recipient does not need to download the build artifacts.
Consumers may require matching records from independent builders or
locally reproduce selected modules. Agreement establishes reproducibility
under those inputs; it does not establish the correctness of a shared
toolchain or turn provenance into a consequence of the typing proof.
A certified compiler would authenticate translation of its input Lean
environment, not establish how arbitrary source commands created that
environment.

**Proving elaboration is outside this claim.** Executing the elaborator
under proof would require a model of its runtime, mutable and persistent
frontend state, native functions and external inputs. A general zkVM is
another possible route, with an authenticated input environment and a
different cost profile from checking the resulting kernel terms. No
implementation or end-to-end cost measurement here establishes that
either route is practical for Mathlib; it is not a dependency of this
demo. Proving a pinned elaborator's execution would still leave the user
to accept that toolchain's semantics and the presentation of the result.
The scoped alternatives are explicit provenance, reproducibility audits,
expected-statement validation (§1.5), and a verified renderer of certified
terms to canonical Ixon text or a restricted readable surface
(`docs/decompile-audit-surface.md`). Renderer verification is separate
work, not a property of the existing name index.

**Under full verification.** Assume the Lean-to-Ixon compiler is
certified, `Ix.Tc` is verified against the lean4lean Theory, and Aiur's
proof system and verifier are verified. Then a certificate over an
address set means "these Lean declarations are well-typed in Lean's
type theory under exactly the listed axioms", provided the coverage and
axiom-accounting requirements above are also established. This would give
a machine-checked chain through compiler, checker and proof system. What
remains trusted: the Theory as the definition of Lean's logic and its
metatheory;
cryptographic assumptions (blake3 collision resistance, Fiat-Shamir, FRI
and STARK conjectures at the carried parameter profile); that the
verified artifacts are what runs, which includes the Lean-to-Aiur
compilation of the checker program itself, best handled by validating
the fixed bytecode against the kernel specification once and pinning
its hash in the verifying key, and the verifier binary's build chain;
the Ixon format identity and primitive pins the compiler certificate is
stated for; and elaborator state, for interpretation only.

For delegation, the ix check can be the authority for new declarations;
using `debug.skipKernelTC` then requires that independent check to be
mandatory before acceptance, rather than treating frontend success as
evidence. Remote elaboration can establish the theorem the client expects
only with the conditions in §1.5. Verification of the compiler and checker
does not remove those conditions. Alternatively, a user can explicitly
delegate source interpretation and name mappings to a chosen authority,
as in the default release policy. A locally reproduced environment and
certified compilation can audit that mapping; publication alone cannot.

## 4. Artifacts

The immediate proving driver needs snapshot catalogs/pieces, a retained
anonymous corpus, final partitions, proof objects/indexes and authenticated
snapshot-to-evidence records. The olean and frontend artifacts below are
for the deferred cache-validation/importer designs.

- **Incremental proving record.** Current snapshot catalog identity and
  selected address inventory; certified corpus identity; exact shard
  subjects/frontiers and final `.ixes`; reusable proof addresses and
  aggregate topology; checker/format/parameter pins and axiom policy.
  Store this as versioned metadata attached to the catalog. Bind the
  exact manifest hash as well as its logical roots, since source pins
  and labels are not committed by those roots. Reference the prior
  catalog/evidence record used as a base; derive reusable claim keys
  independently of commit and manifest identities.
  Persist the underlying objects and proofs, not just index entries or
  the final release certificate. A snapshot is complete only after its
  declared coverage has been established.
- **Olean/build bundle.** Ordinary cached `.olean` parts and the IR/native
  artifacts needed by the selected Lean/Lake targets. A release descriptor
  binds cryptographic hashes of the actual files, with their module and
  import-level inventory. They retain their normal frontend role; the Ix
  certificate covers a declared logical scope, not arbitrary executable
  support or metadata behavior.
- **Admission record.** A local record that the bundle's audited logical
  declarations and import views correspond to certified Ixon (§5.3).
  Bind artifact/dependency hashes, audit/compiler version, covered scope,
  actual claim, checker/profile and accepted axiom policy. Reuse across
  workspaces only when those conditions match.
- **Store.** A machine-wide, address-keyed constant store shared across
  repositories and versions. Today only claims and proofs are stored this
  way; pieces are plain files. Exporting oleans can populate it without
  fetching a second full corpus. Local pieces can bootstrap the demo
  before a complete remote resolver is available.
- **Catalog manifest.** Member address sets, source/toolchain pins,
  dependencies, logical roots and storage hashes/sizes. Fat members may
  overlap; exact proof ownership belongs to the proving plan. Optional
  preimage references exist in the format but are not populated by the
  current assembler. The aggregation tree and assumption metadata remain
  proposed extensions, carried initially by the attached proving record
  (§8).
- **Release descriptor.** The authenticated association between source,
  catalog, frontend metadata and certificate described in §3. Its
  provenance assertion does not replace certificate verification.
- **Certificate.** The aggregate root proof plus the leaf claim digests and
  tree shape, the assumption tree, the parameter profile, and the vk pair.
  Embedding leaf roots shrinks a membership path to its within-shard part.
  Historical root proofs are tens of MiB; the size and verification cost
  after terminal compression must be measured for the selected profile.
- **Name index.** Per member, name to address with hints. Supports
  incremental compilation and statement presentation. Audit dependency
  bindings against actual artifacts before using them as independently
  established addresses. Size for Mathlib: unmeasured.
- **Declaration interfaces** (optional distribution format). Per module
  and import level, the frontend-visible projection of constants, paired
  with their full Ixon addresses. Include types and universe parameters,
  original and presented declaration kinds, visible bodies, inductive/recursor data,
  and the metadata needed to reconstruct the appropriate Lean view.
  Preserve module visibility and `import all` behavior. The deferred
  cache-admission design audits the corresponding views in oleans (§5.3); a later
  projection proof authenticates separately delivered interfaces (§5.2).
  Do not compile body-less theorem presentations as fresh anonymous axiom
  declarations.
- **Frontend metadata** (optional replacement for olean storage, as a
  module-level branch of the existing metadata layer). Today each named
  entry carries the anonymous address, exact per-name reducibility hints,
  and a `ConstantMeta` with
  what the anonymous form erased: enough to rebuild the exact
  `ConstantInfo`, and nothing the elaborator needs beyond that
  (`Ix/ImportIxe.lean` states that instances, attributes and native code
  do not transfer). The proposal stores each module's ordered extension
  entries, imports and visibility levels, with references to separate
  executable-support packs for tactics and initializers. Per-name indexes
  are secondary: one module can register an attribute on another module's
  declaration, so the module exporting the registration must own that effect. The
  name-to-address map connects these entries to certified constants
  without erasing frontend names or scopes. Extraction uses Lean's
  existing export hooks; portable encoding,
  extension-code loading and import reconstruction remain unimplemented
  (§9.2). Metadata has its own schema and content identity; changing a
  registration must invalidate frontend caches even when anonymous Ixon
  and its certificate are unchanged. Metadata changes should preserve
  canonical constant bytes and their addresses.

  *Measured size.* Stripping `constants` and `constNames` from every
  Mathlib olean part and re-serializing with Lean's writer (8322 of 8414
  modules; 92 stale files skipped) leaves 1.15 GB of 5.50 GB: 0.58 GB at
  the exported level, 0.47 GB private, 0.10 GB server. That is about half
  the size of the v4 Ixon. A per-extension breakdown on a 415-module
  sample (relative shares; per-extension files lose cross-extension
  sharing, so absolute figures overcount) says what it is made of:

  - about half is compiled code (`Lean.Compiler.LCNF.baseExt`,
    `monoExt`, `Lean.IR.declMapExt`, specialization caches). Separating it
    permits selective transfer, but custom-extension initializers may
    require code during import, and compilation can require signatures or
    other compiler state. Fully lazy code loading needs an import audit;
  - the server level and `Lean.declRangeExt` are language-server data,
    out of scope for batch builds;
  - simp and instance entries include derived lookup keys that may be
    recomputed from statements. Registration choices, scope, priority,
    direction and other extension-specific flags must still be exported.
    A codec must preserve those facts before replacing an index with a
    reconstruction recipe; the exact CPU/size tradeoff is unmeasured;
  - docstrings, `to_additive` translations, reducibility and defeq
    attributes, and a few Mathlib-side extensions make up the rest.

  A few hundred MB of eager non-code entries for all of Mathlib is a
  hypothesis from this sample, not a measured package size. Declaration
  interfaces and executable-support dependencies must also be counted.
  Fetch per module for the project's effective import closure, preserving
  the global instance and simp registrations that those imports activate.
  Measurement script: strip and re-save each
  module's olean parts in order with `saveModuleDataParts`, keeping
  `entries` and `extraConstNames`.
- **Executable support** (optional separate packaging). Packs keyed by
  toolchain/platform, containing IR or native code, compiler signatures,
  generated-name mappings and initializer dependencies. Exporter bookkeeping must preserve
  `extern`/`implemented_by` bindings and required external libraries.
  Regeneration from Ixon is an optional compilation experiment, not a
  guarantee that arbitrary tactic implementations or native dependencies
  can be recovered from kernel terms alone. Initializers can force eager
  loading. Hosted elaboration keeps these packs on the server instead.
- **Pieces and fat catalogs** remain the producer-side and archival format.
  The consumer-side format is the store plus a resolver.

**Format versioning.** An incompatible anonymous object-format bump can
change constant addresses and invalidates format-specific artifacts,
claims and primitive pins; v3 to v4 in PR #658 required a corpus-wide
recompile and re-prove. The store, catalogs and certificates must record
that format identity. A frontend-metadata schema change should not require
an anonymous format bump or re-proving unchanged constants. Claims
already bind the object-format byte and the validator id; the certificate
wrapper and the store layout must carry the
format id too, and the TruthMines piece cache key already does. Once
certificates are distributed, format stability becomes a product
constraint. v4 is the first version it would make sense to distribute
against, and the design should budget for further bumps rather than assume
they stop.

## 5. Deferred: consumer cache admission

This flow strengthens trust in downloaded oleans. It is independent of
the immediate incremental proving demo; ordinary build caches remain
unchanged while §7.1 is implemented.

1. Resolve the repository's `lake-manifest.json` pins through an
   authenticated release descriptor from the selected authority (§3).
2. Fetch the manifest and certificate. Verify the proof without pieces,
   under an accepted checker/profile, and compare its actual subject root
   and assumptions with the descriptor. A structural proof root need not
   equal the catalog's canonical content root (§8).
3. Fetch ordinary dependency oleans and executable support through the
   chosen build cache. Validate byte identities and audit the logical
   declarations and imported views against covered Ixon (§5.3), or reuse
   a matching local admission record. Keep the resulting address map and
   optionally store the exported objects for later Ix checking.
4. Run ordinary local Lean/Lake builds against those imports. Retain local
   module outputs and re-elaborate/recheck only what the frontend build
   graph invalidates. Dependency proof checking, the admission audit and
   GPU proving are not repeated for each unchanged import on each edit.
5. At explicit validation or publication, export local declarations with
   references to the audited dependency addresses. Check new Ixon against
   certified objects, then request a publishable certificate when desired.
   Missing objects can be exported from installed oleans or fetched by
   address with hash and coverage validation. Evidence reuse follows §7.

A certificate-only recipient needs steps 1–2 plus a binding of the
expected statements or logical artifact to covered subjects. It does not
need the developer's oleans or frontend build. To claim coverage of a
whole snapshot, also establish the declared inventory/coverage relation;
the trusted descriptor supplies the source association, not a proof of
source elaboration (§3).

The Nix analogy is fetching immutable bytes and their references from
substituters. A NAR is a filesystem archive; `narinfo` supplies store
metadata and optional signatures, not membership in a proved typing
claim. In Ix, a release signature authenticates provenance, an object hash
authenticates bytes, and a certificate plus coverage evidence establishes
the checker's claim for those bytes. These are distinct checks (§1.6).

**Cost of membership at scale.** A balanced million-leaf binary tree has
about twenty sibling hashes per path: roughly 640 bytes with 32-byte
hashes, before any additional structural path. Hashing downloaded object
bytes needs one pass; verification time should be measured. Two costs to
design around are:

- *Path transfer.* For approximately 700,000 addresses, separate paths at
  that depth would cost roughly 450 MB. Bulk mode instead ships each
  shard's sorted leaf address list (32 bytes per leaf, about 22 MB for that
  address count) next to the certificate; the consumer authenticates the
  leaf roots and tree shape to the verified subject root, then recomputes
  each shard root from its list. Membership becomes a local binary search with no hashing and
  no network. Individual paths remain
  for the sparse case, a few constants from a library not otherwise
  pulled.
- *Round trips.* One request per constant, sequentially, is minutes to
  hours over a large closure regardless of hashing. The resolver walks the
  closure breadth first using the refs in each constant's bytes and
  requests each level in one batch; the server can also serve prebuilt
  closure packs for common roots, which is what `ix pack` thin bundles
  already are.

Verification is cached per machine. A coverage record binds the address,
subject root, checker/profile and accepted assumptions or policy; builds
reuse it only under matching conditions. Immutable object bytes need one
content-hash check on admission to the local store. Coverage under a new
root needs new membership evidence, not another typecheck. The certificate
and its leaf index are verified once per applicable release/profile.

What forces bulk is Lean, not Ix: `import` loads whole modules and their
transitive imports eagerly, and `Environment` has no lazy constant lookup.
Upstream's own seam softens this: the pinned toolchain writes exported,
private and server olean levels, and dependents elaborate against the
exported interface. Mapped onto Ixon: interfaces, visible bodies and extension
state are eager per effective imported module. The current ix ingress
faults whole constants, including bodies, even for a type query. Making
body transfer depend only on actual unfolding needs a separate interface
lookup and authenticated body-loading path (§5.2). This does not require
making every Lean environment lookup an RPC.

### 5.1 Transport: HTTP first, iroh at the second provider

Because every object is self-verifying, transport and topology are
swappable without touching the certificate or membership design. The
resolver should sit behind a provider interface from the start.

An Ixon address is BLAKE3 over the canonical bytes, and iroh-blobs
addresses content by BLAKE3 over the bytes, so a constant is already an
iroh blob under its own address and a closure pack is a hash sequence
fetched in one request. iroh itself (1.3.0 at the time of writing, stable
since the 1.0 line) provides QUIC dialed by public key, hole punching with
relay fallback, DNS and pkarr address lookup, and auth and screening
hooks; blobs, docs and gossip are separate crates. ix pins iroh 0.97 with
example-derived put/get code over an in-memory map, which is a rewrite
either way.

- *HTTP is enough* while there is one provider: immutable blobs keyed by
  hash are ideal CDN objects, CI runners dial out and keep no state, no
  daemon or keys or relay are needed, and HTTP/2 plus closure packs handle
  the small-object overhead.
- *iroh pays* for prover ingress (CI pushing to GPU boxes behind NAT with
  the auth hook on the write path), for the second provider onward (every
  store becomes a provider dialed by public key; mirrors, LANs and
  air-gapped sites need no server), for release pointers (a record signed
  by the maintainer's key via pkarr or an iroh-docs namespace is the
  label-to-root mapping with no central index), and for large immutable
  artifacts that want verified resumable transfer.
- *Costs:* key and endpoint management, connection setup latency through
  a relay, running a relay rather than depending on public ones, UDP
  blocked on some networks with the HTTPS relay path as fallback.

Decision point: integrate iroh when the second provider appears or when
prover ingress needs it, whichever is first.

### 5.2 Authenticating interfaces without downloading proof bodies

Today a constant's address hashes its complete canonical bytes. A
certificate and membership path for address `a`, together with a claimed
type `T`, establish neither that `T` is the type stored at `a` nor the
meaning of its reference indices. Full-byte hashing establishes that
binding, but defeats a type-only download.

There are three concrete implementation choices:

- **Check new results at use:** accept the maintainer's interface as an
  elaboration input; independently check new Ixon using original full
  constants. This preserves the existing claim format and avoids bulk
  dependency materialization, while still downloading whole constants
  touched by the check if they are not already exported locally. This
  validates the new result; it does not audit all cached olean declarations.
- **Prove the interface projection:** retain existing constant addresses
  and add an auxiliary proof binding an interface root to the covered
  subject root. For each interface record, establish the original
  address's membership and the projection of its bytes under a pinned
  schema. Batch/aggregate those records per module or release. Local
  lookups can then use authenticated types and fetch bodies only where
  needed. This is a new claim/importer capability, not current behavior.
- **Change the object commitment:** separately commit to interfaces and
  bodies in a future anonymous format. This may permit cheaper openings,
  but changes identity and checking/proving machinery. It is unnecessary
  for the first demo and should be compared with auxiliary proofs first.

An interface record must bind universe arity, kind/safety and the
references needed to interpret its type, not just an expression hash.
Ixon's expressions use the enclosing constant's `refs`, `univs` and
`sharing` tables; mutual projections also need their block context.
Use a canonical self-contained projection or authenticate the necessary
table slices. Transparent definitions and inductive computation rules
cannot be replaced arbitrarily by signatures. Body-less theorem views
retain their certified origin and are never counted as newly introduced
axioms in the published artifact.

`RevealConstantInfo` and `run_reveal` in `Ix/IxVM/Kernel/Claim.lean`
already demonstrate selective field checking against a verified
constant. Their expression-field hashes alone are not a complete
frontend interface: the enclosing tables, coverage and import projection
still need binding. Reuse that machinery where applicable rather than
assuming that existing `CheckEnv` or `Reveal` supplies the full protocol.

For the ix checker, splitting type and body lookup is additional work:
`infer` currently obtains a whole `KConst`, and `whnf` can unfold theorem
bodies as well as definition bodies. Preserve those semantics and fetch
on demand; do not assume all theorem bodies are universally dispensable.
For the Lean frontend, reproduce the selected module's exported/private
view rather than exposing every body as `import_ixe` currently does.

### 5.3 Binding downloaded oleans to the certificate

The current proof authenticates Ixon declarations. It has no claim about
an `.olean` file hash. To strengthen cache trust, establish both the
typing claim and the correspondence from the actual cached declarations
to that claim. Merely signing or hashing a manifest containing both an
olean hash and a proof root establishes their association by a publisher,
not their logical correspondence.

**First mechanism: local export and comparison.** A proposed cache audit
performs the following steps on new artifact bytes:

1. Load the compiled logical declarations from the actual olean parts,
   including full private declarations where required. Use a dedicated
   reader/export path; do not re-elaborate source or execute its tactics.
   Disable unnecessary frontend extension initialization in the audit
   process where supported. The reader/compiler remains part of the
   correspondence trust base.
2. Compile the declared logical scope to canonical Ixon and derive the
   name-to-address bindings from those declarations. Resolve dependency
   references from previously audited artifacts or audit them recursively.
   Substituting an unaudited server-supplied name index would bypass the
   correspondence check. Pin format, primitive addresses and compiler
   behavior, including transformations and auxiliary declarations.
3. Establish coverage of every required resulting address by the verified
   certificate, with accepted assumptions and axiom policy. Per-address
   membership or a bulk leaf index works even when the proof's structural
   root differs from the catalog's canonical root. Reject missing or
   unsupported declarations in the advertised scope; partial export must
   not become a claim that the entire cache was validated.
4. Compare the logical views the local frontend/kernel can consume with
   the corresponding full declarations. In module mode, exported theorem
   entries may omit proof bodies and present as axioms. Validate that
   their types, universes, kinds/safety and available computation rules
   agree under the permitted import projection. Check the relevant
   exported/server/private parts and import modes; checking only the
   private declaration map could miss a tampered exported type. These
   presentations must not become additional permitted logical axioms.
5. Store the admission result keyed by cryptographic hashes of the actual
   artifacts and resolved dependencies, import mode, audit/compiler
   version, scope and accepted claim/profile/policy. Reuse it for unchanged
   artifacts in the protected store. Lake's build traces and mtimes are
   useful scheduling hints, not sufficient cryptographic admission keys.

The exported/full distinction is part of
[Lean's declaration projection](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/AddDecl.lean#L91).
Ix already deliberately loads full-content imports for compilation in
`Ix/Meta.lean`; compiling only the exported theorem presentations would
produce different objects with missing proofs. That existing behavior
does not yet implement the comparison between all consumed import views.

The compiled-module loader in `Ix/Meta.lean:getCompileEnv` and the FFI
entrypoints `rs_compile_env_anon`/`rs_compile_env` in
`crates/ffi/src/compile.rs` provide starting points. The current
source-file CLI still needs a direct artifact input path (§1.3).

This audit reads, canonicalizes and hashes existing terms. It avoids
rerunning the library's source elaboration and full dependency proof
checking, but it is not just a checksum of the files. As a baseline,
[PR #658](https://github.com/argumentcomputer/ix/pull/658) reports a full
canonical Mathlib export of 679,499 constants taking roughly 2¼–2½
minutes and 18.7 GB on a shared Ryzen AI 9 HX370 machine. This is a
compiler benchmark, not an end-to-end admission benchmark: import-view
comparison, artifact hashing and certificate verification add work.
Measure first admission and incremental admission separately.

**Per-module admission.** Export a module against address bindings from
already audited dependencies, and cache its result against those exact
dependency artifacts. A server's name index alone cannot establish those
bindings; auditing the referenced module only later leaves the current
admission conditional. Recursively audit required bindings before
acceptance. The compiler already has name/address lookup maps, and
`Ix/Commit.lean` seeds `CompileEnv.nameToAddr` from a compiled base;
loading an external audited index is additional work. Mutual blocks,
auxiliary names and call-site adapters need the same treatment as in a
full export. This offers finer reuse and potentially lower peak memory,
which need measurement, rather than requiring a full Mathlib export for
each changed cache artifact.

**Downloads.** The local audit can retain the Ixon it generates, avoiding
a second full-corpus download. In addition to ordinary build artifacts,
it needs the certificate and authenticated coverage data: for example,
shard leaf lists contain 32 bytes per address, about 22 MB for 680,000
addresses before framing and compression. Verify the lists against the
leaf roots and aggregation structure committed to by the proved claim.
Do not compare the local canonical content root directly with an
unrelated structural aggregation root. The proposed wrapper carries the
required roots and tree shape; current `ix verify --aggregate` instead
reconstructs that structure using `--ixe` and `--ixes` (§10). Proof size
and verification cost depend on the chosen certificate profile and need
separate measurements.

The resulting assurance is scoped: the consumed logical declarations
correspond to objects accepted by the designated Ix checker, under the
accepted axioms and the correctness of the reader/translation/projection
bridge. It does not certify arbitrary tactic code, initializers, native
executables or notation behavior. That frontend provenance trust is
already present with ordinary cached oleans. The compiler's partial
verification work must not be described as a completed proof of the
entire correspondence bridge.

**Later mechanism: prove the artifact correspondence.** A new proof
could bind the cryptographic root of the raw artifact bundle to the
logical root by checking the decode/export/projection relation under
pinned format and toolchain semantics. Compose that with the typing
certificate. Clients would hash downloaded bytes and verify the proofs,
without repeating canonical export. Including the raw hashes as public
inputs without checking this relation is insufficient. This requires
new proof machinery and a cost study; current `CheckEnv` and `Catalog`
claims do not establish it.

**Optional trusted pairing.** A user may instead accept the maintainer's
assertion that the exact olean hashes correspond to the certified root.
This keeps today's build-artifact trust while adding independently
verifiable evidence for the associated Ixon. Label it separately from a
locally audited or proof-backed correspondence. Independent builders can
reproduce and attest to the pairing, strengthening its provenance without
turning that attestation into a proof of the relation. Recipients that
consume only certified Ixon do not need an olean correspondence check.

## 6. Producer flow

- A library's existing local/CI workflow builds and compiles its Ixon
  pieces. Catalog assembly records the snapshot and source pins. The
  first driver may take complete pieces; missing-object uploads are a
  later transport optimization, not existing catalog behavior.
- A persistent worker restores its certified corpus and proof caches,
  computes newly required subjects, proves the delta and aggregates with
  retained evidence (§7.1). It consumes Ixon and does not elaborate Lean.
  The same driver can run locally on a proving machine before any API or
  GitHub Action integration is added.
- Publish the certificate, snapshot inventory, coverage evidence and
  authenticated source association. Olean hashes and correspondence
  audits can be added for the separate cache-trust product (§5.3).
- The hosted prover is an untrusted producer. Authentication on the write
  path (GitHub OIDC is enough) is for abuse control and provenance, never
  for soundness.
- The service's store is one long-lived corpus across libraries and
  releases, deduplicated by address. Reuse of checking evidence also
  depends on compatible claims, profiles and partitions (§7).

## 7. Incrementality

**The ripple.** References are full addresses, so one edit re-addresses
its entire reverse-dependency cone. `ix diff` separates root edits from
rippled re-addressing. Re-serialization and re-hashing produce the new
identities, not evidence that they typecheck. Reducing the corresponding
proving work requires compatible existing claims or a new reuse relation.

**Evidence reuse at claim granularity.** Leaf proofs are reused by claim
digest through the shard-proof index; join subtrees through the aggregate
cache. The index checks the exact `CheckEnv` claim and verifies its proof;
it is not a per-constant proof cache. Changes to a shard's subjects or
assumptions change its claim, while a matching claim can survive a move
to another manifest position. Join reuse likewise requires matching
composition inputs and verifier conditions. Constant addresses separately
enable object deduplication; they do not guarantee reusable checking
evidence for an arbitrary new partition. See `Ix/Cli/ShardProofIndex.lean`.

Independently running `ix shard` on each whole environment recomputes its
byte-balanced min-cut, so an edit can invalidate claims beyond the
declarations it changed. `ix catalog prove --base` instead preserves the
certified partition and partitions newly required blocks. The amount of
cross-snapshot reuse and the cost of growing that corpus need measurement;
release transport remains separate from this local proving driver.

**Stability over balance.** Preserve existing claim boundaries instead of
running a global min-cut for each commit. Existing `ix shard refine`
preserves untouched leaves and tree positions while splitting leaves to
fit RAM, and protects leaves with verified cached proofs. It operates on
one environment's partition; it is not a cross-commit planner. Its exact
cover checks reject removed or newly uncovered blocks. Use its splitting
machinery for new work, and add explicit revision planning.

### 7.1 First implementation: retain certified content and append new work

Keep two inventories:

- `S`: the complete anonymous address set of the current snapshot catalog.
- `U`: the union of subjects covered by retained, compatible certificates,
  including historical declarations. Bytes in a store without verified
  evidence are not members of this certified set.

For a new snapshot, the candidate new subjects are `D = S \ U`. Prove
those subjects with their thin dependency frontier as assumptions, then
discharge that frontier using the retained evidence and other delta
shards. The resulting corpus covers `U' = U ∪ D`, and the release records
that the current snapshot is `S ⊆ U'`. A replaced declaration's old
address remains a valid historical subject; its new address and any
rippled addresses enter `D`. Deletions and reversions can therefore need
no new checking proof when all required addresses already have evidence.

This avoids re-proving unchanged neighbors just because an old shard also
contains a declaration no longer selected by the current commit. Old and
new versions coexist anonymously by address, while the current catalog
and name index select the published version. Retaining historical names
as active frontend declarations is unnecessary.

The initial driver uses existing fat pieces and an anonymous merged
archive, exposed by `ix catalog prove CURRENT.ixc --base BASE.ixc`:

1. Export the current snapshot and assemble/validate its catalog, with
   one member for the single-library demo. Read the prior catalog's
   attached proving record to select a compatible certified base. Use
   address-set differences as the scheduling truth; `ix diff` supplies the
   human explanation of intrinsic edits versus ripple. Names or Git
   changes alone cannot establish reusable evidence.
2. Restore a compatible certified base with its pieces, final partition,
   claim index and aggregate cache. `ix merge` can materialize the
   anonymous union of the base and current pieces; it deduplicates
   identical addresses. For an initial implementation, accept that this
   still reads and writes corpus-scale data.
3. Carry old ownership and tree structure forward. Partition only newly
   required work, append fresh leaf IDs, and construct a tree retaining
   the old tree as a subtree. Keep mutual blocks and their projections
   coherent. Reconstruct exact old subject/frontier claims and verify
   that they match the cache before classifying them as hits.
4. Run existing `ix prove ... --skip-proven` against the combined plan,
   persisting any budget-refined manifest as the next baseline. New
   shards assume already certified dependencies; they do not re-prove
   those dependencies. Execution can still read dependency terms for
   inference and unfolding: thin assumptions do not imply a thin witness
   (`crates/ixon/src/shard_claim.rs`).
5. Run aggregation with its cache enabled and the same proof profile.
   The scheduler already probes from the root downward and skips proving
   beneath a cached aggregate subtree. Preserve the pre-compression root
   and intermediate proofs suitable for future composition, as well as
   any terminal certificate published to users.
6. Verify the result, establish coverage of `S`, and publish the snapshot
   descriptor. Only then advance the certified corpus record. A failed
   job can retain completed valid proofs without marking its whole
   snapshot certified.

There are remaining preparation costs. Current aggregation takes one `.ixe`
and one `.ixes`; the retained historical union must be that environment,
not the new snapshot alone. `prepare_run` reconstructs every shard and
`validate_root_statement` requires coverage of that whole environment.
The current CLI also loads the selected leaf proof wrappers before the
scheduler can reuse an ancestor, so retain those inputs even when the old
root is cached. Root-first *proving* reuse is implemented; a driver that
accepts a prior root plus a delta without that full preparation is not.

The current ownership rule assigns projection wrappers to their mutual
block's shard. If a later snapshot introduces an additional projection
of an already owned block, its old subject set can expand. Detect this by
reconstructing claims; either rebuild the affected leaf, or later support
explicit address ownership that preserves the old claim. Establish full
block-family coverage in the baseline where possible. Do not assume that
every address-set append automatically leaves every old leaf unchanged.

Pin object format, primitives, checker/verifying keys and proof parameters
for a cache cohort. The initial driver conservatively hashes the entire
`ix` executable and additionally pins the object format, structural
threshold and allowed axiom addresses. Finer semantic/key pins remain
future work. The existing leaf index is keyed by claim digest and
verifies with the active system; a service can namespace it by profile
to avoid competing incompatible entries. Aggregate keys already include
the aggregate key, recursion parameters and outer claim. A commit hash
identifies a snapshot record, not the reusable proof content.

Axiom policy applies to the accumulated evidence, including historical
subjects; an empty assumption root alone is insufficient (§3). Do not
accumulate a forbidden axiom and then label a later selection axiom-free.
The first demo should use a fixed accepted policy for the entire cohort.
The release's current inventory and corpus coverage are separately
authenticated, and the corpus root must never be labeled the exact
current-snapshot root.

### 7.2 Costs, retention and the exact-snapshot alternative

Warm cost consists of export/diff and corpus preparation, new subject
execution/proving (including required dependency ingress), new aggregate
joins and optional terminal compression. Cached proof verification and
I/O are additional costs. A small source edit need not yield a small
`D`: every full-address reference to an edited constant can ripple. This
scheme avoids gratuitous partition churn; it does not prove a theorem
under new addresses using evidence for its old addresses.

Appending each delta as a sibling of the previous root is simple, but
grows tree depth with the number of updates. Start with a bounded sequence
of commits; then measure an append-oriented balanced forest of immutable
subtrees or periodic corpus checkpoints. Those operations may require
new join proofs. Archive growth, membership paths and full preparation
can eventually dominate even when leaf proving stays incremental.

If certificates must cover exactly the current snapshot, retain unchanged
leaves whose full subjects still belong to it, rewrite affected leaves,
and update only the necessary aggregate ancestors. This trades historical
retention for re-proving unchanged subjects co-located with deleted or
replaced ones. Compare the two policies on actual successive commits
before building an elaborate stable partitioner. Catalog storage chunks
and proving shards need not have the same boundaries (§8).

### 7.3 Later research and frontend invalidation

**Proposed evidence reuse at constant granularity: the body-edge set.**
The kernel reads each reference either by type (every `.const` it infers)
or by body (only when delta unfolding fires, `crates/kernel/src/whnf.rs` Defn branch,
which covers definitions and theorems alike). If the proven execution
commits to the set of references whose bodies it read, a proof of
`Check(C)` is evidence for any C' obtained by retargeting references that
are outside that set to constants with the same type under the same
substitution. The derivation never looked at those bodies, so it is the
same derivation. Consequences:

- a proof-only change to T invalidates evidence only for dependents that
  actually unfolded T, which are then legitimately re-checked;
- no new identity or hash is needed: the Ixon address stays the only
  identity, the body-edge set is an annotation the proven run emits, and
  reuse is a relation between two addresses checked over their bytes;
- the relation is a cheap claim (working name: rebind): C' is C with refs
  retargeted, no retargeted ref is a body edge, and every retargeted ref's
  type is unchanged under the substitution. Aggregation composes an old
  `Check` with a rebind instead of re-proving. Expressions reference
  constants through indices into the constant's `refs` vector, and the v4
  sharing table is a function of those expressions, so retargeting changes
  the `refs` vector only: expression bytes and sharing table are untouched
  and the rebind check is a vector substitution plus a re-hash;
- finding the old C needs no index: the name layer is the join key `ix
  diff` already uses, and the byte check is what makes the pairing count;
- the set must be committed by the *proven* execution, so the IxVM
  `verify_claim` program accumulates body reads and exposes their root in
  the claim. A Rust-kernel counter is the measurement tool, not evidence.
  Over-approximation is sound, under-approximation is not.

Constants are faulted in whole, so the set cannot be read off the lazy
ingress; it has to be marked at the unfold site.

**Superset coverage.** Composing old leaves, rebinds and fresh proofs
yields a subject set that is a superset of the new snapshot's selection.
A superset certificate is sound for coverage; the issue is binding, not
soundness. Resolve with a subset claim verified by Merkle membership over
the selected addresses, or by a structural audit of leaf sets at
verification time, plus periodic from-scratch proving to compact. With
constant-granularity reuse this is no longer optional.

**What still ripples.** Edits to a statement, to a def body that
dependents unfold, or to an inductive propagate exactly as far as the
kernel's actual dependence, and the frontend problem is untouched.

**Frontend incrementality is a separate cache.** The local driver or
hosted frontend can retain completed module results and, later,
checkpoints before source commands. A reusable checkpoint must match
source, incoming frontend state, options, toolchain and tracked external
inputs. A new instance or simp registration can invalidate elaboration
even if every existing theorem's type and proof is unchanged. Arbitrary
commands can perform I/O, so a generic command cache needs conservative
invalidation or explicit effect tracking.

For an edit inside Mathlib, reuse unchanged cached oleans, elaborate the
edited module locally, and rebuild affected downstream modules according
to their frontend dependencies. Retain local outputs between builds. Skip
unchanged commands within the edited file only when checkpoint validity
has been established. A certificate does not by itself authorize skipping
those frontend effects. Admission records for untouched dependency
artifacts remain reusable. Rebind is a proposed
checking-evidence relation; it does not solve source elaboration reuse
and is not a prerequisite for the local development loop.

**Lake's existing invalidation boundary.** In pinned Lean 4.34.1, the
artifact contribution of an imported module depends on how it is imported:

| Import of a module-mode dependency | Artifacts contributing to its import trace |
|---|---|
| Ordinary module import | Exported `.olean` |
| `meta` import | Exported `.olean`, `.ir.sig` and `.ir` |
| `import all`, or import from a classic non-module consumer | Exported, server and private olean parts, plus `.ir.sig` and `.ir` |

These are combined with the applicable transitive import traces. The
consumer's trace also includes its source, Lean/toolchain, options, module
and package identity, arguments and relevant extra targets/libraries.
The files supplied for an import can exceed those hashed for invalidation:
the builder also includes server and IR artifacts in its ordinary module
import artifact set. A narrow trace is not a promise of equally narrow
downloads. See
[import trace selection](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Build/Module.lean#L296),
[exported artifact sets](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Build/Module.lean#L476)
and [build inputs](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Build/Module.lean#L554).

For example, module B imports A normally and refers to A's theorem T.
Changing T's proof rebuilds A. If the exported artifact bytes and all
other traced inputs remain unchanged, B can reuse its elaboration result.
Calling the edit "proof-only" is not sufficient to guarantee that outcome;
frontend effects or generated declarations may change the exported bytes.
An `import all` or meta dependency can have a different outcome.

Even when B's elaboration is reused, its Ixon export must use T's new full
address. That can re-address B's declarations and change their shard
claims. The compile-against-index step must re-resolve those references
against the new snapshot; an unchanged olean does not authorize reuse of
an old Ixon piece. Frontend reuse, object reuse and proof reuse must each
be reported separately. Moving the job to a remote builder changes none
of these invalidation rules. Nix derivation reuse is a further boundary,
with explicit Lake artifact seeding as described in §1.6.

## 8. The catalog's role in incremental proving

Reuse the catalog work from PR #584 for the artifact inventory. It already
represents library pieces, their source/toolchain pins and dependencies,
and the anonymous union of their declarations. An unchanged member root
is a useful coarse reuse signal; changed members still share most of their
addresses with the old corpus. This applies across commits and across
libraries sharing Mathlib. No server-side elaboration is needed.

**Single-library contract.** Every published snapshot is a catalog. Start
with one member whose `.ixe` contains the library and its dependency
closure. Reuse the existing label, source pin, toolchain, dependency list,
member/content roots and file hash/size fields. This gives the proving
driver and service one artifact contract from the first demo onward.
Keep the current snapshot's catalog immutable; subsequent commits produce
new catalogs and can reference prior evidence for reuse.

**Proving metadata.** The driver attaches a versioned `proving.json` record
within the catalog directory
containing the profile/policy, prior catalog/evidence references, corpus
identity, final partition and assumptions, proof references and coverage
of the current snapshot. Existing catalog readers ignore additional files,
so this can begin as an attachment without changing the manifest encoding.
`ix catalog verify` does not validate this record or its proofs;
`ix catalog verify-proof` checks its manifest binding, profile, corpus
coverage and aggregate evidence. A release descriptor must separately
authenticate the expected record and source association.
Proof objects may remain in the persistent proof store with addressed
references from the attachment.

Keep logical catalog roots independent of proof metadata: adding a proof,
changing a proving plan or publishing another proof encoding must not
change declaration identity. The record binds the immutable manifest's
hash, while claim/profile keys determine proof reuse. A source-pin change
can therefore create a new snapshot record without forcing re-proving of
unchanged claims. The reserved trailing sections can later provide typed
proving metadata once its schema is established.

Three identities have different jobs:

| Identity | Meaning | Reuse consequence |
|---|---|---|
| Catalog member root and `content_root` | Canonical sets of anonymous declaration addresses | Identify unchanged logical content independently of names and storage layout |
| Snapshot descriptor and member metadata | Which source revisions and named library pieces the release selects | Identify the current snapshot within the retained corpus; authenticate pins separately |
| Shard claim and aggregate statement | Subjects checked, frontier assumptions and compatible proof system | Determine which existing proofs can actually be reused |

`members_root` commits to member environment roots, not the labels or
source pins; authenticate the complete manifest/descriptor for provenance.
Nor does `ix catalog verify` prove typing: it checks artifact structure,
roots and coverage, with `--deep` adding file and constant hash checks.

For §7.1, keep the current snapshot catalog and the cumulative corpus
inventory distinct. For example, the current catalog selects
`Mathlib@B`, while the proof corpus can contain the anonymous union of
`Mathlib@A` and `Mathlib@B`. Prove only B's newly required addresses;
unchanged declarations are shared, and old versions remain evidence
without being part of B's selection. A multi-library catalog similarly
shares a certified dependency closure instead of proving it per member.

Existing storage and driver capabilities:

- Fat catalogs contain self-contained `.ixe` members with overlapping
  closures. `ix merge` deduplicates their anonymous union for the current
  one-env/one-manifest proving pipeline. It is suitable for the first
  prototype, although fat storage duplicates bytes across revisions.
- A thin delta cannot simply be passed to `ix catalog assemble` as a fat
  member: the assembler rejects nonempty assumptions. Keep current closed
  pieces and a separate delta proving plan initially.
- The chunked profile specifies disjoint storage chunks with first-owner
  ownership and has verification support, but the current assembler does
  not produce it. This is relevant to persistent corpus deduplication;
  an address store is an alternative, not an implemented replacement.
- The TruthMines driver already caches compiled pieces against the pin
  closure, toolchain, Ix version and format. That saves unchanged member
  compilation; the incremental driver's address/claim planner handles
  proving reuse within a changed member.
- Trailing sections reserve space for an aggregation tree and per-unit
  assumption roots, but readers currently preserve them opaquely.
  The catalog's attached proving record initially carries the `.ixes`
  plan, proof profile and evidence references; a typed manifest extension
  can follow when the protocol is established.

Keep storage chunks distinct from proof shards. Rechunking preserves the
catalog content root, whereas repartitioning subjects can change every
shard claim. Content deduplication alone therefore does not supply proof
reuse. Preserve the claim partition explicitly, even when storage changes.

Finally, the canonical catalog root and a structural aggregate root are
different commitments. Authenticate the snapshot's full address set
against its catalog root and establish coverage under the proved root,
using leaf lists or membership evidence. For the historical corpus policy,
the intended relation is subset coverage, not equality of those roots or
sets. The existing `Catalog` claim variant has no prover; implementing it
is not required for the initial driver. Coverage validation plus an
authenticated snapshot descriptor is sufficient for the proposed demo.

## 9. Deferred: certificate-aware Lake and Lean integration

The short-term driver needs only the ordinary build/export workflow and
an explicit proving request. The following tighter build-cache integration
is future work and does not gate incremental proving.

This future integration preserves the existing frontend and build graph:

- **Lean/Lake** load cached imports, run tactics, check changed local
  declarations and retain ordinary module outputs. Custom targets can
  invoke artifact export, cache audit, Ix validation and publication.
  A wrapper can fetch artifacts and require admission before a build;
  the acceptance test must ensure it checks the artifacts actually used.
- **The Ix auditor** performs §5.3 once for new dependency artifacts and
  records the accepted bindings. A direct compiled-module exporter also
  supplies the publication path, avoiding repeated source elaboration.
  Separate per-module audit/export cache keys include resolved dependency
  addresses, not just Lake's frontend trace (§7).
- **The service** builds dependency cache misses, checks/proves requested
  logical artifacts, and publishes ordinary build outputs with evidence.
  Local edits need no service call while their dependencies stay fixed.
  Dependency build requests and publication proof jobs remain separate.
- **Nix packaging through lean4-nix** can pin these tools and distribute
  the same olean bundles, release descriptors and certificates. Its
  existing package/seed granularity is described in §1.6. A substituted
  producer verification record does not replace client proof verification
  and artifact correspondence checking under an independent policy.

The first integration needs an executable/custom target and cache
admission plumbing, not a replacement importer or Lake fork. Existing
Mathlib cache tooling can supply the build artifacts. The ordinary
language server continues to use oleans; a new LSP plugin is out of scope.

An alternate Ixon import path remains possible: `import_ixe` supplies a
kernel-declaration baseline, while interfaces, persistent entries and
executable support would be needed for full frontend compatibility.
The following frontend-export research is retained for that optional
direction, not as a gate for certificate-backed ordinary caches.

### 9.1 The mechanism, with one example

Lake combines source and build inputs with import traces selected by
import mode (§7). A valid local or remote artifact can satisfy the job;
otherwise stock Lake runs `lean`, which loads its normal import artifacts,
elaborates and checks new declarations, and writes module outputs.
Certificate-gated admission would replace trust in imported constants'
typing. Source provenance, frontend behavior, executable support and
Lake's artifact integration remain separate concerns.

Lean's import artifacts supply three kinds of data, with executable IR
also stored separately in module mode:

| Part | Consumer | Under ix |
|---|---|---|
| Kernel constants: type and value, with frontend names | elaborator and kernel | Audit olean declarations/import views against certified Ixon (§5.3) |
| Extension entries: instances, simp attributes, notation and macros, structure and match info, reducibility | elaborator | Retain in ordinary oleans; behavior is not covered by the typing claim |
| Compiled IR for tactics and initializers | interpreter | Retain ordinary build outputs; build-tool provenance trust applies |

Separate frontend serialization is unnecessary for this workflow.
The certificate audit concerns the logical declarations consumed through
these artifacts; the normal frontend keeps its existing extension state.

```lean
-- Demo/Main.lean
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Ring

theorem my_thm (a b : ℕ) : a + b = b + a := by
  ring
```

- `ℕ` is notation: frontend metadata.
- `+` uses overloaded addition through typeclass resolution. The instance
  definitions are constants (Ixon); their registrations and priorities
  are frontend entries.
- `ring` is Lean code in `Mathlib.Tactic.Ring`: definitions are constants
  (Ixon); running it needs executable support; its simp lemmas are
  constants plus `@[simp]` entries (both).
- The produced proof term refers to certified declarations; the local
  kernel checks the new term when `my_thm` is admitted.

Build:

1. Fetch Mathlib's normal build cache. A proposed `ix sync` authenticates
   the release descriptor and verifies its certificate and coverage index.
2. Audit newly downloaded artifacts against the certificate (§5.3), or
   reuse their prior local admission record.
3. `lake build` elaborates `Demo/Main.lean` normally. `ring` uses the
   cached registrations and executable support. Keep Demo's local oleans
   across edits; unchanged Mathlib imports need no audit or proof job.
4. When ready to publish, the proposed compiled-artifact exporter produces
   Demo's Ixon with the audited dependency bindings. Check it and submit
   a proving request. Aggregate its dependency frontier with compatible
   Mathlib evidence according to the supported partition protocol (§7).
5. A recipient verifies the expected certificate claim and release
   association with no Lean build environment.

Incorrect registrations can make a tactic fail or change the elaborated
statement. Checking the resulting term protects its validity relative to
the admitted declarations, not the user's intended source meaning.
Executable metadata also includes tactics and initializers; the typing
certificate does not establish their runtime behavior. Authenticate
frontend payloads through the chosen release authority, and retain an
independent certificate/checking boundary for mathematical results.

### 9.2 Optional research: export and import of frontend entries

Required only for an alternate frontend artifact format. The incremental
proving demo (§1.3) and hosted-module path (§9.5) do not depend on it.

The extraction hook exists in Lean 4.34.1, the current repository pin at
the time of this design. After a module's compilation tasks complete,
`Lean.mkModuleData` calls the persistent extensions' export functions and
returns their entries alongside constants and import information:

```lean
let data ← Lean.mkModuleData env level
let entries : Array (Lean.Name × Array Lean.EnvExtensionEntry) :=
  data.entries
```

The extension descriptor exposes `exportEntriesFnEx`; the registered
extension stores it as `exportEntriesFn`. Lean's private
`computeExtEntries` helper invokes each exporter once for all levels.
The Ix integration should preserve that behavior when exporting multiple
levels, including completed asynchronous extension state. Export each
module's own contribution: invoking `mkModuleData` on an import-only
wrapper does not export every imported library's entries. Existing
producer artifacts can supply the original per-module entries through
`readModuleDataParts`; parts must be read together because later parts
can share objects with earlier ones. These APIs and their lifecycle are
defined in [Lean's module exporter](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Environment.lean#L1772).

**Ownership and shape.** A module can add a simp registration for a
declaration defined in another module. That registration must activate
only when its exporting module is imported. Store module/import order,
extension identity, entry order, scopes and visibility; keep per-name
indexes as an acceleration structure. A proposed metadata record carries:

- module name, imports, module mode and export level;
- declaration name/address mappings and the existing per-name metadata;
- ordered extension payloads, each with its codec name and version;
- executable-support references, generated names and initialization data;
- toolchain identity and hashes of imported frontend interfaces.

Export the frontend-visible declaration interfaces at the same time,
before dropping constant arrays from the extension payload. The producer
has both public and private views and the full Ixon name map. Preserve
that relation so the consumer need not decompile every proof term just
to recover a theorem type. Legacy modules and `import all` may require
the richer view; do not silently substitute the public interface.

**Encoding.** `EnvExtensionEntry` is opaque and type-erased, not a common
record with a portable serializer. Different extensions choose different
entry types, which may contain names, expressions, syntax or compiler
data. Exporting those values does not automatically replace references
with Ixon addresses. The proposed implementation has two stages:

1. A lossless prototype uses Lean's object serializer for extension
   payloads inside Ix metadata, pinned to the toolchain/runtime. It retains
   module boundaries and omits the top-level constant arrays. This is a
   compatibility encoding, not a portable compact frontend format.
2. Typed codecs cover common extensions, with a registry for library
   extensions. Codecs preserve the complete exported semantics while
   replacing derived indexes with reconstruction recipes where measured
   useful. Unsupported required extensions fail explicitly or use an
   explicitly supported, toolchain-pinned opaque encoding.

Keep frontend names as well as addresses: attributes and syntax operate
on named declarations, and several names may share one anonymous object.
For simp, preserving only theorem name and priority is insufficient in
general; direction, phase, unfolding and scope distinctions must survive.
The codec schema is versioned independently of canonical constant bytes.

**Executable support and restoration.** `mkModuleData.entries` alone is
not the complete executable export. Lean's module-mode writer also uses
`mkIRData`/`exportIREntries` for `.ir` data and tracks generated names and
signatures. Some helpers are private. The importer must provide code for
custom extension registration and initializers before all entries can be
restored, then use the extension `addImportedFn` lifecycle in import order.
Lean's `finalizeImport` takes an `ImportState` whose module representation
is private, so in-memory import needs a supported adapter or an upstream
hook. Extraction, opaque serialization and import adaptation are distinct
tasks; none is implemented by adding a metadata field alone. See
[the writer](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Environment.lean#L1887)
and [the import lifecycle](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Environment.lean#L1975).

**Integration gate for the alternate importer.** Export and restore a small set of modules
containing a simp registration, prioritized/scoped instances, custom
syntax, and an initializer-backed extension. Include a module that adds
an attribute to an imported declaration: a consumer importing only the
declaration's original module must not see that attribute. Elaborate the
consumer with dependency oleans unavailable, verify the resulting
statements and declarations, and compare behavior with the ordinary
source build. Establish this lossless round trip before compacting entry
schemas or attempting full Mathlib coverage. Then repeat with a real
Mathlib tactic, retaining the interface-to-original-address mapping and
checking the consumer's new Ixon. Tamper with an interface type and
confirm that independent checking rejects any resulting invalid term.

### 9.3 Local reconstruction versus regeneration

| Input | Work on the consumer | Role of the certificate |
|---|---|---|
| Certified Ixon plus exported frontend entries | Materialize declarations and restore extension state; rebuild selected derived indexes | Avoid dependency source elaboration and repeated kernel checking |
| Source plus certified Ixon, with a specialized driver | Replay necessary frontend effects while substituting covered declaration bodies | Potentially avoid proof-script execution; not implemented for arbitrary commands |
| Ordinary full source rebuild | Elaborate, execute tactics, check declarations and compile executable support | Initial validation is largely redundant on that machine; portable evidence remains useful to other consumers |

Registration choices cannot be recovered from anonymous Ixon alone:
changing an instance priority or adding a simp attribute can leave every
declaration unchanged. Ordinary source replay reconstructs the choices,
but also reruns elaboration and tactics; skipping the final kernel check
does not skip those costs. A selective replay driver would have to handle
custom commands and their frontend effects, rather than merely scan for
attributes.

For the alternate importer, restoration would be the default dependency
path; source regeneration would be an optional rebuild/audit path.
Ordinary oleans already restore this state in the primary workflow.
Edited modules naturally produce new entries
during their local compilation. Frontend cache keys must include metadata,
toolchain, imported frontend interfaces and relevant build inputs, not
just the anonymous root. Arbitrary command I/O means reproducibility must
be established for the actual build inputs, not assumed from a source
revision alone.

### 9.4 Comparison with lean4export

Source review: lean4export commit
[`66f1fb4`](https://github.com/leanprover/lean4export/tree/66f1fb4bc256072069767fce52d39480e4524869),
format 3.1.0, toolchain 4.35.0-rc3. It exports kernel declarations, not
persistent frontend extension entries. Its parser reconstructs a constant
map and declaration order, not an elaboration environment.

| Property | lean4export | Ixon v4 and proposed frontend export |
|---|---|---|
| Encoding | NDJSON with explicit record schemas | Binary constants; versioned frontend payloads proposed |
| References | File-local name, level and expression indices; constants identified by name | Constants identified by content address; frontend names retained separately |
| Sharing | An expression table across the export | Canonical sharing within each constant; bounded sharing within metadata packs is an option |
| Frontend extension entries | Absent | New module/extension export path (§9.2) |
| Executable frontend support | No IR export; unsafe/partial declarations omitted by default | A separate required part of the frontend payload |

`--export-mdata` exports `Expr.mdata` annotations, not simp registrations,
instance tables or syntax extensions. Even that expression metadata is
not a lossless general codec: the exporter renders values with `reprStr`,
and the current parser restores an empty metadata map. It cannot serve as
the frontend serialization layer. See the
[exporter](https://github.com/leanprover/lean4export/blob/66f1fb4bc256072069767fce52d39480e4524869/Export.lean)
and [parser](https://github.com/leanprover/lean4export/blob/66f1fb4bc256072069767fce52d39480e4524869/Export/Parse.lean).

Useful patterns are explicit schemas and version headers, dependency-first
records, interning, and a readable audit representation. Apply those to a
metadata dump command and typed codecs while retaining binary storage.
Compare sharing as well as encoding size: lean4export's global expression
table is a real deduplication feature despite the text format. For
incremental Ixon transport, prefer bounded per-module/pack tables and
content addresses between packs. The
[format specification](https://github.com/leanprover/lean4export/blob/66f1fb4bc256072069767fce52d39480e4524869/format_ndjson.md)
is a useful schema reference, not a solution to frontend-state export.

### 9.5 Delegating frontend computation to the service

There are two useful delegation boundaries. Neither requires proving the
elaborator's execution: the independently checked object is the resulting
Ixon, with a separate question about its correspondence to the source.

**Whole modules first.** A proposed `lake exe ix build --remote` submits
an immutable workspace snapshot and requests the elaborate and
compile/check jobs of §1.4. The service retains dependency environments
and compiled frontend code, builds misses in dependency order, and returns
diagnostics, new Ixon, a declaration/name map and content identifiers for
the new frontend artifacts. Those artifacts need only be downloaded if
execution will move back to the local frontend. A certificate is a
separate requested result. Module fingerprints include frontend
dependencies, not only the anonymous certificate root.

The request/result protocol must cover more than Lake cache transfer:

1. **Snapshot identity.** Bind a cryptographic source-tree/overlay digest,
   base release descriptor, requested targets, toolchain, platform,
   package configuration, options and other declared build inputs.
   Include dirty edits and selected untracked build inputs; a Git revision
   alone does not identify a developer's workspace. Upload missing source
   blobs against that immutable snapshot.
2. **Graph execution.** Resolve import and build dependencies using the
   actual upstream results. Either the client discovers the next cache
   misses incrementally or the server schedules the whole submitted graph.
   Keep frontend execution separate from publication proving. A remote
   miss is a build request, not an operation provided by `--try-cache`.
3. **Job lifecycle.** Return a job handle bound to the snapshot, with
   progress, diagnostics, cancellation and immutable result identifiers.
   Results from a superseded edit may populate the cache but must not be
   installed as the current workspace's result. Local fallback is an
   explicit execution policy; a remote-only request reports a miss/failure
   unless the caller selected local rebuilding as its fallback.
4. **Publication and admission.** Publish artifacts and cache mappings
   separately from running the job. Bind outputs to the request, validate
   their bytes and provenance, then independently check the delta or verify
   its certificate under local policy. Authenticating a response as the
   service's output does not prove correct source elaboration.

Lake-compatible publication also needs a workspace mapping policy. The
reviewed upstream cache protocol scopes outputs by repository/toolchain/
platform or an explicit scope, and publishes JSONL output maps by Git
revision. It warns on dirty work trees. Do not publish two dirty snapshots
as if they were the same revision: use a distinct snapshot mapping in the
service and an adapter for the client. Lake's build hashes are not
cryptographic integrity commitments; keep the Ix descriptor/object
authentication boundary. See
[Lake cache upload semantics](https://github.com/leanprover/lean4/blob/cd842b6db936b2c5e7e254f011a57eb96fd7cf3b/src/lake/Lake/CLI/Help.lean#L645)
and [revision mappings](https://github.com/leanprover/lean4/blob/cd842b6db936b2c5e7e254f011a57eb96fd7cf3b/src/lake/Lake/Config/Cache.lean#L1034).

This permits ordinary source files, arbitrary library syntax and tactic
implementations, and edits inside Mathlib without downloading its oleans
or tactic runtime to the client. Reusable server state reduces repeated
dependency loading; it does not make an edited module free to elaborate.
Protocol-level incrementality can start at module granularity, with
command checkpoints later. The service may use oleans internally: the
client contract concerns what the developer must fetch and maintain.

During development, either independently check the returned delta locally
with the required certified Ixon objects, or treat server diagnostics as
provisional until a certificate is requested. A verified certificate can
replace local delta checking; a success response, even a signed one, is
not independently verified typing evidence. Avoid GPU proving on every
keystroke. At publication, bind the returned certificate to the actual
new subject addresses and accepted assumptions, not just to a job ID or
source filename.

A source hash in the response identifies the submitted job but does not
prove faithful elaboration of that source. In whole-module mode the
service could return a different well-typed statement. The certificate
would faithfully certify that different artifact. Trust the chosen
frontend for source correspondence, inspect the canonical result, or
validate an independently elaborated expected statement under §1.5's
conditions. Inspection is an audit aid; it is not a source-translation
proof. Proving source-to-term translation would be a separate, much larger
claim. The hosted mode also requires network access and disclosure of the
submitted source; it complements the offline-capable local mode.

**Closed tactic goals later.** Once a local frontend can elaborate a
statement, it can delegate expensive proof search without loading that
tactic's implementation. A possible explicit syntax is
`by ix_remote "ring"`, where the remote script is parsed on the server.
This is a proposed extension, not an existing command. Normal `by ring`
still needs a local registration or a deliberate forwarding adapter.

The request binds the library snapshot, local declaration overlay,
options and a closed expected type obtained by abstracting the goal's
local context and universe parameters. The response supplies a proof
term and any generated declarations, addressed against that same
snapshot. Check all returned declarations and check the proof against
the *client's expected type*, with no unresolved metavariables, extra
axioms or `sorryAx` beyond the accepted policy. A zk certificate is an
optional replacement for repeating that check, provided the proof also
binds the expected type through §5.2 or full verified bytes.

The first endpoint should solve a complete, sufficiently instantiated
goal. Arbitrary tactic states contain metavariable assignments, local
instances, generated declarations and frontend state that are not a
portable RPC boundary today. Tactics that change the environment and
commands such as deriving handlers need a richer effect protocol or
whole-module delegation. Remote proof search also leaves local notation,
typeclass synthesis and statement elaboration intact; it does not by
itself eliminate the frontend package.

## 10. Gaps, in proposed build order

The initial driver implements the core record, planning, retained-corpus
update and cache orchestration in items 1–4 below. Its focused tests cover
the state machine with a simulated backend. Real small-corpus proving,
GPU validation, cross-job coalescing, release packaging and hosted
delivery remain. Planning reports matching claims rather than promising
that every referenced leaf proof is still present and reusable.

Use current build/export tools and existing proof caches first:

1. Define a persisted incremental proving record (§4) over existing
   catalogs, final partitions and proof stores. Make a one-member catalog
   the single-library input and attach the record within its directory,
   binding the manifest and logical roots. Pin compatible profiles,
   declared scope and axiom policy. Retain a baseline's leaves and joins,
   not only its final compressed certificate.
2. Add a planning-only path: compare snapshot/corpus address inventories,
   preserve old ownership, partition new subjects and reconstruct exact
   claims. Report verified cache hits, missing claims, ripple and ownership
   changes without starting a proof. Reuse `ix shard claims` and aggregate
   planning for validation; neither currently plans revisions itself.
3. Implement the retained-corpus update in §7.1, initially with existing
   fat pieces and `ix merge`. Carry the old tree intact, support budget
   splits of new work, and reject uncovered references or duplicate owners.
   Handle new projections of old blocks explicitly.
4. Wire `--skip-proven` and aggregate-cache reuse into a resumable driver.
   Persist corrected manifests and completed evidence, verify reused
   proofs under the accepted profile, and advance the corpus record only
   after successful coverage validation. Identical requests should launch
   no new proving jobs; shared workers should coalesce identical claims.
5. Publish the current snapshot catalog, certificate and coverage relation
   to the retained corpus. A recipient verifies the expected logical scope
   and authenticated commit association without a Lean build (§3 and §8).
   Publish the versioned proving attachment with the catalog; typed
   manifest extensions can follow when the record format settles.
6. Expose the same driver through a proving-only API/Action with a durable
   cache volume. Start with piece uploads; deduplicated missing-object
   transfer is justified by measured upload cost. The worker runs Ix
   checking/proving, not source elaboration.

Optimize the measured warm bottleneck next: retained parsed indexes,
loading only proofs not covered by cached aggregate ancestors, chunked
catalog production or an address store, incremental Ixon export, and an
append-oriented tree/retention policy. Compare exact-snapshot partitions
with historical retention before committing to either at large scale.
Body-edge/rebind proofs are later research if address ripple dominates.

Server-side elaboration, olean correspondence auditing, alternate frontend
packages and custom LSP integration are outside this implementation order.
Their designs in §5 and §9 remain possible follow-on products.

## 11. Measurements that would settle open questions

1. Repeat a certified snapshot with a warm store. New leaf, join and
   compression proofs should all be zero when the same outputs are
   requested. Measure export, corpus scanning, wrapper loading and cached
   proof verification separately from GPU work.
2. A metadata-only change, an added theorem, an isolated proof edit, a
   definition with many dependents, a deletion and a revert. For each,
   report address-set differences, intrinsic edits versus ripple, exact
   claim hits, newly proved subjects and joins. Include a new projection
   of an already retained mutual block.
3. Successive real Mathlib commits: compare global repartitioning, stable
   exact-snapshot leaves and retained-corpus deltas at the same profile.
   Report GPU time and end-to-end latency, including export, merge,
   dependency ingress, aggregation and terminal compression.
4. A second library sharing the same Mathlib base, then a branch and merge.
   Deduplicate by address and exact claim, not repository/commit identity.
   Verify that overlapping fat pieces produce disjoint proof ownership.
5. Cache rejection and recovery: incompatible checker/format/profile,
   corrupt or missing proof objects, incomplete coverage, unresolved
   references, forbidden axioms and interruption after some leaves finish.
   Resume from completed evidence without accepting an incomplete snapshot.
6. Corpus growth over many revisions: retained bytes, leaf-wrapper I/O,
   tree depth, coverage metadata and preparation memory. Compare simple
   append trees, immutable balanced subtrees and explicit checkpoints.
7. Standalone recipient verification without Lean: expected current
   catalog, subset coverage, proof/profile and axiom policy. Demonstrate
   that historical extra subjects cannot be mistaken for current names
   or a source-commit correspondence proof.

Start with a small corpus to validate planning and reuse. Mathlib proving
runs and benchmark sweeps need an explicit resource budget and approval;
source inspection and planning do not establish warm performance numbers.

## 12. Demo sequencing

- **Demo A (warm repeat):** assemble a one-member catalog for a library,
  prove its baseline with the existing pipeline, retain the attached
  partition/evidence record, and repeat it with zero new proofs.
- **Demo B (next commit):** add a theorem over that baseline, prove the new
  subjects, reuse the old aggregate subtree, and verify coverage of the
  new snapshot catalog. Repeat after an isolated edit and a revert.
- **Demo C (shared dependencies):** certify another library over the same
  Mathlib corpus, preserving its existing evidence. Then demonstrate an
  edit inside Mathlib and report the actual address ripple and proving
  work, including cases that remain expensive.
- **Delivery:** wrap the demonstrated driver in a proving-only API or
  GitHub Action. The local/CI Lean build and ordinary olean cache remain
  unchanged. A third party verifies the published logical snapshot.

Success means reuse of compatible evidence across commits, new GPU work
accounted for by missing claims and joins, and verified current-snapshot
coverage. Server-side elaboration and olean cache auditing are separate
projects. Warm performance claims include host preparation and publication
costs, not only the number of skipped leaf proofs.
