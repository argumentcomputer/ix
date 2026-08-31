# Flock Stage 2: direct shard verification and aggregation

Snapshot: 2026-08-31

Status: Phase 1 functional feasibility implemented on `jcb/flock-stage2`;
the matched q=100 performance gate remains unmeasured, with recursion and
rollout deferred because current sizing shows substantial scaling risk

## Implementation checkpoint

The first Phase 1 substrate is implemented on the Stage 2 bookmark:

- canonical `FlockAggregateClaimV1`, `FlockStage2RootStatementV1`, and strict
  root-artifact framing live at the terminal boundary;
- `ValidatedP3ProofV1` and `P3ProofStatementV1` accept explicit ten-word IxVM
  and eighteen-word aggregate layouts while the historical `IXROOT01` API is
  retained as a compatibility adapter;
- the typed witness, transcript replay, PCS/FRI witness, and AIR lowering now
  consume the stage-neutral validated proof;
- `FlockStage2ConfigV1` has a distinct digest and
  `ix:flock-stage2:p3-leaf-verifier:v1` transcript domain;
- `P3VerifierRelationManifestV1` canonically binds the Stage 2 config, P3 key,
  claim layout/entrypoint, typed layout, complete phase mask, exact bounds,
  and compiled circuit digest;
- a real q=2 Aiur/P3 proof with the ten-word IxVM claim shape passes native
  validation, all eleven Flock verifier phases, preflight, proof generation,
  valid verification, and wrong-domain/corrupted-proof rejection; the current
  debug proof bundle is 371,083 bytes and the ignored round trip takes 37.22
  seconds;
- `bench-flock-stage2` now freezes/reimports exact shard fixtures and runs the
  production P3 shape-0 lift or explicitly labelled Flock verifier-core lower
  bound in a fresh process with structured timing, RSS, proof identity, and
  valid/corrupt checks;
- a generated, natively verified q=2 IxVM kernel wrapper over the same shard
  has completed three alternating paired samples: P3 shape 0 has a 14.399 s
  median while the Flock verifier core has a 24.287 s median and 1.81x P3's
  peak RSS; see the matched benchmark plan for the full ranges and scope
  caveats;
- the historical eighteen-word Stage 3 regression still emits exactly
  326,019 artifact bytes and 325,893 payload bytes and passes its valid and
  corrupted verification checks;
- `ix flock-leaf` reconstructs the canonical IxVM key/claim/proof transport
  from a persisted raw proof wrapper and drives Stage 2 preflight or the
  diagnostic prover through the optional Flock FFI;
- the current 4,432,373-byte q=100 raw shard at
  `becb4740c1adf82b1ece4fa3fd230d2992fb263119b8d4d4e78cdd8273bae76f`
  now passes complete evaluated Flock preflight with relation digest
  `c1163b83b88ddd8462ca9adad70e67c06d3d5f3f36ecb5a769b92045393a5b72`;
- phase-isolated `profile`, `pcs-size --queries N`, and `size` modes separate
  native validation, prefix sizing, and full AIR-plus-PCS sizing from circuit
  finalization and proving;
- the production relation has 2,566,088 inputs, 2,567,682 public values,
  56,237,892 total table rows, and exact `nu=24` (16,777,216 rows/table); its
  largest table is Goldilocks addition at 16,353,512 rows;
- exact table geometry and live counts account for 296.65 GiB of primary
  allocations coexisting at the q=100 commit phase, or 370.81 GiB after a
  mechanical 25 percent margin, before circuit/wiring/opening scratch and
  retained pools; the first uncapped run therefore targets a 1 TiB node;
- a directed four-residual zero gate removes Flock's quadratic shared-zero
  equivalence class, Stage 2 add/multiply tables fold result canonicality into
  existing residual words, and an exact sizing pass reduces the initial
  144,128,918-row / `nu=27` construction to the current relation while the
  legacy Stage 3 relation remains byte-identical;
- full q=100 constraint emission takes 45.56 seconds in sizing mode and AIR
  contributes only about 0.11 seconds, confirming that PCS arithmetic—not
  BLAKE3 or AIR—is the row-count bottleneck; and
- cold evaluated preflight succeeds in about 12.9 minutes, of which 680.4
  seconds is `ShapeBuilder::finish`; post-compile evaluation takes about 1.4
  seconds. The next compiler milestone is therefore a pinned compiled-shape
  cache or an upstream serializable/linear-time shape representation.

There are now two q=2 fixtures. The 371,083-byte proof bundle is the synthetic
verifier regression and is not an IxVM kernel proof. The paired benchmark's
246,213-byte compact input is a real IxVM kernel proof generated from the
frozen environment/manifest. Phase 1 has established functional feasibility,
exact production sizing, and a matched small-case baseline, but not production
proving performance. Compiled-shape caching, the uniform application claim and
`CheckEnv` preimage, a second activation/height profile, recursion, and full
q=100 proving/RSS measurements remain unimplemented pending the performance
gate below.

## Preliminary performance assessment

The direct Flock Stage 2 cutover gate remains unresolved. Current measurements
show substantial scaling risk, but they are not an apples-to-apples proving
comparison:

The matched measurement protocol and large-box/cluster handoff are specified
in `plans/flock-stage2-benchmark-plan.md`.

- BLAKE3 is only 92,526 rows (0.16%) of the 56,237,892-row q=100 relation.
  More than 96% is non-native Goldilocks arithmetic, repacking, canonicality,
  and zero assertions. Flock's binary-field advantage is therefore aimed at
  the wrong part of this verifier workload.
- The small q=2 leaf proves in 2.337 seconds after compilation at `nu=12`.
  The real q=100 shard is `nu=24`, a 4,096x larger uniform outer domain before
  accounting for its larger live counts. This is a warning about the likely
  proof-system workload, not a measured 4,096x runtime prediction.
- The apples-to-apples q=2 input is already much larger than that synthetic
  regression: 2,114,302 Flock rows at `nu=20`. Across three samples, its
  verifier-only/same-witness Flock lower bound is 1.69x the median P3 semantic
  lift time, uses 1.81x the peak RSS, and emits a 17.8 percent larger proof.
  That result is unfavorable but cannot predict whether q=100 scaling crosses
  over; it makes W0 a genuine go/no-go experiment rather than confirmation.
- Cold q=100 preflight takes about 12.9 minutes, including 680.4 seconds in
  `ShapeBuilder::finish`. This is an operational problem, but it is not a
  proving-time comparison and may be amortized by a sound compiled-shape cache.

Defer Flock leaf/node recursion and any Flock Stage 1 port until the q=100
performance gate is measured. Preserve the backend, codecs, exact sizing mode,
and regression fixtures as a reproducible feasibility result. The recommended
production path remains, for now:

```text
Stage 1 P3 -> Stage 2 P3 aggregate -> Stage 3 Flock -> terminal SNARK
```

The next useful direct-Stage2 experiment is the explicitly budgeted q=100 W0
probe already specified in the matched benchmark plan: run both the P3 lift
and Flock verifier core over the frozen shard on the same 1 TiB machine and
revision, recording cold setup, same-witness lower-bound proving, peak RSS,
verification, and artifact bytes. A sound compiled-shape cache is still needed
for a production warm path, but it is not required to learn whether the
current cryptographic prover is viable.

## Conditional implementation decision

Build a Flock-backed Stage 2 behind an explicit backend selector while keeping
the current Aiur/P3 aggregator as the production fallback. Advancing beyond
the feasibility backend remains conditional on the matched q=100 benchmark
above.

The target pipeline is:

```text
Stage 1                         Stage 2
Aiur/P3 IxVM shard proofs  ->   Flock leaf verification
                                 + Ix claim folding
                                 + Flock recursive aggregation
                                      |
                                      v
Stage 3
terminal FFLONK/Groth16 proof of one fixed Flock root verifier
```

Stage 1 remains Aiur/P3. This project is about moving the
BLAKE3-heavy verification and aggregation work from the Aiur/P3 recursion
circuit into Flock, not about replacing IxVM proving.

The preferred production design is a tree:

1. a bounded catalog of Flock leaf relations verifies raw Stage 1 proofs;
2. a fixed normalization relation turns every allowed leaf proof into one
   recursive outer proof shape;
3. a fixed steady-state binary node relation, plus only a bounded set of
   bootstrap relations if the tower needs them, verifies normalized children
   and folds their Ix `CheckEnv` statements; and
4. one fixed root relation closes/discharges the recursion state and produces
   the proof consumed by the terminal SNARK.

That design is conditional. The pinned Flock revision has a working
`Chain128` recursion tower, but that tower is specialized to BLAKE3 hash-chain
leaves and application statements. It is evidence that the fixed point can
close, not yet a generic API capable of recursing over the Ix verifier
relation. Generic leaf and node recursion is therefore an explicit feasibility
gate, not an assumed library feature.

If generic recursion does not close, benchmark one fixed-capacity monolithic
Flock relation that verifies and folds an entire shard batch. If neither design
beats the current P3 aggregate on real q=100 proofs, retain:

```text
Stage 1 P3 -> Stage 2 P3 aggregate -> Stage 3 Flock -> terminal SNARK
```

Do not change the default backend until the production corpus, soundness,
terminal-consumption, and rollback gates all pass.

## Why revisit Stage 2 now

The latest complete-verifier optimization is a strong signal:

| Component | Before | After | Improvement |
| --- | ---: | ---: | ---: |
| complete `prove_stage2` | 39.615 s | 3.091 s | 12.8x |
| Flock prover | 1.140 s | 0.140 s | 8.1x |
| union witness generation | 566 ms | 27.9 ms | 20.3x |
| output-buffer return | 160 ms | 1.6 ms | 100x |

The artifact bytes and proof transcript stayed unchanged, and both valid and
corrupted verification checks still pass. That is exactly the kind of
optimization evidence wanted for a protocol implementation: the execution
changed while the proved relation and serialized proof did not.

The current real regression fixture emits a 326,019-byte Stage 3 artifact with
a 325,893-byte production payload. It is nevertheless a tiny q=2 fixture with
active trace heights 8 and 4. It does not establish production Stage 2
performance.

The standing P3 aggregate baseline is four real Init shards at q=100 / PoW 20
on the approximately 512 GiB target box:

| P3 operation | Time | Peak RAM | Proof bytes |
| --- | ---: | ---: | ---: |
| lift, each of four | 98.8-103.0 s | 186.8-195.8 GiB | 8,162,462 |
| lower pair joins | 48.5-48.9 s | about 102.5 GiB | 9,502,843 |
| root join | 85.8 s | 156.9 GiB | 9,455,498 |
| serialized four-shard tree | 10:23 | 195.8 GiB | 9,455,498 |

The reason to investigate Flock is architectural, not merely the 140 ms
micro-result. About 80 percent of the P3 recursive-verifier FFT work has been
attributed to hashing the child proof. Flock represents the repeated Boolean
and BLAKE3 work directly, and the optimized fixture shows that its cryptographic
prover can become a small part of the complete host path.

The same observation does not yet argue for Flock Stage 1. Stage 1 proves IxVM
execution and its arithmetic/AIR semantics; its internal BLAKE3 is native work
inside the leaf proof, not a verifier being emulated by another proof system.
Reconsider Stage 1 only after Stage 2 is complete and profiled.

## What the current result proves and does not prove

It proves:

- the complete Aiur/P3 verifier semantics can be lowered to Flock;
- all eleven verifier phases can coexist in one Flock relation;
- BLAKE3-heavy witness generation can be made copy-free and sparse;
- the Flock proof and transcript are stable across those optimizations; and
- native valid, wrong-relation, and corrupted-proof paths are available.

It does not yet prove:

- that a current q=100, 20-25 MB Stage 1 shard proof fits the relation;
- that one fixed relation covers the Stage 1 activation and height corpus;
- that the relation catalog is bounded independently of individual witnesses;
- that Flock can recursively verify these application relations through a
  fixed outer shape;
- that `Fast128` leaves plus `Slim128` recursion compose to the system
  security target at the maximum shard count;
- that peak RSS fits the intended 256 GiB fleet;
- that claim folding is equivalent to `Ix.Aggr`; or
- that the terminal circuit can consume the resulting fixed root proof.

Those are the gates in this plan.

## Goals

1. Verify every acceptance-relevant part of a raw Stage 1 Aiur/P3 shard proof
   in a Flock relation.
2. Preserve the existing `CheckEnv` statement semantics, including flat and
   structural folding and assumption discharge.
3. Produce one fixed Flock root proof type and one fixed root relation for all
   supported nonempty manifests.
4. Make relation identity, proof-system configuration, capacities, accepted P3
   system identity, and fold semantics externally pin-able.
5. Retain content-addressed resume, deterministic planning, and RAM-gated
   scheduling.
6. Beat the current P3 Stage 2 materially on matched q=100 workloads, not only
   on the q=2 regression fixture.
7. Reuse the Flock-verifier-to-terminal work from
   `flock-terminal-snark-plan.md`, with the Flock aggregate root replacing
   the P3-root verifier proof.
8. Keep the old P3 Stage 2 and old Stage 3 artifacts versioned and verifiable
   throughout migration.

## Non-goals

- Replacing Stage 1 or changing IxVM semantics.
- Lowering q, PoW, or another security parameter to make the comparison look
  favorable.
- Treating a native P3 verification result as a trusted witness bit.
- Accepting a relation or catalog digest supplied only by the prover.
- Preserving byte equality between the old P3 aggregate and the new Flock
  aggregate. They are different protocols.
- Renaming or deleting the current `flock-stage3` workspace during the
  feasibility spike.
- Making Flock zero knowledge. The Stage 2 artifact remains off-chain; hiding
  it is a terminal-backend requirement if privacy is needed.
- Permanently accepting either a P3 or Flock aggregate under one deployment
  policy. Dual support is for migration and rollback, not permanent
  downgrade-friendly consensus.

## Protocol invariants to preserve

The new backend must preserve these properties of `ix_aggr`:

- A raw IxVM child is accepted only under the pinned IxVM verifying key and
  exact `verify_claim` entrypoint.
- Its outer claim has exactly ten Goldilocks words:
  `[0, verify_claim_index, packed_blake3(CheckEnv)[8]]`.
- Every field element and byte encoding is canonical, and trailing bytes are
  rejected.
- Every P3 verifier phase is constrained: key/AIR binding, logUp, transcript,
  Goldilocks and extension arithmetic, AIR/OOD/quotient checks, PCS, Merkle
  paths, FRI grinding/folding, and final polynomial checks.
- Every recursive child carries the same protocol and relation-catalog
  identities transitively.
- Flat folding proves
  `subjects = subjects_left union subjects_right` and
  `assumptions = (assumptions_left union assumptions_right) minus subjects`.
- Structural folding proves
  `subjects = nodeHash(subjects_left.root, subjects_right.root)` and accounts
  for every unique candidate assumption by either carrying it or discharging
  it with a strict Merkle path.
- Canonical trees are strictly sorted and deduplicated; pointer identity and
  host-side set equality are never trusted.
- A singleton manifest is represented by a real unary/pass-through proof, not
  by duplicating a child or inventing an empty proof.
- The verifier receives an expected statement from deployment or caller
  policy. Merely parsing an artifact never establishes cryptographic
  acceptance.

## Stage naming and migration

The current and proposed names must coexist until cutover:

| Current pipeline | Proposed pipeline |
| --- | --- |
| Stage 1: P3 IxVM shards | Stage 1: P3 IxVM shards |
| Stage 2: P3 `ix_aggr` root | Stage 2: Flock verification and aggregate root |
| Stage 3: Flock proof of P3 root verification | removed as a separate stage |
| Stage 4: terminal SNARK | Stage 3: terminal SNARK |

Existing domains such as `IXROOT01`, `IXFLK301`, and `IXFLOCK3` keep
their existing meanings forever. The new backend gets new statement,
manifest, artifact, transcript, and cache domains. No decoder may reinterpret
an old artifact according to the new numbering.

During development, CLI output should call the systems `p3` and `flock`
rather than relying only on stage numbers. Documentation may switch to the
three-stage numbering only when Flock becomes the active Stage 2.

The “do not replace Stage 2” non-goal in
`plans/flock-terminal-snark-plan.md` remains true for the current four-stage
design. This plan conditionally supersedes it only after the cutover gate.

## High-level architecture

### Keep application folding separate from proof recursion

There are two different folds and they must remain distinct in code, metrics,
and review:

1. The **Ix application fold** combines two `CheckEnv` statements into one
   output statement using flat or structural semantics.
2. The **Flock protocol fold** verifies child Flock transcripts in deferred
   form and folds their matrix assertions into the recursion accumulator that
   is discharged at the root.

The first proves what the Ix aggregate means. The second makes a tree of Flock
proofs succinct. Conflating them is a soundness and maintainability risk.

### Proposed proof graph

```text
raw P3 proof(s)
    |
    | complete P3 verification + CheckEnv digest binding
    v
profile-specific Flock leaf proof
    |
    | verify allowed leaf relation and normalize envelope
    v
fixed outer proof
    |
    +-------------------+
    |                   |
    v                   v
fixed outer proof   fixed outer proof
    \                   /
     \ fixed node: child verification
      \ + protocol fold + Ix fold
       v
    fixed outer proof
            |
            | repeat
            v
       fixed root/finalizer
            |
            v
 FlockStage2RootArtifactV1
```

The exact Flock implementation may fuse a leaf and its normalization or fuse
the final internal node and root discharge. The externally reviewed boundaries
remain the same:

- leaf relations may come from a bounded, pinned catalog;
- after normalization, every child has one fixed outer geometry;
- all internal nodes use one fixed relation;
- every nonempty aggregate ends in one fixed root relation.

### Leaf batching

Start with one raw P3 proof per leaf because it is the cleanest correctness and
shape experiment. Then benchmark fixed leaf batch sizes 2 and 4.

A larger leaf batch amortizes relation setup, proof overhead, and recursive
node count, but it also:

- duplicates the P3 verifier relation inside one Flock proof;
- increases peak witness memory;
- creates more combinations of P3 proof profiles;
- makes a failed leaf retry more expensive; and
- can interfere with manifest-preserving structural order.

Select the batch size from complete four-shard and production-corpus
measurements. Do not choose it from isolated BLAKE3 throughput.

### Singleton and odd-sized trees

The protocol must have an explicit unary normalization/finalization path.
Never pair a proof with itself and never introduce an “empty valid proof”
unless the application formally defines an identity statement and proves that
it is neutral.

For an odd frontier, carry one already-normalized child to the next scheduling
round or pass it through the fixed unary path. The choice must be deterministic
and included in the plan/cache version. A final root relation normalizes both
singleton and multi-node cases to the same terminal proof type.

## Fixed relation and proof-shape strategy

### The problem

Stage 1 uses one large IxVM system, but individual shard proofs have
input-dependent activation sets and trace heights. The current Flock lowering
specializes to an observed active mask, layout, and capacity. Compiling a fresh
relation for each proof and accepting its self-reported digest would make the
statement vacuous: the prover could choose a weaker relation.

Stage 2 therefore needs a relation policy fixed before seeing an adversarial
proof.

### Profile key

Define a canonical `P3ProofProfileV1` from structural data only:

- P3 verifying-key and parameter digests;
- total circuit count and ordered circuit identities;
- active circuit bitset;
- active trace heights and matrix widths;
- claim layout identifier;
- query count, FRI round geometry, cap geometry, and PoW policy;
- all fixed proof-array lengths; and
- typed witness-layout version.

Witness values, transcript challenges, roots, openings, and proof bytes are
not part of a profile. Two proofs with the same structural geometry must select
the same relation digest.

### Strategies to measure

Implement and compare three strategies on the corpus:

| Strategy | Advantage | Principal cost |
| --- | --- | --- |
| exact-profile catalog | no global padding; simplest lowering | catalog size and heterogeneous leaf recursion |
| one maximum-capacity relation | one leaf relation identity | pays for all inactive circuits and maximum heights |
| bounded bucket catalog | controls padding and catalog size | bucket design and selector constraints |

The preferred target is a bounded bucket catalog followed by a fixed
normalization relation. It avoids global worst-case padding while keeping the
terminal root independent of the leaf profile.

The profile study must report:

- number and frequency of exact profiles in Init and Mathlib;
- maximum and percentile active-circuit counts and trace heights;
- relation rows by each of the eleven verifier tables;
- relation build time and resident memory;
- online trace/evaluation, witness, prove, serialize, and verify costs;
- proof bytes;
- padding ratio for each proposed bucket; and
- the normalization/root cost caused by catalog size.

### Catalog rules

`Stage2RelationCatalogV1` is canonical, sorted, content-addressed deployment
data. It includes every accepted leaf bucket and the fixed normalization,
node, and root relation manifests.

Each entry identifies the relation, circuit/registry, canonical verifier
material, public layout, capacity, and proof profile. Large verifier material
may live in a content-addressed deployment store, but its digest and exact
codec are catalog data.

The catalog must be bounded independently of the input proof. A proof whose
profile is absent or exceeds a bucket fails during preflight with “protocol
upgrade required.” It must not trigger compilation of a new accepted
relation.

Every relation manifest binds:

- the compiled circuit digest;
- the typed witness-layout digest;
- its exact or bucketed bounds;
- its completed semantic/phase mask, including all eleven P3 phases for leaf
  relations;
- the P3 system and claim-layout identities where applicable;
- the Flock revision and proof-system configuration;
- transcript and Merkle hash identifiers; and
- all shape selectors and inactive-padding rules.

Unused bucket rows must be constrained to their canonical inactive values.
An advice-provided profile or shape selector is a hint only; the relation
checks every bit and every selected bound.

## Cryptographic interfaces

The names and domains below are proposed V1 interfaces. Phase 0 freezes exact
bytes and publishes vectors before production code depends on them.

The new backend needs a distinct `FlockStage2ConfigV1`; it must not reuse the
current standalone `FlockConfigV1` digest. The Stage 2 configuration covers
both leaf and outer profiles, tower/envelope geometry, maximum depth, PCS/code
parameters, grinding, commitment hash, Fiat-Shamir mode, field encoding, Flock
revision, and proof codec.

### Stage 2 protocol manifest

`FlockStage2ProtocolManifestV1` binds:

- the IxVM verifying-key digest and `verify_claim` function index;
- the canonical Stage 1 P3 parameters;
- the relation-catalog format and selector semantics, but not the compiled
  relation digests;
- the `CheckEnv` codec and flat/structural fold versions;
- the Flock git revision;
- leaf and outer proof profiles, including `Fast128`/`Slim128` choices;
- field, commitment hash, Fiat-Shamir, grinding, and serialization IDs;
- maximum leaves, tree depth, tree entries, Merkle path depth, and proof bytes;
- the complete lowering phase mask; and
- the composed security target.

Its canonical digest is the semantic protocol identity carried by every leaf
and node. A separate `Stage2RelationCatalogV1` digest identifies the compiled
relations. A parent requires exact equality of both child digests.

This split is deliberate. The catalog contains the root relation manifest, so
putting the catalog digest into a protocol manifest hard-coded by that root
would create a hash cycle. Relations instead treat the protocol and catalog
digests as constrained public values. The externally expected root statement
pins both, while the fixed relations enforce catalog selection and transitive
equality.

### Uniform application claim

Every Flock leaf and outer proof publishes:

```text
FlockAggregateClaimV1 {
    protocol_digest:         [u8; 32],
    relation_catalog_digest: [u8; 32],
    output_claim_digest:     [u8; 32],
}
```

The proposed canonical byte form is:

```text
"IXF2CL01" || protocol_digest || relation_catalog_digest
             || output_claim_digest
```

The encoding is 104 bytes. Inside Flock, each digest is represented without
reduction as exactly two little-endian F128 words. Cross-language vectors pin
byte, bit, limb, and word order.

The output digest is BLAKE3 of the canonical serialized `CheckEnv`. Any
relation that needs the preimage receives it as private witness, hashes it in
relation, checks the published digest, decodes it strictly, and then applies
the fold. The host may pre-parse the same bytes for fail-fast diagnostics, but
that result is not trusted.

### Canonical Stage 2 root statement

The proposed terminal handoff is 168 bytes:

```text
FlockStage2RootStatementV1 {
    domain:                  "IXFLK201",
    protocol_digest:         [u8; 32],
    relation_catalog_digest: [u8; 32],
    root_relation_digest:    [u8; 32],
    flock_config_digest:     [u8; 32],
    output_claim_digest:     [u8; 32],
}
```

The terminal SNARK exposes the BLAKE3 digest of these exact bytes as two
128-bit public limbs, as in the terminal plan. The settlement layer must derive
or compare the expected output claim; accepting a caller-chosen root statement
and applying an unrelated state transition proves the wrong fact.

The root relation’s public input is the uniform application claim. The native
Flock verifier additionally receives the externally selected root relation
and configuration. `FlockStage2RootStatementV1` binds both views together.

If network or contract replay protection belongs at this layer, add its fixed
domain bytes before V1 is frozen. Do not retrofit it under the same domain.

### Root artifact

`FlockStage2RootArtifactV1` contains only:

- strict magic and version;
- exact statement length and proof length;
- the canonical root statement; and
- the canonical Flock root proof.

The final artifact does not embed the raw P3 proofs, `CheckEnv` preimages, or
relation source used to build it. Those are proving inputs or optional
provenance sidecars, not verifier authority.

Parsing checks framing, bounds, encodings, and trailing bytes. Cryptographic
verification additionally requires an externally expected root statement and
the installed relation catalog/root verifier.

Flock proof serialization needs an explicit field-level codec suitable for
the terminal circuit. A pinned Rust `bincode` object graph is not by itself a
cross-language protocol specification.

### Internal node artifacts

The cache may store a versioned internal artifact containing:

- its uniform application claim;
- relation/profile ID;
- proof bytes;
- fold mode and scheduler level;
- child content digests; and
- non-authoritative timing/RSS metadata.

A cache hit is accepted only after content-address verification, strict decode,
exact expected-claim comparison, relation/catalog membership checks, and
native cryptographic verification.

## Relations

### Leaf relation

`FlockStage2LeafV1(profile)` must:

1. open the canonical semantic protocol manifest, hash it to the public
   protocol digest, and check every leaf-relevant field against this relation;
2. accept one or a fixed bounded batch of canonical P3 proof transports;
3. bind the exact IxVM verifying key, P3 parameters, and entrypoint;
4. reconstruct the typed proof witness from the compact transport;
5. constrain all eleven verifier phases already implemented by the current
   Stage 3 lowering;
6. require the exact ten-word Stage 1 claim layout;
7. open, hash, and strictly decode each `CheckEnv` preimage;
8. for a batch, perform the selected deterministic flat or structural folds;
9. publish the common protocol digest, relation-catalog digest, and resulting
   output-claim digest; and
10. constrain every unused batch/profile slot to canonical inactive values.

Native P3 verification happens before proving as a DoS and diagnostics guard.
The Flock relation independently proves the same verification and does not
consume a host-computed acceptance bit.

### Normalization relation

`FlockStage2NormalizeV1` verifies one allowed leaf relation from the pinned
catalog and republishes the identical application claim in the fixed recursive
outer geometry.

This is the heterogeneity boundary. Above it, no internal node depends on a P3
activation profile or leaf bucket. If the Flock tower can fuse normalization
into the first recursive node without changing this invariant, do so after
measurement.

Catalog selection is constrained. The relation must hash the canonical catalog
or verify an authenticated catalog entry against the public catalog digest.
It must then either contain the fixed allowed verifier material or
cryptographically bind every supplied matrix/circuit object to the
authenticated entry. A relation-digest membership check alone is not enough if
the verifier then trusts prover-supplied matrices.

### Node relation

`FlockStage2NodeV1` takes two fixed-outer children and:

1. verifies both child Flock proofs using the recursion-safe deferred verifier;
2. checks both public application claims use the expected protocol and
   relation-catalog digests;
3. folds all child proof-system matrix assertions into the protocol recursion
   accumulator;
4. opens and hashes both child `CheckEnv` values;
5. applies exactly one constrained flat or structural Ix fold;
6. hashes the canonical output `CheckEnv`; and
7. publishes the same fixed outer statement shape and recursion state.

The fold-mode selector is advice, not trust. Both branches have exact shape,
preimage, tree, and path checks. If separate flat and structural circuits are
materially smaller, they may exist below a final fixed normalizer; the root
relation still remains singular.

### Root relation

`FlockStage2RootV1`:

- accepts exactly one normalized leaf or node result through an explicit
  constrained kind;
- verifies/finalizes the last child;
- checks the protocol and relation-catalog digests against the expected public
  application claim;
- discharges every carried protocol accumulator against the fixed allowed
  matrices committed by the catalog;
- rejects dead, duplicate, orphaned, or wrong-digest accumulator slots;
- republishes the exact application claim;
- is accepted only under the fixed root relation and Stage 2 configuration
  named by the externally expected root statement; and
- has one circuit digest and proof geometry for every supported nonempty
  aggregate.

The terminal circuit verifies only this relation.

## Flock recursion feasibility contract

The generic recursion work is accepted only if the Flock layer exposes a
reviewable API with these properties:

- an application can supply a Flock `BuiltCircuit`, public input, proof, and
  canonical verifier metadata without reaching into private tower fields;
- the first-level builder can verify allowed heterogeneous leaf circuit
  digests or a measured bucket-normalized equivalent;
- the internal builder consumes two outer proofs and returns the same
  externally fixed outer shape;
- application public words can be copied, compared, and transformed by
  application gates rather than hard-coded hash-chain adjacency logic;
- child verification records every transcript operation needed by the circuit;
- Boolean, element, wiring-sigma, and jagged-layout assertions are all folded
  and eventually discharged;
- the root proof has a stable canonical verifier and serialization;
- non-power-of-two and singleton inputs have explicit sound paths; and
- the API reports setup, walk/tape, witness, prove, verify, RSS, and proof-size
  metrics in non-test builds.

The initial profile should evaluate `Chain128`: `Fast128` for workload
leaves and `Slim128` for recursion outers, with BLAKE3 Merkle commitments and
chained-BLAKE3 Fiat-Shamir. Its current m*=29 / nu*=14 envelope is a prototype
constant, not an Ix protocol choice until the generic relation fits and the
soundness/capacity review passes.

Prefer an upstreamable generic tower interface over an Ix-only copy of the
specialized chain tower. Pin any Flock revision change as a new Stage 2 config
and rerun every vector and benchmark.

## Monolithic fallback

If the generic tower cannot support the Ix relation, build one
`FlockStage2BatchV1` experiment:

- fixed `N_max` raw P3 proof slots;
- a constrained active count and canonical inactive suffix;
- fixed profile buckets per slot;
- deterministic manifest fold instructions;
- bounded `CheckEnv`, tree, and Merkle-path witnesses;
- one output application claim; and
- one fixed Flock root relation.

Measure `N_max` at 4, 16, 64, and the intended production maximum where
resources allow. This route loses fine-grained resume and redoes the whole
batch on failure, but it avoids Flock-in-Flock recursion.

Do not combine an unbounded number of dynamically compiled leaf relations in
one accepted batch. If no fixed-capacity batch covers the production corpus,
the monolithic route fails its gate.

## Host pipeline

### Planning

Extend the existing validated/pruned `.ixes` plan rather than inventing a
second manifest interpretation:

1. validate raw manifest coverage;
2. prune empty leaves and contract unary manifest nodes;
3. reconstruct every raw shard’s exact `CheckEnv`;
4. validate and profile every raw P3 proof;
5. map each proof to an allowed Flock leaf bucket;
6. choose deterministic leaf batches without changing structural orientation;
7. derive every intermediate output claim before proving;
8. schedule leaf, normalize, node, and root slots by dependency; and
9. verify the final root against the independently reconstructed expected
   `CheckEnv`.

The planner must finish all statements, relation IDs, and cache keys before the
first proof begins. A proving result cannot influence the shape of a later
statement.

### Scheduling and memory

Reuse the jobs-plus-bytes admission model from `ix aggregate`:

- maintain a measured peak-RSS weight per leaf bucket and node kind;
- admit ready work heaviest-first with deterministic tie-breaking;
- allow one oversize job alone but report it clearly;
- release child buffers as soon as the parent has copied the canonical inputs
  it needs;
- separate process-wide relation setup/cache memory from per-proof online
  memory; and
- drain running independent jobs safely after the first error without
  admitting dependents.

Flock’s internal Rayon pool and the outer aggregate scheduler must not
oversubscribe the same machine. Define one ownership policy for physical cores
and record it in every benchmark.

### Relation setup cache

The optimized tiny fixture spends most of `prove_stage2` outside the 140 ms
Flock prover. Treat relation construction as immutable setup:

- cache built shapes, sparse matrices, CSC lincheck circuits, union instances,
  fill plans, and PCS parameters by complete relation-manifest digest;
- use process-wide shared immutable entries;
- measure cold build, warm memory hit, and optional verified disk load
  separately;
- validate every disk artifact against its canonical digest before use; and
- never include setup time in “online prove” while hiding it from end-to-end
  CLI wall time. Report both.

### CLI

Add explicit development commands:

```text
ix aggregate --backend flock ...
ix verify --aggregate --backend flock ...
ix flock-root --mode preflight|prove|verify ...
```

The exact spelling may follow the existing CLI parser, but these behaviors are
required:

- `p3` remains the default until cutover;
- production profiles are compiled/pinned, not arbitrary security flags;
- preflight performs strict decode, native verification, profile mapping,
  relation-capacity checks, statement derivation, and cost census without
  proving;
- prove writes a temporary artifact, verifies it against the expected
  statement, and atomically installs it;
- verify accepts an expected statement or reconstructs one from
  `.ixe`/`.ixes`; and
- artifact magic may drive parsing, but deployment policy decides which
  backend is accepted, preventing downgrade-by-format.

### Cache key

Each work item key includes, in canonical order:

```text
cache_version
stage2_protocol_manifest_digest
stage2_relation_catalog_digest
relation_manifest_digest
flock_config_digest
fold_mode
expected_output_claim_digest
ordered_child_artifact_digests
ordered_child_statement_digests
```

Leaf keys additionally include the canonical raw P3 proof content digest and
profile ID. Root keys include the expected root statement. Any semantic codec,
capacity, transcript, catalog, or upstream-revision change invalidates the
affected namespace.

## Repository structure

Avoid copying the current verifier lowering.

During the spike:

```text
flock-stage3/
  host/
    current Stage 3 compatibility API
  p3-verifier/
    generic validated P3 transport, typed witness, and 11-phase lowering
  stage2/
    leaf/fold/recursion relations, artifacts, planner, and benchmarks
```

The exact crate split may differ, but the current Stage 3 API should become a
thin adapter over the shared P3-verifier crate. Existing Stage 3 vectors and
artifact bytes must remain unchanged through that refactor.

Only after Stage 2 adoption should the isolated workspace be renamed to a
stage-neutral `flock/` workspace and Nix targets updated atomically. Keep the
Flock workspace isolated from the root Cargo workspace while its pinned
dependency graph requires that separation.

Suggested ownership:

- `crates/terminal`: old P3-root statement plus the new canonical Flock
  Stage 2 root statement; no proving implementation;
- shared P3-verifier crate: codecs, validated transport, typed witness,
  relation census, and complete verifier lowering;
- Stage 2 crate: protocol/catalog manifests, `CheckEnv` folding, Flock
  relations, artifacts, cache, and host backend;
- Lean `Ix/Flock` modules: executable statement/fold specifications and
  eventually verifier refinements;
- CLI bridge: manifest planning, scheduler, store, and user-facing commands;
  and
- test vectors: separate directories for P3 lowering, Stage 2 statements,
  leaf relations, recursion nodes, and roots.

## Implementation phases

### Phase 0: freeze semantics, corpus, and matched baselines

Deliver:

- exact V1 draft encodings and domain-separation table;
- an executable Rust and Lean specification of the uniform application claim,
  protocol-manifest digest, relation-catalog digest, and root statement;
- current q=100 Stage 1 proofs for the four-shard Init fixture;
- representative Init and Mathlib profile corpora, including the largest
  expected shard and at least two distinct activation/height shapes;
- rerun P3 lift/join baselines on the same hardware and current revision;
- a complete timing/RSS/proof-size breakdown for the optimized q=2 Flock
  fixture; and
- a benchmark manifest recording CPU, RAM, kernel, compiler flags, physical
  thread policy, revision, q/PoW, and warm/cold status.

Gate:

- all input artifacts verify natively;
- Rust and Lean produce identical V1 bytes and digests;
- every parameter affecting acceptance is in a canonical manifest; and
- no production conclusion is drawn from the q=2 fixture.

### Phase 1: make the P3 verifier lowering stage-neutral

Refactor the current Stage 3 implementation into:

- `ValidatedP3ProofV1` instead of a type fixed to an aggregate root;
- an explicit claim-layout descriptor for ten-word IxVM and eighteen-word
  recursive claims;
- a generic `P3VerifierRelationManifestV1`;
- the existing eleven verifier phases without semantic changes; and
- compatibility adapters for `Stage3StatementV1`,
  `Stage3RelationManifestV1`, and `Stage3ArtifactV1`.

Add one raw Stage 1 shard fixture and prove its exact ten-word statement with
Flock.

Gate:

- every existing current Stage 3 test passes;
- the deterministic fixture retains identical transcript and artifact bytes;
- the raw Stage 1 proof is accepted;
- one-bit proof, wrong VK, wrong entrypoint, wrong claim, wrong relation, and
  corrupted Flock proof mutations are rejected; and
- the report separates decode, native prevalidation, relation build,
  relation evaluation, per-table witness generation, union assembly, Flock
  prove, buffer return, serialization, and verification.

### Phase 2: production profile and capacity study

Build the profile-census tool and prototype exact, maximum, and bucketed leaf
relations.

Required fixtures:

- the q=2 protocol regression;
- the smallest current q=100 raw proof;
- a normal 20-25 MB Init shard;
- at least two proofs with different activation/height profiles;
- the largest observed Init proof;
- the largest observed Mathlib proof; and
- malformed inputs just above every proposed capacity.

Gate:

- one bounded strategy covers 100 percent of the frozen corpus;
- its catalog size and padding cost are reported;
- repeated proofs of one profile compile to the same relation digest;
- over-capacity inputs fail before relation evaluation/proving;
- no accepted relation is derived from prover-controlled dynamic dimensions;
  and
- the strategy meets the single-leaf minimum performance gate below.

If no strategy passes, stop the recursive work and retain the current
P3-aggregate architecture.

### Phase 3: Ix claim folding in Flock

Implement:

- canonical `CheckEnv` byte decoding;
- packed BLAKE3 claim binding;
- canonical assumption-tree loading and root reconstruction;
- strict bytewise address ordering and deduplication;
- pass-through/singleton;
- flat union/difference;
- structural subject-root construction;
- bounded Merkle inclusion paths; and
- carry-or-discharge accounting for every unique input assumption.

Use `Ix.Aggr.Host` and `Ix.Aggr.Circuit` as the semantic oracle. Generate
shared vectors instead of maintaining handwritten examples in each language.

Gate:

- Rust native, Lean host, current P3 circuit execution, and Flock relation
  agree on every valid vector;
- all adversarial fold mutations fail;
- one- and two-shard Flock leaf artifacts verify against independently derived
  output claims; and
- relation costs for pass-through, flat, and structural modes are reported
  separately.

### Phase 4: generic Flock recursion spike

Work in the pinned Flock tree or an explicit reviewed fork:

1. turn one arbitrary Ix leaf proof into a recursion-safe outer proof;
2. normalize two distinct allowed leaf profiles;
3. verify and merge two normalized children;
4. carry the uniform Ix application claim through public wires;
5. execute one real flat fold and one real structural fold in a node;
6. build a depth-two tree;
7. close/discharge it into a fixed root proof; and
8. corrupt each child proof, public claim, relation ID, accumulator group, and
   transcript tape in turn.

Gate:

- the final root relation digest and proof geometry are identical across the
  two leaf profiles and depths one and two;
- every child proof is cryptographically verified in relation;
- every protocol accumulator group is either carried and matched or discharged
  exactly once;
- root native verification needs no child proof or prover-supplied relation
  source;
- the composed soundness calculation covers the chosen maximum depth; and
- four-shard time/RSS projections can plausibly meet the adoption gate.

If this fails, execute the monolithic fallback experiment before deciding
whether to stop.

### Phase 5: complete Stage 2 proof graph

Implement:

- deterministic one-, two-, and four-proof leaf batching;
- fixed normalization;
- fixed binary nodes;
- odd-frontier carry/unary behavior;
- singleton finalization;
- final accumulator discharge;
- canonical root statement and artifact codecs; and
- strict native root verification against an expected statement.

Gate:

- 1, 2, 3, 4, and 5 nonempty shards all produce the same root relation type;
- balanced and permitted unbalanced schedules yield the independently expected
  `CheckEnv`;
- all root artifacts parse canonically and reject trailing bytes;
- final verification depends only on the expected statement, fixed deployment
  material, and root artifact; and
- no internal proving witness is embedded in the canonical root artifact.

### Phase 6: CLI, cache, resume, and scheduler integration

Deliver:

- `--backend flock` planning/proving/verification;
- preflight output with profile and relation mapping;
- verified leaf/node/root cache entries;
- RAM- and core-aware parallel scheduling;
- atomic artifact installation;
- a machine-readable benchmark ledger; and
- fault injection at every cache and process boundary.

Gate:

- cold, warm, interrupted, and resumed runs produce the same expected
  application statement;
- every cache corruption becomes a miss or hard verification error, never a
  trusted hit or panic;
- jobs=1 and jobs>1 outputs all verify and have identical canonical statements;
- scheduler admission stays within its configured memory envelope; and
- P3 remains the default backend.

Exact proof-byte equality across positive-PoW concurrent runs is not required
unless the selected Flock grinding procedure is deterministic. Canonical
statements and cryptographic validity are required.

### Phase 7: production-scale benchmark and security gate

Run, one benchmark at a time:

- the matched four-shard Init fixture;
- a complete Init aggregate at intended partitioning;
- a representative Mathlib subtree;
- the largest planned Mathlib aggregate or a justified capacity-equivalent
  workload;
- singleton, odd, flat, structural, carried-assumption, and full-discharge
  roots; and
- cold start, warm setup cache, resume, and maximum admitted concurrency.

Record:

- end-to-end wall and CPU time;
- cold setup and warm online time;
- walk/tape, P3 lowering, claim-fold, witness, union, prove, serialize, verify,
  and buffer-release time;
- current, peak resident, and virtual memory;
- bytes for leaf, normalized, node, root, and sidecar artifacts;
- internal and application BLAKE3 compression counts;
- Flock field/PIOP/PCS operation counts;
- tree depth, proof count, and cache hit ratio; and
- terminal-verifier trace/constraint estimates.

Gate:

- all correctness, mutation, and resource-bound tests pass;
- the fixed catalog covers the production corpus with documented headroom;
- the composed concrete-soundness analysis reaches the selected system target;
- independent review signs off on Flock recursion and parameter use;
- the matched performance gate below passes; and
- no benchmark depends on swap or exceeds fleet operational limits.

### Phase 8: rebase the terminal plan

Replace the terminal relation:

```text
verify Flock proof of one P3 Stage 2 root
```

with:

```text
verify one FlockStage2RootV1 proof
```

Reuse the canonical Flock proof decoder, chained-BLAKE3 transcript replay, and
F128 arithmetic work. Regenerate the fixed terminal circuit, constraint
manifest, circuit digest, proving keys, vectors, and gas/size reports.

Gate:

- native Flock verification, terminal constraint evaluation, and Lean
  executable specification agree;
- valid root passes and every proof/statement/config/relation mutation fails;
- the terminal circuit is fixed independently of shard count and leaf profile;
- the settlement layer binds the expected output claim; and
- the selected FFLONK/Groth16 backend meets its capacity and deployment gates.

### Phase 9: cutover and retirement

Cut over only after a versioned release has run both backends on the same
production statements for a burn-in period.

Required actions:

- publish protocol/catalog/config/root-relation digests and vectors;
- freeze the accepted maximum capacities and upgrade process;
- select one active backend in deployment policy;
- retain read-only verification and decoding of historical P3 aggregate and
  old Stage 3 artifacts;
- stop producing new P3 aggregates only after rollback has been rehearsed;
- update stage numbering in user documentation; and
- archive benchmark and security-review artifacts.

Do not delete `ix_aggr` immediately. Keep it as a tested fallback for at
least one release after Flock activation, but do not let a contract or
consensus rule accept either backend indefinitely.

## Performance gates

All comparisons use the same input proofs, q/PoW, hardware, compiler mode,
thread allocation, verification policy, and warm/cold definition.

The binding adoption gate is end-to-end. Per-operation numbers are diagnostics.

| Metric | Current P3 baseline | Minimum Flock adoption gate | Target |
| --- | ---: | ---: | ---: |
| matched raw-shard leaf/lift | about 101 s | at most 50 s | at most 10 s |
| four-shard serialized root | 623 s | at most 311 s | at most 120 s |
| peak RSS per admitted work unit | 195.8 GiB max | at most 128 GiB | at most 96 GiB |
| final off-chain root artifact | 9,455,498 B | no larger, and terminal fits | at most 1 MiB |
| valid root verification | record on matched box | no slower than P3 root verify | terminal-driven |

Additional requirements:

- report cold setup separately, but include it in a fresh CLI invocation;
- report warm setup-cache performance for daemon/batch operation;
- no individual production work unit may require more than 80 percent of a
  256 GiB worker after allocator and OS headroom;
- the scheduler must demonstrate at least the intended fleet concurrency
  without swap;
- corrupted verification cannot be materially more expensive than valid
  verification without an explicit DoS bound; and
- proof-size wins do not compensate for a terminal circuit that misses its
  fixed-capacity gate.

The minimum gate deliberately requires a clear operational improvement. A
10-20 percent win does not justify replacing a mature recursive protocol with
a newer recursion stack.

## Test matrix

### Encoding and identity

- exact round trips in Rust and Lean;
- wrong magic, version, domain, endianness, length, and trailing bytes;
- noncanonical Goldilocks and binary-field elements;
- wrong IxVM VK, function index, P3 params, Flock revision, profile, hash,
  transcript, catalog, relation, or config digest;
- cross-version and old-artifact confusion; and
- expected-statement mismatch even when the artifact’s self-contained
  statement is internally well formed.

### P3 verifier lowering

- inactive/active circuit swap;
- wrong trace height, matrix width, or activation bit;
- lookup/logUp imbalance;
- transcript reorder, omitted absorb, challenge mutation, or rejection-sample
  error;
- Goldilocks and extension arithmetic mutations;
- AIR/OOD/quotient mutation;
- PCS batch/opening mutation;
- Merkle root, leaf, query index, sibling, and path-length mutation;
- FRI cap, beta, grinding witness, fold, roll-in, or final polynomial mutation;
- missing/extra query and duplicate-query ambiguity; and
- compact transport truncation/extension.

### Claim folding

- pass-through claim mismatch;
- missing, extra, duplicated, or unsorted subject/assumption entries;
- left/right ordering changes;
- wrong flat difference result;
- wrong structural root;
- missing, extra, reversed-side, overlong, or corrupted Merkle path;
- discharging a nonmember;
- carrying a discharged candidate or dropping a carried candidate;
- flat/structural selector confusion; and
- singleton padding or self-pair attempts.

### Flock recursion

- leaf relation not in catalog;
- leaf/node kind swap;
- wrong child public claim;
- swapped, skipped, duplicated, or replayed child;
- wrong normalization relation;
- wrong recursion level or envelope geometry;
- mismatched registry, sigma key, jagged-layout key, or matrix claim;
- live claim placed in a dead slot;
- orphan accumulator, double discharge, or missing discharge;
- transcript tape edit;
- proof from another Flock config/revision; and
- valid tree whose root is checked against a different expected statement.

### Host and operations

- profile-census determinism;
- capacity boundary and one-above-bound rejection;
- plan derivation before proving;
- 0-, 1-, 2-, odd-, and non-power-of-two retained leaves;
- empty-leaf pruning after raw coverage validation;
- flat/structural threshold determinism;
- cold/warm cache, corrupt index, corrupt content, wrong claim, wrong relation,
  and interrupted atomic write;
- jobs and memory admission, oversize-alone behavior, failure draining, and
  core oversubscription;
- bounded parser allocation for malicious lengths; and
- valid/corrupted verify timing under resource limits.

### Terminal composition

- native versus circuit Flock verification;
- statement digest limb/bit ordering;
- wrong root relation/config/protocol/catalog/output digest;
- malformed proof points/fields and subgroup checks where applicable;
- terminal proof mutation;
- contract derives or compares the exact expected state claim; and
- old/new backend downgrade tests.

## Soundness argument to document

The implementation review must provide an explicit composition:

```text
Stage 1 P3 proof soundness
  + Flock leaf proof soundness
  + every Flock recursive child-verification/fold step
  + root accumulator discharge
  + terminal SNARK soundness
  = deployed statement soundness
```

The concrete calculation includes:

- the maximum number of Stage 1 proofs per root;
- the maximum number and depth of Flock proofs;
- all P3 FRI/query/grinding losses;
- Flock Boolean and element zerocheck/lincheck losses;
- PCS, matrix-fold, recursion, and transcript losses;
- catalog/profile selector and hash-binding assumptions;
- BLAKE3 collision/preimage assumptions in each separated role; and
- terminal backend and setup assumptions.

`Fast128`, `Slim128`, and `Chain128` are names, not a proof of 128-bit
composed security. The calculation must be independently checked at the exact
pinned revision and maximum tree size.

The trust boundary must state:

- native prevalidation is not trusted for acceptance;
- relation compilation is trusted only through externally pinned digests and
  reproducible builds;
- host planning is checked by constrained claims plus expected-root
  reconstruction;
- cache/store contents are untrusted;
- Flock is not zero knowledge;
- the terminal proving key/setup has its backend-specific trust assumptions;
  and
- formal verification does not remove cryptographic assumptions.

## Principal risks and pivots

| Risk | Detection | Response |
| --- | --- | --- |
| q=100 raw proof exceeds fixed Flock capacity | Phase 2 production fixture | redesign buckets or stop; do not silently compile a new relation |
| activation profiles make the catalog unbounded | corpus census and future-shape simulation | use bounded bucket/max relation or retain P3 Stage 2 |
| generic Flock tower remains chain-specific | Phase 4 arbitrary-leaf spike | upstream a generic API; otherwise benchmark monolithic batch |
| heterogeneous leaf relations prevent a fixed normalizer | two-profile recursion test | reduce buckets, pad to one leaf relation, or stop |
| outer `Slim128` recursion dominates time/RAM | per-level tower ledger | increase leaf batch size, optimize generic tower, or use monolithic batch |
| matrix-claim accumulator does not close for the Ix relation | depth-two discharge test | isolate offending group; no unchecked host discharge |
| claim folding erases the BLAKE3 advantage | per-table fold census | prefer structural folding, specialize canonical codecs, or retain P3 fold |
| relation setup dominates one-shot CLI runs | cold/warm breakdown | verified persistent setup cache and daemon mode; still count cold wall |
| composed security falls below target at Mathlib depth | independent calculation | retune profiles/grinding or lower max depth through larger leaves |
| final Flock proof makes terminal circuit too large | Phase 8 constraint report | specialize root codec/verifier or retain old Stage 3 path |
| upstream Flock changes | digest/vector mismatch | keep pinned revision; upgrade only under a new protocol/config |
| new backend creates downgrade ambiguity | deployment mutation tests | one active backend/version at a time |
| Stage 2 is faster but operationally fragile | burn-in/cache/fault tests | keep P3 default until recovery and rollback are proven |

## Decision gates

Make five explicit decisions from artifacts, not projections:

1. **Leaf viability:** does one real q=100 Stage 1 proof verify in a bounded,
   externally pinned Flock relation with a material time/RAM win?
2. **Shape policy:** does a maximum or bucketed catalog cover the corpus with
   acceptable padding and a fixed normalization boundary?
3. **Aggregation design:** does generic Flock recursion close and win, or does
   a monolithic fixed batch win? If neither, stop.
4. **Terminal viability:** can one fixed root verifier be arithmetized within
   the selected terminal backend’s capacity, size, and gas budget?
5. **Cutover:** do matched production benchmarks, composed security review,
   operational burn-in, and rollback all pass?

Failure at a gate preserves the current P3 Stage 2 plus Flock Stage 3 design;
it does not force a partial migration.

## Definition of done

Flock Stage 2 is complete only when:

- a real full-size Stage 1 corpus aggregates from raw P3 shards to one Flock
  root;
- every supported manifest size ends in the same fixed root relation;
- flat, structural, singleton, odd, carry, and discharge semantics match the
  current aggregate implementation;
- the accepted relation catalog and every protocol parameter are versioned and
  externally pinned;
- the mutation corpus fails at the intended layer;
- production q=100 time, RSS, proof size, and terminal costs pass the gates;
- cache/resume and resource scheduling survive fault injection;
- the terminal SNARK verifies the new root statement end to end; and
- a versioned migration activates Flock without losing historical verification
  or a rehearsed rollback path.

## First implementation slice

The first PR should stop before recursion and do only this:

1. extract the current complete P3 verifier lowering behind stage-neutral
   types while preserving old Stage 3 vectors byte-for-byte;
2. add exact ten-word Stage 1 claim support;
3. ingest one current q=100 raw shard proof;
4. produce and verify one Flock leaf proof with full timing/RSS/table census;
5. corrupt the P3 proof, claim, VK, relation digest, and Flock proof;
6. census at least one second activation/height profile; and
7. publish the exact-profile versus padded-relation comparison.

That PR answers the first real question—whether Flock beats a P3 lift on the
actual proof shape—without prematurely committing to a recursion architecture.

## Review map

Use these files as the source of truth while implementing the plan:

- `plans/aggregate-first-pipeline-pr.md`: landed P3 aggregate semantics,
  measured q=100 baseline, cache, scheduler, and test inventory;
- `Ix/Aggr.lean`: allowed-system identity, public-input packing, and shape
  codes;
- `Ix/Aggr/Circuit.lean`: in-circuit child verification plus flat and
  structural fold semantics;
- `Ix/Aggr/Host.lean`: native fold oracle and advice construction;
- `Ix/Cli/AggregateCmd.lean`: manifest planning, cache/resume, and RAM-gated
  execution;
- `flock-stage3/README.md`: current complete verifier status, pinned Flock
  revision, and known production gaps;
- `flock-stage3/host/src/typed_witness.rs` and
  `flock-stage3/host/src/relation.rs`: typed layout, capacity, phase mask, and
  relation identity;
- `flock-stage3/host/src/fri.rs`: composed eleven-phase relation, proof path,
  mutation fixture, and timing hooks;
- `flock-stage3/host/src/artifact.rs`: current strict statement/artifact
  precedent and the transport that must not be copied into the new root
  artifact;
- `crates/terminal/src/lib.rs`: existing `IXROOT01` boundary and canonical
  P3 transport validation; and
- `plans/flock-terminal-snark-plan.md`: terminal statement, fixed-verifier,
  backend, formalization, and deployment gates to rebase in Phase 8.

At pinned Flock revision
`b310f35f35f68095537150a1c8c0a43caca9a29e`, review
`flock-prover::tower`, `flock-core::aggregate`, the deferred verifier, and
the canonical proof codec together. The tower’s public builders are currently
chain-application-specific; do not infer a generic recursion contract from
their names alone.
