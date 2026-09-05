# Stage 4 verifier boundary — design, not a frozen encoding

Stage 4 should verify a Flock proof against a deployment-owned relation and
expose the same 104-byte `Stage3StatementV1`: domain, Stage 2 root digest,
relation-manifest digest, and Flock configuration digest. This document defines
the trust boundary to preserve while Stage 3 capacity sizing and corpus
measurements are still changing. It does not add a Stage 4 backend or import
the separate formalization work.

## Ownership

| Input | Authority / required check |
| --- | --- |
| Flock revision, profile, transcript domain, PCS security configuration | Deployment-owned protocol pin |
| Relation manifest, compiled circuit, table schemas, wiring, fixed publics | Deployment-owned specialization; never selected solely by the prover |
| Stage 2 key, FRI parameters, activation, trace heights, nested witness layout | Must match that specialization exactly |
| Stage 2 root / 18 claim words | Application-owned expected statement, bound by the relation |
| Flock proof, remaining verifier public words | Untrusted witness; checked by the fixed verifier |
| JSONL report, native validation result, process cache, timings and RSS | Diagnostics / host safeguards only; no acceptance authority |

The Flock verifier's public vector is currently larger than the 104-byte outer
statement: it contains verifier transport values as well as fixed constants
and constrained derived values. An exporter must preserve the compiled public
ordering, enforce all fixed-public checks, and connect the published Stage 2
root to the outer statement. It must not replace those checks with a native
"accepted" bit or assume the outer statement is Flock's entire public vector.

## Export requirements

The current bincode production payload is a versioned host transport, not a
canonical circuit-language witness ABI. A future exporter must specify and
test its own domain/version, exact lengths and order, F128 limb/byte order,
proof-bundle sections, transcript initialization, public-word mapping, and
reject trailing or noncanonical encodings. It must independently reproduce
the configuration and relation digests; a self-consistent prover-supplied
manifest is not a trust anchor.

The explicit `Stage3PreparedRootV1` is the host integration point: one admitted
root owns one compiled relation, report and expected statement. Export should
consume this validated context, with separate exported verifier inputs tested
against the pinned native Flock verifier in a fresh process. Native Stage 2
prevalidation remains a cost guard, not a substitute for verification inside
Stage 3 or Stage 4.

## Order before freezing

The checked count-based compiler, bounded arithmetic assertion groups,
shared PCS/weighted quotients, query-point/denominator reuse and packed
canonicality checks are implemented:
the 100-query toy fixture fits in 3 GiB padded z/a/b, compiles and evaluates in
about 1.8 s, and has passed a full proof with fresh-process verification. Its measured proving
peak was 5.1 GiB RSS (previously 6 GiB padded / 8.4 GiB RSS). Canonicality
packing retains the toy's 3 GiB capacity because additions now set its row
bound. Its current artifact is 478,483 bytes; proof size is not monotonic in
table capacity.
The PCS rewrite constrains nonzero denominators and preserves columnwise reduction exactly;
compiled-gate adversarial tests do not substitute for an independent review.
Circuit, table-schema and relation digests changed; adopting this compiler
requires regenerated artifacts and explicit deployment-pin updates, not
acceptance of prover-selected pins.

The first genuine persisted `ix_aggr` fixture now passes native verification,
but its Stage 3 count still requires **192 GiB padded z/a/b** (`nu=22`, 3.16
million packed canonicality rows), down from 3 TiB / 62.9 million rows on the identical
root. It fits the default table limit but not the default padded-witness limit;
admission rejects it before wiring compilation. Actual real-root peak RAM,
including compiler/PCS/prover scratch, remains unmeasured. The toy's successful
proof is therefore not evidence of practical aggregate proving. The
[baseline](measurements/persisted-singleton-2026-09-05.json),
[PCS measurement](measurements/persisted-singleton-pcs-2026-09-05.json) and
[query-sharing measurement](measurements/pcs-query-sharing-2026-09-05.json) and
[current canonicality-packing measurement](measurements/packed-canonicality-2026-09-05.json)
are retained.

The opt-in Stage 2 `min-opening-width-v1` experiment reduces the same
singleton's active committed column widths by 7.29%. Initially, Stage 3 rows
fell only 1.65% to 12,580,880, with padded z/a/b unchanged at 768 GiB. The
query-sharing compiler counted 6,072,018 rows and 384 GiB; packed canonicality
now counts 3,056,107 rows and **192 GiB** for this
root, which is also rejected before wiring compilation. The experiment changes the
aggregate key, outer claim and root while retaining the same IxVM child and
CheckEnv statement; it does not change the deployment default or authorize
acceptance of a profile selected by the prover. Native verification was slower
in the single measured run despite smaller proof bytes and sampled proving
RSS. See the [paired measurement](measurements/stage2-lookup-packing-2026-09-05.json).
Adoption would require explicit Stage 2 key and Stage 3 relation pin changes.

1. Measure real-root compilation/proving with explicit process bounds on a
   suitable high-memory host; 192 GiB is not a total peak-RAM estimate. Further
   arithmetic/layout optimizations must preserve every constraint and be
   accompanied by independent soundness review. Retain the singleton's native
   proof and count-only admission failures as regressions.
2. Collect current-protocol persisted roots with different activation/height
   patterns using JSONL; retain failures as well as successful measurements.
   Historical protocol-incompatible fixtures cannot stand in for this corpus.
3. Choose a fixed shape, a bounded family, or explicitly constrained padding.
   Capacity padding needs a new manifest version and in-relation constraints;
   host bounds alone cannot authorize reuse across activations or heights.
4. Extend the 100-query full-proof coverage to persisted ix_aggr roots, with
   artifact persistence and fresh-process verification. Interleave independent
   soundness review and adversarial table/wiring vectors with corpus work.
5. Freeze relation identities, canonical export bytes and golden vectors.
   Only then specialize the terminal SNARK and measure its costs.

The required negative vectors include changed claims, activation, heights,
key/configuration, Merkle paths, fold evaluations, grinding/query draws,
noncanonical field words, truncated/extended proof encodings, mismatched
external roots and poisoned recycled buffers. The existing tests cover a
useful subset; they are not an independent security audit.
