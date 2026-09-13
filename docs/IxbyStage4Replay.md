# Generic IxBy → Stage 4 replay

Status: native replay and new public/private statement binding are implemented.
This is progress toward M5, not completion of M5–M8. There is no approved
full terminal topology/key, closed-root circuit, or complete FFLONK proof yet.
The native Flock constraint-to-IxBy refinement obligation in M3 remains too.

## Entry and ownership

The isolated `flock-stage4/exec` crate depends on `ixby-flock`, Flock
`b310f35f35f68095537150a1c8c0a43caca9a29e`, and the imported neutral trace,
circuit, and FFLONK crates. It does not depend on a native Stage 2 verifier.
Root Cargo/Lean dependencies and the experimental m37 configuration are
unchanged. The donor file hashes and excluded legacy APIs were recorded in
`flock-stage4/EXEC-REPLAY-PROVENANCE.json` before import.

`compile_exec_replay(approvedExec)` constructs an immutable `CompiledExecReplay`
using only the approved generic setup. It takes no guest image, commitment,
statement, or proof. Its `replay(commitments, completeProofBytes)` method uses
the strict Exec decoder and complete native verifier; `replay_exec` remains
the compile-and-replay convenience entry point. Its read-only `VerifiedExecProof`
input projection is borrowed from that exact approved setup. There is no
legacy decoder, Stage 2 artifact reconstruction, program/input decoding,
host interpreter, or prover-selected public vector in this boundary.

The setup retains distinct protocol, implementation, semantic-profile,
physical-capacity, primitive-registry, concrete-registry, circuit,
public-template, and input-layout identities. The main transcript uses the
same domain plus complete setup digest as the native Exec verifier. The
auxiliary fold transcript has its own generic Exec domain. Fold claim/table
identities are checked against the approved registry, structure, and layout.

Native verification is a witness-generation check, not the circuit's soundness
argument. A replay export is not an acceptance certificate.

## Exact statement connections

`ExecBindingV0` is compiled only from the approved semantic profile, registry,
circuit, row counts, and explicit public-slot template. Fixed zero words stay
fixed; output positions are never inferred by perturbing a witness vector.

`constrain_exec_binding` computes both domain-separated hashes:

- `S = H4(P || B || I || O)` uses the private input commitment.
- `Q = H5(P || B || O)` is connected to the two external 128-bit digest limbs.

P is fixed by setup; B, I, and O are private circuit variables. The same B and
O wires occur in both hashes. The full Flock public vector is reconstructed
from the fixed template and the two computed S limbs; it is not free advice.
Its exact native chunked BLAKE3 digest is recomputed and bound to the main
transcript. Registry digest, all ordered counts including padding, and circuit
digest are also bound to their exact pre-challenge payloads.

The application must still implement
`verify(approvedConfig, publicCanonicalIxonClaim, compactProof)` and derive Q
from the approved profile/image and canonical result for that explicit claim.
Accepting an opaque prover-selected Q is not the final public-claim API.
Hash binding and backend cryptographic soundness remain named assumptions.

## Replay coverage and setup independence

The generic adapter records and exports:

1. Main chained-BLAKE3 transcript, fork/merge links, and fused PoW predicates.
2. Product-GKR wiring, public/gate recombination, and three structure claims.
3. Standard-RS Boolean zerocheck, union lincheck, and every A/B matrix claim.
4. Two ring switches, packed-direct claims, mixed batching, and dense sumcheck.
5. Multipoint/untwisted assist and its complete jagged assertion.
6. Inner Ligerito, F256 messages, OOD checks, queries, rows, and Merkle paths.
7. Matrix, circuit-structure, and jagged accumulator transcripts and folds.
8. The new generic Exec statement connections described above.

The native accumulator outputs are discharged against the actual fixed tables
as a differential. The circuit composition still exposes those roots publicly;
the differential is not a substitute for closing them inside the final proof.

Wiring and Boolean PIOP topology are independently reconstructed by symbolic
compilers rooted in `CompiledExec`. They never invoke a prover or verifier,
construct a guest, or evaluate witness values. They produce exactly the
arithmetic DAG, static constants, deferred claim identities, challenge/
observation indices, gather mappings, and Boolean PCS wires required by the
approved geometry. The merged PCS, multipoint/anchor assist, and complete
inner Ligerito topology are reconstructed too, including the fixed jagged
heights and every private row/path slot. Native replay is compared structurally
against them before it is returned to the caller.

A separate symbolic tape compiler fixes the complete main operation tree,
not just scalar counts: every label, slice width, PoW difficulty, nonce
payload, fork seed, child closure and merge position. It preserves the
distinction between absent grinding and an explicit zero-bit PoW, and between
one-word vector and scalar squeezes. Query values are never sampled during
setup and cannot alter the row/path allocation. All compilers run before the
strict native proof decoder.

The auxiliary compiler fixes every matrix/structure/jagged claim, fold round,
bridge, root slot, and auxiliary transcript operation. Both transcripts are
lowered to exact BLAKE3 stream sources, compression geometry, CV links, squeeze
sources, fork links, and PoW predicates without hashing or inventing dummy
messages/nonces. Native comparison excludes only the concrete CV/message
witness columns; the existing compression constraints must check their values.
Hash-layout differentials cover absorb/XOF/PoW boundaries with 336 native
instances, and 27 structural mutations are rejected.

The compiled object retains fourteen separate setup/component identities,
including domain-separated main and auxiliary operation-tree digests. It is
borrowed from its approved Exec setup and has no public field replacement or
prover-export constructor. The regression compiles it twice before creating
any guest, then reuses the same object for all three executions. Repeated
native equality is additional evidence, not permission to derive a key from
an arbitrary proof. A proof-free R1CS emitter and terminal key compiler still
need to consume the approved topology without relying on a valid assignment;
no such key-generation API is exposed here.

## Current evidence

The direct scalar setup is the same one exercised by Stage 3's 39-program/
primitive proof corpus: 256 code bytes, two functions, four blocks/function,
two operands, four locals, two continuations, two arguments, 64 input/output
bytes, two input values, and 24 transitions. Its setup digest is
`41163b87f03675917ac93824d8b1c11ab0c489c2fc2e03abece34d11fa3255f7`.

The Stage 4 replay regression uses a local-return program and a three-block
Boolean branch program with both branch outcomes. All three complete Exec
bundles are 296,091 bytes, including their 40-byte envelope. Their thirteen
phase/topology digests agree. No Stage 4 key or FFLONK proof is generated.

| Native replay component | Observed size |
| --- | ---: |
| Public words | 52: 50 fixed, 2 computed S limbs |
| Main transcript operations / challenges | 2,099 / 1,326 |
| Main transcript compression rows / PoW predicates | 1,588 / 320 |
| Boolean arithmetic operations / matrix claims | 3,822 / 46 |
| Wiring arithmetic operations / gather claims | 4,223 / 493 |
| Ligerito levels / queries / opened F128 values | 3 / 371 / 12,524 |
| Merkle path digests | 1,484 |
| Accumulator transcript compression rows / PoW predicates | 4,947 / 1,373 |
| Terminal diagnostic root families | 46 matrix roots, 1 structure, 1 jagged |

The 164 ordinary workspace tests pass; three tests are ignored by default
(the retained large two-ring projection and the two new native replay/census
tests). The real three-execution replay regression passes under a 32 GiB
address-space cap with four Rayon threads. The complete matrix-free census
finished successfully in 1,161.51 seconds, including setup, under that cap.
The first 900-second timeout is superseded by this completed run. The retained
[exact census](../flock-stage4/census/exec-scalar-root-conditional-v0.json)
pins the relation revision, reproduction command, counts, projection digest,
timing scope, and sampled process memory counters.

| Complete root-conditional sizing | Result |
| --- | ---: |
| R1CS constraints / nonzero terms | 590,712,359 / 2,795,440,842 |
| PLONK constraint rows | 989,490,840 |
| PLONK base / polynomial-FFT domain | `2^30` / `2^32` |
| Public scalar vector (including Q) | 1,327 scalars / 42,464 bytes |
| Required SRS degree | 9,663,676,433 |
| Compressed file-SRS bytes | 463,856,469,048 |
| Modeled file-key/SRS/FFT resident payload minimum | 420,923,572,256 bytes |
| Last sampled process high-water RSS | 3,548,100 KiB |

PCS accounts for 350,773,578 R1CS constraints; all transcript chains for
105,378,574; accumulator arithmetic for 106,032,537. These are full counts,
not estimates extrapolated from a prefix. The matrix-free census does not
store a complete witness or check its satisfaction, and the memory figure is
not a terminal prover's RSS. The capacity payload excludes several buffers,
R1CS/witness storage and runtime overhead. It is not evidence of fitting a
particular host. Root closure is additional work/cost. No terminal SRS, key,
materialization or proving job was started; this geometry requires cost
reduction before an admitted complete proof.

The binding tests materialize and check their R1CS, mutate both public limbs,
fixed public words, S wires, and every bound prefix payload including count
padding, and reject changed P/B/I/O or registry/circuit/counts. Different
component values produce identical binding matrices. Native bundle mutations,
wrong commitment openings, truncation, trailing bytes, and both historical
artifact domains are rejected.

## Remaining gates

Implement proof-free R1CS/key compilation from the approved replay blueprints;
extend phase-specific hostile message tests; close every unresolved table
evaluation in the final relation;
then actually prove and isolate-verify that complete relation with only an
approved terminal configuration, externally expected statement, and compact
proof. Resource admission must use the new complete geometry including root
closure. The 992-byte legacy proof-body codec remains only a transport fact.

The scalable guest operations, native representation/refinement proofs,
certified compiler handoff, and changed-Stage-2-guest upgrade test remain part
of the original plan. This replay port does not discharge them.
