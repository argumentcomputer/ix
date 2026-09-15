# Constrained functional codec components

`flock-stage3/host/src/ixby/ixbf_decode` starts the constrained correspondence
to the **original IXBF format 1, semantics 0** bytes. It is separate from both
the complete host reader and the existing IXBY native Exec decoder. The new
components do not admit an IXBF program to Exec or prove the Init run.
The later [record and reference-check components](IxbyFunctionalRecords.md)
extend this layer toward body and value parsing, with the same explicit
source-authentication and whole-parser obligations.
The subsequent [grammar-control layer](IxbyFunctionalGrammar.md) adds complete
ordered traversal and EOF, but not whole-file source/registry authentication.
The later [scalar payload layer](IxbyFunctionalScalars.md) adds checked packing,
the declared Nat-bit limit and streaming strict UTF-8 with decoder/state wiring.

## Component relations

| Component | Explicit boundary | Boolean table |
| --- | --- | --- |
| `NaturalDecodeGate` | Canonical LEB128 payload, 0–4,096 magnitude bits; at most 586 encoded bytes | At 4,096 bits: `k_log = 15`, 28,628 used columns |
| `HeaderDecodeGate` | Fixed 272-byte prefix; 13 exact u128 metadata fields; u64 file length and cursor | `k_log = 17`, 129,069 used columns |
| `ByteArraySpanGate` | 32-byte lookahead; canonical ByteArray tag/length; u128 declared limit; checked u64 payload range | `k_log = 13`, 4,332 used columns |

The table shapes depend on codec capacities, not on the image, field values,
or byte-array payload size. Zero magnitude bits admits Nat zero. Header
metadata above 128 bits and natural payloads above the selected bit capacity
reject; they do not truncate. The host reader still preserves arbitrary-
precision metadata under its separate loader limits.

Natural decoding derives all live-byte flags from continuation bits. It checks
the first terminator, minimality, exact payload length, overflow, and canonical
padding. Disabled payload rows require zero length/data and produce zero.
Magnitude limbs are exact little-endian bits, not sums in the binary field.
This is a payload codec: it does not check a surrounding scalar tag or a
guest-specific Nat limit smaller than its setup capacity. The later
`NaturalLimitGate` supplies that separate check using the actual magnitude
and declared-limit wires.

The header checks `IXBF`, format 1 and semantics 0, then decodes the ten
execution limits, `maxSteps`, entry index, and constructor-vector count in
their original order. It checks that the count fits its declared limit and
remaining file bytes, and returns the exact constructor-table offset. Bytes
after the parsed header may belong to the body and are not forced to zero;
only bytes after file EOF are padding. Constructor/function bodies, entry
validity, and other whole-image checks remain separate obligations.

The ByteArray component starts at scalar tag 6. From that tag and its minimal
LEB128 length it derives `(payload start, payload length)` and the next cursor.
It checks the declared byte-array limit, file bounds, lookahead padding and
every arithmetic carry. Payload contents are not copied into the parser row.
An immutable record must additionally carry the correct artifact identity,
and every later payload read must be authenticated against that artifact.
String and outer value tags are not interchangeable with ByteArray tag 6.

Every slot wrapper connects its validity residual to a verifier-owned zero.
All outputs and unused table columns/rows are constrained; witness drivers
fully overwrite recycled buffers and count-aware constant stripes. Count-only
emission is lazy and checked against actual compilation.

## Cross-component wiring and evidence

The conformance setups connect the decoded `maxSteps` wire directly to both
the initial fuel state and the ledger's original budget. Consequently the
u64 ledger refuses a wider decoded budget instead of treating its upper lane
as already-consumed fuel. A second setup connects the decoded byte-array limit
directly to the ByteArray range checker. Neither consumer accepts an
independently host-selected replacement limit.

The initial three codecs have thirteen ordinary tests covering all 4,096 Nat
basis bits, every component output bit, malformed/nonminimal/truncated data,
arithmetic limits, EOF padding,
count/emission parity, and recycled witness buffers. Their six original opt-in
tests check independent artifacts and real Flock proofs:

- All 81 compiler-corpus headers and 89 corpus Nat literals match constraints.
- The exact Init header and all 608 Init Nat literals match constraints.
- All six original program ByteArray literals, two Init input values and one
  output value have the exact constrained ranges. Input payloads start at
  offsets 16 and 56 with lengths 34 and 9,611,064; the output payload starts at
  offset 15 with length 34.
- Fourteen honest component proofs verify in fresh environment-cleared
  processes receiving only the approved component selector, expected public
  words and proof. This includes the real Init prefix, its decoded fuel budget,
  and its three I/O ranges tied to the decoded byte-array limit.
- Five locally valid, fully recomputed advice substitutions fail global
  wiring verification. A sixth proof using a header budget wider than u64
  also fails fresh verification. Modified public words, component/domain
  identifiers, truncation and trailing proof data reject.

The Nat literal differentials canonically re-encode host-decoded values;
they do not prove discovery of those literals at their original offsets.

| Conformance class | Complete bundle bytes |
| --- | ---: |
| 4,096-bit natural payload | 109,524 |
| 128-bit header metadata | 111,196 |
| Header-derived fuel | 115,300 |
| ByteArray range | 107,244 |
| Header-derived ByteArray limit/range | 115,332 |

The test envelope is `IXFCOD00`, with explicit component tags and separate
transcript domains. These are **not IXBYEX00 Exec proofs**. The expected public
inputs include the exact prefix/lookahead/payload words relevant to each codec;
they are not a substitute for the full original program/input commitment.
Artifact hashes used to select external fixtures are raw BLAKE3 hashes, not
Exec statement digests. The verifier does not run the host decoder.

```sh
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml --workspace ixby::ixbf_decode:: \
  -- --test-threads=1
IXBY_IXBF_CORPUS=/path/to/compiler-corpus \
IXBY_IXBF_STAGE2_IMAGE=/path/to/stage2.ixby \
IXBY_IXBF_INIT_INPUT=/path/to/init.ixbi \
IXBY_IXBF_INIT_OUTPUT=/path/to/init.ixbo \
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml --workspace ixby::ixbf_decode:: \
  -- --ignored --test-threads=1 --nocapture
```

The measured runs use the unchanged Flock pin/Fast128 PCS admission, four
Rayon workers, a 32 GiB virtual-address cap and a 600-second timeout. Component
costs are not full-program or Init-execution prover estimates. On 2026-09-14,
the warm six-test opt-in run took 19.63 seconds wall time with 276,084 KiB
reported maximum RSS, including the independent-fixture checks, fourteen
honest proofs, six forged proofs, and their isolated verifications. Other
local regressions ran concurrently; this is neither a single-proof timing
nor the combined memory use of all concurrent test suites.

## Remaining correspondence work

The later record components cover local constructor/function/instruction and
input-value prefixes, and the grammar component constrains their complete
ordered traversal and EOF. The scalar layer supplies checked payload packing,
guest Nat limits and UTF-8. The later [generic dispatcher](IxbyFunctionalDispatch.md)
derives decoder selection and source requests from carried state and proves
complete small-file grammars with a once-authenticated shared byte buffer.
The [declaration/header registry layer](IxbyFunctionalRegistry.md) additionally
materializes constructors, functions and owned block headers, checks complete
coverage/uniqueness/entry frames, and provides source-bound typed reads in a
bounded class. The [instruction/reference layer](IxbyFunctionalReferences.md)
connects all Program arities, successor frames and duplicate alternatives to
those actual reads. Typed body/value materialization, transport reference
checks and scalable shared chunk authentication remain required. ByteArray consumers
must use the actual constrained descriptor. The complete execution path still needs
streaming witnesses, scalable memory/code access, full-state segments and
sound composition. No source/refinement theorem is established here, and no
existing Exec profile, setup key or resource cap is changed. See the
[scaling plan](IxbyStage3ScalePlan.md).
