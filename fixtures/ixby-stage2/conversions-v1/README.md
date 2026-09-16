# Direct conversion fixture

These frozen files match the independent generator
`ix@d4405b3ceb82e6d4cce19e48186f3272f8482e04:flock-stage4/fixtures/paged-execution-conversions.py`.
`CompilatrixTests.Ixby.Conversions` constructs and serializes the program and
compares it with independently retained literal bytes. The required `ixby-lean`
Nix check compares its exports with these files and executes the serialized
program in a standalone process.

| File | Bytes | Meaning |
| --- | ---: | --- |
| `program.ixby` | 77 | IXBF format 1 / semantics 1; seven transitions |
| `input.ixbi` | 25 | One Nat: `2^65 + 37`; IXFI format 1 / semantics 0 |
| `output.ixbo` | 19 | Bytes `[42, 0, 0, 0]`; IXFO format 1 / semantics 0 |
| `profile.ixfp` | 184 | Profile 0, program format 1 / semantics 1 |
| `expected.statement` | 32 | Raw BLAKE3 statement bytes |

The program converts Nat → Word32 → Nat, adds five, converts to Word32 and
then bytes, and returns. Its limits are `[1, 0, 6, 6, 2, 0, 8, 128, 0, 64]`
in the [documented order](../../../docs/ixby-binary.md#program-file-ixbf),
with `maxSteps = 7`.

The expected statement is
`ecc83e788c114efa6d11fd2a0621fc3472303b38f5ce1de9953e6be684e62e37`.
The [integration record](../nat-word32-integration.json) retains every file's
SHA-256/BLAKE3 digest, independently recomputed profile and commitments,
and successful fresh verification of the upstream 499,443-byte proof.
The proof and prover executable are external measurement artifacts; this
fixture does not assert a full CSLib proof.
