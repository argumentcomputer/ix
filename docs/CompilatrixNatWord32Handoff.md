# Compilatrix handoff: direct Nat ↔ Word32 conversions

## Scope

Ixby now provides two unary primitives in its Lean reference semantics and
the complete functional Flock backend. Compilatrix integration is left to the
compiler owner. This is a **breaking IXBF program revision**: regenerate
programs, profiles, statements, and proofs after integrating it.

The motivation is the existing CSLib profile: `toWord`, `fromWordLoop`,
`nibbleWord`, and `nibbleNat` account for **240,523,261 of 2,268,502,805 logical
transitions (10.60%)**. That is the cost of the existing helpers, not a measured
speedup from this change. The compiler has not yet emitted a CSLib image using
these primitives. See [the measured runtime costs](IxbyPerformance.md).

## Semantic contract

| Lean primitive | Functional opcode | Argument | Result |
| --- | --- | --- | --- |
| `Primitive.natToWord32` | `45` (`0x2d`) | one `.scalar (.nat n)` | `.scalar (.word32 n.toUInt32)` |
| `Primitive.word32ToNat` | `46` (`0x2e`) | one `.scalar (.word32 w)` | `.scalar (.nat w.toNat)` |

`natToWord32` returns `n mod 2^32`. It does **not** fail merely because `n` is
greater than `2^32 - 1`. `word32ToNat` returns the exact unsigned integer in
`[0, 2^32 - 1]`.

Both use the existing `Primitive.eval` checks, in order:

1. Require exactly one argument (`.arityMismatch 1 actual`).
2. Validate scalar arguments against the semantic limits.
3. Require the indicated source type (`.primitiveType primitive`).
4. Compute the conversion and validate the result against the limits.

In particular, a Nat exceeding `limits.natBits` must fail **before** truncation.
A Word32 → Nat result exceeding that limit must also fail. Zero fits a zero-bit
Nat limit in both directions. There is no implicit coercion between the types.

The definitions are in [Basic.lean](../Ix/Ixby/Basic.lean) and
[Primitive.lean](../Ix/Ixby/Primitive.lean); the reference tests, including
kernel-checked examples, are in [Basic tests](../Tests/Ixby/Basic.lean).

## Binary changes

All integers below are little endian. Metadata, natural LEB128 encodings,
value tags, instruction tags, and existing primitive opcodes `0..44` retain
their layouts and meanings.

| Artifact | Header |
| --- | --- |
| Program `.ixby` | `IXBF`, `u32 format = 1`, **`u32 semantics = 1`** |
| Input `.ixbi` | `IXFI`, `u32 format = 1`, `u32 semantics = 0` |
| Output `.ixbo` | `IXFO`, `u32 format = 1`, `u32 semantics = 0` |

The exact new program prefix is `49 58 42 46 01 00 00 00 01 00 00 00`.
Program semantics `0` is rejected, including programs using only old opcodes.
Input/output semantics `1` is rejected. Keep separate program and value
revision constants in the compiler.

A primitive operation is still operation tag `1`, one opcode byte, the
canonical natural argument count, then the operands. For example:

```text
01 2d 01 00 00   # natToWord32 [local 0]
01 2e 01 00 01   # word32ToNat [local 1]
```

These are operation bytes, without the surrounding block/local-count,
`letOp` instruction tag, or successor block index. Admit exactly 47 opcodes;
`47..255` remain invalid. Enforce unary arity during whole-program validation.

The Flock `IXFP` profile remains exactly 184 bytes:

```text
offset  0: "IXFP"
offset  4: u32 profile revision = 0
offset  8: u32 program format = 1
offset 12: u32 program semantics = 1  # changed from 0
offset 16: ten u128 limits in the existing order
offset176: u64 maxSteps
```

This changes the profile digest as well as the program commitment and final
statement `S`. Input/output bytes may remain identical, but their commitments
also include the new program commitment. Recompute them all from the new
artifacts. Existing execution and admission proof setups must be regenerated.

The older experimental **`IXBY` / `IXBP`** crypto profiles are a separate wire
family. They continue to reject these two primitives. Do not reuse their
opcode table for `Compilatrix.Ixby.Binary`.

## Suggested compiler patch

The following paths were inspected in Compilatrix at commit `18da375`.

1. Update the vendored Ixby `Basic.lean` and `Primitive.lean`, and record the
   actual Ixby source revision and file hashes in `vendor/ixby/upstream.json`.
   Keep the compiler's pinned Lean toolchain unchanged unless deliberately
   handling a separate toolchain migration.
2. In `Compilatrix/Ixby/Binary/{Common,Encode,Decode}.lean`, set the **program**
   semantics revision to `1`, add opcodes `45` and `46`, preserve the value
   headers, and extend the encoding/decoding proofs and exhaustive corpus.
3. Replace the two helper bodies in `Compilatrix/Ixby/Runtime/Number.lean`.
   Preserve their three-argument interfaces and function identities so the
   other runtime helpers and source certificates keep calling the same APIs:

   ```text
   toWord(n, wordWeight, wordAcc):
     low      = natToWord32(n)
     weighted = word32Mul(low, wordWeight)
     result   = word32Add(wordAcc, weighted)
     return result

   fromWordLoop(word, natWeight, natAcc):
     natural  = word32ToNat(word)
     weighted = natMul(natural, natWeight)
     result   = natAdd(natAcc, weighted)
     return result
   ```

   Each body needs three primitive instructions and one return block. With
   three original locals, results occupy locals `3`, `4`, and `5`. Preserve the
   exact accumulator/weight contracts; replacing either helper by its first
   conversion alone would be wrong for general callers.
4. Update the exact templates in `Runtime/ConversionCode.lean`, the proofs in
   `Runtime/ToWord.lean` and `Runtime/FromWord.lean`, and primitive evaluation
   lemmas in `Runtime/ScalarLaws.lean`. Keep public theorem names and premises
   where practical. `ConversionCertificate.lean` and the Lean soundness image
   checks must still certify the actual generated bodies.
5. Keep the nibble helpers initially if that avoids changing the function
   inventory. The new conversion bodies no longer call them. Removing dead
   helpers can be a separate compiler pass.

The old `fromWordLoop` computes a next weight that can reach `2^32`, even when
the returned Nat fits in 32 bits. The direct body removes that intermediate.
Review any tests or resource contracts depending on the old 33-bit capacity
requirement. The new `word32ToNat` still checks its own intermediate Nat result,
and the multiplication and addition retain their ordinary Nat capacity checks.

## Proof backend boundary

The paged backend routes both conversions through its immediate Nat128 gate:
control `8` means Nat → Word32, and `9` means Word32 → Nat. These controls are
derived from the authenticated program opcode, not supplied as unconstrained
advice. This reuses the existing numeric execution step and introduces no new
instruction family or call frame.

The source Nat can contain all 128 immediate payload bits. Only the low 32
become the Word32 result. In the reverse direction, the source's upper 96 bits
must be zero, and the exact low 32 bits become a Nat. Source and result tags,
unary padding, division-advice padding, and every output bit are constrained.

The Lean reference semantics still supports arbitrary-size Nat values within
the declared semantic limit. The current paged prover retains its existing
physical restriction to immediate Nat128 values and requires a semantic Nat
limit of at least 128 bits. This patch does not add arbitrary-precision proof
arithmetic.

## Compiler acceptance checks

- Check zero, `1`, `2^32 - 1`, `2^32`, `2^65 + 37`, and the maximum supported
  Nat. The wider examples must truncate to the low 32 bits, after source-limit
  validation.
- Check wrong source types, zero/two arguments, over-limit Nat sources and
  results, old program headers, and unknown opcodes. Preserve exact I/O bytes.
- Prove the existing weighted/accumulated helper contracts, including general
  weights and accumulators; run all conversion/number/field certificates,
  focused runtime tests, required axiom fences, trust audit, and Nix checks.
- Recompile CSLib; rerun the full reference observer and compare its output
  bytes with the old output. Record the new program hash, transitions, helper
  census, and expected statement. Measure the improvement from that new run.
- Export the new program and independent expected I/O for native execution and
  proof checks. A successful fixture proof does not establish a CSLib proof.

## Follow-on breaking changes

These are design recommendations, separate from the implemented conversion
revision. Compatibility with retired formats need not constrain their design.

1. **Unboxed numeric runtime values.** Use the existing distinct Nat, Word32,
   and Field scalar types directly wherever the source representation permits
   it. Remove the `Number(n, lowWord)` wrapper and repeated extraction in those
   paths. The `natural` helper alone accounts for 220,428,864 transitions
   (9.72%). This is the next compiler change to consider while updating its
   representation certificates; preserve arbitrary-size Nat behavior and
   explicit conversions between types.
2. **Native persistent arrays.** Define checked array get/set primitives with
   precise indexing, bounds, and sharing semantics. The current `treeGet` and
   `treeSet` helpers account for 479,966,998 transitions (21.16%). The prover
   needs authenticated paths and checked updates, and the compiler needs a
   representation theorem relating those paths to the source array.
3. **Byte slices and builders.** Define immutable slices and a builder/freeze
   interface, with exact length, aliasing, and bounds rules. Avoid a mutable
   buffer escaping into an immutable source value. Four byte-tree helpers
   account for 328,622,405 transitions (14.49%); replacing their interpreted
   balancing needs matching reference semantics and proof constraints.
4. **One compiler-facing format.** Retire experimental `IXBY`/`IXBP` intake
   and consolidate new compiler integrations on `IXBF`. Remove obsolete
   decoders and selectors when retiring their backends; retain historical
   performance records as records of the revisions actually measured.

The percentages describe separate helper groups in the old CSLib run. They
are opportunities to investigate, not additive predictions of achieved savings.

## Ixby validation

- All 339 checks in the Basic, Crypto, Codec and NatCodec Lean suites pass.
  The trust audit passes 333 theorem roots and a 3,240-declaration source
  frontier. Conversion boundary examples are checked by the Lean kernel.
- All 55 affected Rust checks pass, including every conversion output bit,
  high source bits, type/arity errors, inactive padding, exact fuel,
  authenticated code capture, and complete endpoint wiring.
- The independent seven-step fixture produces a **499,443-byte complete
  recursive execution proof**, including all eleven component proofs and the
  endpoint check. Input `2^65 + 37` becomes output bytes `[42, 0, 0, 0]` through
  Nat → Word32 → Nat, addition of five, Nat → Word32, and Word32 → Bytes.
- The exact expected statement is
  `ecc83e788c114efa6d11fd2a0621fc3472303b38f5ce1de9953e6be684e62e37`.
  An independent BLAKE3 calculation matches the generated statement.
- A fresh process with the fixed profile and class, given only the statement
  and root proof, accepts it and rejects all eleven statement/proof mutations.
  Setup takes 137.12 seconds and verification takes 18.55 seconds. Both Rust
  workspaces pass all-target Clippy with warnings denied. The
  [validation record](../flock-stage4/census/paged-execution-conversions-v1.json)
  includes artifact hashes, complete geometry, timing, and source pins.

Generate the fixture and prove it from the Ixby checkout:

```sh
python3 flock-stage4/fixtures/paged-execution-conversions.py --out /tmp/conversions
cargo build --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-flock-recursion --bin paged-execution
flock-stage4/target/release/paged-execution profile \
  --program /tmp/conversions/program.ixby --out /tmp/conversions/profile.ixfp
flock-stage4/target/release/paged-execution prove \
  --profile /tmp/conversions/profile.ixfp --class bytes --threads 4 \
  --program /tmp/conversions/program.ixby --input /tmp/conversions/input.ixbi \
  --output /tmp/conversions/output.ixbo --out /tmp/conversion-proofs
flock-stage4/target/release/paged-execution verify \
  --profile /tmp/conversions/profile.ixfp --class bytes --threads 4 \
  --counts 1,1,1,1,1,1,1,1,1,1,1 \
  --statement /tmp/conversion-proofs/root.statement \
  --proof /tmp/conversion-proofs/root.flock
```

The measured local run used an 84 GiB RAM cap with swap disabled and took
560.11 seconds inside the CLI (568.13 seconds including process cleanup).
This is an integration check, not a CSLib performance benchmark.
No compiler integration or full CSLib proof is claimed by this handoff.
