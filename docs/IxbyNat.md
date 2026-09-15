# Exact Nat compiler handoff

The pure profile, canonical codec, reference byte executor, and an explicit
[native Flock setup](IxbyFlockNats.md) support `ProfileRevision.cryptoNatV1`.
Flock now constrains all seven Nat primitives, `caseNat`, canonical Nat I/O,
and transport through first-order calls and immutable constructors. Thirty
small executions have real Flock proofs. Aiur still rejects revision 1.
The native constraint-to-reference theorem, scalable guest execution and
compiled Stage 2 guest proof remain unfinished.

Select the revision explicitly and choose a measured bound, for example:

```lean
def guestProfile : Ix.Ixby.Profile := {
  revision := .cryptoNatV1
  limits := { natBits := 96, stringBytes := 0 }
}
```

Here 96 is only an example, not the Stage 2 guest's established requirement.
Keep Nat and Word32 distinct. `natBits` bounds literals, inputs, and primitive
results; exceeding the bound fails instead of wrapping. Zero-bit capacity admits
only Nat zero. Word32 retains modulo-`2^32` arithmetic and its existing byte
indexing/conversion semantics. String remains excluded.

Use `profile.primitives`, `profile.primitiveOpcode`, `profile.validateProgram`,
and `Codec.encodeProgram/encodeInput/encodeOutput` with that same profile.
The legacy `cryptoPrimitives`, `Primitive.cryptoOpcode`, and `cryptoSupported`
helpers deliberately continue to describe v0 only.

The [wire specification](IxbyEncoding.md) preserves the 68-byte profile and all
existing tag/opcode assignments. V1 uses wire/semantic revisions 1/1, scalar tag
5 for minimal little-endian Nat magnitudes (zero has an empty payload), instruction
tag 7 for `caseNat`, and appended primitive opcodes:

| Opcode | Operation | Meaning |
| --- | --- | --- |
| 35 | `natAdd` | Exact sum |
| 36 | `natSub` | Subtraction truncated at zero |
| 37 | `natMul` | Exact product |
| 38 | `natDiv` | Quotient; division by zero returns zero |
| 39 | `natMod` | Remainder; modulo zero returns the dividend |
| 40 | `natEq` | Equality returning Bool |
| 41 | `natLt` | Less-than returning Bool |

`caseNat` keeps the original frame in the zero branch and appends the exact
predecessor in the successor branch. No Nat↔Word32 conversion operation has been
added; report any required conversions with their exact source semantics.

Verification: `Tests/Ixby/NatCodec.lean` passes 64 checks covering independent
profile/value/opcode goldens, all seven operations, values beyond 64 bits,
literal/constructor/PAP transport, `caseNat`, exact partial-byte bit bounds,
overflow, malformed/truncated encodings, shared resource limits, and revision
separation. Four small arithmetic equations are also kernel-checked with `rfl`.
The existing generic `Profile.execute_refines` and
`Codec.Execution.reference_evaluates` bridges apply to this revision as well.

The native entry is `compile_exec_nat_profile(profile, machineCapacity,
(byteCapacity, optionalObjectCapacity, natCapacity), primitives, backend)`.
Use `SemanticProfile::nat` and `PrimitiveSet::crypto_nat()` or an explicitly
approved `PrimitiveSet::with_nat(...)` subset. The current Boolean prototype
allows `NatCapacity::new(bits)` for 0–1024 bits; this is an admission bound,
not a measured production profile. It shares the immutable byte arena and
requires byte capacity at least `ceil(natBits / 8)`. Existing v0 factories and keys remain
v0; parsing v1 profile bytes alone does not upgrade them. See the
[native construction and measurements](IxbyFlockNats.md) for its narrower
physical limits and proof boundary.

Still required from the compiler: actual Nat operation usage, required maximum
`natBits`, Nat↔Word32 boundary operations, and the concrete guest's other capacity
requirements. These determine guest admission and sizing; they do not block
the now-implemented parameterized native Nat constraints. Formal refinement
and full-guest capacity work remain separate obligations.
