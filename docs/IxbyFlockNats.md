# Exact bounded Nat execution in Flock

The explicit revision-1 native setup implements all seven exact Nat primitives,
`caseNat`, canonical magnitude decoding/output, and transport through existing
first-order control, byte operations and optional immutable constructors.
Thirty execution proofs verify under one setup, including values above 128
bits. This is native execution evidence, not the missing native-matrix-to-Lean
refinement theorem, a compiled Stage 2 guest proof, or a terminal SNARK.
Aiur has not been upgraded. The [compiler handoff](IxbyNat.md) and
[wire specification](IxbyEncoding.md) define the common semantics.

## Explicit setup and representation

`compile_exec_nat_profile(profile, machineCapacity,
(byteCapacity, optionalObjectCapacity, natCapacity), primitives, backend)`
accepts only verifier-owned capacities, profile, primitive registry and
implementation selection. No program, input, trace, proof, resolved arithmetic
result or Stage 2 key determines setup. `SemanticProfile::nat` creates the
matching revision-1 profile. `PrimitiveSet::crypto_nat()` admits opcodes 0–41;
`PrimitiveSet::with_nat(...)` selects an explicit subset.

`NatCapacity::new(bits)` currently admits 0–1024 bits. Arithmetic uses a
fixed-width Boolean prototype, with quadratic multiplication/division cost;
the upper API bound is not a demonstrated resource fit. A zero-bit Nat is
necessarily zero. The immutable byte arena must have capacity at least
`ceil(bits / 8)` and still has its existing nonzero byte-capacity requirement.
This factory therefore does not implement every pure profile, including
profiles with byte storage disabled. Constructor and other machine limits
remain those of the existing bounded factories.

Nat cells use a distinct internal tag 8 plus a canonical u32 immutable-record
index. Word32, Bytes and Constructor retain tags 2, 6 and 7. These physical
tags are not wire scalar tags: canonical external Nat uses scalar tag 5.
Nat records share the authenticated byte arena, carrying a presence bit,
length and little-endian magnitude words. Empty magnitude represents zero;
nonempty magnitudes end in a nonzero byte. The exact bit bound, including
partial high bytes, and all length/word padding are constrained.

Decoder-owned allocation slots derive from canonical authenticated program
and input bytes. Every execution step owns one future allocation slot, filled
by its constrained byte or Nat producer. Full-index reads, record presence,
typed handles and producer wiring prevent host heap or magnitude substitution.
Constructor fields and saved frames carry the same immutable handles. No
implicit or explicit Nat↔Word32 conversion has been added.

## Arithmetic and control constraints

Addition checks the final carry; multiplication retains the full double-width
product and requires its high half to be zero. Neither operation wraps at the
Nat bound or at the F128 field width. Subtraction selects zero on underflow.
Restoring division keeps an extra remainder bit before each subtraction;
division by zero gives quotient zero and remainder equal to the dividend.
Equality and less-than return Bool. Inputs and results obey the same exact
`natBits` limit.

The dispatch gate receives fetched instruction headers, resolved typed
operands and two wired arena reads. Arithmetic results and acceptance
residuals are derived Boolean wires, not advised quotients or a host evaluator's
acceptance flag. Nat opcodes are masked out of the existing Word32/byte
primitive path before its constrained dispatch.

For `caseNat`, zero preserves the old frame. A successor appends a newly
allocated exact predecessor and then uses the existing ordered-frame branch
transition. This consumes one VM step, not an extra arithmetic step. Both
destination frame contracts are checked during whole-image admission, even
when unreachable. Canonical output is derived from the terminal value and
authenticated records, including Nat fields nested in constructor trees.

All these components feed the existing complete P/B/I/O/S commitment chain.
Fresh verification consumes only the approved compiled setup, externally
expected 32-byte S, and strict proof bytes. It receives no private artifacts
or reference execution. Nat uses the separate `ix:ixby:nat-exec:v1` transcript
and binds the revision, bit bound, implementation, registry and circuit into
setup identity. Existing scalar, byte and constructor v0 factories still
reject revision 1 and Nat registries; their golden identities are unchanged.

## Proof evidence and measured resources

The fixed proof fixture uses a 192-bit Nat bound; program/input/output buffers
256/192/192 bytes; 2 functions, 3 blocks per function, 4 locals, 2 operands,
2 continuations, 2 input roots and 8 transitions; byte capacity 33; and
2 constructor declarations, depth 3 and 7 external nodes. Its census is
`nu=12`, `m=24`, 38 tables, largest inner exponent 22. Setup identity:

```text
b82c5886b0e40c74c45aa0f7939a3470d2791e275465e3851170857d6e218376
```

All 30 executions produced 387,819-byte Flock proof envelopes, excluding the
separate expected 32-byte S. They cover all seven operations, saturation and
zero divisors, unchanged Word32 wrapping, guest BLAKE3, zero/one/multiword Nat
inputs and literals, both Nat cases, mixed Nat/byte constructors, projection,
constructor-case arithmetic, direct calls and recursive walks with zero, one
or two decrements. Each verified in a fresh environment-cleared process outside the worktree,
which rebuilt only the approved setup and read S plus proof on stdin.

Two forged proofs replaced arithmetic/case rows with locally valid, fully
recomputed rows for different magnitudes. Actual local R1CS satisfaction was
checked before proving; both isolated verifiers rejected the global splice
with `Wiring(Gkr(ProductMismatch))`. Wrong outputs, proof mutations, changed
Nat capacity and replay under the v0 constructor setup also reject, including
proofs with renamed setup headers.

The 2026-09-13 local run took 584.37 seconds for the complete 30-case plus
two-forgery test (584.98 seconds including command overhead). Individual
proving took 4.472–5.559 seconds; fresh verification took 9.825–11.110 seconds.
GNU time reported maximum RSS 41,620,640 KiB, about 39.69 GiB, with no swaps.
This is its reported maximum RSS, not an aggregate concurrent-process peak.
The run used four Rayon threads, a 64 GiB virtual-address limit and a
1,800-second timeout. These are small-profile diagnostic measurements, not
maximum-bound, production, or Stage 4 sizing results.

## Regression and formal boundary

Eleven focused ordinary tests cover the Nat dispatch, authenticated reader,
program/input decoders and output encoder. They check real Boolean R1CS
constraints, malicious outputs and recomputed residuals, full derived record
bits, canonical prefixes/partial-byte bounds and recycled row padding.
Arithmetic differentials include all 1,792 four-bit operation/input triples
and 546 BigUint cases across 13 bit bounds from zero through 257. Three more
ordinary execution/setup tests cover the 30-case corpus, revision and capacity
admission, and non-object setups with zero- and nine-bit bounds, including
invalid types, overflow and noncanonical input rejection. Host execution
rejection alone is not cryptographic verification.

`Tests/Ixby/Flock/Nats.lean` adds 17 independent reference checks and three
whole-statement goldens also asserted by Rust. Kernel-checked zero/successor
control traces use the new `Step.caseNatZero`/`Step.caseNatSucc` rules through
`Step.reference` and the finite-trace theorem, with exact fuel exhaustion.
The 64 earlier Nat codec checks remain in `Tests/Ixby/NatCodec.lean`.
None of these establishes the still-missing native-matrix refinement theorem.

```sh
RAYON_NUM_THREADS=4 cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace -- --test-threads=1
RAYON_NUM_THREADS=4 prlimit --as=68719476736 --core=0 -- \
  timeout 1800 cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  -p ixby-flock ixby::exec::nat_tests:: -- --ignored --test-threads=1 --nocapture
lake test -- ixby-flock-nats ixby-nat-codec ixby-flock-contract
lake build --wfail Ix.Ixby.Audit Tests.Ixby.Audit
```

The Nat proof test is explicitly opt-in; it has not been added to the paid
CI proof tier or given a larger runner budget. Its measured memory exceeds
the older 32 GiB budget, so do not infer CI admission from local success.
Compiler measurements, scalable code/byte/heap access, closure/PAP support,
formal refinement and terminal sizing for this upgraded setup remain open.
