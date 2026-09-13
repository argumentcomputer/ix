# Experimental IxBy Exec contract

Status: execution statements, public-claim binding, setup interfaces, and
conditional composition are implemented. The optional Stage 2 specialization
now composes the independent source refinement. The generic Flock interpreter,
complete terminal relation, and Compilatrix certificate remain unfinished.

## Statements and public claims

`Claim.Exec P S` means a finite admitted `Codec.Evaluates` run opens all four
components of the existing commitment statement `S = (P, B, I, O)`. Its opening
contains exact profile/program/input/output bytes and the canonical profile
encoding equation. Witness generation is not a proof of this proposition.

`Claim.PublicStatement` is `(P, B, O)`. Only `I` is existential at the terminal
boundary: it must still be bound to the actual Stage 3 statement. The caller
supplies the approved profile/image and public canonical Ixon claim `C`.
`Claim.IxonAdapter.expected` reconstructs the expected output and statement;
the caller does not accept a prover-selected digest as a replacement for C.

The initial result ABI represents success as `Value.scalar (.bytes C.ser.data)`
and rejection as `Value.erased`. These have distinct value tags. This is an
explicit wrapper ABI, not a claim about the compiler's default Option layout.
The certified source wrapper must return those success bytes only after
checking the proof against C and the approved Stage 2 configuration.
With this result ABI, that configuration must be closed over by the approved
guest, or checked against an approved constant/digest inside it. It must not
be a freely chosen private key/policy input. A future parameterized public
configuration ABI needs its own explicit statement binding.

The first Ixon adapter admits only `.checkEnv root none`. Its canonical wire
is exactly 34 bytes: `e5 || root[32] || 00`. The adapter checks size/tag before
the general parser, consumes the complete buffer, and retains its exact
re-serialization equation. Other claim kinds, malformed address lengths, and
conditional claims are rejected; their tags/assumptions are never discarded.
The pure `MultiStark.Verify.Claim` component derives the aggregate entry point
and both 8-word BLAKE3 digests (allowed-key identity and C) from the approved
configuration and this exact serialization. Differential tests check it
against the host construction. The pure claim-bound verifier now composes the
complete deterministic protocol checks with independent typed and byte-level
protocol refinements. Compiler certification and cryptographic soundness
remain separate gates; see [Stage 2 verifier](Stage2Verifier.md).

`Claim.IxonAdapter` is an explicit host import because `Ix.Claim` transitively
imports native address hashing. The pure `Ix.Ixby` import includes no such
adapter or FFI, and none of the composition proofs relies on its native calls.

## Canonical experimental wire

Every digest is exactly 32 bytes. Versions are little-endian u32, currently 0.

| Object | Encoding | Bytes |
| --- | --- | ---: |
| Complete execution statement | `IXBE || version || P || B || I || O` | 136 |
| Public result statement | `IXBR || version || P || B || O` | 104 |

Decoders reject wrong domains, versions, truncation, and extra bytes before
returning a value with its checked re-encoding equation. These formats are
experimental; they do not allocate a new production Ixon Claim/proof tag or
change `Claim.eval` semantics.

Existing commitment domains 0–4 are unchanged. Domain 5 is the public-result
digest: BLAKE3 of `"IxBy/commit/v0" || 00 || 05 || P || B || O`. The existing
full statement digest uses domain 4 and all four components. A circuit can
represent a digest by two injective 128-bit limbs; digest binding itself still
requires a computational security argument.

The 104-byte statement is a diagnostic/transport encoding, not a requirement
to append it to the final compact proof. The application reconstructs it from
its public C and approved configuration. The target remains at most 1,024
proof-specific bytes, separately reporting public C and reusable key/setup.
The imported FFLONK body is 992 bytes; its historical root sidecar is not gone.

## Setup and upgrade independence

`FlockBackend.ExecCompiler.compileExecProfile` has only an `ExecSetupInput`:
the semantic profile, physical capacity, registered primitive implementations,
Flock protocol identity, and backend implementation identity. No guest image,
Stage 2 key/AIR, proof, or execution trace is accepted. The primitive registry
uses existing IxBy opcodes, not a `verifyStage2` oracle. Admission checks reject
unsupported/duplicate opcodes, invalid profiles, and undersized capacities.

The fixed public template distinguishes fixed F128 words from the low/high
limbs of the complete Exec digest and requires exactly one slot for each limb.
Terminal setup consumes that compiled generic verifier artifact plus terminal
protocol, implementation, and SRS identities. These are typed interfaces;
the native compilers and their constraint soundness are still to be supplied.

The native interpreter work now has constrained bounded-bank access, full
fixed-capacity BLAKE3, and the exact four-component/final-digest byte-commitment
chain. Different reads and private byte lengths have real Flock conformance
proofs under fixed setups. The byte-binding component also verifies in fresh
processes from only an externally expected digest and proof. The hash schedule,
all length/padding/flag checks, and commitment dependencies are constrained;
the verifier does not run a host hash/execution oracle on private artifacts.
These are components only: canonical image/input decoding and whole-image
admission, instruction/frame/control transitions, exact fuel/halting,
execution-derived output serialization, and the complete constraint-to-
`Codec.Evaluates` theorem remain unfinished. A matching hash of arbitrary
bytes does not establish those missing properties. See the
[native hash/commitment construction](IxbyFlockHash.md).

Application policy must pin the exact source declaration closure/version,
compiler configuration, ABI, semantic profile, image bytes, and execution-
reflection certificate. Approving a guest is separate from compiling the
backend: changing a Stage 2 guest within the same capacity/primitive class must
not change either backend key. Ordinary capacity/protocol changes do require
an explicitly approved backend upgrade.

## The theorem chain and remaining obligations

```text
value-level ExecutionRefinement + ABICorrespondence
                     ↓ byte_refinement_of_value_refinement
              ByteExecutionRefinement
                     ↓
terminal acceptance → PublicExec → source result OR observed hash collision
       ↑                 ↑
CompressionSoundness   ExecSoundness
```

`ABICorrespondence` identifies the actual decoded program, recovers the source
input from every admitted successful byte run, and relates value/byte result
decoding. `Codec.evaluates_execution` connects the byte proposition to the
checked run and original reference semantics. Forward simulation alone is not
substituted for reflection.

`CompressionSoundness` requires the complete Flock verification relation,
including matrix/structure/jagged root discharge. The root-conditional imported
relation cannot establish this premise. `ExecSoundness` requires the generic
machine constraints plus primitive/memory and Flock soundness obligations;
an untrusted trace generator or host execution check cannot establish it.

`terminal_source_or_collision` composes these exact objects. Its collision
alternative names unequal actual/expected program or output hash preimages
with equal digests. There is no axiom of global finite-hash injectivity.
Computational collision resistance, the backend cryptographic/setup security,
and source Stage 2 protocol correctness/soundness remain explicit obligations.
No executable acceptance bit or unrelated certificate discharges them.

The optional pure `Ix.Ixby.Claim.Stage2` specialization now uses the actual
`claimBytesWrapper` as its source computation. Its
`terminal_verified_claim_or_collision` theorem reaches successful pure Stage 2
verification for the externally expected canonical C, or the same concrete
hash-collision alternative. It retains all compiler, generic Exec, and complete
terminal-root/compression premises; it does not turn them into implementations
or assert cryptographic Ixon validity. This optional import does not couple
the generic IxBy core to a particular Stage 2 verifier.
Its `terminal_protocol_claim_or_collision` corollary now uses the canonical
codec, claim-adapter, and full source refinement to reach the independent
`Stage2ProtocolAcceptsBytes` relation for that same externally expected C.
All compiler/backend/security premises remain explicit.

## Regression commands

```sh
lake test --wfail -- ixby-claim ixby-flock-contract ixby-codec
lake build --wfail Ix.Ixby.Audit Tests.Ixby.Audit
cargo test --release --locked --manifest-path flock-stage4/Cargo.toml --workspace
```

The ordinary Lean suites defer fixture work until selection. They cover golden
wire vectors, every truncated prefix, wrong domains/versions/guest/profile/C,
conditional claims, malformed roots, public-template admission, and a forged
`Bool.true` output under the same guest image. The exact theorem audit includes
the new byte and composition roots without new nonstandard axiom allowances.
