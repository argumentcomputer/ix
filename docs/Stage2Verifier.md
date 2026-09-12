# Pure Stage 2 verifier components

Status: the complete pure deterministic protocol checker and claim-bound
source wrapper are implemented, including canonical codecs, key/shape
admission, transcript/PoW, AIR/logUp/OOD, Merkle multiproofs, and PCS/FRI.
Independent protocol refinement/completeness proofs, certified compilation,
and generic Flock/terminal execution are still unfinished. Executable
verification is not, by itself, a certification or cryptographic soundness proof.

## Protocol and import boundary

`Ix.MultiStark.Verify` is a pure Lean umbrella. It imports neither the native
verifier nor the Aiur DSL. Native functions are used only by the separately
selected differential tests. The implementation targets the PR's pinned
multi-stark `9a906122` / Plonky3 `3152b14a` protocol, including sparse activation,
the compiled constraint graph, grouped logUp, and shared Merkle multiproofs.
There is no fallback to the historical per-query advice transport.

`stage2Verify` (in `Verify/Source.lean`, namespace `MultiStark.Verify`) closes over its Stage 2
configuration, derives the exact expected native claim, and verifies using
the same canonical aggregate-key bytes hashed into the allowed identity.
`claimWrapper` and `claimBytesWrapper` return the caller's claim only on success.
The configuration must be fixed by the approved guest/policy; merely passing
an arbitrary private key to these functions does not approve that key or the
aggregate program's claim semantics. See [Exec binding](IxbyExec.md).

## Implemented boundaries

| Component | Checks and output | Does not establish |
| --- | --- | --- |
| `Codec.Proof` | Full current multiproof transport, canonical fields/tags, exact re-encoding | Proof shape or acceptance |
| `Codec.Key` | Dense-v5 native key, all 16 node tags, canonical constant form, exact re-encoding | Graph validity or key approval |
| `Codec.Claims` | Length-prefixed native field-word claims | Their connection to public Ixon C |
| `Claim` | Closed `CheckEnv` bytes, allowed-key identity, exact 18-word aggregate claim | Stage 2 verification or approval policy |
| `Key.Validate` | Topological references, columns, lookup groups/degrees, preprocessing map and parameters | Cryptographic validity or complete PCS geometry |
| `Shape` | Active-indexed dimensions, full preprocessing slots, OOD point/column counts, degree bounds | Correct opened values |
| `Transcript` | Exact parameter seed and observation order through OOD zeta, returned challenger continuation | FRI authentication or cryptographic soundness |
| `Ood` | Claim accumulator, constraint graph, grouped lookup equations, selectors and quotient identity | Authentication of the openings by PCS/FRI |
| `Mmcs` | Verifier-owned widths/indices, exact shared frontier, duplicate/merged-row consistency, all queried cap roots | Collision resistance or low degree |
| `Fri` / `Pcs` | OOD observations, FRI transcript/PoW/queries, input authentication, variable-arity folds/roll-ins, final polynomial, FRI authentication | Cryptographic proximity/soundness bounds |
| `Check` | All typed protocol phases must succeed | Authorization of its supplied native claims/key |
| `Source` | Canonical public C, fixed configuration, pure key/proof decoding, exact derived native statement, claim-returning wrapper | Configuration approval, Ixon truth, certified compilation |

The key codec follows the executable native encoder: circuit records have no
length prefix, and node/zero/lookup counts are u16. Some historical native
module comments describe different framing/count widths. The codec has no
in-band version tag, so its dense-v5 identity must be pinned by the approved
source/guest configuration. Big constants must be canonical Goldilocks values;
a big encoding of a value that fits the small form is rejected.

Default parser limits are 16 MiB of bytes, 1,048,576 elements per vector, and
2,097,152 nested items. Lengths are checked before collection allocation.
Offsets and counts use total natural-number arithmetic, not wrapping machine
arithmetic. These are parser admission limits, not security parameters or
IxBy backend capacities.

Key admission currently covers canonical native-builder preprocessing order
and power-of-two table heights. Every intermediate graph degree must fit u16,
and the advertised maximum must equal the recomputed user/logUp maximum and
fit the PCS blowup. Shape admission pins active preprocessing traces to their
key's height. Completeness must be stated for this explicit supported class,
not every record that an unchecked native decoder could construct.

Transcript field sampling rejects raw u64 words at or above the modulus and
consumes those bytes. The default per-field attempt bound is 64; exhaustion
rejects. Raw bit sampling is different: it never performs field rejection,
and even a zero-bit draw consumes eight bytes. Zero-bit PoW, in contrast,
does not observe or draw. Empty observations are inert.

The binary MMCS implementation supports power-of-two heights through `2^32`.
It authenticates the original same-height matrix order and rejects a cap that
would cut off a shorter matrix's injection layer. That last check is an
explicit restriction beyond the native generic MMCS, preventing acceptance of
unauthenticated shorter rows. Small single-height FRI trees still shorten a
configured cap to their depth. The current pinned native PCS rejects matrices
opened at no points, so inactive preprocessing slots are reconstructed but
remain outside the accepted PCS class.

Default FRI execution limits allow 1,024 queries and fold arity up to 256.
These are resource bounds, not security choices. Folding uses direct Lagrange
interpolation, including the valid case where the challenge equals a row
point. Input quotients reject a query point equal to an opening point. Every
reduced opening must be consumed, with the native `beta^arity` roll-in factor.
Both input and FRI shared multiproofs must consume all frontier hashes.

The typed `Ix.Claim` adapter is an explicit separate `Ix.MultiStark.Stage2`
import. It checks the original claim kind, absence of assumptions, and root
width before serialization. Malformed address lengths can otherwise make a
conditional value's bytes alias a different closed claim. The pure byte
entrypoint separately checks canonical closed-claim framing.

Protocol division rejects zero denominators, including zero extension norms.
It does not inherit the primitive's total `inverse 0 = 0` as an acceptance
rule. LogUp's two coordinates are themselves OOD extension-field values and
remain two separate constraint identities. Raw last-row selectors are
normalized through the accumulator delta, not by changing the selector.

## Current evidence and trust gate

The opt-in differential test generates and natively verifies a real factorial
proof, then checks its exact proof/key/claim codec round trips, key/shape
admission, transcript replay, all AIR/logUp/OOD equations, and the complete
Merkle/PCS/FRI path in pure Lean. It rejects changed public claims, quotient
coefficients, private input rows, FRI siblings/final polynomial, invalid
arities, oversized heights, missing authentication/openings, and singular OOD
points. Its three-query fixture
is a development vector, not a security recommendation. Proof size varies
with the query frontier; it is not a Stage 3/4 compression measurement.

`stage2-wrapper-real` additionally proves the existing test stand-in's native
18-word aggregate layout. It checks the full source wrapper, the public
`Ix.Claim` adapter, and substitutions of both keys, both entrypoints, the
public root, framing, and assumptions. The stand-in does not establish Ixon
truth and is not an approvable production aggregate verifier.

The exact theorem manifest covers 153 public roots, with exact per-root sets of
`propext`, `Quot.sound`, and, where present, `Classical.choice`. The graph sweep
is sound and complete against a separate expression/reference relation.
Observation updates, raw bit draws, grinding, and rejection sampling have
separate relational specifications. The full multi-stark transcript prefix,
from the 14-byte parameter tag through OOD zeta and the PCS continuation
state, now has a soundness-and-completeness equivalence against that relation.
It includes claim lengths, canonical circuit order, both extension
coefficients, and re-observation of the lookup/fingerprint challenges.
PCS opening observations, FRI shape admission, and the complete FRI
Fiat-Shamir sequence also have independent relational equivalences. Separate
corollaries establish the exact query count and every query's domain bound.
All 33 native subgroup-generator table entries are kernel-checked against
powers of the pinned root, including their exact two-adic orders and nonzero
selector normalization constants. Guarded base/extension inversion and
division refine the specified canonical modular arithmetic and reject zero
denominators. These finite and deterministic facts are not a cryptographic
soundness theorem.
The complete OOD checker has a separate soundness-and-completeness relation
covering checked graph references, selectors, grouped two-coordinate logUp,
the initial claim accumulator and circuit-to-circuit balances, and exact
quotient recombination/composition. A valid OOD relation still needs the
independent PCS authentication and low-degree checks.
MMCS geometry, row dimensions, same-height row concatenation, merged-member
row consistency, and canonical query-leaf construction also have independent
relational equivalences. Duplicate queries must agree on every original
matrix row before deduplication. The complete MMCS checker additionally
refines the independent parent-layer/injection/frontier-walk relation and
matches every terminal node to its supplied cap. Both directions require
exact consumption of the full boundary frontier.
FRI bit reversal is proved against positional binary digits and stays within
its requested width. Row folding refines the defining ordered Lagrange
products, including a challenge on the row domain. Input authentication and
quotient reduction have complete phase equivalences: denominators are
checked, alpha powers continue across coordinates/points/matrices/batches at
each height, constant-height quotients vanish, and every present bucket is
returned in descending height order. Nonzero differential vectors pin these
orders and both extension coordinates. The complete FRI checker now has a
soundness-and-completeness equivalence against the separate `FriAccepted`
relation. It composes transcript derivation, input authentication/reduction,
every query fold and roll-in, the final polynomial equation, and all commit
authentications. The row-insertion equation preserves every sibling in order;
saved rows precede roll-in, and the final state consumes every reduction.
Nonzero binary/quaternary chains exercise both extension coordinates,
independently constructed leaf-level caps, and the final subgroup/bit-width
pair. PCS round reconstruction and the full Stage 2 refinement remain unfinished.
Bounded sampling completeness uses the
same attempt budget on both sides. These are phase proofs, not yet a complete
protocol-refinement theorem. The wrapper/composition lemmas establish exact
public-claim binding under the named compiler/Exec/terminal premises.
A source-module scan also checks private/generated theorems and
rejects new axioms. The audit rejects native/DSL imports in the pure umbrella.
These checks do not constitute a complete protocol-refinement theorem.

```sh
lake test --wfail -- stage2-codec stage2-claim stage2-key \
  stage2-transcript stage2-shape stage2-ood stage2-mmcs stage2-fri stage2-source
lake build --wfail Ix.MultiStark.Verify.Audit Tests.MultiStark.Verify.Audit
lake test --wfail -- --ignored stage2-codec-real
lake test --wfail -- --ignored stage2-wrapper-real
```

For a resource-bounded local run, build `IxTests` first, then run the compiled
binary under a process memory/time limit and a CPU affinity supported by the
host. Applying a tight address-space limit to the Lake build launcher can
prevent Lean's worker threads from starting before the test runs.
