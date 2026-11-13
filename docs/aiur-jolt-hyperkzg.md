# Jolt and HyperKZG ideas for Aiur

The most useful Jolt idea for Aiur is reducing the amount of witness data that
needs a separate commitment. HyperKZG is one possible backend for that
approach; several useful optimizations can be adopted independently.

This note distinguishes implementation and compiler improvements suitable for
the initial Aiur compression pipeline from possible future proof backends.
The initial implementation retains the existing KZG and PLONK protocols and
the Ignition-backed PLONK endpoint described in [the compression design](aiur-compression.md).

## 1. Avoid committing every intermediate value

Jolt uses *virtual polynomials*: derived witness values whose evaluations are
established through other proof checks instead of receiving their own
commitments. Sumcheck connects those derived values to the committed inputs.
See [Jolt's architecture](https://jolt.a16zcrypto.com/how/architecture/architecture.html).

For Aiur, the immediate lesson is to eliminate unnecessary intermediate columns,
fuse arithmetic, and share physical traces. That directly addresses the
thousands of column commitments in the current lowering. The fused curve
arithmetic follows this direction already. Adopting Jolt's full sumcheck
machinery would be a larger backend change.

Aiur already preserves field addition, subtraction and multiplication as
expressions in [its circuit compiler](../Aiur/Aiur/Circuit/Compile.lean).
It does not allocate a new witness column for every arithmetic operation.
Calls, hints, division inverses, memory operations and branch results can
introduce columns. Further gains must address those actual sources of width;
generic arithmetic expression elimination is already part of the baseline.

Eliminating a commitment still requires enforcing the value's defining
relation. Compiler substitution must respect the existing constraint-degree
budget and every use of the value; Jolt's sumcheck-based virtualization is
another way to establish such relations, not permission to omit them.

## 2. Preserve small and sparse values

Many witness values are bits, bytes, small indices, or zeros. Jolt exploits
these representations rather than treating every value as an arbitrary large
field element. Its commitment implementation also specializes operations for
small and sparse scalars. See [Jolt's implementation discussion](https://jolt.a16zcrypto.com/how/dory.html).

For Aiur, compact trace storage and avoiding unnecessary expansion into
32-byte BN254 values could reduce memory traffic. The current KZG path
transforms evaluations into polynomial coefficients, which generally become
full-sized field elements. Small input values therefore do not automatically
make its commitment MSM cheaper. Compact storage, streaming, and commitment
arithmetic need separate measurements.

An alternative within the existing KZG protocol is to commit row values using
a precomputed Lagrange-basis SRS for their domain. If the row values are `v_j`
and their interpolation polynomial has coefficients `c_i`, the two MSMs
`sum_j v_j [L_j(tau)]G` and `sum_i c_i [tau^i]G` produce the same commitment.
This preserves transcript and proof bytes while exposing small row values
and padding zeros to specialized MSM algorithms. Coefficients are still needed
for quotient and opening work. Basis preparation, cache storage per domain,
and CPU/GPU MSM costs need measurement before adoption.

## 3. HyperKZG opens a large table through repeated folding

View a table's index as a string of bits. At each step, combine adjacent
entries using a challenge:

```text
[a, b, c, d]
→ [a + r(b − a), c + r(d − c)]
→ one value after another fold
```

HyperKZG uses KZG commitments and opening checks to authenticate this
logarithmic chain of folds. That lets a sumcheck-based proof system open
multilinear tables using ordinary powers-of-tau material. A BN254
implementation can use appropriately authenticated Ignition powers within
their capacity. See the pinned [HyperKZG implementation and setup contract](https://github.com/a16z/jolt/blob/0549ca3469b7656f7c371c3341d1da1c7b3f41f7/crates/jolt-hyperkzg/README.md).

For Aiur, this could support a backend organized around a few large witness
tables. Switching to HyperKZG while retaining thousands of separately
committed columns would retain that commitment-count problem. Getting the
benefit requires changing how the compiler and proof system represent and
check the witness. Larger combined tables also consume more SRS capacity.

Reusing the same ceremony does not make this a protocol-preserving backend
substitution: table layout, reduction arguments, transcript binding, and
degree assumptions must agree between prover and verifier. The final PLONK
endpoint could remain while its Aiur program verifies the new intermediate
proof format.

## 4. Distinguish batched openings from fewer commitments

Many evaluation claims can be reduced to one opening proof. The verifier still
has to process the original commitments when combining them. See [Jolt's
batching explanation](https://jolt.a16zcrypto.com/how/optimizations/batched-openings.html).

Aiur's current KZG backend already batches openings and combines their pairing
equations. Additional opening batching alone would not eliminate the expensive
curve operations over thousands of commitments. The number of commitments,
the number of opening witnesses, and the cost of their verification are
separate measurements.

## 5. Consider lookup and memory arguments separately

Shout handles table reads; Twist extends the approach to mutable memory. They
exploit sparse address representations and sumcheck to avoid materializing or
committing some derived data. See [Twist and Shout](https://jolt.a16zcrypto.com/how/twist-shout.html).

These ideas are relevant to Aiur's range checks, byte operations, and memory
traffic, but replacing the existing lookup argument would be a substantial
cryptographic backend project. Aiur can improve its current lookup tables and
trace population without adopting those arguments.

## Initial implementation priorities

The KZG adapter can group existing LogUp lookups using the same quotient-degree
criterion as the Goldilocks backend: examine group sizes up to eight and retain
only those that preserve each circuit's actual quotient degree. Goldilocks
chooses the largest eligible group; KZG minimizes auxiliary width and uses the
smallest group on ties. The global quotient allowance
is insufficient for that test. A circuit currently using quotient degree one
would incur a larger FFT if grouping raised it to two. Group feasibility can
also be nonmonotonic, so every candidate size must be checked.

Streaming lookup and quotient construction are already enabled by the shared
Aiur KZG capacity configuration. Further memory work includes compact witness
representations and avoiding duplicate logical and physical trace matrices.

Prioritize measured lookup grouping and better trace layouts, then evaluate
Lagrange-basis commitments and compact storage. Use matched inputs including
the actual Init workload, measuring padded cells, commitments, proving
resources, and recursive verification cost separately.

HyperKZG with sumcheck and the Twist/Shout arguments are candidates for a
separate backend investigation. They are not prerequisites for finishing the
initial pipeline with the existing KZG protocol and Ignition-backed PLONK.

## Source version

The Jolt research clone was refreshed on 2026-11-12 to upstream commit
`0549ca3469b7656f7c371c3341d1da1c7b3f41f7`. At that revision, Jolt documents
Dory and Akita as its main backends. Its standalone HyperKZG crate states that
it is exercised in tests rather than linked into production. The broader
Jolt architecture ideas and that particular HyperKZG implementation should
therefore be evaluated separately.
