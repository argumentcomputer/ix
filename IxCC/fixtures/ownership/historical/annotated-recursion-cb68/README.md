# Historical genuine annotated recursion consumer regression

These are genuine historical producer outputs for OS04 `len`/`entry`, not
synthetic declaration mutations and not the final refreshed ownership corpus.
`Annotated.lean` writes the erased type binder; `Plain.lean` is its prepared
stripped twin. Both source interpreters returned Nat3 at inputs0,1,2,5,10,20.
The independent literal Nat3 expectation is preserved in the test.

Producer revision: `cb68d94c42b059a5088050a7ad64b4204a0bf562`.
Producer binary SHA256:
`d96956f18c318679b0f1c45136bdd4a1f32ed5f46a967ca63a46682319f6dc93`.
Lean toolchain:4.34.1, exact original reference/producer command receipts are
included. The copied original lean-core.profile is pinned at SHA256
`860120c0265e5d61444efdef55bbd3fe6c8596b889047d94d7160ba4d5d78aec`.
Its original100000-step/depth256 settings are unchanged. The effective
annotated profile address is
`5e387038c267c42212fa9c62ddbac9d062eb3354f79ade3fb57ee9a3ddac09b9`.
Complete historical artifact-inventory SHA256:
`2f2d9533b882a38b29990a51209ccce19b93bfe096c4ae504ed601717d4668e7`.
Complete copied-library-inventory SHA256:
`d2f11cef853e7fc920ae4d6667cfe63d8f2850decb0c75d1ca4b3bfd3a709c3d`.
Receipts retain original absolute paths as provenance; CI does not execute
those paths or require the historical producer/library snapshot.

Annotated source/bytes were genuinely re-exported and checked on2026-10-09
at01:23UTC; the plain twin at01:36UTC. Named and anonymous equation sidecars
are identical, actual entry/definition/equation addresses were recovered from
the named bytes, and the annotated producer check-equations receipt verified
the genuine recursive len pair. Inputs are content-address authenticated by
the decoder, and every committed file is bound by inputs.sha256, whose digest
is independently fixed in the focused test module.

The annotated test runs actual Src, Fir and production checked Own.immortal:
six complete Nat3 observations each. Its actual Fir retains an erased slot
and `[erased,many]` contracts for len. Plain-RC admission therefore explicitly
refuses; this refusal is independently required. The stripped plain twin
runs Src, Fir and checked Own.Plain, six complete Nat3 observations each.
The test preserves five structural binding refusals and six controls for the
historical local no-profile/absent-or-empty-list adapter. Current corpus
paired-key rules are unchanged. No resource claim exists on the plain twin.

This closes a concrete historical consumer regression, not the strengthened
producer's G1 budget problem or the final lean-core-plain family refreeze.
Immortal results do not establish RC recycling or satisfy H4's real reverse
heap requirement. There are no new trusted operations or proof assumptions.
