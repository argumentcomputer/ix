# Proofs the kernel checks quickly only with the artifact's hints

[`KernelHints.lean`](KernelHints.lean) holds a root (`KernelHints.root`) and, as seeds the sidecar
does not name, proofs the certified kernel checks in a millisecond with the artifact's reducibility
hints and in time exponential in a literal's bit length without them:

| Seed | What it is |
| --- | --- |
| `allOnesXor` | the minimal reproducer, `(BitVec.allOnes 16 ^^^ y).toNat = Nat.xor 65535 y.toNat := rfl` |
| `complement16`, `complement32`, `complement64` | the `complement` word equations as `ix compile --equations` states and proves them |
| `ping`, `pong` | a mutual pair of `partial` definitions: Lean's compiler writes their bodies as one block of `unsafe` definitions, whose members' hints the artifact records under their projection records |

`hints.ixe` is the anonymous role-bound closure, `hints.equations.json` its `ixcc/k1-equations/1`
sidecar (the root only, no equations), from `lake exe pin-src-tables --kernel-hints
fixtures/ixon-v4/kernel-hints` with the ix of this repository; `hints.provenance.json` records its
version, the commands and the file hashes.

`tests-kernel-front` (`IxCCTests/KernelFront/Hints.lean`) accepts it within a bound with its hints,
reads its hint table a second way, and runs it with hostile and missing hints through the front
end. Measurements and the cause: `IxCC/plans/aiur-backend/KERNEL-NOTES.md`, section 10 (a local
working file).
