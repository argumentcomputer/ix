# Certificate-depth input

The input of `tests-cert-text`'s depth part (the producer's read-back, 2026-11-12). `Deep.lean`
writes, with a macro, two chains of `Bool.casesOn (Nat.blt k s)` tests on `s`, thresholds `0, 1, …`,
whose leaves drop `s` and a second parameter: `deep240` with 240 tests and `deep168` with 168. The
canonical plain-RC ownership code nests one binding and one `case` (two levels) per test and one
more level for the chain, so a plain-RC certificate nests 3n + 6 deep: 726 for `deep240`, past the
512 that the certificate text allows (`Src.Hints.maxJsonDepth`), and 510 for `deep168`, within it.
The zero-RC certificate nests 8 deep for both. Each root returns its chain's result paired with its
argument, so that the program allocates and the automatic policy selects plain RC; so
`ixcc compile --rc on` declines `deep240` with `cert: cert.parse: JSON nesting depth 726 exceeds
maximum 512` and writes nothing, and `--rc auto` compiles it under the immortal policy, naming that
reason. The source stays within the consumer's expression depth (256). `main` checks both roots
against an independent formula in Lean's interpreter.

The closure and sidecar are written by the ix of this repository (role-bound) with the
commands `provenance.json` records, by `lake exe refreeze-ixon rc-deep --ix IX --ix-path
FAKE` ([`docs/corpus.md`](../../../docs/corpus.md), "Refreezing"), which also rewrites
`manifest.sha256`.
