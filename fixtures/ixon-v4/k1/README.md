# K1 scalar programs with unfolding equations

[`K1.lean`](K1.lean) holds the first-rung scalar programs of the benchmark
ladder, written as ordinary Lean 4.34 (`fib`, a `for` loop, Ackermann, `tak`
with fuel, and `gcd` by well-founded recursion).

`k1.ixe` is the anonymous Ixon v4 closure of the five roots, produced by an ix
change that implements request R1/R5 of the x86 plan: `ix compile --equations`.
That change:
- realizes the kernel-checked unfolding theorem `f.eq_def` of every recursive
  definition in the closure, including library definitions such as
  `List.map`, `Nat.add` and `Std.Legacy.Range.forIn'.loop`;
- adds each theorem and its dependencies to the closure until nothing new
  appears.

The closure has 1,596 anonymous constants (1,651 named) and 40 equations,
with no realization failures.

[`equations.json`](equations.json) lists the five roots and each
`(definition, equation)` pair by name and content address. The names are
diagnostic only, and the addresses are authoritative. They were resolved with
`ix addr-of` against the named variant of the same closure. That variant is
not retained; its SHA-256 is in the manifest.

[`corpus.json`](corpus.json) is the pack's manifest (`compilatrix/corpus/1`,
[`docs/corpus.md`](../../../docs/corpus.md)): the source, the ix revision
(`be45a159`: the certified line `f829b760` plus the local `--equations`
export), binary hash and commands, every file hash and the roots'
addresses. The roots have no cases there (the stage suites run them).
`lake exe corpus rebuild fixtures/ixon-v4/k1/corpus.json --ix IX --ix-path DIR`
remakes the pack and `lake exe corpus check fixtures/ixon-v4/k1/corpus.json`
verifies it offline.

The required `tests-ixon-v3` suite decodes `k1.ixe` through strict v4
ingress, checks that every recorded root, definition and equation address is
present, and runs erased typing over the whole closure.

[`census.json`](census.json) is the reviewed admission census of `k1.ixe`
(`lake exe census k1.ixe --names equations.json`). Every one of the 1,596
anonymous constants passes decoding, erased typing and the D12 policy stage.
Budget headroom: 1.08 MB of 16 MiB, 1,596 of 16,384 table entries, 1,596 of
4,096 typing declarations, and expression depth 66 of 256. The `census`
check requires the tool to reproduce this file exactly.
