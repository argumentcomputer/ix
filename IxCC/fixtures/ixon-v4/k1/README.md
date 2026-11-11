# K1 scalar programs with unfolding equations

[`K1.lean`](../../../IxCCTests/Fixtures/K1.lean) (the Lake module `IxCCTests.Fixtures.K1`,
this manifest's `source_root`) holds the first-rung scalar programs of the benchmark
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

The manifest records the closure's size and equation count (they change with
every regeneration); there are no realization failures.

[`equations.json`](equations.json) lists the five roots and each
`(definition, equation)` pair by name and content address. The names are
diagnostic only, and the addresses are authoritative. They were resolved with
`ix addr-of` against the named variant of the same closure. That variant is
not retained; its SHA-256 is in the manifest.

[`corpus.json`](corpus.json) is the pack's manifest (`ixcc/corpus/1`,
[`docs/corpus.md`](../../../docs/corpus.md)): the source, the producer (the ix of this
repository, its version) and commands, every file hash and the roots'
addresses. The roots have no cases there (the stage suites run them).
`lake exe corpus rebuild fixtures/ixon-v4/k1/corpus.json --ix IX --ix-path DIR`
remakes the pack and `lake exe corpus check fixtures/ixon-v4/k1/corpus.json`
verifies it offline.

The required `tests-ixon-v3` suite decodes `k1.ixe` through strict v4
ingress, checks that every recorded root, definition and equation address is
present, and runs erased typing over the whole closure.

[`census.json`](census.json) is the reviewed admission census of `k1.ixe`
(`lake exe census k1.ixe --names equations.json`): every anonymous constant
passes decoding and erased typing; the D12 policy stage refuses the `partial`
and `unsafe` members of the logical units the selection brings in, which no
root reaches. It records the budget headroom. The `census`
check requires the tool to reproduce this file exactly.
