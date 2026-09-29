# K1 scalar programs with unfolding equations

[`K1.lean`](K1.lean) holds the first-rung scalar programs of the benchmark
ladder, written as ordinary Lean 4.34 (`fib`, a `for` loop, Ackermann, `tak`
with fuel, and `gcd` by well-founded recursion).

`k1.ixe` is the anonymous Ixon v3 closure of the five roots, produced by an ix
change that implements request R1/R5 of the x86 plan: `ix compile --equations`.
That change:
- realizes the kernel-checked unfolding theorem `f.eq_def` of every recursive
  definition in the closure, including library definitions such as
  `List.map`, `Nat.add` and `Std.Legacy.Range.forIn'.loop`;
- adds each theorem and its dependencies to the closure until nothing new
  appears.

The closure has 1,651 constants and 40 equations, with no realization
failures.

[`equations.json`](equations.json) lists the five roots and each
`(definition, equation)` pair by name and content address. The names are
diagnostic only, and the addresses are authoritative. They were resolved with
`ix addr-of` against the named variant of the same closure. That variant is
not retained; its SHA-256 is in the provenance.

[`provenance.json`](provenance.json) records:
- the ix revision (a local change on top of the pinned `0a31c8db`);
- the binary hash;
- the exact commands;
- the file hashes.

The required `tests-ixon-v3` suite decodes `k1.ixe` through strict v3
ingress, checks that every recorded root, definition and equation address is
present, and runs erased typing over the whole closure.
