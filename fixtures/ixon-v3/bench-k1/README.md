# K1 benchmark closures with unfolding equations

The Phase 1 compiler input: for each K1 benchmark fixture, the anonymous
Ixon v3 closure of its pure `entry` function
([`benchmarks/fixtures/<name>/`](../../../benchmarks/fixtures/README.md)),
with the kernel-checked unfolding theorem `f.eq_def` of every recursive
definition in the closure. The Compilatrix and `lean-clang` benchmark rows
compile the same Lean source.

| Fixture | Entry | Constants | Equations | Bytes |
| --- | --- | ---: | ---: | ---: |
| `fib` | `Nat → Nat` | 55 | 2 | 15,634 |
| `sum-loop` | `Nat → Nat` | 1,540 | 34 | 1,138,673 |
| `ackermann` | `Nat → Nat → Nat` | 1,405 | 34 | 992,719 |
| `tak` | `Nat → Nat → Nat → Nat → Nat` | 149 | 5 | 52,623 |
| `gcd` | `Nat → Nat → Nat` | 265 | 7 | 119,929 |

Files per fixture:
- `<name>.ixe`: the closure, from `ix compile --consts entry --equations
  --anon`, with ix at the local `jcb/compile-equations` change `9c4b9c65`, as
  for the [`k1`](../k1/README.md) pack;
- `<name>.equations.json` (`compilatrix/k1-equations/1`): the root and each
  `(definition, equation)` pair by name and content address. Names are
  diagnostic only; addresses are authoritative, resolved with `ix addr-of`
  against the named twin of the same closure (not retained; its SHA-256 is in
  the provenance);
- `<name>.census.json`: the reviewed admission census. Every constant of
  every closure passes decoding, erased typing and the D12 policy stage.

[`provenance.json`](provenance.json) records the producer revision and binary
hash, the commands, and every file hash. The closures are reproducible: a
second build gave byte-identical files.

**Gates.** `tests-ixon-v3` decodes each closure through strict v3 ingress,
checks that every recorded address is present and the equation count is
unchanged, and runs erased typing over the whole closure. The `census` check
requires the tool to reproduce each census file exactly.

## Primitive and special-form membership

Closure membership of the pinned
[`primitives.tsv`](../primitives.tsv) constants is an upper bound on what
runs. The large closures come from the well-founded termination proofs of
`sum-loop` and `ackermann` (`omega` pulls in `Int`, `String`, `BitVec` and
the `Nat` bitwise operations); those sit in irrelevant positions and are
erased. The exact runtime set is what `Src.Admit` reaches from each root
(phase 1, M1.F1); this table is its starting point.

| Fixture | Nat primitives in the closure | Other pinned constants |
| --- | --- | --- |
| `fib` | `add` | `Nat.rec`, `Nat.casesOn`, `PProd`, `OfNat.ofNat`, `eagerReduce` |
| `tak` | `add`, `pred`, `sub`, `beq`, `ble` | `Nat.decLe`, `Nat.decLt`, `Decidable.rec`, `Bool` |
| `gcd` | `add`, `pred`, `sub`, `mod`, `beq`, `ble` | as `tak`, plus `Nat.decEq`, `Quot`, `Quot.lift` |
| `sum-loop` | `add`, `pred`, `sub`, `mul`, `pow`, `gcd`, `mod`, `div`, `bitwise`, `beq`, `ble`, `land`, `shiftRight` | as `gcd`, plus `Int`, `String`, `Char`, `List`, `Fin`, `BitVec` (proof terms) |
| `ackermann` | as `sum-loop` | as `sum-loop`, plus `SizeOf.sizeOf` |

**Expected runtime set** (design note 02 §9, to be confirmed by `Src.Admit`):
`Nat.add`, `Nat.sub`, `Nat.beq`, `Nat.ble` (through `Nat.decEq`/`decLt`/
`decLe`), and `Nat.mod` (`gcd`); `Nat.casesOn` and literal peeling of
`Nat.rec`; the `lazy` constants `ite`/`dite`; no allocation after
inlining and specialisation.
