# Role-bound closures

Two closures in the role-bound envelope (`0xE5`) that this repository's
`ix compile` writes by default: the closure, the role support, the
certificates and the role binding ([byte contract](../../../docs/byte-contract.md)).
Every other committed closure is unbound (`0xE4`, `ix compile --unbound`).

| Closure | Source | Root | Sidecar |
| --- | --- | --- | --- |
| `tuple.ixe` | `fixtures/corpus/phase1-scalar/src/lean-compile/Tuple.lean` | `entry` | `tuple.equations.json` |
| `fib.ixe` | `benchmarks/fixtures/fib/Fib.lean` | `entry` | `fib.equations.json` |

`tests-ixon-v3` reads them (`IxCCTests/IxonV3/Binding.lean`): each binding
authenticates and decodes; every identity that both the role table and the
fixed table pin is pinned at the same address, and where the table binds no
role the fixed table's constant is absent from the closure; ingress reads each
program with the role table's pins, and its pinned identities resolve to the
constants the fixed table's would.

## Regenerating them

They are the `tuple` and `fib` closures of the `phase1-scalar` and `bench-k1`
families regenerated with the manifests' own commands without `--unbound`.
With this repository's `ix` built (`lake build ix` at the repository root) and
the `lake` stand-in of [Refreezing](../../../docs/corpus.md#refreezing) on
`PATH` (it answers `lake env printenv LEAN_PATH` with the root workspace's
libraries), from `IxCC/`:

```sh
IX=$PWD/../.lake/build/bin/ix
(cd fixtures/corpus/phase1-scalar/src && $IX compile --no-build --consts entry --equations --anon \
  --out ../../../ixon-v4/bound/tuple.ixe --equations-out /tmp/tuple.ix-equations.json lean-compile/Tuple.lean)
(cd benchmarks/fixtures && $IX compile --no-build --consts entry --equations --anon \
  --out ../../fixtures/ixon-v4/bound/fib.ixe --equations-out /tmp/fib.ix-equations.json fib/Fib.lean)
```

The sidecars (`ixcc/k1-equations/1`) name the root and the equations by
address, as `corpus rebuild` writes them from a named twin (`ix compile`
without `--anon`, then `ix addr-of --ixe NAMED NAME`); the root and equation
addresses are those of the unbound closures of the same sources, since the
role-bound closure keeps every constant of the unbound one at its address.
`corpus rebuild` on a copy of the family's manifest whose commands lack
`--unbound` writes both files.
