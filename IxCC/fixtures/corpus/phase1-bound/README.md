# The role-bound corpus

The `phase1-bound` family of the [fixture corpora](../../../docs/corpus.md): five
programs of the [`phase1-scalar`](../phase1-scalar/README.md) family, compiled
from the same sources by the same commands with this repository's `ix`, in the
role-bound envelope (`0xE5`) that `ix compile` writes by default: the closure,
the role support, the certificates and the role binding
([byte contract](../../../docs/byte-contract.md)). It is a required family:
`corpus check` and `tests-corpus` read these closures as they read the unbound
ones, with the pinned identities taken from each closure's role table, and the
cases and expected declines are those of the unbound twins.

| Closure | Source (in `phase1-scalar/src`) | Roots |
| --- | --- | ---: |
| `strictAndOr` | `lean-compile/StrictAndOr.lean` | 2 |
| `tuple` | `lean-compile/Tuple.lean` | 1 |
| `bigctor` | `lean-compile/BigCtor.lean` | 1 |
| `typeFormerPolymorphism` | `lean-compile/TypeFormerPolymorphism.lean` | 1 |
| `natShiftr` | `lean-compile/NatShiftr.lean` | 1 |

The sources, their licences and origins are `phase1-scalar`'s
([`corpus.json`](corpus.json) points its `source_root` there). Every closure
here is admitted whole by `ix check-lean`, which issues its host statement.

`phase1-scalar`'s `scalar` closure is not here: in the role-bound form it is
2.5 MB, and its census, which types it with IxCC's erased checker, takes about
200 s, which would double the time of `corpus check`. It passes `corpus check`
and `tests-corpus` in that form with the unbound family's results (a manual
run, recorded in the change record of the [CI guide](../../../docs/ci.md)); it
can join when typing no longer runs through the erased checker.

## Regenerating

With this repository's `ix` built (`lake build ix` at the repository root),
set the manifest's `producer` fields (`ix_revision`, `ix_binary_sha256`,
`ix_version`, `ix_build`) to that `ix`, then, with the `lake` stand-in of
[Refreezing](../../../docs/corpus.md#refreezing) in the directory `FAKE`, from
`IxCC/`:

```sh
lake exe corpus rebuild fixtures/corpus/phase1-bound/corpus.json \
  --ix ../.lake/build/bin/ix --ix-path FAKE --work WORK
```

The closures here were written by an `ix` whose role selection binds every
role whose constant the artifact holds; the five tables bind 34 to 50 roles.
