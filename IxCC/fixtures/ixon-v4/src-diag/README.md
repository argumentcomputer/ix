# Src admission diagnostics

`Diag.lean` has one root per expected `Src.Admit` outcome (design note 01
§10, part 5). `sorry.ixe` is the anonymous v4 closure of `rootSorry` alone
(the certified kernel declines a whole artifact that uses `sorryAx`, so that
root cannot share one with roots expected to be admitted or refused for
other reasons) and `diag.ixe` of the other five; `STEM.equations.json` names
the roots by address (an `ixcc/k1-equations/1` sidecar with no equations).
Both come from `lake exe pin-src-tables --diagnostics fixtures/ixon-v4/src-diag`
with the ix of this repository (role-bound); `STEM.provenance.json` records its
version, the commands and the file hashes.

| Root | Expected |
| --- | --- |
| `rootPartial` (a `partial def`) | `opaque` |
| `rootMixHash` (`@[extern] opaque mixHash`) | `opaque` |
| `rootFloat` (`Float.add` is a modelled `@[extern] def` in Lean 4.34) | admitted |
| `rootClassical` (`Classical.propDecidable` in a relevant `if`) | `relevant-axiom` |
| `rootSorry` (`sorryAx`) | `relevant-axiom` |
| `rootOpaqueId` (`Lean.opaqueId`) | admitted; `41 ↦ 42` |

`tests-src` loads each root alone and checks its outcome.
