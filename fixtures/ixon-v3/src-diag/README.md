# Src admission diagnostics

`Diag.lean` has one root per expected `Src.Admit` outcome (design note 01
§10, part 5). `diag.ixe` is the anonymous v3 closure of those roots and
`diag.equations.json` names them by address (a `compilatrix/k1-equations/1`
sidecar with no equations), from `lake exe pin-src-tables --diagnostics
fixtures/ixon-v3/src-diag` with ix `9c4b9c65`; `provenance.json` records the
binary, commands and file hashes.

| Root | Expected |
| --- | --- |
| `rootPartial` (a `partial def`) | `opaque` |
| `rootMixHash` (`@[extern] opaque mixHash`) | `opaque` |
| `rootFloat` (`Float.add` is a modelled `@[extern] def` in Lean 4.34) | admitted |
| `rootClassical` (`Classical.propDecidable` in a relevant `if`) | `relevant-axiom` |
| `rootSorry` (`sorryAx`) | `relevant-axiom` |
| `rootOpaqueId` (`Lean.opaqueId`) | admitted; `41 ↦ 42` |

`tests-src` loads each root alone and checks its outcome.
