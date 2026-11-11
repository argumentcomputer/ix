# Sort-polymorphic code at `Sort 0`

[`SortPoly.lean`](../../../IxCCTests/Fixtures/SortPoly.lean) (the Lake module
`IxCCTests.Fixtures.SortPoly`) holds `Nat → Nat` roots that instantiate sort-polymorphic
code at `Sort 0`: the regression for level-exact relevance (D18, research
note `relevance-checker.md` §2.4). `sortpoly.ixe` is the anonymous v4
closure of those roots and `sortpoly.equations.json` names them by address
(an `ixcc/k1-equations/1` sidecar with no equations), from `lake exe
pin-src-tables --sortpoly fixtures/ixon-v4/src-sortpoly` with the ix of this
repository (role-bound); `sortpoly.provenance.json` records its version, the commands
and the file hashes.

| Root | What it exercises | At 3 |
| --- | --- | --- |
| `comp` | `Function.comp` at `β := True`: `g x : β` is a proof at `v = 0` | 8 |
| `throughRoot` | the same shape through a local `through` | 6 |
| `punitCases` | `PUnit.casesOn` at `u = 0`: a subsingleton eliminator | 6 |
| `punitCasesType` | `PUnit.casesOn` at `u = 1`: an ordinary one | 7 |
| `punitRec` | `PUnit.rec` at `u = 0` (`noncomputable`) | 8 |
| `unitBoth` | `unitCase` reached at `u = 0` and `u = 1` | 8 |
| `sigmaRoot` | `PSigma` with a proof first field (`u = 0`) | 8 |
| `typeArg` | a *type* in a relevant position of `through` (`β := Type`) | 10 |

Without level-exact relevance, SrcEval is stuck on `comp`, `throughRoot`,
`unitBoth` and `typeArg`, and the relevance checker rejects `punitCases`
and `punitRec` (C4). Level-exact relevance fixes all but `typeArg`: a type
flowing into a relevant position is not a universe condition, so the
checker rejects it (C2, an exact equality) and, run unchecked, it stays
stuck until a shape typing (SRC-10) or □ absorption covers it. `tests-src`
runs every other root against the same source compiled natively (the
test module `IxCCTests.Fixtures.SortPoly`), and `tests-relevance` classifies the
runs in its stuck-cause census.
