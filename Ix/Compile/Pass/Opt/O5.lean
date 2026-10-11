/- # O5: the level rule of O1-O4 (a Prop member that gained large elimination)

## Contract
Input: a recursor shape `s` (`Ix.Compile.Pass.Opt.RecShape`) and the
universe arguments `us` of an occurrence of one of the Lean auxiliaries built
from `s.leanRec` (its `rec`, `recOn`, `casesOn`, `below*`, `brecOn*`, all with
the recursor's universe parameters, checked by `standardTelescope`).
Output: the universe arguments of the Ix auxiliary that replaces the
occurrence (O1-O4), or `none`.

O5 is not a separate pattern (design document §1.4): it is the rule by which
O1-O4 choose the Ix auxiliary's universe arguments, and the rule covers the
Prop case. The arguments are the image's `ℓs` (Def 3.4 step 2) with the
occurrence's levels for Lean's parameters:
* the Ix auxiliary has Lean's universe parameters: `ℓs = us` up to the
  substitution (the identity case);
* a Prop member that gained large elimination: Lean's recursor has no
  elimination universe, the Ix recursor has one, and the image instantiates
  it at `0` (`ρ.{0, us}`); the Ix `casesOn`/`below`/`brecOn` of the class
  take the same extra parameter first, so they are instantiated at `0` too.

## Faithfulness
Definitional. With `ℓ := 0` the Ix motive sort `Sort ℓ` is `Prop`, Lean's
motive sort, so the Ix auxiliary at `0` has the type of Lean's (every other
step of O1-O4 is unchanged); no conversion beyond O1-O4's own is needed.
Any other shape of `ℓs` (an extra parameter that the image does not
instantiate at `0`, a level count that is neither Lean's nor Lean's plus one)
is refused.

## Canonicity
The levels depend on the image's `ℓs` (canonical: the image depends on the
canonical form) and the occurrence's levels only.

## Side condition and fallback
`ℓs.size = |levelParams|`, or `ℓs.size = |levelParams| + 1` with `ℓs[0] = 0`.
Otherwise `none`: the pass that asked declines and the baseline stays.

## Non-canonical set and evidence
None. Library load 0 (census: no Prop member gains large elimination in
Init+Std, Lean, Batteries or Mathlib). Fixture:
`Tests/Ix/Compile/Pass/O5PropSplit.lean` (a Prop pair split into two
components, each gaining large elimination).
-/
module
public import Ix.Compile.Pass.Opt.Core
public section

namespace Ix.Compile.Pass.Opt

open Ix (Level)

/-- The universe arguments of the Ix auxiliary at an occurrence with levels
`us` (O5's rule), or `none`. -/
def O5.levels (s : RecShape) (us : Array Level) : Option (Array Level) :=
  if s.ixLevels.size == s.levelParams.size then some (s.levelsAt us)
  else if s.ixLevels.size == s.levelParams.size + 1 then
    match s.ixLevels[0]? with
    | some (Level.zero _) => some (s.levelsAt us)
    | _ => none
  else none

end Ix.Compile.Pass.Opt

end
