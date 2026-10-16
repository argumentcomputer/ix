/-
  Ix.AuxGen.LevelEgress: IxC's levels as AuxGen's levels (AuxGen on IxC,
  M1; AUXGEN-IXC §3.3, "Levels out").

  AuxGen emits the levels a kernel answers (`getLevel`'s sort levels) into
  generated terms, so their *spelling* is part of the output: the bytes
  carry canonical (Géran) universes, but `Named` metadata, the `.ixe`, the
  `aux-gen-diff` patch hashes and Lean–Rust lockstep see the spelling.
  `Ix.Tc` builds every level through its smart constructors
  (`Ix.Tc.KUniv.mkMax`/`mkIMax`: at ingress, under substitution, in
  ∀-inference), and the bridge spells its answer back raw
  (`Ix.AuxGen.kunivToLevel`). IxC builds raw levels. So an IxC answer is
  spelled as `Ix.Tc` would have built the same level: positional parameters
  back to the scope's names, then `max`/`imax` rebuilt bottom-up through
  `tcMax`/`tcIMax`, which are `KUniv.mkMax`/`mkIMax` branch for branch on
  `Ix.Level`. The spike measured this equal to `Ix.Tc`'s answer on every
  `.below` level query it answered (fixtures 3,206, Init+Std 282).

  Two departures from `KUniv`, both invisible on the levels egress builds:
  * `KUniv`'s equality is its Merkle address, which hashes a parameter's
    position and not its name; here equality is structural
    (`Ix.Compile.ExactKey.levelEq`), which hashes nothing, over levels whose
    parameters are the scope's names by position. With distinct names
    (`AuxScope.new` refuses duplicates) the two agree.
  * `KUniv.offset` counts in `UInt64`; here in `Nat`.

  A positional parameter beyond the scope's names is refused with the
  bridge's own constructor (`AuxKernelError.levelParamIndex`), never spelled
  `u_{idx}`.

  `normalize` is the same rebuild of a Lean level, `leanLevelToKuniv`
  followed by `kunivToLevel`: what `Ix.Tc`'s ingress does to a level before
  its fast path reads it (AuxGen's `ixcFastLevel`, M2).

  Nothing here depends on `Ix.Tc`, which AuxGen M7 deletes; the tests
  compare it with `Ix.Tc` while both exist.
-/
module
public import Ix.Environment
public import Ix.Compile.ExactKey
public import IxC.Kernel.Expr
public import Ix.AuxGen.KernelError
public section

namespace Ix.AuxGen.Egress

open Ix.Compile.ExactKey (levelEq)

/-! ## `Ix.Tc`'s smart constructors on `Ix.Level` -/

/-- `KUniv.isZero`: the level is `0`. -/
def isZero : Level → Bool
  | .zero _ => true
  | _ => false

/-- `KUniv.isExplicit`: a numeral `succ^n 0`. -/
def isExplicit : Level → Bool
  | .zero _ => true
  | .succ u _ => isExplicit u
  | _ => false

/-- `KUniv.isNeverZero`: nonzero under every assignment. -/
def isNeverZero : Level → Bool
  | .succ _ _ => true
  | .max a b _ => isNeverZero a || isNeverZero b
  | .imax _ b _ => isNeverZero b
  | _ => false

/-- `KUniv.offset`: `(base, n)` with the level `succ^n base`, `base` not a
`succ`. -/
def offset : Level → Level × Nat
  | .succ u _ => let (b, n) := offset u; (b, n + 1)
  | u => (u, 0)

/-- **`KUniv.mkMax`, branch for branch**: both numerals → the larger;
`max a a = a`; `max 0 a = a`, `max a 0 = a`; absorption of `a` into
`max a b'`/`max b' a` on either side; equal bases → the larger offset; else
the raw `max`. -/
def tcMax (a b : Level) : Level :=
  if isExplicit a && isExplicit b then
    if (offset a).2 ≥ (offset b).2 then a else b
  else if levelEq a b then a
  else if isZero a then b
  else if isZero b then a
  else
    let absorbB := match b with
      | .max bl br _ => levelEq bl a || levelEq br a
      | _ => false
    if absorbB then b
    else
      let absorbA := match a with
        | .max al ar _ => levelEq al b || levelEq ar b
        | _ => false
      if absorbA then a
      else
        let (baseA, offA) := offset a
        let (baseB, offB) := offset b
        if levelEq baseA baseB then
          if offA ≥ offB then a else b
        else Level.mkMax a b

/-- **`KUniv.mkIMax`, branch for branch**: `imax a b = max a b` when `b` is
never zero; `imax a 0 = 0`; `imax 0 b = b`, `imax 1 b = b`; `imax a a = a`;
else the raw `imax`. -/
def tcIMax (a b : Level) : Level :=
  if isNeverZero b then tcMax a b
  else if isZero b then b
  else if isZero a then b
  else
    let aIsOne := match a with
      | .succ inner _ => isZero inner
      | _ => false
    if aIsOne then b
    else if levelEq a b then a
    else Level.mkIMax a b

/-! ## Egress -/

/-- **An IxC level as `Ix.Tc` would have built it**: parameter `i` is the
scope's `i`-th name (`lps`), `max`/`imax` go through `tcMax`/`tcIMax`
bottom-up. A parameter beyond `lps` is refused. -/
def egressLevel (lps : Array Name) : Ix.Kernel.Level → Except AuxKernelError Level
  | .zero => pure Level.mkZero
  | .succ u => return Level.mkSucc (← egressLevel lps u)
  | .max u v => return tcMax (← egressLevel lps u) (← egressLevel lps v)
  | .imax u v => return tcIMax (← egressLevel lps u) (← egressLevel lps v)
  | .param i =>
    match lps[i]? with
    | some n => pure (Level.mkParam n)
    | none => throw (.levelParamIndex i)

/-- **A Lean level rebuilt as `Ix.Tc`'s ingress builds it**
(`leanLevelToKuniv` then `kunivToLevel`): `succ` kept, `max`/`imax` through
`tcMax`/`tcIMax` bottom-up, parameters and metavariables kept as they are
(the ingress refuses the latter two when unknown; this rebuild does not
judge them). -/
def normalize : Level → Level
  | .succ u _ => Level.mkSucc (normalize u)
  | .max u v _ => tcMax (normalize u) (normalize v)
  | .imax u v _ => tcIMax (normalize u) (normalize v)
  | u => u

end Ix.AuxGen.Egress

end
