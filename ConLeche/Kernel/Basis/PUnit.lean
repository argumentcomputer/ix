module

public import ConLeche.Kernel.Basis.Builder

@[expose] public section

/-!
# The pinned `PUnit` basis block

The raw pin — the `PUnit` block exactly as an export carries it: the
toolchain's `Init.Prelude` declaration at the parser's raw binder
annotations, plus the pinned capabilities (η and unit-likeness, which
no export carries and the checker does not re-derive for a basis
block).  The
*annotated* forms (`punitA`, …) are computed from these by the
checker's own annotation pass at elaboration time; see
`ConLeche/Kernel/BasisA.lean`.
-/

namespace ConLeche

open BasisDSL

/-- `PUnit.{u} : Sort u`. -/
def punitRaw : ConstantInfo :=
  .indInfo ⟨punitName, [uN], srt u⟩
    { eta := true, etaCtor := punitUnitName,
      etaParams := 0, etaFields := 0, unitlike := true,
      sortZ := .ifAllZero [uN] }

/-- `PUnit.unit.{u} : PUnit.{u}`. -/
def punitUnitRaw : ConstantInfo :=
  .ctorInfo ⟨punitUnitName, [uN], cnst punitName [u]⟩ 0 0

/-- The motive of `PUnit.rec`: `∀ (t : PUnit.{u}), Sort u_1`. -/
def punitRecMotive : Expr :=
  pi "t" (cnst punitName [u]) (srt u1)

/-- `PUnit.rec.{u_1, u} {motive : PUnit.{u} → Sort u_1}
(unit : motive PUnit.unit) (t : PUnit.{u}) : motive t`. -/
def punitRecRaw : ConstantInfo :=
  .recInfo ⟨punitRecName, [u1N, uN],
    piI "motive" punitRecMotive <|
    pi "unit" (.app (bv 0) (cnst punitUnitName [u])) <|
    pi "t" (cnst punitName [u]) (.app (bv 2) (bv 0))⟩
    2 2
    [rule punitUnitName 0 <|
      lm "motive" punitRecMotive <|
      lm "unit" (.app (bv 0) (cnst punitUnitName [u])) <|
      bv 0]

/-- The pinned `PUnit` basis block, in install order. -/
def punitBasis : List ConstantInfo := [punitRaw, punitUnitRaw, punitRecRaw]

end ConLeche
