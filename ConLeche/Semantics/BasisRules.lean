module

import ConLeche.Kernel.BasisA
public import ConLeche.Verify.EnvPreds

@[expose] public section

/-!
# The basis blocks' stored rules, at the base (task #161 S7, Wall C)

`Nat.rec`'s two stored rules and the entry equation that names them.
They are pure `RecRule`/`Expr` syntax — no `V`, no `denote`, no
`EnvS` — and were declared in `SetR/Install/BasisS.lean` only because
the collapsed install needed them first.  Both lanes read them (the P
lane at `BasisBlocksP`'s `Nat.rec` row), so they belong here; the
census's "the gate sees imports, not crossings" finding is what hid
the crossing until the `BasisEmptyP → Install/BasisS` import died.

Statements verbatim from their old home; names unchanged.
-/

namespace ConLeche.Semantics

open ConLeche
/-- `Nat.rec`'s two stored rules. -/
def natRecZeroRule : RecRule :=
  { ctor := natZeroName, nfields := 0, ctorParams := 0, fire := .plain,
    paramsBlind := true,
    rhs := Expr.lam
      (Expr.forallE (.const natName [])
        (.sort (.param uN)) { pw := .never })
      (Expr.lam
        (.app (.bvar 0) (.const natZeroName []))
        (Expr.lam
          (Expr.forallE (.const natName [])
            (Expr.forallE (.app (.bvar 2)
              (.bvar 0))
              (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))
              { pw := .ifAllZero [uN] })
            { pw := .ifAllZero [uN] })
          (.bvar 1) { pw := .ifAllZero [uN] })
        { pw := .ifAllZero [uN] })
      { pw := .ifAllZero [uN] } }

def natRecSuccRule : RecRule :=
  { ctor := natSuccName, nfields := 1, ctorParams := 0, fire := .plain,
    paramsBlind := true,
    rhs := Expr.lam
      (Expr.forallE (.const natName [])
        (.sort (.param uN)) { pw := .never })
      (Expr.lam
        (.app (.bvar 0) (.const natZeroName []))
        (Expr.lam
          (Expr.forallE (.const natName [])
            (Expr.forallE (.app (.bvar 2)
              (.bvar 0))
              (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))
              { pw := .ifAllZero [uN] })
            { pw := .ifAllZero [uN] })
          (Expr.lam (.const natName [])
            (.app (.app (.bvar 1) (.bvar 0))
              (.app (.app (.app (.app (.const (natName.str "rec")
                [.param uN]) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar
                  0)))
            { pw := .ifAllZero [uN] })
          { pw := .ifAllZero [uN] })
        { pw := .ifAllZero [uN] })
      { pw := .ifAllZero [uN] } }

theorem natRecA_eq :
    natRecA = .recInfo natRecA.toConstantVal 3 3
      [natRecZeroRule, natRecSuccRule] := by
  show natRecA = _
  rfl

/-- `Quot.ind`'s single stored rule. -/
def quotIndRule : RecRule :=
  { ctor := quotMkName, nfields := 1, ctorParams := 2, fire := .plain,
    paramsBlind := true,
    rhs := Expr.lam (.sort (.param uN))
      (Expr.lam
        (Expr.forallE (.bvar 0)
          (Expr.forallE (.bvar 1) (.sort .zero)
            { pw := .never }) { pw := .never })
        (Expr.lam
          (Expr.forallE
            (.app (.app (.const quotName [.param uN]) (.bvar 1)) (.bvar
              0))
            (.sort .zero) { pw := .never })
          (Expr.lam
            (Expr.forallE (.bvar 2)
              (.app (.bvar 1)
                (.app (.app (.app (.const quotMkName [.param uN])
                  (.bvar 3)) (.bvar 2)) (.bvar 0)))
              { pw := .ifAllZero [] })
            (Expr.lam (.bvar 3)
              (.app (.bvar 1) (.bvar 0)) { pw := .ifAllZero [] })
            { pw := .ifAllZero [] })
          { pw := .ifAllZero [] })
        { pw := .ifAllZero [] })
      { pw := .ifAllZero [] } }


/-- `Quot.lift`'s single stored rule. -/
def quotLiftRule : RecRule :=
  { ctor := quotMkName, nfields := 1, ctorParams := 2, fire := .plain,
    paramsBlind := true,
    rhs := Expr.lam (.sort (.param uN))
      (Expr.lam
        (Expr.forallE (.bvar 0)
          (Expr.forallE (.bvar 1) (.sort .zero)
            { pw := .never }) { pw := .never })
        (Expr.lam (.sort (.param vN))
          (Expr.lam
            (Expr.forallE (.bvar 2) (.bvar 1)
              { pw := .ifAllZero [vN] })
            (Expr.lam
              (Expr.forallE (.bvar 3)
                (Expr.forallE (.bvar 4)
                  (Expr.forallE
                    (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                    (.app (.app (.app (.const eqName [.param vN])
                      (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
                      (.app (.bvar 3) (.bvar 1)))
                    { pw := .ifAllZero [] }) { pw := .ifAllZero [] })
                { pw := .ifAllZero [] })
              (Expr.lam (.bvar 4)
                (.app (.bvar 2) (.bvar 0)) { pw := .ifAllZero [vN] })
              { pw := .ifAllZero [vN] })
            { pw := .ifAllZero [vN] })
          { pw := .ifAllZero [vN] })
        { pw := .ifAllZero [vN] })
      { pw := .ifAllZero [vN] } }


/-- `Eq.rec`'s single stored rule. -/
def eqRecRule : RecRule :=
  { ctor := eqReflName, nfields := 0, ctorParams := 2, fire := .plain,
    paramsBlind := true,
    k := true,
    rhs := Expr.lam (.sort (.param uN))
      (Expr.lam (.bvar 0)
        (Expr.lam
          (Expr.forallE (.bvar 1)
            (Expr.forallE
              (.app (.app (.app (.const eqName [.param uN]) (.bvar 2))
                (.bvar 1)) (.bvar 0))
              (.sort (.param u1N)) { pw := .never })
            { pw := .never })
          (Expr.lam
            (.app (.app (.bvar 0) (.bvar 1))
              (.app (.app (.const eqReflName [.param uN]) (.bvar 2))
                (.bvar 1)))
            (.bvar 0) { pw := .ifAllZero [u1N] })
          { pw := .ifAllZero [u1N] })
        { pw := .ifAllZero [u1N] })
      { pw := .ifAllZero [u1N] } }


/-- The stored declaration, with its rule named. -/
theorem quotIndA_eq :
    quotIndA = .recInfo quotIndA.toConstantVal 4 4 [quotIndRule] := by rfl


theorem quotLiftA_eq :
    quotLiftA = .recInfo quotLiftA.toConstantVal 5 5 [quotLiftRule] := by
      rfl


/-- The stored declaration, with its rule named. -/
theorem eqRecA_eq :
    eqRecA = .recInfo eqRecA.toConstantVal 5 4 [eqRecRule] := by rfl


end ConLeche.Semantics
