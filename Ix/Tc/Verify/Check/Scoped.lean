import Ix.Tc.Verify.Level
import Ix.Tc.Verify.Totalization

/-!
# Successful well-scopedness validation

`PendingDecl` deliberately permits raw, ill-scoped syntax.  K3 therefore
cannot assume universe-parameter or de Bruijn bounds when it starts checking
a declaration: those facts have to be recovered from the successful
production `validateExprWellScoped` pass.

This file first records the pure syntax predicate implemented by that pass.
The operational proof below it is kept separate from typing; in particular,
`Scoped` says nothing about applications being well typed or declarations
being admissible.
-/

namespace Ix.Tc

namespace KUniv

/-- Every positional universe parameter occurring in `u` is below `bound`.
This is the pure predicate decided by `validateUnivParamsSeen`; addresses are
irrelevant to the predicate itself. -/
def Scoped (bound : Nat) : KUniv m → Prop
  | .zero _ => True
  | .succ u _ => u.Scoped bound
  | .max a b _ | .imax a b _ => a.Scoped bound ∧ b.Scoped bound
  | .param idx _ _ => idx.toNat < bound

/-- Positional universe scoping is exactly Theory `VLevel.WF` after the
structure-preserving `toVLevel` translation. -/
theorem scoped_iff_toVLevel_wf {u : KUniv m} {bound : Nat} :
    u.Scoped bound ↔ u.toVLevel.WF bound := by
  induction u with
  | zero => rfl
  | succ u _ ih => simpa [Scoped, toVLevel, Lean4Lean.VLevel.WF] using ih
  | max a b _ iha ihb =>
      simp only [Scoped, toVLevel, Lean4Lean.VLevel.WF, iha, ihb]
  | imax a b _ iha ihb =>
      simp only [Scoped, toVLevel, Lean4Lean.VLevel.WF, iha, ihb]
  | param => rfl

theorem Scoped.toVLevel_wf {u : KUniv m} {bound : Nat}
    (h : u.Scoped bound) : u.toVLevel.WF bound :=
  scoped_iff_toVLevel_wf.mp h

end KUniv

namespace KExpr

/-- The syntax-only portion of `validateExprWellScoped`.

The depth is intentionally a `UInt64`, matching the production worklist and
its exact comparison.  Constant arity and projection-head existence are
state/world obligations and are recorded separately by the operational
validator theorem; this predicate captures precisely the binder and universe
bounds needed to turn raw syntax into a Theory expression.  Free variables
are leaves because the validator accepts them and the active local-context
relation is responsible for resolving them. -/
def Scoped (depth : UInt64) (levelBound : Nat) : KExpr m → Prop
  | .var idx _ _ => idx < depth
  | .fvar .. => True
  | .sort u _ => u.Scoped levelBound
  | .const _ us _ => ∀ u ∈ us, u.Scoped levelBound
  | .app f a _ => f.Scoped depth levelBound ∧ a.Scoped depth levelBound
  | .lam _ _ ty body _ | .all _ _ ty body _ =>
      ty.Scoped depth levelBound ∧ body.Scoped (depth + 1) levelBound
  | .letE _ ty val body _ _ =>
      ty.Scoped depth levelBound ∧ val.Scoped depth levelBound ∧
        body.Scoped (depth + 1) levelBound
  | .prj _ _ val _ => val.Scoped depth levelBound
  | .nat .. | .str .. => True

end KExpr

end Ix.Tc
