module

public import IxC.Kernel.Model.GuardClassifierErase

@[expose] public section

/-! # Erasing metadata from classifier lookups and head computations

The classifier never tests binder or let metadata. Its data computation therefore commutes
with erasing that metadata from its input and from every successful declaration lookup.
-/

namespace Ix.Kernel.GuardClassifier

/-- A dictionary whose successful answers have binder/let metadata erased. -/
def Lookup.eraseMeta (look : Lookup md) : Lookup md where
  typeOf k us := (look.typeOf k us).map Expr.eraseMeta
  valueOf k us := (look.valueOf k us).map Expr.eraseMeta

/-- Exact head computation commutes with metadata erasure, including capture-avoiding beta. -/
theorem head_eraseMeta (look : Lookup md) :
    ∀ fuel e, head look.eraseMeta fuel e.eraseMeta = (head look fuel e).map Expr.eraseMeta := by
  intro fuel
  induction fuel with
  | zero => intro e; rfl
  | succ fuel ih =>
    intro e
    cases e <;> try rfl
    case const k us =>
      simp only [head, Lookup.eraseMeta, Expr.eraseMeta]
      cases hv : look.valueOf k us with
      | none => rfl
      | some v => exact ih v
    case app f a =>
      simp only [head, Expr.eraseMeta]
      rw [ih f]
      cases hf : head look fuel f with
      | none => rfl
      | some value =>
        cases value <;> try rfl
        case lam ty body mb =>
          change head look.eraseMeta fuel (body.eraseMeta.instantiate1Lift a.eraseMeta) =
            (head look fuel (body.instantiate1Lift a)).map Expr.eraseMeta
          rw [← eraseMeta_instantiate1Lift]
          exact ih _
    case letE ty value body lm =>
      simp only [head, Expr.eraseMeta]
      rw [← eraseMeta_instantiate1Lift]
      exact ih _

/-- Metadata erasure preserves every successful head result with precisely the expected erasure. -/
theorem head_eraseMeta_of_some {look : Lookup md} {fuel : Nat} {e r : Expr md}
    (h : head look fuel e = some r) : head look.eraseMeta fuel e.eraseMeta = some r.eraseMeta := by
  rw [head_eraseMeta, h]
  rfl

end Ix.Kernel.GuardClassifier
