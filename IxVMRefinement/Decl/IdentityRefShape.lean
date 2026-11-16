import IxC.Kernel.ExprOps
import Ix.IxVM.Consistency.Statement

/-! # Covariant identity-reference syntax

The selected reference changes with substitution, abstraction and annotation. Keeping it
explicit allows the original and final checked frames to supply different type annotations.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- The reference itself or an identity beta redex applied to that reference. -/
inductive IdentityRef (domainSort : Level) (reference : Expr md) : Expr md → Prop
  | reference : IdentityRef domainSort reference reference
  | beta {metadata : BinderMeta} :
      IdentityRef domainSort reference (.app (.lam (.sort domainSort) (.bvar 0) metadata) reference)

/-- Substitution acts on both the tracked reference and the expression. -/
theorem IdentityRef.instantiate1 {md : Mode} {domainSort : Level} {reference e : Expr md}
    (shape : IdentityRef domainSort reference e) (value : Expr md) (cut : Nat) :
    IdentityRef domainSort (reference.instantiate1 value cut) (e.instantiate1 value cut) := by
  cases shape with
  | reference => exact .reference
  | @beta metadata =>
    simpa [Expr.instantiate1] using
      (IdentityRef.beta (domainSort := domainSort) (reference := reference.instantiate1 value cut) (metadata := metadata))

/-- Closing also transports the tracked reference rather than dropping its identity. -/
theorem IdentityRef.abstract1 {md : Mode} {domainSort : Level} {reference e : Expr md}
    (shape : IdentityRef domainSort reference e) (index cut : Nat) :
    IdentityRef domainSort (reference.abstract1 index cut) (e.abstract1 index cut) := by
  cases shape with
  | reference => exact .reference
  | @beta metadata =>
    simpa [Expr.abstract1] using
      (IdentityRef.beta (domainSort := domainSort) (reference := reference.abstract1 index cut) (metadata := metadata))

/-- Reannotation returns a related reference and preserves the identity-redex shape. -/
theorem IdentityRef.annotated {domainSort : Level} {reference e out : Expr .anon}
    (shape : IdentityRef domainSort reference e) (annotation : IxVM.Consistency.Annotates out e) :
    ∃ nextReference, IxVM.Consistency.Annotates nextReference reference ∧ IdentityRef domainSort nextReference out := by
  cases shape with
  | reference => exact ⟨out, annotation, .reference⟩
  | beta =>
    cases annotation with
    | app functionAnn argumentAnn =>
      cases functionAnn with
      | lam domainAnn bodyAnn =>
        cases domainAnn
        cases bodyAnn
        exact ⟨_, argumentAnn, .beta⟩

/-- In a closed telescope the selected bound reference itself cannot change under annotation. -/
theorem IdentityRef.annotated_bvar {domainSort : Level} {index : Nat} {e out : Expr .anon}
    (shape : IdentityRef domainSort (.bvar index) e) (annotation : IxVM.Consistency.Annotates out e) :
    IdentityRef domainSort (.bvar index) out := by
  obtain ⟨reference, referenceAnn, result⟩ := shape.annotated annotation
  cases referenceAnn
  exact result

end IxVM.Refinement.Decl
