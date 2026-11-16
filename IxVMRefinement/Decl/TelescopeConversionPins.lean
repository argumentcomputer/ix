import IxC.Kernel.Rules.Inversion
import IxC.Kernel.Verify.PropRead

/-! # What an actual conversion between product types retains

Products are rigid under head reduction. A conversion between two products therefore
retains their domain comparison, their binder datum, and a comparison of their opened
bodies. Symmetry may select either original opener; that choice stays explicit instead
of replacing free-variable annotations inside a derivation.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Rules

private theorem forall_type_not_const {md : Mode} {env : Env md} {grade : Grade} {depth : Nat}
    {domain body inferred reduced : Expr md} {binderMeta : BinderMeta} {name : Key md} {levels : List Level}
    (typed : Infer env grade depth (.forallE domain body binderMeta) inferred)
    (steps : Red env depth inferred reduced) (head : reduced.getAppFn = .const name levels) : False := by
  obtain ⟨sortLevel, rfl⟩ := Infer.sort_of_sortOrPi typed rfl
  have same := Red.rigid steps rfl
  rw [same] at head
  cases head

private theorem forall_type_not_unit {md : Mode} {env : Env md} {grade : Grade} {depth : Nat}
    {domain body inferred reduced : Expr md} {binderMeta : BinderMeta}
    (typed : Infer env grade depth (.forallE domain body binderMeta) inferred)
    (steps : Red env depth inferred reduced) (unit : isUnitLikeTy env reduced = true) : False := by
  obtain ⟨sortLevel, rfl⟩ := Infer.sort_of_sortOrPi typed rfl
  have same := Red.rigid steps rfl
  rw [same] at unit
  cases unit

private theorem forall_not_proof {md : Mode} {env : Env md} {depth : Nat}
    {domain body inferred sortType : Expr md} {binderMeta : BinderMeta} {sortLevel : Level}
    (typed : Infer env .io depth (.forallE domain body binderMeta) inferred)
    (typedAgain : Infer env .io depth inferred sortType)
    (sorted : Red env depth sortType (.sort sortLevel))
    (zero : ∀ φ, sortLevel.eval φ = 0) : False := by
  obtain ⟨level, rfl⟩ := Infer.sort_of_sortOrPi typed rfl
  have sortTypeEq := Infer.sort_inv typedAgain
  subst sortType
  have sortEq := Red.sort_eq sorted
  subst sortLevel
  have impossible := zero (fun _ => 0)
  simp only [Level.eval] at impossible
  omega

/-- Product conversion retains an actual opened-body derivation at one of its original domains.
No arbitrary conversion transitivity or free-variable type replacement is used. -/
theorem forall_conversion_components {md : Mode} {env : Env md} {depth : Nat}
    {leftDomain leftBody rightDomain rightBody : Expr md} {leftMeta rightMeta : BinderMeta}
    (converted : DefEq env depth (.forallE leftDomain leftBody leftMeta)
      (.forallE rightDomain rightBody rightMeta)) :
    DefEq env depth leftDomain rightDomain ∧ leftMeta.pw = rightMeta.pw ∧
      (DefEq env (depth + 1) (leftBody.instantiate1 (.fvar depth leftDomain))
          (rightBody.instantiate1 (.fvar depth leftDomain)) ∨
        DefEq env (depth + 1) (leftBody.instantiate1 (.fvar depth rightDomain))
          (rightBody.instantiate1 (.fvar depth rightDomain))) := by
  cases converted with
  | refl => exact ⟨.refl, rfl, .inl .refl⟩
  | symm reversed =>
    obtain ⟨domain, metadata, leftOpened | rightOpened⟩ := forall_conversion_components reversed
    · exact ⟨.symm domain, metadata.symm, .inr (.symm leftOpened)⟩
    · exact ⟨.symm domain, metadata.symm, .inl (.symm rightOpened)⟩
  | redL reduced further =>
    have same := Red.rigid reduced rfl
    cases same
    exact forall_conversion_components further
  | natOffset _ _ offset _ _ => cases offset
  | forallE domain body metadata => exact ⟨domain, metadata, .inr body⟩
  | proofFast first _ =>
    simp only [isProofFast, proofPW, Expr.getAppFn, headProofPW, PropWhen.isProp_never] at first
    cases first
  | proofIrrel typed typedAgain sorted zero _ _ _ _ =>
    exact (forall_not_proof typed typedAgain sorted zero).elim
  | unitLike typed reduced unit _ _ _ => exact (forall_type_not_unit typed reduced unit).elim
  | structEta _ _ head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => cases head
  | structUnit typed reduced head _ _ _ _ _ _ _ _ _ =>
    exact (forall_type_not_const typed reduced head).elim
  | proofIrrelTy typed typedAgain sorted zero _ _ =>
    exact (forall_not_proof typed typedAgain sorted zero).elim
  | unitLikeTy typed reduced head _ _ _ _ _ _ _ =>
    exact (forall_type_not_const typed reduced head).elim
  | structEtaTy head _ _ _ _ _ _ _ _ _ _ _ _ _ => cases head
termination_by converted

end IxVM.Refinement.Decl
