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
mutual

private theorem forall_conversion_components_aux {md : Mode} {env : Env md} :
    ∀ {depth : Nat} {left right : Expr md}, DefEq env depth left right →
    ∀ {leftDomain leftBody rightDomain rightBody : Expr md} {leftMeta rightMeta : BinderMeta},
    left = .forallE leftDomain leftBody leftMeta → right = .forallE rightDomain rightBody rightMeta →
    DefEq env depth leftDomain rightDomain ∧ leftMeta.pw = rightMeta.pw ∧
      (DefEq env (depth + 1) (leftBody.instantiate1 (.fvar depth leftDomain))
          (rightBody.instantiate1 (.fvar depth leftDomain)) ∨
        DefEq env (depth + 1) (leftBody.instantiate1 (.fvar depth rightDomain))
          (rightBody.instantiate1 (.fvar depth rightDomain)))
  | _, _, _, .refl => by
    intro ld lb rd rb lm rm le re
    obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (le.symm.trans re)
    exact ⟨.refl, rfl, .inl .refl⟩
  | _, _, _, .symm reversed => by
    intro ld lb rd rb lm rm le re
    obtain ⟨domain, metadata, leftOpened | rightOpened⟩ := forall_conversion_components_aux reversed re le
    · exact ⟨.symm domain, metadata.symm, .inr (.symm leftOpened)⟩
    · exact ⟨.symm domain, metadata.symm, .inl (.symm rightOpened)⟩
  | _, _, _, .redL reduced further => by
    intro ld lb rd rb lm rm le re
    have same := Red.rigid reduced (by rw [le]; rfl)
    exact forall_conversion_components_aux further (same.trans le) re
  | _, _, _, .sort _ => by intros; contradiction
  | _, _, _, .fvar => by intros; contradiction
  | _, _, _, .const _ => by intros; contradiction
  | _, _, _, .natZero => by intros; contradiction
  | _, _, _, .natSucc _ => by intros; contradiction
  | _, _, _, .natOffset _ _ offset _ _ => by
    intro ld lb rd rb lm rm le _
    rw [le] at offset
    cases offset
  | _, _, _, .forallE domain body metadata => by
    intro ld lb rd rb lm rm le re
    obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj le
    obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj re
    exact ⟨domain, metadata, .inr body⟩
  | _, _, _, .lam _ _ _ => by intros; contradiction
  | _, _, _, .app _ _ => by intros; contradiction
  | _, _, _, .proj _ => by intros; contradiction
  | _, _, _, .eta _ _ _ _ _ => by intros; contradiction
  | _, _, _, .proofFast first _ => by
    intro ld lb rd rb lm rm le _
    rw [le] at first
    simp only [isProofFast, proofPW, Expr.getAppFn, headProofPW, PropWhen.isProp_never] at first
    cases first
  | _, _, _, .proofIrrel typed typedAgain sorted zero _ _ _ _ => by
    intro ld lb rd rb lm rm le _
    rw [le] at typed
    exact (forall_not_proof typed typedAgain sorted zero).elim
  | _, _, _, .unitLike typed reduced unit _ _ _ => by
    intro ld lb rd rb lm rm le _
    rw [le] at typed
    exact (forall_type_not_unit typed reduced unit).elim
  | _, _, _, .structEta _ _ head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by
    intro ld lb rd rb lm rm le _
    rw [le] at head
    cases head
  | _, _, _, .structUnit typed reduced head _ _ _ _ _ _ _ _ _ => by
    intro ld lb rd rb lm rm le _
    rw [le] at typed
    exact (forall_type_not_const typed reduced head).elim
  | _, _, _, .proofIrrelTy typed typedAgain sorted zero _ _ => by
    intro ld lb rd rb lm rm le _
    rw [le] at typed
    exact (forall_not_proof typed typedAgain sorted zero).elim
  | _, _, _, .unitLikeTy typed reduced head _ _ _ _ _ _ _ => by
    intro ld lb rd rb lm rm le _
    rw [le] at typed
    exact (forall_type_not_const typed reduced head).elim
  | _, _, _, .structEtaTy head _ _ _ _ _ _ _ _ _ _ _ _ _ => by
    intro ld lb rd rb lm rm _ re
    rw [re] at head
    cases head

private theorem forall_conversion_red {md : Mode} {env : Env md} :
    ∀ {d : Nat} {a b : Expr md}, Red env d a b → True
  | _, _, _, _ => trivial

private theorem forall_conversion_infer {md : Mode} {env : Env md} :
    ∀ {grade : Grade} {d : Nat} {e t : Expr md}, Infer env grade d e t → True
  | _, _, _, _, _ => trivial

private theorem forall_conversion_certs {md : Mode} {env : Env md} :
    ∀ {d : Nat} {licensed : Bool} {ty : Expr md} {args : List (Expr md)}, Certs env d licensed ty args → True
  | _, _, _, _, _ => trivial

private theorem forall_conversion_list {md : Mode} {env : Env md} :
    ∀ {d : Nat} {left right : List (Expr md)}, DefEqList env d left right → True
  | _, _, _, _ => trivial

private theorem forall_conversion_eta {md : Mode} {env : Env md} :
    ∀ {d : Nat} {T : Key md} {us : List Level} {args : List (Expr md)} {body : Expr md}
      {levels : List LevelParam} {indices : List Nat}, EtaProjCerts env d T us args body levels indices → True
  | _, _, _, _, _, _, _, _ => trivial

end



/-- Product conversion retains its checked domain and one actual opened-body comparison. -/
theorem forall_conversion_components {md : Mode} {env : Env md} {depth : Nat}
    {leftDomain leftBody rightDomain rightBody : Expr md} {leftMeta rightMeta : BinderMeta}
    (converted : DefEq env depth (.forallE leftDomain leftBody leftMeta)
      (.forallE rightDomain rightBody rightMeta)) :
    DefEq env depth leftDomain rightDomain ∧ leftMeta.pw = rightMeta.pw ∧
      (DefEq env (depth + 1) (leftBody.instantiate1 (.fvar depth leftDomain))
          (rightBody.instantiate1 (.fvar depth leftDomain)) ∨
        DefEq env (depth + 1) (leftBody.instantiate1 (.fvar depth rightDomain))
          (rightBody.instantiate1 (.fvar depth rightDomain))) :=
  forall_conversion_components_aux converted rfl rfl

end IxVM.Refinement.Decl
