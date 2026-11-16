import IxVMRefinement.Decl.SortBetaReduction
import IxC.Kernel.Verify.PropRead
import IxC.Kernel.Verify.PropWhen

/-! # Actual comparison of a sort with a constant-sort beta redex

One endpoint stays a literal sort throughout the rules induction. The other may reduce
within the fixed-sort beta fragment. Application congruence and forged lambda metadata
cannot replace the literal endpoint, and no conversion transitivity is introduced.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Rules

mutual

private theorem sort_side_comparison {md : Mode} {env : Env md} :
    ∀ {depth : Nat} {left right : Expr md}, DefEq env depth left right →
      (∀ {leftSort rightSort : Level}, left = .sort leftSort → SortBeta rightSort right →
        ∀ φ, leftSort.eval φ = rightSort.eval φ) ∧
      (∀ {leftSort rightSort : Level}, SortBeta leftSort left → right = .sort rightSort →
        ∀ φ, leftSort.eval φ = rightSort.eval φ)
  | _, _, _, .refl => by
    constructor
    · intro leftSort rightSort equal shape φ
      rw [equal] at shape
      rw [shape.sort_level]
    · intro leftSort rightSort shape equal φ
      rw [equal] at shape
      rw [shape.sort_level]
  | _, _, _, .symm reversed => by
    constructor
    · intro leftSort rightSort equal shape φ
      exact ((sort_side_comparison reversed).2 shape equal φ).symm
    · intro leftSort rightSort shape equal φ
      exact ((sort_side_comparison reversed).1 equal shape φ).symm
  | _, _, _, .redL reduced further => by
    constructor
    · intro leftSort rightSort equal shape φ
      have same := Red.rigid reduced (by rw [equal]; rfl)
      exact (sort_side_comparison further).1 (same.trans equal) shape φ
    · intro leftSort rightSort shape equal φ
      exact (sort_side_comparison further).2 (shape.reduced reduced) equal φ
  | _, _, _, .sort levels => by
    constructor
    · intro leftSort rightSort equal shape φ
      obtain rfl := Expr.sort.inj equal
      obtain rfl := shape.sort_level
      exact levels φ
    · intro leftSort rightSort shape equal φ
      obtain rfl := shape.sort_level
      obtain rfl := Expr.sort.inj equal
      exact levels φ
  | _, _, _, .natOffset _ _ offset _ _ => by
    constructor
    · intro leftSort rightSort equal shape φ
      rw [equal] at offset
      cases offset
    · intro leftSort rightSort shape equal φ
      rw [shape.offset_none] at offset
      cases offset
  | _, _, _, .proofFast first second => by
    constructor
    · intro leftSort rightSort equal shape φ
      rw [equal] at first
      simp only [isProofFast, proofPW, Expr.getAppFn, headProofPW, PropWhen.isProp_never] at first
      cases first
    · intro leftSort rightSort shape equal φ
      rw [equal] at second
      simp only [isProofFast, proofPW, Expr.getAppFn, headProofPW, PropWhen.isProp_never] at second
      cases second
  | _, _, _, .proofIrrel typed typedAgain sorted zero _ _ _ _ => by
    constructor
    · intro leftSort rightSort equal shape φ
      rw [equal] at typed
      exact (SortBeta.not_proof .sort typed typedAgain sorted zero).elim
    · intro leftSort rightSort shape equal φ
      exact (shape.not_proof typed typedAgain sorted zero).elim
  | _, _, _, .unitLike typed reduced unit _ _ _ => by
    constructor
    · intro leftSort rightSort equal shape φ
      rw [equal] at typed
      exact (SortBeta.type_not_unit .sort typed reduced unit).elim
    · intro leftSort rightSort shape equal φ
      exact (shape.type_not_unit typed reduced unit).elim
  | _, _, _, .structEta _ _ head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by
    constructor
    · intro leftSort rightSort equal shape φ
      rw [equal] at head
      cases head
    · intro leftSort rightSort shape equal φ
      exact (shape.not_const_head _ _ head).elim
  | _, _, _, .structUnit typed reduced head _ _ _ _ _ _ _ _ _ => by
    constructor
    · intro leftSort rightSort equal shape φ
      rw [equal] at typed
      exact (SortBeta.type_not_const .sort typed reduced head).elim
    · intro leftSort rightSort shape equal φ
      exact (shape.type_not_const typed reduced head).elim
  | _, _, _, .proofIrrelTy typed typedAgain sorted zero _ _ => by
    constructor
    · intro leftSort rightSort equal shape φ
      rw [equal] at typed
      exact (SortBeta.not_proof .sort typed typedAgain sorted zero).elim
    · intro leftSort rightSort shape equal φ
      exact (shape.not_proof typed typedAgain sorted zero).elim
  | _, _, _, .unitLikeTy typed reduced head _ _ _ _ _ _ _ => by
    constructor
    · intro leftSort rightSort equal shape φ
      rw [equal] at typed
      exact (SortBeta.type_not_const .sort typed reduced head).elim
    · intro leftSort rightSort shape equal φ
      exact (shape.type_not_const typed reduced head).elim
  | _, _, _, .structEtaTy head _ _ _ _ _ _ _ _ _ _ _ _ _ => by
    constructor
    · intro leftSort rightSort equal shape φ
      exact (shape.not_const_head _ _ head).elim
    · intro leftSort rightSort shape equal φ
      rw [equal] at head
      cases head
  | _, _, _, .eta .. => by
    constructor
    · intros; contradiction
    · intro leftSort rightSort shape equal φ
      cases shape
  | _, _, _, .fvar | _, _, _, .const _ | _, _, _, .natZero | _, _, _, .natSucc _
  | _, _, _, .forallE .. | _, _, _, .lam .. | _, _, _, .app .. | _, _, _, .proj .. => by
    constructor <;> intros <;> contradiction

private theorem sort_side_red {md : Mode} {env : Env md} :
    ∀ {d : Nat} {a b : Expr md}, Red env d a b → True
  | _, _, _, _ => trivial

private theorem sort_side_infer {md : Mode} {env : Env md} :
    ∀ {grade : Grade} {d : Nat} {e t : Expr md}, Infer env grade d e t → True
  | _, _, _, _, _ => trivial

private theorem sort_side_certs {md : Mode} {env : Env md} :
    ∀ {d : Nat} {licensed : Bool} {ty : Expr md} {args : List (Expr md)}, Certs env d licensed ty args → True
  | _, _, _, _, _ => trivial

private theorem sort_side_list {md : Mode} {env : Env md} :
    ∀ {d : Nat} {left right : List (Expr md)}, DefEqList env d left right → True
  | _, _, _, _ => trivial

private theorem sort_side_eta {md : Mode} {env : Env md} :
    ∀ {d : Nat} {T : Key md} {us : List Level} {args : List (Expr md)} {body : Expr md}
      {levels : List LevelParam} {indices : List Nat}, EtaProjCerts env d T us args body levels indices → True
  | _, _, _, _, _, _, _, _ => trivial

end

/-- A literal sort compared with the fixed-sort beta fragment has the same universe level,
without assumptions on the argument's context or any semantic recursor law. -/
theorem sort_beta_levels {md : Mode} {env : Env md} {depth : Nat} {leftSort rightSort : Level}
    {right : Expr md} (compared : DefEq env depth (.sort leftSort) right) (shape : SortBeta rightSort right) :
    ∀ φ, leftSort.eval φ = rightSort.eval φ := (sort_side_comparison compared).1 rfl shape

/-- The actual comparison determines the canonical zero-ness datum. -/
theorem sort_beta_zero {md : Mode} {env : Env md} {depth : Nat} {leftSort rightSort : Level}
    {right : Expr md} (compared : DefEq env depth (.sort leftSort) right) (shape : SortBeta rightSort right) :
    Level.zeronessOf leftSort = Level.zeronessOf rightSort := by
  apply PropWhen.eq_of_holds
  intro φ
  rw [PropWhen.zeronessOf_sound, PropWhen.zeronessOf_sound, sort_beta_levels compared shape φ]

/-- Term substitution preserves a constant-sort beta body exactly. -/
theorem SortBeta.instantiate1 {md : Mode} {sortLevel : Level} {e : Expr md}
    (shape : SortBeta sortLevel e) (value : Expr md) (cut : Nat) :
    SortBeta sortLevel (e.instantiate1 value cut) := by
  cases shape with
  | sort => exact .sort
  | beta => exact .beta

end IxVM.Refinement.Decl
