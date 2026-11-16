import IxC.Kernel.Rules.Inversion

/-! # Reduction of constant-sort beta redexes

A lambda is rigid under the rules' head reductions. Applying a lambda whose body is a
literal sort can only retain such a redex, change its argument, or expose that same sort.
The argument and its context need not be inhabited for this syntactic fact.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Rules

/-- A literal sort or one beta redex whose lambda body is that exact sort. -/
inductive SortBeta (sortLevel : Level) : Expr md → Prop
  | sort : SortBeta sortLevel (.sort sortLevel)
  | beta {domain argument : Expr md} {binderMeta : BinderMeta} :
      SortBeta sortLevel (.app (.lam domain (.sort sortLevel) binderMeta) argument)

theorem SortBeta.sort_level {md : Mode} {left right : Level} (shape : SortBeta (md := md) left (.sort right)) :
    left = right := by cases shape; rfl

theorem SortBeta.not_const_head {md : Mode} {sortLevel : Level} {e : Expr md} (shape : SortBeta sortLevel e)
    (name : Key md) (levels : List Level) : e.getAppFn ≠ .const name levels := by
  cases shape <;> intro impossible <;> cases impossible

theorem SortBeta.unfold_none {md : Mode} {env : Env md} {sortLevel : Level} {e : Expr md}
    (shape : SortBeta sortLevel e) : unfoldDefinition env e = none := by cases shape <;> rfl

theorem SortBeta.offset_none {md : Mode} {sortLevel : Level} {e : Expr md}
    (shape : SortBeta sortLevel e) : natOffsetOf e = none := by cases shape <;> rfl

/-- Any inference of this fragment has the exact successor-sort type. -/
theorem SortBeta.inferred_type {md : Mode} {env : Env md} {grade : Grade} {depth : Nat}
    {sortLevel : Level} {e inferred : Expr md} (shape : SortBeta sortLevel e)
    (typed : Infer env grade depth e inferred) : inferred = .sort (.succ sortLevel) := by
  cases shape with
  | sort => exact Infer.sort_inv typed
  | beta =>
    cases typed with
    | app functionTyped functionReduced _ _ =>
      cases functionTyped with
      | lam _ _ bodyTyped _ _ _ _ =>
        have bodyType := Infer.sort_inv bodyTyped
        rw [bodyType] at functionReduced
        obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Red.rigid functionReduced rfl)
        rfl
    | appSkip functionTyped functionReduced _ =>
      cases functionTyped with
      | lam _ _ bodyTyped _ _ _ _ =>
        have bodyType := Infer.sort_inv bodyTyped
        rw [bodyType] at functionReduced
        obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Red.rigid functionReduced rfl)
        rfl

theorem SortBeta.type_not_const {md : Mode} {env : Env md} {grade : Grade} {depth : Nat}
    {sortLevel : Level} {e inferred reduced : Expr md} {name : Key md} {levels : List Level}
    (shape : SortBeta sortLevel e) (typed : Infer env grade depth e inferred)
    (steps : Red env depth inferred reduced) (head : reduced.getAppFn = .const name levels) : False := by
  rw [shape.inferred_type typed] at steps
  have same := Red.rigid steps rfl
  rw [same] at head
  cases head

theorem SortBeta.type_not_unit {md : Mode} {env : Env md} {grade : Grade} {depth : Nat}
    {sortLevel : Level} {e inferred reduced : Expr md}
    (shape : SortBeta sortLevel e) (typed : Infer env grade depth e inferred)
    (steps : Red env depth inferred reduced) (unit : isUnitLikeTy env reduced = true) : False := by
  rw [shape.inferred_type typed] at steps
  have same := Red.rigid steps rfl
  rw [same] at unit
  cases unit

theorem SortBeta.not_proof {md : Mode} {env : Env md} {depth : Nat}
    {sortLevel proofLevel : Level} {e inferred inferredAgain : Expr md}
    (shape : SortBeta sortLevel e) (typed : Infer env .io depth e inferred)
    (typedAgain : Infer env .io depth inferred inferredAgain)
    (sorted : Red env depth inferredAgain (.sort proofLevel))
    (zero : ∀ φ, proofLevel.eval φ = 0) : False := by
  rw [shape.inferred_type typed] at typedAgain
  rw [Infer.sort_inv typedAgain] at sorted
  have proofLevelEq := Red.sort_eq sorted
  rw [proofLevelEq] at zero
  have impossible := zero (fun _ => 0)
  simp only [Level.eval] at impossible
  omega

private theorem lambda_type_not_const {md : Mode} {env : Env md} {grade : Grade} {depth : Nat}
    {e inferred reduced domain body : Expr md} {binderMeta : BinderMeta} {name : Key md} {levels : List Level}
    (shape : e = .lam domain body binderMeta) (typed : Infer env grade depth e inferred)
    (steps : Red env depth inferred reduced) (head : reduced.getAppFn = .const name levels) : False := by
  rw [shape] at typed
  cases typed with
  | lam =>
    have same := Red.rigid steps rfl
    rw [same] at head
    cases head

mutual

private theorem reduction_special_heads {md : Mode} {env : Env md} :
    ∀ {depth : Nat} {left right : Expr md}, Red env depth left right →
      (∀ {domain body : Expr md} {binderMeta : BinderMeta}, left = .lam domain body binderMeta → right = left) ∧
      (∀ {sortLevel : Level}, SortBeta sortLevel left → SortBeta sortLevel right)
  | _, _, _, .refl => ⟨fun _ => rfl, fun shape => shape⟩
  | _, _, _, .trans first second => by
    constructor
    · intro domain body bm shape
      have firstEq := (reduction_special_heads first).1 shape
      exact ((reduction_special_heads second).1 (firstEq.trans shape)).trans firstEq
    · intro sortLevel shape
      exact (reduction_special_heads second).2 ((reduction_special_heads first).2 shape)
  | _, _, _, .appFn functionReduced => by
    constructor
    · intros; contradiction
    · intro sortLevel shape
      cases shape with
      | beta =>
        have same := (reduction_special_heads functionReduced).1 rfl
        rw [same]
        exact .beta
  | _, _, _, .appArg _ => by
    constructor
    · intros; contradiction
    · intro sortLevel shape; cases shape; exact .beta
  | _, _, _, .betaGate _ => by
    constructor
    · intros; contradiction
    · intro sortLevel shape; cases shape; exact .sort
  | _, _, _, .beta _ _ => by
    constructor
    · intros; contradiction
    · intro sortLevel shape; cases shape; exact .sort
  | _, _, _, .delta unfolded => by
    constructor
    · intro domain body bm shape
      rw [shape] at unfolded
      cases unfolded
    · intro sortLevel shape
      rw [shape.unfold_none] at unfolded
      cases unfolded
  | _, _, _, .eqProof head .. => by
    constructor
    · intro domain body bm shape; rw [shape] at head; cases head
    · intro sortLevel shape; exact (shape.not_const_head _ _ head).elim
  | _, _, _, .iota head .. => by
    constructor
    · intro domain body bm shape; rw [shape] at head; cases head
    · intro sortLevel shape; exact (shape.not_const_head _ _ head).elim
  | _, _, _, .rescueK _ _ _ _ _ typed reduced head .. => by
    constructor
    · intro domain body bm shape
      exact (lambda_type_not_const shape typed reduced head).elim
    · intro sortLevel shape
      exact (shape.type_not_const typed reduced head).elim
  | _, _, _, .rescueEta _ _ _ _ _ typed reduced head .. => by
    constructor
    · intro domain body bm shape
      exact (lambda_type_not_const shape typed reduced head).elim
    · intro sortLevel shape
      exact (shape.type_not_const typed reduced head).elim
  | _, _, _, .rescueAnd _ _ _ _ typed reduced head .. => by
    constructor
    · intro domain body bm shape
      exact (lambda_type_not_const shape typed reduced head).elim
    · intro sortLevel shape
      exact (shape.type_not_const typed reduced head).elim
  | _, _, _, .projArg _ | _, _, _, .deltaThm .. | _, _, _, .natLit _
  | _, _, _, .natZeroLit _ | _, _, _, .strLit _ | _, _, _, .natSucc ..
  | _, _, _, .natOp .. | _, _, _, .natAddSucc .. | _, _, _, .natAddZero .. | _, _, _, .proj .. => by
    constructor
    · intros; contradiction
    · intro sortLevel shape; cases shape

private theorem reduction_special_defeq {md : Mode} {env : Env md} :
    ∀ {d : Nat} {a b : Expr md}, DefEq env d a b → True
  | _, _, _, _ => trivial

private theorem reduction_special_infer {md : Mode} {env : Env md} :
    ∀ {grade : Grade} {d : Nat} {e t : Expr md}, Infer env grade d e t → True
  | _, _, _, _, _ => trivial

private theorem reduction_special_certs {md : Mode} {env : Env md} :
    ∀ {d : Nat} {licensed : Bool} {ty : Expr md} {args : List (Expr md)}, Certs env d licensed ty args → True
  | _, _, _, _, _ => trivial

private theorem reduction_special_list {md : Mode} {env : Env md} :
    ∀ {d : Nat} {left right : List (Expr md)}, DefEqList env d left right → True
  | _, _, _, _ => trivial

private theorem reduction_special_eta {md : Mode} {env : Env md} :
    ∀ {d : Nat} {T : Key md} {us : List Level} {args : List (Expr md)} {body : Expr md}
      {levels : List LevelParam} {indices : List Nat}, EtaProjCerts env d T us args body levels indices → True
  | _, _, _, _, _, _, _, _ => trivial

end

/-- Actual reduction preserves the exact constant-sort result of this beta fragment. -/
theorem SortBeta.reduced {md : Mode} {env : Env md} {depth : Nat} {left right : Expr md}
    {sortLevel : Level} (shape : SortBeta sortLevel left) (reduced : Red env depth left right) :
    SortBeta sortLevel right := (reduction_special_heads reduced).2 shape

end IxVM.Refinement.Decl
