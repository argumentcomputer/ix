import IxC.Kernel.Rules.Inversion

/-! # Typed signatures of constant-sort motive fragments

The fragment contains literal sorts, lambda telescopes returning them, and applications of
those telescopes. The remaining arity is tracked syntactically. Actual inference therefore
returns a product telescope of that arity ending in the exact successor sort, independently
of argument values and of whether a caller's context has inhabitants.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Rules

/-- A syntactic product telescope ending in a fixed sort. -/
inductive ProductSort (sortLevel : Level) : Nat → Expr md → Prop
  | sort : ProductSort sortLevel 0 (.sort sortLevel)
  | pi {count : Nat} {domain body : Expr md} {binderMeta : BinderMeta} :
      ProductSort sortLevel count body → ProductSort sortLevel (count + 1) (.forallE domain body binderMeta)

/-- A constant-sort lambda/application fragment, indexed by its remaining argument count. -/
inductive SortFunction (sortLevel : Level) : Nat → Expr md → Prop
  | sort : SortFunction sortLevel 0 (.sort sortLevel)
  | lam {count : Nat} {domain body : Expr md} {binderMeta : BinderMeta} :
      SortFunction sortLevel count body → SortFunction sortLevel (count + 1) (.lam domain body binderMeta)
  | app {count : Nat} {functionExpr argument : Expr md} :
      SortFunction sortLevel (count + 1) functionExpr → SortFunction sortLevel count (.app functionExpr argument)

theorem ProductSort.zero_eq {md : Mode} {sortLevel : Level} {e : Expr md}
    (shape : ProductSort sortLevel 0 e) : e = .sort sortLevel := by cases shape; rfl

theorem ProductSort.rigid {md : Mode} {sortLevel : Level} {count : Nat} {e : Expr md}
    (shape : ProductSort sortLevel count e) : isSortOrPi e = true := by cases shape <;> rfl

theorem ProductSort.instantiate1 {md : Mode} {sortLevel : Level} {count : Nat} {e : Expr md}
    (shape : ProductSort sortLevel count e) (value : Expr md) :
    ∀ cut, ProductSort sortLevel count (e.instantiate1 value cut) := by
  induction shape with
  | sort => intro cut; exact .sort
  | pi _ ih => intro cut; exact .pi (ih (cut + 1))

theorem ProductSort.abstract1 {md : Mode} {sortLevel : Level} {count : Nat} {e : Expr md}
    (shape : ProductSort sortLevel count e) (index : Nat) :
    ∀ cut, ProductSort sortLevel count (e.abstract1 index cut) := by
  induction shape with
  | sort => intro cut; exact .sort
  | pi _ ih => intro cut; exact .pi (ih (cut + 1))

theorem SortFunction.instantiate1 {md : Mode} {sortLevel : Level} {count : Nat} {e : Expr md}
    (shape : SortFunction sortLevel count e) (value : Expr md) :
    ∀ cut, SortFunction sortLevel count (e.instantiate1 value cut) := by
  induction shape with
  | sort => intro cut; exact .sort
  | lam _ ih => intro cut; exact .lam (ih (cut + 1))
  | app _ ih => intro cut; exact .app (ih cut)

theorem SortFunction.sort_level {md : Mode} {sortLevel actual : Level} {count : Nat}
    (shape : SortFunction (md := md) sortLevel count (.sort actual)) : sortLevel = actual := by cases shape; rfl

theorem SortFunction.not_const_head {md : Mode} {sortLevel : Level} {count : Nat} {e : Expr md}
    (shape : SortFunction sortLevel count e) (name : Key md) (levels : List Level) : e.getAppFn ≠ .const name levels := by
  induction shape with
  | sort | lam => intro impossible; cases impossible
  | app _ ih => exact ih

theorem SortFunction.unfold_none {md : Mode} {env : Env md} {sortLevel : Level} {count : Nat} {e : Expr md}
    (shape : SortFunction sortLevel count e) : unfoldDefinition env e = none := by
  unfold unfoldDefinition
  cases head : e.getAppFn with
  | const name levels => exact (shape.not_const_head name levels head).elim
  | _ => rfl

theorem SortFunction.offset_none {md : Mode} {sortLevel : Level} {count : Nat} {e : Expr md}
    (shape : SortFunction sortLevel count e) : natOffsetOf e = none := by
  cases e with
  | lit => cases shape
  | app functionExpr argument =>
    cases functionExpr with
    | const => exact (shape.not_const_head _ _ rfl).elim
    | app head argument' =>
      cases head with
      | const => exact (shape.not_const_head _ _ rfl).elim
      | _ => rfl
    | _ => rfl
  | _ => rfl

private structure InferredSortFunction {md : Mode} (subject inferred : Expr md) : Prop where
  shape : ∀ {count : Nat} {sortLevel : Level},
    SortFunction sortLevel count subject → ProductSort (.succ sortLevel) count inferred

mutual

private theorem infer_sort_function {md : Mode} {env : Env md} :
    ∀ {grade : Grade} {depth : Nat} {subject inferred : Expr md}, Infer env grade depth subject inferred →
      InferredSortFunction subject inferred
  | _, _, _, _, .sort => by
    refine ⟨?_⟩
    intro count sortLevel shape
    cases shape
    exact .sort
  | _, depth, .lam parameter body bm, _, .lam _ _ bodyTyped _ _ _ _ => by
    have bodyFacts := infer_sort_function bodyTyped
    refine ⟨?_⟩
    intro count sortLevel shape
    cases shape with
    | lam bodyShape =>
      exact .pi ((bodyFacts.shape (bodyShape.instantiate1 (.fvar depth parameter) 0)).abstract1 depth 0)
  | _, _, .app functionExpr argument, _, .app functionTyped functionReduced _ _ => by
    have functionFacts := infer_sort_function functionTyped
    refine ⟨?_⟩
    intro count sortLevel shape
    cases shape with
    | app functionShape =>
      have signature := functionFacts.shape functionShape
      cases signature with
      | pi bodySignature =>
        obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Red.rigid functionReduced rfl)
        exact bodySignature.instantiate1 argument 0
  | _, _, .app functionExpr argument, _, .appSkip functionTyped functionReduced _ => by
    have functionFacts := infer_sort_function functionTyped
    refine ⟨?_⟩
    intro count sortLevel shape
    cases shape with
    | app functionShape =>
      have signature := functionFacts.shape functionShape
      cases signature with
      | pi bodySignature =>
        obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Red.rigid functionReduced rfl)
        exact bodySignature.instantiate1 argument 0
  | _, _, _, _, .fvar _ | _, _, _, _, .const .. | _, _, _, _, .natLit _
  | _, _, _, _, .strLit _ | _, _, _, _, .forallE .. | _, _, _, _, .proj .. => by
    refine ⟨?_⟩
    intro count sortLevel shape
    cases shape

private theorem infer_sort_function_red {md : Mode} {env : Env md} :
    ∀ {d : Nat} {a b : Expr md}, Red env d a b → True
  | _, _, _, _ => trivial

private theorem infer_sort_function_defeq {md : Mode} {env : Env md} :
    ∀ {d : Nat} {a b : Expr md}, DefEq env d a b → True
  | _, _, _, _ => trivial

private theorem infer_sort_function_certs {md : Mode} {env : Env md} :
    ∀ {d : Nat} {licensed : Bool} {ty : Expr md} {args : List (Expr md)}, Certs env d licensed ty args → True
  | _, _, _, _, _ => trivial

private theorem infer_sort_function_list {md : Mode} {env : Env md} :
    ∀ {d : Nat} {left right : List (Expr md)}, DefEqList env d left right → True
  | _, _, _, _ => trivial

private theorem infer_sort_function_eta {md : Mode} {env : Env md} :
    ∀ {d : Nat} {T : Key md} {us : List Level} {args : List (Expr md)} {body : Expr md}
      {levels : List LevelParam} {indices : List Nat}, EtaProjCerts env d T us args body levels indices → True
  | _, _, _, _, _, _, _, _ => trivial

end

/-- Actual inference retains the complete result-sort signature of the motive fragment. -/
theorem SortFunction.inferred_signature {md : Mode} {env : Env md} {grade : Grade} {depth count : Nat}
    {sortLevel : Level} {subject inferred : Expr md} (shape : SortFunction sortLevel count subject)
    (typed : Infer env grade depth subject inferred) : ProductSort (.succ sortLevel) count inferred :=
  (infer_sort_function typed).shape shape

theorem SortFunction.inferred_zero {md : Mode} {env : Env md} {grade : Grade} {depth : Nat}
    {sortLevel : Level} {subject inferred : Expr md} (shape : SortFunction sortLevel 0 subject)
    (typed : Infer env grade depth subject inferred) : inferred = .sort (.succ sortLevel) :=
  (shape.inferred_signature typed).zero_eq

theorem SortFunction.type_not_const {md : Mode} {env : Env md} {grade : Grade} {depth count : Nat}
    {sortLevel : Level} {e inferred reduced : Expr md} {name : Key md} {levels : List Level}
    (shape : SortFunction sortLevel count e) (typed : Infer env grade depth e inferred)
    (steps : Red env depth inferred reduced) (head : reduced.getAppFn = .const name levels) : False := by
  have signature := shape.inferred_signature typed
  have same := Red.rigid steps signature.rigid
  rw [same] at head
  cases signature <;> cases head

theorem SortFunction.type_not_unit {md : Mode} {env : Env md} {grade : Grade} {depth count : Nat}
    {sortLevel : Level} {e inferred reduced : Expr md}
    (shape : SortFunction sortLevel count e) (typed : Infer env grade depth e inferred)
    (steps : Red env depth inferred reduced) (unit : isUnitLikeTy env reduced = true) : False := by
  have signature := shape.inferred_signature typed
  have same := Red.rigid steps signature.rigid
  rw [same] at unit
  cases signature <;> cases unit

theorem SortFunction.not_proof {md : Mode} {env : Env md} {depth : Nat}
    {sortLevel proofLevel : Level} {e inferred inferredAgain : Expr md}
    (shape : SortFunction sortLevel 0 e) (typed : Infer env .io depth e inferred)
    (typedAgain : Infer env .io depth inferred inferredAgain)
    (sorted : Red env depth inferredAgain (.sort proofLevel))
    (zero : ∀ φ, proofLevel.eval φ = 0) : False := by
  rw [shape.inferred_zero typed] at typedAgain
  rw [Infer.sort_inv typedAgain] at sorted
  have proofLevelEq := Red.sort_eq sorted
  rw [proofLevelEq] at zero
  have impossible := zero (fun _ => 0)
  simp only [Level.eval] at impossible
  omega

end IxVM.Refinement.Decl
