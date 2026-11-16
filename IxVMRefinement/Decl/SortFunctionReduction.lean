import IxVMRefinement.Decl.SortFunctionTyping

/-! # Reduction preserves uniform-motive arity and result sorts

The fragment may contain any number of lambdas and applications. Beta reduction consumes
one argument and preserves the remaining constant-sort function. Actual inference gives
only product or sort types, excluding the constructor rescues from this fragment.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Rules

private structure ReducedSortFunction {md : Mode} (left right : Expr md) : Prop where
  shape : ∀ {count : Nat} {sortLevel : Level}, SortFunction sortLevel count left → SortFunction sortLevel count right

mutual

private theorem reduce_sort_function {md : Mode} {env : Env md} :
    ∀ {depth : Nat} {left right : Expr md}, Red env depth left right → ReducedSortFunction left right
  | _, _, _, .refl => ⟨fun shape => shape⟩
  | _, _, _, .trans first second => by
    have firstFacts := reduce_sort_function first
    have secondFacts := reduce_sort_function second
    exact ⟨fun shape => secondFacts.shape (firstFacts.shape shape)⟩
  | _, _, _, .appFn functionReduced => by
    have functionFacts := reduce_sort_function functionReduced
    refine ⟨?_⟩
    intro count sortLevel shape
    cases shape with
    | app functionShape => exact .app (functionFacts.shape functionShape)
  | _, _, _, .appArg _ => by
    refine ⟨?_⟩
    intro count sortLevel shape
    cases shape with
    | app functionShape => exact .app functionShape
  | _, _, .app (.lam domain body bm) argument, _, .betaGate _ => by
    refine ⟨?_⟩
    intro count sortLevel shape
    cases shape with
    | app functionShape =>
      cases functionShape with
      | lam bodyShape => exact bodyShape.instantiate1 argument 0
  | _, _, .app (.lam domain body bm) argument, _, .beta _ _ => by
    refine ⟨?_⟩
    intro count sortLevel shape
    cases shape with
    | app functionShape =>
      cases functionShape with
      | lam bodyShape => exact bodyShape.instantiate1 argument 0
  | _, _, _, .delta unfolded => by
    refine ⟨?_⟩
    intro count sortLevel shape
    rw [shape.unfold_none] at unfolded
    cases unfolded
  | _, _, _, .eqProof head .. | _, _, _, .iota head .. => by
    refine ⟨?_⟩
    intro count sortLevel shape
    exact (shape.not_const_head _ _ head).elim
  | _, _, _, .rescueK _ _ _ _ _ typed reduced head ..
  | _, _, _, .rescueEta _ _ _ _ _ typed reduced head ..
  | _, _, _, .rescueAnd _ _ _ _ typed reduced head .. => by
    refine ⟨?_⟩
    intro count sortLevel shape
    exact (shape.type_not_const typed reduced head).elim
  | _, _, _, .deltaThm .. | _, _, _, .natZeroLit _ | _, _, _, .natSucc ..
  | _, _, _, .natOp .. | _, _, _, .natAddSucc .. | _, _, _, .natAddZero .. => by
    refine ⟨?_⟩
    intro count sortLevel shape
    exact (shape.not_const_head _ _ rfl).elim
  | _, _, _, .projArg _ | _, _, _, .natLit _ | _, _, _, .strLit _ | _, _, _, .proj .. => by
    refine ⟨?_⟩
    intro count sortLevel shape
    cases shape

private theorem reduce_sort_function_defeq {md : Mode} {env : Env md} :
    ∀ {d : Nat} {a b : Expr md}, DefEq env d a b → True
  | _, _, _, _ => trivial

private theorem reduce_sort_function_infer {md : Mode} {env : Env md} :
    ∀ {grade : Grade} {d : Nat} {e t : Expr md}, Infer env grade d e t → True
  | _, _, _, _, _ => trivial

private theorem reduce_sort_function_certs {md : Mode} {env : Env md} :
    ∀ {d : Nat} {licensed : Bool} {ty : Expr md} {args : List (Expr md)}, Certs env d licensed ty args → True
  | _, _, _, _, _ => trivial

private theorem reduce_sort_function_list {md : Mode} {env : Env md} :
    ∀ {d : Nat} {left right : List (Expr md)}, DefEqList env d left right → True
  | _, _, _, _ => trivial

private theorem reduce_sort_function_eta {md : Mode} {env : Env md} :
    ∀ {d : Nat} {T : Key md} {us : List Level} {args : List (Expr md)} {body : Expr md}
      {levels : List LevelParam} {indices : List Nat}, EtaProjCerts env d T us args body levels indices → True
  | _, _, _, _, _, _, _, _ => trivial

end

/-- Reduction preserves the actual fixed result sort and the number of pending arguments. -/
theorem SortFunction.reduced {md : Mode} {env : Env md} {depth count : Nat} {left right : Expr md}
    {sortLevel : Level} (shape : SortFunction sortLevel count left) (reduced : Red env depth left right) :
    SortFunction sortLevel count right := (reduce_sort_function reduced).shape shape

/-- Applying a correctly sized spine consumes exactly its remaining motive arguments. -/
theorem SortFunction.apply_spine {md : Mode} {count : Nat} {sortLevel : Level} (arguments : List (Expr md)) :
    ∀ {functionExpr : Expr md}, SortFunction sortLevel (count + arguments.length) functionExpr →
      SortFunction sortLevel count (Expr.mkAppN functionExpr arguments) := by
  induction arguments with
  | nil => intro functionExpr shape; exact shape
  | cons argument arguments ih =>
    intro functionExpr shape
    apply ih
    apply SortFunction.app
    simpa only [List.length_cons, Nat.add_succ] using shape

end IxVM.Refinement.Decl
