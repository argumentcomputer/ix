import IxVMRefinement.Decl.TelescopeFunctionResult
import IxVMRefinement.Decl.TypeConstructorMetadata

/-! # Actual minor checks for indexed uniform motives

The motive may bind any number of indices before its major premise. Its syntactic lambda
spine and the actual expected minor type provide the fixed-sort function fragment; the
minor's recorded inference and conversion then determine every returned product datum.
No model principal-sort property or satisfiability of the field context is required.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- A lambda telescope whose literal body is a sort is a uniform motive of that exact arity. -/
theorem SortFunction.of_stripLams {md : Mode} {count : Nat} {motive : Expr md}
    {binders : List (Expr md × BinderMeta)} {sortLevel : Level}
    (shape : motive.stripLams count = some (binders, .sort sortLevel)) : SortFunction sortLevel count motive := by
  induction count generalizing motive binders with
  | zero =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj shape)
    exact .sort
  | succ count ih =>
    cases motive with
    | lam domain body bm =>
      simp only [Expr.stripLams, Option.map_eq_some_iff] at shape
      obtain ⟨⟨tail, result⟩, bodyShape, same⟩ := shape
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact .lam (ih bodyShape)
    | _ => cases shape

/-- Applying all index and major arguments preserves the motive's fixed sort. -/
theorem SortFunction.uniform_motive_result {md : Mode} {motive : Expr md} {arguments : List (Expr md)}
    {binders : List (Expr md × BinderMeta)} {sortLevel : Level}
    (shape : motive.stripLams arguments.length = some (binders, .sort sortLevel)) :
    SortFunction sortLevel 0 (Expr.mkAppN motive arguments) := by
  apply SortFunction.apply_spine arguments
  simpa only [Nat.zero_add] using SortFunction.of_stripLams shape

/-- Actual dependent minor checking fixes a returned product's datum for the entire
constant-sort function fragment, including indexed motives with multiple applications. -/
theorem checked_uniform_minor_product_metadata {md : Mode} {env : Env md} {depth count : Nat}
    {minor minorType expectedType domain body expectedResult : Expr md}
    {minorBinders expectedBinders : List (Expr md × BinderMeta)} {productMeta : BinderMeta} {sortLevel : Level}
    (typed : Rules.Infer env .full depth minor minorType)
    (compared : Rules.DefEq env depth minorType expectedType)
    (minorShape : minor.stripLams count = some (minorBinders, .forallE domain body productMeta))
    (expectedShape : expectedType.stripPis count = some (expectedBinders, expectedResult))
    (motiveResult : SortFunction sortLevel 0 expectedResult) : productMeta.pw = Level.zeronessOf sortLevel := by
  obtain ⟨inferredBinders, inferredSort, inferredShape, metadata⟩ := infer_type_constructor_product typed minorShape
  have zero := converted_telescope_function_zero compared inferredShape expectedShape motiveResult
  exact metadata.symm.trans zero

/-- The actual expected motive application discharges the fixed-sort fragment directly. -/
theorem checked_uniform_motive_minor_metadata {md : Mode} {env : Env md} {depth count : Nat}
    {minor minorType expectedType domain body motive : Expr md} {arguments : List (Expr md)}
    {minorBinders expectedBinders motiveBinders : List (Expr md × BinderMeta)}
    {productMeta : BinderMeta} {sortLevel : Level}
    (typed : Rules.Infer env .full depth minor minorType)
    (compared : Rules.DefEq env depth minorType expectedType)
    (minorShape : minor.stripLams count = some (minorBinders, .forallE domain body productMeta))
    (expectedShape : expectedType.stripPis count = some (expectedBinders, Expr.mkAppN motive arguments))
    (motiveShape : motive.stripLams arguments.length = some (motiveBinders, .sort sortLevel)) :
    productMeta.pw = Level.zeronessOf sortLevel :=
  checked_uniform_minor_product_metadata typed compared minorShape expectedShape
    (SortFunction.uniform_motive_result motiveShape)

/-- The application constructs the minor typing and comparison consumed by the metadata proof. -/
theorem infer_uniform_minor_product_metadata {md : Mode} {env : Env md} {depth count : Nat}
    {functionExpr minor resultType domain body : Expr md}
    {minorBinders : List (Expr md × BinderMeta)} {productMeta : BinderMeta}
    (typed : Rules.Infer env .full depth (.app functionExpr minor) resultType)
    (minorShape : minor.stripLams count = some (minorBinders, .forallE domain body productMeta)) :
    ∃ functionType minorType expectedDomain resultBody functionMeta,
      Rules.Infer env .full depth functionExpr functionType ∧
      Rules.Red env depth functionType (.forallE expectedDomain resultBody functionMeta) ∧
      Rules.Infer env .full depth minor minorType ∧
      Rules.DefEq env depth minorType expectedDomain ∧
      ∀ expectedBinders expectedResult sortLevel,
        expectedDomain.stripPis count = some (expectedBinders, expectedResult) →
        SortFunction sortLevel 0 expectedResult → productMeta.pw = Level.zeronessOf sortLevel := by
  obtain ⟨functionType, expectedDomain, resultBody, functionMeta, minorType,
    functionTyped, functionReduced, minorTyped, compared, _⟩ := Rules.Infer.app_inv typed
  refine ⟨functionType, minorType, expectedDomain, resultBody, functionMeta,
    functionTyped, functionReduced, minorTyped, compared, ?_⟩
  intro expectedBinders expectedResult sortLevel expectedShape motiveResult
  exact checked_uniform_minor_product_metadata minorTyped compared minorShape expectedShape motiveResult

end IxVM.Refinement.Decl
