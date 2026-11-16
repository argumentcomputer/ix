import IxVMRefinement.Decl.TelescopeBetaResult
import IxVMRefinement.Decl.TypeConstructorMetadata

/-! # Product metadata from actual checked uniform-motive minors

A minor's lambda telescope may have arbitrary dependent domains. Its actual inference and
argument conversion fix a returned product's datum when the expected result is a constant
sort motive applied to a constructor expression. The constructor expression may be open
and its field context may be uninhabited; no semantic recursor-law typing is presumed.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- A minor returning a product receives its datum from its actual argument comparison. -/
theorem checked_minor_product_metadata {md : Mode} {env : Env md} {depth count : Nat}
    {minor minorType expectedType domain body expectedResult : Expr md}
    {minorBinders expectedBinders : List (Expr md × BinderMeta)} {productMeta : BinderMeta} {sortLevel : Level}
    (typed : Rules.Infer env .full depth minor minorType)
    (compared : Rules.DefEq env depth minorType expectedType)
    (minorShape : minor.stripLams count = some (minorBinders, .forallE domain body productMeta))
    (expectedShape : expectedType.stripPis count = some (expectedBinders, expectedResult))
    (motiveResult : SortBeta sortLevel expectedResult) : productMeta.pw = Level.zeronessOf sortLevel := by
  obtain ⟨inferredBinders, inferredSort, inferredShape, metadata⟩ := infer_type_constructor_product typed minorShape
  have zero := converted_telescope_beta_zero compared inferredShape expectedShape motiveResult
  exact metadata.symm.trans zero

/-- The application itself constructs the checked minor and its expected domain. Every uniform
motive shape subsequently read from that actual domain has the proved metadata correspondence. -/
theorem infer_minor_product_metadata {md : Mode} {env : Env md} {depth count : Nat}
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
        SortBeta sortLevel expectedResult → productMeta.pw = Level.zeronessOf sortLevel := by
  obtain ⟨functionType, expectedDomain, resultBody, functionMeta, minorType,
    functionTyped, functionReduced, minorTyped, compared, _⟩ := Rules.Infer.app_inv typed
  refine ⟨functionType, minorType, expectedDomain, resultBody, functionMeta,
    functionTyped, functionReduced, minorTyped, compared, ?_⟩
  intro expectedBinders expectedResult sortLevel expectedShape motiveResult
  exact checked_minor_product_metadata minorTyped compared minorShape expectedShape motiveResult

end IxVM.Refinement.Decl
