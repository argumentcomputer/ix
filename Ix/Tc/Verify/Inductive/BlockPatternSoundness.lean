import Ix.Tc.Verify.Inductive.BlockCertificate

/-!
# Consumer boundary for certified generated-pattern soundness

Lean4Lean's block certificate already identifies the exact generated pattern,
RHS template, checks, registered equation, and well-formed post-environment
for every flattened constructor.  The remaining consumer theorem says that a
well-typed match satisfying those checks is definitionally equal to that RHS
in every future environment.

This interface is deliberately stated entirely in Lean4Lean's Theory
vocabulary.  It carries no Ix address, catalog, ownership, ingress, or checker
claim, so a temporary upstream witness cannot discharge any downstream
correspondence obligation.
-/

namespace Ix.Tc

open Lean4Lean

/-- Environment-parametric soundness of one dependent pattern payload.
Keeping this independent of any certificate makes transport along an equality
of pattern indices explicit and reusable by representation adapters. -/
def CertifiedPatternPayloadSound (base : VEnv) (pattern : Pattern)
    (rhs : pattern.RHS) (checks : pattern.Check) : Prop :=
  ∀ ⦃future : VEnv⦄, base ≤ future → future.WF →
    ∀ ⦃uvars : Nat⦄ ⦃Gamma : List VExpr⦄ ⦃expression : VExpr⦄
      ⦃levels : List VLevel⦄ ⦃captures : pattern.Path → VExpr⦄ ⦃A : VExpr⦄,
      OnCtx Gamma (future.IsType uvars) →
      pattern.Matches expression levels captures →
      future.HasType uvars Gamma expression A →
      checks.OK (future.IsDefEqU uvars Gamma) levels captures →
      future.IsDefEqU uvars Gamma expression (rhs.apply levels captures)

namespace CertifiedPatternPayloadSound

/-- Dependent RHS/check payloads transport coherently when their pattern
index is rewritten. -/
theorem cast {base : VEnv} {left right : Pattern}
    {rhs : left.RHS} {checks : left.Check} (patternEq : left = right)
    (sound : CertifiedPatternPayloadSound base left rhs checks) :
    CertifiedPatternPayloadSound base right (patternEq ▸ rhs)
      (patternEq ▸ checks) := by
  cases patternEq
  exact sound

end CertifiedPatternPayloadSound

/-- The semantic rule promised by the pending consumer wrapper around
`BlockGenerationChecked.pat_wf`.

The certificate fixes the generated rule payload.  Quantification over future
well-formed environments is the exact monotonicity required by trusted-world
admission and later iota reduction. -/
def CertifiedBlockRulePatternSound
    {source : VInductDecl} {before after : VEnv}
    (certificate : source.BlockCertificate before after) : Prop :=
  ∀ ⦃i : Nat⦄ ⦃constructor : VInductDecl.NormalizedBlockCtor⦄,
    (entry : certificate.generation.ruleEntry i constructor) →
    CertifiedPatternPayloadSound after
      ((certificate.generation.rulePattern constructor).toPattern)
      (certificate.generation.ruleRHS certificate.ruleClosure entry)
      (certificate.generation.ruleCheck certificate.ruleClosure
        (List.mem_of_getElem? entry))

end Ix.Tc
