import Lean4Lean.Theory.Typing.EnvLemmas

/-!
# Certified inductive-generation transactions

This module is the Theory-only consumer boundary for Lean4Lean's normalized
inductive-generation certificate.  It deliberately imports no
`Lean4Lean.Verify` module and mentions no Ix catalog, address, checker state,
or recursor-pattern relation.

`GenerationCertificate` proves that one exact normalized generation is
semantically valid in the input Theory environment.  A successful
`addInductCertified` equation then determines the atomic output environment.
The adapter below packages that data and derives precisely the stable Theory
facts that Ix will later combine with its own catalog and execution proofs.

In particular, this boundary does *not* construct `InductiveOracle`: a Theory
certificate cannot by itself establish which concrete Ix constants were
checked, how their addresses map to names, or that production iota metadata
matches the generated Theory rules.
-/

namespace Ix.Tc

open Lean4Lean

/-- One successful proof-carrying normalized inductive transaction, together
with the well-formed input environment needed to extend a Theory history.

This is a data-bearing structure rather than a proposition so the exact
certificate/generation remains available to downstream adapters. -/
structure CertifiedGenerationTransaction (source : VInductDecl)
    (before after : VEnv) where
  certificate : source.GenerationCertificate before
  success : before.addInductCertified certificate = some after
  beforeWF : before.WF

/-- The complete Theory-owned consequences of a certified generation
transaction.  All fields concern only the Lean4Lean source, generated
artifacts, and input/output `VEnv`s. -/
structure CertifiedGenerationFacts {source : VInductDecl}
    (before after : VEnv) (certificate : source.GenerationCertificate before) :
    Prop where
  envLE : before ≤ after
  afterWF : after.WF
  familyFresh :
    before.constants certificate.generation.block.sourceType.name = none
  familyLookup :
    after.constants certificate.generation.block.sourceType.name =
      some certificate.generation.block.sourceType.toVConstant
  ctorFresh : ∀ {ctor},
    ctor ∈ certificate.generation.block.sourceType.ctors →
      before.constants ctor.name = none
  ctorLookup : ∀ {ctor},
    ctor ∈ certificate.generation.block.sourceType.ctors →
      after.constants ctor.name = some ctor.toVConstant
  recursorFresh :
    before.constants
      (.str certificate.generation.block.sourceType.name "rec") = none
  recursorLookup :
    after.constants
      (.str certificate.generation.block.sourceType.name "rec") =
        some certificate.generation.recursor
  ruleMem : ∀ {rule}, rule ∈ certificate.generation.generatedRules →
    after.defeqs rule

namespace CertifiedGenerationTransaction

/-- Recover the exact, proof-irrelevant intermediate-state trace of the
certified atomic transaction. -/
theorem trace {source : VInductDecl} {before after : VEnv}
    (tx : CertifiedGenerationTransaction source before after) :
    Nonempty (VEnv.AddInductGenerationTrace before after
      tx.certificate.generation) :=
  VEnv.addInductCertified_trace tx.success

/-- Extend the input `VEnv.WF` history with the exact normalized inductive
declaration step carried by the certificate. -/
theorem afterWF {source : VInductDecl} {before after : VEnv}
    (tx : CertifiedGenerationTransaction source before after) : after.WF := by
  rcases tx.beforeWF with ⟨decls, hdecls⟩
  refine ⟨.induct source :: decls, hdecls.decl (.induct tx.certificate.wf ?_)⟩
  simpa only [VEnv.addInductCertified_eq_addInductGeneration] using tx.success

/-- Assemble every stable Theory consequence from the one successful trace.
No checker-specific provenance is introduced by this projection. -/
theorem facts {source : VInductDecl} {before after : VEnv}
    (tx : CertifiedGenerationTransaction source before after) :
    CertifiedGenerationFacts before after tx.certificate := by
  rcases tx.trace with ⟨trace⟩
  exact {
    envLE := trace.le
    afterWF := tx.afterWF
    familyFresh := trace.family_fresh
    familyLookup := trace.family_lookup
    ctorFresh := fun hctor => trace.ctor_fresh hctor
    ctorLookup := fun hctor => trace.ctor_lookup hctor
    recursorFresh := trace.rec_fresh
    recursorLookup := trace.rec_lookup
    ruleMem := fun hrule => trace.rule_mem hrule
  }

end CertifiedGenerationTransaction

end Ix.Tc
