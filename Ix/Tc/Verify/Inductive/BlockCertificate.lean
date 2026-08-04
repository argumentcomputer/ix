import Lean4Lean.Theory.Typing.InductiveCertificate

/-!
# Certified mutual-inductive block transactions

This is the Theory-only consumer boundary for Lean4Lean's L4L-08 block
generation certificate.  A mutual block is one atomic semantic transaction:
all family constants are inserted before any constructors, all constructors
before any recursors, and all recursors before the globally flattened iota
rules.  It must not be represented as a list of singleton transactions.

As with `CertifiedGenerationTransaction`, this module imports no executable
Lean4Lean verifier and mentions no Ix address, catalog, or checker state.
-/

namespace Ix.Tc

open Lean4Lean

/-- One successful proof-carrying block generation, together with the
well-formed Theory environment it extends. -/
structure CertifiedBlockGenerationTransaction (source : VInductDecl)
    (before after : VEnv) where
  certificate : source.BlockGenerationCertificate before
  success : before.addInductBlockCertified certificate = some after
  beforeWF : before.WF

/-- Stable Theory consequences of a successful block-wide transaction.
Every inventory is quantified over the complete retained source/generation;
no family-local truncation can satisfy this interface. -/
structure CertifiedBlockGenerationFacts {source : VInductDecl}
    (before after : VEnv)
    (certificate : source.BlockGenerationCertificate before) : Prop where
  envLE : before ≤ after
  afterWF : after.WF
  familyFresh : ∀ {family}, family ∈ source.types →
    before.constants family.name = none
  familyLookup : ∀ {family}, family ∈ source.types →
    after.constants family.name = some family.toVConstant
  ctorFresh : ∀ {constructor},
    constructor ∈ source.blockConstructorConstants →
      before.constants constructor.name = none
  ctorLookup : ∀ {constructor},
    constructor ∈ source.blockConstructorConstants →
      after.constants constructor.name = some constructor.toVConstant
  recursorFresh : ∀ {recursor},
    recursor ∈ certificate.generation.recursors →
      before.constants recursor.name = none
  recursorLookup : ∀ {recursor},
    recursor ∈ certificate.generation.recursors →
      after.constants recursor.name = some recursor.toVConstant
  ruleMem : ∀ {rule}, rule ∈ certificate.generation.generatedRules →
    after.defeqs rule

namespace CertifiedBlockGenerationTransaction

/-- Repackage Ix's historical transaction adapter as Lean4Lean's current
consumer certificate.  This is definitionally the same semantic input,
successful atomic transaction, and pre-environment WF proof; no second
generation run or compatibility axiom is introduced. -/
def toBlockCertificate {source : VInductDecl} {before after : VEnv}
    (tx : CertifiedBlockGenerationTransaction source before after) :
    source.BlockCertificate before after where
  semantic := tx.certificate
  success := tx.success
  beforeWF := tx.beforeWF

/-- Recover L4L-08's exact four-phase trace for the atomic block. -/
theorem trace {source : VInductDecl} {before after : VEnv}
    (tx : CertifiedBlockGenerationTransaction source before after) :
    Nonempty (VEnv.AddInductBlockGenerationTrace before after
      tx.certificate.generation) :=
  VEnv.addInductBlockCertified_trace tx.success

/-- Extend the declaration history with one genuine block-generation step. -/
theorem afterWF {source : VInductDecl} {before after : VEnv}
    (tx : CertifiedBlockGenerationTransaction source before after) :
    after.WF := by
  rcases tx.beforeWF with ⟨decls, hdecls⟩
  refine ⟨.induct source :: decls,
    hdecls.decl (.inductBlock tx.certificate.wf ?_)⟩
  simpa only [VEnv.addInductBlockCertified_eq_addInductBlockGeneration] using
    tx.success

/-- Project all stable family, constructor, recursor, rule, and environment
facts from the same successful trace. -/
theorem facts {source : VInductDecl} {before after : VEnv}
    (tx : CertifiedBlockGenerationTransaction source before after) :
    CertifiedBlockGenerationFacts before after tx.certificate := by
  rcases tx.trace with ⟨trace⟩
  exact {
    envLE := trace.le
    afterWF := tx.afterWF
    familyFresh := fun hfamily => trace.family_fresh hfamily
    familyLookup := fun hfamily => trace.family_lookup hfamily
    ctorFresh := fun hconstructor => trace.ctor_fresh hconstructor
    ctorLookup := fun hconstructor => trace.ctor_lookup hconstructor
    recursorFresh := fun hrecursor => trace.rec_fresh hrecursor
    recursorLookup := fun hrecursor => trace.rec_lookup hrecursor
    ruleMem := fun hrule => trace.rule_mem hrule
  }

end CertifiedBlockGenerationTransaction

end Ix.Tc
