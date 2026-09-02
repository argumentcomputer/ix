import Ix.Tc.Verify.Inductive.Certificate
import Lean4Lean.Verify.Environment.ConstructorValidation

/-!
# Producer-linked inductive-generation transactions

`CertifiedGenerationTransaction` is intentionally Theory-only: it retains the
generation certificate and the exact `VEnv.addInductCertified` result, but it
does not remember which ordinary Lean4Lean metadata execution selected that
certificate.

For E2c we need both facts at once.  A successful outer producer call must not
be allowed to justify Theory semantics by itself, and an independently chosen
Theory certificate must not be passed off as the result of that producer.  The
record below therefore owns Lean4Lean's dependent
`ProducedGenerationCandidatePackage`, then erases it through the existing
Theory-only transaction only at the consumer boundary.
-/

namespace Ix.Tc

open Lean4Lean

/-- One exact producer-selected singleton package together with its successful
certified Theory insertion and well-formed input environment.

The package couples the executable `buildNormalizationCandidate` equation to
the semantic generation run.  The separate `success` field only executes the
certificate projected from that same package; it cannot substitute another
generation or caller-selected analyzer view. -/
structure ProducedGenerationTransaction (before after : VEnv)
    (Us : List Name) where
  package : VInductDecl.ProducedGenerationCandidatePackage before Us
  success :
    before.addInductCertified package.package.certificate = some after
  beforeWF : before.WF

namespace ProducedGenerationTransaction

/-- The exact source declaration owned by the producer-selected package. -/
def source {before after : VEnv} {Us : List Name}
    (tx : ProducedGenerationTransaction before after Us) : VInductDecl :=
  tx.package.package.source

/-- The Theory certificate projected from the exact produced package. -/
def certificate {before after : VEnv} {Us : List Name}
    (tx : ProducedGenerationTransaction before after Us) :
    tx.source.GenerationCertificate before :=
  tx.package.package.certificate

/-- Erase only the Verify-side producer provenance, preserving the exact
package-owned source, certificate, successful post-environment, and input WF
evidence in E2a's Theory-only transaction. -/
def toCertified {before after : VEnv} {Us : List Name}
    (tx : ProducedGenerationTransaction before after Us) :
    CertifiedGenerationTransaction tx.source before after where
  certificate := tx.certificate
  success := tx.success
  beforeWF := tx.beforeWF

@[simp] theorem toCertified_certificate {before after : VEnv}
    {Us : List Name} (tx : ProducedGenerationTransaction before after Us) :
    tx.toCertified.certificate = tx.certificate := rfl

@[simp] theorem toCertified_generation {before after : VEnv}
    {Us : List Name} (tx : ProducedGenerationTransaction before after Us) :
    tx.toCertified.certificate.generation =
      tx.package.package.generation := rfl

/-- Exact producer and semantic-transition facts retained at the E2c
boundary.  In particular, the outer producer equation and the Theory
certificate are projections of one dependent package rather than unrelated
premises. -/
structure Facts {before after : VEnv} {Us : List Name}
    (tx : ProducedGenerationTransaction before after Us) : Prop where
  produced :
    AddInductive.buildNormalizationCandidate tx.package.nparams
        [tx.package.package.kernelSource] tx.package.numNested
        tx.package.isUnsafe tx.package.context =
      .ok tx.package.package.candidate
  success : before.addInductCertified tx.certificate = some after
  generationWF : tx.package.package.generation.WF before
  envLE : before ≤ after
  afterWF : after.WF

/-- Project the complete coupled fact package.  Semantic consequences are
derived through `CertifiedGenerationTransaction`; the executable producer
equation contributes provenance only. -/
theorem facts {before after : VEnv} {Us : List Name}
    (tx : ProducedGenerationTransaction before after Us) : tx.Facts where
  produced := tx.package.produced
  success := tx.success
  generationWF := tx.certificate.wf
  envLE := tx.toCertified.facts.envLE
  afterWF := tx.toCertified.afterWF

end ProducedGenerationTransaction

/-! ## Exact dependent producer transactions -/

/-- The L4L-01E producer closure before source and generation indices are
erased.  Its type retains the exact raw family, kernel source, producer
arguments, normalized source declaration, and checked generation selected by
one successful outer candidate execution.

Downstream operational code can erase this record to
`ProducedGenerationTransaction`, but keeping it at the construction boundary
prevents a fixture from pairing one producer equation with another source or
generation that merely happens to have the same erased package type. -/
structure ExactProducedGenerationTransaction
    {source : VInductDecl} {raw : VInductiveType}
    {kernelSource : Lean.InductiveType} {numNested : Nat}
    {isUnsafe : Bool} {context : Lean4Lean.AddInductive.Context}
    (before after : VEnv) (Us : List Name)
    (producedCandidate : VInductDecl.ProducedGenerationShapeCandidate source
      raw kernelSource numNested isUnsafe context)
    (generation : source.GenerationChecked) where
  exactPackage : VInductDecl.ExactProducedGenerationCandidatePackage before Us
    producedCandidate generation
  success :
    before.addInductCertified
        exactPackage.package.package.certificate = some after
  beforeWF : before.WF

namespace ExactProducedGenerationTransaction

/-- Erase the dependent source/generation indices only at an explicit
consumer boundary. -/
noncomputable def toProduced
    {source : VInductDecl} {raw : VInductiveType}
    {kernelSource : Lean.InductiveType} {numNested : Nat}
    {isUnsafe : Bool} {context : Lean4Lean.AddInductive.Context}
    {before after : VEnv} {Us : List Name}
    {producedCandidate : VInductDecl.ProducedGenerationShapeCandidate source
      raw kernelSource numNested isUnsafe context}
    {generation : source.GenerationChecked}
    (tx : ExactProducedGenerationTransaction before after Us
      producedCandidate generation) :
    ProducedGenerationTransaction before after Us where
  package := tx.exactPackage.package
  success := tx.success
  beforeWF := tx.beforeWF

@[simp] theorem toProduced_source
    {source : VInductDecl} {raw : VInductiveType}
    {kernelSource : Lean.InductiveType} {numNested : Nat}
    {isUnsafe : Bool} {context : Lean4Lean.AddInductive.Context}
    {before after : VEnv} {Us : List Name}
    {producedCandidate : VInductDecl.ProducedGenerationShapeCandidate source
      raw kernelSource numNested isUnsafe context}
    {generation : source.GenerationChecked}
    (tx : ExactProducedGenerationTransaction before after Us
      producedCandidate generation) :
    tx.toProduced.source = source := rfl

@[simp] theorem toProduced_generation
    {source : VInductDecl} {raw : VInductiveType}
    {kernelSource : Lean.InductiveType} {numNested : Nat}
    {isUnsafe : Bool} {context : Lean4Lean.AddInductive.Context}
    {before after : VEnv} {Us : List Name}
    {producedCandidate : VInductDecl.ProducedGenerationShapeCandidate source
      raw kernelSource numNested isUnsafe context}
    {generation : source.GenerationChecked}
    (tx : ExactProducedGenerationTransaction before after Us
      producedCandidate generation) :
    tx.toProduced.certificate.generation = generation := rfl

/-- The same producer/semantic/environment facts remain available after the
intentional erasure. -/
theorem facts
    {source : VInductDecl} {raw : VInductiveType}
    {kernelSource : Lean.InductiveType} {numNested : Nat}
    {isUnsafe : Bool} {context : Lean4Lean.AddInductive.Context}
    {before after : VEnv} {Us : List Name}
    {producedCandidate : VInductDecl.ProducedGenerationShapeCandidate source
      raw kernelSource numNested isUnsafe context}
    {generation : source.GenerationChecked}
    (tx : ExactProducedGenerationTransaction before after Us
      producedCandidate generation) : tx.toProduced.Facts :=
  tx.toProduced.facts

end ExactProducedGenerationTransaction

end Ix.Tc
