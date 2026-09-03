import Ix.Tc.Verify.Check.PreTranslationCompatibility
import Ix.Tc.Verify.Inductive.BlockPatternSoundness
import Ix.Tc.Verify.Inductive.MutualFamily

/-!
# Generated recursors of a certified mutual block

This module contains the reusable, representation-neutral part of the second
physical block in Ix's mutual-inductive layout.  Lean4Lean installs all family
recursors and globally flattened equations in the original atomic source
transaction; Ix later checks a separately owned recursor block.  The lemmas
below retain the exact global generated-rule position while permitting each
physical recursor to dispatch by its family-local constructor index.
-/

namespace Ix.Tc

open Lean4Lean (VConstant VConstVal VDefEq VEnv VExpr VInductDecl)

namespace CertifiedMutualGeneration

/-- The globally flattened generated-rule list preserves the exact
constructor position supplied by `flatCtors`. -/
theorem generatedRuleAt {source : VInductDecl}
    (generation : source.BlockGenerationChecked) {index : Nat}
    {constructor : VInductDecl.NormalizedBlockCtor}
    (hconstructor : generation.flatCtors[index]? = some constructor) :
    generation.generatedRules[index]? =
      some (generation.rule index constructor) := by
  unfold VInductDecl.BlockGenerationChecked.generatedRules
  simp only [List.getElem?_map]
  rw [List.getElem?_zipIdx]
  simp [hconstructor]

/-- Every generated mutual equation remains headed by the recursor of its
constructor's owning family beneath the shared rule telescope. -/
theorem generatedRuleHead {source : VInductDecl}
    (generation : source.BlockGenerationChecked) (index : Nat)
    (constructor : VInductDecl.NormalizedBlockCtor) :
    HeadConstUnderLambdas (generation.ruleRecName constructor)
      (generation.rule index constructor).lhs := by
  unfold VInductDecl.BlockGenerationChecked.rule
  apply HeadConstUnderLambdas.lamN
  apply HeadConst.appN
  apply HeadConst.appN
  exact .const _

end CertifiedMutualGeneration

namespace CertifiedMutualRecursor

variable {source : VInductDecl} {before after : VEnv}

/-- Repackage Lean4Lean's exact generated RHS/check payload as the finite
pattern record consumed by Ix.  `ruleIndex` is family-local (the physical
dispatch index); `index` remains the global flattened equation position.
`argumentArity` is the one explicit representation equality connecting the
serialized parameter/field split to Lean4Lean's pattern arity. -/
def generatedPattern
    (certificate : source.BlockCertificate before after)
    {index : Nat} {constructor : VInductDecl.NormalizedBlockCtor}
    (entry : certificate.generation.ruleEntry index constructor)
    (constructorId : KId .anon) (ruleIndex : Nat)
    (constructorParams constructorFields : UInt64)
    (argumentArity : constructorParams.toNat + constructorFields.toNat =
      certificate.generation.ruleArgArity constructor) :
    RecursorRulePattern := by
  have patternEq :
      RecursorIotaPattern
          (certificate.generation.ruleRecName constructor)
          (certificate.generation.ruleMajorArity constructor)
          constructor.ctor.raw.name
          (constructorParams.toNat + constructorFields.toNat) =
        (certificate.generation.rulePattern constructor).toPattern := by
    rw [argumentArity]
    rfl
  exact {
    recursorName := certificate.generation.ruleRecName constructor
    constructorId := constructorId
    constructorName := constructor.ctor.raw.name
    constructorParams := constructorParams
    constructorFields := constructorFields
    ruleIndex := ruleIndex
    majorIdx := certificate.generation.ruleMajorArity constructor
    rhs := patternEq.symm ▸
      certificate.generation.ruleRHS certificate.ruleClosure entry
    checks := patternEq.symm ▸
      certificate.generation.ruleCheck certificate.ruleClosure
        (List.mem_of_getElem? entry) }

/-- The pending upstream consumer law transports directly to the exact Ix
pattern record; no physical metadata premise participates in soundness. -/
theorem generatedPattern_sound
    (certificate : source.BlockCertificate before after)
    (semantic : CertifiedBlockRulePatternSound certificate)
    {index : Nat} {constructor : VInductDecl.NormalizedBlockCtor}
    (entry : certificate.generation.ruleEntry index constructor)
    (constructorId : KId .anon) (ruleIndex : Nat)
    (constructorParams constructorFields : UInt64)
    (argumentArity : constructorParams.toNat + constructorFields.toNat =
      certificate.generation.ruleArgArity constructor) :
    (generatedPattern certificate entry constructorId ruleIndex
      constructorParams constructorFields argumentArity).Sound after := by
  have patternEq :
      RecursorIotaPattern
          (certificate.generation.ruleRecName constructor)
          (certificate.generation.ruleMajorArity constructor)
          constructor.ctor.raw.name
          (constructorParams.toNat + constructorFields.toNat) =
        (certificate.generation.rulePattern constructor).toPattern := by
    rw [argumentArity]
    rfl
  change CertifiedPatternPayloadSound after
    (RecursorIotaPattern
      (certificate.generation.ruleRecName constructor)
      (certificate.generation.ruleMajorArity constructor)
      constructor.ctor.raw.name
      (constructorParams.toNat + constructorFields.toNat))
    (patternEq.symm ▸
      certificate.generation.ruleRHS certificate.ruleClosure entry)
    (patternEq.symm ▸
      certificate.generation.ruleCheck certificate.ruleClosure
        (List.mem_of_getElem? entry))
  exact (CertifiedPatternPayloadSound.cast patternEq.symm (semantic entry))

/-- A physical RHS tied to one exact global rule entry inherits registration,
equation WF, and recursor-headedness from the completed block certificate. -/
theorem registeredRule
    (certificate : source.BlockCertificate before after)
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {id : KId .anon} {concrete : KConst .anon}
    {name : Lean.Name} {constant : VConstant}
    (recursorRaw : RawInductiveConstRel after nameOf trProj id concrete name
      constant)
    (recursorLookup : after.constants name = some constant)
    {index : Nat} {constructor : VInductDecl.NormalizedBlockCtor}
    (recursorName : name = certificate.generation.ruleRecName constructor)
    (entry : certificate.generation.ruleEntry index constructor)
    {concreteRule : RecRule .anon}
    (rhsRaw : RawExprRel
      (uvars := (certificate.generation.rule index constructor).uvars)
      after nameOf trProj [] concreteRule.rhs
      (certificate.generation.rule index constructor).rhs)
    (rhsTyped : TrKExprS after
      (certificate.generation.rule index constructor).uvars nameOf trProj []
      concreteRule.rhs
      (certificate.generation.rule index constructor).rhs) :
    RegisteredRecursorRuleRhsRel after nameOf trProj id concrete concreteRule
      (certificate.generation.rule index constructor) := by
  cases recursorName
  have facts := certificate.recursorRuleFacts entry
  exact ⟨_, constant, recursorRaw, recursorLookup, facts.registered,
    facts.wf,
    CertifiedMutualGeneration.generatedRuleHead certificate.generation index
      constructor,
    rhsRaw, rhsTyped⟩

/-- Combine independently proved finite production metadata with the one
upstream semantic pattern law. -/
theorem generatedPatternRel
    (certificate : source.BlockCertificate before after)
    (semantic : CertifiedBlockRulePatternSound certificate)
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {id : KId .anon} {concrete : KConst .anon}
    {rule : RecRule .anon}
    {index : Nat} {constructor : VInductDecl.NormalizedBlockCtor}
    (entry : certificate.generation.ruleEntry index constructor)
    (constructorId : KId .anon) (ruleIndex : Nat)
    (constructorParams constructorFields : UInt64)
    (argumentArity : constructorParams.toNat + constructorFields.toNat =
      certificate.generation.ruleArgArity constructor)
    (metadata : RawRecursorRulePatternMetadataRel catalog nameOf id concrete
      rule (generatedPattern certificate entry constructorId ruleIndex
        constructorParams constructorFields argumentArity)) :
    RawRecursorRulePatternRel after catalog nameOf id concrete rule
      (generatedPattern certificate entry constructorId ruleIndex
        constructorParams constructorFields argumentArity) :=
  RawRecursorRulePatternRel.of_metadata_sound metadata
    (generatedPattern_sound certificate semantic entry constructorId ruleIndex
      constructorParams constructorFields argumentArity)

end CertifiedMutualRecursor

end Ix.Tc
