import Compilatrix.IxIR2.WireCheck
import Compilatrix.IxIR2.Pipeline
import Compilatrix.IxIR2.CallReuse

/-!
# Canonical snapshots of the actual checked lowering

Export materializes the compiler's finite constructor table, including both
ownership worlds, exact layout preimages and scalar-leaf facts. Its decoded
context is extensionally the original checker context, not a caller-supplied
approximation. The suspended-call adapter records the actual selected body
and policy, including baseline fallback.
-/

namespace Compilatrix.IxIR2.Wire

open Compilatrix.Ixon (Address Owned)
open Compilatrix.IxIR

def baselineSchema (world : Owned) (info : Pipeline.ConstructorInfo) : Schema :=
  { world, constructor := info.identity
    definition :=
      { layout := Pipeline.baselineLayout world info.identity
        fields := Array.replicate info.arity world } }

def baselineSchemas (constructors : List Pipeline.ConstructorInfo) : List Schema :=
  constructors.flatMap fun info => [baselineSchema .unique info, baselineSchema .shared info]

def baselineLayouts (constructors : List Pipeline.ConstructorInfo) : List Layout :=
  constructors.flatMap fun info =>
    [ { identity := Pipeline.baselineLayout .unique info.identity
        preimage := Pipeline.baselineLayoutPreimage .unique info.identity }
    , { identity := Pipeline.baselineLayout .shared info.identity
        preimage := Pipeline.baselineLayoutPreimage .shared info.identity } ]

theorem baselineSchemas_lookup (constructors : List Pipeline.ConstructorInfo)
    (world : Owned) (constructor : CtorId) :
    ((baselineSchemas constructors).find? fun schema =>
      schema.world == world && schema.constructor == constructor).map (·.definition) =
        Pipeline.schema? constructors world constructor := by
  induction constructors with
  | nil => rfl
  | cons info rest ih =>
      change (List.find? _ ([baselineSchema .unique info, baselineSchema .shared info] ++
        baselineSchemas rest)).map (·.definition) = _
      cases world <;> by_cases same : info.identity = constructor
      · simp [baselineSchema, Pipeline.schema?, same,
          pure, bind, Option.bind]
      · simpa [baselineSchema, Pipeline.schema?, same, pure, bind, Option.bind] using ih
      · simp [baselineSchema, Pipeline.schema?, same,
          pure, bind, Option.bind]
      · simpa [baselineSchema, Pipeline.schema?, same, pure, bind, Option.bind] using ih

variable {world : Owned} {lowerFuel : Nat}

def ofCompiled (attached : Pipeline.CompiledAttachment world lowerFuel) : Artifact :=
  { policy :=
      { semantics := semanticsVersion, validator := validatorVersion
        lowering := "structured-ownership-lowering/1", passes := #[]
        layout := "baseline-constructor-world/0", credits := .callLocalV0
        allowExtern := attached.target.artifact.validationContext.allowExtern }
    dependencies := #[⟨"ixir1-graph", IxIR1.Optimizer.graphRoot
      attached.source.lowering.result.artifacts attached.source.lowering.result.main⟩]
    layouts := (baselineLayouts attached.sidecars.constructors).toArray
    schemas := (baselineSchemas attached.sidecars.constructors).toArray
    scalarLeaves := attached.target.artifact.validationContext.scalarLeaves.toArray
    program := attached.target.artifact.program }

theorem ofCompiled_program (attached : Pipeline.CompiledAttachment world lowerFuel) :
    (ofCompiled attached).program = attached.target.artifact.program := rfl

theorem ofCompiled_context (attached : Pipeline.CompiledAttachment world lowerFuel) :
    (ofCompiled attached).context = attached.target.artifact.validationContext := by
  have schemas : (ofCompiled attached).context.schemas =
      attached.target.artifact.validationContext.schemas := by
    rw [attached.targetSchemasProduced, attached.contextProduced]
    funext world constructor
    exact baselineSchemas_lookup attached.sidecars.constructors world constructor
  have leaves : (ofCompiled attached).context.scalarLeaves =
      attached.target.artifact.validationContext.scalarLeaves := by
    simp [Artifact.context, ofCompiled]
  have externs : (ofCompiled attached).context.allowExtern =
      attached.target.artifact.validationContext.allowExtern := rfl
  generalize leftEq : (ofCompiled attached).context = left at *
  generalize rightEq : attached.target.artifact.validationContext = right at *
  cases left
  cases right
  simp_all

theorem ofCompiled_validated (attached : Pipeline.CompiledAttachment world lowerFuel) :
    Validate.validateWithPolicy (ofCompiled attached).policy.credits Validate.defaultLimits
      (ofCompiled attached).context (ofCompiled attached).program = .ok attached.target.stats := by
  rw [ofCompiled_context, ofCompiled_program]
  exact attached.target.accepted

/-- Persistence followed by the public bounded reader preserves the exact
compiler-produced program and its complete ownership-checker context. -/
theorem ofCompiled_roundtrip (attached : Pipeline.CompiledAttachment world lowerFuel)
    (limits : Bounded.Limits) (fits : (ofCompiled attached).Fits limits) :
    Artifact.decodePreimage limits (ofCompiled attached).preimage = .ok (ofCompiled attached) ∧
      (ofCompiled attached).program = attached.target.artifact.program ∧
      (ofCompiled attached).context = attached.target.artifact.validationContext :=
  ⟨Artifact.decodePreimage_roundtrip limits _ fits, rfl, ofCompiled_context attached⟩

/-- A separately loaded root recovers the compiler's actual program and
context under the existing pairwise hash-collision premise. -/
theorem ofCompiled_matches (attached : Pipeline.CompiledAttachment world lowerFuel)
    {limits : Bounded.Limits} {bytes : ByteArray} {root : Address}
    (decoded : Addressed limits bytes root) (fits : (ofCompiled attached).Fits limits)
    (identity : (ofCompiled attached).address = root)
    (collision : Address.Blake3NoCollision decoded.artifact.preimage (ofCompiled attached).preimage) :
    decoded.artifact.program = attached.target.artifact.program ∧
      decoded.artifact.context = attached.target.artifact.validationContext := by
  rw [decoded.matches (ofCompiled attached) fits identity collision]
  exact ⟨rfl, ofCompiled_context attached⟩

def ofCallReuse (attached : Pipeline.CompiledAttachment world lowerFuel)
    {limits : Validate.Limits}
    (selection : CallReuse.Selection limits attached.target.artifact.validationContext
      attached.target.artifact.program) : Artifact :=
  let base := ofCompiled attached
  { base with
    policy :=
      { base.policy with
        credits := selection.policy
        passes := match selection with | .optimized .. => #[CallReuse.policyTag] | .baseline .. => #[] }
    program := selection.target }

theorem ofCallReuse_program (attached : Pipeline.CompiledAttachment world lowerFuel)
    {limits : Validate.Limits}
    (selection : CallReuse.Selection limits attached.target.artifact.validationContext
      attached.target.artifact.program) :
    (ofCallReuse attached selection).program = selection.target := rfl

theorem ofCallReuse_context (attached : Pipeline.CompiledAttachment world lowerFuel)
    {limits : Validate.Limits}
    (selection : CallReuse.Selection limits attached.target.artifact.validationContext
      attached.target.artifact.program) :
    (ofCallReuse attached selection).context = attached.target.artifact.validationContext :=
  ofCompiled_context attached

theorem ofCallReuse_validated (attached : Pipeline.CompiledAttachment world lowerFuel)
    {limits : Validate.Limits}
    (selection : CallReuse.Selection limits attached.target.artifact.validationContext
      attached.target.artifact.program) :
    ∃ stats, Validate.validateWithPolicy (ofCallReuse attached selection).policy.credits limits
      (ofCallReuse attached selection).context (ofCallReuse attached selection).program = .ok stats := by
  rw [ofCallReuse_context, ofCallReuse_program]
  exact selection.valid

theorem ofCallReuse_matches (attached : Pipeline.CompiledAttachment world lowerFuel)
    {validationLimits : Validate.Limits}
    (selection : CallReuse.Selection validationLimits attached.target.artifact.validationContext
      attached.target.artifact.program)
    {limits : Bounded.Limits} {bytes : ByteArray} {root : Address}
    (decoded : Addressed limits bytes root) (fits : (ofCallReuse attached selection).Fits limits)
    (identity : (ofCallReuse attached selection).address = root)
    (collision : Address.Blake3NoCollision decoded.artifact.preimage (ofCallReuse attached selection).preimage) :
    decoded.artifact.program = selection.target ∧ decoded.artifact.policy.credits = selection.policy ∧
      decoded.artifact.context = attached.target.artifact.validationContext := by
  rw [decoded.matches (ofCallReuse attached selection) fits identity collision]
  exact ⟨rfl, rfl, ofCallReuse_context attached selection⟩

end Compilatrix.IxIR2.Wire
