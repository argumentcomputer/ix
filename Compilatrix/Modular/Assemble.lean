import Compilatrix.Modular.Check
import Compilatrix.PipelineSound

/-! Close independently checked units and enter the existing proved pipeline. -/

namespace Compilatrix.Modular

open Ixon (Address Constant Owned)

structure Program where
  constants : SourceEntries
  blobs : BlobEntries
  natBlock : Option Address

def Program.config (program : Program) (policy : Policy) : Pipeline.Config :=
  let index := AddressEnv.build program.blobs
  { blobs := AddressEnv.lookup index, natBlock := program.natBlock, limits := policy.unit }

def Program.source (program : Program) (policy : Policy) : Ixon.Eval.EvalCtx :=
  Pipeline.validatedEvalCtx program.constants (program.config policy)

structure Compiled (policy : Policy) (main : Address) (world : Owned) where
  program : Program
  source : Pipeline.ValidatedCompilation program.constants main (program.config policy)
    world policy.eraseFuel policy.lowerFuel

def Compiled.artifact {policy main world} (compiled : Compiled policy main world) :
    Pipeline.Artifact := compiled.source.artifact

/-- Aggregate accounting includes repeated imported environments. It runs
before the whole-program eraser, readdresser, or lowerer. -/
def programOf (limits : Limits) (policy : Policy) (units : List (CheckedUnit policy)) :
    Except String Program := do
  ensure (!units.isEmpty && units.length ≤ limits.maxUnits) "aggregate unit count limit"
  let constants := units.flatMap (·.input.constants)
  ensure ((constants.map (·.1)).eraseDups.length == constants.length)
    "duplicate ownership of a source constant"
  let names := units.map (·.input.name)
  ensure (names.eraseDups == names) "duplicate unit name"
  let stats := Ixon.Work.programStats constants
  ensure (stats.constants ≤ limits.maxConstants && proofObligations constants ≤ limits.maxCandidates &&
    stats.expandedExpressionUnits ≤ limits.maxExpandedUnits) "aggregate source size limit"
  let imported := units.foldl (fun total unit => total + unit.context.constants.length +
    unit.context.blobs.length + unit.context.declarations.length) 0
  ensure (imported ≤ limits.maxImportBindings) "aggregate import binding limit"
  let work := units.foldl (fun total unit => total +
    proofWork unit.input.constants unit.context.constants) 0
  ensure (work ≤ limits.maxCertificateWork) "aggregate certificate work limit"
  let bytes := units.foldl (fun total unit => total + unit.query.size +
    (IxIR.Encoding.list targetEntryBytes unit.output).size) 0
  ensure (bytes ≤ limits.maxBytes) "aggregate certificate byte limit"
  let blobs ← unionEntries (units.flatMap (·.input.blobs))
  let natBlock := units.head?.bind (·.input.natBlock)
  ensure (units.all (fun unit => unit.input.natBlock == natBlock)) "incompatible program Nat identities"
  let _ ← checked (Pipeline.preflightCompile policy.unit constants
    policy.checkFuel policy.eraseFuel policy.lowerFuel)
  return { constants, blobs, natBlock }

/-- Every imported `Covered` and member fact is transported to the actual
whole-program eraser output. The entry certificate and both downstream pass
traces are the original pipeline types. No monolithic source-certificate
discovery/checking pass is performed. -/
def assemble (limits : Limits) (policy : Policy) (units : List (CheckedUnit policy))
    (main : Address) (world : Owned := .shared) :
    Except String (Compiled policy main world) := do
  let program ← programOf limits policy units
  ensure ((candidates program.constants).contains main) "main is not an exported source declaration"
  let ectx := program.source policy
  let erasure ← (EraseAddressed.runWithTrace (EraseValidator.eraseCtxOf ectx)
    program.constants (.ref main) policy.eraseFuel).mapError (fun err => reprStr err)
  let context : Context := {
    constants := program.constants, blobs := program.blobs,
    declarations := erasure.result.raw, natBlock := program.natBlock }
  letI _scope : Sim.MemberScope := context.scope
  do
    let (coverage, packets) ← importedEvidence context units
    let members ← closeMembers context packets context.scope.plan
    let ictx : IxIR0.Ctx := { env := IxIR0.Env.ofList erasure.result.raw }
    have hsource : context.source = ectx := rfl
    have htarget : context.target = ictx := by
      exact congrArg (fun env => ({ env } : IxIR0.Ctx))
        (IxIR0.Env.Index.toEnv_ofList erasure.result.raw)
    let retainedCoverage : @EraseValidator.CoverageDB context.scope ectx.inlineSharing ictx := by
      rw [← hsource, ← htarget]
      exact coverage
    let entry ← (@EraseValidator.certifySharedClosedExpr context.scope ectx ictx
      (@EraseValidator.CoverageDB.oracle context.scope _ _ retainedCoverage)
      (Pipeline.validatedMainFrame main) Pipeline.validatedMainSource
      policy.eraseFuel policy.validateFuel).mapError (fun err => reprStr err)
    if hentry : entry.target == (.ref main : IxIR0.Expr) then
      let externsRejected : PLift (Pipeline.ValidatedExternsRejected erasure.result.declarations) ←
        match hboundary : Pipeline.firstValidatedExtern? erasure.result.declarations with
        | none => pure ⟨hboundary⟩
        | some _ => throw "assembled source violates the validated extern ownership ABI"
      let lowering ← (IxIR1.Lower.lowerAllIndexedFullyAddressedWithTrace
        erasure.result.declarations erasure.result.main world policy.lowerFuel).mapError
        (fun message => s!"assembled lowering: {message}")
      let targetExternsRejected : PLift (Pipeline.ValidatedTargetExternsRejected
          (lowering.result.artifacts.flatMap IxIR1.ReaddressAll.Artifact.declarations)) ←
        match hboundary : Pipeline.firstValidatedTargetExtern?
            (lowering.result.artifacts.flatMap IxIR1.ReaddressAll.Artifact.declarations) with
        | none => pure ⟨hboundary⟩
        | some _ => throw "assembled lowering violates the validated extern ownership ABI"
      let retainedMembers : @Sim.MemberCoverage context.scope ectx.inlineSharing ictx
          context.scope.plan := by
        rw [← hsource, ← htarget]
        exact members.down
      return {
        program
        source := {
          memberScope := context.scope, erasure, entry
          entryTarget := beq_iff_eq.mp hentry
          members := retainedMembers
          strict := ⟨rfl, rfl⟩
          externsRejected := externsRejected.down
          lowering, targetExternsRejected := targetExternsRejected.down } }
    else throw "assembled entry certificate differs from the selected main"

/-- The closed-program source preservation result follows from the assembled
unit facts. `SharingWF` is the same source premise as the monolithic theorem;
the fixed no-extern policy discharges its oracle premise. -/
theorem Compiled.sourcePreservation {policy main world}
    (compiled : Compiled policy main world) {fuel : Nat} {value : Ixon.Eval.Value}
    (contextWF : (compiled.program.source policy).SharingWF)
    (evaluated : Ixon.Eval.eval (compiled.program.source policy) fuel
      (Pipeline.validatedMainFrame main) [] Pipeline.validatedMainSource = .ok value) :
    ∃ targetFuel targetValue,
      IxIR0.eval compiled.source.rawCtx targetFuel [] (.ref main) = .ok targetValue ∧
      @Sim.InlinedValRel (compiled.program.source policy) compiled.source.rawCtx
        value targetValue compiled.source.memberScope := by
  letI : Sim.MemberScope := compiled.source.memberScope
  have frameWF : (Pipeline.validatedMainFrame main).SharingWF := by
    constructor
    · rfl
    · intro index member found
      simp [Pipeline.validatedMainFrame] at found
  have below : Ixon.Sharing.sharesBelow 0 Pipeline.validatedMainSource = true := rfl
  have inlined := Ixon.Eval.eval_inlineSharing contextWF frameWF .nil below evaluated
  have related := compiled.source.entry.related
  rw [EraseValidator.inlineTables_tablesOfFrame] at related
  have oracles : Sim.OracleRel (compiled.program.source policy).inlineSharing
      compiled.source.rawCtx := Sim.OracleRel.of_externFree (fun _ => rfl)
  obtain ⟨targetFuel, targetValue, targetEval, relatedValue⟩ := Sim.erasure_sim_with_members
    compiled.source.members oracles inlined.1 related (by
      simpa [Ixon.Eval.valuesInlineSharing, Program.source,
        Pipeline.ValidatedCompilation.rawCtx, EraseAddressed.Result.rawCtx] using
        (Sim.EnvRel.nil (ectx := (compiled.program.source policy).inlineSharing)
          (ictx := compiled.source.rawCtx)
          (refs := (Pipeline.validatedMainFrame main).inlineSharing.refs)
          (muts := (Pipeline.validatedMainFrame main).inlineSharing.selfMuts)
          (sa := (Pipeline.validatedMainFrame main).inlineSharing.selfAddr)))
  rw [compiled.source.entryTarget] at targetEval
  exact ⟨targetFuel, targetValue, targetEval, relatedValue⟩

end Compilatrix.Modular
