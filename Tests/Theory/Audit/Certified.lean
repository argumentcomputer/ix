/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean
import Ix.Theory.Certified

open Ix.Theory

/-!
# Certified mathematical dependency audit

This audit names the implemented checking, admission, and no-False roots.
The generated report includes theorem types so that explicit
mathematical hypotheses remain visible alongside the transitive axiom leaves.
-/

open Lean Lean.Elab Command

namespace Tests.Theory.Audit.Certified

def roots : Array Name := #[
  `Ix.Theory.Model.SetTheory.empty_exists,
  `Ix.Theory.Model.SetTheory.not_mem_empty,
  `Ix.Theory.VLevel.eval_inst,
  `Ix.Theory.Certified.PropWhen.eq_iff_holds,
  `Ix.Theory.Certified.validateZero?_sound,
  `Ix.Theory.Certified.zeroCondition_correct,
  `Ix.Theory.Certified.zeroCondition_inst,
  `Ix.Theory.Certified.instCondition_comp,
  `Ix.Theory.Model.readAnnotations?,
  `Ix.Theory.Model.interp_inst,
  `Ix.Theory.Model.interp_instL,
  `Ix.Theory.Model.interp_rename,
  `Ix.Theory.Model.piR_mem_univ,
  `Ix.Theory.Model.falseValue_uninhabited,
  `Ix.Theory.Model.falseElimValue_mem,
  `Ix.Theory.Certified.PrimitiveSignature.validate_iff,
  `Ix.Theory.Certified.readDefinition?,
  `Ix.Theory.Certified.LevelEq.check_sound,
  `Ix.Theory.Certified.LevelEq.leq_sound,
  `Ix.Theory.Model.wellDenoted_inst,
  `Ix.Theory.Model.wellDenoted_beta,
  `Ix.Theory.Model.extend_definition,
  `Ix.Theory.Model.ConversionClaim.equation,
  `Ix.Theory.Model.IndexedContainer.closed_exists,
  `Ix.Theory.Model.IndexedContainer.carrier_eq,
  `Ix.Theory.Model.IndexedContainer.induction,
  `Ix.Theory.Model.IndexedContainer.child_wellFounded,
  `Ix.Theory.Model.IndexedContainer.fold_node,
  `Ix.Theory.Model.IndexedContainer.fold_mem,
  `Ix.Theory.Model.IndexedContainer.small_elim,
  `Ix.Theory.Model.Telescope.applyN_curry,
  `Ix.Theory.Model.Telescope.curry_applyN,
  `Ix.Theory.Certified.verifyTelescope_sound,
  `Ix.Theory.Certified.verifyArguments_sound,
  `Ix.Theory.Certified.Ordinary.checkShape_sound,
  `Ix.Theory.Certified.Ordinary.checkLarge_sound,
  `Ix.Theory.Certified.Ordinary.Shape.container_wf,
  `Ix.Theory.Certified.Ordinary.Shape.constructorValue_mem,
  `Ix.Theory.Certified.Ordinary.Shape.decodeField_branches,
  `Ix.Theory.Certified.Ordinary.Shape.branches_decodeFields,
  `Ix.Theory.Certified.Ordinary.Shape.container_large,
  `Ix.Theory.Certified.Ordinary.Shape.largeValue_iota,
  `Ix.Theory.Certified.Ordinary.Shape.constructorType_interp,
  `Ix.Theory.Certified.Ordinary.Shape.recursorType_interp,
  `Ix.Theory.Certified.Ordinary.Shape.closedRecursorValue_mem_source,
  `Ix.Theory.Certified.Ordinary.Shape.produced_rule_eq,
  `Ix.Theory.Certified.Ordinary.checkBlock_sound,
  `Ix.Theory.Certified.Ordinary.Shape.publishedAssignment_realizes,
  `Ix.Theory.Certified.admitOrdinary?_extends,
  `Ix.Theory.Model.ConversionClaim.proofIrrel,
  `Ix.Theory.Certified.Basis.Equality.Interface.of_checked,
  `Ix.Theory.Certified.Basis.Equality.value_eq_eqv,
  `Ix.Theory.Certified.Basis.Iff.Interface.of_checked,
  `Ix.Theory.Certified.Basis.Iff.eq_of_mem,
  `Ix.Theory.Certified.Basis.Nonempty.Interface.of_checked,
  `Ix.Theory.Certified.Basis.Nonempty.value_eq_truthVal,
  `Ix.Theory.Certified.Standard.Spec.value_mem,
  `Ix.Theory.Certified.Standard.check_sound,
  `Ix.Theory.Certified.Standard.assignment_realizes,
  `Ix.Theory.Certified.admitStandard?_extends,
  `Ix.Theory.Model.SetTheory.quotSet_mem_univ,
  `Ix.Theory.Model.SetTheory.quotSound,
  `Ix.Theory.Certified.Signature.checkTypes_sound,
  `Ix.Theory.Certified.Signature.Formed.realizes,
  `Ix.Theory.Certified.Quotient.value_mem,
  `Ix.Theory.Certified.Quotient.liftValue_apply,
  `Ix.Theory.Certified.Quotient.liftRule_eq,
  `Ix.Theory.Certified.Quotient.check_sound,
  `Ix.Theory.Certified.Quotient.assignment_realizes,
  `Ix.Theory.Certified.admitQuotient?_extends,
  `Ix.Theory.Model.TypingClaim.fact,
  `Ix.Theory.Model.TypingClaim.natLit,
  `Ix.Theory.Model.TypingClaim.betaResult,
  `Ix.Theory.Model.ConversionClaim.natZero,
  `Ix.Theory.Model.ConversionClaim.natSucc,
  `Ix.Theory.Model.ConversionClaim.proj,
  `Ix.Theory.Certified.Structure.Description.projections_fit,
  `Ix.Theory.Certified.Structure.Description.constructor_eta,
  `Ix.Theory.Certified.Structure.Description.constructor_iota,
  `Ix.Theory.Certified.Structure.Description.projection_meaning,
  `Ix.Theory.Certified.Structure.Description.eta_eq,
  `Ix.Theory.Certified.Structure.Description.iota_eq,
  `Ix.Theory.Certified.Structure.check_sound,
  `Ix.Theory.Certified.Structure.Description.factAssignment_realizes,
  `Ix.Theory.Certified.Structure.Description.publishedAssignment_realizes,
  `Ix.Theory.Certified.admitStructure?_extends,
  `Ix.Theory.Certified.Natural.value_mem,
  `Ix.Theory.Certified.Natural.meaning,
  `Ix.Theory.Certified.Natural.check_sound,
  `Ix.Theory.Certified.Natural.assignment_realizes,
  `Ix.Theory.Certified.admitNatural?_extends,
  `Ix.Theory.Model.interp_mapRefs,
  `Ix.Theory.Model.wellDenoted_mapRefs,
  `Ix.Theory.Model.AExpr.mapRefs_restore,
  `Ix.Theory.Model.interp_mapRefs_restore,
  `Ix.Theory.Model.interp_mapRefs_permutation,
  `Ix.Theory.Model.wellDenoted_mapRefs_permutation,
  `Ix.Theory.Model.interp_mapRefs_merge,
  `Ix.Theory.Model.wellDenoted_mapRefs_merge,
  `Ix.Theory.Certified.Modeled.propositional_equation,
  `Ix.Theory.Certified.Modeled.checkEquation?_sound,
  `Ix.Theory.Certified.Modeled.CheckedCompanions.fixed_old,
  `Ix.Theory.Certified.Modeled.environment_wf,
  `Ix.Theory.Certified.Modeled.assignment_agrees,
  `Ix.Theory.Certified.Modeled.assignment_realizes,
  `Ix.Theory.Certified.Modeled.check?_sound,
  `Ix.Theory.Certified.Modeled.EntrySource.not_axiom,
  `Ix.Theory.Certified.Modeled.EntrySource.header,
  `Ix.Theory.Certified.checkModeledExtension?,
  `Ix.Theory.Certified.admitModeled?_extends,
  `Ix.Theory.Certified.PrimitiveSignature.compatible_assignment,
  `Ix.Theory.Certified.checkTypeCertified_sound,
  `Ix.Theory.Certified.defeqCertified_sound,
  `Ix.Theory.Certified.inferCertified_sound,
  `Ix.Theory.Certified.whnfCertified_sound,
  `Ix.Theory.Certified.admitDefinition?_extends,
  `Ix.Theory.Certified.checkStoreCertified,
  `Ix.Theory.Certified.accepted_store_has_model,
  `Ix.Theory.Certified.EntrySource.header,
  `Ix.Theory.Certified.CheckedStore.subject_sound,
  `Ix.Theory.Certified.accepted_store_source_sound,
  `Ix.Theory.Certified.checkDeclarationExtensions?,
  `Ix.Theory.Certified.CheckedExtension.admit,
  `Ix.Theory.Certified.checkFrontier?_refs,
  `Ix.Theory.Certified.CheckedFrontier.compatible,
  `Ix.Theory.Certified.ConditionalStore.subject_sound,
  `Ix.Theory.Certified.EntrySource.axiom_policy,
  `Ix.Theory.Certified.ConditionalStore.logical_axioms_authorized,
  `Ix.Theory.Certified.acceptsBatch,
  `Ix.Theory.Certified.CheckedBatch.closed_has_model,
  `Ix.Theory.Certified.CheckedBatch.compatible_leaves,
  `Ix.Theory.Certified.CheckedBatch.frontier_coverage,
  `Ix.Theory.Certified.DependencyOrder.before,
  `Ix.Theory.Certified.DependencyOrder.edge_for,
  `Ix.Theory.Certified.CheckedBatch.acyclic,
  `Ix.Theory.Certified.CheckedBatch.no_circular_discharge,
  `Ix.Theory.Certified.CheckedBatch.leaf_axiom_retained,
  `Ix.Theory.Certified.CheckedBatch.logicalUses_authorized,
  `Ix.Theory.Certified.checkBatch?_assoc,
  `Ix.Theory.Certified.CheckedBatch.no_False,
  `Ix.Theory.Certified.acceptsCertified,
  `Ix.Theory.Certified.accepted_has_model,
  `Ix.Theory.Certified.accepted_proof_sound,
  `Ix.Theory.Certified.no_proof_of_False,
  `Ix.Theory.Certified.no_proof_of_empty]

private def baseline : Array Name := #[`propext, `Classical.choice, `Quot.sound]

/-- Definitions whose logical content is hidden behind a name in a root's
pretty-printed type. Changes to their bodies must change the frozen report. -/
private def premiseDefinitions : Array Name := #[
  `Ix.Theory.Model.AExpr.mapRefs,
  `Ix.Theory.Certified.Modeled.EquationWitness.mk,
  `Ix.Theory.Certified.Modeled.EquationProof.propositional,
  `Ix.Theory.Certified.Modeled.CheckedEquation.mk,
  `Ix.Theory.Certified.Modeled.checkEquation?,
  `Ix.Theory.Certified.Modeled.Companion.mk,
  `Ix.Theory.Certified.Modeled.Companion.entry,
  `Ix.Theory.Certified.Modeled.mapping,
  `Ix.Theory.Certified.Modeled.CompanionChecked.mk,
  `Ix.Theory.Certified.Modeled.CheckedCompanions.mk,
  `Ix.Theory.Certified.Modeled.checkCompanions?,
  `Ix.Theory.Certified.Modeled.assignment,
  `Ix.Theory.Certified.Modeled.SourceMatches,
  `Ix.Theory.Certified.Modeled.sourceRefs?,
  `Ix.Theory.Certified.Modeled.sourceRules?,
  `Ix.Theory.Certified.Modeled.betaHead?,
  `Ix.Theory.Certified.Modeled.majorSource?,
  `Ix.Theory.Certified.Modeled.ruleSource?,
  `Ix.Theory.Certified.Modeled.Witness.mk,
  `Ix.Theory.Certified.Modeled.Checked.mk,
  `Ix.Theory.Certified.Modeled.EntrySource,
  `Ix.Theory.Model.Equinumerous, `Ix.Theory.Model.IsTGUniverse,
  `Ix.Theory.Model.SetTheory.mk,
  `Ix.Theory.Model.AExpr.Scope, `Ix.Theory.Model.Reading,
  `Ix.Theory.Certified.DefinitionReading.mk,
  `Ix.Theory.Certified.PrimitiveSignature.mk,
  `Ix.Theory.Certified.CheckedStore.mk,
  `Ix.Theory.Certified.SourceHeader.mk,
  `Ix.Theory.Certified.CheckedInterface.mk,
  `Ix.Theory.Certified.CheckedExtension.mk,
  `Ix.Theory.Certified.FrontierWitness.mk,
  `Ix.Theory.Certified.FrontierHeader.mk,
  `Ix.Theory.Certified.deferredSource,
  `Ix.Theory.Certified.CheckedFrontier.mk,
  `Ix.Theory.Certified.CheckedFrontier.interface,
  `Ix.Theory.Certified.HeaderPresent,
  `Ix.Theory.Certified.ConditionalStore.mk,
  `Ix.Theory.Certified.ClaimNode.mk,
  `Ix.Theory.Certified.CheckedNode.mk,
  `Ix.Theory.Certified.ReplayResult.mk,
  `Ix.Theory.Certified.CheckedBatch.mk,
  `Ix.Theory.Certified.DependencyOrder.nil,
  `Ix.Theory.Certified.DependencyOrder.cons,
  `Ix.Theory.Certified.DependencyEdge,
  `Ix.Theory.Certified.outstanding,
  `Ix.Theory.Certified.logicalAxioms,
  `Ix.Theory.Certified.CheckedBatch.logicalUses,
  `Ix.Theory.Model.WellDenoted, `Ix.Theory.Model.Context.Valid,
  `Ix.Theory.Model.TypingClaim, `Ix.Theory.Model.ConversionClaim,
  `Ix.Theory.Model.ConstantEntry.mk, `Ix.Theory.Model.Realizes.mk,
  `Ix.Theory.Model.ConstantEquation.mk,
  `Ix.Theory.Model.ConstantFact.typed,
  `Ix.Theory.Model.ConstantFact.natural,
  `Ix.Theory.Model.ConstantFact.Meaning,
  `Ix.Theory.Model.ConstantFact.Scope,
  `Ix.Theory.Model.ConstantFact.ReferencesIn,
  `Ix.Theory.Model.NaturalMeaning.mk,
  `Ix.Theory.Model.projectValue,
  `Ix.Theory.Model.Numeral.zero,
  `Ix.Theory.Model.Numeral.succ,
  `Ix.Theory.Model.Numeral.value,
  `Ix.Theory.Model.Environment.WF.mk, `Ix.Theory.Model.Assignment.AgreesOn,
  `Ix.Theory.Model.IndexedContainer.mk, `Ix.Theory.Model.IndexedContainer.WF.mk,
  `Ix.Theory.Model.IndexedContainer.LargeElim, `Ix.Theory.Model.IndexedContainer.AlgebraTyping,
  `Ix.Theory.Certified.TelescopeBound, `Ix.Theory.Certified.TelescopeProp,
  `Ix.Theory.Certified.ArgumentsFit,
  `Ix.Theory.Certified.Ordinary.Shape.mk,
  `Ix.Theory.Certified.Ordinary.Constructor.mk,
  `Ix.Theory.Certified.Ordinary.RecursiveField.mk,
  `Ix.Theory.Certified.Ordinary.CheckedShape.mk,
  `Ix.Theory.Certified.Ordinary.ConstructorEvidence,
  `Ix.Theory.Certified.Ordinary.RecursiveEvidence,
  `Ix.Theory.Certified.Ordinary.LargeEvidence,
  `Ix.Theory.Certified.Ordinary.Shape.container,
  `Ix.Theory.Certified.Ordinary.FamilyReading.mk,
  `Ix.Theory.Certified.Ordinary.ConstructorReading.mk,
  `Ix.Theory.Certified.Ordinary.RecursorReading.mk,
  `Ix.Theory.Certified.Ordinary.ModeEvidence,
  `Ix.Theory.Certified.Ordinary.Shape.ConstructorFormation,
  `Ix.Theory.Certified.Ordinary.Shape.RecursorFormation.mk,
  `Ix.Theory.Certified.Ordinary.Shape.SupportsK,
  `Ix.Theory.Certified.Ordinary.Shape.RecursorSourceMatches,
  `Ix.Theory.Certified.Ordinary.Shape.RuleFormation.mk,
  `Ix.Theory.Certified.Ordinary.CheckedBlock.mk,
  `Ix.Theory.Certified.Ordinary.EntrySource,
  `Ix.Theory.Certified.Ordinary.Shape.recursorAt,
  `Ix.Theory.Certified.Ordinary.BlockWitness.mk,
  `Ix.Theory.Certified.DeclarationWitness.definition,
  `Ix.Theory.Certified.DeclarationWitness.ordinary,
  `Ix.Theory.Certified.DeclarationWitness.standard,
  `Ix.Theory.Certified.DeclarationWitness.quotient,
  `Ix.Theory.Certified.DeclarationWitness.structure,
  `Ix.Theory.Certified.DeclarationWitness.natural,
  `Ix.Theory.Certified.Natural.shape,
  `Ix.Theory.Certified.Natural.fact,
  `Ix.Theory.Certified.Natural.entry,
  `Ix.Theory.Certified.Natural.environment,
  `Ix.Theory.Certified.Natural.Checked.mk,
  `Ix.Theory.Certified.Natural.EntrySource,
  `Ix.Theory.Certified.Structure.Field.mk,
  `Ix.Theory.Certified.Structure.Description.mk,
  `Ix.Theory.Certified.Structure.Description.ordinary,
  `Ix.Theory.Certified.Structure.FieldsFormed.nil,
  `Ix.Theory.Certified.Structure.FieldsFormed.cons,
  `Ix.Theory.Certified.Structure.fieldResult,
  `Ix.Theory.Certified.Structure.Description.facts,
  `Ix.Theory.Certified.Structure.Description.equations,
  `Ix.Theory.Certified.Structure.Description.iotaEnvironment,
  `Ix.Theory.Certified.Structure.Description.etaRule,
  `Ix.Theory.Certified.Structure.Description.iotaRule,
  `Ix.Theory.Certified.Structure.FactsWitness.mk,
  `Ix.Theory.Certified.Structure.Witness.mk,
  `Ix.Theory.Certified.Structure.FactsChecked.mk,
  `Ix.Theory.Certified.Structure.Checked.mk,
  `Ix.Theory.Certified.Structure.EntrySource,
  `Ix.Theory.Model.Environment.HasType,
  `Ix.Theory.Certified.Basis.Equality.Interface.mk,
  `Ix.Theory.Certified.Basis.Equality.shape,
  `Ix.Theory.Certified.Basis.Equality.type,
  `Ix.Theory.Certified.Basis.Equality.reflType,
  `Ix.Theory.Certified.Basis.Equality.recType,
  `Ix.Theory.Certified.Basis.Iff.Interface.mk,
  `Ix.Theory.Certified.Basis.Iff.shape,
  `Ix.Theory.Certified.Basis.Iff.type,
  `Ix.Theory.Certified.Basis.Iff.introType,
  `Ix.Theory.Certified.Basis.Iff.recType,
  `Ix.Theory.Certified.Basis.Nonempty.Interface.mk,
  `Ix.Theory.Certified.Basis.Nonempty.shape,
  `Ix.Theory.Certified.Basis.Nonempty.type,
  `Ix.Theory.Certified.Basis.Nonempty.introType,
  `Ix.Theory.Certified.Basis.Nonempty.recType,
  `Ix.Theory.Certified.Standard.Spec.Prerequisites,
  `Ix.Theory.Certified.Standard.Spec.type,
  `Ix.Theory.Certified.Standard.Spec.value,
  `Ix.Theory.Certified.Standard.chooseSet,
  `Ix.Theory.Certified.Standard.Witness.mk,
  `Ix.Theory.Certified.Standard.Checked.mk,
  `Ix.Theory.Certified.Standard.EntrySource,
  `Ix.Theory.Certified.Signature.Header.mk,
  `Ix.Theory.Certified.Signature.Formed.nil,
  `Ix.Theory.Certified.Signature.Formed.cons,
  `Ix.Theory.Certified.Signature.TypeWitness.mk,
  `Ix.Theory.Certified.Signature.Rule.mk,
  `Ix.Theory.Certified.Signature.RuleFormed.mk,
  `Ix.Theory.Certified.Signature.RuleWitness.mk,
  `Ix.Theory.Model.SetTheory.quotSet,
  `Ix.Theory.Model.SetTheory.quotClass,
  `Ix.Theory.Model.SetTheory.qrep,
  `Ix.Theory.Model.SetTheory.QuotRel.base,
  `Ix.Theory.Model.SetTheory.QuotRel.refl,
  `Ix.Theory.Model.SetTheory.QuotRel.symm,
  `Ix.Theory.Model.SetTheory.QuotRel.trans,
  `Ix.Theory.Certified.Quotient.Refs.mk,
  `Ix.Theory.Certified.Quotient.Refs.ExactSource,
  `Ix.Theory.Certified.Quotient.Refs.environment,
  `Ix.Theory.Certified.Quotient.Refs.assignment,
  `Ix.Theory.Certified.Quotient.Refs.entryType,
  `Ix.Theory.Certified.Quotient.Refs.source,
  `Ix.Theory.Certified.Quotient.Refs.equations,
  `Ix.Theory.Certified.Quotient.Reading.mk,
  `Ix.Theory.Certified.Quotient.Witness.mk,
  `Ix.Theory.Certified.Quotient.Checked.mk,
  `Ix.Theory.Certified.Quotient.EntrySource,
  `Ix.Theory.Certified.Quotient.formerValue,
  `Ix.Theory.Certified.Quotient.constructorValue,
  `Ix.Theory.Certified.Quotient.liftValue,
  `Ix.Theory.Certified.PrimitiveSignature.Compatible.mk,
  `Ix.Theory.Certified.EntrySource, `Ix.Theory.Certified.Extends.mk,
  `Ix.Theory.Certified.AdmittedEnvironment.mk,
  `Ix.Theory.Certified.CheckedClaim.mk,
  `Ix.Theory.Certified.InferenceResult.mk, `Ix.Theory.Certified.WhnfResult.mk,
  `Ix.Theory.Store.mk, `Ix.Theory.Certified.ProofInput.mk,
  `Ix.Theory.Certified.ProofWitness.mk, `Ix.Theory.Certified.CheckedProof.mk]

private def directConstants (info : ConstantInfo) : Array Name :=
  info.type.getUsedConstants ++ match info with
  | .thmInfo value => value.value.getUsedConstants
  | .defnInfo value => value.value.getUsedConstants
  | .opaqueInfo value => value.value.getUsedConstants
  | .inductInfo value => value.ctors.toArray
  | _ => #[]

private partial def closure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then closure env rest seen
    else match env.checked.get.find? name with
    | some info => closure env ((directConstants info).toList ++ rest) (seen.insert name)
    | none => closure env rest (seen.insert name)

private def axiomsIn (env : Environment) (dependencies : NameSet) : Array Name :=
  dependencies.toList.toArray.filter fun name =>
    match env.checked.get.find? name with
    | some (.axiomInfo _) => true
    | _ => false

private def forbiddenModule (name : Name) : Bool :=
  ((`Ix).isPrefixOf name && !(`Ix.Theory).isPrefixOf name) ||
  #[`Ix.Theory.Named, `Tests, `Benchmarks, `Ix.Theory.Fixtures, `Ix.Theory.Tests, `Ix.Theory.Harness,
    `Ix.Theory.Audit, `Ix.Theory.Typing.Conjectures,
    `Ix.Theory.Typing.UniqueTyping].any (·.isPrefixOf name)

run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let some boundary := modules.toList.idxOf? `Ix.Theory.Certified |
    throwError "certified audit: public target is missing"
  -- The audit's own Lean import is outside the certified boundary. Walk the
  -- mathematical import graph from that boundary. Meta-only tactic imports
  -- are tooling, and are outside this graph; proof constants remain audited.
  let mut pending := [boundary]
  let mut visited : List Nat := []
  while let index :: rest := pending do
    pending := rest
    unless visited.contains index do
      visited := index :: visited
      let name := modules[index]!
      if forbiddenModule name || (`Lean).isPrefixOf name then
        throwError m!"certified target imports forbidden module {name}"
      for dependency in env.header.moduleData[index]!.imports do
        unless dependency.isMeta do
          if let some depIndex := modules.toList.idxOf? dependency.module then
            pending := depIndex :: pending

  -- Freeze the foundational premise's complete fields. It must never acquire
  -- a field that postulates kernel acceptance or semantic soundness.
  let some foundation := getStructureInfo? env `Ix.Theory.Model.SetTheory |
    throwError "certified audit: SetTheory is missing"
  let expectedFields : Array Name := #[
    `Mem, `ext, `upair, `mem_upair, `sUnion, `mem_sUnion, `power, `mem_power,
    `regularity, `image, `mem_image, `univChain, `univChain_mem, `univChain_tg]
  unless foundation.fieldNames == expectedFields do
    throwError m!"certified audit: foundational fields changed: {foundation.fieldNames}"

  let mut declarations : Nat := 0
  let mut recursionWorkers : Array Name := #[]
  let mut projectDeclarations : List Name := []
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      if visited.contains index.toNat && (`Ix.Theory).isPrefixOf modules[index.toNat]! then
        declarations := declarations + 1
        projectDeclarations := name :: projectDeclarations
        -- Compiled replacements and unsafe implementations are a separate
        -- boundary from proof axioms. User-authored escapes are forbidden;
        -- the compiler's recursion workers are inventoried in full below.
        if (Lean.Compiler.getImplementedBy? env name).isSome || Lean.isExtern env name ||
            Lean.Elab.ComputedFields.computedFieldAttr.hasTag env name then
          throwError m!"certified declaration has an unreviewed runtime replacement: {name}"
        if let some replacement := (Lean.Compiler.CSimp.ext.getState env).map.find? name then
          throwError m!"certified declaration has an unreviewed csimp replacement: {name} -> {replacement.toDeclName}"
        if let some info := env.find? name then
          match info with
          | .defnInfo value =>
            unless value.safety == .safe do
              let some parent := Lean.Compiler.isUnsafeRecName? name |
                throwError m!"certified declaration is unsafe or partial: {name}"
              let some (.defnInfo original) := env.find? parent |
                throwError m!"recursion worker has no source definition: {name}"
              unless original.safety == .safe do
                throwError m!"recursion worker's source is not safe: {name}"
              recursionWorkers := recursionWorkers.push name
          | .opaqueInfo value =>
            if value.isUnsafe then throwError m!"certified opaque declaration is unsafe: {name}"
          | _ => pure ()
  unless declarations > 0 do throwError "certified audit measured no project declarations"

  -- Traverse the checked declarations, including every constructor field.
  -- Imported axiom summaries can omit dependencies of recursive groups.
  for axiomName in axiomsIn env (closure env projectDeclarations) do
    unless baseline.contains axiomName do
      throwError m!"certified foundation reaches unapproved axiom {axiomName}"

  for root in roots do
    let some info := env.find? root |
      throwError m!"certified audit: missing root {root}"
    let dependencies := closure env [root]
    unless dependencies.size > 1 do
      throwError m!"certified audit: empty dependency measurement for {root}"
    let type ← liftTermElabM <| Meta.ppExpr info.type
    let axioms := (axiomsIn env dependencies).qsort Name.lt
    let mut projectModules : NameSet := {}
    for dependency in dependencies.toList do
      if let some index := env.getModuleIdxFor? dependency then
        let moduleName := modules[index.toNat]!
        if (`Ix.Theory).isPrefixOf moduleName then
          projectModules := projectModules.insert moduleName
    let moduleRows := projectModules.toList.toArray.qsort Name.lt
    logInfo m!"certified root {root}\n  type: {type}\n  axioms: {axioms}\n  constants: {dependencies.size}\n  project modules: {moduleRows}"
  for name in premiseDefinitions do
    let some info := env.find? name |
      throwError m!"certified audit: missing premise definition {name}"
    let type ← liftTermElabM <| Meta.ppExpr info.type
    match info with
    | .defnInfo value =>
      let body ← liftTermElabM <| Meta.ppExpr value.value
      logInfo m!"premise definition {name}\n  type: {type}\n  definition: {body}"
    | .ctorInfo _ => logInfo m!"premise constructor {name}\n  type: {type}"
    | _ => throwError m!"certified audit: unclassified premise definition {name}"
  for name in recursionWorkers.qsort Name.lt do
    let some (.defnInfo value) := env.find? name |
      throwError m!"certified audit: missing recursion worker {name}"
    let type ← liftTermElabM <| Meta.ppExpr value.type
    let body ← liftTermElabM <| Meta.ppExpr value.value
    logInfo m!"compiler recursion worker {name}\n  type: {type}\n  implementation: {body}"
  logInfo m!"Certified project runtime audit OK: {recursionWorkers.size} compiler recursion workers inventoried; no other unsafe/partial declarations, extern, implemented_by, computed_field, or csimp replacements in the mathematical import graph"
  logInfo m!"Certified foundation audit OK: {declarations} declarations; {roots.size} named roots; explicit SetTheory hypothesis; baseline axioms only"

end Tests.Theory.Audit.Certified
