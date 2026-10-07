import IxC.Kernel.Audit.Axioms
import Ix.CompileCert.Entry
import Ix.CompileCert.StrongEntry
import Ix.CompileCert.StrongCone
import Ix.CompileCert.Indexed
import Ix.CompileCert.Canon
import Ix.CompileCert.Changed
import Ix.CompileCert.Conv
import Ix.CompileCert.Bridge

/-! # The compiler-certification lane's axiom audit

The frozen root list of `Ix.CompileCert` and its allowed axiom set. This module
fails elaboration when

* a root is missing (renamed, deleted, or no longer imported here), or the
  root list holds a duplicate;
* a root depends on any axiom outside the standard logical axioms
  (`propext`, `Classical.choice`, `Quot.sound`); `sorryAx` is an axiom, so a
  `sorry` anywhere below a root fails here too.

A root may depend on a subset of the three. The transitive axiom set is
computed by the certified gate's traversal `Ix.Kernel.Audit.collect`
(`IxC/Kernel/Audit/Axioms.lean`), which follows checked types, bodies and
constructor lists. The root list was frozen from the lane's last audit before
it moved onto `main`'s layout (597 roots, every one reporting a subset of the
three axioms). Run it with `lake run check-cert`, or build this module. -/

open Lean Elab Command

namespace Ix.CompileCert.Audit

/-- The axioms a root may depend on. -/
def allowedAxioms : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Fail unless every root exists, the list has no duplicate, and every root's
transitive axiom set is contained in `allowed`. On success, report the number
of roots and the union of their axioms. -/
def checkAuditRoots (roots : Array Lean.Name) (allowed : Array Lean.Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut seen : Lean.NameSet := {}
  let mut duplicates : Array Lean.Name := #[]
  let mut missing : Array Lean.Name := #[]
  let mut violations : Array MessageData := #[]
  let mut used : Array Lean.Name := #[]
  let mut cache : Ix.Kernel.Audit.Cache := {}
  for root in roots do
    if seen.contains root then
      duplicates := duplicates.push root
      continue
    seen := seen.insert root
    unless env.contains root do
      missing := missing.push root
      continue
    let (state, cache') := Ix.Kernel.Audit.collectCached env root cache
    cache := cache'
    for ax in state.axioms do
      unless used.contains ax do used := used.push ax
    let extra := state.axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      violations := violations.push m!"{root}: {extra}"
  unless duplicates.isEmpty do
    throwError m!"duplicate roots: {duplicates}"
  unless missing.isEmpty do
    throwError m!"required roots are missing: {missing}"
  unless violations.isEmpty do
    throwError m!"roots depend on axioms outside {allowed}:\n{MessageData.joinSep violations.toList "\n"}"
  logInfo m!"[cert-audit] {roots.size} roots; axioms used: {used.qsort Lean.Name.lt}"

/-- The frozen roots: the lane's soundness theorems, its checkers, and the
facts they are assembled from. -/
def roots : Array Lean.Name := #[
  `Ix.CompileCert.checkCompleteSource_sound,
  `Ix.CompileCert.checkMap_sound,
  `Ix.CompileCert.checkDirect_sound,
  `Ix.CompileCert.compatible_definition_fields,
  `Ix.CompileCert.SelectedSource.original,
  `Ix.CompileCert.faithful_sound,
  `Ix.CompileCert.checkRoots_coverage,
  `Ix.CompileCert.AdmittedArtifact.installed_exact,
  `Ix.CompileCert.AcceptedAssociation.has_model,
  `Ix.CompileCert.captureCone,
  `Ix.CompileCert.RawDefinitionAgrees.reader_decl,
  `Ix.CompileCert.AcceptedAssociation.raw_definition_reading,
  `Ix.CompileCert.AdmittedArtifact.checked_declarations,
  `Ix.CompileCert.AcceptedAssociation.direct_member_reading,
  `Ix.CompileCert.DefinitionGroupsCovered.member,
  `Ix.CompileCert.importUniv_eval,
  `Ix.CompileCert.exportUniv_eval,
  `Ix.CompileCert.checkedLevelImage_eval,
  `Ix.CompileCert.exportLevel_preserves_raw,
  `Ix.CompileCert.exportLevel_eval,
  `Ix.CompileCert.checkedLevelImage_subst_eval,
  `Ix.CompileCert.exportLevel_instantiated_eval,
  `Ix.CompileCert.exportExpr_bvarBound,
  `Ix.CompileCert.exportExpr_scoped,
  `Ix.CompileCert.exportExpr_noFvar,
  `Ix.CompileCert.exportExpr_lift,
  `Ix.CompileCert.exportExpr_instantiate,
  `Ix.CompileCert.exportExpr_rename,
  `Ix.CompileCert.kernelRenameAll_eq_renameConsts,
  `Ix.CompileCert.ixExpr_bvarBound,
  `Ix.CompileCert.ixToKernel_bvarBound,
  `Ix.CompileCert.ixToKernel_scoped_iff,
  `Ix.CompileCert.ixLevel_eval,
  `Ix.CompileCert.ixLevel_export_eval,
  `Ix.CompileCert.exportExprWith_target,
  `Ix.CompileCert.exportExprWith_bvarBound,
  `Ix.CompileCert.exportSourceExpr_bvarBound,
  `Ix.CompileCert.exportSourceLevel_eval,
  `Ix.CompileCert.SourceInstallation.has_model,
  `Ix.CompileCert.SourceInstallation.skels,
  `Ix.CompileCert.validateSourceGroups_sound,
  `Ix.CompileCert.exportSourceGroups_cover,
  `Ix.CompileCert.exportSourceDeclarations_groups,
  `Ix.CompileCert.SourceInstallation.groups,
  `Ix.CompileCert.orderSourceGroups_perm,
  `Ix.CompileCert.SourceInstallation.declarations_perm,
  `Ix.CompileCert.sourceName_injective,
  `Ix.CompileCert.exportSourceRule_sound,
  `Ix.CompileCert.exportSourceRules_positions,
  `Ix.CompileCert.exportSourceEntry_defn,
  `Ix.CompileCert.exportSourceEntry_thm,
  `Ix.CompileCert.exportSourceEntry_opaque,
  `Ix.CompileCert.exportSourceEntry_recursor,
  `Ix.CompileCert.exportSourceEntry_axiom,
  `Ix.CompileCert.exportSourceEntry_inductive,
  `Ix.CompileCert.exportSourceEntry_constructor,
  `Ix.CompileCert.exportSourceEntry_quotient,
  `Ix.CompileCert.SourceInstallation.member,
  `Ix.CompileCert.SourceInstallation.member_installed,
  `Ix.CompileCert.SourceBlockEvidence.original_member,
  `Ix.CompileCert.exportSourceBlockEvidence,
  `Ix.CompileCert.sourceModelBasisSupport_closed,
  `Ix.CompileCert.SourceModelInstallation.has_model,
  `Ix.CompileCert.SourceModelInstallation.has_model_values,
  `Ix.CompileCert.SourceModelInstallation.member,
  `Ix.CompileCert.SourceModelInstallation.original_decl,
  `Ix.CompileCert.sourceProjectionField_constructor,
  `Ix.CompileCert.sourceAppSpine_apps,
  `Ix.CompileCert.sourceProjectionCompute_constructor,
  `Ix.CompileCert.SourceNormalizedInstallation.has_model,
  `Ix.CompileCert.SourceNormalizedInstallation.has_model_values,
  `Ix.CompileCert.SourceProjectionNormalization.member,
  `Ix.CompileCert.SourceNormalizedInstallation.member,
  `Ix.CompileCert.SourceProjectionReceipt.constructor_computes,
  `Ix.CompileCert.SourceProjectionReceipt.original_fields,
  `Ix.CompileCert.strongInstalledModel_exists,
  `Ix.CompileCert.StrongInstalledModel.recursor_rule,
  `Ix.CompileCert.StrongInstalledModel.eq_sound,
  `Ix.CompileCert.SourceInstallation.strong_model,
  `Ix.CompileCert.SourceNormalizedInstallation.strong_model,
  `Ix.CompileCert.AdmittedArtifact.strong_model,
  `Ix.CompileCert.InstalledExprImage.denotes,
  `Ix.CompileCert.InstalledExprImage.symm,
  `Ix.CompileCert.InstalledExprImage.denotes_iff,
  `Ix.CompileCert.AnnotationTrace.header_fields,
  `Ix.CompileCert.AnnotationTrace.theorem_step,
  `Ix.CompileCert.AnnotationTrace.theorem_run,
  `Ix.CompileCert.AnnotationTrace.theorem_checked,
  `Ix.CompileCert.AnnotationTrace.TheoremInstalled.denotes,
  `Ix.CompileCert.installed_forall_elim,
  `Ix.CompileCert.SourceNormalizedInstallation.theorem_annotation,
  `Ix.CompileCert.SourceConstructorCoverChecked.annotation,
  `Ix.CompileCert.SourceConstructorCoverChecked.strong_model,
  `Ix.CompileCert.semanticConstructorCover_iff,
  `Ix.CompileCert.original_projection_extensional,
  `Ix.CompileCert.original_projection_function_extensional,
  `Ix.CompileCert.InstalledTelescope.apply,
  `Ix.CompileCert.InstalledTelescope.model_apply,
  `Ix.CompileCert.ValuationLift.push,
  `Ix.CompileCert.denotes_lift,
  `Ix.CompileCert.InstalledTelescope.lift,
  `Ix.CompileCert.InstalledBinderPrefix.inhabited,
  `Ix.CompileCert.installed_church_elim,
  `Ix.CompileCert.sourceForalls_transfer,
  `Ix.CompileCert.sourceForalls_lift,
  `Ix.CompileCert.sourceForalls_reflect_lift,
  `Ix.CompileCert.SourceCoverInstalledShape.constructor_member,
  `Ix.CompileCert.SourceCoverInstalledShape.theorem_member,
  `Ix.CompileCert.SourceCoverInstalledShape.constructor_apply,
  `Ix.CompileCert.installed_eq_implication_inhabited,
  `Ix.CompileCert.InstalledTelescope.final_valuation,
  `Ix.CompileCert.pushArguments_above,
  `Ix.CompileCert.pushArguments_append,
  `Ix.CompileCert.pushArguments_get,
  `Ix.CompileCert.DenotesSpine.of_get,
  `Ix.CompileCert.DenotesSpine.append,
  `Ix.CompileCert.denotes_mkAppN,
  `Ix.CompileCert.denotes_self_instance,
  `Ix.CompileCert.denotes_mkAppN_head,
  `Ix.CompileCert.sourceParameterVars_denotes,
  `Ix.CompileCert.sourceParameterVars_pushed,
  `Ix.CompileCert.SourceCoverInstalledShape.equality_denotes,
  `Ix.CompileCert.SourceCoverInstalledShape.equality_value,
  `Ix.CompileCert.SourceCoverInstalledShape.owner_member,
  `Ix.CompileCert.SourceCoverInstalledShape.owner_apply,
  `Ix.CompileCert.InstalledTelescope.read,
  `Ix.CompileCert.valuationLift_two,
  `Ix.CompileCert.denotes_forall_domain,
  `Ix.CompileCert.denotes_church_continuation,
  `Ix.CompileCert.liftSourceFieldDomains_length,
  `Ix.CompileCert.sourceForalls_binders,
  `Ix.CompileCert.SourceCoverInstalledShape.carrier_denotes,
  `Ix.CompileCert.SourceCoverInstalledShape.constructor_result_denotes,
  `Ix.CompileCert.SourceCoverInstalledShape.constructor_fields,
  `Ix.CompileCert.SourceCoverInstalledShape.constructor_typed,
  `Ix.CompileCert.SourceCoverInstalledShape.church,
  `Ix.CompileCert.SourceCoverInstalledShape.semantic_cover,
  `Ix.CompileCert.SourceCoverInstalledShape.constructor_presentation,
  `Ix.CompileCert.StrongInstalledModel.graded_eq_arguments,
  `Ix.CompileCert.StrongInstalledModel.graded_eq_sound,
  `Ix.CompileCert.InstalledTelescope.graded_reading,
  `Ix.CompileCert.StrongInstalledModel.graded_type,
  `Ix.CompileCert.StrongInstalledModel.graded_telescope,
  `Ix.CompileCert.StrongInstalledModel.graded_public_eq_sound,
  `Ix.CompileCert.StrongInstalledModel.theorem_eq,
  `Ix.CompileCert.InstalledTelescope.append,
  `Ix.CompileCert.SourceProjectionInstalled.typed_equation,
  `Ix.CompileCert.SourceProjectionInstalled.left_denotes,
  `Ix.CompileCert.SourceProjectionInstalled.right_denotes,
  `Ix.CompileCert.SourceProjectionInstalled.constructor_computation,
  `Ix.CompileCert.SourceProjectionInstalled.arbitrary_value,
  `Ix.CompileCert.SourceProjectionInstalled.definition_denotes,
  `Ix.CompileCert.originalProjectionSelection_reading,
  `Ix.CompileCert.SourceProjectionFunction.typed,
  `Ix.CompileCert.SourceProjectionFunction.value_eq,
  `Ix.CompileCert.SourceProjectionFunction.body_application_denotes,
  `Ix.CompileCert.AnnotationTrace.value_fields,
  `Ix.CompileCert.AnnotationTrace.prepared_value_fields,
  `Ix.CompileCert.AnnotationTrace.definition_step,
  `Ix.CompileCert.AnnotationTrace.definition_run,
  `Ix.CompileCert.AnnotationTrace.definition_checked,
  `Ix.CompileCert.AnnotationTrace.DefinitionInstalled.denotes,
  `Ix.CompileCert.AnnotationTrace.opaque_step,
  `Ix.CompileCert.AnnotationTrace.opaque_run,
  `Ix.CompileCert.AnnotationTrace.opaque_checked,
  `Ix.CompileCert.AnnotationTrace.checked_unique_names,
  `Ix.CompileCert.AnnotationTrace.unique_member,
  `Ix.CompileCert.AnnotationTrace.DefinitionInstalled.exact,
  `Ix.CompileCert.SourceProjectionInstalled.annotation,
  `Ix.CompileCert.AnnotationTrace.checked_header_fields,
  `Ix.CompileCert.AnnotationTrace.checked_definition_fields,
  `Ix.CompileCert.AnnotationTrace.checked_opaque_fields,
  `Ix.CompileCert.AnnotationTrace.checked_definition_decl,
  `Ix.CompileCert.AnnotationTrace.checked_opaque_decl,
  `Ix.CompileCert.AnnotationTrace.definition_all_step,
  `Ix.CompileCert.AnnotationTrace.opaque_all_step,
  `Ix.CompileCert.AnnotationTrace.definition_all_run,
  `Ix.CompileCert.AnnotationTrace.opaque_all_run,
  `Ix.CompileCert.AnnotationTrace.definition_all_checked,
  `Ix.CompileCert.AnnotationTrace.opaque_all_checked,
  `Ix.CompileCert.AnnotationTrace.DefinitionInstalledAll.exact,
  `Ix.CompileCert.AnnotationTrace.DefinitionInstalledAll.denotes,
  `Ix.CompileCert.AnnotationTrace.OpaqueInstalledAll.denotes,
  `Ix.CompileCert.SourceProjectionInstalled.annotation_all,
  `Ix.CompileCert.StrongInstalledModel.recursor_rhs,
  `Ix.CompileCert.StrongInstalledModel.recursor_computation,
  `Ix.CompileCert.DenotesSpine.take,
  `Ix.CompileCert.DenotesSpine.drop,
  `Ix.CompileCert.StrongInstalledModel.recursor_denotes,
  `Ix.CompileCert.AnnotatedApplication.internal_fit,
  `Ix.CompileCert.AnnotatedApplication.denotes_arguments,
  `Ix.CompileCert.AnnotatedApplication.residual_shape,
  `Ix.CompileCert.AnnotatedApplication.residual_scope,
  `Ix.CompileCert.AnnotatedApplication.denotes_residual,
  `Ix.CompileCert.StrongInstalledModel.instantiated_type,
  `Ix.CompileCert.AnnotatedApplication.installed_fit,
  `Ix.CompileCert.AnnotatedApplication.length,
  `Ix.CompileCert.FiredRecursorApplication.denotes,
  `Ix.CompileCert.InstalledRenaming.lift,
  `Ix.CompileCert.InstalledRenaming.instantiate1,
  `Ix.CompileCert.InstalledRenaming.instantiate1Lift,
  `Ix.CompileCert.InstalledRenaming.Laws.fiber,
  `Ix.CompileCert.InstalledRenaming.denotes,
  `Ix.CompileCert.ConstantSupport.mono,
  `Ix.CompileCert.ConstantSupport.lift,
  `Ix.CompileCert.ConstantSupport.instantiate1,
  `Ix.CompileCert.ConstantSupport.instantiate1Lift,
  `Ix.CompileCert.InstalledRenaming.denotes_on,
  `Ix.CompileCert.StrongInstalledModel.acyclic_definition_value,
  `Ix.CompileCert.AnnotationTrace.let_pure,
  `Ix.CompileCert.AnnotationTrace.let_cached,
  `Ix.CompileCert.AnnotationTrace.LetAnnotation.paired_residuals,
  `Ix.CompileCert.AnnotationTrace.ValueAnnotationCalls.let_trace,
  `Ix.CompileCert.AnnotationTrace.definition_prefix_run,
  `Ix.CompileCert.AnnotationTrace.definition_prefix_checked,
  `Ix.CompileCert.AnnotationTrace.DefinitionCheckedPrefix.let_trace,
  `Ix.CompileCert.AnnotationTrace.declaration_prefix_run,
  `Ix.CompileCert.AnnotationTrace.declaration_prefix_checked,
  `Ix.CompileCert.AnnotationTrace.CheckedDeclarationPrefix.definition,
  `Ix.CompileCert.AnnotationTrace.CheckedDeclarationPrefix.opaque_value,
  `Ix.CompileCert.AnnotationTrace.cached_pure,
  `Ix.CompileCert.AnnotationTrace.constant_pure,
  `Ix.CompileCert.AnnotationTrace.constant_cached,
  `Ix.CompileCert.AnnotationTrace.paired_constant_cached,
  `Ix.CompileCert.AnnotationTrace.application_pure,
  `Ix.CompileCert.AnnotationTrace.application_cached,
  `Ix.CompileCert.InstalledRenaming.abstract1,
  `Ix.CompileCert.AnnotationTrace.binder_pure,
  `Ix.CompileCert.AnnotationTrace.binder_cached,
  `Ix.CompileCert.AnnotationTrace.BinderAnnotationTrace.paired_image,
  `Ix.CompileCert.UniverseImage.eval,
  `Ix.CompileCert.UniverseImage.holds,
  `Ix.CompileCert.UniverseImage.regime,
  `Ix.CompileCert.UniverseImage.output_regime,
  `Ix.CompileCert.AnnotationTrace.BinderAnnotationTrace.semantic_image,
  `Ix.CompileCert.UniverseImage.select_level,
  `Ix.CompileCert.UniverseImage.select_datum,
  `Ix.CompileCert.UniverseImage.select_valuation,
  `Ix.CompileCert.UniverseImage.select_expr,
  `Ix.CompileCert.StrongInstalledModel.value_params,
  `Ix.CompileCert.PullbackMap.values_params,
  `Ix.CompileCert.PullbackTypeEvidence.model,
  `Ix.CompileCert.PullbackDefinitionEvidence.valueModel,
  `Ix.CompileCert.SourceInstallation.target_value_pullback,
  `Ix.CompileCert.SourceNormalizedInstallation.target_value_pullback,
  `Ix.CompileCert.insertValuation_at,
  `Ix.CompileCert.insertValuation_below,
  `Ix.CompileCert.insertValuation_above,
  `Ix.CompileCert.denotes_instantiate1Lift,
  `Ix.CompileCert.InstalledTelescope.instantiate1Lift,
  `Ix.CompileCert.DenotedApplication.of_telescope,
  `Ix.CompileCert.DenotedApplication.apply,
  `Ix.CompileCert.DenotesSpine.argumentVariables,
  `Ix.CompileCert.DenotedApplication.arbitrary_arguments,
  `Ix.CompileCert.closeN_under_binders,
  `Ix.CompileCert.closeN_substitution,
  `Ix.CompileCert.AnnotatedApplication.of_public,
  `Ix.CompileCert.ArgumentAnnotation.variable,
  `Ix.CompileCert.ArgumentAnnotations.variables,
  `Ix.CompileCert.argumentFVars_closed,
  `Ix.CompileCert.argumentReadings_values,
  `Ix.CompileCert.AnnotatedApplication.arbitrary_arguments,
  `Ix.CompileCert.StrongInstalledModel.arbitrary_installed_fit,
  `Ix.CompileCert.ValuationAgreement.push,
  `Ix.CompileCert.denotes_valuation,
  `Ix.CompileCert.InstalledTelescope.rebase,
  `Ix.CompileCert.ArgumentAnnotations.denotes,
  `Ix.CompileCert.ArgumentAnnotations.append,
  `Ix.CompileCert.ArgumentAnnotations.facts,
  `Ix.CompileCert.AnnotatedApplication.argument_annotations,
  `Ix.CompileCert.AnnotatedApplication.represented_arguments,
  `Ix.CompileCert.AnnotatedApplication.applied_argument,
  `Ix.CompileCert.PublicRecursorApplication.denotes,
  `Ix.CompileCert.InstalledExprImage.lift,
  `Ix.CompileCert.InstalledExprImage.instantiate1Lift,
  `Ix.CompileCert.InstalledTelescope.image,
  `Ix.CompileCert.InstalledSpineImage.append,
  `Ix.CompileCert.InstalledSpineImage.take,
  `Ix.CompileCert.InstalledSpineImage.drop,
  `Ix.CompileCert.InstalledSpineImage.mkAppN,
  `Ix.CompileCert.DenotedApplication.image,
  `Ix.CompileCert.levelSubst_get,
  `Ix.CompileCert.UniverseImage.telescope_instance,
  `Ix.CompileCert.checkTelescopes_sound,
  `Ix.CompileCert.PullbackMap.fromEnvs_locality,
  `Ix.CompileCert.PullbackMap.fromEnvs_constant,
  `Ix.CompileCert.InstalledExprImage.constant_equivalent_levels,
  `Ix.CompileCert.InstalledExprImage.natural,
  `Ix.CompileCert.InstalledExprImage.string,
  `Ix.CompileCert.checkInstalledConstant_sound,
  `Ix.CompileCert.bothChecks_true,
  `Ix.CompileCert.checkInstalledPins_sound,
  `Ix.CompileCert.checked_natural_image,
  `Ix.CompileCert.checked_string_image,
  `Ix.CompileCert.checkInstalledProjection_sound,
  `Ix.CompileCert.checkInstalledExpr_sound,
  `Ix.CompileCert.naturalConstructor_parameters,
  `Ix.CompileCert.stringConstructor_parameters,
  `Ix.CompileCert.InstalledExprImage.source_levels,
  `Ix.CompileCert.UniverseImage.telescope_recovery,
  `Ix.CompileCert.checkInstalledMemberExpr_sound,
  `Ix.CompileCert.UniverseImage.identity_level,
  `Ix.CompileCert.UniverseImage.identity_valuation,
  `Ix.CompileCert.checkInstalledTypes_member,
  `Ix.CompileCert.checkInstalledTypes_sound,
  `Ix.CompileCert.checkInstalledPin_sound,
  `Ix.CompileCert.checkedPullbackTypes,
  `Ix.CompileCert.checkInstalledDefinitions_member,
  `Ix.CompileCert.checkInstalledDefinitions_sound,
  `Ix.CompileCert.checkedStreams_publicValueModel,
  `Ix.CompileCert.InstalledSpineImage.sorts,
  `Ix.CompileCert.checkInstalledMemberExprs_sound,
  `Ix.CompileCert.checkInstalledFire_sound,
  `Ix.CompileCert.InstalledRulesImage.length,
  `Ix.CompileCert.InstalledRulesImage.at,
  `Ix.CompileCert.checkInstalledRules_sound,
  `Ix.CompileCert.checkInstalledRecursors_member,
  `Ix.CompileCert.checkInstalledRecursors_sound,
  `Ix.CompileCert.naturalConstructor_instantiateLevels,
  `Ix.CompileCert.stringConstructor_instantiateLevels,
  `Ix.CompileCert.InstalledExprImage.instantiateLevels,
  `Ix.CompileCert.PullbackMap.fromEnvs_instance,
  `Ix.CompileCert.PullbackMap.fromEnvs_constant_instance,
  `Ix.CompileCert.PullbackMap.fromEnvs_instantiated_image,
  `Ix.CompileCert.checkInstalledMemberExpr_instance,
  `Ix.CompileCert.checkInstalledRecursors_rhs_instance,
  `Ix.CompileCert.PublicRecursorApplication.pullback,
  `Ix.CompileCert.DenotesSpine.length,
  `Ix.CompileCert.DenotesSpine.functional,
  `Ix.CompileCert.DenotesSpine.image,
  `Ix.CompileCert.ArgumentAnnotation.app_inv,
  `Ix.CompileCert.ArgumentAnnotation.spine,
  `Ix.CompileCert.ArgumentAnnotation.index_pin,
  `Ix.CompileCert.ArgumentAnnotation.index_pin_image,
  `Ix.CompileCert.AnnotatedApplication.installed_residual,
  `Ix.CompileCert.InstalledExprImage.app_inv,
  `Ix.CompileCert.InstalledExprImage.spine_inv,
  `Ix.CompileCert.closeN_spine_inv,
  `Ix.CompileCert.ArgumentAnnotation.index_pin_of_residual_image,
  `Ix.CompileCert.DenotedApplication.arguments,
  `Ix.CompileCert.AnnotatedApplication.from_source,
  `Ix.CompileCert.AnnotatedApplication.from_checked_type,
  `Ix.CompileCert.AnnotatedApplication.installed_value_fit,
  `Ix.CompileCert.AnnotatedApplication.installed_unit,
  `Ix.CompileCert.AnnotatedApplication.installed_eta,
  `Ix.CompileCert.checkInstalledEtaFamily_sound,
  `Ix.CompileCert.checkInstalledCapabilities_member,
  `Ix.CompileCert.checkInstalledCapabilities_sound,
  `Ix.CompileCert.StrongInstalledModel.reserved_unit_name,
  `Ix.CompileCert.StrongInstalledModel.punit_value,
  `Ix.CompileCert.StrongInstalledModel.reserved_unit,
  `Ix.CompileCert.checked_unit_pullback,
  `Ix.CompileCert.checkInstalledFamilyMember_lookups,
  `Ix.CompileCert.checkInstalledFamilyMember_sound,
  `Ix.CompileCert.StrongInstalledModel.reserved_eta_name,
  `Ix.CompileCert.StrongInstalledModel.punit_unit_value,
  `Ix.CompileCert.StrongInstalledModel.reserved_eta,
  `Ix.CompileCert.etaFabArgsV_image,
  `Ix.CompileCert.checkInstalledEtaAt_sound,
  `Ix.CompileCert.checked_eta_pullback,
  `Ix.CompileCert.ArgumentAnnotations.parameters_image,
  `Ix.CompileCert.ArgumentAnnotations.take,
  `Ix.CompileCert.AnnotatedApplication.take,
  `Ix.CompileCert.AnnotatedApplication.readings,
  `Ix.CompileCert.AnnotatedApplication.installed_nested_pin,
  `Ix.CompileCert.ArgumentAnnotations.length,
  `Ix.CompileCert.instSeq_closed_bound,
  `Ix.CompileCert.instSeq_scoped,
  `Ix.CompileCert.ArgumentAnnotations.instSeq_annotation,
  `Ix.CompileCert.ArgumentAnnotation.denotes,
  `Ix.CompileCert.AnnotatedApplication.installed_nested_annotation,
  `Ix.CompileCert.InstalledSpineImage.instSeqLift,
  `Ix.CompileCert.closeN_instSeq,
  `Ix.CompileCert.InstalledSpineImage.closed_instSeq,
  `Ix.CompileCert.checkInstalledMemberExprs_instance,
  `Ix.CompileCert.InstalledSpineImage.get,
  `Ix.CompileCert.checkInstalledRuleUniverses_sound,
  `Ix.CompileCert.ArgumentAnnotations.get,
  `Ix.CompileCert.AnnotatedApplication.nested_parameter_image,
  `Ix.CompileCert.InstalledSpineImage.argumentVariables,
  `Ix.CompileCert.checked_unit_telescope,
  `Ix.CompileCert.checked_eta_telescope,
  `Ix.CompileCert.bothChecks_fold_true,
  `Ix.CompileCert.checkInstalledEtaAssociations_sound,
  `Ix.CompileCert.checkedCapabilities_publicLaws,
  `Ix.CompileCert.checkedStreams_publicCapabilities,
  `Ix.CompileCert.InstalledSpineImage.length,
  `Ix.CompileCert.checkInstalledRecursors_nested_pin_instance,
  `Ix.CompileCert.checkInstalledConstructors_member,
  `Ix.CompileCert.InstalledRuleFrame.target_constructor,
  `Ix.CompileCert.InstalledFireImage.fires,
  `Ix.CompileCert.readInstalledRuleFrame_complete,
  `Ix.CompileCert.InstalledRuleFrame.checked_target,
  `Ix.CompileCert.checkInstalledTypes_telescope,
  `Ix.CompileCert.InstalledRuleFrame.checked_tuple_typing,
  `Ix.CompileCert.ArgumentAnnotations.drop,
  `Ix.CompileCert.RuleTupleTyping.rebase,
  `Ix.CompileCert.RuleTupleTyping.represented,
  `Ix.CompileCert.RuleTupleRepresentation.constructor_application,
  `Ix.CompileCert.RuleTupleRepresentation.recursor_application,
  `Ix.CompileCert.RuleTupleRepresentation.plain_parameters,
  `Ix.CompileCert.InstalledSpineImage.symm,
  `Ix.CompileCert.DenotesSpine.get,
  `Ix.CompileCert.RuleTupleRepresentation.argument_image,
  `Ix.CompileCert.RuleTupleRepresentation.field_image,
  `Ix.CompileCert.RuleTupleRepresentation.source_readings,
  `Ix.CompileCert.RuleTupleRepresentation.prefix_application,
  `Ix.CompileCert.RuleTupleRepresentation.nested_parameter,
  `Ix.CompileCert.RuleTupleRepresentation.checked_index_pin,
  `Ix.CompileCert.InstalledRuleFrame.checked_universes,
  `Ix.CompileCert.InstalledRuleFrame.checked_images,
  `Ix.CompileCert.InstalledRuleFrame.checked_rhs_instance,
  `Ix.CompileCert.InstalledFireImage.plain_iff,
  `Ix.CompileCert.InstalledFireImage.nested_source,
  `Ix.CompileCert.InstalledRuleFrame.checked_nested_pins,
  `Ix.CompileCert.RuleTupleRepresentation.checked_application,
  `Ix.CompileCert.RuleTupleRepresentation.checked_fired,
  `Ix.CompileCert.checked_rules_simulation,
  `Ix.CompileCert.checkedStreams_publicRules,
  `Ix.CompileCert.checkInstalledOwnerLevels_instance,
  `Ix.CompileCert.levelEvalEqList_of_values,
  `Ix.CompileCert.levelSubst_values_eq,
  `Ix.CompileCert.InstalledRuleFrame.universeComparands_instance,
  `Ix.CompileCert.InstalledRuleFrame.checked_level_link,
  `Ix.CompileCert.InstalledRuleFrame.transfer_universe_selection,
  `Ix.CompileCert.TelescopeAssociation.target_instance_arity,
  `Ix.CompileCert.InstalledRuleFrame.transfer_selection,
  `Ix.CompileCert.checkInstalledRuleLevelLinks_frame,
  `Ix.CompileCert.checked_universal_rules,
  `Ix.CompileCert.checkedStreams_universalRules,
  `Ix.CompileCert.checkInstalledAssociation_sound,
  `Ix.CompileCert.checkedAssociation_universalRules,
  `Ix.CompileCert.checkArtifactInstalledAssociation_sound,
  `Ix.CompileCert.SourceInstallation.artifact_universalRules,
  `Ix.CompileCert.SourceNormalizedInstallation.artifact_universalRules,
  `Ix.CompileCert.InstalledTelescope.result_of_stripPis,
  `Ix.CompileCert.checked_constant_eq,
  `Ix.CompileCert.SourceProjectionInstalled.constructor_computation_pullback,
  `Ix.CompileCert.SourceProjectionInstalled.arbitrary_value_pullback,
  `Ix.CompileCert.SourceProjectionInstalled.arbitrary_value_checkedTarget,
  `Ix.CompileCert.SourceProjectionFunction.value_eq_pullback,
  `Ix.CompileCert.SourceProjectionFunction.body_application_denotes_pullback,
  `Ix.CompileCert.AdmittedSupport.strong_model,
  `Ix.CompileCert.AdmittedSupport.original_member,
  `Ix.CompileCert.SourceConstructorCoverChecked.supported_universalRules,
  `Ix.CompileCert.AdmittedSupport.original_universalRules,
  `Ix.CompileCert.AdmittedSupport.original_value,
  `Ix.CompileCert.InstalledAssociation.public_laws,
  `Ix.CompileCert.SourceConstructorCoverChecked.combined_publicModels,
  `Ix.CompileCert.SourceProjectionFunction.original_artifact_value,
  `Ix.CompileCert.RuleTupleTyping.represented_exact,
  `Ix.CompileCert.checked_public_recursors,
  `Ix.CompileCert.checkedStreams_publicSemanticModel,
  `Ix.CompileCert.sourceAndHelperNames_original,
  `Ix.CompileCert.SourceConstructorCoverChecked.combined_publicSemanticModels,
  `Ix.CompileCert.sourceSemanticBasisSupport_closed,
  `Ix.CompileCert.SourceSemanticBasisCompletion.original_prefix,
  `Ix.CompileCert.SourceSemanticBasisCompletion.support_closed,
  `Ix.CompileCert.SourceSemanticBasisCompletion.only_missing,
  `Ix.CompileCert.SourceNormalizedInstallation.normalized_prefix,
  `Ix.CompileCert.PullbackMap.fromEnvs_annotation_instance,
  `Ix.CompileCert.AnnotatedImage.reading,
  `Ix.CompileCert.AnnotatedImage.pullback,
  `Ix.CompileCert.checkInstalledProjection_annotated,
  `Ix.CompileCert.PullbackMap.fromEnvs_annotated_constant,
  `Ix.CompileCert.checkInstalledConstant_annotated,
  `Ix.CompileCert.PullbackMap.annotations_wellDenotedV,
  `Ix.CompileCert.PullbackMap.annotations_params,
  `Ix.CompileCert.installed_type_annotated_pullback,
  `Ix.CompileCert.AnnotatedSyntax.fvar,
  `Ix.CompileCert.AnnotatedSyntax.instantiate1,
  `Ix.CompileCert.AnnotatedSyntax.opened,
  `Ix.CompileCert.checkInstalledExpr_annotatedSyntax,
  `Ix.CompileCert.checkInstalledPins_annotated,
  `Ix.CompileCert.AnnotatedImage.constant_leaf,
  `Ix.CompileCert.checked_natural_annotations,
  `Ix.CompileCert.checked_string_annotations,
  `Ix.CompileCert.checkInstalledExpr_annotated,
  `Ix.CompileCert.denoteMeta_params_at,
  `Ix.CompileCert.checkInstalledMemberExpr_annotated_reading,
  `Ix.CompileCert.checkInstalledTypes_annotated,
  `Ix.CompileCert.checkInstalledDefinitions_annotated,
  `Ix.CompileCert.checkReservedNameMap_sound,
  `Ix.CompileCert.pulledAnnotatedBase,
  `Ix.CompileCert.pulledAnnotatedBase_valid,
  `Ix.CompileCert.pulledAnnotatedBase_types,
  `Ix.CompileCert.pulledAnnotatedBase_definitions,
  `Ix.CompileCert.checked_natural_annotations_of_flag,
  `Ix.CompileCert.checked_string_annotations_of_flag,
  `Ix.CompileCert.checkInstalledExpr_annotatedSyntax_local,
  `Ix.CompileCert.checkInstalledMemberExpr_annotated_reading_local,
  `Ix.CompileCert.checkInstalledTypes_annotated_local,
  `Ix.CompileCert.checkInstalledDefinitions_annotated_local,
  `Ix.CompileCert.checkAnnotatedAssociation_sound,
  `Ix.CompileCert.AnnotatedAssociation.modelCore,
  `Ix.CompileCert.checkedAnnotatedAssociation_core,
  `Ix.CompileCert.SourceConstructorCoverChecked.annotated_modelCore,
  `Ix.CompileCert.pulledAnnotatedBase_reserved,
  `Ix.CompileCert.pulledAnnotatedBase_eqLaw,
  `Ix.CompileCert.pulledAnnotatedBase_natHeads,
  `Ix.CompileCert.checkedAnnotatedAssociation_linked,
  `Ix.CompileCert.SourceConstructorCoverChecked.annotated_modelCore_linked,
  `Ix.CompileCert.AnnotatedAssociation.instantiated_type,
  `Ix.CompileCert.checkInstalledFamilyMember_annotations,
  `Ix.CompileCert.AnnotatedAssociation.unit_law,
  `Ix.CompileCert.AnnotatedAssociation.eta_law,
  `Ix.CompileCert.AnnotatedAssociation.caps_ok,
  `Ix.CompileCert.SourceConstructorCoverChecked.annotated_modelCore_caps,
  `Ix.CompileCert.literalReady_instantiateFVar,
  `Ix.CompileCert.literalReady_of_reading,
  `Ix.CompileCert.checkInstalledExpr_literal_support,
  `Ix.CompileCert.checkInstalledExpr_literal_support_of_readings,
  `Ix.CompileCert.checkInstalledMemberExpr_literal_support_of_readings,
  `Ix.CompileCert.checkTypeLiteralSupport_of_installed,
  `Ix.CompileCert.checkDefinitionLiteralSupport_of_installed,
  `Ix.CompileCert.checkAnnotatedAssociation_of_installed,
  `Ix.CompileCert.literalReady_instantiateLevels,
  `Ix.CompileCert.literalReady_openRev,
  `Ix.CompileCert.openRev_allLevelParamsDefined,
  `Ix.CompileCert.AnnotatedSyntax.openRev,
  `Ix.CompileCert.checkInstalledMemberExpr_opened_annotations,
  `Ix.CompileCert.checkInstalledRules_at,
  `Ix.CompileCert.AnnotatedAssociation.rule_rhs,
  `Ix.CompileCert.checkInstalledMemberExprs_getD,
  `Ix.CompileCert.checkInstalledMemberExpr_literal_support,
  `Ix.CompileCert.AnnotatedAssociation.nested_pin,
  `Ix.CompileCert.AnnotatedAssociation.member_instance_reading,
  `Ix.CompileCert.AnnotatedAssociation.opened_member_instance_reading,
  `Ix.CompileCert.AnnotatedAssociation.type_instance_reading,
  `Ix.CompileCert.AnnotatedAssociation.type_instance_teleFit,
  `Ix.CompileCert.InstalledRuleFrame.annotated_teleFit,
  `Ix.CompileCert.InstalledRuleFrame.checked_comparisons,
  `Ix.CompileCert.InstalledRuleFrame.annotated_rhs_instance,
  `Ix.CompileCert.pin_getD_allLevelParamsDefined,
  `Ix.CompileCert.InstalledRuleFrame.annotated_pin_instance,
  `Ix.CompileCert.AnnotatedAssociation.rec_rule,
  `Ix.CompileCert.AnnotatedAssociation.rec_rules,
  `Ix.CompileCert.SourceConstructorCoverChecked.annotated_modelCore_recursors,
  `Ix.CompileCert.checkInstalledTowerEntry,
  `Ix.CompileCert.InstalledTowerEntryComparison,
  `Ix.CompileCert.checkInstalledTowerEntry_sound,
  `Ix.CompileCert.checkInstalledTowers,
  `Ix.CompileCert.checkInstalledTowers_entry,
  `Ix.CompileCert.UniverseImage.telescope_instances_agree,
  `Ix.CompileCert.checkInstalledMemberSort_instance,
  `Ix.CompileCert.projTele_allLevelParamsDefined,
  `Ix.CompileCert.InstalledTowerEntryComparison.tower_law,
  `Ix.CompileCert.AnnotatedAssociation.tower_ok,
  `Ix.CompileCert.checkSupportedArtifactTowerAssociation,
  `Ix.CompileCert.SourceConstructorCoverChecked.annotated_modelCore_towers,
  `Ix.CompileCert.ValueEquationRequest,
  `Ix.CompileCert.ValueEquationRequest.type,
  `Ix.CompileCert.CheckedValueEquation,
  `Ix.CompileCert.ValueEquationEvidence,
  `Ix.CompileCert.CheckedValueEndpoints,
  `Ix.CompileCert.readCheckedValueEndpoints,
  `Ix.CompileCert.CheckedValueEndpoints.value_eq,
  `Ix.CompileCert.mappedValueRequest,
  `Ix.CompileCert.CheckedMappedValue,
  `Ix.CompileCert.readCheckedMappedValue,
  `Ix.CompileCert.CheckedMappedValue.value_eq,
  `Ix.CompileCert.CheckedReduceOperation,
  `Ix.CompileCert.readCheckedReduceOperation,
  `Ix.CompileCert.CheckedReduceOperation.law,
  `Ix.CompileCert.checkReduceOperationReceipts,
  `Ix.CompileCert.checkReduceOperationReceipts_entry,
  `Ix.CompileCert.AnnotatedAssociation.reduce_ops,
  `Ix.CompileCert.checkSupportedArtifactReduceAssociation,
  `Ix.CompileCert.SourceConstructorCoverChecked.annotated_modelCore_reduce,
  `Ix.CompileCert.divModValueNames,
  `Ix.CompileCert.divModClauses_values,
  `Ix.CompileCert.readCheckedCanonicalValue,
  `Ix.CompileCert.checkCanonicalValues,
  `Ix.CompileCert.checkCanonicalValues_entry,
  `Ix.CompileCert.checkCanonicalValues_values,
  `Ix.CompileCert.readCheckedDivModOperation,
  `Ix.CompileCert.CheckedDivModOperation.law,
  `Ix.CompileCert.checkDivModReceipts,
  `Ix.CompileCert.checkDivModReceipts_entry,
  `Ix.CompileCert.AnnotatedAssociation.div_mod,
  `Ix.CompileCert.readCheckedNatEquation,
  `Ix.CompileCert.CheckedNatEquation.readings,
  `Ix.CompileCert.checkNatEquationReceipts,
  `Ix.CompileCert.checkNatEquationReceipts_entry,
  `Ix.CompileCert.readCheckedNatOperation,
  `Ix.CompileCert.CheckedNatOperation.law,
  `Ix.CompileCert.checkNatOperationReceipts,
  `Ix.CompileCert.checkNatOperationReceipts_entry,
  `Ix.CompileCert.AnnotatedAssociation.nat_ops,
  `Ix.CompileCert.AnnotatedAssociation.strongInternal,
  `Ix.CompileCert.strongInstalledModelOfInternal,
  `Ix.CompileCert.checkSupportedArtifactStrongAssociation,
  `Ix.CompileCert.SourceConstructorCoverChecked.annotated_strong_model,
  `Ix.CompileCert.checkStrongAssociation,
  `Ix.CompileCert.checkedStrongAssociation,
  `Ix.CompileCert.checkSourceArtifactStrongAssociation,
  `Ix.CompileCert.SourceInstallation.artifact_strong_model]

end Ix.CompileCert.Audit

/-! ## Controls

Both rejection directions, each beside a passing neighbour: an axiom outside
the allowed set (`Classical.choice` itself, with `Classical.choice` not
allowed; `sorryAx`), and a missing root. -/

/-- info: [cert-audit] 1 roots; axioms used: [propext] -/
#guard_msgs in
run_cmd Ix.CompileCert.Audit.checkAuditRoots #[``propext] Ix.CompileCert.Audit.allowedAxioms

/--
error: roots depend on axioms outside [propext, Quot.sound]:
Classical.choice: [Classical.choice]
-/
#guard_msgs in
run_cmd Ix.CompileCert.Audit.checkAuditRoots #[``Classical.choice] #[``propext, ``Quot.sound]

/--
error: roots depend on axioms outside [propext, Classical.choice, Quot.sound]:
sorryAx: [sorryAx]
-/
#guard_msgs in
run_cmd Ix.CompileCert.Audit.checkAuditRoots #[``sorryAx] Ix.CompileCert.Audit.allowedAxioms

/-- error: required roots are missing: [Ix.CompileCert.Audit.noSuchRoot] -/
#guard_msgs in
run_cmd Ix.CompileCert.Audit.checkAuditRoots #[``propext, `Ix.CompileCert.Audit.noSuchRoot] Ix.CompileCert.Audit.allowedAxioms

/-- error: duplicate roots: [propext] -/
#guard_msgs in
run_cmd Ix.CompileCert.Audit.checkAuditRoots #[``propext, ``propext] Ix.CompileCert.Audit.allowedAxioms

/-! ## The audit -/

run_cmd Ix.CompileCert.Audit.checkAuditRoots Ix.CompileCert.Audit.roots Ix.CompileCert.Audit.allowedAxioms

/-! ## M3: the indexed check

The roots added by M3 (the metadata erasure lemmas and the indexed W check
behind the certifier), audited separately so the frozen line above is
unchanged. -/

namespace Ix.CompileCert.Audit

def m3Roots : Array Lean.Name :=
  #[`exportExpr_mdata, `exportExprWith_mdata,
    `nodup_map_inj, `find?_of_sub, `mem_of_hinted, `nodupBy, `nodupBy_sound, `nodup_of_nodupBy,
    `strideOf, `mem_strideOf, `allPar, `allPar_true,
    `mem_of_set, `set_contains_iff, `Refines, `throw_ne_ok, `Refines.rfl', `Refines.bind,
    `Refines.mapM, `Extends, `Extends.mapFind, `memberName_refines, `Refines.of_throw,
    `Refines.of_throw_bind, `Refines.forIn, `Refines.ite, `name_refines, `plainLevels_refines,
    `levels_refines, `exportLevel_context, `exportExpr_refines, `directExport_refines,
    `exportBlock_refines, `blockMatch_transfer, `optionMapM_transfer, `groupImage_transfer,
    `nameAgrees_transfer, `sourceRecordFlags_transfer, `smallContext, `smallContext_extends,
    `directAt, `directAt_sound, `rawAt, `rawAt_sound, `refsIn, `refsIn_sound, `declRefsIn,
    `declRefsIn_sound, `domainFast, `domainFast_sound, `AddressSet, `addressSet, `addressIn,
    `addressIn_set, `addressesNodup, `addressesNodup_sound, `coveredFast, `coveredFast_eq,
    `Hints, `Shared, `Shared.small, `Shared.declCheck, `Shared.entryCheck, `Shared.ofArtifact,
    `Shared.small_extends, `checkIndexed, `AcceptedAssociation.faithful,
    `checkIndexed_sound].map (`Ix.CompileCert ++ ·)

end Ix.CompileCert.Audit

run_cmd Ix.CompileCert.Audit.checkAuditRoots Ix.CompileCert.Audit.m3Roots Ix.CompileCert.Audit.allowedAxioms

/-! The roots added by KB: the projection lowering receipt
(`Ix/CompileCert/SourceProjectionLowering.lean`), the normalised route that
requires it, and the S endpoint over the original declarations through it
(`StrongEntry.lean`). Checked the same way, against the same allowed set. -/

namespace Ix.CompileCert.Audit

def kbRoots : Array Lean.Name :=
  #[`loweringStatement, `loweredLevel, `lambdaDomains, `piDomains, `sourceProjectionRecipe,
    `projectionSourceValue, `entryDeclaration, `declarationParts, `replaceValue,
    `SourceProjectionLowering, `checkSourceProjectionLowering, `declarationParts_replaceValue,
    `SourceProjectionLowering.faithful, `proposeSourceProjection, `proposeSourceProof,
    `SourceProjectionNormalization, `normalizeSourceProjections, `installSourceNormalized,
    `SourceProjectionNormalization.member, `SourceNormalizedInstallation.member,
    `checkNormalizedArtifactStrongAssociation,
    `SourceNormalizedInstallation.artifact_strong_model].map (`Ix.CompileCert ++ ·)

end Ix.CompileCert.Audit

run_cmd Ix.CompileCert.Audit.checkAuditRoots Ix.CompileCert.Audit.kbRoots Ix.CompileCert.Audit.allowedAxioms

/-! The roots added by M4 (d): S restated for every target model, the certifier's
per-cone decision and what an S-Certified verdict implies (`StrongCone.lean`),
and the stored-family gate of the eta associations (`RuleLaws.lean`). Checked
the same way, against the same allowed set. -/

namespace Ix.CompileCert.Audit

def m4dRoots : Array Lean.Name :=
  #[`SourceNormalizedInstallation.artifact_strong_model_all, `admittedSupportEmpty, `admitSupport,
    `installSourceNormalizedWith, `installSourceNormalizedComplete, `StrongCone, `StrongProposal, `decideStrongCone, `StrongCone.sound,
    `decideStrongCone_sound,
    `checkInstalledEtaFamily_complete, `checkInstalledEtaAssociations_sound,
    `checkedCapabilities_publicLaws, `AnnotatedAssociation.eta_law,
    `AnnotatedAssociation.caps_ok].map (`Ix.CompileCert ++ ·)

end Ix.CompileCert.Audit

run_cmd Ix.CompileCert.Audit.checkAuditRoots Ix.CompileCert.Audit.m4dRoots Ix.CompileCert.Audit.allowedAxioms

/-! The roots added by M7 L1 (WP-D, `plans/PLAN-proofs.md`): Pass 1 proved
(`Ix/CompileCert/Canon/**`, theorems about `Ix/Compile/Canon/**` as it is). WP-E (2026-10-07)
adds the block driver, the nested auxiliaries' discovery order, evaporation, the block name map
and the clique statements, over the functions the hashing change cleared. Checked the same way,
against the same allowed set; the frozen line above is unchanged. -/

namespace Ix.CompileCert.Audit

def l1Roots : Array Lean.Name :=
  #[`Le, `PreOn, `TotalPre, `PreOn.cmpM, `PreOn.lexIf, `PreOn.ofTag, `PreOn.zipCtx,
    `instLawfulBEqOrderingIx, `PreOn.ofSize,
    `transCmp_compareUniv, `compareLevelSyn_total, `compareLevel_total, `compareLevels_total,
    `AddrCongr, `name_beq_iff, `nameCompare_eq_iff, `transCmp_nameCompare, `transCmp_address,
    `mutCtx_getElem?_congr, `compareRef_total,
    `transCmp_literal, `ehd, `eC, `compareExpr_strip, `compareExpr_bad, `compareExpr_diff,
    `compareExpr_total,
    `transCmp_defKind, `ctorP, `indP, `constP, `compareDef_total, `ctorP_total, `indP_total,
    `compareRecr_total, `constP_total, `compareConstBody_today_mixed,
    `ResRel, `compareExpr_rel, `constP_rel, `StrongRel, `SameDom, `constP_strong, `ctorP_strong,
    `EqRel, `Coarser, `constP_eq_mono,
    `Ent, `ents, `NameInj, `entP, `Run, `Coh, `Sim, `cacheGet_spec, `cachePut_coh,
    `compareCtor_sim, `compareInd_sim, `compareConstBody_sim, `compareConstIn_sim, `constOrd,
    `compareConst_sim, `compareFresh_eq, `liftOrd, `constOrd_total, `compareFresh_total,
    `cacheGet_today_reversed,
    `qsort_perm, `mem_qsort, `Reach, `Edge, `Inv, `inv_init, `inv_root, `inv_new, `inv_on,
    `inv_done, `inv_pop, `inv_lift, `inv_finish, `tarjanLoop_spec, `fold_spec, `filt,
    `condensation_eq, `condensation_state, `condensation_cover, `condensation_range,
    `condensation_unique, `condensation_topo, `condensation_reach, `condensation_scc,
    `condensation_acyclic, `RelReach, `NodupB, `nameIdx_spec, `adjOf, `NEdge, `edge_adjOf,
    `sccsOf_eq, `sccsOf_condensation, `sccsOf_cover, `sccsOf_range, `sccsOf_unique, `sccsOf_scc,
    `LeC, `Sorted, `Oriented, `sortByM_spec, `sortByM_sim, `groupAdjP, `GroupsOK, `groupAdjP_spec,
    `groupAdjacent_sim, `ctx_eq, `ctx_fold, `KeysDistinct, `ctx_member, `ctx_ctor, `ctx_val, `ctx_dom,
    `Refines, `ctx_merge,
    `refineClassP, `refineClassesP, `sortLoopP, `sortClassesP, `seedOf, `KeysDistinct.nameInj,
    `refineClass_sim, `refineClasses_sim, `sortLoop_sim, `sortClasses_eq, `refineClassP_spec,
    `refineClassesP_spec, `same_group_of_eq, `Partition, `Consistent, `Coarsest, `constOrd_eq_mono,
    `sortLoopP_spec, `sortClassesP_coarsest, `sortClasses_coarsest,
    `nameLt_trans, `nameLt_asymm, `KeysDistinct.names, `insertByName_pairwise, `sortByName_pairwise,
    `eq_of_perm_nameLt, `sortByName_eq_of_perm, `sortClasses_perm,
    `BothOk, `mergeM_ok, `runs_ok, `mergePairs_ok, `mergeAll_ok, `sortByM_ok, `groupAdjP_ok,
    `SetEq, `ctx_setEq, `okRel, `constOrd_lookup, `constOrd_lookup_iff, `OrdPart, `ordPart_unique,
    `refineClassP_setEq, `refineClassesP_setEq, `sortLoopP_setEq, `sortClassesP_setEq,
    `sortClasses_setEq,
    `nodesOf, `refsOf, `compMembers, `blockComponents_eq, `NReach, `NodeEdge, `sccsOf_nscc,
    `mem_nodesOf, `blockComponents_sccs, `blockComponents_sub, `blockComponents_cover,
    `blockComponents_unique, `blockComponents_scc, `nodupB_iff, `sccsOf_index_unique,
    `blockComponents_perm, `ciName, `EnvWF, `ctor_edges, `reach_restrict, `blockComponents_separate,
    `mapM_perm, `keysOf_mutConstOf, `classesOf, `canon_member_order,
    `restrictC, `restrictP, `refineClassP_sim, `refineClassesP_sim, `sortLoopP_sim, `sortClassesP_sim,
    `ERen, `ehd_ren, `ResRel2, `compareExpr_ren, `LRel, `DefRen, `CtorRen, `IndRen, `RecRen, `MRen,
    `constP_ren, `OrdIff, `ordIff, `constOrd_iff, `keysOf_ren, `keysDistinct_ren, `ctx_ren,
    `compareRef_ren, `constOrd_ren, `sortClasses_rename,
    `constOrd_size_of_eq, `consistent_size, `keysDistinct_col, `ctx_col, `compareRef_col,
    `restrictC_single, `sortClasses_collapse, `sortClasses_collapse_single,
    `cliquePairs, `cliqueNameMap_eq, `cliqueNameMap_spec,
    `pot, `tarjanLoop_fuel, `rootStep_fuel, `fold_fuel, `condensation_isSome, `condensation_some,
    `sccsOf_some, `blockComponents_ok, `canon_member_order_total, `blockComponents_separate_total,
    `blockComponents_acyclic,
    `Occ, `Sub, `HashCons, `refsExpr_sound, `go_spec, `refsExpr_complete, `RefOcc, `ConstHashCons,
    `refsConst_sound, `refsConst_complete,
    `refineClassP_ok, `refineClassesP_ok, `sortLoopP_ok, `sortClassesP_ok, `sortClasses_ok,
    -- WP-E (after the hashing functions were cleared of `native_decide`)
    `forIn_id_list, `forIn_id_array, `except_pure_ok, `forIn_except_list, `forIn_except_array,
    `Pointwise, `Pointwise.nil, `Pointwise.snoc, `forIn_push_array, `Pointwise.length, `Pointwise.get,
    `Pointwise.get', `forIn_except_list_mem, `forIn_except_array_mem,
    `FirstSpec, `ComponentSpec, `canonBlock_spec, `canonBlock_comps, `canonBlock_scc, `canonBlock_acyclic,
    `canonBlock_members_sub, `canonBlock_mem_spec, `canonBlock_coarsest, `sortClassesBlind_perm,
    `component_keys, `canonBlock_member_order, `canonBlock_separate,
    `repsOf, `canonExpand, `canonAux, `canonicalAuxOrder_discovery, `aux_eq_empty, `componentNested_some,
    `componentNested_none, `sigsInOrder_empty, `componentNested_reps_empty, `auxOf,
    `componentNested_auxOf, `componentNested_canonAux, `evaporate_fields, `canonAux_evaporate,
    `canonBlock_nested_discovery, `canonBlock_canonAux, `canonBlock_member_order_nested,
    `canonBlock_separate_nested,
    `inCompOf, `strictOf, `originalsOf, `PermEntry, `option_orElse_some, `option_orElse_none,
    `except_throw_bind_ne, `computePerm_spec, `matchSig_spec, `computePerm_onto, `computePerm_entry,
    `computePerm_size, `computePerm_some,
    `compMembersOf, `strictFor, `refsOfSig, `keyAddrOf, `Claims, `ClaimedElsewhere, `TargetOk,
    `Evaporates, `bfalse, `targetOk_iff, `FlagsInv, `setBang_getElem?, `evaporate_spec,
    `evaporates_congr, `canonBlock_evaporated, `canonBlock_evaporated_perm,
    `flatMap_congr', `forIn_id_flat, `forIn_id_flat_array, `id_bind_eq, `insStep, `nestedStep,
    `namePairs, `memberPairs, `nposOf, `nestedSuffixes, `nestedName, `nestedEvents, `blockNameMap_eq,
    `stepVal, `nestedFold_getElem?, `foldl_stepVal_none_iff, `foldl_stepVal_mem, `foldl_stepVal_outside,
    `nestedVals, `nestedVal, `NameMapKeys, `nposOf_ne_outside, `mem_nestedEvents, `nested_preserves,
    `nestedName_lt, `blockNameMap_memberPairs, `nestedVals_filter, `blockNameMap_nested,
    `blockNameMap_other, `mem_memberPairs_member, `blockNameMap_member, `blockNameMap_suffix,
    `blockNameMap_ctor, `mem_nestedVals, `nposOf_mem_nestedVals, `nestedVal_aux, `nestedVal_evaporated,
    `nestedVal_outside, `nestedVal_none,
    `skel, `auxNameOf, `Grow, `Grow.refl, `Grow.trans, `Grow.push, `forIn_id_inv, `forIn_id_inv_array,
    `list_foldl_inv, `array_foldl_inv, `replaceIfNested_grow, `replaceAll_grow, `skel_modify,
    `walkCtor_grow, `walkCtor_none, `skel_getElem?, `skel_length, `QInv, `qinv_step, `walkQueue_qinv,
    `aux_getElem?_eq, `expand_spec, `expand_owner, `componentNested_discovery,
    `cliqueSpecs, `CliqueNamesDistinct, `cliqueClasses_eq, `cliqueClasses_ok_iff, `keysOf_toMutConst,
    `cliqueSpecs_keys, `cliqueKeys, `cliqueClasses_coarsest, `cliqueClasses_ok, `cliqueClasses_perm,
    `cliqueClasses_setEq, `statementClique, `flatten_singletons, `classNames_singletons,
    `pairwise_nbeq_index, `findIdx_singletons, `statementOrder_spec].map (`Ix.CompileCert.Canon ++ ·)

end Ix.CompileCert.Audit

run_cmd Ix.CompileCert.Audit.checkAuditRoots Ix.CompileCert.Audit.l1Roots Ix.CompileCert.Audit.allowedAxioms

/-! The hashing functions (WP-E, the owner's option A, 2026-10-07): every BLAKE3 digest of `Ix` is
finalized by `Address.ofHasher`, which passes the package's length bound explicitly
(`Address.digestLen_lt_wordBound`, by cases on the word size) instead of its default
`by native_decide`. The constructors that hash, and the Pass 1 functions built on them (the
functions that carried the two `native_decide` auxiliaries, `plans/review2/M7-L1-pass1.md` §3),
are checked the same way, against the same allowed set; the frozen line above is unchanged. -/

namespace Ix.CompileCert.Audit

def hashRoots : Array Lean.Name :=
  #[``Address.digestLen_lt_wordBound, ``Address.ofHasher, ``Address.blake3,
    ``Ix.Name.mkAnon, ``Ix.Name.mkStr, ``Ix.Name.mkNat, ``Ix.Name.fromLeanName,
    ``Ix.Level.mkZero, ``Ix.Level.mkSucc, ``Ix.Level.mkMax, ``Ix.Level.mkIMax,
    ``Ix.Level.mkParam, ``Ix.Level.mkMvar,
    ``Ix.Expr.mkBVar, ``Ix.Expr.mkFVar, ``Ix.Expr.mkMVar, ``Ix.Expr.mkSort, ``Ix.Expr.mkConst,
    ``Ix.Expr.mkApp, ``Ix.Expr.mkLam, ``Ix.Expr.mkForallE, ``Ix.Expr.mkLetE, ``Ix.Expr.mkLit,
    ``Ix.Expr.mkProj, ``Ix.Expr.mkMData,
    ``Ix.Compile.Canon.addrKey, ``Ix.Compile.Canon.replaceIfNested, ``Ix.Compile.Canon.walkQueue,
    ``Ix.Compile.Canon.expand, ``Ix.Compile.Canon.canonicalAuxOrder, ``Ix.Compile.Canon.sigsInOrder,
    ``Ix.Compile.Canon.computePerm, ``Ix.Compile.Canon.componentNested,
    ``Ix.Compile.Canon.evaporate, ``Ix.Compile.Canon.canonBlock, ``Ix.Compile.Canon.blockNameMap,
    ``Ix.Compile.Canon.CliqueMember.toMutConst, ``Ix.Compile.Canon.cliqueClasses,
    ``Ix.Compile.Canon.statementOrder, ``Ix.Compile.Canon.recMajorSignatures,
    ``Ix.Compile.Canon.unsafeRecToMembers]

end Ix.CompileCert.Audit

run_cmd Ix.CompileCert.Audit.checkAuditRoots Ix.CompileCert.Audit.hashRoots Ix.CompileCert.Audit.allowedAxioms

/-! The roots added by M5 (WP-A, W+): changed constants certified by theorem
and equation rows checked by the certified checker, changed inductive blocks
by containment (`Ix/CompileCert/Changed.lean`), the image claims of the export
context (`noImages`, `imageRecordAgrees`). Checked the same way, against the
same allowed set. -/

namespace Ix.CompileCert.Audit

def m5Roots : Array Lean.Name :=
  #[`noImages, `imageRecordAgrees,
    `sourceLevelSubst, `sourceInstLevels, `sourceDropMData, `sourcePiPrefix, `sourceMkForalls,
    `sourceInstForalls, `sourceSpine, `sourceResultSort, `sourceIndexPlaceholder, `leanRuleStatement,
    `directHeader, `ruleStatements, `definitionSides, `except_mapM_length, `ruleStatements_length,
    `kernelEq, `eqParts, `eqParts_kernelEq, `eqParts_sound, `endsInEq, `eqLeftHead,
    `HasTheoremRow, `isTheoremRow, `isTheoremRow_iff, `hasTheoremRow_iff,
    `HasRflRow, `isRflRow, `isRflRow_iff, `hasRflRow_iff,
    `HasTypeRow, `isTypeRow, `isTypeRow_iff, `hasTypeRow_iff, `TypeAgrees,
    `DefinitionHeaderMatch, `isDefinitionHeader, `definitionHeaderMatch_iff,
    `TheoremHeaderMatch, `isTheoremHeader, `theoremHeaderMatch_iff,
    `isThmInfo, `ThmStatementMatch, `RflEquation, `EqDefEquation, `EquationMatch,
    `ChangedMember, `exportChangedBlock, `ChangedMemberMatch, `ChangedBlockMatch,
    `SourceCorrespondence', `BlockCorrespondence',
    `directHeader_refines, `ruleStatements_refines, `definitionSides_refines,
    `exportChangedBlock_refines, `changedBlockMatch_transfer,
    `mem_of_compatible_thm, `mem_of_compatible_defn, `streamEntries_append, `mem_rows_thm,
    `typeRowAt, `typeRowAt_sound, `headerAgreesAt, `headerAgreesAt_sound,
    `defnHeaderAt, `defnHeaderAt_sound, `thmHeaderAt, `thmHeaderAt_sound,
    `thmAt, `thmAt_sound, `rowAt, `rowAt_sound, `rflAt, `rflAt_sound, `eqDefAt, `eqDefAt_sound,
    `equationsAt, `equationsAt_sound,
    `FoldedSupport, `FoldError, `foldSupport, `AcceptedAssociation', `Decline',
    `SharedW, `SharedW.ofArtifact, `SharedW.small_extends, `SharedW.rows_toList, `HintsW,
    `SharedW.declCheck', `checkIndexed', `checkIndexed'_sound,
    `AcceptedAssociation'.toAccepted, `AcceptedAssociation'.unchanged_faithful,
    `thm_mem_folded, `EquationHolds, `equationHolds_of_installed, `TypeHolds,
    `AcceptedAssociation'.row_holds, `AcceptedAssociation'.type_holds, `AcceptedAssociation'.model_statement,
    `AcceptedAssociation'.model_equations].map (`Ix.CompileCert ++ ·)

end Ix.CompileCert.Audit

run_cmd Ix.CompileCert.Audit.checkAuditRoots Ix.CompileCert.Audit.m5Roots Ix.CompileCert.Audit.allowedAxioms

namespace Ix.CompileCert.Audit

/-! ## No decision trusts a cached hash as equality

R4 (discovery 6): an `Ix.Expr`, `Ix.Level` or `Ix.Name` compares by its cached
hash (`Ix.Expr.instBEq` and siblings are `a.getHash == b.getHash`), and
`Lean.Expr`'s `BEq` (`Lean.Expr.instBEq`) is the opaque runtime `Lean.Expr.eqv`. No certified
decision may use either as equality. The instances are listed by name: under
the module system an importer does not see a core instance's body, so the
closure stops at the instance. This check computes the transitive
constant closure (types, and bodies of definitions, theorems and opaques) of
the lane's decision procedures and fails if it reaches one of them. The
equalities the decisions do use are `Kernel.Expr`'s derived `DecidableEq`
(and `Kernel.Expr.beq`, proved equal to it by `Kernel.Expr.beqMemo_eq`),
`Lean.Name`'s lawful `BEq`, and `DecidableEq` on addresses and references. The
structural `BEq` instances `Ix.Common` derives for Lean's syntax
(`instBEqExpr_ix` and siblings, not proved lawful) are listed too: no decision
may rest on an unproved equality either. -/

def hashEqualities : Array Lean.Name :=
  #[``Ix.Expr.instBEq, ``Ix.Level.instBEq, ``Ix.Name.instBEq, ``Ix.Expr.getHash,
    ``Ix.Level.getHash, ``Ix.Name.getHash, ``Lean.Expr.instBEq, ``Lean.Expr.instHashable,
    ``Lean.Expr.eqv, ``Lean.Expr.equal,
    ``Lean.Expr.quickLt, ``Lean.Expr.hash, ``instBEqExpr_ix, ``instBEqLevel_ix,
    ``instBEqConstantInfo_ix]

def decisionRoots : Array Lean.Name :=
  #[``Ix.CompileCert.checkCompiled, ``Ix.CompileCert.checkRoots, ``Ix.CompileCert.checkIndexed,
    ``Ix.CompileCert.checkIndexed_sound, ``Ix.CompileCert.faithful_sound,
    ``Ix.CompileCert.checkSourceArtifactStrongAssociation,
    ``Ix.CompileCert.SourceInstallation.artifact_strong_model,
    ``Ix.CompileCert.checkSourceProjectionLowering, ``Ix.CompileCert.SourceProjectionLowering.faithful,
    ``Ix.CompileCert.installSourceNormalized,
    ``Ix.CompileCert.checkNormalizedArtifactStrongAssociation,
    ``Ix.CompileCert.SourceNormalizedInstallation.artifact_strong_model,
    ``Ix.CompileCert.SourceNormalizedInstallation.artifact_strong_model_all,
    ``Ix.CompileCert.decideStrongCone, ``Ix.CompileCert.StrongCone.sound,
    ``Ix.CompileCert.checkIndexed', ``Ix.CompileCert.checkIndexed'_sound,
    ``Ix.CompileCert.AcceptedAssociation'.model_equations, ``Ix.CompileCert.AcceptedAssociation'.model_statement,
    ``Ix.CompileCert.leanRuleStatement,
    ``Ix.CompileCert.installSourceNormalizedWith]

def constClosure (env : Lean.Environment) (roots : Array Lean.Name) : Lean.NameSet := Id.run do
  let mut seen : Lean.NameSet := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let exprs : Array Lean.Expr := #[ci.type] ++ match ci with
      | .defnInfo v => #[v.value]
      | .thmInfo v => #[v.value]
      | .opaqueInfo v => #[v.value]
      | .recInfo v => v.rules.toArray.map (·.rhs)
      | _ => #[]
    let more : Array Lean.Name := match ci with
      | .inductInfo v => v.ctors.toArray ++ v.all.toArray
      | .ctorInfo v => #[v.induct]
      | .recInfo v => v.all.toArray
      | _ => #[]
    for e in exprs do
      for c in e.getUsedConstants do
        unless seen.contains c do todo := todo.push c
    for c in more do
      unless seen.contains c do todo := todo.push c
  return seen

def checkNoHashEquality (roots forbidden : Array Lean.Name) : CommandElabM Unit := do
  let env ← getEnv
  let missing := roots.filter (!env.contains ·)
  unless missing.isEmpty do throwError m!"decision roots are missing: {missing}"
  let closure := constClosure env roots
  let hits := forbidden.filter closure.contains
  unless hits.isEmpty do
    throwError m!"decisions reach hash-cached equality: {hits}"
  logInfo m!"[cert-audit] {roots.size} decisions, {closure.size} constants: no hash-cached equality"

/-- A decision that uses `Lean.Expr`'s core `BEq` (the runtime `Lean.Expr.eqv`). -/
def hashDecisionControl (a b : Lean.Expr) : Bool := @BEq.beq Lean.Expr Lean.Expr.instBEq a b

/-- A decision that uses `Ix.Expr`'s cached-hash `BEq`. -/
def ixHashDecisionControl (a b : Ix.Expr) : Bool := a == b

/-- A decision that compares by structure (`Kernel.Expr`'s `DecidableEq`). -/
def structuralDecisionControl (a b : Ix.Kernel.Expr) : Bool := decide (a = b)

end Ix.CompileCert.Audit

/-- error: decisions reach hash-cached equality: [Lean.Expr.instBEq, Lean.Expr.eqv] -/
#guard_msgs in
run_cmd Ix.CompileCert.Audit.checkNoHashEquality #[``Ix.CompileCert.Audit.hashDecisionControl] Ix.CompileCert.Audit.hashEqualities

/-- error: decisions reach hash-cached equality: [Ix.Expr.instBEq, Ix.Expr.getHash] -/
#guard_msgs in
run_cmd Ix.CompileCert.Audit.checkNoHashEquality #[``Ix.CompileCert.Audit.ixHashDecisionControl] Ix.CompileCert.Audit.hashEqualities

#guard_msgs(drop info) in
run_cmd Ix.CompileCert.Audit.checkNoHashEquality #[``Ix.CompileCert.Audit.structuralDecisionControl] Ix.CompileCert.Audit.hashEqualities


run_cmd Ix.CompileCert.Audit.checkNoHashEquality Ix.CompileCert.Audit.decisionRoots Ix.CompileCert.Audit.hashEqualities

/-! ## M5 WP-B: the walks on the DAG

The roots added by WP-B (`Translate.lean`, `Indexed.lean`): the sharing-aware
export, reference walk and entry comparison, their equations with the tree
functions, and the `@[csimp]` substitutions that make compiled code run them.
Audited separately, against the same allowed set, so the frozen line above is
unchanged. -/

namespace Ix.CompileCert.Audit

def m5bRoots : Array Lean.Name :=
  #[`exportIs, `exportIs_iff, `ExportEntry, `ExportMemo, `ExportRes, `ExportOut, `exportProbe,
    `exportWith_app, `exportWith_lam, `exportWith_forallE, `exportWith_letE, `exportWith_proj,
    `exportGo, `ExportVal, `exportExprWithSharedVal, `exportExprWithShared,
    `exportExprWithShared_eq, `exportExprWith_eq_shared, `exportExprShared, `exportExprShared_eq,
    `exportExpr_eq_shared,
    `constantValBeq, `constantValBeq_iff, `recRuleBeq, `recRuleBeq_iff, `recRulesBeq,
    `recRulesBeq_iff, `DirectEntry.beqShared, `DirectEntry.beqShared_iff, `DirectEntry.decEqShared,
    `instDecidableEqDirectEntry_eq_shared, `exprDecEqShared, `instDecidableEqExpr_eq_shared,
    `RefsEntry, `RefsMemo, `RefsRes, `RefsOut, `refsProbe, `refsGo, `RefsVal, `refsInSharedVal,
    `refsInShared, `refsInShared_eq, `refsIn_eq_shared].map (`Ix.CompileCert ++ ·)

end Ix.CompileCert.Audit

run_cmd Ix.CompileCert.Audit.checkAuditRoots Ix.CompileCert.Audit.m5bRoots Ix.CompileCert.Audit.allowedAxioms

/-! ### No decision trusts a cached hash as equality, as executed

`@[csimp]` replaces a constant by another in compiled code only: the constant
closure above is the closure of what the decisions' *definitions* read, not of
what their compiled code runs. `executedClosure` also follows every `@[csimp]`
substitution registered in the environment (the certified kernel's
`Kernel.Expr.beq ↦ beqMemo` and siblings, WP-B's `exportExprWith ↦
exportExprWithShared`, `exportExpr ↦ exportExprShared`, `refsIn ↦ refsInShared`,
`instDecidableEqDirectEntry ↦ DirectEntry.decEqShared`, `Kernel.instDecidableEqExpr ↦
exprDecEqShared`, core's), so the check
below covers the code that runs. The control: a decision whose substitute reads
`Lean.Expr.hash` passes the definitional check and is refused by this one. -/

namespace Ix.CompileCert.Audit

/-- The constant closure of `constClosure`, also following `@[csimp]` substitutions. -/
def executedClosure (env : Lean.Environment) (roots : Array Lean.Name) : Lean.NameSet := Id.run do
  let substitutions := (Lean.Compiler.CSimp.ext.getState env).map
  let mut seen : Lean.NameSet := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some entry := substitutions.find? n then
      unless seen.contains entry.toDeclName do todo := todo.push entry.toDeclName
    let some ci := env.find? n | continue
    let exprs : Array Lean.Expr := #[ci.type] ++ match ci with
      | .defnInfo v => #[v.value]
      | .thmInfo v => #[v.value]
      | .opaqueInfo v => #[v.value]
      | .recInfo v => v.rules.toArray.map (·.rhs)
      | _ => #[]
    let more : Array Lean.Name := match ci with
      | .inductInfo v => v.ctors.toArray ++ v.all.toArray
      | .ctorInfo v => #[v.induct]
      | .recInfo v => v.all.toArray
      | _ => #[]
    for e in exprs do
      for c in e.getUsedConstants do
        unless seen.contains c do todo := todo.push c
    for c in more do
      unless seen.contains c do todo := todo.push c
  return seen

def checkNoHashEqualityExecuted (roots forbidden : Array Lean.Name) : CommandElabM Unit := do
  let env ← getEnv
  let missing := roots.filter (!env.contains ·)
  unless missing.isEmpty do throwError m!"decision roots are missing: {missing}"
  let closure := executedClosure env roots
  let hits := forbidden.filter closure.contains
  unless hits.isEmpty do
    throwError m!"decisions as executed reach hash-cached equality: {hits}"
  logInfo m!"[cert-audit] {roots.size} decisions as executed (with @[csimp] substitutions), \
    {closure.size} constants: no hash-cached equality"

/-- The decisions WP-B's substitutions run, named as roots of their own. -/
def m5bDecisionRoots : Array Lean.Name :=
  #[``Ix.CompileCert.exportExprWithShared, ``Ix.CompileCert.exportExprShared,
    ``Ix.CompileCert.refsInShared, ``Ix.CompileCert.DirectEntry.decEqShared,
    ``Ix.CompileCert.exportExprWith_eq_shared, ``Ix.CompileCert.exportExpr_eq_shared,
    ``Ix.CompileCert.refsIn_eq_shared, ``Ix.CompileCert.instDecidableEqDirectEntry_eq_shared,
    ``Ix.CompileCert.exprDecEqShared, ``Ix.CompileCert.instDecidableEqExpr_eq_shared]

/-- A control decision: `true`, whose compiled substitute reads `Lean.Expr.hash`. -/
def executedHashControl (_a : Lean.Expr) : Bool := true

def executedHashControlImpl (a : Lean.Expr) : Bool := a.hash == a.hash || true

@[csimp] theorem executedHashControl_eq : @executedHashControl = @executedHashControlImpl := by
  funext a
  simp [executedHashControl, executedHashControlImpl]

/-- Every decision of the lane, for the check as executed. -/
def executedDecisionRoots : Array Lean.Name := decisionRoots ++ m5bDecisionRoots

end Ix.CompileCert.Audit

#guard_msgs(drop info) in
run_cmd Ix.CompileCert.Audit.checkNoHashEquality #[``Ix.CompileCert.Audit.executedHashControl] Ix.CompileCert.Audit.hashEqualities

/-- error: decisions as executed reach hash-cached equality: [Lean.Expr.hash] -/
#guard_msgs in
run_cmd Ix.CompileCert.Audit.checkNoHashEqualityExecuted #[``Ix.CompileCert.Audit.executedHashControl] Ix.CompileCert.Audit.hashEqualities

run_cmd Ix.CompileCert.Audit.checkNoHashEquality Ix.CompileCert.Audit.m5bDecisionRoots Ix.CompileCert.Audit.hashEqualities

run_cmd Ix.CompileCert.Audit.checkNoHashEqualityExecuted Ix.CompileCert.Audit.executedDecisionRoots Ix.CompileCert.Audit.hashEqualities

/-! ## M7 WP-F: the S decisions on indices and the DAG

The roots added by WP-F (`SourceExportFast.lean`, `SourceInstallFast.lean`, the indexed
normalisation in `SourceNormalization.lean`, `StrongFast.lean`): the indexed and sharing-aware
decisions of the S path, their equations with the list and tree functions they replace, and the
`@[csimp]` substitutions that make compiled code run them. Audited separately, against the same
allowed set, so the frozen line and every earlier root line are unchanged; then the hash-equality
checks, by definition and as executed, on the substitutes. -/

namespace Ix.CompileCert.Audit

def m7fRoots : Array Lean.Name :=
  #[-- the source export
    `sourceIndex, `sourceIndex_get, `sourceIndex_find, `keepNew, `eraseDups_filter_eq_keepNew,
    `keepNew_append, `keepNew_suffix, `keepNew_covers, `keepNew_absorb, `DepEntry, `DepState, `DepRes,
    `DepState.init, `depStep, `depSteps, `DepRes.seq, `DepRes.record, `depProbe, `depGo, `depItems,
    `itemRefs, `sourceTermRefs_items, `depItemsGo, `depsWalkVal, `depsWalk, `depsWalk_eq,
    `sourceGroupDependenciesP, `sourceGroupDependenciesP_find, `findMember, `sourceGroupDependenciesF,
    `mapM_map_except, `sourceGroupDependenciesF_eq, `exportSourceInductiveP, `exportSourceInductiveP_find,
    `buildSourceGroupsP, `buildSourceGroupsP_find, `singletonDeclaration, `buildStepA, `buildSourceGroupsA,
    `forIn_rep, `buildSourceGroupsA_eq, `buildSourceGroupsF, `buildSourceGroupsF_eq, `coverFast,
    `coverFast_sound, `validateSourceGroupsF, `validateSourceGroupsF_eq, `exportSourceGroupsF,
    `exportSourceGroupsF_eq, `exportSourceGroups_eq_fast, `orderF, `foldl_insert_contains,
    `foldl_groups_contains, `orderF_eq, `orderF_empty, `exportSourceDeclarationsF,
    `exportSourceDeclarationsF_eq, `exportSourceDeclarations_eq_fast,
    -- constants and declarations compared on the DAG
    `exprsBeq, `exprsBeq_iff, `projTableBeq, `projTableBeq_iff, `ciBeq, `ciBeq_iff, `cisBeq, `cisBeq_iff,
    `ciDecEqShared, `instDecidableEqConstantInfo_eq_shared, `declBeq, `declBeq_iff, `declDecEqShared,
    `instDecidableEqDeclaration_eq_shared,
    -- the model proposal, the entry correspondence, the normalisation
    `exportSourceBlockEvidenceP, `exportSourceBlockEvidenceP_find, `exportSourceBlockEvidenceP_subst,
    `exportSourceBlockEvidenceF, `exportSourceInductiveP_index, `exportSourceBlockEvidenceF_eq,
    `proposeSourceModelsP, `proposeSourceModelsP_find, `proposeSourceModelsQ, `proposeSourceModelsQ_list,
    `proposeSourceModelsQ_spec, `declKey, `groupBuckets, `groupBuckets_getD, `find?_filter_of_imp, `queryBuckets,
    `queryBuckets_eq, `proposeSourceModelsF, `proposeSourceModelsF_eq,
    `proposeSourceModels_eq_fast, `directEntryName, `entryIndex, `entryIndex_mem, `entriesFast,
    `entriesFast_sound, `entriesFastDecidable, `instDecidableSourceEntryCorrespondence_eq_fast,
    `sourceKernelFind, `sourceKernelIndex, `sourceKernelIndex_find, `proposeSourceProjectionP,
    `proposeSourceProjectionP_find, `proposeSourceProofP, `proposeSourceProofP_find,
    `proposeSourceProjectionP_conv, `proposeSourceProofP_conv, `normalizeSourceProjectionsP,
    `normalizeSourceProjectionsP_find, `normalizeSourceProjectionsP_subst, `normalizeSourceProjectionsF,
    `normalizeSourceProjectionsF_eq, `normalizeSourceProjections_eq_fast,
    -- the strong check
    `envFind, `envFind_eq, `lookupProj, `lookupProj_env, `checkInstalledConstantL, `checkInstalledConstantL_env,
    `checkInstalledPinsL, `checkInstalledPinsL_env, `checkInstalledProjectionL, `checkInstalledProjectionL_env,
    `checkInstalledExprL, `checkInstalledExprL_env, `PairEntry, `PairRes, `pairKey, `pairProbe,
    `pairRecursive, `pairGo, `checkInstalledExprSharedVal, `checkInstalledExprShared,
    `checkInstalledExprShared_eq, `checkInstalledMemberExprL, `checkInstalledMemberExprL_env,
    `checkInstalledMemberExprF, `checkInstalledMemberExprF_eq, `checkInstalledMemberExprF_env,
    `checkInstalledMemberExprsF_env, `checkInstalledFireF_env, `checkInstalledRulesF_env,
    `checkTelescopesF_env, `checkInstalledTypesF_env, `checkInstalledDefinitionsF_env,
    `checkInstalledCapabilitiesF_env, `checkInstalledRecursorsF_env, `checkInstalledConstructorsF_env,
    `checkInstalledEtaAssociationsF_env, `readFrameL, `readFrameL_env, `checkInstalledRuleLevelLinkF_env,
    `checkInstalledRuleLevelLinksF_env, `checkInstalledTowersF_env,
    `checkInstalledComparisonAvailabilityF_env, `availability_row, `bothChecks_foldr_true,
    `availability_of_checks, `checkInstalledAssociationF, `checkInstalledAssociationF_eq,
    `checkExprLiteralSupport_both, `checkLiteralSupportsF, `checkLiteralSupportsF_eq,
    `checkAnnotatedAssociationF, `checkAnnotatedAssociationF_eq, `checkInstalledTowersFast,
    `checkInstalledTowersFast_eq, `checkStrongAssociationF, `checkStrongAssociationF_eq,
    `mapIndex, `mapIndex_get, `memberNameL, `contextNameL, `contextNameL_find, `semanticNamesFast,
    `semanticNamesFast_iff, `semanticNamesDecidable, `rowsPreservedFast, `rowsPreservedFast_iff,
    `rowsPreservedDecidable, `instDecidableInstalledRowsPreserved_eq_fast, `supportFreshFast,
    `supportFreshFast_sound, `supportFreshDecidable, `instDecidableSupportFresh_eq_fast,
    `checkAdmittedSupportC, `checkAdmittedSupport_eq_copy, `checkNormalizedArtifactStrongAssociationF,
    `checkNormalizedArtifactStrongAssociationF_eq, `checkNormalizedArtifactStrongAssociation_eq_fast,
    `checkInstalledTypes_eq_fast, `checkInstalledDefinitions_eq_fast,
    `checkInstalledComparisonAvailability_eq_fast, `checkInstalledTowers_eq_fast,
    `checkInstalledAssociation_eq_fast, `checkTelescopes_eq_fast, `checkInstalledCapabilities_eq_fast,
    `checkInstalledRecursors_eq_fast, `checkInstalledConstructors_eq_fast,
    `checkInstalledEtaAssociations_eq_fast, `checkInstalledRuleLevelLinks_eq_fast,
    `checkTypeLiteralSupport_eq_fast, `checkDefinitionLiteralSupport_eq_fast,
    `instDecidableSemanticNamesAgree_eq_fast].map (`Ix.CompileCert ++ ·)

/-- The decisions WP-F's substitutions run, named as roots of their own. -/
def m7fDecisionRoots : Array Lean.Name :=
  #[`exportSourceDeclarationsF, `exportSourceGroupsF, `proposeSourceModelsF, `entriesFastDecidable,
    `normalizeSourceProjectionsF, `ciDecEqShared, `declDecEqShared, `checkInstalledAssociationF,
    `checkStrongAssociationF, `checkNormalizedArtifactStrongAssociationF, `semanticNamesDecidable,
    `rowsPreservedDecidable, `supportFreshDecidable, `checkAdmittedSupportC,
    `exportSourceDeclarations_eq_fast, `exportSourceGroups_eq_fast, `proposeSourceModels_eq_fast,
    `instDecidableSourceEntryCorrespondence_eq_fast, `normalizeSourceProjections_eq_fast,
    `instDecidableEqConstantInfo_eq_shared, `instDecidableEqDeclaration_eq_shared,
    `checkNormalizedArtifactStrongAssociation_eq_fast, `checkAdmittedSupport_eq_copy,
    `instDecidableInstalledRowsPreserved_eq_fast, `instDecidableSupportFresh_eq_fast,
    `instDecidableSemanticNamesAgree_eq_fast].map (`Ix.CompileCert ++ ·)

end Ix.CompileCert.Audit

run_cmd Ix.CompileCert.Audit.checkAuditRoots Ix.CompileCert.Audit.m7fRoots Ix.CompileCert.Audit.allowedAxioms

run_cmd Ix.CompileCert.Audit.checkNoHashEquality Ix.CompileCert.Audit.m7fDecisionRoots Ix.CompileCert.Audit.hashEqualities

run_cmd Ix.CompileCert.Audit.checkNoHashEqualityExecuted Ix.CompileCert.Audit.m7fDecisionRoots Ix.CompileCert.Audit.hashEqualities

/-! ## Package C (PLAN-L2a, the costs of W+): the certified fold continued

The roots added by package C (`FoldCompose.lean`, `Changed.lean`): the fold over
artifact + support composed from the admission's two phases and the support's
(`checkDecls_append_of_phases`, from `IxC`'s `InstallRun`, `installRun_trace`,
`mkFEnv_find?_visibleBelow` and the congruence lemmas of `KnotCongr`), the staged
admission and the staged support fold. Audited on their own line, against the same
allowed set, so every line above is unchanged; the two new decisions are also checked
for hash-cached equality, as executed. -/

namespace Ix.CompileCert.Audit

def cRoots : Array Lean.Name :=
  #[`InstallRun.append, `annotValC_congr', `checkPending_congr, `prefixTo_of_append,
    `restrictTo_find?_of_chain, `checkDecls_append_of_phases, `checkPendingList_drop_size,
    `StagedAdmission, `StagedAdmission.env_eq, `prepareArtifactStaged,
    `foldSupportStaged].map (`Ix.CompileCert ++ ·)

/-- The decisions package C adds. -/
def cDecisionRoots : Array Lean.Name :=
  #[``Ix.CompileCert.prepareArtifactStaged, ``Ix.CompileCert.foldSupportStaged]

end Ix.CompileCert.Audit

run_cmd Ix.CompileCert.Audit.checkAuditRoots Ix.CompileCert.Audit.cRoots Ix.CompileCert.Audit.allowedAxioms

run_cmd Ix.CompileCert.Audit.checkNoHashEqualityExecuted Ix.CompileCert.Audit.cDecisionRoots Ix.CompileCert.Audit.hashEqualities

/-! The roots added by M7 X1 (`Ix/CompileCert/Conv/**`): the conversion relation on the
compiler's terms (through their erasure), its stability under the compiler's term operations,
the development lemma (the developed term is convertible to the plain substitution; the inline
rewrite is δ then the development), the simple types of the erasure and the development's
termination on them, and fuel monotonicity. Audited separately, against the same allowed set,
so the frozen line above is unchanged. -/

namespace Ix.CompileCert.Audit

def x1Roots : Array Lean.Name :=
  #[-- the erased terms
    `Tm, `er, `Tm.lift, `Tm.lower, `Tm.inst, `Tm.occ, `Tm.range, `Tm.appN, `Tm.appN_append,
    `Tm.appN_concat, `Tm.lift_zero, `Tm.lift_lift_of_le, `Tm.lift_lift_comm, `Tm.occ_lift_lt,
    `Tm.occ_lift_mid, `Tm.occ_of_range_le, `Tm.lift_of_range_le, `Tm.lower_of_range_le,
    `Tm.inst_of_range_le, `Tm.inst_lift_self, `Tm.inst_lift_lo, `Tm.lift_inst_hi, `Tm.inst_inst,
    `Tm.lift_appN, `Tm.inst_appN, `Tm.lower_appN, `Tm.inst_eq_lower, `Tm.occ_inst_lt,
    `Tm.lower_zero,
    -- the relation and its theory
    `pairName, `Env, `Env.empty, `pair4, `Step, `Conv, `Forall2, `ExprConv, `Conv.rfl',
    `Conv.equivalence, `Conv.appN, `Conv.appN_args, `Conv.forall₂_refl, `Conv.beta_appN,
    `Conv.mono, `Env.LiftClosed, `Env.InstClosed, `Env.empty_liftClosed, `Env.empty_instClosed,
    `Env.liftClosed_of_closed, `Env.instClosed_of_closed, `Step.lift, `Conv.lift, `Step.inst,
    `Conv.inst, `Conv.inst_val, `Conv.inst₂, `Conv.lower,
    -- the compiler's term functions erased
    `er_mkBVar, `er_mkFVar, `er_mkSort, `er_mkConst, `er_mkApp, `er_mkLam, `er_mkForallE,
    `er_mkLetE, `er_mkProj, `er_mkMData, `er_getAppFnArgs, `er_mkAppN_list, `er_mkAppN,
    `er_liftLoose_go, `er_liftLoose, `er_lowerLoose_go, `er_lowerLoose, `projCtor?_spec,
    -- stability under the compiler's other operations
    `Tm.mapC, `Tm.mapC_lift, `Tm.mapC_inst, `Tm.occ_mapC, `Tm.mapC_lower, `Tm.mapC_appN,
    `Conv.mapC, `er_substLevels_go, `Tm.mapC_id, `er_substLevels, `er_canonicalizeConstNames_go,
    `er_canonicalizeConstNames, `Tm.abstractF, `Tm.abstractF_lift, `Tm.abstractF_inst,
    `Tm.occ_abstractF, `Tm.abstractF_appN, `Env.AbstractClosed, `Conv.abstractF,
    `er_abstractFVars_go, `Tm.abstractF_empty, `er_abstractFVars,
    -- the development without its tables, and the development lemma
    `looseRangeP, `liftP, `lowerP, `occursP, `hinstP, `happP, `instantiateP, `substFVarsP,
    `looseRangeP_eq, `er_liftP, `er_lowerP, `occursP_eq, `EForall2, `mapM_ok, `bind_ok, `map_ok,
    `pure_ok, `hinstP_zero, `happP_zero, `happP_succ, `forall2_of_mapM, `develop_conv,
    `hinstP_conv, `happP_conv, `instantiateP_conv, `inline_conv,
    `Env.ofExpansions, `Tm.range_mapC, `range_substLevels, `ofExpansions_closed,
    `ofExpansions_liftClosed, `ofExpansions_instClosed, `expansion_inline_conv, `imageInlineP,
    `imageInlineP_conv, `foldl_inst_conv, `foldlM_conv, `substFVarsP_conv, `hasLooseBVar_go_eq,
    `hasLooseBVar_eq, `etaReduce_conv, `er_eq_of_eRen, `exprConv_of_eRen,
    -- simple types of the erasure, and the development's termination
    `Ty, `Ty.size, `Ty.pair, `Ty.arrows, `Ty.pair_inj, `Ty.size_pos, `Ty.size_pair,
    `Ty.arrows_append, `Ty.arr_inj, `pairKind, `ctorKind, `Typ, `TypArgs, `Typ.appN_iff,
    `Typ.lift, `Typ.lift_front, `Typ.lower, `Typ.inst, `TypArgs.length, `TypArgs.append,
    `TypArgs.split, `TypArgs.lower, `Ext, `Ext.refl, `Ext.bind, `Ext.map, `Ext.mapM,
    `appTail_ext, `fuel_mono, `appN_eq_app, `Tm.occ_appN, `lower_lift_succ, `getAppFnArgs_sizeOf,
    `DirectInv, `HinstOk, `size_arrows_le, `size_arrows_dom, `HinstOk.size, `pairName_ctorKind,
    `pairName_pairKind, `typ_const_pair, `typ_pair4, `typ_lam_inv, `args_total, `HinstTotalAt,
    `mkAppN_toList, `happP_succ_nonlam, `happP_total_of, `hinstTotalAt_of, `develop_total,
    `happP_total, `instantiate_total, `instantiateP_of_total].map (`Ix.CompileCert.Conv ++ ·)

end Ix.CompileCert.Audit

run_cmd Ix.CompileCert.Audit.checkAuditRoots Ix.CompileCert.Audit.x1Roots Ix.CompileCert.Audit.allowedAxioms

/-! ## Package V: value rows for transported clique members (M7)

Package V adds no relation and changes no statement: a value row is a support row
stating a transported member's `rfl` equation `@Eq T c v_lean` with a proof the
certifier generates (`Ix/CompileCert/CliqueRows.lean`, untrusted), checked by the
certified fold like every row. The roots its reading rests on, audited on their own
line against the same allowed set: the two lemmas it adds (`rflEquation_of_row`: such a
row is an `RflEquation` whatever its proof; `value_row_holds`: an accepted one holds in
every strong model of the folded environment) and W+'s theorems they compose with. -/

namespace Ix.CompileCert.Audit

def vRoots : Array Lean.Name :=
  #[`rflEquation_of_row, `AcceptedAssociation'.value_row_holds, `AcceptedAssociation'.row_holds,
    `AcceptedAssociation'.model_equations, `checkIndexed'_sound, `hasRflRow_iff, `rflAt_sound,
    `equationsAt_sound].map (`Ix.CompileCert ++ ·)

end Ix.CompileCert.Audit

run_cmd Ix.CompileCert.Audit.checkAuditRoots Ix.CompileCert.Audit.vRoots Ix.CompileCert.Audit.allowedAxioms

/-! The roots added by M7 X2 (`Ix/CompileCert/Bridge/**`): the bridge from the compiler's erased
terms to the reader's `Kernel.Expr` (totality, injectivity on erased content, commutation with the
de Bruijn operations, the skeleton relation of annotated terms), the translation lemma to the
lane's export, the per-compile emission check, the public reading under lifting, substitution,
lowering and universe instantiation, and conversion soundness rule by rule (semantic equality and
its congruences, β, η, δ, installed theorems, justified conversions). Audited separately, against
the same allowed set, so every line above is unchanged. -/

namespace Ix.CompileCert.Audit

def x2Roots : Array Lean.Name :=
  #[-- the bridge
    `never, `optMap, `optMap_nil, `optMap_cons_some, `optMap_cons_inv, `optMap_isSome_iff,
    `optMap_length, `optMap_inj, `bridgeLit, `app2, `app3, `app2_inv, `app3_inv, `bridgeT,
    `bridge, `Supported, `bridgeT_isSome_iff, `bridgeT_bvar_inv, `bridgeT_sort_inv,
    `bridgeT_const_inv, `bridgeT_app_inv, `bridgeT_lam_inv, `bridgeT_pi_inv, `bridgeT_letE_inv,
    `bridgeT_proj_inv, `Agree, `bridgeLit_injective, `tTag, `kTag, `bridgeT_tag,
    `bridgeT_mismatch, `bridgeT_agree, `NameInj, `agree_eq, `bridgeT_injective, `bridgeT_lift,
    `bridgeT_lower, `bridgeT_inst, `bridgeT_appN, `bridgeT_erasePw, `Skel, `skel_of_bridgeT,
    `erasePw_liftLooseBVars, `erasePw_lowerBVars, `erasePw_instantiate1Lift, `Skel.lift,
    `Skel.lower, `Skel.inst, `skel_app, `skel_lam, `skel_pi, `skel_proj, `skel_const, `skel_bvar,
    -- the lane's export, emission
    `laneN, `laneL, `ixExprE, `NoMData, `ixExprE_eq, `toOption_bind, `optMap_toOption,
    `ixToKernelE, `bridge_eq_lane, `bridge_eq_ixToKernel, `Emitted, `checkEmitted,
    `checkEmitted_sound,
    -- the public reading under the operations
    `liftEnv, `instEnv, `dropEnv, `lowerEnv, `push_liftEnv, `push_instEnv, `dropEnv_push,
    `liftEnv_zero_cut, `liftEnv_one_push, `push_lowerEnv, `NoVarIn, `natLit_closed_lift,
    `natLit_closed_inst, `natLit_closed_lower, `natLit_closed_levels, `strLit_noVarIn,
    `strLit_closed_lift, `strLit_closed_inst, `strLit_closed_lower, `strLit_closed_levels,
    `denotes_lift, `denotes_lift_push, `denotes_inst, `denotes_inst0, `denotes_lower, `CvalLocal,
    `cvalLocal_of_strong, `substFn_map_subst, `regime_substPW, `denotes_levels,
    -- conversion soundness, rule by rule
    `SemEq, `SemEq.refl, `SemEq.symm, `SemEq.trans, `SemEq.left, `SemEq.right, `SemEq.value,
    `SemEq.app, `KForall2, `SemEq.appN, `SemEq.proj, `SemEq.lam, `SemEq.pi, `app_lam_value,
    `semEq_beta, `lam_dom_of_mem, `semEq_beta_graph, `semEq_eta, `semEq_delta, `semEq_theorem,
    -- justified conversions
    `Justified, `Justified.refl, `Justified.symm, `Justified.trans, `Justified.app,
    `Justified.proj, `Justified.lam, `Justified.pi, `Justified.beta, `Justified.beta_graph,
    `Justified.eta, `Justified.delta, `Justified.ax, `justified_sound].map
      (`Ix.CompileCert.Bridge ++ ·)

end Ix.CompileCert.Audit

run_cmd Ix.CompileCert.Audit.checkAuditRoots Ix.CompileCert.Audit.x2Roots Ix.CompileCert.Audit.allowedAxioms
