import Ix.CompileCert.Audit
import Ix.CompileCert.RuleRowAnnotations

/-! The axiom audit of the S+b firing-row stack (`Ix.CompileCert.RuleRowAnnotations` and
the modules it imports).
Elaboration fails unless every root exists, none is listed twice, and each
depends only on the standard axioms (`Ix.CompileCert.Audit.checkAuditRoots`). -/

run_cmd (Ix.CompileCert.Audit.checkAuditRoots #[
  ``Ix.CompileCert.installedTypeRowF,
  ``Ix.CompileCert.installedTypeRowF_spec,
  ``Ix.CompileCert.checkInstalledTypesRowsF,
  ``Ix.CompileCert.checkInstalledTypesRows,
  ``Ix.CompileCert.checkInstalledTypesRows_member,
  ``Ix.CompileCert.checkInstalledTypesRows_sound,
  ``Ix.CompileCert.checkedTypeRowsModel,
  ``Ix.CompileCert.checkedTypeRowsValueModel,
  ``Ix.CompileCert.InstalledRuleFrame.rowLeft,
  ``Ix.CompileCert.InstalledRuleFrame.rowRight,
  ``Ix.CompileCert.ruleRowForalls,
  ``Ix.CompileCert.InstalledRuleFrame.rowBody,
  ``Ix.CompileCert.InstalledRuleFrame.rowStatement,
  ``Ix.CompileCert.ruleRowForalls_strip,
  ``Ix.CompileCert.InstalledTelescope.ruleRow_arity,
  ``Ix.CompileCert.checkInstalledFiringRow,
  ``Ix.CompileCert.checkInstalledFiringRow_spec,
  ``Ix.CompileCert.checkInstalledFiringRow_sound,
  ``Ix.CompileCert.exportRuleResidual,
  ``Ix.CompileCert.exportExpr_sourceDropMData,
  ``Ix.CompileCert.exportExpr_sourceInstForalls,
  ``Ix.CompileCert.InstalledTelescope.instPisAtLift_prefix,
  ``Ix.CompileCert.InstalledTelescope.ruleRow_binders,
  ``Ix.CompileCert.RuleTupleTyping.constructor_parameter_instance,
  ``Ix.CompileCert.RuleTupleTyping.firing_field_row,
  ``Ix.CompileCert.open_rule_parameter_control,
  ``Ix.CompileCert.closed_rule_parameter_neighbour,
  ``Ix.CompileCert.InstalledRuleFrame.openParameterRecipe,
  ``Ix.CompileCert.SourceRuleComparisons.openParameterRecipe_reading,
  ``Ix.CompileCert.RuleTupleTyping.generated_parameter_field_row,
  ``Ix.CompileCert.SourceRuleComparisons.nested_recipe_shape,
  ``Ix.CompileCert.RuleUniverseSelection.constructor_value,
  ``Ix.CompileCert.InstalledRuleFrame.firingParameterRecipe,
  ``Ix.CompileCert.SourceRuleComparisons.firingParameterRecipe_reading,
  ``Ix.CompileCert.RuleTupleTyping.firing_recipe_fields,
  ``Ix.CompileCert.InstalledTelescope.split_arguments,
  ``Ix.CompileCert.ruleRowForalls_append,
  ``Ix.CompileCert.RuleTupleTyping.firing_recursor_prefix,
  ``Ix.CompileCert.RuleTupleTyping.firing_open_row,
  ``Ix.CompileCert.DenotedApplication.instPisAtLift_result,
  ``Ix.CompileCert.RuleTupleTyping.firing_constructor_indices,
  ``Ix.CompileCert.equationRowBinders,
  ``Ix.CompileCert.equationRowBinders_domains,
  ``Ix.CompileCert.equationRowBinders_length,
  ``Ix.CompileCert.FiringRowProposal.forEquation,
  ``Ix.CompileCert.FiringRowProposal.forEquation_preserves,
  ``Ix.CompileCert.InstalledTelescope.equation_row_annotations,
  ``Ix.CompileCert.checkInstalledFiringRow_equation_spec,
  ``Ix.CompileCert.checkInstalledFiringRow_equation_sound
] Ix.CompileCert.Audit.allowedAxioms)
