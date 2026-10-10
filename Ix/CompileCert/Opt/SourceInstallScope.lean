import Ix.CompileCert.Opt.SourceScope
import Ix.CompileCert.SourceInstallation

/-!
Extract source universe scope from the existing full SourceInstallation receipt. No installation-success premise is added to the
general compiler endpoint; obtaining that receipt and relating CanonM output to
the original source remain separate obligations.
-/

namespace Ix.CompileCert.Opt.SourceScope

theorem definition_scope_of_export {source : Lean.DefinitionVal} {out : DirectEntry}
    (exported : exportSourceEntry (.defnInfo source) = .ok out) {k : Lean.Name} :
    (ExprOccurs k source.type → k ∈ source.levelParams) ∧
      (ExprOccurs k source.value → k ∈ source.levelParams) := by
  cases ht : exportSourceExpr source.levelParams source.type <;>
    cases hb : exportSourceExpr source.levelParams source.value
  all_goals simp only [exportSourceEntry, Lean.ConstantInfo.levelParams,
    Lean.ConstantInfo.type, Lean.ConstantInfo.name, Lean.ConstantInfo.toConstantVal, ht, hb,
    bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals try contradiction
  exact ⟨exportSourceExpr_scope ht, exportSourceExpr_scope hb⟩

theorem theorem_scope_of_export {source : Lean.TheoremVal} {out : DirectEntry}
    (exported : exportSourceEntry (.thmInfo source) = .ok out) {k : Lean.Name} :
    (ExprOccurs k source.type → k ∈ source.levelParams) ∧
      (ExprOccurs k source.value → k ∈ source.levelParams) := by
  cases ht : exportSourceExpr source.levelParams source.type <;>
    cases hb : exportSourceExpr source.levelParams source.value
  all_goals simp only [exportSourceEntry, Lean.ConstantInfo.levelParams,
    Lean.ConstantInfo.type, Lean.ConstantInfo.name, Lean.ConstantInfo.toConstantVal, ht, hb,
    bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals try contradiction
  exact ⟨exportSourceExpr_scope ht, exportSourceExpr_scope hb⟩

/-- Every original definition in the installation's finite source inventory
has its complete original type and value scoped by its declared telescope. -/
theorem definition_scope_of_installation {source : Source} {roots : List Lean.Name}
    (installed : SourceInstallation source roots) {definition : Lean.DefinitionVal}
    (member : Lean.ConstantInfo.defnInfo definition ∈ source.declarations)
    {k : Lean.Name} :
    (ExprOccurs k definition.type → k ∈ definition.levelParams) ∧
      (ExprOccurs k definition.value → k ∈ definition.levelParams) := by
  have hm := installed.members (.defnInfo definition) member
  cases he : exportSourceEntry (.defnInfo definition) with
  | error reason => simp only [SourceEntryMatches, he] at hm
  | ok out => exact definition_scope_of_export he

/-- The same inventory-backed scope fact for an original theorem; this does
not turn its proof body into a semantic definition. -/
theorem theorem_scope_of_installation {source : Source} {roots : List Lean.Name}
    (installed : SourceInstallation source roots) {declaration : Lean.TheoremVal}
    (member : Lean.ConstantInfo.thmInfo declaration ∈ source.declarations)
    {k : Lean.Name} :
    (ExprOccurs k declaration.type → k ∈ declaration.levelParams) ∧
      (ExprOccurs k declaration.value → k ∈ declaration.levelParams) := by
  have hm := installed.members (.thmInfo declaration) member
  cases he : exportSourceEntry (.thmInfo declaration) with
  | error reason => simp only [SourceEntryMatches, he] at hm
  | ok out => exact theorem_scope_of_export he


end Ix.CompileCert.Opt.SourceScope
