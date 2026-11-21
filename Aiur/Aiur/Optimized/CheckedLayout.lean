import Aiur.Optimized.AllocationCertificate
import Aiur.Optimized.Propagation
import Aiur.Optimized.ScopedPropagation
import Aiur.Optimized.ConstraintElimination
import Aiur.Optimized.LookupMerging

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

def ScopedChip.Realizes (source : ScopedChip F) (physical : Circuit.Chip F) : Prop :=
  ∀ rom conclusion premises, source.Rule rom conclusion premises ↔ physical.LocalRule rom conclusion premises

theorem realizes_emit {source logical : ScopedChip F} {layout : ColumnLayout}
    (same : source.Equivalent logical) (allocation : Allocation.Certificate logical layout)
    (formed : (emitChip logical layout).wellFormed = true) : source.Realizes (emitChip logical layout) := by
  intro rom conclusion premises
  rw [same.rule_iff]
  constructor
  · rintro ⟨a, valid, root, calls⟩
    obtain ⟨row, name, valid, root', calls'⟩ := allocation.complete rom a formed valid
    exact ⟨row, name, valid, root'.trans root, calls'.trans calls⟩
  · rintro ⟨row, _, valid, root, calls⟩
    exact ⟨_, ((emitChip_validRow logical layout rom row).mp valid).2.2,
      (emitChip_receive logical layout row).symm.trans root,
      (emitChip_premises logical layout row).symm.trans calls⟩

structure CheckedLayout (source : ScopedChip F) extends LaidOutChip F where
  equivalent : source.Realizes chip
  name_eq : chip.name = source.name
  inputTypes : chip.inputs.map WireValue.type = source.inputs.map WireValue.type
  outputType : chip.output.type = source.output.type

def checkedLayOut (config : Config) (chip : ScopedChip F) : Except String (CheckedLayout chip) := do
  let aliases ← Alias.checkedResolve chip
  let propagated ← if config.propagateScopes then ScopedPropagation.run aliases.chip
    else pure (ScopedPropagation.identity aliases.chip)
  let simplified := if config.simplifyConstraints then ConstraintElimination.run propagated.chip
    else ScopedPropagation.identity propagated.chip
  let degree ← Degree.checkedBound config simplified.chip
  let logical := degree.chip
  unless logical.wellScoped do throw s!"auxiliary escaped its activation scope in {chip.name}"
  let layout := allocateColumns config logical
  let physical := emitChip logical layout
  if allocation : Allocation.Certificate logical layout then
    if formed : physical.wellFormed = true then
      let lookups := LookupMerging.run config logical layout
      let propagatedValues ← if config.propagateValues then Propagation.run lookups.chip
        else pure (Propagation.Checked.identity lookups.chip)
      let values : Propagation.Checked physical := {
        chip := propagatedValues.chip
        equivalent := lookups.equivalent.trans propagatedValues.equivalent
        name_eq := propagatedValues.name_eq.trans lookups.name_eq
        inputTypes := propagatedValues.inputTypes.trans lookups.inputTypes
        outputType := propagatedValues.outputType.trans lookups.outputType }
      let lookupCap := if config.mergeLookups && !logical.choices.isEmpty then 2 else 1
      if finalFormed : values.chip.wellFormed = true then
        if values.chip.stats.maxConstraintDegree > config.maxDegree || values.chip.stats.maxLookupDegree > lookupCap ||
            values.chip.maxLookupGuardDegree > 1 then
          throw s!"degree reduction failed in {chip.name}"
        return {
          logical, layout, chip := values.chip
          equivalent := fun rom root premises =>
            (realizes_emit (aliases.equivalent.trans
              (propagated.equivalent.trans (simplified.equivalent.trans degree.equivalent)))
              allocation formed rom root premises).trans
              (values.equivalent.localRule formed finalFormed rom root premises)
          name_eq := values.name_eq.trans
            (degree.name_eq.trans (simplified.name_eq.trans (propagated.name_eq.trans aliases.name_eq)))
          inputTypes := values.inputTypes.trans (by
            simp [physical, emitChip, logical, degree.inputs_eq, simplified.inputs_eq, propagated.inputs_eq, aliases.inputs_eq,
              List.map_map, Function.comp_def])
          outputType := values.outputType.trans (by
            simp [physical, emitChip, logical, degree.output_eq, simplified.output_eq, propagated.output_eq, aliases.output_eq]) }
      else throw s!"invalid propagated layout in {chip.name}"
    else throw s!"invalid optimized layout in {chip.name}"
  else throw s!"invalid column-allocation certificate in {chip.name}"

def layOut (config : Config) (chip : ScopedChip F) : Except String (LaidOutChip F) :=
  (checkedLayOut config chip).map CheckedLayout.toLaidOutChip

/-- The actual layout pipeline preserves the entire local rule: selector
elimination, scoped propagation, degree reduction, sharing, emission, quadratic lookup merging, branch outputs, value propagation,
and compaction. -/
theorem layOut_correct {config : Config} {source : ScopedChip F} {result : LaidOutChip F}
    (compiled : layOut config source = .ok result) : source.Realizes result.chip := by
  unfold layOut at compiled
  cases found : checkedLayOut config source with
  | error error => simp [found, Except.map] at compiled
  | ok checked =>
      have same : checked.toLaidOutChip = result := by simpa [found, Except.map] using compiled
      cases same
      exact checked.equivalent

theorem layOut_interface {config : Config} {source : ScopedChip F} {result : LaidOutChip F}
    (compiled : layOut config source = .ok result) :
    result.chip.name = source.name ∧ result.chip.inputs.map WireValue.type = source.inputs.map WireValue.type ∧
      result.chip.output.type = source.output.type := by
  unfold layOut at compiled
  cases found : checkedLayOut config source with
  | error error => simp [found, Except.map] at compiled
  | ok checked =>
      have same : checked.toLaidOutChip = result := by simpa [found, Except.map] using compiled
      cases same
      exact ⟨checked.name_eq, checked.inputTypes, checked.outputType⟩

end Aiur.Optimized
