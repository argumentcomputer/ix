import IxCC.Aiur.Trace

namespace IxCC.Aiur.Trace

open _root_.IxCC.Vendor.Aiur (G gSize)

theorem providerSum_zero (message : Message) (rows : List Row)
    (zero : ∀ row ∈ rows, row.provides = message → row.multiplicity = 0) :
    providerSum message rows = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have tail := ih (fun r hr => zero r (List.mem_cons_of_mem _ hr))
    simp only [providerSum, tail, Field.add_zero]
    split
    · exact zero row List.mem_cons_self ‹row.provides = message›
    · rfl

theorem providerSum_ne_zero (message : Message) (rows : List Row)
    (nonzero : providerSum message rows ≠ 0) :
    ∃ row ∈ rows, row.provides = message ∧ row.multiplicity ≠ 0 := by
  classical
  apply Classical.byContradiction
  intro absent
  apply nonzero
  apply providerSum_zero
  intro row member equal
  apply Classical.byContradiction
  intro nonzero
  exact absent ⟨row, member, equal, nonzero⟩

theorem public_mem_requirements (trace : Trace) {message : Message}
    (member : message ∈ trace.publicClaims) : message ∈ trace.requirements := by
  exact List.mem_append_left _ member

theorem demand_mem_requirements (trace : Trace) (id : trace.RowId)
    (active : (trace.row id).active = true) {message : Message}
    (member : message ∈ (trace.row id).demands) : message ∈ trace.requirements := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨trace.row id, trace.row_mem id, by simpa [active] using member⟩

/-- The nonzero embedding of a nonempty demand count forces a matching
nonzero provider. Activity then makes it a usable row. No natural-number
interpretation of provider multiplicities is needed. -/
theorem provider_exists (trace : Trace) (activity : trace.Activity)
    (balanced : trace.Balanced) (bound : trace.WithinCharacteristic)
    {message : Message} (demanded : message ∈ trace.requirements) :
    ∃ id : trace.RowId, (trace.row id).provides = message ∧
      (trace.row id).multiplicity ≠ 0 ∧ (trace.row id).active = true := by
  have positive : 0 < trace.demandCount message := List.count_pos_iff.mpr demanded
  have countBound : trace.demandCount message < gSize.toNat := by
    have countLe : trace.demandCount message ≤ trace.requirements.length := List.count_le_length
    unfold WithinCharacteristic unitSlots at bound
    omega
  have nonzero := Field.ofNat_ne_zero positive countBound
  rw [balanced message] at nonzero
  obtain ⟨row, member, sameMessage, weight⟩ := providerSum_ne_zero message trace.rows nonzero
  obtain ⟨index, inBounds, equal⟩ := List.mem_iff_getElem.mp member
  refine ⟨⟨index, inBounds⟩, ?_⟩
  change trace.rows[index].provides = message ∧
    trace.rows[index].multiplicity ≠ 0 ∧ trace.rows[index].active = true
  rw [equal]
  exact ⟨sameMessage, weight, activity row member weight⟩

end IxCC.Aiur.Trace
