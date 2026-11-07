import IxCC.Aiur.AIR.Rank.Range

/-! Scalar-range provider existence from normalized physical lookup
balance. Weights are field elements, not natural counts; the fixed-table
row index and full two-field message remain part of the argument. -/

namespace IxCC.Aiur.AIR.Rank

open _root_.Aiur (G gSize)

structure RangeRow where
  index : Fin limbBound
  multiplicity : G

def RangeRow.message (row : RangeRow) : List G := [15, rangeValue row.index.val]

def rangeProviderSum (message : List G) : List RangeRow → G
  | [] => 0
  | row :: rows =>
      (if row.message = message then row.multiplicity else 0) + rangeProviderSum message rows

/-- Balance for this physical channel after selected unit pushes and
negative table pulls have been separated. Other channels cannot supply
these complete messages. The full AIR adapter must establish this premise. -/
def RangeBalanced (demands : List (List G)) (providers : List RangeRow) : Prop :=
  ∀ value, G.ofNat (demands.count [15, value]) = rangeProviderSum [15, value] providers

theorem rangeProviderSum_zero (message : List G) (rows : List RangeRow)
    (zero : ∀ row ∈ rows, row.message = message → row.multiplicity = 0) :
    rangeProviderSum message rows = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have tail := ih (fun r hr => zero r (List.mem_cons_of_mem _ hr))
    simp only [rangeProviderSum, tail, Field.add_zero]
    split
    · exact zero row List.mem_cons_self ‹row.message = message›
    · rfl

theorem rangeProviderSum_ne_zero (message : List G) (rows : List RangeRow)
    (nonzero : rangeProviderSum message rows ≠ 0) :
    ∃ row ∈ rows, row.message = message ∧ row.multiplicity ≠ 0 := by
  classical
  apply Classical.byContradiction
  intro absent
  apply nonzero
  apply rangeProviderSum_zero
  intro row member equal
  apply Classical.byContradiction
  intro weight
  exact absent ⟨row, member, equal, weight⟩

theorem rangeProvided_of_balance {demands : List (List G)} {providers : List RangeRow}
    (balanced : RangeBalanced demands providers) (budget : demands.length < gSize.toNat)
    {value : G} (requested : [15, value] ∈ demands) : RangeProvided value := by
  have positive : 0 < demands.count [15, value] := List.count_pos_iff.mpr requested
  have countBound : demands.count [15, value] < gSize.toNat :=
    Nat.lt_of_le_of_lt List.count_le_length budget
  have nonzero := Field.ofNat_ne_zero positive countBound
  rw [balanced value] at nonzero
  obtain ⟨row, _, message, _⟩ := rangeProviderSum_ne_zero _ providers nonzero
  exact ⟨row.index.val, row.index.isLt, message.symm⟩

theorem range_bound_of_balance {demands : List (List G)} {providers : List RangeRow}
    (balanced : RangeBalanced demands providers) (budget : demands.length < gSize.toNat)
    {value : G} (requested : [15, value] ∈ demands) : value.n < limbBound :=
  (rangeProvided_iff value).mp (rangeProvided_of_balance balanced budget requested)

def Limbs.requests (limbs : Limbs) : List (List G) :=
  [[15, limbs.low], [15, limbs.middle], [15, limbs.high]]

theorem Limbs.ranges_of_balance {demands : List (List G)} {providers : List RangeRow}
    (balanced : RangeBalanced demands providers) (budget : demands.length < gSize.toNat)
    (limbs : Limbs) (requested : ∀ message ∈ limbs.requests, message ∈ demands) :
    limbs.RangeProvided := by
  exact ⟨rangeProvided_of_balance balanced budget (requested _ (by simp [Limbs.requests])),
    rangeProvided_of_balance balanced budget (requested _ (by simp [Limbs.requests])),
    rangeProvided_of_balance balanced budget (requested _ (by simp [Limbs.requests]))⟩

theorem ordered_of_balance {demands : List (List G)} {providers : List RangeRow}
    (balanced : RangeBalanced demands providers) (budget : demands.length < gSize.toNat)
    {parent gap child : Limbs}
    (requested : ∀ message ∈ parent.requests ++ gap.requests ++ child.requests, message ∈ demands)
    (binding : ordered parent gap = child.packed) :
    child.value = parent.value + 1 + gap.value ∧ parent.value < child.value := by
  apply ordered_from_range
  · exact parent.ranges_of_balance balanced budget (fun message member => requested message (by simp [member]))
  · exact gap.ranges_of_balance balanced budget (fun message member => requested message (by simp [member]))
  · exact child.ranges_of_balance balanced budget (fun message member => requested message (by simp [member]))
  · exact binding

end IxCC.Aiur.AIR.Rank
