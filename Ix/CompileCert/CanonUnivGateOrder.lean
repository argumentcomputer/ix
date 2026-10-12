import Ix.CompileCert.CanonUnivMeaning
import Ix.CompileCert.CanonUnivPaths

/-! Refinement and prefix laws for the actual gate-order loop. The order-only
view is proved equal to the producer; it installs no runtime substitution.
Sorted prefix contexts recover the same gate prefix, with their hypotheses
discharged for the paths produced by normalization. -/

namespace Ix.CompileCert.CanonUnivGateOrder

open Ixon Ixon.CanonUniv Ix.CompileCert.CanonUnivMeaning

def chooseGate (norm : CNorm) (chosen remaining : List UInt64) (nonempty : remaining ≠ []) : UInt64 :=
  (remaining.find? (absorbable norm chosen)).getD (remaining.head nonempty)

theorem chooseGate_mem (norm : CNorm) (chosen remaining : List UInt64) (nonempty : remaining ≠ []) :
    chooseGate norm chosen remaining nonempty ∈ remaining := by
  unfold chooseGate
  cases found : remaining.find? (absorbable norm chosen) with
  | none => exact List.head_mem nonempty
  | some gate => exact List.mem_of_find?_eq_some found

theorem find_filter_kept (predicate keep : UInt64 → Bool) (items : List UInt64) {gate : UInt64}
    (found : items.find? predicate = some gate) (kept : keep gate = true) :
    (items.filter keep).find? predicate = some gate := by
  induction items with
  | nil => simp at found
  | cons head rest ih =>
    simp only [List.find?_cons] at found
    split at found
    · rename_i accepted
      cases Option.some.inj found
      simp [kept, accepted]
    · rename_i refused
      by_cases keepHead : keep head = true <;>
        simp [keepHead, refused, ih found]

theorem chooseGate_filter (norm : CNorm) (chosen remaining : List UInt64) (nonempty : remaining ≠ [])
    (keep : UInt64 → Bool) (kept : keep (chooseGate norm chosen remaining nonempty) = true)
    (filtered : remaining.filter keep ≠ []) :
    chooseGate norm chosen (remaining.filter keep) filtered = chooseGate norm chosen remaining nonempty := by
  cases found : remaining.find? (absorbable norm chosen) with
  | none =>
    have filteredNone : (remaining.filter keep).find? (absorbable norm chosen) = none := by
      apply List.find?_eq_none.mpr
      intro gate member
      exact List.find?_eq_none.mp found gate (List.mem_filter.mp member).1
    have headKept : keep (remaining.head nonempty) = true := by simpa [chooseGate, found] using kept
    simpa only [chooseGate, found, filteredNone, Option.getD_none] using List.head_filter_of_pos nonempty headKept
  | some gate =>
    have gateKept : keep gate = true := by simpa [chooseGate, found] using kept
    have same := find_filter_kept (absorbable norm chosen) keep remaining found gateKept
    simp only [chooseGate, found, same, Option.getD_some]

/-- A total order-only view of the loop. Its equality with the production
loop below is proved; it does not replace any executable compiler code. -/
def orderAux (norm : CNorm) (chosen remaining : List UInt64) : List UInt64 :=
  if empty : remaining = [] then []
  else
    let gate := chooseGate norm chosen remaining empty
    gate :: orderAux norm (chosen ++ [gate]) (remaining.filter (· != gate))
termination_by remaining.length
decreasing_by
  rw [List.unattach_filter (g := fun value => value != gate) (hf := fun _ _ => rfl), List.unattach_attach]
  change (remaining.filter (· != gate)).length < remaining.length
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨gate, chooseGate_mem norm chosen remaining empty, by simp⟩

theorem orderAux_nil (norm : CNorm) (chosen : List UInt64) : orderAux norm chosen [] = [] := by
  rw [orderAux]
  simp

theorem gateLoop_order (norm : CNorm) (state : GateState) :
    (gateLoop norm state).1 = state.1 ++ orderAux norm state.1 state.2.2 := by
  induction state using (measure (fun state : GateState => state.2.2.length)).wf.induction with
  | h state ih =>
    rcases state with ⟨chosen, flag, remaining⟩
    rw [gateLoop_eq, orderAux]
    by_cases empty : remaining = []
    · subst remaining
      simp [gateStep, pure]
    · cases found : remaining.find? (absorbable norm chosen) with
      | none =>
        have member := List.head_mem empty
        have smaller : (remaining.filter (· != remaining.head empty)).length < remaining.length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨_, member, by simp⟩
        have next := ih (chosen ++ [remaining.head empty], false,
          remaining.filter (· != remaining.head empty)) smaller
        simpa [gateStep, empty, found, chooseGate, pure, List.append_assoc] using next
      | some gate =>
        have member := List.mem_of_find?_eq_some found
        have smaller : (remaining.filter (· != gate)).length < remaining.length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨_, member, by simp⟩
        have next := ih (chosen ++ [gate], flag, remaining.filter (· != gate)) smaller
        simpa [gateStep, empty, found, chooseGate, pure, List.append_assoc] using next

theorem gateOrder_eq (norm : CNorm) (context : CPath) : gateOrder norm context = orderAux norm [] context := by
  unfold gateOrder
  rw [gateOrderChecked_eq]
  simpa using gateLoop_order norm ([], true, context)

theorem orderAux_mem (norm : CNorm) (chosen remaining : List UInt64) (query : UInt64) :
    query ∈ orderAux norm chosen remaining ↔ query ∈ remaining := by
  induction remaining using (measure (fun xs : List UInt64 => xs.length)).wf.induction generalizing chosen with
  | h remaining ih =>
    rw [orderAux]
    split
    · rename_i empty
      simp [empty]
    · rename_i nonempty
      let gate := chooseGate norm chosen remaining nonempty
      have member := chooseGate_mem norm chosen remaining nonempty
      have smaller : (remaining.filter (· != gate)).length < remaining.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨gate, member, by simp⟩
      change (query ∈ gate :: orderAux norm (chosen ++ [gate]) (remaining.filter (· != gate))) ↔ _
      rw [List.mem_cons, ih _ smaller]
      by_cases same : query = gate <;> simp_all

theorem orderAux_nodup (norm : CNorm) (chosen remaining : List UInt64) :
    (orderAux norm chosen remaining).Nodup := by
  induction remaining using (measure (fun xs : List UInt64 => xs.length)).wf.induction generalizing chosen with
  | h remaining ih =>
    rw [orderAux]
    split
    · simp
    · rename_i nonempty
      let gate := chooseGate norm chosen remaining nonempty
      have member := chooseGate_mem norm chosen remaining nonempty
      have smaller : (remaining.filter (· != gate)).length < remaining.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨gate, member, by simp⟩
      apply List.nodup_cons.mpr
      constructor
      · rw [orderAux_mem]
        simp
      · exact ih _ smaller (chosen ++ [gate])

theorem orderAux_length_le (norm : CNorm) (chosen remaining : List UInt64) :
    (orderAux norm chosen remaining).length ≤ remaining.length := by
  induction remaining using (measure (fun xs : List UInt64 => xs.length)).wf.induction generalizing chosen with
  | h remaining ih =>
    rw [orderAux]
    split
    · simp
    · rename_i nonempty
      let gate := chooseGate norm chosen remaining nonempty
      have member := chooseGate_mem norm chosen remaining nonempty
      have smaller : (remaining.filter (· != gate)).length < remaining.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨gate, member, by simp⟩
      have bound := ih _ smaller (chosen ++ [gate])
      change (orderAux norm (chosen ++ [gate]) (remaining.filter (· != gate))).length + 1 ≤ remaining.length
      omega

theorem gateOrder_nodup (norm : CNorm) (context : CPath) : (gateOrder norm context).Nodup := by
  rw [gateOrder_eq]
  exact orderAux_nodup norm [] context

theorem gateOrder_length_le (norm : CNorm) (context : CPath) :
    (gateOrder norm context).length ≤ context.length := by
  rw [gateOrder_eq]
  exact orderAux_length_le norm [] context

/-- Restricting the candidate list to an initial part of its computed order
reproduces that part exactly, preserving the original candidate priority. -/
theorem orderAux_restrict (norm : CNorm) (chosen remaining : List UInt64) (count : Nat) :
    orderAux norm chosen (remaining.filter (fun gate => ((orderAux norm chosen remaining).take count).contains gate)) =
      (orderAux norm chosen remaining).take count := by
  induction count generalizing chosen remaining with
  | zero =>
    have filtered : remaining.filter (fun _ => false) = [] := by simp
    simp only [List.take_zero, List.contains_nil, filtered, orderAux_nil]
  | succ count ih =>
    by_cases empty : remaining = []
    · subst remaining; simp only [List.filter_nil, orderAux_nil, List.take_nil]
    · let gate := chooseGate norm chosen remaining empty
      let rest := remaining.filter (· != gate)
      let tailOrder := orderAux norm (chosen ++ [gate]) rest
      have unfolds : orderAux norm chosen remaining = gate :: tailOrder := by
        rw [orderAux]
        simp only [empty, ↓reduceDIte]
        rfl
      rw [unfolds]
      change orderAux norm chosen (remaining.filter (fun value => (gate :: tailOrder.take count).contains value)) =
        gate :: tailOrder.take count
      let keep : UInt64 → Bool := (gate :: tailOrder.take count).contains
      have kept : keep gate = true := by simp [keep]
      have member := chooseGate_mem norm chosen remaining empty
      have filtered : remaining.filter keep ≠ [] :=
        List.ne_nil_of_mem (List.mem_filter.mpr ⟨member, kept⟩)
      have same := chooseGate_filter norm chosen remaining empty keep kept filtered
      change orderAux norm chosen (remaining.filter keep) = gate :: tailOrder.take count
      rw [orderAux]
      simp only [filtered, ↓reduceDIte, same]
      have remainingEq : (remaining.filter keep).filter (· != gate) =
          rest.filter (fun value => (tailOrder.take count).contains value) := by
        dsimp only [rest]
        rw [List.filter_filter, List.filter_filter]
        congr 1
        funext value
        by_cases equal : value = gate <;> simp [keep, equal, Bool.and_comm]
      change gate :: orderAux norm (chosen ++ [gate]) ((remaining.filter keep).filter (· != gate)) =
        gate :: tailOrder.take count
      rw [remainingEq]
      exact congrArg (List.cons gate) (ih (chosen ++ [gate]) rest)

theorem gateOrder_restrict (norm : CNorm) (context : CPath) (count : Nat) :
    gateOrder norm (context.filter (fun gate => ((gateOrder norm context).take count).contains gate)) =
      (gateOrder norm context).take count := by
  simp only [gateOrder_eq]
  exact orderAux_restrict norm [] context count

theorem sorted_take_filter (context selected : CPath)
    (sorted : context.Pairwise (· ≤ ·)) (unique : context.Nodup) (selectedUnique : selected.Nodup)
    (inside : ∀ gate ∈ selected, gate ∈ context) :
    context.filter (fun gate => selected.contains gate) = selected.mergeSort (· ≤ ·) := by
  have filteredUnique : (context.filter (fun gate => selected.contains gate)).Nodup :=
    List.Pairwise.filter _ unique
  have filteredPerm : List.Perm (context.filter (fun gate => selected.contains gate)) selected := by
    apply (List.perm_ext_iff_of_nodup filteredUnique selectedUnique).mpr
    intro gate
    constructor
    · intro member
      exact List.contains_iff_mem.mp (List.mem_filter.mp member).2
    · intro member
      exact List.mem_filter.mpr ⟨inside gate member, List.contains_iff_mem.mpr member⟩
  have sortedSelected : (selected.mergeSort (· ≤ ·)).Pairwise (· ≤ ·) := by
    have ordered := List.pairwise_mergeSort (le := fun a b : UInt64 => decide (a ≤ b))
      (fun a b c ab bc => decide_eq_true (UInt64.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc)))
      (fun a b => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using UInt64.le_total a b) selected
    simpa only [decide_eq_true_eq] using ordered
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => UInt64.le_antisymm ab ba)
    (List.Pairwise.filter _ sorted) sortedSelected
    (filteredPerm.trans (List.mergeSort_perm selected (· ≤ ·)).symm)

/-- The sorted prefix context used by marker consumption reconstructs exactly
that prefix of the actual gate order. Sortedness and uniqueness will be
supplied by the producer's path invariant. -/
theorem gateOrder_sorted_prefix (norm : CNorm) (context : CPath)
    (sorted : context.Pairwise (· ≤ ·)) (unique : context.Nodup) (count : Nat) :
    gateOrder norm (((gateOrder norm context).take count).mergeSort (· ≤ ·)) =
      (gateOrder norm context).take count := by
  have selectedUnique : ((gateOrder norm context).take count).Nodup :=
    List.Pairwise.take (gateOrder_nodup norm context)
  have inside : ∀ gate ∈ (gateOrder norm context).take count, gate ∈ context := by
    intro gate member
    exact (gateOrder_members norm context gate).mp (List.mem_of_mem_take member)
  rw [← sorted_take_filter context _ sorted unique selectedUnique inside]
  exact gateOrder_restrict norm context count

theorem normalize_prefix (level : Univ) (path : CPath) (node : CNode)
    (member : (path, node) ∈ (normalize level).toList) (count : Nat) :
    gateOrder (normalize level) (((gateOrder (normalize level) path).take count).mergeSort (· ≤ ·)) =
      (gateOrder (normalize level) path).take count := by
  have strict := CanonUnivPaths.normalize_strictPaths level path node member
  exact gateOrder_sorted_prefix (normalize level) path strict.sorted strict.nodup count

theorem normalize_filtered_prefix (level : Univ) (path : CPath) (node : CNode)
    (member : (path, node) ∈ (normalize level).toList) (parameter : UInt64) (count : Nat) :
    let context := path.filter (· != parameter)
    gateOrder (normalize level) (((gateOrder (normalize level) context).take count).mergeSort (· ≤ ·)) =
      (gateOrder (normalize level) context).take count := by
  have strict : CanonUnivPaths.StrictPath (path.filter (· != parameter)) :=
    List.Pairwise.filter _ (CanonUnivPaths.normalize_strictPaths level path node member)
  exact gateOrder_sorted_prefix (normalize level) _ strict.sorted strict.nodup count

/-- The source context of every consumed marker is strictly shorter than the
group whose gate order consumes it. This is the measure for consumption chains. -/
theorem consumption_context_shorter (norm : CNorm) (context : CPath) (index : Nat)
    (inside : index < (gateOrder norm context).length) :
    (((gateOrder norm context).take index).mergeSort (· ≤ ·)).length < context.length := by
  have lengthBound := gateOrder_length_le norm context
  simp only [List.length_mergeSort, List.length_take]
  omega

end Ix.CompileCert.CanonUnivGateOrder

