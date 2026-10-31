import IxSharingVerify.BuildSuccess
import IxSharingVerify.TieredPhase3
import IxSharingVerify.BudgetMono
import IxC.Kernel.Audit.Axioms

/-!
# Materializing a table never refuses

`materializeTable` writes a table entry by entry, each against the
dictionary of the entries before it, then the roots against the whole
table. Its only refusals besides `build` are its two budgets, the
materialized length and the materialization work. Every value it compares
with them is determined by the run, which never depends on the budgets, so
some budget covers them all (`materializeTable_ok`): `build` never refuses
an evaluation of the prefix dictionary (`PrepWF.build_ok`).
-/

namespace Ix.Sharing.Verify.Tiered

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (indexOfPrefix_zero)

/-- The step of the table loop succeeds once its two values fit, with a
next state that does not depend on the budgets. -/
theorem materializeStep_ok {dag : Dag} (hwf : DagWF dag) {table : Array Nat} {widthAt : Nat → Nat}
    (hsize : table.size < UInt64.size) (hrange : ∀ k, k < table.size → table[k]! < dag.size)
    {i : Nat} {st : TableState} (hI : TableEvInv dag table widthAt i st) (hi : i < table.size) :
    ∃ bound next, TableEvInv dag table widthAt (i + 1) next ∧
      ∀ limits : Limits, bound ≤ limits.maxMaterialize → bound ≤ limits.maxMaterializeWork →
        materializeStep (Prep.ofDag dag) table limits widthAt st i = .ok next := by
  have hp := prepWF_ofDag hwf
  obtain ⟨hle, hidx, hwid, hev, hsz, hent, hpred⟩ := hI
  have hwidth : ∀ u, widthOf st.width u = if prefixAvail dag.size table i u then
      some (prefixWd dag.size table widthAt i u) else none := by
    intro u; rw [hwid]; exact prefix_width dag.size table widthAt i u
  have hindex : ∀ u, (st.index[u]?.getD none).isSome = prefixAvail dag.size table i u := by
    intro u; rw [hidx]; rfl
  have ht := hrange i hi
  obtain ⟨e, he⟩ := hp.build_ok st.ev hev st.index st.width hwidth hindex
    ((Prep.ofDag dag).dag.size + 1) false table[i]! ht (by simp only [ofDag_dag]; omega)
  let c := st.ev.cost[table[i]!]!
  let work := st.work + st.ev.work + c
  let next : TableState :=
    { entries := st.entries.push e, index := st.index.set! table[i]! (some i),
      width := st.width.set! table[i]! (some (widthAt i)),
      ev := (Prep.ofDag dag).evalUp st.ev (st.width.set! table[i]! (some (widthAt i))) table[i]!,
      predicted := st.predicted + c, work }
  have stepped : ∀ limits : Limits, max c work ≤ limits.maxMaterialize →
      max c work ≤ limits.maxMaterializeWork →
      materializeStep (Prep.ofDag dag) table limits widthAt st i = .ok next := by
    intro limits room roomWork
    have h1 := Nat.le_max_left c work
    have h2 := Nat.le_max_right c work
    unfold materializeStep
    dsimp only
    rw [ite_eq_right (show ¬ c > limits.maxMaterialize by omega), Budget.bind_ok_eq he]
    try dsimp only
    rw [ite_eq_right (show ¬ work > limits.maxMaterializeWork by omega)]
    rfl
  refine ⟨max c work, next, ?_, stepped⟩
  exact tableEvInv_step hwf hsize hrange ⟨hle, hidx, hwid, hev, hsz, hent, hpred⟩ hi (stepped { maxMaterialize := max c work, maxMaterializeWork := max c work }
      (Nat.le_refl _) (Nat.le_refl _))

theorem materializeLoop_ok {dag : Dag} (hwf : DagWF dag) {table : Array Nat} {widthAt : Nat → Nat}
    (hsize : table.size < UInt64.size) (hrange : ∀ k, k < table.size → table[k]! < dag.size) :
    ∀ count i (st : TableState), i + count = table.size → TableEvInv dag table widthAt i st →
      ∃ bound final, TableEvInv dag table widthAt table.size final ∧
        ∀ limits : Limits, bound ≤ limits.maxMaterialize → bound ≤ limits.maxMaterializeWork →
          (List.range' i count).foldlM (materializeStep (Prep.ofDag dag) table limits widthAt) st =
            .ok final := by
  intro count
  induction count with
  | zero =>
    intro i st sum hI
    have : i = table.size := by omega
    subst this
    exact ⟨0, st, hI, fun _ _ _ => rfl⟩
  | succ count ih =>
    intro i st sum hI
    obtain ⟨b1, next, hnext, step⟩ := materializeStep_ok hwf hsize hrange hI (by omega)
    obtain ⟨b2, final, hfinal, rest⟩ := ih (i + 1) next (by omega) hnext
    refine ⟨max b1 b2, final, hfinal, fun limits room roomWork => ?_⟩
    have := Nat.le_max_left b1 b2
    have := Nat.le_max_right b1 b2
    rw [List.range'_succ, List.foldlM_cons, step limits (by omega) (by omega)]
    exact rest limits (by omega) (by omega)

/-- **`materializeTable` never refuses** a table of DAG terms that fits the
Share word, under large enough budgets. -/
theorem materializeTable_ok {dag : Dag} (hwf : DagWF dag) {table roots : Array Nat}
    (widthAt : Nat → Nat) (hsize : table.size < wordBound)
    (hrange : ∀ t ∈ table.toList, t < dag.size) (hroots : ∀ r ∈ roots.toList, r < dag.size) :
    ∃ limits out, materializeTable (Prep.ofDag dag) table roots limits widthAt = .ok out := by
  have hp := prepWF_ofDag hwf
  have hrange' : ∀ k, k < table.size → table[k]! < dag.size := by
    intro k hk
    rw [getElem!_pos table k hk]
    exact hrange _ (Array.getElem_mem_toList hk)
  have hsize' : table.size < UInt64.size := hsize
  have hidx0 := indexOfPrefix_zero dag.size table
  have init : TableEvInv dag table widthAt 0
      { entries := #[], index := Array.replicate (Prep.ofDag dag).dag.size none,
        width := Array.replicate (Prep.ofDag dag).dag.size none,
        ev := (Prep.ofDag dag).evalAll (Array.replicate (Prep.ofDag dag).dag.size none),
        predicted := tag0Size table.size, work := 0 } := by
    refine ⟨Nat.zero_le _, by rw [hidx0]; rfl, by rw [hidx0]; simp; rfl, ?_, rfl,
      fun j hj => absurd hj (by simp), by simp⟩
    refine hp.evalAll_ok (ofDag_empty_size dag) _ fun u => ?_
    rw [widthOf_eq]
    unfold prefixAvail
    rw [hidx0]
    simp only [ofDag_dag]
    by_cases hu : u < dag.size
    · simp [hu]
    · simp [hu]; rfl
  obtain ⟨bound, final, hfinal, loop⟩ := materializeLoop_ok hwf hsize' hrange' table.size 0 _
    (by omega) init
  obtain ⟨_, hidx, hwid, hev, _, _, _⟩ := hfinal
  have hwidth : ∀ u, widthOf final.width u = if prefixAvail dag.size table table.size u then
      some (prefixWd dag.size table widthAt table.size u) else none := by
    intro u; rw [hwid]; exact prefix_width dag.size table widthAt table.size u
  have hindex : ∀ u, (final.index[u]?.getD none).isSome = prefixAvail dag.size table table.size u := by
    intro u; rw [hidx]; rfl
  obtain ⟨rs, hrs⟩ := array_mapM_ok _ roots (fun r hr =>
    hp.build_ok final.ev hev final.index final.width hwidth hindex ((Prep.ofDag dag).dag.size + 1)
      false r (hroots r hr) (by have := hroots r hr; simp only [ofDag_dag]; omega))
  let rootCost := roots.foldl (fun acc r => acc + final.ev.cost[r]!) 0
  let lastWork := final.work + final.ev.work + rootCost
  let top := max bound (max rootCost lastWork)
  have h1 := Nat.le_max_left bound (max rootCost lastWork)
  have h2 := Nat.le_max_left rootCost lastWork
  have h3 := Nat.le_max_right rootCost lastWork
  have h4 := Nat.le_max_right bound (max rootCost lastWork)
  let limits : Limits := { maxMaterialize := top, maxMaterializeWork := top }
  refine ⟨limits, ?_⟩
  unfold materializeTable
  rw [ite_eq_right (show ¬ table.size ≥ wordBound by omega)]
  have allIn : table.all (· < (Prep.ofDag dag).dag.size) = true := by
    rw [Array.all_eq_true']
    intro t member
    exact decide_eq_true (hrange t (Array.mem_toList_iff.mpr member))
  rw [ite_eq_right (by simp [allIn])]
  rw [List.range_eq_range', Budget.bind_ok_eq (loop limits h1 (by omega))]
  dsimp only
  rw [ite_eq_right (show ¬ rootCost > top by omega), Budget.bind_ok_eq hrs]
  try dsimp only
  rw [ite_eq_right (show ¬ lastWork > top by omega)]
  exact ⟨_, rfl⟩

end Ix.Sharing.Verify.Tiered

#guard_kernel_axioms Ix.Sharing.Verify.Tiered.materializeTable_ok [propext, Classical.choice, Quot.sound]
