import IxSharingVerify.TableSuccess
import IxSharingVerify.WireSuccess
import IxSharingVerify.ReexpandSuccess
import IxSharingVerify.TieredGuard
import IxSharingVerify.FamilyBudget
import IxC.Kernel.Audit.Axioms

/-!
# Re-materialization at the layout widths never refuses

`rematerialize` writes the allocated table again at the real Share widths
and refuses unless its priced length equals the evaluation, is at most the
length of the uniform encoding, re-expands to the table terms and the input
roots, and every expression is in the wire domain. After a successful
uniform phase and allocation on a canonical DAG of fewer than `2^64` terms
whose references carry fewer than `2^64` universes, every check passes under
large enough budgets (`rematerialize_ok`).
-/

namespace Ix.Sharing.Verify.Tiered

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (Desc termOf materializeTable_parts materializeTable_backward
  materializeTable_correct mapM_ok_forall₂ forall₂_getElem materializeStep_spec foldlM_range_inv)
open Ix.Sharing.Verify.CanonicalMeaning (ExpandedOK reexpand_ids dagModel_termOf)
open Ix.Sharing.Verify.Budget (LimitsLe Limits.join materializeTable_mono reexpand_mono)

theorem checkInternal_true {b : Bool} (msg : String) (h : b = true) :
    checkInternal b msg = .ok () := by
  subst h
  rfl

/-- Every expression a successful table materialization writes is in the
wire domain. -/
theorem materializeTable_wire {dag : Dag} (hwf : DagWF dag)
    (fits : ∀ t, t < dag.size → HeadFits (dag.node t).head) (small : dag.size < UInt64.size)
    {table roots : Array Nat} {limits : Limits} {widthAt : Nat → Nat}
    {entries rs : Array Ixon.Expr} {predicted work : Nat}
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (h : materializeTable (Prep.ofDag dag) table roots limits widthAt =
      .ok (entries, rs, predicted, work)) :
    ∀ e ∈ entries.toList ++ rs.toList, (wireCounts e).isSome := by
  have hp := prepWF_ofDag hwf
  obtain ⟨hsize, hrange, st, hst, rfl, hrs, -⟩ := materializeTable_parts _ _ _ _ _ h
  have wire : ∀ k (ev : DictEval) (s : TableState) (t : Nat) (e : Ixon.Expr), k ≤ table.size →
      GEvalOK (Prep.ofDag dag) (prefixWd dag.size table widthAt k) (prefixAvail dag.size table k) ev →
      s.index = indexOfPrefix dag.size table k →
      s.width = (indexOfPrefix dag.size table k).map (·.map widthAt) → t < dag.size →
      (Prep.ofDag dag).build ev s.index s.width false (dag.size + 1) t = .ok e →
      (wireCounts e).isSome := by
    intro k ev s t e hk hev hidx hwid ht hb
    rw [hidx, hwid] at hb
    obtain ⟨c, hc, _⟩ := hp.build_wire fits small ev hev _ _ (prefix_width dag.size table widthAt k)
      (fun u => rfl) (dag.size + 1) false t e ht hb
    simp [hc]
  have loop := foldlM_range_inv _
    (fun k (s : TableState) => k ≤ table.size → TableEvInv dag table widthAt k s ∧
      ∀ e ∈ s.entries.toList, (wireCounts e).isSome)
    (fun i s s' inv stepped le => by
      obtain ⟨hI, hw⟩ := inv (by omega)
      obtain ⟨_, hidx, hwid, hev, _⟩ := id hI
      refine ⟨tableEvInv_step hwf hsize hrange hI (by omega) stepped, ?_⟩
      obtain ⟨e, he, hent, -⟩ := materializeStep_spec stepped
      intro x hx
      rw [hent, Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact hw x hx
      · rw [hx]
        exact wire i s.ev s _ e (by omega) hev hidx hwid (hrange i (by omega)) he)
    table.size _ st (fun _ => by
      refine ⟨?_, fun e he => by simp at he⟩
      have hidx0 := Ix.Sharing.Verify.SharingExact.indexOfPrefix_zero dag.size table
      refine ⟨Nat.zero_le _, by rw [hidx0]; rfl, by rw [hidx0]; simp; rfl, ?_, rfl,
        fun j hj => absurd hj (by simp), by simp⟩
      refine hp.evalAll_ok (ofDag_empty_size dag) _ fun u => ?_
      rw [widthOf_eq]
      unfold prefixAvail
      rw [hidx0]
      simp only [ofDag_dag]
      by_cases hu : u < dag.size
      · simp [hu]
      · simp [hu]; rfl) hst
  obtain ⟨hI, hw⟩ := loop (Nat.le_refl _)
  obtain ⟨_, hidx, hwid, hev, _⟩ := hI
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hw e he
  · rw [Array.mapM_eq_mapM_toList] at hrs
    cases hm : List.mapM (fun r => (Prep.ofDag dag).build st.ev st.index st.width false
        ((Prep.ofDag dag).dag.size + 1) r) roots.toList with
    | error err => rw [hm] at hrs; cases hrs
    | ok l =>
      rw [hm] at hrs
      have : rs = l.toArray := by cases hrs; rfl
      subst this
      obtain ⟨r, hr, hb⟩ := forall₂_mem_right'
        (mapM_ok_forall₂ _ _ _ hm) e (by simpa using he)
      exact wire table.size st.ev st r e (Nat.le_refl _) hev hidx hwid (hroots r hr) hb

theorem forall₂_of_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, xs.length = ys.length →
      (∀ k (h1 : k < xs.length) (h2 : k < ys.length), R xs[k] ys[k]) → List.Forall₂ R xs ys
  | [], [], _, _ => .nil
  | x :: xs, y :: ys, hl, h =>
    .cons (h 0 (by simp) (by simp)) (forall₂_of_getElem (by simpa using hl)
      (fun k h1 h2 => h (k + 1) (by simpa using h1) (by simpa using h2)))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- The entries of a successful table materialization, pointwise. -/
theorem entries_forall₂ {table : Array Nat} {entries : Array Ixon.Expr} {R : Nat → Ixon.Expr → Prop}
    (size : entries.size = table.size)
    (each : ∀ k (hk : k < entries.size), R table[k]! entries[k]) :
    List.Forall₂ R table.toList entries.toList := by
  apply forall₂_of_getElem (by simp [size])
  intro k h1 h2
  have hk : k < entries.size := by simpa using h2
  have := each k hk
  rw [getElem!_pos table k (by omega)] at this
  simpa using this

/-- **Re-materialization never refuses** after a successful uniform phase
and allocation. -/
theorem rematerialize_ok {layout : ShareLayout} {ex : Expanded} (ok : ExpandedOK ex)
    (fits : ∀ t, t < ex.dag.size → HeadFits (ex.dag.node t).head)
    (small : ex.dag.size < UInt64.size) {u : UniformSharingResult} (trees : UniformTrees ex u)
    {allocLimits : Limits} {a : Allocation}
    (ha : allocate layout allocLimits ex.dag (graphFacts ex.dag ex.roots).deg u.result.tableTerms
      u.result.sharing u.result.roots = .ok a) :
    ∃ limits m, rematerialize layout limits ex a.order
      (layoutBytes layout u.result.sharing u.result.roots) = .ok m := by
  have hwf := ok.wf
  obtain ⟨_, _, hin1, hsize1, _, _, _⟩ := id trees
  obtain ⟨hnd1, -, hperm, -⟩ := allocate_spec ha
  have orderIn : ∀ t ∈ a.order.toList, t < ex.dag.size := fun t ht => hin1 t (hperm.subset ht)
  have orderNodup : a.order.toList.Nodup := hperm.nodup_iff.mpr hnd1
  have orderSize : a.order.size = u.result.tableTerms.size := by
    simpa using hperm.length_eq
  obtain ⟨first, ⟨entries, rs, predicted, work⟩, hm⟩ := materializeTable_ok hwf layout.widthAt
    (show a.order.size < wordBound by unfold wordBound; omega) orderIn ok.roots
  obtain ⟨-, -, -, predictedEq⟩ := materializeTable_spec hwf ok.roots hm
  have priced : layoutBytes layout entries rs = predicted := by
    rw [layoutBytes_eq, predictedEq]
  have bound := rematerialized_le_of_trees trees ha hm
  obtain ⟨esSize, backward, rootsBelow⟩ := materializeTable_backward _ _ _ _ _
    (by omega) hm
  obtain ⟨entries', rootRows⟩ := materializeTable_correct _ _ _ _ _ (by omega) hm
    (termOf ex.dag.nodes) (dagModel_termOf hwf)
  have rsSize : rs.size = ex.roots.size := by
    have := (forall₂_getElem rootRows).1
    simpa using this.symm
  obtain ⟨second, visits, reexpanded⟩ := reexpand_ids hwf ok.injective orderIn ok.roots esSize rsSize
    backward rootsBelow (entries_forall₂ esSize entries') rootRows (by unfold wordBound; omega)
  have wire := materializeTable_wire hwf fits small ok.roots hm
  have allWire : ((entries ++ rs).all fun e => (wireCounts e).isSome) = true := by
    rw [Array.all_eq_true']
    intro e he
    exact wire e (by simpa using he)
  let limits := Limits.join first second
  have hm' := materializeTable_mono (LimitsLe.join_left first second) _ _ _ _ hm
  have re := reexpand_mono (LimitsLe.join_right first second) reexpanded
  refine ⟨limits, ?_⟩
  unfold rematerialize
  rw [materializeTableOnePass_eq, Budget.bind_ok_eq hm']
  dsimp only
  rw [checkInternal_true _ (by simp [priced]), checkInternal_true _ (by simp [bound])]
  rw [Budget.bind_ok_eq re]
  dsimp only
  rw [checkInternal_true _ (beq_self_eq_true _), checkInternal_true _ (beq_self_eq_true _),
    checkInternal_true _ allWire]
  exact ⟨_, rfl⟩

end Ix.Sharing.Verify.Tiered

#guard_kernel_axioms Ix.Sharing.Verify.Tiered.materializeTable_wire [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Tiered.rematerialize_ok [propext, Classical.choice, Quot.sound]
