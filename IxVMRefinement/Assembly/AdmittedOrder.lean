import IxVMRefinement.Assembly.AdmittedOverlay

/-! # An exact dependency order for the admitted and walked record union

Walked records come first by their actual trace rank. The remaining admitted records keep
their accepted relative order. This permits a role record to refer to a newly traced record
without assuming that the original role store contained every reference target.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel
open IxVM.Consistency (ReaderAdmissionWitness UsedCompiledReachAt UsedClosureOrderAt)
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

noncomputable def admittedWalkEnv {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) (calls : List (Call F)) (trace : Ixon.Env) : Ixon.Env :=
  admittedOverlay w trace (WkAll calls b.address w.table trace)

noncomputable def admittedWalkRank {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) (calls : List (Call F)) (trace : Ixon.Env)
    (a : _root_.Address) : Nat :=
  letI := Classical.propDecidable
  let rank := rankAll calls b.address w.table trace
  if WkAll calls b.address w.table trace a then rank a
  else (trace.consts.keys.map rank).sum + 1 + w.order.idxOf a

noncomputable def admittedWalkOrder {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) (calls : List (Call F)) (trace : Ixon.Env)
    (seeds : _root_.Address → Prop) : List _root_.Address :=
  letI := Classical.propDecidable
  let allKeys := (w.order ++ trace.consts.keys).eraseDups
  let reachable := allKeys.filter fun a => decide (UsedCompiledReachAt w.table
    (admittedWalkEnv w calls trace) seeds a)
  reachable.mergeSort fun a b => decide (admittedWalkRank w calls trace a ≤ admittedWalkRank w calls trace b)

private theorem le_sum_of_mem {xs : List Nat} {n : Nat} (h : n ∈ xs) : n ≤ xs.sum := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

private theorem idxOf_lt_of_pairwise {α : Type} [BEq α] [LawfulBEq α] {R : α → α → Prop} :
    ∀ {xs : List α} {a b : α}, xs.Pairwise R → a ∈ xs → b ∈ xs →
      (R a b → False) → a ≠ b → xs.idxOf b < xs.idxOf a
  | [], _, _, _, ha, _, _, _ => nomatch ha
  | x :: xs, a, b, hpw, ha, hb, hnot, hne => by
    rw [List.pairwise_cons] at hpw
    by_cases hax : a = x
    · subst a
      have hb_tail : b ∈ xs := by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact (hne rfl).elim
        · exact hb
      exact (hnot (hpw.1 b hb_tail)).elim
    · by_cases hbx : b = x
      · subst b
        rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm hax)]
        omega
      · have ha_tail : a ∈ xs := by
          rcases List.mem_cons.mp ha with rfl | ha
          · exact (hax rfl).elim
          · exact ha
        have hb_tail : b ∈ xs := by
          rcases List.mem_cons.mp hb with rfl | hb
          · exact (hbx rfl).elim
          · exact hb
        have hlt := idxOf_lt_of_pairwise hpw.2 ha_tail hb_tail hnot hne
        rw [List.idxOf_cons_ne _ (Ne.symm hbx), List.idxOf_cons_ne _ (Ne.symm hax)]
        omega

/-- The actual selected union has an exact finite used-reference closure order. Missing
admission-store owners are included when reachable, without inventing a stored row for them. -/
theorem admittedWalkOrder_spec {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (hload : IxVM.Consistency.LoadedBy calls trace) (hdecoded : L1.EnvDecoded trace)
    {extra : List ByteArray} (hno : ¬ V.HashedCollision extra calls)
    (seeds : _root_.Address → Prop) :
    UsedClosureOrderAt w.table (admittedWalkEnv w calls trace) seeds
      (admittedWalkOrder w calls trace seeds) := by
  classical
  let Wk := WkAll calls b.address w.table trace
  let rank := rankAll calls b.address w.table trace
  let E := admittedWalkEnv w calls trace
  have hclosed : ClosedSubwalk calls b.address w.table trace Wk rank :=
    wkAll_closedSubwalk calls b.address w.table trace
  have traceAt {a : _root_.Address} (ha : Wk a) {c : Ixon.Constant}
      (hc : Ix.Cert.recordAt E a = some c) : Ix.Cert.recordAt trace a = some c := by
    obtain ⟨c', htrace, _⟩ := hclosed.checked a ha
    have hkept : Ix.Cert.recordAt E a = some c' :=
      recordAt_subEnv_of_keep trace (admittedKeep w Wk) (roleSuppOf w.env w.order) (.inr ha) htrace
    have heq := Option.some.inj (hkept.symm.trans hc)
    rw [heq] at htrace
    exact htrace
  have roleOwner {a : _root_.Address} {c : Ixon.Constant}
      (ha : a ∈ w.order) (hc : Ix.Cert.recordAt w.env a = some c) :
      Ix.Cert.ownerOf a c ∈ w.order := by
    by_cases heq : Ix.Cert.ownerOf a c = a
    · rwa [heq]
    · exact (w.closure.complete _).mpr
        (.step ((w.closure.complete _).mp ha) ⟨c, hc, .inl ⟨rfl, heq⟩⟩)
  have contains {a : _root_.Address} (ha : E.consts.contains a = true) : a ∈ w.order ∨ Wk a := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?] at ha
    obtain ⟨lc, hget⟩ := Option.isSome_iff_exists.mp ha
    rcases subEnv_get?_some_inv trace (admittedKeep w Wk) (roleSuppOf w.env w.order) hget with
      ⟨hk, _⟩ | ⟨_, _, _, hm, _⟩
    · rcases hk with ⟨ha, _⟩ | hw
      · exact .inl ha
      · exact .inr hw
    · exact .inl (mem_roleSuppOf_iff.mp hm).1
  have reachable {a : _root_.Address} (ha : UsedCompiledReachAt w.table E seeds a) :
      a ∈ w.order ∨ Wk a := by
    induction ha with
    | seed _ stored => exact contains stored
    | step _ hedge _ =>
      obtain ⟨c, hc, hedge⟩ := hedge
      rcases hedge with ⟨rfl, hne⟩ | ⟨_, stored⟩
      · rcases admittedOverlay_recordAt_inv w Wk hload hdecoded hno hc with ⟨ha, hrole⟩ | ⟨hw, _⟩
        · exact .inl (roleOwner ha hrole)
        · exact .inr (hclosed.step _ _ hw ⟨c, traceAt hw hc, .inl ⟨rfl, hne⟩⟩).1
      · exact contains stored
    | ground _ hedge _ => exact contains hedge.1
    | recursor _ hedge _ => exact contains hedge.1
  have rankBound {a : _root_.Address} (ha : Wk a) : rank a < (trace.consts.keys.map rank).sum + 1 := by
    obtain ⟨c, hc, _⟩ := hclosed.checked a ha
    have hkeys := Ix.Cert.Order.mem_keys_of_stored trace hc
    have hsum : rank a ≤ (trace.consts.keys.map rank).sum :=
      le_sum_of_mem (List.mem_map.mpr ⟨a, hkeys, rfl⟩)
    omega
  have rankDecreases {a target : _root_.Address} (href : IxVM.Consistency.UsedRecordRef E a target) :
      admittedWalkRank w calls trace target < admittedWalkRank w calls trace a := by
    obtain ⟨c, hc, i, hi, ref, href, cr, hcr, howner, hne⟩ := href
    have walkOwner (hr : Wk ref) : Wk target ∧ rank target ≤ rank ref := by
      by_cases heq : target = ref
      · rw [heq]; exact ⟨hr, Nat.le_refl _⟩
      · obtain ⟨ht, hlt⟩ := hclosed.step ref target hr
          ⟨cr, traceAt hr hcr, .inl ⟨howner, heq⟩⟩
        exact ⟨ht, Nat.le_of_lt hlt⟩
    by_cases ha : Wk a
    · have hi' : i ∈ Core.S0.usedRefIdxs c := by rwa [usedRefIdxs_eq]
      obtain ⟨hr, hlt⟩ := hclosed.step a ref ha ⟨c, traceAt ha hc, .inr ⟨i, hi', href⟩⟩
      obtain ⟨ht, hle⟩ := walkOwner hr
      simp only [admittedWalkRank, show WkAll calls b.address w.table trace a from ha,
        show WkAll calls b.address w.table trace target from ht, ↓reduceIte]
      change rank target < rank a
      omega
    · by_cases ht : Wk target
      · have hb := rankBound ht
        simp only [admittedWalkRank, show ¬ WkAll calls b.address w.table trace a from ha,
          show WkAll calls b.address w.table trace target from ht, ↓reduceIte]
        change rank target < (trace.consts.keys.map rank).sum + 1 + w.order.idxOf a
        omega
      · have hr : ¬ Wk ref := fun hr => ht (walkOwner hr).1
        have roleA : a ∈ w.order ∧ Ix.Cert.recordAt w.env a = some c := by
          rcases admittedOverlay_recordAt_inv w Wk hload hdecoded hno hc with h | ⟨hw, _⟩
          · exact h
          · exact (ha hw).elim
        have roleR : ref ∈ w.order ∧ Ix.Cert.recordAt w.env ref = some cr := by
          rcases admittedOverlay_recordAt_inv w Wk hload hdecoded hno hcr with h | ⟨hw, _⟩
          · exact h
          · exact (hr hw).elim
        have roleT : target ∈ w.order := by simpa only [howner] using roleOwner roleR.1 roleR.2
        have original : Ix.Cert.RecordRef w.env a target :=
          ⟨c, roleA.2, ref, Array.mem_of_getElem? href, cr, roleR.2, howner, hne⟩
        have hlt := idxOf_lt_of_pairwise w.closure.ordered roleA.1 roleT (fun h => h original) hne.symm
        simp only [admittedWalkRank, show ¬ WkAll calls b.address w.table trace a from ha,
          show ¬ WkAll calls b.address w.table trace target from ht, ↓reduceIte]
        omega
  let allKeys := (w.order ++ trace.consts.keys).eraseDups
  let selected := allKeys.filter fun a => decide (UsedCompiledReachAt w.table E seeds a)
  have hnd : selected.Nodup := List.nodup_eraseDups.filter _
  have members (a : _root_.Address) : a ∈ selected ↔ UsedCompiledReachAt w.table E seeds a := by
    simp only [selected, List.mem_filter, decide_eq_true_eq]
    refine ⟨And.right, fun ha => ⟨?_, ha⟩⟩
    rcases reachable ha with role | walked
    · simp [allKeys, role]
    · obtain ⟨c, hc, _⟩ := hclosed.checked a walked
      have hk := Ix.Cert.Order.mem_keys_of_stored trace hc
      simp [allKeys, hk]
  have perm := List.mergeSort_perm selected fun a b =>
    decide (admittedWalkRank w calls trace a ≤ admittedWalkRank w calls trace b)
  refine ⟨perm.nodup_iff.mpr hnd, fun a => perm.mem_iff.trans (members a), ?_⟩
  have sorted := List.pairwise_mergeSort
    (le := fun a b => decide (admittedWalkRank w calls trace a ≤ admittedWalkRank w calls trace b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) selected
  refine sorted.imp fun {a target} hle href => ?_
  have hlt := rankDecreases href
  simp only [decide_eq_true_eq] at hle
  omega

end IxVM.Refinement.Assembly
