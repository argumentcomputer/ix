import Ix.Compile.Verify.UniformDecomp

/-!
# Runtime-checked facts of the uniform search

Specifications of the checkers the optimizer runs: `reachLabels` /
`labelsSeparated` (the labels reachable along non-opaque paths) and
`componentsChecked` (the uncertain components are a separated partition).
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Compile.Verify.SharingExact (child_eq_getElem)

/-! ## Reach summaries -/

/-- `x` allows label `ℓ`: it records several labels, or exactly `ℓ`. -/
def Allows (x : Option (Option Nat)) (ℓ : Nat) : Prop := x = some none ∨ x = some (some ℓ)

theorem allows_join_left {a : Option (Option Nat)} {ℓ : Nat} (h : Allows a ℓ)
    (b : Option (Option Nat)) : Allows (labelJoin a b) ℓ := by
  rcases h with rfl | rfl
  · rcases b with _ | _ | b <;> simp [labelJoin, Allows]
  · rcases b with _ | _ | b
    · simp [labelJoin, Allows]
    · simp [labelJoin, Allows]
    · unfold labelJoin Allows
      by_cases hab : ℓ = b
      · simp [hab]
      · simp [hab]

theorem allows_join_right {b : Option (Option Nat)} {ℓ : Nat} (h : Allows b ℓ)
    (a : Option (Option Nat)) : Allows (labelJoin a b) ℓ := by
  rcases h with rfl | rfl
  · rcases a with _ | _ | a <;> simp [labelJoin, Allows]
  · rcases a with _ | _ | a
    · simp [labelJoin, Allows]
    · simp [labelJoin, Allows]
    · unfold labelJoin Allows
      by_cases hab : a = ℓ
      · simp [hab]
      · simp [hab]

theorem foldl_congr_mem {α β : Type} {f g : β → α → β} :
    ∀ (l : List α) (init : β), (∀ v x, x ∈ l → f v x = g v x) → l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | x :: xs, init, h => by
    simp only [List.foldl_cons]
    rw [h init x List.mem_cons_self]
    exact foldl_congr_mem xs _ fun v y hy => h v y (List.mem_cons_of_mem _ hy)

theorem allows_foldl {α : Type} (g : α → Option (Option Nat)) {ℓ : Nat} :
    ∀ (l : List α) (init : Option (Option Nat)),
      (Allows init ℓ ∨ ∃ a ∈ l, Allows (g a) ℓ) →
        Allows (l.foldl (fun v a => labelJoin v (g a)) init) ℓ := by
  intro l
  induction l with
  | nil =>
    intro init h
    rcases h with h | ⟨a, ha, _⟩
    · exact h
    · cases ha
  | cons x xs ih =>
    intro init h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | ⟨a, ha, hga⟩
    · exact Or.inl (allows_join_left h _)
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl (allows_join_right hga _)
      · exact Or.inr ⟨a, ha, hga⟩

/-- The row of `reachLabels` at `t`, reading `acc` for the children. -/
def labelRow (dag : Dag) (opq : Nat → Bool) (lab : Nat → Option Nat)
    (acc : Array (Option (Option Nat))) (t : Nat) : Option (Option Nat) :=
  (dag.node t).children.foldl (fun v c =>
    labelJoin v (if opq c then (lab c).map some else acc[c]!)) ((lab t).map some)

theorem labelRow_congr {dag : Dag} (hwf : DagWF dag) {opq : Nat → Bool} {lab : Nat → Option Nat}
    {a b : Array (Option (Option Nat))} {t : Nat} (ht : t < dag.size)
    (h : ∀ c, c < t → a[c]! = b[c]!) : labelRow dag opq lab a t = labelRow dag opq lab b t := by
  unfold labelRow
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  apply foldl_congr_mem
  intro v c hc
  have := hwf.child_lt ht (Array.mem_toList_iff.mp hc)
  rw [h c this]

theorem reachLabels_spec {dag : Dag} (hwf : DagWF dag) (opq : Nat → Bool)
    (lab : Nat → Option Nat) {t : Nat} (ht : t < dag.size) :
    (reachLabels dag opq lab)[t]! = labelRow dag opq lab (reachLabels dag opq lab) t := by
  have hinv : ∀ m, m ≤ dag.size →
      ((List.range m).foldl (fun acc t => acc.set! t (labelRow dag opq lab acc t))
          (Array.replicate dag.size none)).size = dag.size ∧
      ∀ t, t < m →
        ((List.range m).foldl (fun acc t => acc.set! t (labelRow dag opq lab acc t))
            (Array.replicate dag.size none))[t]! =
          labelRow dag opq lab ((List.range m).foldl
            (fun acc t => acc.set! t (labelRow dag opq lab acc t))
            (Array.replicate dag.size none)) t := by
    intro m
    induction m with
    | zero => intro _; exact ⟨by simp, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨hs, hrows⟩ := ih (by omega)
      rw [foldl_range_succ]
      generalize (List.range m).foldl (fun acc t => acc.set! t (labelRow dag opq lab acc t))
        (Array.replicate dag.size none) = acc at hs hrows
      have keep : ∀ c, c < m → (acc.set! m (labelRow dag opq lab acc m))[c]! = acc[c]! :=
        fun c hc => setBang_getElem!_ne _ _ (by omega)
      refine ⟨by simp [hs], fun t ht => ?_⟩
      by_cases htm : t = m
      · subst htm
        rw [setBang_getElem!_self _ _ (by omega)]
        exact labelRow_congr hwf (by omega) fun c hc => (keep c hc).symm
      · rw [keep t (by omega), hrows t (by omega)]
        exact labelRow_congr hwf (by omega) fun c hc => (keep c (by omega)).symm
  unfold reachLabels
  rw [foldRange_zero]
  exact (hinv dag.size (Nat.le_refl _)).2 t ht

/-- Paths only descend. -/
theorem NReach.le_of_wf {dag : Dag} (hwf : DagWF dag) {O : Nat → Bool} {y v : Nat}
    (h : NReach (Prep.ofDag dag) O y v) (hy : y < dag.size) : v ≤ y := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ _ he ih =>
    obtain ⟨k, hk, rfl⟩ := he
    simp only [ofDag_dag] at hk ⊢
    have := hwf.childAt_lt (by omega) hk
    omega

/-- A path is empty or starts with an edge into an opaque endpoint or into a
non-opaque term it continues from. -/
theorem NReach.head {p : Prep} {O : Nat → Bool} {y v : Nat} (h : NReach p O y v) :
    v = y ∨ ∃ k, k < (p.dag.node y).head.arity ∧
      ((O ((p.dag.node y).child k) = true ∧ v = (p.dag.node y).child k) ∨
        (O ((p.dag.node y).child k) = false ∧ NReach p O ((p.dag.node y).child k) v)) := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail u v hu hun he ih =>
    obtain ⟨k', hk', hv⟩ := he
    have direct : u = y →
        ∃ k, k < (p.dag.node y).head.arity ∧
          ((O ((p.dag.node y).child k) = true ∧ v = (p.dag.node y).child k) ∨
            (O ((p.dag.node y).child k) = false ∧ NReach p O ((p.dag.node y).child k) v)) := by
      intro huy
      subst huy
      refine ⟨k', hk', ?_⟩
      cases hOv : O ((p.dag.node u).child k')
      · exact Or.inr ⟨rfl, by rw [hv]; exact .refl⟩
      · exact Or.inl ⟨rfl, hv.symm⟩
    right
    rcases hun with huy | hOu
    · exact direct huy
    · rcases ih with rfl | ⟨k, hk, (⟨hO, rfl⟩ | ⟨hO, hc⟩)⟩
      · exact direct rfl
      · rw [hO] at hOu; cases hOu
      · exact ⟨k, hk, Or.inr ⟨hO, .tail hc (Or.inr hOu) ⟨k', hk', hv⟩⟩⟩

/-- **The reach summaries allow every reachable label.** -/
theorem reachLabels_allows {dag : Dag} (hwf : DagWF dag) (opq : Nat → Bool)
    (lab : Nat → Option Nat) :
    ∀ y, y < dag.size → ∀ v, NReach (Prep.ofDag dag) opq y v → ∀ ℓ, lab v = some ℓ →
      Allows (reachLabels dag opq lab)[y]! ℓ := by
  intro y
  induction y using Nat.strongRecOn with
  | _ y ih =>
    intro hy v hv ℓ hℓ
    rw [reachLabels_spec hwf opq lab hy]
    unfold labelRow
    rw [← Array.foldl_toList]
    apply allows_foldl
    rcases hv.head with rfl | ⟨k, hk, (⟨hO, rfl⟩ | ⟨hO, hc⟩)⟩
    · left; rw [hℓ]; exact Or.inr rfl
    · right
      have har := hwf.arity y hy
      rw [← dag_node_eq hy] at har
      simp only [ofDag_dag] at hk hO hℓ ⊢
      refine ⟨(dag.node y).child k, ?_, ?_⟩
      · rw [child_eq_getElem _ k (by omega)]
        exact Array.mem_toList_iff.mpr (Array.getElem_mem _)
      · rw [if_pos hO, hℓ]; exact Or.inr rfl
    · right
      have har := hwf.arity y hy
      rw [← dag_node_eq hy] at har
      simp only [ofDag_dag] at hk hO hc ⊢
      have hlt := hwf.childAt_lt hy hk
      refine ⟨(dag.node y).child k, ?_, ?_⟩
      · rw [child_eq_getElem _ k (by omega)]
        exact Array.mem_toList_iff.mpr (Array.getElem_mem _)
      · rw [if_neg (by simp [hO])]
        exact ih _ hlt (by omega) v hc ℓ hℓ

/-- **Checked separation.** If the check passes, every listed term carries a
label and reaches (along non-opaque paths) only terms with that label. -/
theorem labelsSeparated_spec {dag : Dag} (hwf : DagWF dag) {opq : Nat → Bool}
    {lab : Nat → Option Nat} {terms : Array Nat} (hchk : labelsSeparated dag opq lab terms = true)
    {y : Nat} (hy : y ∈ terms) (hyn : y < dag.size) :
    ∃ ℓ, lab y = some ℓ ∧ ∀ v, NReach (Prep.ofDag dag) opq y v → ∀ ℓ', lab v = some ℓ' → ℓ' = ℓ := by
  unfold labelsSeparated at hchk
  rw [Array.all_eq_true'] at hchk
  have h := hchk y hy
  cases hl : lab y with
  | none => rw [hl] at h; cases h
  | some ℓ =>
    rw [hl] at h
    simp only [beq_iff_eq] at h
    refine ⟨ℓ, rfl, fun v hv ℓ' hℓ' => ?_⟩
    have := reachLabels_allows hwf opq lab y hyn v hv ℓ' hℓ'
    rw [h] at this
    rcases this with h1 | h1
    · cases h1
    · simp only [Option.some.injEq] at h1; exact h1.symm

/-! ## The component check -/

theorem uclass_eq_of_beq {a b : UClass} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

theorem uclass_beq_self (a : UClass) : (a == a) = true := by
  cases a <;> rfl

theorem arr_getElem!_eq {α : Type} [Inhabited α] (a : Array α) {i : Nat} (h : i < a.size) :
    a[i]! = a[i] := by
  simp [getElem!_def, Array.getElem?_eq_getElem h]

/-- What a passing `componentsChecked` guarantees: the listed components are
duplicate-free sets of uncertain terms labeled by their index, every
uncertain term is listed in the component of its label, and uncertain terms
joined by a path whose intermediate terms are not certain-stored share a
label. -/
theorem componentsChecked_spec {dag : Dag} (hwf : DagWF dag) {cls : Array UClass}
    {opaq : Array Bool} {comps : Array (Array Nat)} {label : Array (Option Nat)}
    (hchk : componentsChecked dag cls opaq comps label = true) :
    (∀ i, i < comps.size → ∀ t ∈ comps[i]!.toList,
      t < dag.size ∧ cls[t]! = .uncertain ∧ label[t]! = some i) ∧
    (∀ i, i < comps.size → comps[i]!.toList.Nodup) ∧
    (∀ t, t < dag.size → cls[t]! = .uncertain →
      ∃ i, i < comps.size ∧ label[t]! = some i ∧ t ∈ comps[i]!.toList) ∧
    (∀ a b, a < dag.size → cls[a]! = .uncertain → cls[b]! = .uncertain →
      NReach (Prep.ofDag dag) (opaq[·]!) a b → label[a]! = label[b]!) := by
  unfold componentsChecked at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨h1, h2⟩, h3⟩ := hchk
  rw [Array.all_eq_true'] at h1 h2
  -- per-component facts
  have hcomp : ∀ i, i < comps.size → ∀ j, j < comps[i]!.size →
      comps[i]![j]! < dag.size ∧ cls[comps[i]![j]!]! = .uncertain ∧
        label[comps[i]![j]!]! = some i ∧
        (j + 1 < comps[i]!.size → comps[i]![j]! < comps[i]![j + 1]!) := by
    intro i hi j hj
    have := h1 i (Array.mem_range.mpr hi)
    rw [List.all_eq_true] at this
    have := this j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := this
    exact ⟨ha, uclass_eq_of_beq hb, hc, hd⟩
  have hmem : ∀ i, i < comps.size → ∀ t ∈ comps[i]!.toList,
      ∃ j, j < comps[i]!.size ∧ comps[i]![j]! = t := by
    intro i _ t ht
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
    simp only [Array.length_toList] at hj
    exact ⟨j, hj, by rw [arr_getElem!_eq _ hj]; rfl⟩
  have hcover : ∀ t, t < dag.size → cls[t]! = .uncertain →
      ∃ i, i < comps.size ∧ label[t]! = some i ∧ t ∈ comps[i]!.toList := by
    intro t ht hu
    have := h2 t (Array.mem_range.mpr ht)
    simp only [Bool.or_eq_true] at this
    rcases this with h | h
    · rw [hu] at h; exact absurd h (by decide)
    · cases hl : label[t]! with
      | none => rw [hl] at h; cases h
      | some i =>
        rw [hl] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨i, h.1, rfl, Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp h.2)⟩
  refine ⟨fun i hi t ht => ?_, fun i hi => ?_, fun t ht hu => ?_, fun a b ha hua hub hab => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := hmem i hi t ht
    exact ⟨(hcomp i hi j hj).1, (hcomp i hi j hj).2.1, (hcomp i hi j hj).2.2.1⟩
  · -- strictly increasing, hence duplicate-free
    have hlt : ∀ a b, a < b → b < comps[i]!.size → comps[i]![a]! < comps[i]![b]! := by
      intro a b hab hb
      induction b with
      | zero => omega
      | succ b ihb =>
        have hstep := (hcomp i hi b (by omega)).2.2.2 hb
        by_cases hab' : a = b
        · subst hab'; exact hstep
        · exact Nat.lt_trans (ihb (by omega) (by omega)) hstep
    apply List.Pairwise.imp (R := (· < ·)) (fun h => Nat.ne_of_lt h)
    rw [List.pairwise_iff_getElem]
    intro a b ha hb hab
    simp only [Array.length_toList] at ha hb
    have := hlt a b hab hb
    rw [arr_getElem!_eq _ ha, arr_getElem!_eq _ hb] at this
    simpa using this
  · exact hcover t ht hu
  · have hmemu : a ∈ (Array.range dag.size).filter (cls[·]! == .uncertain) := by
      rw [Array.mem_filter]
      exact ⟨Array.mem_range.mpr ha, by rw [hua]; exact uclass_beq_self _⟩
    obtain ⟨ℓ, hℓ, hreach⟩ := labelsSeparated_spec hwf h3 hmemu ha
    have hbn : b < dag.size := by
      have := NReach.le_of_wf hwf hab ha
      omega
    obtain ⟨i, _, hlb, _⟩ := hcover b hbn hub
    have := hreach b hab i hlb
    rw [hℓ, hlb, this]

end Ix.Compile.Verify.UniformModel
