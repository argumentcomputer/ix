/-
  The area search computes the specification's search, part 3: the truncated
  side. The truncated tables of a stage (`TBase.ofPrep`) satisfy the truncated
  row recurrence with nothing available, and the area evaluation (`areaFold`
  with the base rows outside the area) satisfies it with the available members
  at every term (`area_rows`).
-/
module

public import Ix.Sharing.Exact.AreaClosureRows
import all Ix.Sharing.Exact.Basic
import all Ix.Sharing.Exact.Dag
import all Ix.Sharing.Exact.Dictionary
import all Ix.Sharing.Exact.UniformSearch
import all Ix.Sharing.Exact.UniformSearchLocal
import all Ix.Sharing.Exact.AreaSearch
import all Ix.Sharing.Exact.AreaRowsRel
import all Ix.Sharing.Exact.AreaClosureRows

public section

namespace Ix.Sharing.Exact.AreaProof

open Ix.Sharing.Exact

/-! ## Congruence of a truncated row -/

theorem tScan_congr (tLn : Array Nat) (w : Nat) (tS1 tS2 tB1 tB2 : Nat → Nat) (l s : Nat)
    (SB : Nat → Prop) (hag : ∀ u, SB u → tS1 u = tS2 u ∧ tB1 u = tB2 u)
    (hcl : ∀ u, SB u → tB1 u ≠ 0 → SB (tB1 u - 1)) :
    ∀ fuel cur best, (cur ≠ 0 → SB (cur - 1)) →
      tScan tLn w tS1 tB1 l s fuel cur best = tScan tLn w tS2 tB2 l s fuel cur best
  | 0, _, _, _ => rfl
  | fuel + 1, cur, best, hcur => by
    simp only [tScan]
    by_cases hc : cur = 0
    · simp [hc]
    · simp only [hc, ite_false]
      obtain ⟨a, b⟩ := hag _ (hcur hc)
      rw [← a, ← b]
      exact tScan_congr tLn w tS1 tS2 tB1 tB2 l s SB hag hcl fuel _ _ (hcl _ (hcur hc))

theorem TRow.of_parts {p : Prep} {opaq : Array Bool} {tLn tTl : Array Nat} {w : Nat}
    {X : Nat → Bool} {tC tI tS tB : Nat → Nat} {t : Nat}
    (h1 : tC t = tCost opaq w X t (tI t)) (h2 : tI t = tInl p opaq tLn tTl w X tC tS tB t)
    (h3 : p.family[t]! ≠ .none → tS t = tSide p opaq tC tS t ∧ tB t = tBl p opaq X tB t)
    (h4 : p.family[t]! = .none → tS t = 0 ∧ tB t = 0) :
    TRow p opaq tLn tTl w X tC tI tS tB t := by
  unfold TRow
  rw [tRow_eq, ← h2, ← h1]
  by_cases hf : p.family[t]! = .none
  · obtain ⟨a, b⟩ := h4 hf
    simp only [hf, ite_true, a, b]
  · obtain ⟨a, b⟩ := h3 hf
    simp only [hf, ite_false, ← a, ← b]

section TCongr

variable {p : Prep} (h : DagOK p.dag)
  (hfam : ∀ t, t < p.dag.size → p.family[t]! = (p.dag.node t).head.family)
  {opaq : Array Bool} {tLn tTl : Array Nat} {w : Nat}
  {X1 X2 : Nat → Bool} {tC1 tC2 tS1 tS2 tB1 tB2 : Nat → Nat}
  {t : Nat} (ht : t < p.dag.size) (SC SB : Nat → Prop)
  (hC : ∀ u, SC u → tC1 u = tC2 u)
  (hSB : ∀ u, SB u → tS1 u = tS2 u ∧ tB1 u = tB2 u ∧ X1 u = X2 u)
  (hch : ∀ c ∈ (p.dag.node t).children, SC c)
  (hnx : p.family[t]! ≠ .none → p.family[nx p t]! = p.family[t]! → opaq[nx p t]! = false →
    SB (nx p t))

include h hfam ht hC hSB hch hnx in
theorem tSide_congr (hf : p.family[t]! ≠ .none) :
    tSide p opaq tC1 tS1 t = tSide p opaq tC2 tS2 t := by
  unfold tSide
  rw [hC _ (hch _ (side_mem h hfam ht hf))]
  split
  · rename_i hc
    rw [(hSB _ (hnx hf hc.1 hc.2)).1]
  · rfl

set_option linter.unusedSectionVars false in
include h hfam ht hC hSB hch hnx in
theorem tBl_congr (hf : p.family[t]! ≠ .none) : tBl p opaq X1 tB1 t = tBl p opaq X2 tB2 t := by
  unfold tBl
  split
  · rename_i hc
    obtain ⟨_, b, c⟩ := hSB _ (hnx hf hc.1 hc.2)
    rw [b, c]
  · rfl

include h hfam ht hC hSB hch hnx in
/-- The inline cost of a truncated row depends only on the costs at a set `SC`
holding its children and its truncated tail, and on the spine readers at a set
`SB` holding its continuing spine successor and closed under the first
readers' links. -/
theorem tInl_congr (htl : p.family[t]! ≠ .none → SC tTl[t]!)
    (hcl : ∀ u, SB u → tB1 u ≠ 0 → SB (tB1 u - 1)) :
    tInl p opaq tLn tTl w X1 tC1 tS1 tB1 t = tInl p opaq tLn tTl w X2 tC2 tS2 tB2 t := by
  unfold tInl
  by_cases hf : p.family[t]! = .none
  · rw [ite_eq_left hf, ite_eq_left hf, ← Array.foldl_toList, ← Array.foldl_toList]
    have hc : ∀ c ∈ (p.dag.node t).children.toList, tC1 c = tC2 c :=
      fun c hc => hC c (hch c (Array.mem_toList_iff.mp hc))
    generalize (p.dag.node t).children.toList = l at hc
    generalize (p.dag.node t).head.ownBytes = acc
    induction l generalizing acc with
    | nil => rfl
    | cons c l ihl =>
      simp only [List.foldl_cons]
      rw [hc c List.mem_cons_self]
      exact ihl (fun c hc' => hc c (List.mem_cons_of_mem _ hc')) _
  · rw [ite_eq_right hf, ite_eq_right hf, tSide_congr h hfam ht SC SB hC hSB hch hnx hf,
      tBl_congr h hfam ht SC SB hC hSB hch hnx hf, hC _ (htl hf)]
    apply tScan_congr tLn w tS1 tS2 tB1 tB2 _ _ SB (fun u hu => ⟨(hSB u hu).1, (hSB u hu).2.1⟩)
      hcl
    intro hb
    rw [← tBl_congr h hfam ht SC SB hC hSB hch hnx hf] at hb ⊢
    unfold tBl at hb ⊢
    split at hb
    · rename_i hc
      rw [ite_eq_left hc]
      split at hb
      · rename_i hx
        rw [ite_eq_left hx, Nat.add_sub_cancel]
        exact hnx hf hc.1 hc.2
      · rename_i hx
        rw [ite_eq_right hx]
        exact hcl _ (hnx hf hc.1 hc.2) hb
    · exact absurd rfl hb

end TCongr

/-! ## Links of truncated rows -/

section TLinks

variable {p : Prep} (h : DagOK p.dag)
  (hfam : ∀ t, t < p.dag.size → p.family[t]! = (p.dag.node t).head.family)
  {opaq : Array Bool} {tLn tTl : Array Nat} {w : Nat} {X : Nat → Bool}
  {tC tI tS tB : Nat → Nat}

include h hfam in
/-- A truncated link leads below, given the rows at and below the term. -/
theorem tLinkLt : ∀ x, x < p.dag.size → (∀ v, v ≤ x → TRow p opaq tLn tTl w X tC tI tS tB v) →
    tB x ≠ 0 → tB x - 1 < x := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro hx hr hb
    by_cases hf : p.family[x]! = .none
    · have := (hr x (Nat.le_refl _))
      unfold TRow at this
      rw [tRow_eq] at this
      simp only [hf, ite_true, Prod.mk.injEq] at this
      exact absurd this.2.2.2 hb
    · have hn := nx_lt h hfam hx hf
      have hbx := ((hr x (Nat.le_refl _)).parts.2.2 hf).2
      rw [hbx] at hb ⊢
      unfold tBl at hb ⊢
      split at hb
      · rename_i hc
        rw [ite_eq_left hc]
        split at hb
        · rename_i hX; rw [ite_eq_left hX]; omega
        · rename_i hX
          rw [ite_eq_right hX]
          have := ih _ hn (by omega) (fun v hv => hr v (by omega)) hb
          omega
      · exact absurd rfl hb

end TLinks

/-- A whole truncated row depends only on the readers at a set `S` of terms
holding its children, its truncated tail and its continuing successor, closed
under the first readers' links, and on the availability of `t`. -/
theorem tRow_congrS {p : Prep} (h : DagOK p.dag)
    (hfam : ∀ t, t < p.dag.size → p.family[t]! = (p.dag.node t).head.family)
    {opaq : Array Bool} {tLn tTl : Array Nat} {w : Nat}
    {X1 X2 : Nat → Bool} {tC1 tC2 tS1 tS2 tB1 tB2 : Nat → Nat}
    {t : Nat} (ht : t < p.dag.size) (SC SB : Nat → Prop)
    (hC : ∀ u, SC u → tC1 u = tC2 u)
    (hSB : ∀ u, SB u → tS1 u = tS2 u ∧ tB1 u = tB2 u ∧ X1 u = X2 u)
    (hch : ∀ c ∈ (p.dag.node t).children, SC c)
    (hnx : p.family[t]! ≠ .none → p.family[nx p t]! = p.family[t]! → opaq[nx p t]! = false →
      SB (nx p t))
    (htl : p.family[t]! ≠ .none → SC tTl[t]!)
    (hcl : ∀ u, SB u → tB1 u ≠ 0 → SB (tB1 u - 1)) (hX : X1 t = X2 t) :
    tRow p opaq tLn tTl w X1 tC1 tS1 tB1 t = tRow p opaq tLn tTl w X2 tC2 tS2 tB2 t := by
  rw [tRow_eq, tRow_eq, tInl_congr h hfam ht SC SB hC hSB hch hnx htl hcl]
  unfold tCost
  rw [hX]
  by_cases hf : p.family[t]! = .none
  · simp only [hf, ite_true]
  · simp only [hf, ite_false, tSide_congr h hfam ht SC SB hC hSB hch hnx hf,
      tBl_congr h hfam ht SC SB hC hSB hch hnx hf]

theorem push_read {α : Type} [Inhabited α] (L : Array α) (x : α) (u : Nat) :
    (L.push x)[u]! = if u < L.size then L[u]! else if u = L.size then x else default := by
  by_cases h1 : u < L.size
  · rw [ite_eq_left h1, getElem!_pos (L.push x) u (by simp; omega), getElem!_pos L u h1]
    simp [Array.getElem_push_lt h1]
  · rw [ite_eq_right h1]
    by_cases h2 : u = L.size
    · subst h2; rw [ite_eq_left rfl, getElem!_pos (L.push x) L.size (by simp)]; simp
    · rw [ite_eq_right h2, getElem!_neg (L.push x) u (by simp; omega)]

/-! ## The truncated tables -/

section TBase

variable {p : Prep} (h : DagOK p.dag)
  (hfam : ∀ t, t < p.dag.size → p.family[t]! = (p.dag.node t).head.family)

include h hfam in
/-- **The truncated tables** satisfy the truncated row recurrence with
nothing available at every term. -/
theorem tbase_rows (opaq : Array Bool) (w : Nat) :
    let tb := TBase.ofPrep p w opaq
    tb.tLen = (tSpineTables p.dag p.family opaq).1 ∧
      tb.tTail = (tSpineTables p.dag p.family opaq).2 ∧
      ∀ t, t < p.dag.size → TRow p opaq tb.tLen tb.tTail w (fun _ => false)
        (tb.cost[·]!) (tb.inl[·]!) (tb.sides[·]!) (tb.below[·]!) t := by
  intro tb
  unfold tb TBase.ofPrep
  have hT := tSpineTables_rows h hfam opaq
  generalize tSpineTables p.dag p.family opaq = tt at hT
  obtain ⟨tLn, tTl⟩ := tt
  simp only at hT ⊢
  have httl : ∀ t, t < p.dag.size → p.family[t]! ≠ .none → tTl[t]! < t := by
    intro t
    induction t using Nat.strongRecOn with
    | _ t ih =>
      intro ht hf
      have hn := nx_lt h hfam ht hf
      obtain ⟨_, t2⟩ := spineRow_trunc (hT t ht) hf
      split at t2
      · rename_i hc
        have hfn : p.family[nx p t]! ≠ .none := by rw [hc.1]; exact hf
        have := ih _ hn (by omega) hfn
        omega
      · omega
  -- the fold of pushed rows
  have key : ∀ m, m ≤ p.dag.size →
      let st := foldRange (tBaseStep p opaq tLn tTl w) 0 m
        (Array.mkEmpty p.dag.size, Array.mkEmpty p.dag.size, Array.mkEmpty p.dag.size,
          Array.mkEmpty p.dag.size)
      st.1.size = m ∧ st.2.1.size = m ∧ st.2.2.1.size = m ∧ st.2.2.2.size = m ∧
        ∀ t, t < m → TRow p opaq tLn tTl w (fun _ => false) (st.1[·]!) (st.2.1[·]!)
          (st.2.2.1[·]!) (st.2.2.2[·]!) t := by
    intro m
    induction m with
    | zero => intro _; simp [Ix.Sharing.Exact.LocalSearch.foldRange_zero]
    | succ m ih =>
      intro hm
      obtain ⟨s1, s2, s3, s4, hr⟩ := ih (by omega)
      simp only at s1 s2 s3 s4 hr ⊢
      rw [Ix.Sharing.Exact.LocalSearch.foldRange_succ, Nat.zero_add]
      generalize foldRange (tBaseStep p opaq tLn tTl w) 0 m
        (Array.mkEmpty p.dag.size, Array.mkEmpty p.dag.size, Array.mkEmpty p.dag.size,
          Array.mkEmpty p.dag.size) = st at s1 s2 s3 s4 hr
      obtain ⟨C, I, S, B⟩ := st
      simp only at s1 s2 s3 s4 hr
      have hstep : tBaseStep p opaq tLn tTl w (C, I, S, B) m =
          (C.push (tRow p opaq tLn tTl w (fun _ => false) (C[·]!) (S[·]!) (B[·]!) m).1,
            I.push (tRow p opaq tLn tTl w (fun _ => false) (C[·]!) (S[·]!) (B[·]!) m).2.1,
            S.push (tRow p opaq tLn tTl w (fun _ => false) (C[·]!) (S[·]!) (B[·]!) m).2.2.1,
            B.push (tRow p opaq tLn tTl w (fun _ => false) (C[·]!) (S[·]!) (B[·]!) m).2.2.2) := by
        unfold tBaseStep
        rfl
      rw [hstep]
      generalize hrow : tRow p opaq tLn tTl w (fun _ => false) (C[·]!) (S[·]!) (B[·]!) m = row
      obtain ⟨c, i, s, b⟩ := row
      simp only
      -- the new readers agree with the old ones off `m`
      have hagC : ∀ u, u < m → (C.push c)[u]! = C[u]! := fun u hu => by
        rw [push_read, ite_eq_left (by omega)]
      have hagI : ∀ u, u < m → (I.push i)[u]! = I[u]! := fun u hu => by
        rw [push_read, ite_eq_left (by omega)]
      have hagS : ∀ u, u < m → (S.push s)[u]! = S[u]! := fun u hu => by
        rw [push_read, ite_eq_left (by omega)]
      have hagB : ∀ u, u < m → (B.push b)[u]! = B[u]! := fun u hu => by
        rw [push_read, ite_eq_left (by omega)]
      -- the row of `t` with the old readers equals the row with the new ones
      have hcongr : ∀ t, t ≤ m →
          tRow p opaq tLn tTl w (fun _ => false) (C[·]!) (S[·]!) (B[·]!) t =
            tRow p opaq tLn tTl w (fun _ => false) ((C.push c)[·]!) ((S.push s)[·]!)
              ((B.push b)[·]!) t := by
        intro t htm
        have htn : t < p.dag.size := by omega
        apply tRow_congrS h hfam htn (fun u => u < t) (fun u => u < t)
        · intro u hu; exact (hagC u (by omega)).symm
        · intro u hu; exact ⟨(hagS u (by omega)).symm, (hagB u (by omega)).symm, rfl⟩
        · intro c hc; exact h.child_lt htn hc
        · intro hf hs ho; exact nx_lt h hfam htn hf
        · intro hf
          exact httl t htn hf
        · intro u hu hb
          have := tLinkLt h hfam u (by omega) (fun v hv => hr v (by omega)) hb
          omega
        · rfl
      refine ⟨by simp [s1], by simp [s2], by simp [s3], by simp [s4], fun t ht => ?_⟩
      by_cases htm : t = m
      · subst htm
        unfold TRow
        rw [← hcongr t (Nat.le_refl _), hrow]
        simp only [push_read, s1, s2, s3, s4, Nat.lt_irrefl, ite_false, ite_true]
      · have hrt := hr t (by omega)
        unfold TRow at hrt ⊢
        rw [← hcongr t (by omega)]
        show ((C.push c)[t]!, (I.push i)[t]!, (S.push s)[t]!, (B.push b)[t]!) = _
        rw [hagC t (by omega), hagI t (by omega), hagS t (by omega), hagB t (by omega)]
        exact hrt
  obtain ⟨_, _, _, _, hr⟩ := key p.dag.size (Nat.le_refl _)
  refine ⟨?_, ?_, hr⟩ <;> first | rfl | trivial

end TBase

/-! ## The area evaluation -/

section Area

variable {p : Prep} (h : DagOK p.dag)
  (hfam : ∀ t, t < p.dag.size → p.family[t]! = (p.dag.node t).head.family)
  {opaq : Array Bool} {tLn tTl : Array Nat}
  (hT : ∀ t, t < p.dag.size → SpineRow p.dag p.family (fun u => !opaq[u]!) tLn tTl t)

include h hfam hT in
theorem ttail_lt : ∀ t, t < p.dag.size → p.family[t]! ≠ .none → tTl[t]! < t := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht hf
    have hn := nx_lt h hfam ht hf
    obtain ⟨_, t2⟩ := spineRow_trunc (hT t ht) hf
    split at t2
    · rename_i hc
      have hfn : p.family[nx p t]! ≠ .none := by rw [hc.1]; exact hf
      have := ih _ hn (by omega) hfn
      omega
    · omega

include h hfam hT in
/-- The truncated tail of a telescope is a child of the telescope or of a term
on its truncated spine. -/
theorem ttail_parent : ∀ t, t < p.dag.size → p.family[t]! ≠ .none →
    tTl[t]! ∈ (p.dag.node t).children ∨
      ∃ y, TSp p opaq t y ∧ tTl[t]! ∈ (p.dag.node y).children := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht hf
    have hn := nx_lt h hfam ht hf
    obtain ⟨_, t2⟩ := spineRow_trunc (hT t ht) hf
    split at t2
    · rename_i hc
      have hfn : p.family[nx p t]! ≠ .none := by rw [hc.1]; exact hf
      rw [t2]
      rcases ih _ hn (by omega) hfn with h1 | ⟨y, hy, h2⟩
      · exact Or.inr ⟨nx p t, .one hf hc.1 hc.2, h1⟩
      · exact Or.inr ⟨y, .step hf hc.1 hc.2 hy, h2⟩
    · rw [t2]
      exact Or.inl (nx_mem h hfam ht hf)

/-- `u` is a term of the area. -/
def InA (area : Array Nat) (u : Nat) : Prop := ∃ j, j < area.size ∧ area[j]! = u

theorem rdA_in {area posA : Array Nat}
    (hpos : Ix.Sharing.Exact.LocalSearch.PosFn area.size (area[·]!) (posOf posA))
    (L base : Array Nat) {u j : Nat} (hj : j < area.size) (hu : area[j]! = u) :
    rdA posA L base u = if j < L.size then L[j]! else base[u]! := by
  have hp := (hpos u j).mpr ⟨hj, hu⟩
  rw [Ix.Sharing.Exact.LocalSearch.posOf_some] at hp
  unfold rdA
  rw [hp]
  simp

theorem rdA_out {area posA : Array Nat}
    (hpos : Ix.Sharing.Exact.LocalSearch.PosFn area.size (area[·]!) (posOf posA))
    (L base : Array Nat) {u : Nat} (hu : ¬ InA area u) : rdA posA L base u = base[u]! := by
  unfold rdA
  have h0 : posA[u]! = 0 := by
    cases hz : posA[u]! with
    | zero => rfl
    | succ k =>
      have := (hpos u k).mp ((Ix.Sharing.Exact.LocalSearch.posOf_some posA u k).mpr hz)
      exact absurd ⟨k, this.1, this.2⟩ hu
  rw [h0]
  simp

theorem avA_out {area posA : Array Nat}
    (hpos : Ix.Sharing.Exact.LocalSearch.PosFn area.size (area[·]!) (posOf posA))
    (fl : Array Bool) {u : Nat} (hu : ¬ InA area u) : avA posA fl u = false := by
  unfold avA
  have h0 : posA[u]! = 0 := by
    cases hz : posA[u]! with
    | zero => rfl
    | succ k =>
      have := (hpos u k).mp ((Ix.Sharing.Exact.LocalSearch.posOf_some posA u k).mpr hz)
      exact absurd ⟨k, this.1, this.2⟩ hu
  rw [h0]
  simp

theorem strictInc_lt_iff {a : Array Nat} (h : strictInc a = true) {i j : Nat} (hi : i < a.size)
    (hj : j < a.size) : a[i]! < a[j]! ↔ i < j := by
  constructor
  · intro hlt
    by_cases hij : i < j
    · exact hij
    · exfalso
      by_cases he : i = j
      · subst he; omega
      · have := Ix.Sharing.Exact.LocalSearch.strictInc_lt h j i (by omega) hi
        omega
  · intro hij
    exact Ix.Sharing.Exact.LocalSearch.strictInc_lt h i j hij hj

/-- The states of the area fold. -/
abbrev areaStep (p : Prep) (opaq : Array Bool) (tb : TBase) (w : Nat) (area posA : Array Nat)
    (fl : Array Bool) (st : Array Nat × Array Nat × Array Nat × Array Nat) (i : Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat :=
  match st with
  | (C, I, S, B) =>
    match tRow p opaq tb.tLen tb.tTail w (avA posA fl) (rdA posA C tb.cost) (rdA posA S tb.sides)
        (rdA posA B tb.below) area[i]! with
    | (c, inl, s, b) => (C.push c, I.push inl, S.push s, B.push b)

/-- The row the area fold writes at position `j`, from the state before it. -/
abbrev areaRow (p : Prep) (opaq : Array Bool) (tb : TBase) (w : Nat) (area posA : Array Nat)
    (fl : Array Bool) (st : Array Nat × Array Nat × Array Nat × Array Nat) (j : Nat) :
    Nat × Nat × Nat × Nat :=
  tRow p opaq tb.tLen tb.tTail w (avA posA fl) (rdA posA st.1 tb.cost) (rdA posA st.2.2.1 tb.sides)
    (rdA posA st.2.2.2 tb.below) area[j]!

theorem areaFold_entries (p : Prep) (opaq : Array Bool) (tb : TBase) (w : Nat)
    (area posA : Array Nat) (fl : Array Bool) :
    ∀ i, i ≤ area.size →
      let st := foldRange (areaStep p opaq tb w area posA fl) 0 i
        (Array.mkEmpty area.size, Array.mkEmpty area.size, Array.mkEmpty area.size,
          Array.mkEmpty area.size)
      st.1.size = i ∧ st.2.1.size = i ∧ st.2.2.1.size = i ∧ st.2.2.2.size = i ∧
        ∀ j, j < i → (st.1[j]!, st.2.1[j]!, st.2.2.1[j]!, st.2.2.2[j]!) =
          areaRow p opaq tb w area posA fl (foldRange (areaStep p opaq tb w area posA fl) 0 j
            (Array.mkEmpty area.size, Array.mkEmpty area.size, Array.mkEmpty area.size,
              Array.mkEmpty area.size)) j := by
  intro i
  induction i with
  | zero => intro _; simp [Ix.Sharing.Exact.LocalSearch.foldRange_zero]
  | succ i ih =>
    intro hi
    obtain ⟨s1, s2, s3, s4, he⟩ := ih (by omega)
    simp only at s1 s2 s3 s4 he ⊢
    rw [Ix.Sharing.Exact.LocalSearch.foldRange_succ, Nat.zero_add]
    generalize hst : foldRange (areaStep p opaq tb w area posA fl) 0 i
      (Array.mkEmpty area.size, Array.mkEmpty area.size, Array.mkEmpty area.size,
        Array.mkEmpty area.size) = st at s1 s2 s3 s4 he
    obtain ⟨C, I, S, B⟩ := st
    simp only at s1 s2 s3 s4 he
    have hstep : areaStep p opaq tb w area posA fl (C, I, S, B) i =
        (C.push (areaRow p opaq tb w area posA fl (C, I, S, B) i).1,
          I.push (areaRow p opaq tb w area posA fl (C, I, S, B) i).2.1,
          S.push (areaRow p opaq tb w area posA fl (C, I, S, B) i).2.2.1,
          B.push (areaRow p opaq tb w area posA fl (C, I, S, B) i).2.2.2) := by
      unfold areaStep areaRow
      rfl
    rw [hstep]
    refine ⟨by simp [s1], by simp [s2], by simp [s3], by simp [s4], fun j hj => ?_⟩
    simp only [push_read, s1, s2, s3, s4]
    by_cases hji : j < i
    · simp only [hji, ite_true]
      exact he j hji
    · have hje : j = i := by omega
      subst hje
      simp only [Nat.lt_irrefl, ite_false, ite_true]
      rw [hst]

include h hfam in
theorem TSp.lt_fam {t u : Nat} (ht : t < p.dag.size) (hu : TSp p opaq t u) :
    u < t ∧ p.family[u]! = p.family[t]! ∧ p.family[t]! ≠ .none := by
  induction hu with
  | @one t hf hs _ => exact ⟨nx_lt h hfam ht hf, hs, hf⟩
  | @step t u hf hs _ _ ih =>
    have hn := nx_lt h hfam ht hf
    obtain ⟨a, b, _⟩ := ih (by omega)
    exact ⟨by omega, by rw [b, hs], hf⟩

include h hfam in
/-- A term with a term of the area on its truncated spine is in the area,
when the parents of the area's non-opaque terms are in the area. -/
theorem TSp_area {area : Array Nat}
    (hclose : ∀ y q, InA area y → opaq[y]! = false → q < p.dag.size →
      y ∈ (p.dag.node q).children → InA area q)
    {t u : Nat} (ht : t < p.dag.size) (hu : TSp p opaq t u) (hin : InA area u) : InA area t := by
  induction hu with
  | @one t hf _ ho => exact hclose _ t hin ho ht (nx_mem h hfam ht hf)
  | @step t u hf _ ho _ ih =>
    have hn := nx_lt h hfam ht hf
    exact hclose _ t (ih (by omega) hin) ho ht (nx_mem h hfam ht hf)

include h hfam hT in
/-- **The area evaluation** (`areaFold`, with the base rows outside the area)
satisfies the truncated row recurrence with the available members at every
term. -/
theorem area_rows {w : Nat} (tb : TBase) (hTL : tb.tLen = tLn) (hTT : tb.tTail = tTl)
    (htb : ∀ t, t < p.dag.size → TRow p opaq tLn tTl w (fun _ => false)
      (tb.cost[·]!) (tb.inl[·]!) (tb.sides[·]!) (tb.below[·]!) t)
    (area posA : Array Nat) (fl : Array Bool) (hinc : strictInc area = true)
    (hpos : Ix.Sharing.Exact.LocalSearch.PosFn area.size (area[·]!) (posOf posA))
    (hclose : ∀ y q, InA area y → opaq[y]! = false → q < p.dag.size →
      y ∈ (p.dag.node q).children → InA area q) :
    let r := areaFold p opaq tb w area posA fl
    ∀ t, t < p.dag.size → TRow p opaq tLn tTl w (avA posA fl)
      (rdA posA r.1 tb.cost) (rdA posA r.2.1 tb.inl) (rdA posA r.2.2.1 tb.sides)
      (rdA posA r.2.2.2 tb.below) t := by
  intro r
  have hr : r = foldRange (areaStep p opaq tb w area posA fl) 0 area.size
      (Array.mkEmpty area.size, Array.mkEmpty area.size, Array.mkEmpty area.size,
        Array.mkEmpty area.size) := rfl
  obtain ⟨r1, r2, r3, r4, hent⟩ := areaFold_entries p opaq tb w area posA fl area.size
    (Nat.le_refl _)
  rw [← hr] at r1 r2 r3 r4 hent
  -- the state before position `j` agrees with the final one below position `j`
  have hpre : ∀ j, j ≤ area.size → ∀ u,
      (¬ InA area u ∨ ∃ q, q < j ∧ area[q]! = u) →
      let F := foldRange (areaStep p opaq tb w area posA fl) 0 j
        (Array.mkEmpty area.size, Array.mkEmpty area.size, Array.mkEmpty area.size,
          Array.mkEmpty area.size)
      rdA posA F.1 tb.cost u = rdA posA r.1 tb.cost u ∧
        rdA posA F.2.2.1 tb.sides u = rdA posA r.2.2.1 tb.sides u ∧
        rdA posA F.2.2.2 tb.below u = rdA posA r.2.2.2 tb.below u := by
    intro j hj u hu F
    obtain ⟨f1, f2, f3, f4, fent⟩ := areaFold_entries p opaq tb w area posA fl j hj
    rcases hu with hu | ⟨q, hq, hqu⟩
    · refine ⟨?_, ?_, ?_⟩ <;> rw [rdA_out hpos _ _ hu, rdA_out hpos _ _ hu]
    · have hqa : q < area.size := by omega
      rw [rdA_in hpos _ _ hqa hqu, rdA_in hpos _ _ hqa hqu, rdA_in hpos _ _ hqa hqu,
        rdA_in hpos _ _ hqa hqu, rdA_in hpos _ _ hqa hqu, rdA_in hpos _ _ hqa hqu]
      have e := (fent q hq).trans (hent q hqa).symm
      simp only [Prod.mk.injEq] at e
      rw [ite_eq_left (by rw [f1]; exact hq), ite_eq_left (by rw [r1]; exact hqa),
        ite_eq_left (by rw [f3]; exact hq), ite_eq_left (by rw [r3]; exact hqa),
        ite_eq_left (by rw [f4]; exact hq), ite_eq_left (by rw [r4]; exact hqa)]
      exact ⟨e.1, e.2.2.1, e.2.2.2⟩
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    by_cases hin : InA area t
    · obtain ⟨j, hj, hjt⟩ := hin
      -- the final readers at `t` are the row written at position `j`
      have e := hent j hj
      have hval : (rdA posA r.1 tb.cost t, rdA posA r.2.1 tb.inl t, rdA posA r.2.2.1 tb.sides t,
          rdA posA r.2.2.2 tb.below t) = (r.1[j]!, r.2.1[j]!, r.2.2.1[j]!, r.2.2.2[j]!) := by
        rw [rdA_in hpos _ _ hj hjt, rdA_in hpos _ _ hj hjt, rdA_in hpos _ _ hj hjt,
          rdA_in hpos _ _ hj hjt]
        simp [r1, r2, r3, r4, hj]
      unfold TRow
      rw [hval, e]
      unfold areaRow
      rw [hjt, hTL, hTT]
      obtain ⟨_, _, _, _, _⟩ := areaFold_entries p opaq tb w area posA fl j (by omega)
      apply tRow_congrS h hfam ht (fun u => u < t) (fun u => u < t)
      · intro u hu
        have := hpre j (by omega) u (by
          by_cases hu' : InA area u
          · obtain ⟨q, hq, hqu⟩ := hu'
            refine Or.inr ⟨q, ?_, hqu⟩
            rw [← hjt, ← hqu] at hu
            exact (strictInc_lt_iff hinc hq hj).mp hu
          · exact Or.inl hu')
        exact this.1
      · intro u hu
        have := hpre j (by omega) u (by
          by_cases hu' : InA area u
          · obtain ⟨q, hq, hqu⟩ := hu'
            refine Or.inr ⟨q, ?_, hqu⟩
            rw [← hjt, ← hqu] at hu
            exact (strictInc_lt_iff hinc hq hj).mp hu
          · exact Or.inl hu')
        exact ⟨this.2.1, this.2.2, rfl⟩
      · intro c hc; exact h.child_lt ht hc
      · intro hf _ _; exact nx_lt h hfam ht hf
      · intro hf; exact ttail_lt h hfam hT t ht hf
      · intro u hu hb
        have hagree := hpre j (by omega) u (by
          by_cases hu' : InA area u
          · obtain ⟨q, hq, hqu⟩ := hu'
            refine Or.inr ⟨q, ?_, hqu⟩
            rw [← hjt, ← hqu] at hu
            exact (strictInc_lt_iff hinc hq hj).mp hu
          · exact Or.inl hu')
        rw [hagree.2.2] at hb ⊢
        have := tLinkLt h hfam u (by omega) (fun v hv => ih v (by omega) (by omega)) hb
        omega
      · rfl
    · -- outside the area: the base row, with every read the same
      have hval : (rdA posA r.1 tb.cost t, rdA posA r.2.1 tb.inl t, rdA posA r.2.2.1 tb.sides t,
          rdA posA r.2.2.2 tb.below t) = (tb.cost[t]!, tb.inl[t]!, tb.sides[t]!, tb.below[t]!) := by
        rw [rdA_out hpos _ _ hin, rdA_out hpos _ _ hin, rdA_out hpos _ _ hin, rdA_out hpos _ _ hin]
      unfold TRow
      rw [hval, htb t ht]
      apply tRow_congrS h hfam ht
        (fun u => u < t ∧ (¬ InA area u ∨ opaq[u]! = true)) (fun u => TSp p opaq t u)
      · intro u ⟨hu, hcase⟩
        rcases hcase with hcase | hcase
        · rw [rdA_out hpos _ _ hcase]
        · have h1 := (htb u (by omega)).parts.1
          have h2 := (ih u hu (by omega)).parts.1
          unfold tCost at h1 h2
          simp only [hcase, ite_true] at h1 h2
          rw [h1, h2]
      · intro u hu
        have hnot : ¬ InA area u := fun hin' => hin (TSp_area h hfam hclose ht hu hin')
        rw [rdA_out hpos _ _ hnot, rdA_out hpos _ _ hnot, avA_out hpos _ hnot]
        exact ⟨rfl, rfl, rfl⟩
      · intro c hc
        refine ⟨h.child_lt ht hc, ?_⟩
        by_cases ho : opaq[c]! = true
        · exact Or.inr ho
        · exact Or.inl (fun hin' => hin (hclose c t hin' (by simpa using ho) ht hc))
      · intro hf hs ho; exact .one hf hs ho
      · intro hf
        refine ⟨ttail_lt h hfam hT t ht hf, ?_⟩
        by_cases ho : opaq[tTl[t]!]! = true
        · exact Or.inr ho
        · refine Or.inl (fun hin' => hin ?_)
          have ho' : opaq[tTl[t]!]! = false := by simpa using ho
          rcases ttail_parent h hfam hT t ht hf with hc | ⟨y, hy, hc⟩
          · exact hclose _ t hin' ho' ht hc
          · have hyt := (TSp.lt_fam h hfam ht hy).1
            exact TSp_area h hfam hclose ht hy (hclose _ y hin' ho' (by omega) hc)
      · intro u hu hb
        obtain ⟨a1, a2, a3⟩ := TSp.lt_fam h hfam ht hu
        obtain ⟨a, _⟩ := tLink h hfam htb u (by omega) (by rw [a2]; exact a3) hb
        exact hu.trans a
      · exact (avA_out hpos fl hin).symm

end Area

end Ix.Sharing.Exact.AreaProof

end
