/-
  The area search computes the specification's search, part 5: the search
  block. The bound and visible-count tables without tuples are those of
  `reboundL` and `revisibleL` field by field (`reboundA_eq`, `revisibleA_eq`);
  `sepCheckA` (reach labels over the area) equals `sepCheckL` (reach labels
  over the closure) (`sepCheckA_eq`); and the mutual search block on the area
  is the local one (`block_eq`).
-/
module

public import Ix.Sharing.Exact.AreaCostEq
import all Ix.Sharing.Exact.Basic
import all Ix.Sharing.Exact.Dag
import all Ix.Sharing.Exact.Dictionary
import all Ix.Sharing.Exact.UniformSearch
import all Ix.Sharing.Exact.UniformSearchLocal
import all Ix.Sharing.Exact.AreaSearch
import all Ix.Sharing.Exact.AreaRowsRel
import all Ix.Sharing.Exact.AreaClosureRows
import all Ix.Sharing.Exact.AreaTruncRows
import all Ix.Sharing.Exact.AreaCostEq

public section

namespace Ix.Sharing.Exact.AreaProof

open Ix.Sharing.Exact
open Ix.Sharing.Exact.LocalSearch (PosFn)

/-! ## Folds and checks over arrays -/

theorem arr_foldl_congr {α β : Type} (a : Array α) (f g : β → α → β)
    (h : ∀ x ∈ a.toList, ∀ b, f b x = g b x) (init : β) : a.foldl f init = a.foldl g init := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  generalize a.toList = l at h
  induction l generalizing init with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self]
    exact ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem arr_all_congr {α : Type} (a : Array α) (p q : α → Bool)
    (h : ∀ x ∈ a.toList, p x = q x) : a.all p = a.all q := by
  rw [← Array.all_toList, ← Array.all_toList]
  generalize a.toList = l at h
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.all_cons]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-! ## Bounds and visible counts without tuples

`reboundA` and `revisibleA` keep the tables of `reboundL` and `revisibleL`
field by field (`reboundA_eq`, `revisibleA_eq`), so every reader of them is
the specification's reader. -/

theorem rdA_eq_readAtF (pos L base : Array Nat) (u : Nat) :
    rdA pos L base u = readAtF (posOf pos) L id (base[·]!) u := by
  unfold rdA readAtF posOf
  by_cases h : pos[u]! = 0
  · simp [h]
  · have hb : (pos[u]! == 0) = false := by simpa using h
    have hn : (pos[u]! != 0) = true := by simpa using h
    simp only [hb, hn, Bool.false_eq_true, ite_false, Bool.true_and, decide_eq_true_eq, id]

theorem rdA_map {α : Type} [Inhabited α] (pos : Array Nat) (L : Array α) (proj : α → Nat)
    (base : Array Nat) (u : Nat) :
    rdA pos (L.map proj) base u = readAtF (posOf pos) L proj (base[·]!) u := by
  rw [rdA_eq_readAtF, Ix.Sharing.Exact.LocalSearch.readAtF_map]

theorem rdRev_eq_readAtF (k : Nat) (pos L base : Array Nat) (u : Nat) :
    rdRev k pos L base u = readAtF (posRev k pos) L id (base[·]!) u := by
  unfold rdRev readAtF posRev posOf
  by_cases h : pos[u]! = 0
  · simp [h]
  · have hb : (pos[u]! == 0) = false := by simpa using h
    have hn : (pos[u]! != 0) = true := by simpa using h
    have hk : k - 1 - (pos[u]! - 1) = k - pos[u]! := by omega
    simp only [hb, hn, Bool.false_eq_true, ite_false, hk, Bool.true_and, decide_eq_true_eq, id]

theorem rdRev_map {α : Type} [Inhabited α] (k : Nat) (pos : Array Nat) (L : Array α)
    (proj : α → Nat) (base : Array Nat) (u : Nat) :
    rdRev k pos (L.map proj) base u = readAtF (posRev k pos) L proj (base[·]!) u := by
  rw [rdRev_eq_readAtF, Ix.Sharing.Exact.LocalSearch.readAtF_map]

theorem areaFlags_spec (k : Nat) (posA ts : Array Nat) (i : Nat) :
    (areaFlags k posA ts)[i]! = true ↔ (i < k ∧ ∃ x ∈ ts.toList, posA[x]! = i + 1) := by
  unfold areaFlags
  rw [← Array.foldl_toList]
  have key : ∀ (l : List Nat) (f : Array Bool), f.size = k →
      (l.foldl (fun f t => let q := posA[t]!; if q != 0 then f.set! (q - 1) true else f) f).size = k ∧
      ((l.foldl (fun f t => let q := posA[t]!; if q != 0 then f.set! (q - 1) true else f) f)[i]!
        = true ↔ (f[i]! = true ∨ (i < k ∧ ∃ x ∈ l, posA[x]! = i + 1))) := by
    intro l
    induction l with
    | nil => intro f hf; simp [hf]
    | cons x l ih =>
      intro f hf
      simp only [List.foldl_cons]
      by_cases hx : posA[x]! = 0
      · have hb : (posA[x]! != 0) = false := by simp [hx]
        simp only [hb, Bool.false_eq_true, ite_false]
        obtain ⟨h1, h2⟩ := ih f hf
        refine ⟨h1, ?_⟩
        rw [h2]
        constructor
        · rintro (h | ⟨hi, y, hy, hyi⟩)
          · exact Or.inl h
          · exact Or.inr ⟨hi, y, List.mem_cons_of_mem _ hy, hyi⟩
        · rintro (h | ⟨hi, y, hy, hyi⟩)
          · exact Or.inl h
          · rcases List.mem_cons.mp hy with rfl | hy
            · omega
            · exact Or.inr ⟨hi, y, hy, hyi⟩
      · have hb : (posA[x]! != 0) = true := by simp [hx]
        simp only [hb, ite_true]
        obtain ⟨h1, h2⟩ := ih (f.set! (posA[x]! - 1) true) (by simp [hf])
        refine ⟨h1, ?_⟩
        rw [h2, getElem!_setBang]
        constructor
        · rintro (h | ⟨hi, y, hy, hyi⟩)
          · split at h
            · rename_i hc
              exact Or.inr ⟨by omega, x, List.mem_cons_self, by omega⟩
            · exact Or.inl h
          · exact Or.inr ⟨hi, y, List.mem_cons_of_mem _ hy, hyi⟩
        · rintro (h | ⟨hi, y, hy, hyi⟩)
          · left
            split
            · rfl
            · exact h
          · rcases List.mem_cons.mp hy with rfl | hy
            · left
              rw [ite_eq_left ⟨by omega, by omega⟩]
            · exact Or.inr ⟨hi, y, hy, hyi⟩
  obtain ⟨_, h2⟩ := key ts.toList (Array.replicate k false) (by simp)
  rw [h2]
  have h0 : (Array.replicate k false)[i]! = false := by
    by_cases hi : i < k
    · rw [getElem!_pos _ i (by simpa using hi)]; simp
    · rw [getElem!_neg _ i (by simpa using hi)]; rfl
  rw [h0]
  simp

/-- The flags of `areaFlags` at an area position: whether the term there is
listed. -/
theorem areaFlags_at {area posA ts : Array Nat} (hpos : PosFn area.size (area[·]!) (posOf posA))
    {i : Nat} (hi : i < area.size) :
    (areaFlags area.size posA ts)[i]! = ts.contains area[i]! := by
  have h := areaFlags_spec area.size posA ts i
  cases hc : ts.contains area[i]! with
  | true =>
    rw [h]
    refine ⟨hi, area[i]!, Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp hc), ?_⟩
    exact (Ix.Sharing.Exact.LocalSearch.posOf_some posA _ i).mp ((hpos _ i).mpr ⟨hi, rfl⟩)
  | false =>
    cases hf : (areaFlags area.size posA ts)[i]! with
    | false => rfl
    | true =>
      obtain ⟨_, x, hx, hxi⟩ := h.mp hf
      have := (hpos x i).mp ((Ix.Sharing.Exact.LocalSearch.posOf_some posA x i).mpr hxi)
      simp only at this
      rw [this.2] at hc
      rw [Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp hx)] at hc
      cases hc

theorem reboundA_eq (cx : SCtx) (posA : Array Nat)
    (hpos : PosFn cx.area.size (cx.area[·]!) (posOf posA)) (o : Array Nat) :
    (reboundA cx posA o).inl = (reboundL cx posA o).map (·.1) ∧
      (reboundA cx posA o).mrg = (reboundL cx posA o).map (·.2.1) ∧
      (reboundA cx posA o).head = (reboundL cx posA o).map (·.2.2.1) ∧
      (reboundA cx posA o).cont = (reboundL cx posA o).map (·.2.2.2) := by
  have key : ∀ m, m ≤ cx.area.size →
      foldRange (fun (st : Array Nat × Array Nat × Array Nat × Array Nat) i =>
        match st with
        | (I, M, H, C) =>
          match boundsValsG cx.up.prep cx.up.w
              (cx.cand[cx.area[i]!]! && !(areaFlags cx.area.size posA o)[i]!)
              (rdA posA H cx.bounds0.headLB) (rdA posA C cx.bounds0.contLB) cx.area[i]! with
          | (a, b, c, d) => (I.push a, M.push b, H.push c, C.push d))
        0 m (Array.mkEmpty cx.area.size, Array.mkEmpty cx.area.size, Array.mkEmpty cx.area.size,
          Array.mkEmpty cx.area.size) =
      ((foldRange (fun L i => L.push (boundsValsG cx.up.prep cx.up.w
          (maybeStoredAt cx o cx.area[i]!)
          (readAtF (posOf posA) L (·.2.2.1) (cx.bounds0.headLB[·]!))
          (readAtF (posOf posA) L (·.2.2.2) (cx.bounds0.contLB[·]!)) cx.area[i]!)) 0 m
          (Array.mkEmpty cx.area.size)).map (·.1),
       (foldRange (fun L i => L.push (boundsValsG cx.up.prep cx.up.w
          (maybeStoredAt cx o cx.area[i]!)
          (readAtF (posOf posA) L (·.2.2.1) (cx.bounds0.headLB[·]!))
          (readAtF (posOf posA) L (·.2.2.2) (cx.bounds0.contLB[·]!)) cx.area[i]!)) 0 m
          (Array.mkEmpty cx.area.size)).map (·.2.1),
       (foldRange (fun L i => L.push (boundsValsG cx.up.prep cx.up.w
          (maybeStoredAt cx o cx.area[i]!)
          (readAtF (posOf posA) L (·.2.2.1) (cx.bounds0.headLB[·]!))
          (readAtF (posOf posA) L (·.2.2.2) (cx.bounds0.contLB[·]!)) cx.area[i]!)) 0 m
          (Array.mkEmpty cx.area.size)).map (·.2.2.1),
       (foldRange (fun L i => L.push (boundsValsG cx.up.prep cx.up.w
          (maybeStoredAt cx o cx.area[i]!)
          (readAtF (posOf posA) L (·.2.2.1) (cx.bounds0.headLB[·]!))
          (readAtF (posOf posA) L (·.2.2.2) (cx.bounds0.contLB[·]!)) cx.area[i]!)) 0 m
          (Array.mkEmpty cx.area.size)).map (·.2.2.2)) := by
    intro m
    induction m with
    | zero => intro _; simp [Ix.Sharing.Exact.LocalSearch.foldRange_zero]
    | succ m ih =>
      intro hm
      rw [Ix.Sharing.Exact.LocalSearch.foldRange_succ, Ix.Sharing.Exact.LocalSearch.foldRange_succ,
        Nat.zero_add, ih (by omega)]
      generalize foldRange (fun L i => L.push (boundsValsG cx.up.prep cx.up.w
          (maybeStoredAt cx o cx.area[i]!)
          (readAtF (posOf posA) L (·.2.2.1) (cx.bounds0.headLB[·]!))
          (readAtF (posOf posA) L (·.2.2.2) (cx.bounds0.contLB[·]!)) cx.area[i]!)) 0 m
          (Array.mkEmpty cx.area.size) = L
      have hfl : (cx.cand[cx.area[m]!]! && !(areaFlags cx.area.size posA o)[m]!) =
          maybeStoredAt cx o cx.area[m]! := by
        rw [areaFlags_at hpos (by omega)]; rfl
      have hH : rdA posA (L.map (·.2.2.1)) cx.bounds0.headLB =
          readAtF (posOf posA) L (·.2.2.1) (cx.bounds0.headLB[·]!) := funext (rdA_map _ _ _ _)
      have hC : rdA posA (L.map (·.2.2.2)) cx.bounds0.contLB =
          readAtF (posOf posA) L (·.2.2.2) (cx.bounds0.contLB[·]!) := funext (rdA_map _ _ _ _)
      simp only [hfl, hH, hC, Array.map_push]
  have := key cx.area.size (Nat.le_refl _)
  simp only [reboundA, reboundL, localFold]
  rw [this]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem fold_pair (l : List (Nat × Nat × Nat)) (f g : Nat × Nat × Nat → Nat) (a b : Nat) :
    l.foldl (fun (dh : Nat × Nat) e => (dh.1 + f e, dh.2 + g e)) (a, b) =
      (l.foldl (fun acc e => acc + f e) a, l.foldl (fun acc e => acc + g e) b) := by
  induction l generalizing a b with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons]; exact ih _ _

theorem foldRange_sim {σ τ : Type} (f : σ → Nat → σ) (g : τ → Nat → τ) (R : σ → τ → Prop)
    (k : Nat) (hstep : ∀ s t i, i < k → R s t → R (f s i) (g t i)) (s0 : σ) (t0 : τ)
    (h0 : R s0 t0) : R (foldRange f 0 k s0) (foldRange g 0 k t0) := by
  have key : ∀ m, m ≤ k → R (foldRange f 0 m s0) (foldRange g 0 m t0) := by
    intro m
    induction m with
    | zero => intro _; exact h0
    | succ m ih =>
      intro hm
      rw [Ix.Sharing.Exact.LocalSearch.foldRange_succ, Ix.Sharing.Exact.LocalSearch.foldRange_succ,
        Nat.zero_add]
      exact hstep _ _ m (by omega) (ih (by omega))
  exact key k (Nat.le_refl _)

theorem outAt_eq {area posA : Array Nat} (hpos : PosFn area.size (area[·]!) (posOf posA))
    (o : Array Nat) (q : Nat) :
    outAt posA (areaFlags area.size posA o) (o.all (posA[·]! != 0)) o q = o.contains q := by
  unfold outAt
  split
  · rename_i hall
    by_cases hq : posA[q]! = 0
    · have hc : o.contains q = false := by
        cases hc : o.contains q
        · rfl
        · have := Array.all_eq_true'.mp hall q (Array.contains_iff_mem.mp hc)
          simp [hq] at this
      rw [hc]
      simp [hq]
    · obtain ⟨i, hi⟩ : ∃ i, posA[q]! = i + 1 := ⟨posA[q]! - 1, by omega⟩
      have hpi := (hpos q i).mp ((Ix.Sharing.Exact.LocalSearch.posOf_some posA q i).mpr hi)
      simp only at hpi
      simp only []
      rw [hi, Nat.add_sub_cancel, areaFlags_at hpos hpi.1, hpi.2]
      simp
  · rfl

theorem revisibleA_eq (cx : SCtx) (posA : Array Nat)
    (hpos : PosFn cx.area.size (cx.area[·]!) (posOf posA)) (o : Array Nat) :
    (revisibleA cx posA o).1 = (revisibleL cx posA o).map (·.1) ∧
      (revisibleA cx posA o).2 = (revisibleL cx posA o).map (·.2) := by
  have hR : (fun (s : Array Nat × Array Nat) (t : Array (Nat × Nat)) =>
      s = (t.map (·.1), t.map (·.2))) (revisibleA cx posA o) (revisibleL cx posA o) := by
    simp only [revisibleA, revisibleL, localFold]
    apply foldRange_sim (R := fun (s : Array Nat × Array Nat) (t : Array (Nat × Nat)) =>
      s = (t.map (·.1), t.map (·.2)))
    · intro s t i _ hst
      subst hst
      have hw : ∀ q, visW cx posA (outAt posA (areaFlags cx.area.size posA o)
          (o.all (posA[·]! != 0)) o) (t.map (·.1)) q =
          (if maybeStoredAt cx o q then 1
           else min (readAtF (posRev cx.area.size posA) t (·.1) (cx.vis0.1[·]!) q) visibleCap) := by
        intro q
        unfold visW maybeStoredAt
        rw [outAt_eq hpos, rdRev_map]
      simp only [hw, Array.map_push]
      rw [← Array.foldl_toList, ← Array.foldl_toList, ← Array.foldl_toList, fold_pair]
    · simp
  simp only at hR
  rw [hR]
  exact ⟨rfl, rfl⟩

theorem opaqueUnderA_eq (cx : SCtx) (posA : Array Nat)
    (hpos : PosFn cx.area.size (cx.area[·]!) (posOf posA)) (o : Array Nat) (t : Nat) :
    opaqueUnderA cx posA (reboundA cx posA o) t = opaqueUnderL cx posA (reboundL cx posA o) t := by
  obtain ⟨h1, h2, _, _⟩ := reboundA_eq cx posA hpos o
  unfold opaqueUnderA opaqueUnderL
  rw [h1, h2, rdA_map, rdA_map]

theorem opqArrA_eq (cx : SCtx) (posA : Array Nat)
    (hpos : PosFn cx.area.size (cx.area[·]!) (posOf posA)) (o inAll : Array Nat) (t : Nat) :
    opqArrA cx posA (reboundA cx posA o) inAll t = opqArrR cx posA (reboundL cx posA o) inAll t := by
  unfold opqArrA opqArrR
  rw [opaqueUnderA_eq cx posA hpos]

theorem reclassifyA_eq (cx : SCtx) (posA : Array Nat)
    (hpos : PosFn cx.area.size (cx.area[·]!) (posOf posA)) (o localIn und : Array Nat) :
    reclassifyA cx posA o localIn und =
      ((reclassifyL cx posA o localIn und).1, (reclassifyL cx posA o localIn und).2.1,
        reboundA cx posA o) := by
  obtain ⟨h1, h2, _, _⟩ := reboundA_eq cx posA hpos o
  obtain ⟨v1, v2⟩ := revisibleA_eq cx posA hpos o
  have e1 : rdA posA (reboundA cx posA o).inl cx.bounds0.inlineLB =
      readAtF (posOf posA) (reboundL cx posA o) (·.1) (cx.bounds0.inlineLB[·]!) := by
    rw [h1]; exact funext (rdA_map _ _ _ _)
  have e2 : rdA posA (reboundA cx posA o).mrg cx.bounds0.mergedLB =
      readAtF (posOf posA) (reboundL cx posA o) (·.2.1) (cx.bounds0.mergedLB[·]!) := by
    rw [h2]; exact funext (rdA_map _ _ _ _)
  have e3 : ∀ t, rdRev cx.area.size posA (revisibleA cx posA o).1 cx.vis0.1 t =
      readAtF (posRev cx.area.size posA) (revisibleL cx posA o) (·.1) (cx.vis0.1[·]!) t := by
    intro t; rw [v1, rdRev_map]
  have e4 : ∀ t, rdRev cx.area.size posA (revisibleA cx posA o).2 cx.vis0.2 t =
      readAtF (posRev cx.area.size posA) (revisibleL cx posA o) (·.2) (cx.vis0.2[·]!) t := by
    intro t; rw [v2, rdRev_map]
  unfold reclassifyA reclassifyL
  simp only [e1, e2, e3, e4]

/-! ## Local folds as fixed points -/

theorem localFold_entries {V : Type} [Inhabited V] (k : Nat) (xsAt : Nat → Nat)
    (G : Array V → Nat → Nat → V) (m : Nat) :
    (foldRange (fun L i => L.push (G L i (xsAt i))) 0 m (Array.mkEmpty k)).size = m ∧
      ∀ q, q < m → (foldRange (fun L i => L.push (G L i (xsAt i))) 0 m (Array.mkEmpty k))[q]! =
        G (foldRange (fun L i => L.push (G L i (xsAt i))) 0 q (Array.mkEmpty k)) q (xsAt q) := by
  induction m with
  | zero => exact ⟨by simp [Ix.Sharing.Exact.LocalSearch.foldRange_zero],
      fun q hq => absurd hq (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨s, he⟩ := ih
    rw [Ix.Sharing.Exact.LocalSearch.foldRange_succ, Nat.zero_add]
    refine ⟨by rw [Array.size_push, s], fun q hq => ?_⟩
    rw [push_read, s]
    by_cases hqm : q < m
    · rw [ite_eq_left hqm]; exact he q hqm
    · have hq' : q = m := by omega
      subst hq'
      simp

theorem readAtF_some {α : Type} [Inhabited α] {posf : Nat → Option Nat} {L : Array α}
    {base : Nat → α} {u j : Nat} (hp : posf u = some j) (hj : j < L.size) :
    readAtF posf L id base u = L[j]! := by
  unfold readAtF; rw [hp]; simp [hj]

theorem readAtF_none {α : Type} [Inhabited α] {posf : Nat → Option Nat} {L : Array α}
    {base : Nat → α} {u : Nat} (hp : posf u = none) : readAtF posf L id base u = base u := by
  unfold readAtF; rw [hp]

/-- The reader of a local fold whose step reads only below the term is a
fixed point of the step at the fold's terms and the base elsewhere. -/
theorem localFold_fix {V : Type} [Inhabited V] (xs pos : Array Nat) (hinc : strictInc xs = true)
    (hpos : PosFn xs.size (xs[·]!) (posOf pos)) (base : Nat → V) (F : (Nat → V) → Nat → V)
    (hF : ∀ g g' t, InA xs t → (∀ u, u < t → g u = g' u) → F g t = F g' t) (t : Nat) :
    (InA xs t →
      readAtF (posOf pos) (localFold xs.size (xs[·]!)
        (fun L _ t => F (readAtF (posOf pos) L id base) t)) id base t =
      F (readAtF (posOf pos) (localFold xs.size (xs[·]!)
        (fun L _ t => F (readAtF (posOf pos) L id base) t)) id base) t) ∧
    (¬ InA xs t → readAtF (posOf pos) (localFold xs.size (xs[·]!)
        (fun L _ t => F (readAtF (posOf pos) L id base) t)) id base t = base t) := by
  have hL := localFold_entries xs.size (xs[·]!) (fun L _ t => F (readAtF (posOf pos) L id base) t)
  have hLk : localFold xs.size (xs[·]!) (fun L _ t => F (readAtF (posOf pos) L id base) t) =
      foldRange (fun L i => L.push (F (readAtF (posOf pos) L id base) xs[i]!)) 0 xs.size
        (Array.mkEmpty xs.size) := rfl
  rw [hLk]
  constructor
  · rintro ⟨j, hj, hjt⟩
    rw [readAtF_some ((hpos t j).mpr ⟨hj, hjt⟩) (by rw [(hL xs.size).1]; exact hj),
      (hL xs.size).2 j hj, hjt]
    apply hF _ _ t ⟨j, hj, hjt⟩
    intro u hu
    cases hp : posOf pos u with
    | none => rw [readAtF_none hp, readAtF_none hp]
    | some q =>
      obtain ⟨hq, hqu⟩ := (hpos u q).mp hp
      simp only at hqu
      have hqj : q < j := (strictInc_lt_iff hinc hq hj).mp (by rw [hqu, hjt]; exact hu)
      rw [readAtF_some hp (by rw [(hL j).1]; exact hqj),
        readAtF_some hp (by rw [(hL xs.size).1]; exact hq), (hL j).2 q hqj, (hL xs.size).2 q hq]
  · intro hn
    cases hp : posOf pos t with
    | none => exact readAtF_none hp
    | some q => exact absurd ⟨q, ((hpos t q).mp hp).1, ((hpos t q).mp hp).2⟩ hn

/-! ## Reach labels over the area -/

/-- The reach-label step at `t` from the labels `g` of the other terms. -/
def reachF (dag : Dag) (opq : Nat → Bool) (lab : Nat → Option Nat) (g : Nat → Option (Option Nat))
    (t : Nat) : Option (Option Nat) :=
  (dag.node t).children.foldl (fun v c => labelJoin v (if opq c then (lab c).map some else g c))
    ((lab t).map some)

theorem reachLabelsL_eq (dag : Dag) (xs pos : Array Nat) (opq : Nat → Bool)
    (lab : Nat → Option Nat) :
    reachLabelsL dag xs pos opq lab = localFold xs.size (xs[·]!)
      (fun L _ t => reachF dag opq lab (readAtF (posOf pos) L id (fun _ => none)) t) := by
  unfold reachLabelsL reachF
  rfl

theorem labelJoin_none_fold (l : List Nat) :
    l.foldl (fun v (_ : Nat) => labelJoin v none) none = none := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons]; exact ih

section Reach

variable {dag : Dag} (h : DagOK dag)

include h in
theorem reachF_congr (opq : Nat → Bool) (lab : Nat → Option Nat) (xs : Array Nat)
    (hlt : ∀ u, InA xs u → u < dag.size) (g g' : Nat → Option (Option Nat)) (t : Nat)
    (ht : InA xs t) (hg : ∀ u, u < t → g u = g' u) : reachF dag opq lab g t = reachF dag opq lab g' t := by
  unfold reachF
  apply arr_foldl_congr
  intro c hc b
  rw [hg c (h.child_lt (hlt t ht) (Array.mem_toList_iff.mp hc))]

include h in
/-- **Reach labels over the area.** With labels only on non-opaque area terms,
the area closed upward through its non-opaque terms and inside the closure,
the reach labels over the area agree with those over the closure at every area
term. -/
theorem reach_area (opq : Nat → Bool) (lab : Nat → Option Nat) (opaq : Nat → Bool)
    (area posA closure posC : Array Nat)
    (hincA : strictInc area = true) (hposA : PosFn area.size (area[·]!) (posOf posA))
    (hincC : strictInc closure = true) (hposC : PosFn closure.size (closure[·]!) (posOf posC))
    (hAlt : ∀ u, InA area u → u < dag.size) (hClt : ∀ u, InA closure u → u < dag.size)
    (hopq : ∀ u, opaq u = true → opq u = true)
    (hlab : ∀ u, lab u ≠ none → InA area u ∧ opaq u = false)
    (hclose : ∀ y q, InA area y → opaq y = false → q < dag.size →
      y ∈ (dag.node q).children → InA area q)
    (hAC : ∀ u, InA area u → InA closure u) (v : Nat) (hv : InA area v) :
    readAtF (posOf posC) (reachLabelsL dag closure posC opq lab) id (fun _ => none) v =
      readAtF (posOf posA) (reachLabelsL dag area posA opq lab) id (fun _ => none) v := by
  rw [reachLabelsL_eq, reachLabelsL_eq]
  have fixC := localFold_fix closure posC hincC hposC (fun _ => none) (reachF dag opq lab)
    (fun g g' t ht hg => reachF_congr h opq lab closure hClt g g' t ht hg)
  have fixA := localFold_fix area posA hincA hposA (fun _ => none) (reachF dag opq lab)
    (fun g g' t ht hg => reachF_congr h opq lab area hAlt g g' t ht hg)
  generalize readAtF (posOf posC) (localFold closure.size (closure[·]!)
    (fun L _ t => reachF dag opq lab (readAtF (posOf posC) L id (fun _ => none)) t)) id
    (fun _ => none) = Rc at fixC
  generalize readAtF (posOf posA) (localFold area.size (area[·]!)
    (fun L _ t => reachF dag opq lab (readAtF (posOf posA) L id (fun _ => none)) t)) id
    (fun _ => none) = Ra at fixA
  have key : ∀ u, (InA area u → Rc u = Ra u) ∧ (¬ InA area u → Rc u = none) := by
    intro u
    induction u using Nat.strongRecOn with
    | _ u ih =>
      constructor
      · intro hu
        rw [(fixC u).1 (hAC u hu), (fixA u).1 hu]
        unfold reachF
        apply arr_foldl_congr
        intro c hc b
        have hcu := h.child_lt (hAlt u hu) (Array.mem_toList_iff.mp hc)
        by_cases hoc : opq c = true
        · simp only [hoc, ite_true]
        · simp only [hoc, Bool.false_eq_true, ite_false]
          by_cases hca : InA area c
          · rw [(ih c hcu).1 hca]
          · rw [(ih c hcu).2 hca, (fixA c).2 hca]
      · intro hu
        by_cases huc : InA closure u
        · rw [(fixC u).1 huc]
          unfold reachF
          have hlu : lab u = none := by
            cases hl : lab u with
            | none => rfl
            | some k => exact absurd (hlab u (by rw [hl]; simp)).1 hu
          rw [hlu, Option.map_none]
          rw [arr_foldl_congr _ _ (fun v _ => labelJoin v none) ?_, ← Array.foldl_toList]
          · exact labelJoin_none_fold _
          · intro c hc b
            have hcm := Array.mem_toList_iff.mp hc
            have hcu := h.child_lt (hClt u huc) hcm
            by_cases hoc : opq c = true
            · simp only [hoc, ite_true]
              have : lab c = none := by
                cases hl : lab c with
                | none => rfl
                | some k =>
                  obtain ⟨hca, hco⟩ := hlab c (by rw [hl]; simp)
                  exact absurd (hclose c u hca hco (hClt u huc) hcm) hu
              rw [this, Option.map_none]
            · simp only [hoc, Bool.false_eq_true, ite_false]
              have hca : ¬ InA area c := by
                intro hca
                have hco : opaq c = false := by
                  cases hq : opaq c
                  · rfl
                  · exact absurd (hopq c hq) hoc
                exact hu (hclose c u hca hco (hClt u huc) hcm)
              rw [(ih c hcu).2 hca]
        · exact (fixC u).2 huc
  exact (key v).1 hv

include h in
/-- The separation check over the area and over the closure, with the
labels of `sepLab`. -/
theorem sep_core (members g inRed outRed : Array Nat) (opqR opaq : Nat → Bool)
    (area posA closure posC : Array Nat)
    (hincA : strictInc area = true) (hposA : PosFn area.size (area[·]!) (posOf posA))
    (hincC : strictInc closure = true) (hposC : PosFn closure.size (closure[·]!) (posOf posC))
    (hAlt : ∀ u, InA area u → u < dag.size) (hClt : ∀ u, InA closure u → u < dag.size)
    (hopq : ∀ u, opaq u = true → opqR u = true)
    (hmem : ∀ m, members.contains m = true → InA area m ∧ opaq m = false)
    (hclose : ∀ y q, InA area y → opaq y = false → q < dag.size →
      y ∈ (dag.node q).children → InA area q)
    (hAC : ∀ u, InA area u → InA closure u) :
    (g.all (fun t => (decide (t < dag.size) && members.contains t) &&
        sepLab dag.size members g inRed outRed t == some 1) &&
      members.all fun v => (decide (v < dag.size) && outRed.contains v) || opqR v ||
        readAtF (posOf posA) (reachLabelsL dag area posA opqR
          (sepLab dag.size members g inRed outRed)) id (fun _ => none) v != some none) =
    (g.all (fun t => (decide (t < dag.size) && members.contains t) &&
        sepLab dag.size members g inRed outRed t == some 1) &&
      members.all fun v => (decide (v < dag.size) && outRed.contains v) || opqR v ||
        readAtF (posOf posC) (reachLabelsL dag closure posC opqR
          (sepLab dag.size members g inRed outRed)) id (fun _ => none) v != some none) := by
  cases hG : g.all (fun t => (decide (t < dag.size) && members.contains t) &&
      sepLab dag.size members g inRed outRed t == some 1) with
  | false => rfl
  | true =>
    simp only [Bool.true_and]
    have hgm : ∀ u, g.contains u = true → members.contains u = true := by
      intro u hu
      have := Array.all_eq_true'.mp hG u (Array.contains_iff_mem.mp hu)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.2
    have hlab : ∀ u, sepLab dag.size members g inRed outRed u ≠ none → InA area u ∧ opaq u = false := by
      intro u hu
      apply hmem
      unfold sepLab at hu
      split at hu
      · split at hu
        · exact absurd rfl hu
        · split at hu
          · exact hgm u (by assumption)
          · split at hu
            · assumption
            · exact absurd rfl hu
      · exact absurd rfl hu
    apply arr_all_congr
    intro v hv
    have hvA := (hmem v (Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp hv))).1
    rw [reach_area h opqR _ opaq area posA closure posC hincA hposA hincC hposC hAlt hClt hopq
      hlab hclose hAC v hvA]

end Reach

/-- The light context of a component: its context without the closure. -/
abbrev lightCx (cx : SCtx) : SCtx := { cx with closure := #[], rootsC := #[], storedInC := #[] }

/-- **Separation check.** `sepCheckA` on the light context is `sepCheckL`. -/
theorem sepCheckA_eq {cx : SCtx} {posA posC : Array Nat}
    (hr : Ix.Sharing.Exact.LocalSearch.Ready cx posA posC) (hdag : DagOK cx.up.prep.dag)
    (hmem : ∀ m, cx.members.contains m = true → InA cx.area m ∧ cx.up.opaq[m]! = false)
    (hclose : ∀ y q, InA cx.area y → cx.up.opaq[y]! = false → q < cx.up.prep.dag.size →
      y ∈ (cx.up.prep.dag.node q).children → InA cx.area q)
    (hAC : ∀ y, InA cx.area y → InA cx.closure y) (g inRed outRed : Array Nat) :
    sepCheckA (lightCx cx) posA g inRed outRed = sepCheckL cx posA posC g inRed outRed := by
  obtain ⟨_, _, _, _, _, _, _, _, hareaLt, hclLt⟩ :=
    Ix.Sharing.Exact.LocalSearch.localSearchOK_spec hr.ok
  obtain ⟨hincA, hincC⟩ := Ix.Sharing.Exact.LocalSearch.localSearchOK_inc hr.ok
  have hoa : ∀ t, opqArrA (lightCx cx) posA (reboundA (lightCx cx) posA outRed) inRed t =
      opqArrR cx posA (reboundL cx posA outRed) inRed t :=
    fun t => opqArrA_eq cx posA hr.area outRed inRed t
  unfold sepCheckA sepCheckL
  simp only [hoa, reachLabelsA_eq]
  exact sep_core hdag cx.members g inRed outRed
    (fun t => opqArrR cx posA (reboundL cx posA outRed) inRed t) (cx.up.opaq[·]!)
    cx.area posA cx.closure posC hincA hr.area hincC hr.closure
    (fun u ⟨j, hj, hju⟩ => hju ▸ hareaLt j hj) (fun u ⟨j, hj, hju⟩ => hju ▸ hclLt j hj)
    (fun u hu => by unfold opqArrR; simp [hu]) hmem hclose hAC

/-- **The area search block** is the local search block, given the component
cost and the separation check. -/
theorem block_eq (cx : SCtx) (posA posC : Array Nat) (tb : TBase) (aux : AAux)
    (fb : Unit → SCtx × Array Nat) (limits : Limits)
    (hphi : ∀ avail stored, phiA (lightCx cx) posA tb aux fb avail stored =
      phiEL2 cx posA posC avail stored)
    (hsep : ∀ g i o, sepCheckA (lightCx cx) posA g i o = sepCheckL cx posA posC g i o)
    (hrc : ∀ o l u, reclassifyA (lightCx cx) posA o l u =
      ((reclassifyL cx posA o l u).1, (reclassifyL cx posA o l u).2.1,
        reboundA (lightCx cx) posA o))
    (hou : ∀ o t, opaqueUnderA (lightCx cx) posA (reboundA (lightCx cx) posA o) t =
      opaqueUnderL cx posA (reboundL cx posA o) t)
    (hoa : ∀ o i t, opqArrA (lightCx cx) posA (reboundA (lightCx cx) posA o) i t =
      opqArrR cx posA (reboundL cx posA o) i t) :
    ∀ fuel,
    (∀ g inAll outAll st, solvePA (lightCx cx) posA tb aux fb limits fuel g inAll outAll st =
      solvePL cx posA posC limits fuel g inAll outAll st) ∧
    (∀ g inRed outRed st, solveBodyA (lightCx cx) posA tb aux fb limits fuel g inRed outRed st =
      solveBodyL cx posA posC limits fuel g inRed outRed st) ∧
    (∀ phi0 inCtx outAll nOutCtx localIn und ct st,
      nodePA (lightCx cx) posA tb aux fb limits fuel phi0 inCtx outAll nOutCtx localIn und ct st =
        nodePL cx posA posC limits fuel phi0 inCtx outAll nOutCtx localIn und ct st) ∧
    (∀ inAll outAll grps comb st,
      splitPA (lightCx cx) posA tb aux fb limits fuel inAll outAll grps comb st =
        splitPL cx posA posC limits fuel inAll outAll grps comb st)
  | 0 => by
    refine ⟨fun _ _ _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ _ _ _ _ _ => ?_,
      fun _ _ _ _ _ => ?_⟩
    · simp only [solvePA, solvePL]
    · simp only [solveBodyA, solveBodyL]
    · simp only [nodePA, nodePL]
    · simp only [splitPA, splitPL]
  | fuel + 1 => by
    obtain ⟨ihP, ihB, ihN, ihS⟩ :=
      block_eq cx posA posC tb aux fb limits hphi hsep hrc hou hoa fuel
    refine ⟨fun g inAll outAll st => ?_, fun g inRed outRed st => ?_,
      fun phi0 inCtx outAll nOutCtx localIn und ct st => ?_,
      fun inAll outAll grps comb st => ?_⟩
    · simp only [solvePA, solvePL, hsep, hoa, memoKeyA_eq, ihB] <;> rfl
    · simp only [solveBodyA, solveBodyL, hphi, ihN] <;> rfl
    · simp only [nodePA, nodePL, hphi, hrc, hou, groupsA_eq, memoKeyA_eq, ihN, ihS] <;> rfl
    · cases grps with
      | nil => simp only [splitPA, splitPL]
      | cons grp grps => simp only [splitPA, splitPL, ihP, ihS]

end Ix.Sharing.Exact.AreaProof

end
