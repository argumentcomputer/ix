import Compilatrix.Rt.Proof.LayoutFun
import Compilatrix.Lir.Proof.Relabel

/-!
# Pruning keeps the reached blocks in lock step

`pruneWith seen raw` keeps the blocks whose labels `seen` contains, in
order, and renumbers the edges by rank among the kept labels. With `seen`
containing the entry and closed under successors (`function` checks
`reachClosed`), the pruned function simulates the unpruned one under
"`l` is kept at rank `l'`" (`prune_sim`): related labels hold the same
block, edges go to related labels, and ranks keep the label order, so each
edge charges as before.
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word Label)
open Compilatrix.Rt.Lower
open Compilatrix.Src (NatMap NatSet)

/-! ## The reached set -/

theorem contains_insert (s : NatSet) (k j : Nat) (h : s.contains j = true) : (s.insert k).contains j = true := by
  simp only [NatMap.contains, NatSet.insert, NatMap.get?_insert] at h ⊢
  split <;> simp_all

theorem foldl_contains (l : List Nat) :
    ∀ (s : NatSet) (acc : List Nat) (j : Nat), s.contains j = true →
      (l.foldl (fun (p : NatSet × List Nat) t => if p.1.contains t then (p.1, p.2) else (p.1.insert t, t :: p.2))
        (s, acc)).1.contains j = true := by
  induction l with
  | nil => intro s acc j h; exact h
  | cons t l ih =>
    intro s acc j h
    simp only [List.foldl_cons]
    split
    · exact ih _ _ _ h
    · exact ih _ _ _ (contains_insert _ _ _ h)

/-- The worklist only adds labels. -/
theorem reach_mono (succ : NatMap (List Label)) :
    ∀ (fuel : Nat) (ls : List Label) (seen : NatSet) (j : Nat), seen.contains j = true →
      (reach succ fuel ls seen).contains j = true
  | 0, _, _, _, h => h
  | _ + 1, [], _, _, h => h
  | fuel + 1, l :: ls, seen, j, h => by
    simp only [reach]
    exact reach_mono succ fuel _ _ j (foldl_contains _ _ _ _ h)

theorem reachable_zero (raw : List Lir.Block) : (reachable raw).contains 0 = true := by
  unfold reachable
  apply reach_mono
  simp [NatSet.ofList, NatMap.ofList, NatMap.contains, NatMap.get?_insert]

/-! ## The kept blocks -/

/-- The kept blocks' labels and positions. -/
theorem kept_spec (P : Nat → Bool) :
    ∀ (xs : List Lir.Block) (k : Nat),
      (∀ {r : Nat} {b : Lir.Block} {l : Nat}, ((xs.zipIdx k).filter fun p => P p.2)[r]? = some (b, l) →
        k ≤ l ∧ xs[l - k]? = some b ∧ P l = true) ∧
      (∀ {b : Lir.Block} {l : Nat}, k ≤ l → xs[l - k]? = some b → P l = true →
        ∃ r : Nat, ((xs.zipIdx k).filter fun p => P p.2)[r]? = some (b, l)) ∧
      (∀ {r r' : Nat} {b b' : Lir.Block} {l l' : Nat}, ((xs.zipIdx k).filter fun p => P p.2)[r]? = some (b, l) →
        ((xs.zipIdx k).filter fun p => P p.2)[r']? = some (b', l') → r < r' → l < l')
  | [], k => ⟨fun h => by simp at h, fun _ h _ => by simp at h, fun h => by simp at h⟩
  | x :: xs, k => by
    obtain ⟨ih₁, ih₂, ih₃⟩ := kept_spec P xs (k + 1)
    simp only [List.zipIdx_cons, List.filter_cons]
    cases hP : P k with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨fun {r b l} h => ?_, fun {b l} hk hb hl => ?_, fun {r r' b b' l l'} h h' hr => ih₃ h h' hr⟩
      · obtain ⟨h1, h2, h3⟩ := ih₁ h
        refine ⟨by omega, ?_, h3⟩
        rw [show l - k = (l - (k + 1)) + 1 by omega]
        simpa using h2
      · by_cases hlk : l = k
        · subst hlk; rw [hP] at hl; cases hl
        · exact ih₂ (by omega) (by rw [show l - k = (l - (k + 1)) + 1 by omega] at hb; simpa using hb) hl
    | true =>
      simp only [↓reduceIte]
      refine ⟨fun {r b l} h => ?_, fun {b l} hk hb hl => ?_, fun {r r' b b' l l'} h h' hr => ?_⟩
      · cases r with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨Nat.le_refl _, by simp, hP⟩
        | succ r =>
          simp only [List.getElem?_cons_succ] at h
          obtain ⟨h1, h2, h3⟩ := ih₁ h
          refine ⟨by omega, ?_, h3⟩
          rw [show l - k = (l - (k + 1)) + 1 by omega]
          simpa using h2
      · by_cases hlk : l = k
        · subst hlk
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hb
          subst hb
          exact ⟨0, rfl⟩
        · obtain ⟨r, hr⟩ := ih₂ (by omega)
            (by rw [show l - k = (l - (k + 1)) + 1 by omega] at hb; simpa using hb) hl
          exact ⟨r + 1, by simpa using hr⟩
      · cases r with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          cases r' with
          | zero => omega
          | succ r' =>
            simp only [List.getElem?_cons_succ] at h'
            have := (ih₁ h').1
            omega
        | succ r =>
          cases r' with
          | zero => omega
          | succ r' =>
            simp only [List.getElem?_cons_succ] at h h'
            exact ih₃ h h' (by omega)


/-- The blocks `pruneWith` keeps, with their labels. -/
abbrev keptOf (raw : List Lir.Block) (seen : NatSet) : List (Lir.Block × Nat) :=
  (raw.zipIdx 0).filter fun p => seen.contains p.2

/-- Label `l` is kept at rank `l'`. -/
def Kept (raw : List Lir.Block) (seen : NatSet) (l l' : Label) : Prop :=
  ∃ b, (keptOf raw seen)[l']? = some (b, l)

theorem kept_le_iff {raw : List Lir.Block} {seen : NatSet} {l l' t t' : Nat} (h : Kept raw seen l l')
    (h' : Kept raw seen t t') : (t' ≤ l' ↔ t ≤ l) := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨b', hb'⟩ := h'
  obtain ⟨-, -, hmono⟩ := kept_spec (fun l => seen.contains l) raw 0
  constructor
  · intro hle
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · exact Nat.le_of_lt (hmono hb' hb hlt)
    · rw [hb] at hb'; cases hb'; exact Nat.le_refl _
  · intro hle
    apply Nat.le_of_not_lt
    intro hgt
    have := hmono hb hb' hgt
    omega

/-- The rank map of `pruneWith`. -/
abbrev rankOf (raw : List Lir.Block) (seen : NatSet) : NatMap Label :=
  NatMap.ofList ((keptOf raw seen).zipIdx.map fun ((_, l), r) => (l, r))

theorem rank_get {raw : List Lir.Block} {seen : NatSet} {l l' : Nat} (h : Kept raw seen l l') :
    (rankOf raw seen).get? l = some l' := by
  obtain ⟨b, hb⟩ := h
  apply NatMap.get?_ofList
  · have hkeys : ((keptOf raw seen).zipIdx.map fun ((_, l), r) => (l, r)).map (·.1) =
        (keptOf raw seen).map (·.2) := by
      apply List.ext_getElem?
      intro i
      simp [List.getElem?_zipIdx]
      cases (keptOf raw seen)[i]? <;> rfl
    rw [hkeys]
    apply List.Pairwise.imp (R := (· < ·)) (fun h => Nat.ne_of_lt h)
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_map] at hi hj
    simp only [List.getElem_map]
    obtain ⟨-, -, hmono⟩ := kept_spec (fun l => seen.contains l) raw 0
    have h1 : (keptOf raw seen)[i]? = some ((keptOf raw seen)[i].1, (keptOf raw seen)[i].2) := by
      simp [List.getElem?_eq_getElem hi]
    have h2 : (keptOf raw seen)[j]? = some ((keptOf raw seen)[j].1, (keptOf raw seen)[j].2) := by
      simp [List.getElem?_eq_getElem hj]
    exact hmono h1 h2 hij
  · rw [List.mem_map]
    exact ⟨((b, l), l'), List.mem_zipIdx_iff_getElem?.2 (by simpa using hb), rfl⟩

/-- A kept label is related to its rank; every reached label of the
function is kept. -/
theorem kept_of_seen {raw : List Lir.Block} {seen : NatSet} {t : Nat} {TB : Lir.Block} (ht : raw[t]? = some TB)
    (hs : seen.contains t = true) : ∃ r, Kept raw seen t r := by
  obtain ⟨r, hr⟩ := (kept_spec (fun l => seen.contains l) raw 0).2.1 (Nat.zero_le t) (by simpa using ht) hs
  exact ⟨r, TB, hr⟩

/-- **Pruning simulates the unpruned function.** -/
theorem prune_sim {F : Lir.Func} {raw : List Lir.Block} (hF : F.blocks = raw.toArray) {seen : NatSet}
    (hc : reachClosed raw seen = true) (h0 : seen.contains 0 = true) (hne : raw ≠ []) :
    Lir.FuncSim F { F with blocks := (pruneWith seen raw).toArray } (Kept raw seen) := by
  have hspec := kept_spec (fun l => seen.contains l) raw 0
  have hclosed : ∀ {l : Nat} {B : Lir.Block}, raw[l]? = some B → seen.contains l = true →
      ∀ t ∈ B.term.succs, seen.contains t = true := by
    intro l B hB hl t ht
    unfold reachClosed at hc
    rw [List.all_eq_true] at hc
    have := hc (B, l) (List.mem_zipIdx_iff_getElem?.2 (by simpa using hB))
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at this
    rcases this with h | h
    · rw [hl] at h; cases h
    · exact h t ht
  refine ⟨rfl, ?_, ?_⟩
  · -- the entry
    obtain ⟨b0, hb0⟩ : ∃ b0, raw[0]? = some b0 := by
      cases raw with
      | nil => exact absurd rfl hne
      | cons b _ => exact ⟨b, rfl⟩
    obtain ⟨r, b, hr⟩ := kept_of_seen hb0 h0
    refine ⟨b, ?_⟩
    cases r with
    | zero => exact hr
    | succ r =>
      exfalso
      cases hk : (keptOf raw seen)[0]? with
      | none =>
        simp only [List.getElem?_eq_none_iff] at hk
        have := (List.getElem?_eq_some_iff.1 hr).1
        omega
      | some p =>
        obtain ⟨b', l'⟩ := p
        have := hspec.2.2 hk hr (Nat.succ_pos r)
        omega
  · intro l l' B ⟨b, hb⟩ hB
    rw [hF, List.getElem?_toArray] at hB
    obtain ⟨-, hraw, hseen⟩ := hspec.1 hb
    simp only [Nat.sub_zero] at hraw
    rw [hraw] at hB
    cases hB
    let g : Lir.Edge → Lir.Edge := fun e => { e with target := (rankOf raw seen).getD e.target 0 }
    have hedge : ∀ e ∈ B.term.edges, Lir.EdgeSim F { F with blocks := (pruneWith seen raw).toArray }
        (Kept raw seen) l l' e (g e) := by
      intro e he TB hTB
      rw [hF, List.getElem?_toArray] at hTB
      have hst : seen.contains e.target = true :=
        hclosed hraw hseen e.target (List.mem_map.2 ⟨e, he, rfl⟩)
      obtain ⟨r, hr⟩ := kept_of_seen hTB hst
      have hrank : (rankOf raw seen).getD e.target 0 = r := by
        simp [NatMap.getD, rank_get hr]
      refine .inl ⟨rfl, by simpa [g, hrank] using hr, ?_⟩
      simp only [g, hrank]
      exact decide_eq_decide.2 (kept_le_iff ⟨_, hb⟩ hr)
    refine ⟨B.term.setEdges (B.term.edges.map g), B.cold, ?_, ?_⟩
    · show (pruneWith seen raw).toArray[l']? = _
      rw [List.getElem?_toArray]
      unfold pruneWith
      simp only [List.getElem?_map]
      rw [show (List.filter (fun x => match x with | (_, l) => seen.contains l) raw.zipIdx) = keptOf raw seen from rfl, hb]
      rfl
    · cases ht : B.term with
      | jump e =>
        refine ⟨g e, by simp [Lir.Term.setEdges, Lir.Term.edges], ?_⟩
        exact hedge e (by rw [ht]; simp [Lir.Term.edges])
      | br c w a b' t f =>
        refine ⟨g t, g f, by simp [Lir.Term.setEdges, Lir.Term.edges], hedge t ?_, hedge f ?_⟩ <;>
          · rw [ht]; simp [Lir.Term.edges]
      | brOvf o x a b' ok ovf =>
        refine ⟨g ok, g ovf, by simp [Lir.Term.setEdges, Lir.Term.edges], hedge ok ?_, hedge ovf ?_⟩ <;>
          · rw [ht]; simp [Lir.Term.edges]
      | ret as => simp [Lir.TermSim, Lir.Term.setEdges, Lir.Term.edges]
      | tail g' as => simp [Lir.TermSim, Lir.Term.setEdges, Lir.Term.edges]
      | fail r => simp [Lir.TermSim, Lir.Term.setEdges, Lir.Term.edges]
      | trap => simp [Lir.TermSim, Lir.Term.setEdges, Lir.Term.edges]

end Compilatrix.Rt.Proof
