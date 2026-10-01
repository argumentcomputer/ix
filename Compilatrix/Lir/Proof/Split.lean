import Compilatrix.Lir.Proof.Relabel
import Compilatrix.Lir.SplitEdges

/-!
# Splitting critical edges keeps the clock

`splitCriticalEdges` places each block's split blocks right after it, so
block `l` moves to `l + (splits before it)` and a split block for the `k`-th
critical edge of block `l` sits at its new label plus `1 + k`. Each critical
edge becomes a forward (free) edge to its split block, whose jump carries
the edge's arguments to the relabelled target, charging exactly when the
original edge did (`split_sim`). An unsplit function is unchanged.
-/

set_option autoImplicit false

namespace Compilatrix.Lir

/-! ## The identity -/

/-- **A function simulates itself.** -/
theorem funcSim_refl (F : Func) : FuncSim F F Eq where
  params := rfl
  entry := rfl
  block := by
    intro l l' B hl hB
    subst hl
    refine ⟨B.term, B.cold, by rw [hB], ?_⟩
    have hedge : ∀ e : Edge, EdgeSim F F Eq l l e e := fun e _ _ => .inl ⟨rfl, rfl, rfl⟩
    cases ht : B.term with
    | jump e => exact ⟨e, rfl, hedge e⟩
    | br c w a b t f => exact ⟨t, f, rfl, hedge t, hedge f⟩
    | brOvf o x a b ok ovf => exact ⟨ok, ovf, rfl, hedge ok, hedge ovf⟩
    | _ => rfl

/-! ## Labels -/

theorem newLabels_get : ∀ (ss : List Nat) (label offset : Nat) (i : Nat), i < ss.length →
    (Func.newLabels ss label offset)[i]? = some (label + i + offset + (ss.take i).sum)
  | [], _, _, _, h => by simp at h
  | s :: ss, label, offset, 0, _ => by simp [Func.newLabels]
  | s :: ss, label, offset, i + 1, h => by
    simp only [Func.newLabels, List.getElem?_cons_succ, List.take_succ_cons, List.sum_cons]
    rw [newLabels_get ss (label + 1) (offset + s) i (by simpa using h)]
    congr 1
    omega

theorem newLabels_length : ∀ (ss : List Nat) (label offset : Nat), (Func.newLabels ss label offset).length = ss.length
  | [], _, _ => rfl
  | _ :: ss, label, offset => by simp [Func.newLabels, newLabels_length ss]

/-- The new label of block `i`. -/
def newLabel (splits : List Nat) (i : Nat) : Nat := i + (splits.take i).sum

theorem newLabel_succ (splits : List Nat) {i : Nat} (hi : i < splits.length) :
    newLabel splits (i + 1) = newLabel splits i + 1 + splits[i] := by
  unfold newLabel
  rw [List.take_succ, List.sum_append, List.getElem?_eq_getElem hi]
  simp
  omega

theorem newLabel_mono (splits : List Nat) {i j : Nat} (h : i ≤ j) : newLabel splits i + (j - i) ≤ newLabel splits j := by
  unfold newLabel
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  rw [List.take_add, List.sum_append]
  omega

theorem newLabel_le_iff (splits : List Nat) {i j : Nat} : newLabel splits i ≤ newLabel splits j ↔ i ≤ j := by
  constructor
  · intro h
    apply Nat.le_of_not_lt
    intro hlt
    have := newLabel_mono splits (Nat.le_of_lt hlt)
    omega
  · intro h
    have := newLabel_mono splits h
    omega

/-! ## Split edges -/

theorem splitEdges_spec (crit : Edge → Bool) (rel : Label → Label) (first : Label) :
    ∀ (es acc pend : List Edge),
      (Func.splitEdges crit rel first es acc pend).2 = pend ++ es.filter crit ∧
      ∃ outs, (Func.splitEdges crit rel first es acc pend).1 = acc ++ outs ∧ outs.length = es.length ∧
        ∀ (m : Nat) (hm : m < es.length), outs[m]? = some (if crit es[m] then
          { target := first + pend.length + ((es.take m).filter crit).length, args := [] }
          else { es[m] with target := rel es[m].target })
  | [], acc, pend => ⟨by simp [Func.splitEdges], [], by simp [Func.splitEdges], rfl, fun m hm => by simp at hm⟩
  | e :: es, acc, pend => by
    by_cases hc : crit e = true
    · simp only [Func.splitEdges, hc, ↓reduceIte]
      obtain ⟨h2, outs, h1, hlen, hget⟩ := splitEdges_spec crit rel first es
        (acc ++ [{ target := first + pend.length, args := [] }]) (pend ++ [e])
      refine ⟨by rw [h2]; simp [List.filter_cons, hc], { target := first + pend.length, args := [] } :: outs,
        by rw [h1]; simp, by simp [hlen], ?_⟩
      intro m hm
      cases m with
      | zero => simp [hc]
      | succ m =>
        simp only [List.getElem?_cons_succ, List.getElem_cons_succ, List.take_succ_cons, List.filter_cons, hc,
          ↓reduceIte, List.length_cons]
        rw [hget m (by simpa using hm)]
        simp only [List.length_append, List.length_singleton]
        have hm' : m < es.length := by simpa using hm
        by_cases hcm : crit es[m] = true
        · simp only [hcm, ↓reduceIte, Option.some.injEq, Edge.mk.injEq, and_true]
          ac_rfl
        · simp [hcm]
    · have hc' : crit e = false := by simpa using hc
      simp only [Func.splitEdges, hc', Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h2, outs, h1, hlen, hget⟩ := splitEdges_spec crit rel first es
        (acc ++ [{ e with target := rel e.target }]) pend
      refine ⟨by rw [h2]; simp [List.filter_cons, hc'], { e with target := rel e.target } :: outs,
        by rw [h1]; simp, by simp [hlen], ?_⟩
      intro m hm
      cases m with
      | zero => simp [hc']
      | succ m =>
        simp only [List.getElem?_cons_succ, List.getElem_cons_succ, List.take_succ_cons, List.filter_cons, hc',
          Bool.false_eq_true, ↓reduceIte, List.length_cons]
        exact hget m (by simpa using hm)

/-- The critical edge before which `k` critical edges come is the `k`-th
pending one. -/
theorem filter_getElem_count (crit : Edge → Bool) :
    ∀ (es : List Edge) (m : Nat) (hm : m < es.length), crit es[m] = true →
      (es.filter crit)[((es.take m).filter crit).length]? = some es[m] ∧
        ((es.take m).filter crit).length < (es.filter crit).length
  | [], _, hm, _ => by simp at hm
  | e :: es, 0, _, hc => by simp [List.filter_cons, show crit e = true from hc]
  | e :: es, m + 1, hm, hc => by
    obtain ⟨h1, h2⟩ := filter_getElem_count crit es m (by simpa using hm) hc
    cases he : crit e <;> simp [List.filter_cons, he, h2] <;> exact (List.getElem?_eq_some_iff.1 h1).2


/-! ## The emitted blocks -/

/-- The number of split blocks of a block. -/
abbrev splitsOf (crit : Block → Edge → Bool) (b : Block) : Nat := (b.term.edges.filter (crit b)).length

/-- A split block. -/
def hopOf (W : List Block) (rel : Label → Label) (b : Block) (e : Edge) : Block :=
  { term := .jump { e with target := rel e.target }, cold := b.cold || ((W[e.target]?).map (·.cold)).getD false }

/-- **Where `emit` puts each block and its split blocks.** -/
theorem emit_spec (W : List Block) (crit : Block → Edge → Bool) (rel : Label → Label) :
    ∀ (bs : List Block) (l₀ o₀ : Nat) (i : Nat) (hi : i < bs.length),
      (Func.splitCriticalEdges.emit W crit rel bs (Func.newLabels (bs.map (splitsOf crit)) l₀ o₀))[
          i + ((bs.map (splitsOf crit)).take i).sum]? =
        some { bs[i] with term := bs[i].term.setEdges (Func.splitEdges (crit bs[i]) rel
          (l₀ + o₀ + (i + ((bs.map (splitsOf crit)).take i).sum) + 1) bs[i].term.edges [] []).1 } ∧
      ∀ (k : Nat) (e : Edge), (Func.splitEdges (crit bs[i]) rel
          (l₀ + o₀ + (i + ((bs.map (splitsOf crit)).take i).sum) + 1) bs[i].term.edges [] []).2[k]? = some e →
        (Func.splitCriticalEdges.emit W crit rel bs (Func.newLabels (bs.map (splitsOf crit)) l₀ o₀))[
            i + ((bs.map (splitsOf crit)).take i).sum + 1 + k]? = some (hopOf W rel bs[i] e)
  | [], _, _, _, hi => by simp at hi
  | b :: bs, l₀, o₀, i, hi => by
    simp only [List.map_cons, Func.newLabels, Func.splitCriticalEdges.emit]
    obtain ⟨h2, -⟩ := splitEdges_spec (crit b) rel (l₀ + o₀ + 1) b.term.edges [] []
    have hsplit : (Func.splitEdges (crit b) rel (l₀ + o₀ + 1) b.term.edges [] []).2.length = splitsOf crit b := by
      rw [h2]; simp
    cases i with
    | zero =>
      simp only [List.take_zero, List.sum_nil, Nat.add_zero, Nat.zero_add, List.getElem_cons_zero]
      refine ⟨by simp, fun k e hke => ?_⟩
      rw [show 1 + k = k + 1 by omega, List.getElem?_append_left (by simp; exact (List.getElem?_eq_some_iff.1 hke).1),
        List.getElem?_cons_succ]
      simp only [List.getElem?_map, hke, Option.map_some]
      rfl
    | succ i =>
      have hi' : i < bs.length := by simpa using hi
      obtain ⟨ih₁, ih₂⟩ := emit_spec W crit rel bs (l₀ + 1) (o₀ + splitsOf crit b) i hi'
      simp only [List.getElem_cons_succ, List.take_succ_cons, List.sum_cons]
      have hfirst : l₀ + o₀ + (i + 1 + (splitsOf crit b + ((bs.map (splitsOf crit)).take i).sum)) + 1 =
          l₀ + 1 + (o₀ + splitsOf crit b) + (i + ((bs.map (splitsOf crit)).take i).sum) + 1 := by omega
      rw [hfirst]
      refine ⟨?_, fun k e hke => ?_⟩
      · rw [List.getElem?_append_right (by simp [hsplit]; omega)]
        simp only [List.length_cons, List.length_map, hsplit]
        rw [show i + 1 + (splitsOf crit b + ((bs.map (splitsOf crit)).take i).sum) - (splitsOf crit b + 1) =
          i + ((bs.map (splitsOf crit)).take i).sum by omega]
        exact ih₁
      · rw [List.getElem?_append_right (by simp [hsplit]; omega)]
        simp only [List.length_cons, List.length_map, hsplit]
        rw [show i + 1 + (splitsOf crit b + ((bs.map (splitsOf crit)).take i).sum) + 1 + k - (splitsOf crit b + 1) =
          i + ((bs.map (splitsOf crit)).take i).sum + 1 + k by omega]
        exact ih₂ k e hke


/-! ## The simulation -/

/-- The split function, for a criticality and a relabelling. -/
def splitWith (F : Func) (crit : Block → Edge → Bool) (rel : Label → Label) : Func :=
  { F with blocks := (Func.splitCriticalEdges.emit F.blocks.toList crit rel F.blocks.toList
      (Func.newLabels (F.blocks.toList.map (splitsOf crit)) 0 0)).toArray }

/-- Block `l` moves to its new label. -/
def Moved (F : Func) (crit : Block → Edge → Bool) (l l' : Label) : Prop :=
  l < F.blocks.size ∧ l' = newLabel (F.blocks.toList.map (splitsOf crit)) l

theorem split_core (F : Func) (crit : Block → Edge → Bool) (rel : Label → Label)
    (hrel : ∀ t < F.blocks.size, rel t = newLabel (F.blocks.toList.map (splitsOf crit)) t) (hne : 0 < F.blocks.size) :
    FuncSim F (splitWith F crit rel) (Moved F crit) where
  params := rfl
  entry := ⟨hne, by simp [newLabel]⟩
  block := by
    intro l l' B ⟨hl, hl'⟩ hB
    subst hl'
    have hBl : F.blocks.toList[l]? = some B := by simpa using hB
    have hBl' : F.blocks.toList[l] = B := by
      rw [List.getElem?_eq_some_iff] at hBl
      exact hBl.2
    have hlen : l < F.blocks.toList.length := by simpa using hl
    obtain ⟨hpos, hhop⟩ := emit_spec F.blocks.toList crit rel F.blocks.toList 0 0 l hlen
    simp only [hBl', Nat.zero_add] at hpos hhop
    have hnl : l + ((F.blocks.toList.map (splitsOf crit)).take l).sum = newLabel (F.blocks.toList.map (splitsOf crit)) l := rfl
    rw [hnl] at hpos hhop
    obtain ⟨hpend, outs, houts, holen, hget⟩ := splitEdges_spec (crit B) rel (newLabel (F.blocks.toList.map (splitsOf crit)) l + 1) B.term.edges [] []
    simp only [List.nil_append, List.length_nil, Nat.add_zero] at hpend houts hget
    have hsplit_l : (F.blocks.toList.map (splitsOf crit))[l]'(by simp; exact hl) = (B.term.edges.filter (crit B)).length := by
      simp [splitsOf, hBl']
    -- each edge of the block
    have hedge : ∀ (m : Nat) (hm : m < B.term.edges.length) (o : Edge), outs[m]? = some o →
        EdgeSim F (splitWith F crit rel) (Moved F crit) l (newLabel (F.blocks.toList.map (splitsOf crit)) l) B.term.edges[m] o := by
      intro m hm o ho TB hTB
      rw [hget m hm] at ho
      simp only [Option.some.injEq] at ho
      have ht : B.term.edges[m].target < F.blocks.size := (Array.getElem?_eq_some_iff.1 hTB).1
      have hL : Moved F crit B.term.edges[m].target (rel B.term.edges[m].target) := ⟨ht, hrel _ ht⟩
      split at ho
      · -- a critical edge: through its split block
        rename_i hc
        subst ho
        obtain ⟨hk, hklt⟩ := filter_getElem_count (crit B) B.term.edges m hm hc
        refine .inr ⟨rfl, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _), { B.term.edges[m] with target := rel B.term.edges[m].target },
          B.cold || ((F.blocks.toList[B.term.edges[m].target]?).map (·.cold)).getD false, ?_, rfl, hL, ?_⟩
        · show (Func.splitCriticalEdges.emit _ _ _ _ _).toArray[_]? = _
          rw [List.getElem?_toArray]
          rw [← hpend] at hk
          have := hhop _ _ hk
          rw [show newLabel (F.blocks.toList.map (splitsOf crit)) l + 1 + 0 + (List.filter (crit B) (List.take m B.term.edges)).length =
            newLabel (F.blocks.toList.map (splitsOf crit)) l + 1 + (List.filter (crit B) (List.take m B.term.edges)).length by omega]
          rw [this]
          rfl
        · simp only
          rw [hrel _ ht]
          have hsucc := newLabel_succ (F.blocks.toList.map (splitsOf crit)) (i := l) (by simp; exact hl)
          rw [hsplit_l] at hsucc
          by_cases htl : B.term.edges[m].target ≤ l
          · have := (newLabel_le_iff (F.blocks.toList.map (splitsOf crit))).2 htl
            simp only [htl, decide_true, decide_eq_true_eq]
            exact Nat.le_trans this (Nat.le_trans (Nat.le_succ _) (Nat.le_add_right _ _))
          · have := (newLabel_le_iff (F.blocks.toList.map (splitsOf crit))).2 (Nat.succ_le_of_lt (Nat.lt_of_not_le htl))
            simp only [htl, decide_false, decide_eq_false_iff_not, Nat.not_le]
            rw [hsucc] at this
            exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hklt _) this
      · -- an edge to its relabelled target
        subst ho
        refine .inl ⟨rfl, hL, ?_⟩
        simp only
        rw [hrel _ ht]
        exact decide_eq_decide.2 (newLabel_le_iff (F.blocks.toList.map (splitsOf crit)))
    have hedge' : ∀ (m : Nat) (e o : Edge), B.term.edges[m]? = some e → outs[m]? = some o →
        EdgeSim F (splitWith F crit rel) (Moved F crit) l (newLabel (F.blocks.toList.map (splitsOf crit)) l) e o := by
      intro m e o he ho
      obtain ⟨hm, rfl⟩ := List.getElem?_eq_some_iff.1 he
      exact hedge m hm o ho
    refine ⟨B.term.setEdges outs, B.cold, ?_, ?_⟩
    · show (Func.splitCriticalEdges.emit _ _ _ _ _).toArray[_]? = _
      rw [List.getElem?_toArray, hpos, houts]
    · cases ht : B.term with
      | jump e =>
        have hes : B.term.edges = [e] := by rw [ht]; rfl
        obtain ⟨o, ho⟩ : ∃ o, outs = [o] := by
          match outs, holen with
          | [o], _ => exact ⟨o, rfl⟩
          | [], h => rw [hes] at h; cases h
          | _ :: _ :: _, h => rw [hes] at h; simp at h
        subst ho
        refine ⟨o, by simp [Term.setEdges], ?_⟩
        exact hedge' 0 e o (by rw [hes]; rfl) rfl
      | br c w a b t f =>
        have hes : B.term.edges = [t, f] := by rw [ht]; rfl
        obtain ⟨o₁, o₂, ho⟩ : ∃ o₁ o₂, outs = [o₁, o₂] := by
          match outs, holen with
          | [o₁, o₂], _ => exact ⟨o₁, o₂, rfl⟩
          | [], h => rw [hes] at h; cases h
          | [_], h => rw [hes] at h; simp at h
          | _ :: _ :: _ :: _, h => rw [hes] at h; simp at h
        subst ho
        refine ⟨o₁, o₂, by simp [Term.setEdges], ?_, ?_⟩
        · exact hedge' 0 t o₁ (by rw [hes]; rfl) rfl
        · exact hedge' 1 f o₂ (by rw [hes]; rfl) rfl
      | brOvf op x a b ok ovf =>
        have hes : B.term.edges = [ok, ovf] := by rw [ht]; rfl
        obtain ⟨o₁, o₂, ho⟩ : ∃ o₁ o₂, outs = [o₁, o₂] := by
          match outs, holen with
          | [o₁, o₂], _ => exact ⟨o₁, o₂, rfl⟩
          | [], h => rw [hes] at h; cases h
          | [_], h => rw [hes] at h; simp at h
          | _ :: _ :: _ :: _, h => rw [hes] at h; simp at h
        subst ho
        refine ⟨o₁, o₂, by simp [Term.setEdges], ?_, ?_⟩
        · exact hedge' 0 ok o₁ (by rw [hes]; rfl) rfl
        · exact hedge' 1 ovf o₂ (by rw [hes]; rfl) rfl
      | ret as =>
        have : outs = [] := by rw [ht] at holen; simpa [Term.edges] using holen
        subst this; rfl
      | tail g as =>
        have : outs = [] := by rw [ht] at holen; simpa [Term.edges] using holen
        subst this; rfl
      | fail r =>
        have : outs = [] := by rw [ht] at holen; simpa [Term.edges] using holen
        subst this; rfl
      | trap =>
        have : outs = [] := by rw [ht] at holen; simpa [Term.edges] using holen
        subst this; rfl

/-- `splitCriticalEdges`'s criticality: an edge of a block with two or more
edges into a block with two or more predecessors. -/
def critOf (F : Func) : Block → Edge → Bool :=
  fun b e => decide (b.term.edges.length ≥ 2) &&
    decide (((List.range F.blocks.toList.length).map fun a =>
      (F.blocks.toList.flatMap fun x => x.term.succs).count a)[e.target]?.getD 0 ≥ 2)

/-- The label relation of `splitCriticalEdges F`. -/
def splitRel (F : Func) : Label → Label → Prop :=
  if ((F.blocks.toList.map (splitsOf (critOf F))).all fun x => x == 0) = true then Eq else Moved F (critOf F)

/-- **Splitting critical edges simulates the function.** -/
theorem split_sim (F : Func) : FuncSim F F.splitCriticalEdges (splitRel F) := by
  unfold Func.splitCriticalEdges splitRel
  dsimp only
  split
  · rename_i hall
    have h' : ((F.blocks.toList.map (splitsOf (critOf F))).all fun x => x == 0) = true := hall
    rw [if_pos h']
    exact funcSim_refl F
  · rename_i hall
    have h' : ¬ ((F.blocks.toList.map (splitsOf (critOf F))).all fun x => x == 0) = true := hall
    rw [if_neg h']
    refine split_core F (critOf F) _ (fun t ht => ?_) ?_
    · simp only [Array.length_toList, ht, ↓reduceIte]
      rw [newLabels_get _ 0 0 t (by simpa using ht)]
      simp only [Option.getD_some, Nat.zero_add, Nat.add_zero, newLabel]
      rfl
    · apply Nat.pos_of_ne_zero
      intro h0
      apply hall
      have : F.blocks.toList = [] := by simpa using h0
      simp [this]

end Compilatrix.Lir
