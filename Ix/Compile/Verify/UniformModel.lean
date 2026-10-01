import Ix.Compile.Verify.SharingExactCanon

/-!
# The uniform-width cost model

A pure model of the length the uniform-width optimizer minimises, over the
canonical DAG `p.dag` (with its telescope tables `Prep.ofDag`), a Share
width `w` and a set `avail` of stored terms (every stored term costs `w` at
every reference):

* `uCost t`: the cheapest standalone writing of `t` — a Share (`w`) if `t` is
  stored and that is shorter, otherwise inline;
* `uInl t`: the cheapest inline writing of `t` (the body of its entry):
  for a non-telescope head its own bytes plus its children's `uCost`; for a
  telescope `t = t₀, t₁, …, t_{l-1}` with natural tail `t_l`, the minimum
  over the inline prefix lengths `j`: the full spine ending in the tail
  (`tag4Size l + Σ side bytes + uCost t_l`), or, for `1 ≤ j < l` with `t_j`
  stored, the prefix ending in `Share(t_j)` (`tag4Size j + Σ_{k<j} side
  bytes + w`);
* `uniformCost`: `tag0Size |table| + Σ_{entries} uInl + Σ_{roots} uCost`.

This is the objective `L(S)` of `Ix.Sharing.Exact.Uniform`.
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Compile.Verify.SharingExact (CP NodeArity getElem!_eq_getElem setBang_getElem!
  child_eq_getElem cp_of_childrenPrecede)

/-! ## Counted loops -/

theorem foldRange_eq {σ : Type} (f : σ → Nat → σ) :
    ∀ (i k : Nat) (st : σ), foldRange f k i st = (List.range' k i).foldl f st := by
  intro i
  induction i with
  | zero => intro k st; rfl
  | succ i ih =>
    intro k st
    rw [foldRange, ih, List.range'_succ, List.foldl_cons]

theorem foldRange_zero {σ : Type} (f : σ → Nat → σ) (n : Nat) (st : σ) :
    foldRange f 0 n st = (List.range n).foldl f st := by
  rw [foldRange_eq, List.range_eq_range']

theorem foldl_range_succ {σ : Type} (f : σ → Nat → σ) (m : Nat) (st : σ) :
    (List.range (m + 1)).foldl f st = f ((List.range m).foldl f st) m := by
  rw [List.range_succ, List.foldl_append]
  rfl


/-! ## Well-formed DAGs -/

/-- The DAG checks of `optimizeUniformExpanded`: children precede their
parents and every node has its head's arity. -/
structure DagWF (dag : Dag) : Prop where
  precede : CP dag.nodes
  arity : NodeArity dag.nodes

theorem dag_node_eq {dag : Dag} {t : Nat} (ht : t < dag.size) : dag.node t = dag.nodes[t]! := by
  simp [Dag.node, Dag.size] at ht ⊢
  simp [ht]

theorem DagWF.child_lt {dag : Dag} (h : DagWF dag) {t c : Nat} (ht : t < dag.size)
    (hc : c ∈ (dag.node t).children) : c < t := by
  rw [dag_node_eq ht] at hc
  exact h.precede t ht c hc

theorem DagWF.childAt_lt {dag : Dag} (h : DagWF dag) {t k : Nat} (ht : t < dag.size)
    (hk : k < (dag.node t).head.arity) : (dag.node t).child k < t := by
  have ha := h.arity t ht
  rw [← dag_node_eq ht] at ha
  rw [child_eq_getElem _ k (by omega)]
  exact h.child_lt ht (Array.getElem_mem _)

/-! ## Telescope tables -/

theorem ofDag_family {dag : Dag} {t : Nat} (ht : t < dag.size) :
    (Prep.ofDag dag).family[t]! = (dag.node t).head.family := by
  simp only [Prep.ofDag, dag_node_eq ht]
  simp only [Dag.size] at ht
  simp [ht]

theorem ofDag_dag (dag : Dag) : (Prep.ofDag dag).dag = dag := rfl

/-- A telescope node continues its spine past itself. -/
def continues (p : Prep) (t : Nat) : Bool :=
  p.family[(p.dag.node t).spineNext]! == p.family[t]!

theorem spineNext_lt {dag : Dag} (h : DagWF dag) {t : Nat} (ht : t < dag.size)
    (hf : (dag.node t).head.family ≠ .none) : (dag.node t).spineNext < t := by
  unfold Node.spineNext
  cases hh : (dag.node t).head <;> simp only [hh, Head.family] at hf ⊢ <;>
    first | exact absurd rfl hf | exact h.childAt_lt ht (by simp [hh, Head.arity])

theorem sideChild_lt {dag : Dag} (h : DagWF dag) {t : Nat} (ht : t < dag.size)
    (hf : (dag.node t).head.family ≠ .none) : (dag.node t).sideChild < t := by
  unfold Node.sideChild
  cases hh : (dag.node t).head <;> simp only [hh, Head.family] at hf ⊢ <;>
    first | exact absurd rfl hf | exact h.childAt_lt ht (by simp [hh, Head.arity])

instance : LawfulBEq Family where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

instance : DecidableEq Family := fun a b =>
  if h : (a == b) = true then isTrue (eq_of_beq h)
  else isFalse (fun e => h (e ▸ beq_self_eq_true a))

theorem ofDag_spineLen (dag : Dag) :
    (Prep.ofDag dag).spineLen = (spineTables dag (Prep.ofDag dag).family).1 := rfl

theorem ofDag_tail (dag : Dag) :
    (Prep.ofDag dag).tail = (spineTables dag (Prep.ofDag dag).family).2 := rfl

/-- The recurrence of the telescope tables at `t`. -/
def SpineRow (dag : Dag) (family : Array Family) (len tail : Array Nat) (t : Nat) : Prop :=
  (family[t]! ≠ .none →
    len[t]! = (if family[(dag.node t).spineNext]! = family[t]! then
        len[(dag.node t).spineNext]! + 1 else 1) ∧
      tail[t]! = (if family[(dag.node t).spineNext]! = family[t]! then
        tail[(dag.node t).spineNext]! else (dag.node t).spineNext)) ∧
  (family[t]! = .none → len[t]! = 0 ∧ tail[t]! = 0)

theorem SpineRow.congr {dag : Dag} (h : DagWF dag) {family : Array Family}
    (hfam : ∀ t, t < dag.size → family[t]! = (dag.node t).head.family)
    {len tail len' tail' : Array Nat} {t : Nat} (ht : t < dag.size)
    (hlen : ∀ i, i ≤ t → len'[i]! = len[i]!) (htail : ∀ i, i ≤ t → tail'[i]! = tail[i]!)
    (hrow : SpineRow dag family len tail t) : SpineRow dag family len' tail' t := by
  obtain ⟨h1, h2⟩ := hrow
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · have hfm : (dag.node t).head.family ≠ .none := by rw [← hfam t ht]; exact hf
    have hn := spineNext_lt h ht hfm
    rw [hlen t (Nat.le_refl _), htail t (Nat.le_refl _), hlen (dag.node t).spineNext (by omega),
      htail (dag.node t).spineNext (by omega)]
    exact h1 hf
  · rw [hlen t (Nat.le_refl _), htail t (Nat.le_refl _)]
    exact h2 hf

theorem spineTables_spec {dag : Dag} (h : DagWF dag) {family : Array Family}
    (hfam : ∀ t, t < dag.size → family[t]! = (dag.node t).head.family) (t : Nat)
    (ht : t < dag.size) :
    SpineRow dag family (spineTables dag family).1 (spineTables dag family).2 t := by
  have z : ∀ i : Nat, (Array.replicate dag.size (0 : Nat))[i]! = 0 := by
    intro i; simp only [getElem!_def, Array.getElem?_replicate]
    by_cases hi : i < dag.size <;> simp [hi]
  have hinv : ∀ m, m ≤ dag.size →
      let st := (List.range m).foldl (spineStep dag family)
        (Array.replicate dag.size 0, Array.replicate dag.size 0)
      st.1.size = dag.size ∧ st.2.size = dag.size ∧
        (∀ t, t < m → SpineRow dag family st.1 st.2 t) ∧
        (∀ t, m ≤ t → st.1[t]! = 0 ∧ st.2[t]! = 0) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨by simp, by simp, fun _ h => absurd h (Nat.not_lt_zero _), fun t _ => ⟨z t, z t⟩⟩
    | succ m ih =>
      intro hm
      obtain ⟨hs1, hs2, hrow, hzero⟩ := ih (by omega)
      simp only at hs1 hs2 hrow hzero ⊢
      rw [foldl_range_succ]
      generalize (List.range m).foldl (spineStep dag family)
        (Array.replicate dag.size 0, Array.replicate dag.size 0) = st at hs1 hs2 hrow hzero
      obtain ⟨len, tl⟩ := st
      simp only at hs1 hs2 hrow hzero
      have hmn : m < dag.size := by omega
      by_cases hf : family[m]! = .none
      · have hstep : spineStep dag family (len, tl) m = (len, tl) := by
          unfold spineStep; simp [hf]
        rw [hstep]
        refine ⟨hs1, hs2, fun t ht => ?_, fun t ht => hzero t (by omega)⟩
        by_cases htm : t = m
        · subst htm
          exact ⟨fun h' => absurd hf h', fun _ => hzero _ (Nat.le_refl _)⟩
        · exact hrow t (by omega)
      · have hfm : (dag.node m).head.family ≠ .none := by rw [← hfam m hmn]; exact hf
        have hnxt := spineNext_lt h hmn hfm
        generalize hnx : (dag.node m).spineNext = nxt at hnxt
        let vlen := if family[nxt]! = family[m]! then len[nxt]! + 1 else 1
        let vtl := if family[nxt]! = family[m]! then tl[nxt]! else nxt
        have hstep : spineStep dag family (len, tl) m = (len.set! m vlen, tl.set! m vtl) := by
          unfold spineStep
          simp only [hf, hnx, vlen, vtl, bne_iff_ne, ne_eq, not_false_eq_true, if_true,
            beq_iff_eq]
          split <;> rfl
        rw [hstep]
        have keep : ∀ (v : Nat) (arr : Array Nat) (i : Nat), i ≠ m →
            (arr.set! m v)[i]! = arr[i]! := by
          intro v arr i hi
          rw [setBang_getElem!, if_neg (by intro h; exact hi h.1.symm)]
        have hat : ∀ (v : Nat) (arr : Array Nat), arr.size = dag.size →
            (arr.set! m v)[m]! = v := by
          intro v arr hs
          rw [setBang_getElem!, if_pos ⟨rfl, by omega⟩]
        refine ⟨by simp [hs1], by simp [hs2], fun t ht => ?_, fun t ht => ?_⟩
        · by_cases htm : t = m
          · subst htm
            refine ⟨fun _ => ?_, fun h' => absurd h' hf⟩
            rw [hnx, hat _ _ hs1, hat _ _ hs2, keep _ _ _ (by omega), keep _ _ _ (by omega)]
            exact ⟨rfl, rfl⟩
          · exact SpineRow.congr h hfam (by omega)
              (fun i hi => keep _ _ _ (by omega)) (fun i hi => keep _ _ _ (by omega))
              (hrow t (by omega))
        · rw [keep _ _ _ (by omega), keep _ _ _ (by omega)]
          exact hzero t (by omega)
  have := (hinv dag.size (Nat.le_refl _)).2.2.1 t ht
  unfold spineTables
  rw [foldRange_zero]
  exact this

/-! ## Well-formed telescope tables -/

/-- The facts about `Prep.ofDag dag` that the model uses. -/
structure PrepWF (p : Prep) : Prop where
  dag : DagWF p.dag
  family : ∀ t, t < p.dag.size → p.family[t]! = (p.dag.node t).head.family
  row : ∀ t, t < p.dag.size → SpineRow p.dag p.family p.spineLen p.tail t

theorem prepWF_ofDag {dag : Dag} (h : DagWF dag) : PrepWF (Prep.ofDag dag) where
  dag := h
  family := fun t ht => ofDag_family ht
  row := fun t ht => by
    rw [ofDag_spineLen, ofDag_tail]
    exact spineTables_spec h (fun t ht => ofDag_family ht) t ht

/-- The next node on the spine. -/
def snext (p : Prep) (t : Nat) : Nat := (p.dag.node t).spineNext

/-- `t` after `k` spine steps. -/
def spineAt (p : Prep) : Nat → Nat → Nat
  | t, 0 => t
  | t, k + 1 => spineAt p (snext p t) k

section Spine

variable {p : Prep} (hp : PrepWF p)
include hp

theorem PrepWF.snext_lt {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none) :
    snext p t < t :=
  spineNext_lt hp.dag ht (by rw [← hp.family t ht]; exact hf)

theorem PrepWF.sideChild_lt {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none) :
    (p.dag.node t).sideChild < t :=
  UniformModel.sideChild_lt hp.dag ht (by rw [← hp.family t ht]; exact hf)

/-- One step of the spine recurrence: either the spine continues into a node
of the same family, one shorter, with the same tail, or it ends with
`snext p t` as the tail. -/
theorem PrepWF.spine_step {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none) :
    (p.family[snext p t]! = p.family[t]! ∧ p.spineLen[t]! = p.spineLen[snext p t]! + 1 ∧
        p.tail[t]! = p.tail[snext p t]!) ∨
      (p.family[snext p t]! ≠ p.family[t]! ∧ p.spineLen[t]! = 1 ∧ p.tail[t]! = snext p t) := by
  obtain ⟨hrow, _⟩ := hp.row t ht
  obtain ⟨hl, htl⟩ := hrow hf
  unfold snext
  by_cases hs : p.family[(p.dag.node t).spineNext]! = p.family[t]!
  · rw [if_pos hs] at hl htl
    exact Or.inl ⟨hs, hl, htl⟩
  · rw [if_neg hs] at hl htl
    exact Or.inr ⟨hs, hl, htl⟩

/-- The spine of a telescope node: every node before the tail is a
telescope node of the same family, at or below `t`, with the remaining spine
length and the same tail; the tail is below `t` and of another family. -/
theorem PrepWF.spine :
    ∀ t, t < p.dag.size → p.family[t]! ≠ .none →
      1 ≤ p.spineLen[t]! ∧
      (∀ k, k < p.spineLen[t]! → spineAt p t k ≤ t ∧
        p.family[spineAt p t k]! = p.family[t]! ∧
        p.spineLen[spineAt p t k]! = p.spineLen[t]! - k ∧
        p.tail[spineAt p t k]! = p.tail[t]!) ∧
      spineAt p t p.spineLen[t]! = p.tail[t]! ∧ p.tail[t]! < t ∧
      p.family[p.tail[t]!]! ≠ p.family[t]! := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht hf
    have hlt := hp.snext_lt ht hf
    rcases hp.spine_step ht hf with ⟨hs, hl, htl⟩ | ⟨hs, hl, htl⟩
    · have hf' : p.family[snext p t]! ≠ .none := by rw [hs]; exact hf
      obtain ⟨h1, hk, hend, htlt, htf⟩ := ih _ hlt (by omega) hf'
      refine ⟨by omega, fun k hk' => ?_, ?_, by rw [htl]; omega, by rw [htl, ← hs]; exact htf⟩
      · cases k with
        | zero => exact ⟨Nat.le_refl _, rfl, by simp [spineAt], rfl⟩
        | succ k =>
          obtain ⟨a, b, c, d⟩ := hk k (by omega)
          refine ⟨by simp only [spineAt]; omega, by simp only [spineAt]; rw [b, hs], ?_, ?_⟩
          · simp only [spineAt]; rw [c]; omega
          · simp only [spineAt]; rw [d, htl]
      · rw [hl, htl]
        exact hend
    · refine ⟨by omega, fun k hk => ?_, ?_, by rw [htl]; exact hlt, by rw [htl]; exact hs⟩
      · have : k = 0 := by omega
        subst this
        exact ⟨Nat.le_refl _, rfl, by simp [spineAt], rfl⟩
      · rw [hl, htl]
        rfl

end Spine

/-! ## The model -/

/-- Contract byte plus the cost of the side child of telescope node `y`. -/
def sideCost (p : Prep) (cost : Nat → Nat) (y : Nat) : Nat :=
  (p.dag.node y).sideExtra + cost (p.dag.node y).sideChild

/-- Side bytes of the first `j` spine nodes from `t`. -/
def prefixSides (p : Prep) (cost : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | t, j + 1 => sideCost p cost t + prefixSides p cost (snext p t) j

/-- The full spine of `t` written inline, ending in its natural tail. -/
def naturalCost (p : Prep) (cost : Nat → Nat) (t : Nat) : Nat :=
  tag4Size p.spineLen[t]! + prefixSides p cost t p.spineLen[t]! + cost p.tail[t]!

/-- The internal cuts of telescope `t`: for `1 ≤ j < spineLen t` with the
`j`-th spine node stored, the prefix of `j` nodes ending in its Share. -/
def cutCosts (p : Prep) (w : Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t : Nat) :
    List Nat :=
  (List.range' 1 (p.spineLen[t]! - 1)).filterMap fun j =>
    if avail (spineAt p t j) then some (tag4Size j + prefixSides p cost t j + w) else none

/-- Cheapest inline writing of `t` given the costs of the terms below it. -/
def inlOf (p : Prep) (w : Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t : Nat) : Nat :=
  if p.family[t]! = .none then
    (p.dag.node t).children.foldl (fun acc c => acc + cost c) (p.dag.node t).head.ownBytes
  else
    (cutCosts p w avail cost t).foldl min (naturalCost p cost t)

/-- Cheapest standalone writing of `t`: its Share if stored and shorter. -/
def costOf (p : Prep) (w : Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t : Nat) : Nat :=
  if avail t then min (inlOf p w avail cost t) w else inlOf p w avail cost t

/-- The model values of every term, children first. -/
def uVals (p : Prep) (w : Nat) (avail : Nat → Bool) : Array Nat :=
  foldRange (fun arr t => arr.set! t (costOf p w avail (arr[·]!) t)) 0 p.dag.size
    (Array.replicate p.dag.size 0)

/-- `C_S(t)`: the cheapest standalone writing of `t` with the stored terms
`avail` at width `w`. -/
def uCost (p : Prep) (w : Nat) (avail : Nat → Bool) (t : Nat) : Nat :=
  (uVals p w avail)[t]!

/-- `inl_S(t)`: the cheapest inline writing of `t` (its entry body). -/
def uInl (p : Prep) (w : Nat) (avail : Nat → Bool) (t : Nat) : Nat :=
  inlOf p w avail (uCost p w avail) t

/-- The uniform-model length of a table and roots: the table count, every
entry body and every root. -/
def uniformCost (p : Prep) (w : Nat) (avail : Nat → Bool) (table roots : List Nat) : Nat :=
  tag0Size table.length + (table.map (uInl p w avail)).sum + (roots.map (uCost p w avail)).sum

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a List.mem_cons_self,
      filterMap_congr' (fun b hb => h b (List.mem_cons_of_mem _ hb))]

section Model


variable {p : Prep} (hp : PrepWF p)
include hp

theorem PrepWF.prefixSides_congr {f g : Nat → Nat} :
    ∀ (j t : Nat), t < p.dag.size → p.family[t]! ≠ .none → j ≤ p.spineLen[t]! →
      (∀ c, c < t → f c = g c) → prefixSides p f t j = prefixSides p g t j := by
  intro j
  induction j with
  | zero => intro _ _ _ _ _; rfl
  | succ j ih =>
    intro t ht hf hj hfg
    simp only [prefixSides, sideCost]
    rw [hfg _ (hp.sideChild_lt ht hf)]
    congr 1
    cases j with
    | zero => rfl
    | succ j =>
      have hlt := hp.snext_lt ht hf
      rcases hp.spine_step ht hf with ⟨hs, hl, _⟩ | ⟨_, hl, _⟩
      · exact ih _ (by omega) (by rw [hs]; exact hf) (by omega)
          (fun c hc => hfg c (by omega))
      · omega

theorem PrepWF.inlOf_congr {w : Nat} {avail : Nat → Bool} {f g : Nat → Nat} {t : Nat}
    (ht : t < p.dag.size) (hfg : ∀ c, c < t → f c = g c) :
    inlOf p w avail f t = inlOf p w avail g t := by
  unfold inlOf
  split
  · rw [← Array.foldl_toList, ← Array.foldl_toList]
    have hch : ∀ c ∈ (p.dag.node t).children.toList, f c = g c :=
      fun c hc => hfg c (hp.dag.child_lt ht (Array.mem_toList_iff.mp hc))
    generalize (p.dag.node t).children.toList = l at hch
    generalize (p.dag.node t).head.ownBytes = acc
    induction l generalizing acc with
    | nil => rfl
    | cons c l ih =>
      simp only [List.foldl_cons]
      rw [hch c List.mem_cons_self]
      exact ih (fun c hc => hch c (List.mem_cons_of_mem _ hc)) _
  · rename_i hf
    obtain ⟨_, _, _, htl, _⟩ := hp.spine t ht hf
    have hcuts : cutCosts p w avail f t = cutCosts p w avail g t := by
      unfold cutCosts
      apply filterMap_congr'
      intro j hj
      rw [List.mem_range'_1] at hj
      rw [hp.prefixSides_congr j t ht hf (by omega) hfg]
    unfold naturalCost
    rw [hcuts, hp.prefixSides_congr _ t ht hf (Nat.le_refl _) hfg, hfg _ htl]

theorem PrepWF.costOf_congr {w : Nat} {avail : Nat → Bool} {f g : Nat → Nat} {t : Nat}
    (ht : t < p.dag.size) (hfg : ∀ c, c < t → f c = g c) :
    costOf p w avail f t = costOf p w avail g t := by
  unfold costOf
  rw [hp.inlOf_congr ht hfg]

/-- The model recurrence: `C_S(t)` from the costs of the terms below `t`. -/
theorem PrepWF.uCost_eq (w : Nat) (avail : Nat → Bool) (t : Nat) (ht : t < p.dag.size) :
    uCost p w avail t = costOf p w avail (uCost p w avail) t := by
  let step := fun (arr : Array Nat) (t : Nat) => arr.set! t (costOf p w avail (arr[·]!) t)
  have hinv : ∀ m, m ≤ p.dag.size →
      ((List.range m).foldl step (Array.replicate p.dag.size 0)).size = p.dag.size ∧
      ∀ t, t < m → ((List.range m).foldl step (Array.replicate p.dag.size 0))[t]! =
        costOf p w avail (((List.range m).foldl step (Array.replicate p.dag.size 0))[·]!) t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      obtain ⟨hsize, hprev⟩ := ih (by omega)
      rw [foldl_range_succ]
      generalize hA : (List.range m).foldl step (Array.replicate p.dag.size 0) = A at hsize hprev
      have hsame : ∀ c, c < m → (step A m)[c]! = A[c]! := by
        intro c hc
        simp only [step, setBang_getElem!]
        rw [if_neg (by omega)]
      refine ⟨by simp [step, hsize], fun t' ht' => ?_⟩
      have hcongr : costOf p w avail ((step A m)[·]!) t' = costOf p w avail (A[·]!) t' :=
        hp.costOf_congr (by omega) fun c hc => hsame c (by omega)
      rw [hcongr]
      by_cases htm : t' = m
      · subst htm
        simp only [step, setBang_getElem!, hsize]
        rw [if_pos (by simp; omega)]
      · rw [hsame t' (by omega)]
        exact hprev t' (by omega)
  have := (hinv p.dag.size (Nat.le_refl _)).2 t ht
  unfold uCost uVals
  rw [foldRange_zero]
  exact this

end Model

/-! ## The executable evaluation computes the model -/

theorem spineAt_add (p : Prep) : ∀ (a b t : Nat), spineAt p t (a + b) = spineAt p (spineAt p t a) b := by
  intro a
  induction a with
  | zero => intro b t; simp [spineAt]
  | succ a ih =>
    intro b t
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [spineAt]
    rw [ih]

theorem prefixSides_add (p : Prep) (cost : Nat → Nat) :
    ∀ (a b t : Nat), prefixSides p cost t (a + b) =
      prefixSides p cost t a + prefixSides p cost (spineAt p t a) b := by
  intro a
  induction a with
  | zero => intro b t; simp [prefixSides, spineAt]
  | succ a ih =>
    intro b t
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [prefixSides, spineAt]
    rw [ih]
    omega

/-- The cost of the cut after `j` spine nodes of `t`. -/
def cutCost (p : Prep) (w : Nat) (cost : Nat → Nat) (t j : Nat) : Nat :=
  tag4Size j + prefixSides p cost t j + w

/-- The available cuts of `t` at spine positions `j, …, spineLen t - 1`. -/
def cutsFrom (p : Prep) (w : Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t j : Nat) :
    List Nat :=
  (List.range' j (p.spineLen[t]! - j)).filterMap fun j' =>
    if avail (spineAt p t j') then some (cutCost p w cost t j') else none

theorem cutCosts_eq (p : Prep) (w : Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t : Nat) :
    cutCosts p w avail cost t = cutsFrom p w avail cost t 1 := rfl

/-- `b` is the first stored spine node of `t` at a position in `[j, spineLen t)`. -/
def FirstAvail (p : Prep) (avail : Nat → Bool) (t j : Nat) : Option Nat → Prop
  | none => ∀ k, j ≤ k → k < p.spineLen[t]! → avail (spineAt p t k) = false
  | some u => ∃ k, j ≤ k ∧ k < p.spineLen[t]! ∧ u = spineAt p t k ∧ avail u = true ∧
      ∀ k', j ≤ k' → k' < k → avail (spineAt p t k') = false

theorem ite_lt_eq_min (a b : Nat) : (if a < b then a else b) = min b a := by
  rw [Nat.min_def]
  split <;> split <;> omega

theorem cutsFrom_split (p : Prep) (w : Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t j k : Nat)
    (hjk : j ≤ k) (hk : k < p.spineLen[t]!) (hav : avail (spineAt p t k) = true)
    (hnone : ∀ k', j ≤ k' → k' < k → avail (spineAt p t k') = false) :
    cutsFrom p w avail cost t j = cutCost p w cost t k :: cutsFrom p w avail cost t (k + 1) := by
  unfold cutsFrom
  rw [show p.spineLen[t]! - j = (k - j) + (1 + (p.spineLen[t]! - (k + 1))) by omega,
    ← List.range'_append_1, ← List.range'_append_1, List.filterMap_append,
    List.filterMap_append]
  have hpre : (List.range' j (k - j)).filterMap (fun j' =>
      if avail (spineAt p t j') then some (cutCost p w cost t j') else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro a ha
    rw [List.mem_range'_1] at ha
    rw [hnone a ha.1 (by omega)]
    rfl
  rw [hpre, show j + (k - j) = k by omega]
  simp [hav]

theorem cutsFrom_nil (p : Prep) (w : Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t j : Nat)
    (hnone : ∀ k, j ≤ k → k < p.spineLen[t]! → avail (spineAt p t k) = false) :
    cutsFrom p w avail cost t j = [] := by
  unfold cutsFrom
  rw [List.filterMap_eq_nil_iff]
  intro a ha
  rw [List.mem_range'_1] at ha
  rw [hnone a ha.1 (by omega)]
  rfl

theorem FirstAvail.shift {p : Prep} {avail : Nat → Bool} {t k : Nat} {b : Option Nat}
    (hlen : p.spineLen[spineAt p t k]! = p.spineLen[t]! - k)
    (h : FirstAvail p avail (spineAt p t k) 1 b) : FirstAvail p avail t (k + 1) b := by
  cases b with
  | none =>
    intro k' hk1 hk2
    have := h (k' - k) (by omega) (by omega)
    rwa [← spineAt_add, show k + (k' - k) = k' by omega] at this
  | some u =>
    obtain ⟨i, hi1, hi2, rfl, hav, hnone⟩ := h
    refine ⟨k + i, by omega, by omega, by rw [spineAt_add], hav, fun k' hk1 hk2 => ?_⟩
    have := hnone (k' - k) (by omega) (by omega)
    rwa [← spineAt_add, show k + (k' - k) = k' by omega] at this

/-- The internal-cut scan finds the cheapest available cut. -/
theorem PrepWF.cutScan_spec {p : Prep} (hp : PrepWF p) {w : Nat} {avail : Nat → Bool}
    {cost : Nat → Nat} (sides : Array Nat) (below : Array (Option Nat))
    (width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some w else none)
    {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none)
    (hsides : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
      sides[spineAt p t k]! = prefixSides p cost (spineAt p t k) (p.spineLen[t]! - k))
    (hbelow : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
      FirstAvail p avail (spineAt p t k) 1 below[spineAt p t k]!) :
    ∀ (fuel j : Nat) (cur : Option Nat) (best work : Nat), 1 ≤ j → j ≤ p.spineLen[t]! →
      p.spineLen[t]! - j ≤ fuel → FirstAvail p avail t j cur →
      (cutScan p.spineLen sides below width p.spineLen[t]!
          (prefixSides p cost t p.spineLen[t]!) fuel cur best work).1 =
        (cutsFrom p w avail cost t j).foldl min best := by
  obtain ⟨_, hk, _, _, _⟩ := hp.spine t ht hf
  intro fuel
  induction fuel with
  | zero =>
    intro j cur best work _ hj hfuel _
    have : cutsFrom p w avail cost t j = [] := by
      unfold cutsFrom
      rw [show p.spineLen[t]! - j = 0 by omega]
      rfl
    rw [this]
    rfl
  | succ fuel ih =>
    intro j cur best work hj1 hj hfuel hcur
    cases cur with
    | none =>
      rw [cutsFrom_nil p w avail cost t j hcur]
      rfl
    | some u =>
      obtain ⟨k, hjk, hkl, rfl, hav, hnone⟩ := hcur
      obtain ⟨_, _, hlenk, _⟩ := hk k hkl
      simp only [cutScan]
      rw [cutsFrom_split p w avail cost t j k hjk hkl hav hnone, List.foldl_cons,
        ite_lt_eq_min]
      have hcand : tag4Size (p.spineLen[t]! - p.spineLen[spineAt p t k]!) +
          (prefixSides p cost t p.spineLen[t]! - sides[spineAt p t k]!) +
          (widthOf width (spineAt p t k)).getD 0 = cutCost p w cost t k := by
        rw [hlenk, hsides k (by omega) hkl, hwidth, if_pos hav]
        have hsplit := prefixSides_add p cost k (p.spineLen[t]! - k) t
        rw [show k + (p.spineLen[t]! - k) = p.spineLen[t]! by omega] at hsplit
        unfold cutCost
        rw [show p.spineLen[t]! - (p.spineLen[t]! - k) = k by omega, hsplit]
        simp
      rw [hcand]
      exact ih (k + 1) _ _ _ (by omega) (by omega) (by omega)
        (FirstAvail.shift hlenk (hbelow k (by omega) hkl))

theorem foldl_add_congr {f g : Nat → Nat} (a : Nat) (arr : Array Nat)
    (h : ∀ c ∈ arr, f c = g c) :
    arr.foldl (fun acc c => acc + f c) a = arr.foldl (fun acc c => acc + g c) a := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  have h' : ∀ c ∈ arr.toList, f c = g c := fun c hc => h c (Array.mem_toList_iff.mp hc)
  generalize arr.toList = l at h'
  induction l generalizing a with
  | nil => rfl
  | cons c l ih =>
    simp only [List.foldl_cons]
    rw [h' c List.mem_cons_self]
    exact ih _ (fun c hc => h' c (List.mem_cons_of_mem _ hc))

/-- The evaluation entries of term `t` agree with the model. -/
def EvalRow (p : Prep) (w : Nat) (avail : Nat → Bool) (st : DictEval) (t : Nat) : Prop :=
  st.cost[t]! = uCost p w avail t ∧
    (p.family[t]! ≠ .none →
      st.sides[t]! = prefixSides p (uCost p w avail) t p.spineLen[t]! ∧
        FirstAvail p avail t 1 st.below[t]!)

theorem FirstAvail.unshift {p : Prep} {avail : Nat → Bool} {t j : Nat} {b : Option Nat}
    (hj : j < p.spineLen[t]!) (hav : avail (spineAt p t j) = false)
    (h : FirstAvail p avail t (j + 1) b) : FirstAvail p avail t j b := by
  cases b with
  | none =>
    intro k hk1 hk2
    by_cases hkj : k = j
    · subst hkj; exact hav
    · exact h k (by omega) hk2
  | some u =>
    obtain ⟨k, hk1, hk2, rfl, hu, hnone⟩ := h
    refine ⟨k, by omega, hk2, rfl, hu, fun k' hk'1 hk'2 => ?_⟩
    by_cases hkj : k' = j
    · subst hkj; exact hav
    · exact hnone k' (by omega) hk'2

theorem ite_beq_family (a b : Family) {α : Type} (x y : α) :
    (if (a == b) = true then x else y) = if a = b then x else y := by
  by_cases h : a = b
  · subst h; simp
  · have : (a == b) = false := by simpa using h
    simp [this, h]

theorem PrepWF.spineAt_lt {p : Prep} (hp : PrepWF p) {t k : Nat} (ht : t < p.dag.size)
    (hf : p.family[t]! ≠ .none) (hk1 : 1 ≤ k) (hk : k < p.spineLen[t]!) : spineAt p t k < t := by
  have hlt := hp.snext_lt ht hf
  rcases hp.spine_step ht hf with ⟨hs, hl, _⟩ | ⟨_, hl, _⟩
  · obtain ⟨_, hk', _, _, _⟩ := hp.spine (snext p t) (by omega) (by rw [hs]; exact hf)
    obtain ⟨hle, _⟩ := hk' (k - 1) (by omega)
    rw [show k = (k - 1) + 1 by omega]
    simp only [spineAt]
    omega
  · omega

/-- One evaluation step establishes the model row of the new term and keeps
the rows of the earlier ones. -/
theorem PrepWF.evalStep_spec {p : Prep} (hp : PrepWF p) {w : Nat} {avail : Nat → Bool}
    (width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some w else none)
    (affected : Array Bool) (st : DictEval) (m : Nat) (hm : m < p.dag.size)
    (haff : affected[m]! = true)
    (hsz : st.cost.size = p.dag.size ∧ st.sides.size = p.dag.size ∧
      st.below.size = p.dag.size)
    (hrows : ∀ t, t < m → EvalRow p w avail st t) :
    let st' := evalStep p.dag p.family p.spineLen p.tail width affected st m
    (st'.cost.size = p.dag.size ∧ st'.sides.size = p.dag.size ∧
      st'.below.size = p.dag.size) ∧ ∀ t, t < m + 1 → EvalRow p w avail st' t := by
  intro st'
  obtain ⟨hcs, hss, hbs⟩ := hsz
  have keepN : ∀ (v : Nat) (arr : Array Nat) (i : Nat), i ≠ m → (arr.set! m v)[i]! = arr[i]! := by
    intro v arr i hi
    rw [setBang_getElem!, if_neg (by intro h; exact hi h.1.symm)]
  have keepO : ∀ (v : Option Nat) (arr : Array (Option Nat)) (i : Nat), i ≠ m →
      (arr.set! m v)[i]! = arr[i]! := by
    intro v arr i hi
    rw [setBang_getElem!, if_neg (by intro h; exact hi h.1.symm)]
  have atN : ∀ (v : Nat) (arr : Array Nat), arr.size = p.dag.size → (arr.set! m v)[m]! = v := by
    intro v arr hs
    rw [setBang_getElem!, if_pos ⟨rfl, by omega⟩]
  have atO : ∀ (v : Option Nat) (arr : Array (Option Nat)), arr.size = p.dag.size →
      (arr.set! m v)[m]! = v := by
    intro v arr hs
    rw [setBang_getElem!, if_pos ⟨rfl, by omega⟩]
  have hcostLt : ∀ c, c < m → st.cost[c]! = uCost p w avail c := fun c hc => (hrows c hc).1
  have hcm := hp.uCost_eq w avail m hm
  have hcostOf : ∀ inl, inlOf p w avail (uCost p w avail) m = inl →
      (match widthOf width m with
        | some w => min inl w
        | none => inl) = uCost p w avail m := by
    intro inl hinl
    rw [hcm]
    unfold costOf
    rw [hinl, hwidth]
    by_cases ha : avail m = true <;> simp [ha]
  by_cases hf : p.family[m]! = .none
  · -- non-telescope
    have hfold : (p.dag.node m).children.foldl (fun acc c => acc + st.cost[c]!)
        (p.dag.node m).head.ownBytes = inlOf p w avail (uCost p w avail) m := by
      unfold inlOf
      rw [if_pos hf]
      exact foldl_add_congr _ _ fun c hc => hcostLt c (hp.dag.child_lt hm hc)
    have hst' : st'.cost = st.cost.set! m (uCost p w avail m) ∧ st'.sides = st.sides ∧
        st'.below = st.below := by
      simp only [st', evalStep, haff, if_true, hf, beq_self_eq_true]
      refine ⟨?_, trivial, trivial⟩
      congr 1
      exact hcostOf _ hfold.symm
    obtain ⟨hc', hs', hb'⟩ := hst'
    refine ⟨⟨by simp [hc', hcs], by rw [hs']; exact hss, by rw [hb']; exact hbs⟩,
      fun t ht => ?_⟩
    by_cases htm : t = m
    · subst htm
      exact ⟨by rw [hc', atN _ _ hcs], fun h => absurd hf h⟩
    · obtain ⟨h1, h2⟩ := hrows t (by omega)
      refine ⟨by rw [hc', keepN _ _ _ htm, h1], ?_⟩
      rw [hs', hb']
      exact h2
  · -- telescope
    obtain ⟨hl1, hk, hend, htl, _⟩ := hp.spine m hm hf
    have hlt := hp.snext_lt hm hf
    have hside := hp.sideChild_lt hm hf
    have hS : (p.dag.node m).sideExtra + st.cost[(p.dag.node m).sideChild]! +
        (if p.family[snext p m]! = p.family[m]! then st.sides[snext p m]! else 0) =
        prefixSides p (uCost p w avail) m p.spineLen[m]! := by
      rw [hcostLt _ hside]
      rcases hp.spine_step hm hf with ⟨hs, hl, _⟩ | ⟨hs, hl, _⟩
      · rw [if_pos hs, ((hrows _ hlt).2 (by rw [hs]; exact hf)).1, hl]
        rfl
      · rw [if_neg hs, hl]
        simp [prefixSides, sideCost]
    have hB : FirstAvail p avail m 1
        (if p.family[snext p m]! = p.family[m]! then
          (if (widthOf width (snext p m)).isSome then some (snext p m)
            else st.below[snext p m]!) else none) := by
      rcases hp.spine_step hm hf with ⟨hs, hl, _⟩ | ⟨hs, hl, _⟩
      · rw [if_pos hs, hwidth]
        have hn1 := (hp.spine (snext p m) (by omega) (by rw [hs]; exact hf)).1
        by_cases hav : avail (snext p m) = true
        · rw [if_pos hav]
          exact ⟨1, Nat.le_refl _, by omega, rfl, hav, fun k' h1 h2 => by omega⟩
        · rw [if_neg hav]
          simp only [Option.isSome_none, Bool.false_eq_true, if_false]
          have hrow := ((hrows _ hlt).2 (by rw [hs]; exact hf)).2
          have hlen1 : p.spineLen[spineAt p m 1]! = p.spineLen[m]! - 1 := by
            simp only [spineAt]; omega
          exact FirstAvail.unshift (by omega) (by simpa [spineAt] using hav)
            (FirstAvail.shift hlen1 hrow)
      · rw [if_neg hs]
        intro k h1 h2
        omega
    generalize hBdef : (if p.family[snext p m]! = p.family[m]! then
          (if (widthOf width (snext p m)).isSome then some (snext p m)
            else st.below[snext p m]!) else none) = B at hB
    generalize hSdef : prefixSides p (uCost p w avail) m p.spineLen[m]! = S at hS
    -- rows of the spine nodes below `m`
    have hspine : ∀ k, 1 ≤ k → k < p.spineLen[m]! →
        spineAt p m k ≠ m ∧ EvalRow p w avail st (spineAt p m k) ∧
          p.family[spineAt p m k]! ≠ .none ∧
          p.spineLen[spineAt p m k]! = p.spineLen[m]! - k := by
      intro k h1 h2
      have hlt' := hp.spineAt_lt hm hf h1 h2
      obtain ⟨_, hkf, hklen, _⟩ := hk k h2
      exact ⟨by omega, hrows _ hlt', by rw [hkf]; exact hf, hklen⟩
    have hsides : ∀ k, 1 ≤ k → k < p.spineLen[m]! →
        (st.sides.set! m S)[spineAt p m k]! =
          prefixSides p (uCost p w avail) (spineAt p m k) (p.spineLen[m]! - k) := by
      intro k h1 h2
      obtain ⟨hne, hrow, hfk, hlenk⟩ := hspine k h1 h2
      rw [keepN _ _ _ hne, (hrow.2 hfk).1, hlenk]
    have hbelow : ∀ k, 1 ≤ k → k < p.spineLen[m]! →
        FirstAvail p avail (spineAt p m k) 1 (st.below.set! m B)[spineAt p m k]! := by
      intro k h1 h2
      obtain ⟨hne, hrow, hfk, _⟩ := hspine k h1 h2
      rw [keepO _ _ _ hne]
      exact (hrow.2 hfk).2
    have hscan := hp.cutScan_spec (cost := uCost p w avail) (st.sides.set! m S)
      (st.below.set! m B) width hwidth hm hf hsides hbelow p.spineLen[m]! 1 B
      (tag4Size p.spineLen[m]! + S + st.cost[p.tail[m]!]!) st.work (Nat.le_refl _)
      (by omega) (by omega) hB
    rw [hSdef] at hscan
    have hinl : inlOf p w avail (uCost p w avail) m =
        (cutScan p.spineLen (st.sides.set! m S) (st.below.set! m B) width p.spineLen[m]! S
          p.spineLen[m]! B (tag4Size p.spineLen[m]! + S + st.cost[p.tail[m]!]!) st.work).1 := by
      rw [hscan, hcostLt _ htl]
      unfold inlOf
      rw [if_neg hf, cutCosts_eq, naturalCost, hSdef]
    have hst' : st'.cost = st.cost.set! m (uCost p w avail m) ∧
        st'.sides = st.sides.set! m S ∧ st'.below = st.below.set! m B := by
      simp only [st', evalStep, haff, if_true]
      have hfb : (p.family[m]! == Family.none) = false := by simpa using hf
      simp only [hfb, Bool.false_eq_true, if_false]
      simp only [ite_beq_family]
      rw [show (p.dag.node m).spineNext = snext p m from rfl, hS, hBdef]
      refine ⟨?_, rfl, rfl⟩
      congr 1
      exact hcostOf _ hinl
    obtain ⟨hc', hs', hb'⟩ := hst'
    refine ⟨⟨by simp [hc', hcs], by simp [hs', hss], by simp [hb', hbs]⟩, fun t ht => ?_⟩
    by_cases htm : t = m
    · subst htm
      refine ⟨by rw [hc', atN _ _ hcs], fun _ => ⟨?_, ?_⟩⟩
      · rw [hs', atN _ _ hss, hSdef]
      · rw [hb', atO _ _ hbs]
        exact hB
    · obtain ⟨h1, h2⟩ := hrows t (by omega)
      refine ⟨by rw [hc', keepN _ _ _ htm, h1], fun hft => ?_⟩
      obtain ⟨h3, h4⟩ := h2 hft
      exact ⟨by rw [hs', keepN _ _ _ htm, h3], by rw [hb', keepO _ _ _ htm]; exact h4⟩

theorem evalStep_size (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (width : Array (Option Nat)) (affected : Array Bool) (st : DictEval) (m : Nat) :
    (evalStep dag family spineLen tail width affected st m).cost.size = st.cost.size ∧
      (evalStep dag family spineLen tail width affected st m).sides.size = st.sides.size ∧
      (evalStep dag family spineLen tail width affected st m).below.size = st.below.size := by
  unfold evalStep
  split
  · simp only
    split
    · simp
    · simp
  · exact ⟨rfl, rfl, rfl⟩

theorem evalFrom_size (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (init : DictEval) (width : Array (Option Nat)) (affected : Array Bool) :
    (evalFrom dag family spineLen tail init width affected).cost.size = init.cost.size ∧
      (evalFrom dag family spineLen tail init width affected).sides.size = init.sides.size ∧
      (evalFrom dag family spineLen tail init width affected).below.size =
        init.below.size := by
  unfold evalFrom
  rw [foldRange_zero]
  generalize List.range dag.size = l
  suffices h : ∀ (st : DictEval),
      (l.foldl (evalStep dag family spineLen tail width affected) st).cost.size = st.cost.size ∧
      (l.foldl (evalStep dag family spineLen tail width affected) st).sides.size =
        st.sides.size ∧
      (l.foldl (evalStep dag family spineLen tail width affected) st).below.size =
        st.below.size from h _
  induction l with
  | nil => intro st; exact ⟨rfl, rfl, rfl⟩
  | cons x l ih =>
    intro st
    rw [List.foldl_cons]
    obtain ⟨a, b, c⟩ := ih (evalStep dag family spineLen tail width affected st x)
    obtain ⟨a', b', c'⟩ := evalStep_size dag family spineLen tail width affected st x
    exact ⟨a.trans a', b.trans b', c.trans c'⟩

theorem ofDag_empty_size (dag : Dag) :
    (Prep.ofDag dag).empty.cost.size = dag.size ∧ (Prep.ofDag dag).empty.sides.size = dag.size ∧
      (Prep.ofDag dag).empty.below.size = dag.size := by
  have := evalFrom_size dag (Prep.ofDag dag).family (Prep.ofDag dag).spineLen
    (Prep.ofDag dag).tail
    { cost := Array.replicate dag.size 0, sides := Array.replicate dag.size 0,
      below := Array.replicate dag.size none } (Array.replicate dag.size none)
    (Array.replicate dag.size true)
  simp only [Array.size_replicate] at this
  exact this

/-- The executable evaluation computes the model rows of every term. -/
theorem PrepWF.evalFrom_spec {p : Prep} (hp : PrepWF p) {w : Nat} {avail : Nat → Bool}
    (width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some w else none) (init : DictEval)
    (hsz : init.cost.size = p.dag.size ∧ init.sides.size = p.dag.size ∧
      init.below.size = p.dag.size)
    (affected : Array Bool) (haff : ∀ t, t < p.dag.size → affected[t]! = true) :
    ∀ t, t < p.dag.size →
      EvalRow p w avail (evalFrom p.dag p.family p.spineLen p.tail init width affected) t := by
  have hinv : ∀ m, m ≤ p.dag.size →
      let st := (List.range m).foldl (evalStep p.dag p.family p.spineLen p.tail width affected)
        { init with work := 0 }
      (st.cost.size = p.dag.size ∧ st.sides.size = p.dag.size ∧ st.below.size = p.dag.size) ∧
        ∀ t, t < m → EvalRow p w avail st t := by
    intro m
    induction m with
    | zero => intro _; exact ⟨hsz, fun t h => absurd h (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨hs, hrows⟩ := ih (by omega)
      simp only at hs hrows ⊢
      rw [foldl_range_succ]
      exact hp.evalStep_spec width hwidth affected _ m (by omega) (haff m (by omega)) hs hrows
  intro t ht
  unfold evalFrom
  rw [foldRange_zero]
  exact (hinv p.dag.size (Nat.le_refl _)).2 t ht

theorem uVals_size (p : Prep) (w : Nat) (avail : Nat → Bool) :
    (uVals p w avail).size = p.dag.size := by
  unfold uVals
  rw [foldRange_zero]
  generalize List.range p.dag.size = l
  suffices h : ∀ (arr : Array Nat),
      (l.foldl (fun arr t => arr.set! t (costOf p w avail (arr[·]!) t)) arr).size = arr.size by
    rw [h]; simp
  induction l with
  | nil => intro _; rfl
  | cons x l ih => intro arr; rw [List.foldl_cons, ih]; simp

theorem uCost_of_ge (p : Prep) (w : Nat) (avail : Nat → Bool) {t : Nat}
    (ht : p.dag.size ≤ t) : uCost p w avail t = 0 := by
  unfold uCost
  simp [uVals_size, show ¬ t < p.dag.size by omega]

/-- `Prep.evalAll` computes `C_S` for every term (`0` out of range on both
sides). -/
theorem PrepWF.evalAll_cost {p : Prep} (hp : PrepWF p) {w : Nat} {avail : Nat → Bool}
    (hempty : p.empty.cost.size = p.dag.size ∧ p.empty.sides.size = p.dag.size ∧
      p.empty.below.size = p.dag.size)
    (width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some w else none) (t : Nat) :
    (p.evalAll width).cost[t]! = uCost p w avail t := by
  by_cases ht : t < p.dag.size
  · exact (hp.evalFrom_spec width hwidth p.empty hempty _
      (fun t ht => by simp [ht]) t ht).1
  · have hs := (evalFrom_size p.dag p.family p.spineLen p.tail p.empty width
      (Array.replicate p.dag.size true)).1
    rw [uCost_of_ge p w avail (by omega)]
    unfold Prep.evalAll Prep.eval
    simp [hs, hempty.1, show ¬ t < p.dag.size by omega]

/-! ## The entry cost of materialization -/

theorem foldl_min_le : ∀ (xs : List Nat) (x y : Nat), y ∈ x :: xs → xs.foldl min x ≤ y := by
  intro xs
  induction xs with
  | nil => intro x y hy; simp at hy; subst hy; simp
  | cons z zs ih =>
    intro x y hy
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · have := ih (min y z) (min y z) List.mem_cons_self
      omega
    · rcases List.mem_cons.mp hy with rfl | hy
      · have := ih (min x y) (min x y) List.mem_cons_self
        omega
      · exact ih _ y (List.mem_cons_of_mem _ hy)

theorem foldl_min_mem : ∀ (xs : List Nat) (x : Nat), xs.foldl min x ∈ x :: xs := by
  intro xs
  induction xs with
  | nil => intro x; simp
  | cons z zs ih =>
    intro x
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp (ih (min x z)) with h | h
    · rw [h, Nat.min_def]
      split
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

/-- A list minimum: the element below every element. -/
theorem foldl_min_unique (xs : List Nat) (x c : Nat) (hc : c ∈ x :: xs)
    (hle : ∀ y ∈ x :: xs, c ≤ y) : xs.foldl min x = c := by
  have h1 := foldl_min_le xs x c hc
  have h2 := hle _ (foldl_min_mem xs x)
  omega

/-- The step of `pickOption`. -/
def pickStep (best : Option (Choice × Nat × ByteArray)) (o : Choice × Nat × ByteArray) :
    Option (Choice × Nat × ByteArray) :=
  match best with
  | none => some o
  | some b =>
    if o.2.1 < b.2.1 then some o
    else if o.2.1 == b.2.1 && compareBytes o.2.2 b.2.2 == .lt then some o
    else best

theorem pickStep_spec (init : Option (Choice × Nat × ByteArray)) (x : Choice × Nat × ByteArray) :
    ∃ b, pickStep init x = some b ∧ (b = x ∨ init = some b) ∧ b.2.1 ≤ x.2.1 ∧
      ∀ b', init = some b' → b.2.1 ≤ b'.2.1 := by
  cases init with
  | none => exact ⟨x, rfl, Or.inl rfl, Nat.le_refl _, fun _ h => by cases h⟩
  | some c =>
    unfold pickStep
    simp only
    by_cases hlt : x.2.1 < c.2.1
    · rw [if_pos hlt]
      exact ⟨x, rfl, Or.inl rfl, Nat.le_refl _, fun b' h => by cases h; omega⟩
    · rw [if_neg hlt]
      split
      · rename_i heq
        have hxc : x.2.1 = c.2.1 := by
          simp only [Bool.and_eq_true, beq_iff_eq] at heq
          exact heq.1
        exact ⟨x, rfl, Or.inl rfl, Nat.le_refl _, fun b' h => by cases h; omega⟩
      · exact ⟨c, rfl, Or.inr rfl, by omega, fun b' h => by cases h; omega⟩

theorem pick_foldl_spec :
    ∀ (l : List (Choice × Nat × ByteArray)) (init : Option (Choice × Nat × ByteArray))
      (o : Choice × Nat × ByteArray), l.foldl pickStep init = some o →
      (o ∈ l ∨ init = some o) ∧ (∀ x ∈ l, o.2.1 ≤ x.2.1) ∧
        ∀ b, init = some b → o.2.1 ≤ b.2.1 := by
  intro l
  induction l with
  | nil =>
    intro init o h
    refine ⟨Or.inr h, fun _ hx => (by cases hx), fun b hb => ?_⟩
    simp only [List.foldl_nil] at h
    rw [h] at hb
    cases hb
    omega
  | cons x xs ih =>
    intro init o h
    simp only [List.foldl_cons] at h
    obtain ⟨s, hs, hsx, hsle, hsinit⟩ := pickStep_spec init x
    rw [hs] at h
    obtain ⟨hmem, hle, hinit⟩ := ih _ o h
    have hos := hinit s rfl
    refine ⟨?_, fun y hy => ?_, fun b hb => ?_⟩
    · rcases hmem with hm | hm
      · exact Or.inl (List.mem_cons_of_mem _ hm)
      · cases hm
        rcases hsx with rfl | h'
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h'
    · rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact hle y hy
    · have := hsinit b hb
      omega

/-- `pickOption` returns a minimum-cost option. -/
theorem pickOption_min (opts : Array (Choice × Nat × ByteArray)) {ch : Choice} {c : Nat}
    (h : pickOption opts = some (ch, c)) :
    (∀ o ∈ opts.toList, c ≤ o.2.1) ∧ ∃ o ∈ opts.toList, o.2.1 = c := by
  unfold pickOption at h
  rw [← Array.foldl_toList] at h
  change (List.foldl pickStep none opts.toList).map _ = _ at h
  cases hr : List.foldl pickStep none opts.toList with
  | none => rw [hr] at h; cases h
  | some o =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    obtain ⟨hmem, hle, _⟩ := pick_foldl_spec opts.toList none o hr
    rcases hmem with hm | hm
    · exact ⟨hle, o, hm, rfl⟩
    · cases hm

theorem pickOption_isSome (opts : Array (Choice × Nat × ByteArray)) (h : opts.size ≠ 0) :
    ∃ ch c, pickOption opts = some (ch, c) := by
  unfold pickOption
  rw [← Array.foldl_toList]
  change ∃ ch c, (List.foldl pickStep none opts.toList).map _ = _
  cases hl : opts.toList with
  | nil => exact absurd (by simpa using congrArg List.length hl) h
  | cons x xs =>
    obtain ⟨s, hs, _⟩ := pickStep_spec none x
    simp only [List.foldl_cons, hs]
    suffices hh : ∀ (l : List (Choice × Nat × ByteArray)) (s : Choice × Nat × ByteArray),
        ∃ o, List.foldl pickStep (some s) l = some o by
      obtain ⟨o, ho⟩ := hh xs s
      rw [ho]
      exact ⟨o.1, o.2.1, rfl⟩
    intro l
    induction l with
    | nil => intro s; exact ⟨s, rfl⟩
    | cons y ys ih =>
      intro s
      obtain ⟨s', hs', _⟩ := pickStep_spec (some s) y
      simp only [List.foldl_cons, hs']
      exact ih s'

/-- The internal-cut options found by `Prep.cutOptions` are the available cuts. -/
theorem PrepWF.cutOptions_spec {p : Prep} (hp : PrepWF p) {w : Nat} {avail : Nat → Bool}
    (ev : DictEval) (index width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some w else none)
    (hindex : ∀ u, (index[u]?.getD none).isSome = avail u)
    {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none) (flag : UInt8)
    (hsides : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
      ev.sides[spineAt p t k]! =
        prefixSides p (uCost p w avail) (spineAt p t k) (p.spineLen[t]! - k))
    (hbelow : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
      FirstAvail p avail (spineAt p t k) 1 ev.below[spineAt p t k]!) :
    ∀ (fuel j : Nat) (cur : Option Nat) (opts : Array (Choice × Nat × ByteArray)),
      1 ≤ j → j ≤ p.spineLen[t]! → p.spineLen[t]! - j ≤ fuel → FirstAvail p avail t j cur →
      ∃ L : List (Choice × Nat × ByteArray),
        (p.cutOptions ev index width flag p.spineLen[t]!
          (prefixSides p (uCost p w avail) t p.spineLen[t]!) fuel cur opts).toList =
          opts.toList ++ L ∧
        L.map (·.2.1) = cutsFrom p w avail (uCost p w avail) t j ∧
        ∀ o ∈ L, o.1 ≠ .share := by
  obtain ⟨_, hk, _, _, _⟩ := hp.spine t ht hf
  intro fuel
  induction fuel with
  | zero =>
    intro j cur opts _ hj hfuel _
    refine ⟨[], by simp [Prep.cutOptions], ?_, fun o ho => by cases ho⟩
    unfold cutsFrom
    rw [show p.spineLen[t]! - j = 0 by omega]
    rfl
  | succ fuel ih =>
    intro j cur opts hj1 hj hfuel hcur
    cases cur with
    | none =>
      exact ⟨[], by simp [Prep.cutOptions], by rw [cutsFrom_nil p w avail _ t j hcur]; rfl,
        fun o ho => by cases ho⟩
    | some u =>
      obtain ⟨k, hjk, hkl, rfl, hav, hnone⟩ := hcur
      obtain ⟨_, _, hlenk, _⟩ := hk k hkl
      have hcand : tag4Size (p.spineLen[t]! - p.spineLen[spineAt p t k]!) +
          (prefixSides p (uCost p w avail) t p.spineLen[t]! - ev.sides[spineAt p t k]!) +
          (widthOf width (spineAt p t k)).getD 0 = cutCost p w (uCost p w avail) t k := by
        rw [hlenk, hsides k (by omega) hkl, hwidth, if_pos hav]
        have hsplit := prefixSides_add p (uCost p w avail) k (p.spineLen[t]! - k) t
        rw [show k + (p.spineLen[t]! - k) = p.spineLen[t]! by omega] at hsplit
        unfold cutCost
        rw [show p.spineLen[t]! - (p.spineLen[t]! - k) = k by omega, hsplit]
        simp
      have hidx : (index[spineAt p t k]?.getD none).isSome = true := by rw [hindex]; exact hav
      simp only [Prep.cutOptions, hidx, if_true]
      obtain ⟨L, hL, hcost, hnot⟩ := ih (k + 1) _ _ (by omega) (by omega) (by omega)
        (FirstAvail.shift hlenk (hbelow k (by omega) hkl))
      refine ⟨(Choice.cut (p.spineLen[t]! - p.spineLen[spineAt p t k]!),
        tag4Size (p.spineLen[t]! - p.spineLen[spineAt p t k]!) +
          (prefixSides p (uCost p w avail) t p.spineLen[t]! - ev.sides[spineAt p t k]!) +
          (widthOf width (spineAt p t k)).getD 0,
        tag4Bytes flag (p.spineLen[t]! - p.spineLen[spineAt p t k]!)) :: L, ?_, ?_, ?_⟩
      · rw [hL]; simp
      · rw [List.map_cons, hcost, cutsFrom_split p w avail _ t j k hjk hkl hav hnone]
        simp only
        rw [hcand]
      · intro o ho
        rcases List.mem_cons.mp ho with rfl | ho
        · simp
        · exact hnot o ho

theorem choice_ne_share {o : Choice × Nat × ByteArray} (h : o.1 ≠ .share) :
    (o.1 != .share) = true := by
  obtain ⟨c, _, _⟩ := o
  cases c with
  | share => exact absurd rfl h
  | inline => rfl
  | cut j => rfl

/-- The base options (`Share(t)` when `t` has an index) are removed by the
entry filter. -/
theorem share_opts_filter (index : Array (Option Nat)) (width : Array (Option Nat)) (t : Nat) :
    ((match index[t]?.getD none with
      | some i => #[(Choice.share, (widthOf width t).getD 0, tag4Bytes Ixon.Expr.FLAG_SHARE i)]
      | none => (#[] : Array (Choice × Nat × ByteArray))).toList.filter
        (fun (o : Choice × Nat × ByteArray) => o.1 != Choice.share)) = [] := by
  split <;> rfl

theorem pickOption_toList {A B : Array (Choice × Nat × ByteArray)} (h : A.toList = B.toList) :
    pickOption A = pickOption B := by
  have : A = B := Array.ext' h
  rw [this]

/-- The minimum-cost pick over `x :: L` has cost `min` of the costs. -/
theorem pickOption_cost (A : Array (Choice × Nat × ByteArray)) (x : Choice × Nat × ByteArray)
    (L : List (Choice × Nat × ByteArray)) (h : A.toList = x :: L) :
    ((pickOption A).map (·.2)).getD 0 = (L.map (·.2.1)).foldl min x.2.1 := by
  obtain ⟨ch, c, hpick⟩ := pickOption_isSome A (by
    intro h0; have := congrArg List.length h; simp [h0] at this)
  rw [hpick]
  obtain ⟨hle, o, ho, hoc⟩ := pickOption_min _ hpick
  rw [h] at hle ho
  simp only [Option.map_some, Option.getD_some]
  symm
  apply foldl_min_unique
  · rw [← hoc]
    rcases List.mem_cons.mp ho with rfl | ho
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem ho)
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hle _ List.mem_cons_self
    · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hy
      exact hle _ (List.mem_cons_of_mem _ ho')

/-- The entry cost used by `materializeDependent` is the model's inline cost. -/
theorem PrepWF.inlineCost_eq {p : Prep} (hp : PrepWF p)
    (hempty : p.empty.cost.size = p.dag.size ∧ p.empty.sides.size = p.dag.size ∧
      p.empty.below.size = p.dag.size)
    {w : Nat} {avail : Nat → Bool} (index width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some w else none)
    (hindex : ∀ u, (index[u]?.getD none).isSome = avail u) (t : Nat) (ht : t < p.dag.size) :
    p.inlineCost (p.evalAll width) index width t = uInl p w avail t := by
  have hrow : ∀ t', t' < p.dag.size → EvalRow p w avail (p.evalAll width) t' :=
    hp.evalFrom_spec width hwidth p.empty hempty _ (fun t ht => by simp [ht])
  have hcost : ∀ c, c < p.dag.size → (p.evalAll width).cost[c]! = uCost p w avail c :=
    fun c hc => (hrow c hc).1
  let base : Array (Choice × Nat × ByteArray) :=
    match index[t]?.getD none with
    | some i => #[(Choice.share, (widthOf width t).getD 0, tag4Bytes Ixon.Expr.FLAG_SHARE i)]
    | none => #[]
  have hbase : base.toList.filter (fun o => o.1 != Choice.share) = [] :=
    share_opts_filter index width t
  unfold Prep.inlineCost Prep.options uInl
  by_cases hf : p.family[t]! = .none
  · have hfb : (p.family[t]! == Family.none) = true := by simp [hf]
    simp only [hfb, if_true]
    have hfold : (p.dag.node t).children.foldl (fun acc c => acc + (p.evalAll width).cost[c]!)
        (p.dag.node t).head.ownBytes = inlOf p w avail (uCost p w avail) t := by
      unfold inlOf
      rw [if_pos hf]
      exact foldl_add_congr _ _ fun c hc =>
        hcost c (by have := hp.dag.child_lt ht hc; omega)
    rw [pickOption_cost _ (Choice.inline, inlOf p w avail (uCost p w avail) t,
      Ixon.runPut (Ixon.putTagN 4 (p.dag.node t).head.flag (p.dag.node t).head.tag4Field)) []]
    · rfl
    · rw [Array.toList_filter, Array.toList_push, List.filter_append]
      change base.toList.filter _ ++ _ = _
      rw [hbase, hfold]
      rfl
  · have hfb : (p.family[t]! == Family.none) = false := by simpa using hf
    simp only [hfb, Bool.false_eq_true, if_false]
    obtain ⟨hs, hb⟩ := (hrow t ht).2 hf
    obtain ⟨_, hk, _, htl, _⟩ := hp.spine t ht hf
    have hspine : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
        EvalRow p w avail (p.evalAll width) (spineAt p t k) ∧
          p.family[spineAt p t k]! ≠ .none ∧
          p.spineLen[spineAt p t k]! = p.spineLen[t]! - k := by
      intro k h1 h2
      have hlt' := hp.spineAt_lt ht hf h1 h2
      obtain ⟨_, hkf, hklen, _⟩ := hk k h2
      exact ⟨hrow _ (by omega), by rw [hkf]; exact hf, hklen⟩
    let natOpt : Choice × Nat × ByteArray :=
      (Choice.cut p.spineLen[t]!,
        tag4Size p.spineLen[t]! + (p.evalAll width).sides[t]! +
          (p.evalAll width).cost[p.tail[t]!]!,
        tag4Bytes (p.dag.node t).head.flag p.spineLen[t]!)
    obtain ⟨L, hL, hLcost, hLnot⟩ := hp.cutOptions_spec (p.evalAll width) index width hwidth
      hindex ht hf (p.dag.node t).head.flag
      (fun k h1 h2 => by
        obtain ⟨hr, hfk, hlenk⟩ := hspine k h1 h2
        rw [(hr.2 hfk).1, hlenk])
      (fun k h1 h2 => by
        obtain ⟨hr, hfk, _⟩ := hspine k h1 h2
        exact (hr.2 hfk).2)
      p.spineLen[t]! 1 _ (base.push natOpt) (Nat.le_refl _) (by omega) (by omega) hb
    rw [← hs] at hL
    have hnat : natOpt.2.1 = naturalCost p (uCost p w avail) t := by
      simp only [natOpt]
      rw [hs, hcost _ (by omega)]
      rfl
    rw [pickOption_cost _ natOpt L]
    · rw [hLcost, hnat]
      unfold inlOf
      rw [if_neg hf, cutCosts_eq]
    · simp only [base, natOpt] at hL hbase
      rw [Array.toList_filter]
      refine (congrArg (List.filter _) hL).trans ?_
      rw [Array.toList_push, List.filter_append, List.filter_append,
        hbase, List.filter_eq_self.mpr (fun o ho => choice_ne_share (hLnot o ho))]
      rfl

end Ix.Compile.Verify.UniformModel
