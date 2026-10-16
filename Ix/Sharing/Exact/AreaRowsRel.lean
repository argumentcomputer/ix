/-
  The area search computes the specification's search, part 1: a dictionary
  evaluation and a truncated evaluation that satisfy their row recurrences at
  every term agree on every cost and every inline cost, provided every opaque
  term passes the opacity test on its truncated row (`rows_rel`). The relation
  is proved by induction on term IDs along the telescope spines: below an
  opaque spine node `c` the dictionary's options are dominated by the cut at
  `c`, which is the truncated natural ending.
-/
module

public import Ix.Sharing.Exact.AreaSearch
import all Ix.Sharing.Exact.Basic
import all Ix.Sharing.Exact.Dag
import all Ix.Sharing.Exact.Dictionary
import all Ix.Sharing.Exact.UniformSearch
import all Ix.Sharing.Exact.UniformSearchLocal
import all Ix.Sharing.Exact.AreaSearch

public section

namespace Ix.Sharing.Exact.AreaProof

open Ix.Sharing.Exact
open Ix.Sharing.Exact.LocalSearch (node_children_lt setBang_read)

/-! ## Counted loops -/

theorem foldRange_list {σ : Type} (f : σ → Nat → σ) :
    ∀ (i k : Nat) (st : σ), foldRange f k i st = (List.range' k i).foldl f st := by
  intro i
  induction i with
  | zero => intro k st; rfl
  | succ i ih =>
    intro k st
    rw [foldRange, ih, List.range'_succ, List.foldl_cons]

theorem foldRange_range {σ : Type} (f : σ → Nat → σ) (n : Nat) (st : σ) :
    foldRange f 0 n st = (List.range n).foldl f st := by
  rw [foldRange_list, List.range_eq_range']

theorem foldl_range_succ {σ : Type} (f : σ → Nat → σ) (m : Nat) (st : σ) :
    (List.range (m + 1)).foldl f st = f ((List.range m).foldl f st) m := by
  rw [List.range_succ, List.foldl_append]
  rfl

/-! ## The DAG -/

/-- The DAG checks the area search relies on: children before their parents,
and every node with its head's arity. -/
structure DagOK (dag : Dag) : Prop where
  cp : childrenPrecede dag.nodes = true
  arity : ∀ t, t < dag.size → (dag.node t).children.size = (dag.node t).head.arity

theorem DagOK.child_lt {dag : Dag} (h : DagOK dag) {t c : Nat} (ht : t < dag.size)
    (hc : c ∈ (dag.node t).children) : c < t :=
  node_children_lt h.cp ht hc

theorem child_mem_of_lt (n : Node) {k : Nat} (hk : k < n.children.size) :
    n.child k ∈ n.children := by
  simp [Node.child, Array.getD_eq_getD_getElem?, hk]

theorem tele_arity {n : Node} (hf : n.head.family ≠ .none) : n.head.arity = 2 := by
  cases h : n.head <;> simp_all [Head.family, Head.arity]

theorem spineNext_mem {n : Node} (hf : n.head.family ≠ .none)
    (ha : n.children.size = n.head.arity) : n.spineNext ∈ n.children := by
  have h2 := tele_arity hf
  unfold Node.spineNext
  split
  · exact child_mem_of_lt n (by omega)
  · exact child_mem_of_lt n (by omega)

theorem sideChild_mem {n : Node} (hf : n.head.family ≠ .none)
    (ha : n.children.size = n.head.arity) : n.sideChild ∈ n.children := by
  have h2 := tele_arity hf
  unfold Node.sideChild
  split
  · exact child_mem_of_lt n (by omega)
  · exact child_mem_of_lt n (by omega)

theorem DagOK.spineNext_lt {dag : Dag} (h : DagOK dag) {t : Nat} (ht : t < dag.size)
    (hf : (dag.node t).head.family ≠ .none) : (dag.node t).spineNext < t :=
  h.child_lt ht (spineNext_mem hf (h.arity t ht))

theorem DagOK.sideChild_lt {dag : Dag} (h : DagOK dag) {t : Nat} (ht : t < dag.size)
    (hf : (dag.node t).head.family ≠ .none) : (dag.node t).sideChild < t :=
  h.child_lt ht (sideChild_mem hf (h.arity t ht))

theorem ofDag_family {dag : Dag} {t : Nat} (ht : t < dag.size) :
    (Prep.ofDag dag).family[t]! = (dag.node t).head.family := by
  have hn : dag.node t = dag.nodes[t]'(by simpa [Dag.size] using ht) := by
    unfold Dag.node; simp only [Dag.size] at ht; simp [ht]
  simp only [Prep.ofDag, hn]
  simp only [Dag.size] at ht
  simp [ht]

/-- Decidable equality of families (scoped: the proof modules open it). -/
scoped instance instDecEqFamily : DecidableEq Family := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (fun h => Family.noConfusion h)

theorem family_beq {a b : Family} : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

/-- `==` on families is equality (scoped). -/
scoped instance instLawfulBEqFamily : LawfulBEq Family where
  eq_of_beq h := family_beq.mp h
  rfl := family_beq.mpr rfl

/-! ## Spine tables

`SpineRow` is the recurrence of a pair of spine tables at a telescope node:
the length and tail continue into the spine successor while it has the same
family and `cont` holds there. The tables of `Prep.ofDag` continue
unconditionally; the truncated tables stop at opaque terms. -/

/-- The recurrence of spine tables at `t`. -/
def SpineRow (dag : Dag) (family : Array Family) (cont : Nat → Bool) (len tail : Array Nat)
    (t : Nat) : Prop :=
  family[t]! ≠ .none →
    len[t]! = (if family[(dag.node t).spineNext]! = family[t]! ∧ cont (dag.node t).spineNext = true
        then len[(dag.node t).spineNext]! + 1 else 1) ∧
      tail[t]! = (if family[(dag.node t).spineNext]! = family[t]! ∧
          cont (dag.node t).spineNext = true then
        tail[(dag.node t).spineNext]! else (dag.node t).spineNext)

theorem SpineRow.congr {dag : Dag} (h : DagOK dag) {family : Array Family}
    (hfam : ∀ t, t < dag.size → family[t]! = (dag.node t).head.family) {cont : Nat → Bool}
    {len tail len' tail' : Array Nat} {t : Nat} (ht : t < dag.size)
    (hlen : ∀ i, i ≤ t → len'[i]! = len[i]!) (htail : ∀ i, i ≤ t → tail'[i]! = tail[i]!)
    (hrow : SpineRow dag family cont len tail t) : SpineRow dag family cont len' tail' t := by
  intro hf
  have hfm : (dag.node t).head.family ≠ .none := by rw [← hfam t ht]; exact hf
  have hn := h.spineNext_lt ht hfm
  rw [hlen t (Nat.le_refl _), htail t (Nat.le_refl _), hlen _ (by omega), htail _ (by omega)]
  exact hrow hf

theorem setBang_ne {α : Type} [Inhabited α] (a : Array α) {i j : Nat} (v : α) (h : j ≠ i) :
    (a.set! i v)[j]! = a[j]! := by
  rw [getElem!_setBang, ite_eq_right (fun h' => h h'.1)]

theorem setBang_self {α : Type} [Inhabited α] (a : Array α) {i : Nat} (v : α) (h : i < a.size) :
    (a.set! i v)[i]! = v := by
  rw [getElem!_setBang, ite_eq_left ⟨rfl, h⟩]

/-- The spine tables of a fold whose step at `t` writes the recurrence. -/
theorem spineFold_rows {dag : Dag} (h : DagOK dag) {family : Array Family}
    (hfam : ∀ t, t < dag.size → family[t]! = (dag.node t).head.family) (cont : Nat → Bool)
    (step : Array Nat × Array Nat → Nat → Array Nat × Array Nat)
    (hstep : ∀ (len tl : Array Nat) (t : Nat), t < dag.size →
      step (len, tl) t = if family[t]! ≠ .none then
        (if family[(dag.node t).spineNext]! = family[t]! ∧ cont (dag.node t).spineNext = true then
          (len.set! t (len[(dag.node t).spineNext]! + 1), tl.set! t tl[(dag.node t).spineNext]!)
        else (len.set! t 1, tl.set! t (dag.node t).spineNext))
      else (len, tl)) :
    ∀ t, t < dag.size → SpineRow dag family cont
      (foldRange step 0 dag.size (Array.replicate dag.size 0, Array.replicate dag.size 0)).1
      (foldRange step 0 dag.size (Array.replicate dag.size 0, Array.replicate dag.size 0)).2 t := by
  have hinv : ∀ m, m ≤ dag.size →
      let st := (List.range m).foldl step (Array.replicate dag.size 0, Array.replicate dag.size 0)
      st.1.size = dag.size ∧ st.2.size = dag.size ∧
        (∀ t, t < m → SpineRow dag family cont st.1 st.2 t) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨by simp, by simp, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨hs1, hs2, hrow⟩ := ih (by omega)
      simp only at hs1 hs2 hrow ⊢
      rw [foldl_range_succ]
      generalize (List.range m).foldl step
        (Array.replicate dag.size 0, Array.replicate dag.size 0) = st at hs1 hs2 hrow
      obtain ⟨len, tl⟩ := st
      simp only at hs1 hs2 hrow
      have hmn : m < dag.size := by omega
      rw [hstep len tl m hmn]
      by_cases hf : family[m]! = .none
      · simp only [hf, ne_eq, not_true_eq_false, ite_false]
        refine ⟨hs1, hs2, fun t ht => ?_⟩
        by_cases htm : t = m
        · subst htm; intro h'; exact absurd hf h'
        · exact hrow t (by omega)
      · simp only [hf, ne_eq, not_false_eq_true, ite_true]
        have hfm : (dag.node m).head.family ≠ .none := by rw [← hfam m hmn]; exact hf
        have hnxt := h.spineNext_lt hmn hfm
        split
        · rename_i hc
          refine ⟨by simp [hs1], by simp [hs2], fun t ht => ?_⟩
          by_cases htm : t = m
          · subst htm
            intro _
            rw [setBang_self _ _ (by omega), setBang_self _ _ (by omega),
              setBang_ne _ _ (by omega), setBang_ne _ _ (by omega), ite_eq_left hc, ite_eq_left hc]
            exact ⟨rfl, rfl⟩
          · exact SpineRow.congr h hfam (by omega)
              (fun i hi => setBang_ne _ _ (by omega)) (fun i hi => setBang_ne _ _ (by omega))
              (hrow t (by omega))
        · rename_i hc
          refine ⟨by simp [hs1], by simp [hs2], fun t ht => ?_⟩
          by_cases htm : t = m
          · subst htm
            intro _
            rw [setBang_self _ _ (by omega), setBang_self _ _ (by omega), ite_eq_right hc, ite_eq_right hc]
            exact ⟨rfl, rfl⟩
          · exact SpineRow.congr h hfam (by omega)
              (fun i hi => setBang_ne _ _ (by omega)) (fun i hi => setBang_ne _ _ (by omega))
              (hrow t (by omega))
  intro t ht
  rw [foldRange_range]
  exact (hinv dag.size (Nat.le_refl _)).2.2 t ht

theorem spineTables_rows {dag : Dag} (h : DagOK dag) {family : Array Family}
    (hfam : ∀ t, t < dag.size → family[t]! = (dag.node t).head.family) :
    ∀ t, t < dag.size → SpineRow dag family (fun _ => true)
      (spineTables dag family).1 (spineTables dag family).2 t := by
  unfold spineTables
  refine spineFold_rows h hfam (fun _ => true) (spineStep dag family) ?_
  intro len tl t _
  unfold spineStep
  by_cases hf : family[t]! = .none
  · simp [hf]
  · by_cases hs : family[(dag.node t).spineNext]! = family[t]!
    · simp [hf, hs]
    · simp [hf, hs]

theorem tSpineTables_rows {dag : Dag} (h : DagOK dag) {family : Array Family}
    (hfam : ∀ t, t < dag.size → family[t]! = (dag.node t).head.family) (opaq : Array Bool) :
    ∀ t, t < dag.size → SpineRow dag family (fun u => !opaq[u]!)
      (tSpineTables dag family opaq).1 (tSpineTables dag family opaq).2 t := by
  unfold tSpineTables
  refine spineFold_rows h hfam (fun u => !opaq[u]!) (tSpineStep dag family opaq) ?_
  intro len tl t _
  unfold tSpineStep
  by_cases hf : family[t]! = .none
  · simp [hf]
  · by_cases hs : family[(dag.node t).spineNext]! = family[t]!
    · simp [hf, hs]
    · simp [hf, hs]

/-! ## Truncated spines

Below, `p` is a `Prep` over a checked DAG whose family table is the heads'
families and whose spine tables satisfy their recurrence, and `tLn`, `tTl`
are spine tables that stop at the terms of `opaq`. A truncated spine is at most
as long as the full one; when it is shorter it stops at an opaque term of the
same family (`stopOf`), whose own full spine makes up the difference. -/

section Spines

variable {p : Prep} (h : DagOK p.dag)
  (hfam : ∀ t, t < p.dag.size → p.family[t]! = (p.dag.node t).head.family)
  (hS : ∀ t, t < p.dag.size → SpineRow p.dag p.family (fun _ => true) p.spineLen p.tail t)
  {opaq : Array Bool} {tLn tTl : Array Nat}
  (hT : ∀ t, t < p.dag.size → SpineRow p.dag p.family (fun u => !opaq[u]!) tLn tTl t)

/-- The spine successor. -/
abbrev nx (p : Prep) (t : Nat) : Nat := (p.dag.node t).spineNext

/-- The opaque term where the truncated spine of `t` stops, if it stops before
the full spine ends. -/
def stopOf (p : Prep) (tLn tTl : Array Nat) (t : Nat) : Option Nat :=
  if tLn[t]! < p.spineLen[t]! then some tTl[t]! else none

include h hfam in
theorem nx_lt {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none) : nx p t < t :=
  h.spineNext_lt ht (by rw [← hfam t ht]; exact hf)

include h hfam in
theorem side_lt {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none) :
    (p.dag.node t).sideChild < t :=
  h.sideChild_lt ht (by rw [← hfam t ht]; exact hf)

theorem spineRow_full {t : Nat} (hr : SpineRow p.dag p.family (fun _ => true) p.spineLen p.tail t)
    (hf : p.family[t]! ≠ .none) :
    p.spineLen[t]! = (if p.family[nx p t]! = p.family[t]! then p.spineLen[nx p t]! + 1 else 1) ∧
      p.tail[t]! = (if p.family[nx p t]! = p.family[t]! then p.tail[nx p t]! else nx p t) := by
  obtain ⟨a, b⟩ := hr hf
  simp only [and_true] at a b
  exact ⟨a, b⟩

theorem spineRow_trunc {t : Nat} (hr : SpineRow p.dag p.family (fun u => !opaq[u]!) tLn tTl t)
    (hf : p.family[t]! ≠ .none) :
    tLn[t]! = (if p.family[nx p t]! = p.family[t]! ∧ opaq[nx p t]! = false then tLn[nx p t]! + 1
      else 1) ∧
      tTl[t]! = (if p.family[nx p t]! = p.family[t]! ∧ opaq[nx p t]! = false then tTl[nx p t]!
        else nx p t) := by
  obtain ⟨a, b⟩ := hr hf
  simp only [Bool.not_eq_true'] at a b
  exact ⟨a, b⟩

include h hfam hS hT in
/-- **Truncated spines.** `1 ≤ tLn ≤ spineLen`; equal lengths share the tail;
a shorter truncated spine stops at an opaque term of the same family below `t`
whose spine makes up the difference and has the same tail. -/
theorem trunc_spine : ∀ t, t < p.dag.size → p.family[t]! ≠ .none →
    1 ≤ tLn[t]! ∧ tLn[t]! ≤ p.spineLen[t]! ∧
      (tLn[t]! = p.spineLen[t]! → tTl[t]! = p.tail[t]!) ∧
      (tLn[t]! < p.spineLen[t]! → tTl[t]! < t ∧ opaq[tTl[t]!]! = true ∧
        p.family[tTl[t]!]! = p.family[t]! ∧ p.spineLen[t]! = tLn[t]! + p.spineLen[tTl[t]!]! ∧
        p.tail[t]! = p.tail[tTl[t]!]!) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht hf
    have hn := nx_lt h hfam ht hf
    obtain ⟨s1, s2⟩ := spineRow_full (hS t ht) hf
    obtain ⟨t1, t2⟩ := spineRow_trunc (hT t ht) hf
    by_cases hsame : p.family[nx p t]! = p.family[t]!
    · have hfn : p.family[nx p t]! ≠ .none := by rw [hsame]; exact hf
      obtain ⟨i1, i2, i3, i4⟩ := ih _ hn (by omega) hfn
      rw [ite_eq_left hsame] at s1 s2
      by_cases ho : opaq[nx p t]! = false
      · rw [ite_eq_left ⟨hsame, ho⟩] at t1 t2
        refine ⟨by omega, by omega, fun he => ?_, fun hlt => ?_⟩
        · rw [t2, s2]; exact i3 (by omega)
        · obtain ⟨j1, j2, j3, j4, j5⟩ := i4 (by omega)
          rw [t2]
          refine ⟨by omega, j2, by rw [j3, hsame], by omega, by rw [s2, j5]⟩
      · have ho' : opaq[nx p t]! = true := by simpa using ho
        rw [ite_eq_right (fun hc => ho hc.2)] at t1 t2
        refine ⟨by omega, by omega, fun he => by omega, fun _ => ?_⟩
        rw [t2]
        exact ⟨hn, ho', hsame, by omega, s2⟩
    · rw [ite_eq_right hsame] at s1 s2
      rw [ite_eq_right (fun hc => hsame hc.1)] at t1 t2
      refine ⟨by omega, by omega, fun _ => by rw [t2, s2], fun hlt => by omega⟩

include h hfam hS hT in
/-- The stop of a telescope from its successor. -/
theorem stopOf_step {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none) :
    stopOf p tLn tTl t =
      if p.family[nx p t]! = p.family[t]! then
        (if opaq[nx p t]! = true then some (nx p t) else stopOf p tLn tTl (nx p t))
      else none := by
  have hn := nx_lt h hfam ht hf
  obtain ⟨s1, _⟩ := spineRow_full (hS t ht) hf
  obtain ⟨t1, t2⟩ := spineRow_trunc (hT t ht) hf
  unfold stopOf
  by_cases hsame : p.family[nx p t]! = p.family[t]!
  · rw [ite_eq_left hsame] at s1 ⊢
    have hfn : p.family[nx p t]! ≠ .none := by rw [hsame]; exact hf
    obtain ⟨i1, _, _, _⟩ := trunc_spine h hfam hS hT _ (by omega) hfn
    by_cases ho : opaq[nx p t]! = true
    · rw [ite_eq_right (fun hc => by simp [ho] at hc)] at t1 t2
      rw [ite_eq_left ho, ite_eq_left (by omega), t2]
    · have ho' : opaq[nx p t]! = false := by simpa using ho
      rw [ite_eq_left ⟨hsame, ho'⟩] at t1 t2
      rw [ite_eq_right ho, t2]
      by_cases hl : tLn[nx p t]! < p.spineLen[nx p t]!
      · rw [ite_eq_left (by omega), ite_eq_left hl]
      · rw [ite_eq_right (by omega), ite_eq_right hl]
  · rw [ite_eq_right hsame] at s1 ⊢
    rw [ite_eq_right (fun hc => hsame hc.1)] at t1
    rw [ite_eq_right (by omega)]

/-- `u` is on the truncated spine of `t`, strictly below it: reached by
same-family steps through non-opaque terms. -/
inductive TSp (p : Prep) (opaq : Array Bool) : Nat → Nat → Prop
  | one {t : Nat} : p.family[t]! ≠ .none → p.family[nx p t]! = p.family[t]! →
      opaq[nx p t]! = false → TSp p opaq t (nx p t)
  | step {t u : Nat} : p.family[t]! ≠ .none → p.family[nx p t]! = p.family[t]! →
      opaq[nx p t]! = false → TSp p opaq (nx p t) u → TSp p opaq t u

/-- `v` is on the full spine of `t`, strictly below it. -/
inductive DSp (p : Prep) : Nat → Nat → Prop
  | one {t : Nat} : p.family[t]! ≠ .none → p.family[nx p t]! = p.family[t]! → DSp p t (nx p t)
  | step {t u : Nat} : p.family[t]! ≠ .none → p.family[nx p t]! = p.family[t]! →
      DSp p (nx p t) u → DSp p t u

theorem TSp.trans {opaq : Array Bool} {t u v : Nat} (h1 : TSp p opaq t u) (h2 : TSp p opaq u v) :
    TSp p opaq t v := by
  induction h1 with
  | one a b c => exact .step a b c h2
  | step a b c _ ih => exact .step a b c (ih h2)

theorem DSp.trans {t u v : Nat} (h1 : DSp p t u) (h2 : DSp p u v) : DSp p t v := by
  induction h1 with
  | one a b => exact .step a b h2
  | step a b _ ih => exact .step a b (ih h2)

include h hfam hS hT in
/-- A term on the truncated spine of `t`: below `t`, of `t`'s family, not
opaque, with the same stop, a shorter truncated spine, and the same depth below
`t` on both spines. -/
theorem TSp.props {t u : Nat} (ht : t < p.dag.size) (hu : TSp p opaq t u) :
    u < t ∧ p.family[u]! = p.family[t]! ∧ opaq[u]! = false ∧
      stopOf p tLn tTl u = stopOf p tLn tTl t ∧ tLn[u]! < tLn[t]! ∧
      p.spineLen[u]! < p.spineLen[t]! ∧
      p.spineLen[t]! - p.spineLen[u]! = tLn[t]! - tLn[u]! := by
  induction hu with
  | @one t hf hs ho =>
    have hn := nx_lt h hfam ht hf
    obtain ⟨s1, _⟩ := spineRow_full (hS t ht) hf
    obtain ⟨t1, _⟩ := spineRow_trunc (hT t ht) hf
    rw [ite_eq_left hs] at s1
    rw [ite_eq_left ⟨hs, ho⟩] at t1
    rw [stopOf_step h hfam hS hT ht hf, ite_eq_left hs, ite_eq_right (by simp [ho])]
    exact ⟨hn, hs, ho, rfl, by omega, by omega, by omega⟩
  | @step t u hf hs ho _ ih =>
    have hn := nx_lt h hfam ht hf
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := ih (by omega)
    obtain ⟨s1, _⟩ := spineRow_full (hS t ht) hf
    obtain ⟨t1, _⟩ := spineRow_trunc (hT t ht) hf
    rw [ite_eq_left hs] at s1
    rw [ite_eq_left ⟨hs, ho⟩] at t1
    have hst : stopOf p tLn tTl t = stopOf p tLn tTl (nx p t) := by
      rw [stopOf_step h hfam hS hT ht hf, ite_eq_left hs, ite_eq_right (by simp [ho])]
    refine ⟨by omega, by rw [i2, hs], i3, by rw [i4, hst], by omega, by omega, by omega⟩

include h hfam hS in
theorem DSp.props {t v : Nat} (ht : t < p.dag.size) (hv : DSp p t v) :
    v < t ∧ p.family[v]! = p.family[t]! ∧ p.spineLen[v]! < p.spineLen[t]! := by
  induction hv with
  | @one t hf hs =>
    have hn := nx_lt h hfam ht hf
    obtain ⟨s1, _⟩ := spineRow_full (hS t ht) hf
    rw [ite_eq_left hs] at s1
    exact ⟨hn, hs, by omega⟩
  | @step t u hf hs _ ih =>
    have hn := nx_lt h hfam ht hf
    obtain ⟨i1, i2, i3⟩ := ih (by omega)
    obtain ⟨s1, _⟩ := spineRow_full (hS t ht) hf
    rw [ite_eq_left hs] at s1
    exact ⟨by omega, by rw [i2, hs], by omega⟩

end Spines

/-! ## Rows

The dictionary row of `t` (`evalRowG`) and the truncated row (`tRow`), taken
apart. -/

/-- A width as a cost: the minimum with the width when present. -/
def costW (o : Option Nat) (v : Nat) : Nat :=
  match o with
  | some w => min v w
  | none => v

/-- The spine sum the dictionary row of a telescope writes. -/
def dSide (p : Prep) (dC dS : Nat → Nat) (t : Nat) : Nat :=
  (p.dag.node t).sideExtra + dC (p.dag.node t).sideChild +
    (if p.family[nx p t]! = p.family[t]! then dS (nx p t) else 0)

/-- The descendant link the dictionary row of a telescope writes. -/
def dBl (p : Prep) (wd : Nat → Option Nat) (dB : Nat → Option Nat) (t : Nat) : Option Nat :=
  if p.family[nx p t]! = p.family[t]! then
    (if (wd (nx p t)).isSome then some (nx p t) else dB (nx p t))
  else none

/-- The inline cost the dictionary row of `t` computes before its width. -/
def dInl (p : Prep) (wd : Nat → Option Nat) (dC dS : Nat → Nat) (dB : Nat → Option Nat)
    (t : Nat) : Nat :=
  if p.family[t]! = .none then
    (p.dag.node t).children.foldl (fun acc c => acc + dC c) (p.dag.node t).head.ownBytes
  else
    (cutScanG p.spineLen (fun u => if u = t then dSide p dC dS t else dS u)
      (fun u => if u = t then dBl p wd dB t else dB u) wd p.spineLen[t]! (dSide p dC dS t)
      p.spineLen[t]! (dBl p wd dB t) (tag4Size p.spineLen[t]! + dSide p dC dS t + dC p.tail[t]!)
      0).1

theorem evalRowG_eq (p : Prep) (wd : Nat → Option Nat) (dC dS : Nat → Nat)
    (dB : Nat → Option Nat) (t : Nat) :
    evalRowG p.dag p.family p.spineLen p.tail wd dC dS dB t =
      (costW (wd t) (dInl p wd dC dS dB t),
        (if p.family[t]! = .none then dS t else dSide p dC dS t),
        (if p.family[t]! = .none then dB t else dBl p wd dB t)) := by
  unfold evalRowG dInl dSide dBl costW
  by_cases hf : p.family[t]! = .none
  · simp only [hf, beq_self_eq_true, ite_true]
    rcases wd t with _ | w <;> rfl
  · have hb : (p.family[t]! == Family.none) = false := by simpa using hf
    simp only [hb, Bool.false_eq_true, ite_false, hf, beq_iff_eq]
    rcases wd t with _ | w <;> rfl

/-- The dictionary row recurrence at `t` (readers `dC dS dB`, widths `wd`). -/
def DRow (p : Prep) (wd : Nat → Option Nat) (dC dS : Nat → Nat) (dB : Nat → Option Nat)
    (t : Nat) : Prop :=
  (dC t, dS t, dB t) = evalRowG p.dag p.family p.spineLen p.tail wd dC dS dB t

theorem DRow.parts {p : Prep} {wd : Nat → Option Nat} {dC dS : Nat → Nat}
    {dB : Nat → Option Nat} {t : Nat} (h : DRow p wd dC dS dB t) :
    dC t = costW (wd t) (dInl p wd dC dS dB t) ∧
      (p.family[t]! ≠ .none → dS t = dSide p dC dS t ∧ dB t = dBl p wd dB t) := by
  unfold DRow at h
  rw [evalRowG_eq] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun hf => ?_⟩
  rw [ite_eq_right hf] at h2 h3
  exact ⟨h2, h3⟩

/-- The spine sum the truncated row of a telescope writes. -/
def tSide (p : Prep) (opaq : Array Bool) (tC tS : Nat → Nat) (t : Nat) : Nat :=
  (p.dag.node t).sideExtra + tC (p.dag.node t).sideChild +
    (if p.family[nx p t]! = p.family[t]! ∧ opaq[nx p t]! = false then tS (nx p t) else 0)

/-- The encoded descendant link the truncated row of a telescope writes. -/
def tBl (p : Prep) (opaq : Array Bool) (X : Nat → Bool) (tB : Nat → Nat) (t : Nat) : Nat :=
  if p.family[nx p t]! = p.family[t]! ∧ opaq[nx p t]! = false then
    (if X (nx p t) then nx p t + 1 else tB (nx p t))
  else 0

/-- The inline cost of the truncated row. -/
def tInl (p : Prep) (opaq : Array Bool) (tLn tTl : Array Nat) (w : Nat) (X : Nat → Bool)
    (tC tS tB : Nat → Nat) (t : Nat) : Nat :=
  if p.family[t]! = .none then
    (p.dag.node t).children.foldl (fun acc c => acc + tC c) (p.dag.node t).head.ownBytes
  else
    tScan tLn w tS tB tLn[t]! (tSide p opaq tC tS t) tLn[t]! (tBl p opaq X tB t)
      (tag4Size tLn[t]! + tSide p opaq tC tS t + tC tTl[t]!)

/-- The cost of the truncated row from its inline cost. -/
def tCost (opaq : Array Bool) (w : Nat) (X : Nat → Bool) (t inl : Nat) : Nat :=
  if opaq[t]! then w else if X t then min w inl else inl

theorem tRow_eq (p : Prep) (opaq : Array Bool) (tLn tTl : Array Nat) (w : Nat) (X : Nat → Bool)
    (tC tS tB : Nat → Nat) (t : Nat) :
    tRow p opaq tLn tTl w X tC tS tB t =
      (tCost opaq w X t (tInl p opaq tLn tTl w X tC tS tB t),
        tInl p opaq tLn tTl w X tC tS tB t,
        (if p.family[t]! = .none then 0 else tSide p opaq tC tS t),
        (if p.family[t]! = .none then 0 else tBl p opaq X tB t)) := by
  unfold tRow tInl tSide tBl tCost
  by_cases hf : p.family[t]! = .none
  · simp only [hf, beq_self_eq_true, ite_true]
  · have hb : (p.family[t]! == Family.none) = false := by simpa using hf
    simp only [hb, Bool.false_eq_true, ite_false, hf, Bool.and_eq_true, beq_iff_eq,
      Bool.not_eq_true']

/-- The truncated row recurrence at `t`. -/
def TRow (p : Prep) (opaq : Array Bool) (tLn tTl : Array Nat) (w : Nat) (X : Nat → Bool)
    (tC tI tS tB : Nat → Nat) (t : Nat) : Prop :=
  (tC t, tI t, tS t, tB t) = tRow p opaq tLn tTl w X tC tS tB t

theorem TRow.parts {p : Prep} {opaq : Array Bool} {tLn tTl : Array Nat} {w : Nat}
    {X : Nat → Bool} {tC tI tS tB : Nat → Nat} {t : Nat}
    (h : TRow p opaq tLn tTl w X tC tI tS tB t) :
    tC t = tCost opaq w X t (tI t) ∧ tI t = tInl p opaq tLn tTl w X tC tS tB t ∧
      (p.family[t]! ≠ .none → tS t = tSide p opaq tC tS t ∧ tB t = tBl p opaq X tB t) := by
  unfold TRow at h
  rw [tRow_eq] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [h1, h2], h2, fun hf => ?_⟩
  rw [ite_eq_right hf] at h3 h4
  exact ⟨h3, h4⟩

/-! ## Links -/

section Links

variable {p : Prep} (h : DagOK p.dag)
  (hfam : ∀ t, t < p.dag.size → p.family[t]! = (p.dag.node t).head.family)

include h hfam in
/-- A dictionary link leads down the full spine to an available term (with the
rows below `m`). -/
theorem dLinkBelow {wd : Nat → Option Nat} {dC dS : Nat → Nat} {dB : Nat → Option Nat}
    (m : Nat) (hm : m ≤ p.dag.size) (hD : ∀ t, t < m → DRow p wd dC dS dB t) :
    ∀ x, x < m → p.family[x]! ≠ .none → ∀ v, dB x = some v →
      DSp p x v ∧ (wd v).isSome = true := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro hx hf v hv
    have hn := nx_lt h hfam (by omega) hf
    rw [((hD x hx).parts.2 hf).2] at hv
    unfold dBl at hv
    by_cases hs : p.family[nx p x]! = p.family[x]!
    · rw [ite_eq_left hs] at hv
      by_cases hw : (wd (nx p x)).isSome = true
      · rw [ite_eq_left hw] at hv
        cases hv
        exact ⟨.one hf hs, hw⟩
      · rw [ite_eq_right hw] at hv
        have hfn : p.family[nx p x]! ≠ .none := by rw [hs]; exact hf
        obtain ⟨a, b⟩ := ih _ hn (by omega) hfn v hv
        exact ⟨.step hf hs a, b⟩
    · rw [ite_eq_right hs] at hv
      cases hv

include h hfam in
/-- A dictionary link leads down the full spine to an available term. -/
theorem dLink {wd : Nat → Option Nat} {dC dS : Nat → Nat} {dB : Nat → Option Nat}
    (hD : ∀ t, t < p.dag.size → DRow p wd dC dS dB t) :
    ∀ x, x < p.dag.size → p.family[x]! ≠ .none → ∀ v, dB x = some v →
      DSp p x v ∧ (wd v).isSome = true :=
  dLinkBelow h hfam p.dag.size (Nat.le_refl _) hD

include h hfam in
/-- Dictionary spine sums decrease down the spine. -/
theorem dSides_mono {wd : Nat → Option Nat} {dC dS : Nat → Nat} {dB : Nat → Option Nat}
    (hD : ∀ t, t < p.dag.size → DRow p wd dC dS dB t) {x v : Nat} (hx : x < p.dag.size)
    (hv : DSp p x v) : dS v ≤ dS x := by
  induction hv with
  | @one x hf hs =>
    rw [((hD x hx).parts.2 hf).1]
    unfold dSide
    rw [ite_eq_left hs]
    omega
  | @step x u hf hs _ ih =>
    have hn := nx_lt h hfam hx hf
    have := ih (by omega)
    rw [((hD x hx).parts.2 hf).1]
    unfold dSide
    rw [ite_eq_left hs]
    omega

include h hfam in
/-- A truncated link leads down the truncated spine to an available member. -/
theorem tLink {opaq : Array Bool} {tLn tTl : Array Nat} {w : Nat} {X : Nat → Bool}
    {tC tI tS tB : Nat → Nat} (hTr : ∀ t, t < p.dag.size → TRow p opaq tLn tTl w X tC tI tS tB t) :
    ∀ x, x < p.dag.size → p.family[x]! ≠ .none → tB x ≠ 0 →
      TSp p opaq x (tB x - 1) ∧ X (tB x - 1) = true := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro hx hf hv
    have hn := nx_lt h hfam hx hf
    have hb := ((hTr x hx).parts.2.2 hf).2
    rw [hb] at hv ⊢
    unfold tBl at hv ⊢
    by_cases hs : p.family[nx p x]! = p.family[x]! ∧ opaq[nx p x]! = false
    · rw [ite_eq_left hs] at hv ⊢
      by_cases hX : X (nx p x) = true
      · rw [ite_eq_left hX] at hv ⊢
        simp only [Nat.add_sub_cancel]
        exact ⟨.one hf hs.1 hs.2, hX⟩
      · rw [ite_eq_right hX] at hv ⊢
        have hfn : p.family[nx p x]! ≠ .none := by rw [hs.1]; exact hf
        obtain ⟨a, b⟩ := ih _ hn (by omega) hfn hv
        exact ⟨.step hf hs.1 hs.2 a, b⟩
    · rw [ite_eq_right hs] at hv
      exact absurd rfl hv

end Links

/-! ## Scans

`cutScanG` and `tScan` keep the cheaper of the running best and each visited
cut. `scan_rel` runs a dictionary scan alongside a truncated scan: while the
truncated cursor is on the truncated spine both visit the same term with the
same cut cost; when it ends, the dictionary cursor is at the stop `c`, whose cut
is the truncated natural ending, and every later dictionary cut costs at least
as much. -/

/-- The kept value of a scan step. -/
theorem keep_eq (a b : Nat) : (if a < b then a else b) = min a b := by
  rw [Nat.min_def]; split <;> split <;> omega

/-- A dictionary scan whose remaining cuts all cost at least `X`, from a best
of at most `X`, keeps its best. -/
theorem scan_dominated (sl : Array Nat) (gS : Nat → Nat) (gB : Nat → Option Nat)
    (wd : Nat → Option Nat) (l s X : Nat) (R : Nat → Prop)
    (hR : ∀ v v', R v → gB v = some v' → R v')
    (hX : ∀ v, R v → X ≤ tag4Size (l - sl[v]!) + (s - gS v) + (wd v).getD 0) :
    ∀ fuel cur acc work, acc ≤ X → (∀ v, cur = some v → R v) →
      (cutScanG sl gS gB wd l s fuel cur acc work).1 = acc
  | 0, _, _, _, _, _ => by simp only [cutScanG]
  | _ + 1, none, _, _, _, _ => by simp only [cutScanG]
  | fuel + 1, some v, acc, work, hacc, hcur => by
    simp only [cutScanG]
    have hv := hcur v rfl
    have hc := hX v hv
    rw [keep_eq, Nat.min_eq_right (by omega)]
    exact scan_dominated sl gS gB wd l s X R hR hX fuel _ acc _ hacc
      (fun v' hv' => hR v v' hv hv')

/-- **Scans side by side.** -/
theorem scan_rel (sl tLn : Array Nat) (w : Nat) (gS : Nat → Nat) (gB : Nat → Option Nat)
    (wd : Nat → Option Nat) (lD sD : Nat) (tS tB : Nat → Nat) (lT sT : Nat)
    (OnT : Nat → Prop) (stop : Option Nat)
    (H1 : ∀ u, OnT u → tag4Size (lD - sl[u]!) + (sD - gS u) + (wd u).getD 0 =
      tag4Size (lT - tLn[u]!) + (sT - tS u) + w)
    (H2 : ∀ u, OnT u → gB u = if tB u = 0 then stop else some (tB u - 1))
    (H3 : ∀ u, OnT u → tB u ≠ 0 → OnT (tB u - 1) ∧ sl[tB u - 1]! < sl[u]! ∧
      tLn[tB u - 1]! < tLn[u]!)
    (H4 : ∀ c, stop = some c → ∀ u, OnT u → sl[c]! < sl[u]!)
    (H5 : ∀ c, stop = some c → ∃ R : Nat → Prop, R c ∧ (∀ v v', R v → gB v = some v' → R v') ∧
      ∀ v, R v → tag4Size (lD - sl[c]!) + (sD - gS c) + (wd c).getD 0 ≤
        tag4Size (lD - sl[v]!) + (sD - gS v) + (wd v).getD 0) :
    ∀ fuelT fuelD curT accD accT work,
      (curT = 0 → ∀ c, stop = some c → sl[c]! < fuelD) →
      (curT ≠ 0 → OnT (curT - 1) ∧ sl[curT - 1]! < fuelD ∧ tLn[curT - 1]! < fuelT) →
      (match stop with
        | none => accD = accT
        | some c => min (tag4Size (lD - sl[c]!) + (sD - gS c) + (wd c).getD 0) accD = accT) →
      (cutScanG sl gS gB wd lD sD fuelD (if curT = 0 then stop else some (curT - 1)) accD work).1 =
        tScan tLn w tS tB lT sT fuelT curT accT := by
  intro fuelT
  induction fuelT with
  | zero =>
    intro fuelD curT accD accT work h0 hne hacc
    have hc0 : curT = 0 := by
      by_cases hc : curT = 0
      · exact hc
      · have := (hne hc).2.2
        omega
    subst hc0
    simp only [ite_true, tScan]
    cases hst : stop with
    | none =>
      rw [hst] at hacc
      cases fuelD <;> simp only [cutScanG] <;> exact hacc
    | some c =>
      rw [hst] at hacc
      have hfd := h0 rfl c hst
      obtain ⟨fD, rfl⟩ : ∃ fD, fuelD = fD + 1 := ⟨fuelD - 1, by omega⟩
      simp only [cutScanG]
      obtain ⟨R, hRc, hRcl, hRX⟩ := H5 c hst
      rw [keep_eq]
      rw [hacc]
      apply scan_dominated sl gS gB wd lD sD _ R hRcl (fun v hv => hRX v hv)
      · rw [← hacc]; exact Nat.min_le_left _ _
      · intro v hv; exact hRcl c v hRc hv
  | succ fT ih =>
    intro fuelD curT accD accT work h0 hne hacc
    by_cases hc0 : curT = 0
    · subst hc0
      simp only [ite_true, tScan]
      cases hst : stop with
      | none =>
        rw [hst] at hacc
        cases fuelD <;> simp only [cutScanG] <;> exact hacc
      | some c =>
        rw [hst] at hacc
        have hfd := h0 rfl c hst
        obtain ⟨fD, rfl⟩ : ∃ fD, fuelD = fD + 1 := ⟨fuelD - 1, by omega⟩
        simp only [cutScanG]
        obtain ⟨R, hRc, hRcl, hRX⟩ := H5 c hst
        rw [keep_eq, hacc]
        apply scan_dominated sl gS gB wd lD sD _ R hRcl (fun v hv => hRX v hv)
        · rw [← hacc]; exact Nat.min_le_left _ _
        · intro v hv; exact hRcl c v hRc hv
    · obtain ⟨hon, hsl, htl⟩ := hne hc0
      obtain ⟨fD, rfl⟩ : ∃ fD, fuelD = fD + 1 := ⟨fuelD - 1, by omega⟩
      simp only [hc0, ite_false, tScan, cutScanG]
      rw [H2 _ hon, H1 _ hon, keep_eq, keep_eq]
      refine ih fD (tB (curT - 1)) _ _ _ ?_ ?_ ?_
      · intro hz c hst
        have := H4 c hst _ hon
        omega
      · intro hz
        obtain ⟨a, b, c⟩ := H3 _ hon hz
        exact ⟨a, by omega, by omega⟩
      · cases hst : stop with
        | none =>
          rw [hst] at hacc
          simp only
          rw [hacc]
        | some c =>
          rw [hst] at hacc
          simp only
          rw [← hacc]
          omega

/-- A dictionary scan depends only on the readers at the terms it can visit. -/
theorem scan_congr (sl : Array Nat) (gS gS' : Nat → Nat) (gB gB' : Nat → Option Nat)
    (wd wd' : Nat → Option Nat) (l s : Nat) (R : Nat → Prop)
    (hR : ∀ v v', R v → gB v = some v' → R v')
    (hagree : ∀ v, R v → gS v = gS' v ∧ gB v = gB' v ∧ wd v = wd' v) :
    ∀ fuel cur acc work, (∀ v, cur = some v → R v) →
      (cutScanG sl gS gB wd l s fuel cur acc work).1 =
        (cutScanG sl gS' gB' wd' l s fuel cur acc work).1
  | 0, _, _, _, _ => by simp only [cutScanG]
  | _ + 1, none, _, _, _ => by simp only [cutScanG]
  | fuel + 1, some v, acc, work, hcur => by
    simp only [cutScanG]
    have hv := hcur v rfl
    obtain ⟨a, b, c⟩ := hagree v hv
    rw [a, c, ← b]
    exact scan_congr sl gS gS' gB gB' wd wd' l s R hR hagree fuel _ _ _
      (fun v' hv' => hR v v' hv hv')

/-! ## Widths -/

theorem tag4Size_mono {a b : Nat} (h : a ≤ b) : tag4Size a ≤ tag4Size b := by
  unfold tag4Size
  rw [tagNByteWidth_eq_fast]
  unfold tagNByteWidthFast
  simp only [ite_true]
  repeat' split
  all_goals omega

theorem tag4Size_pos (a : Nat) : 1 ≤ tag4Size a := by
  unfold tag4Size
  rw [tagNByteWidth_eq_fast]
  unfold tagNByteWidthFast
  simp only [ite_true]
  repeat' split
  all_goals omega

/-! ## The relation of the two evaluations -/

section Rel

variable {p : Prep} (h : DagOK p.dag)
  (hfam : ∀ t, t < p.dag.size → p.family[t]! = (p.dag.node t).head.family)
  (hS : ∀ t, t < p.dag.size → SpineRow p.dag p.family (fun _ => true) p.spineLen p.tail t)
  {opaq : Array Bool} {tLn tTl : Array Nat}
  (hT : ∀ t, t < p.dag.size → SpineRow p.dag p.family (fun u => !opaq[u]!) tLn tTl t)

include h hfam hS hT in
/-- The tails of a telescope are below it. -/
theorem tails_lt : ∀ t, t < p.dag.size → p.family[t]! ≠ .none →
    p.tail[t]! < t ∧ tTl[t]! < t := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht hf
    have hn := nx_lt h hfam ht hf
    obtain ⟨_, s2⟩ := spineRow_full (hS t ht) hf
    obtain ⟨_, t2⟩ := spineRow_trunc (hT t ht) hf
    by_cases hs : p.family[nx p t]! = p.family[t]!
    · have hfn : p.family[nx p t]! ≠ .none := by rw [hs]; exact hf
      obtain ⟨i1, i2⟩ := ih _ hn (by omega) hfn
      rw [ite_eq_left hs] at s2
      refine ⟨by omega, ?_⟩
      split at t2 <;> omega
    · rw [ite_eq_right hs] at s2
      rw [ite_eq_right (fun hc => hs hc.1)] at t2
      omega

/-- The spine sum below the stop of `t` (`0` if its truncated spine does not
stop). -/
def stopSides (p : Prep) (tLn tTl : Array Nat) (dS : Nat → Nat) (t : Nat) : Nat :=
  match stopOf p tLn tTl t with
  | some c => dS c
  | none => 0

/-- The relation of the dictionary and truncated rows at `t`. -/
def RowsRel (p : Prep) (opaq : Array Bool) (tLn tTl : Array Nat) (w : Nat) (wd : Nat → Option Nat)
    (dC dS : Nat → Nat) (dB : Nat → Option Nat) (tC tI tS tB : Nat → Nat) (t : Nat) : Prop :=
  dC t = tC t ∧ dInl p wd dC dS dB t = tI t ∧
    (p.family[t]! ≠ .none → dS t = tS t + stopSides p tLn tTl dS t ∧
      dB t = (if tB t = 0 then stopOf p tLn tTl t else some (tB t - 1))) ∧
    (p.family[t]! ≠ .none → opaq[t]! = true → w ≤ dS t + dC p.tail[t]!)

include h hfam hS hT in
/-- **The two evaluations agree.** Given the dictionary rows (widths `w` on the
opaque and the available terms) and the truncated rows at every term, and the
opacity test of every opaque term on its truncated row, the costs and inline
costs agree at every term. -/
theorem rows_rel {w : Nat} {wd : Nat → Option Nat} {X : Nat → Bool}
    (hwd : ∀ u, u < p.dag.size → wd u = if opaq[u]! = true ∨ X u = true then some w else none)
    {dC dS : Nat → Nat} {dB : Nat → Option Nat} {tC tI tS tB : Nat → Nat}
    (hD : ∀ t, t < p.dag.size → DRow p wd dC dS dB t)
    (hTr : ∀ t, t < p.dag.size → TRow p opaq tLn tTl w X tC tI tS tB t)
    (hG : ∀ c, c < p.dag.size → opaq[c]! = true → tGuard p tTl w tC tI tS c = true) :
    ∀ t, t < p.dag.size → RowsRel p opaq tLn tTl w wd dC dS dB tC tI tS tB t := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    obtain ⟨hDc, hDtel⟩ := (hD t ht).parts
    obtain ⟨hTc, hTi, hTtel⟩ := (hTr t ht).parts
    -- the cost from the inline cost
    have hcost : dInl p wd dC dS dB t = tI t → dC t = tC t := by
      intro hi
      rw [hDc, hTc, hi, hwd t ht]
      unfold costW tCost
      by_cases ho : opaq[t]! = true
      · have hg := hG t ht ho
        unfold tGuard at hg
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
        simp only [ho, true_or, ite_true]
        exact Nat.min_eq_right hg.1
      · have ho' : opaq[t]! = false := by simpa using ho
        by_cases hx : X t = true
        · simp only [ho', hx, Bool.false_eq_true, false_or, ite_true, ite_false]
          exact Nat.min_comm _ _
        · have hx' : X t = false := by simpa using hx
          simp only [ho', hx', Bool.false_eq_true, false_or, ite_false]
    by_cases hf : p.family[t]! = .none
    · -- a non-telescope term: its children's costs
      have hinl : dInl p wd dC dS dB t = tI t := by
        rw [hTi]
        unfold dInl tInl
        rw [ite_eq_left hf, ite_eq_left hf, ← Array.foldl_toList, ← Array.foldl_toList]
        have hch : ∀ c ∈ (p.dag.node t).children.toList, dC c = tC c := fun c hc =>
          (ih c (h.child_lt ht (Array.mem_toList_iff.mp hc)) (by
            have := h.child_lt ht (Array.mem_toList_iff.mp hc); omega)).1
        generalize (p.dag.node t).children.toList = l at hch
        generalize (p.dag.node t).head.ownBytes = acc
        induction l generalizing acc with
        | nil => rfl
        | cons c l ihl =>
          simp only [List.foldl_cons]
          rw [hch c List.mem_cons_self]
          exact ihl (fun c hc => hch c (List.mem_cons_of_mem _ hc)) _
      exact ⟨hcost hinl, hinl, fun h' => absurd hf h', fun h' => absurd hf h'⟩
    · -- a telescope
      have hn := nx_lt h hfam ht hf
      have hsd := side_lt h hfam ht hf
      obtain ⟨hdS, hdB⟩ := hDtel hf
      obtain ⟨htS, htB⟩ := hTtel hf
      have hside : dC (p.dag.node t).sideChild = tC (p.dag.node t).sideChild :=
        (ih _ hsd (by omega)).1
      have hstop := stopOf_step h hfam hS hT ht hf
      obtain ⟨hl1, hl2, hl3, hl4⟩ := trunc_spine h hfam hS hT t ht hf
      obtain ⟨htl1, htl2⟩ := tails_lt h hfam hS hT t ht hf
      -- the spine sums and links
      have hR34 : dS t = tS t + stopSides p tLn tTl dS t ∧
          dB t = (if tB t = 0 then stopOf p tLn tTl t else some (tB t - 1)) := by
        have eS : dS t = (p.dag.node t).sideExtra + tC (p.dag.node t).sideChild +
            (if p.family[nx p t]! = p.family[t]! then dS (nx p t) else 0) := by
          rw [hdS, ← hside]; rfl
        have eT : tS t = (p.dag.node t).sideExtra + tC (p.dag.node t).sideChild +
            (if p.family[nx p t]! = p.family[t]! ∧ opaq[nx p t]! = false then tS (nx p t)
              else 0) := by
          rw [htS]; rfl
        have eB : dB t = if p.family[nx p t]! = p.family[t]! then
            (if (wd (nx p t)).isSome then some (nx p t) else dB (nx p t)) else none := by
          rw [hdB]; rfl
        have eTB : tB t = if p.family[nx p t]! = p.family[t]! ∧ opaq[nx p t]! = false then
            (if X (nx p t) then nx p t + 1 else tB (nx p t)) else 0 := by
          rw [htB]; rfl
        unfold stopSides
        by_cases hs : p.family[nx p t]! = p.family[t]!
        · have hfn : p.family[nx p t]! ≠ .none := by rw [hs]; exact hf
          by_cases ho : opaq[nx p t]! = true
          · have hw : (wd (nx p t)).isSome = true := by
              rw [hwd _ (by omega)]; simp [ho]
            have hc : ¬ (p.family[nx p t]! = p.family[t]! ∧ opaq[nx p t]! = false) := by
              intro hc; rw [ho] at hc; cases hc.2
            have hst : stopOf p tLn tTl t = some (nx p t) := by rw [hstop, ite_eq_left hs, ite_eq_left ho]
            have e1 : dS t = (p.dag.node t).sideExtra + tC (p.dag.node t).sideChild +
                dS (nx p t) := by rw [eS, ite_eq_left hs]
            have e2 : tS t = (p.dag.node t).sideExtra + tC (p.dag.node t).sideChild + 0 := by
              rw [eT, ite_eq_right hc]
            have e3 : dB t = some (nx p t) := by rw [eB, ite_eq_left hs, ite_eq_left hw]
            have e4 : tB t = 0 := by rw [eTB, ite_eq_right hc]
            refine ⟨?_, ?_⟩
            · rw [hst]; show dS t = tS t + dS (nx p t); omega
            · rw [e3, e4, hst]; rfl
          · have ho' : opaq[nx p t]! = false := by simpa using ho
            have hc : p.family[nx p t]! = p.family[t]! ∧ opaq[nx p t]! = false := ⟨hs, ho'⟩
            have hst : stopOf p tLn tTl t = stopOf p tLn tTl (nx p t) := by
              rw [hstop, ite_eq_left hs, ite_eq_right ho]
            obtain ⟨_, _, i3, _⟩ := ih _ hn (by omega)
            obtain ⟨j1, j2⟩ := i3 hfn
            unfold stopSides at j1
            have e1 : dS t = (p.dag.node t).sideExtra + tC (p.dag.node t).sideChild +
                dS (nx p t) := by rw [eS, ite_eq_left hs]
            have e2 : tS t = (p.dag.node t).sideExtra + tC (p.dag.node t).sideChild +
                tS (nx p t) := by rw [eT, ite_eq_left hc]
            rw [hst]
            refine ⟨?_, ?_⟩
            · rw [e1, e2, j1]; omega
            · by_cases hx : X (nx p t) = true
              · have hw : (wd (nx p t)).isSome = true := by
                  rw [hwd _ (by omega)]; simp [hx]
                have e3 : dB t = some (nx p t) := by rw [eB, ite_eq_left hs, ite_eq_left hw]
                have e4 : tB t = nx p t + 1 := by rw [eTB, ite_eq_left hc, ite_eq_left hx]
                rw [e3, e4, ite_eq_right (by omega), Nat.add_sub_cancel]
              · have hx' : X (nx p t) = false := by simpa using hx
                have hw : (wd (nx p t)).isSome = false := by
                  rw [hwd _ (by omega)]; simp [ho', hx']
                have e3 : dB t = dB (nx p t) := by
                  rw [eB, ite_eq_left hs, ite_eq_right (by simp [hw])]
                have e4 : tB t = tB (nx p t) := by rw [eTB, ite_eq_left hc, ite_eq_right hx]
                rw [e3, e4]
                exact j2
        · have hc : ¬ (p.family[nx p t]! = p.family[t]! ∧ opaq[nx p t]! = false) :=
            fun hc => hs hc.1
          have hst : stopOf p tLn tTl t = none := by rw [hstop, ite_eq_right hs]
          have e1 : dS t = (p.dag.node t).sideExtra + tC (p.dag.node t).sideChild + 0 := by
            rw [eS, ite_eq_right hs]
          have e2 : tS t = (p.dag.node t).sideExtra + tC (p.dag.node t).sideChild + 0 := by
            rw [eT, ite_eq_right hc]
          have e3 : dB t = none := by rw [eB, ite_eq_right hs]
          have e4 : tB t = 0 := by rw [eTB, ite_eq_right hc]
          refine ⟨?_, ?_⟩
          · rw [hst]; show dS t = tS t + 0; omega
          · rw [e3, e4, hst]; rfl
      obtain ⟨hR3, hR4⟩ := hR34
      -- the stop's facts
      have hstopFacts : ∀ c, stopOf p tLn tTl t = some c →
          c < t ∧ opaq[c]! = true ∧ p.family[c]! = p.family[t]! ∧
            p.spineLen[t]! = tLn[t]! + p.spineLen[c]! ∧ p.tail[t]! = p.tail[c]! ∧ tTl[t]! = c := by
        intro c hc
        unfold stopOf at hc
        by_cases hlt : tLn[t]! < p.spineLen[t]!
        · rw [ite_eq_left hlt] at hc
          cases hc
          obtain ⟨a, b, c', d, e⟩ := hl4 hlt
          exact ⟨a, b, c', d, e, rfl⟩
        · rw [ite_eq_right hlt] at hc; cases hc
      have hnostop : stopOf p tLn tTl t = none → tLn[t]! = p.spineLen[t]! ∧ tTl[t]! = p.tail[t]! := by
        intro hc
        unfold stopOf at hc
        by_cases hlt : tLn[t]! < p.spineLen[t]!
        · rw [ite_eq_left hlt] at hc; cases hc
        · exact ⟨by omega, hl3 (by omega)⟩
      -- the inline cost: the two scans
      have hinl : dInl p wd dC dS dB t = tI t := by
        rw [hTi]
        unfold dInl tInl
        rw [ite_eq_right hf, ite_eq_right hf]
        rw [← hdS, ← htS, ← htB]
        have hbl : dBl p wd dB t = if tB t = 0 then stopOf p tLn tTl t else some (tB t - 1) := by
          rw [← hdB]; exact hR4
        rw [hbl]
        apply scan_rel p.spineLen tLn w _ _ wd _ _ tS tB _ _
          (fun u => TSp p opaq t u ∧ X u = true) (stopOf p tLn tTl t)
        · -- equal cuts on the truncated spine
          intro u ⟨hu, hxu⟩
          obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := TSp.props h hfam hS hT ht hu
          have hfu : p.family[u]! ≠ .none := by rw [u2]; exact hf
          obtain ⟨_, _, k3, _⟩ := ih u u1 (by omega)
          obtain ⟨k31, _⟩ := k3 hfu
          have hwu : (wd u).getD 0 = w := by rw [hwd u (by omega)]; simp [hxu]
          have hut : u ≠ t := by omega
          simp only [hut, ite_false, hwu]
          have hz : stopSides p tLn tTl dS u = stopSides p tLn tTl dS t := by
            unfold stopSides; rw [u4]
          rw [k31, hR3, hz, show p.spineLen[t]! - p.spineLen[u]! = tLn[t]! - tLn[u]! from u7]
          omega
        · -- equal links on the truncated spine
          intro u ⟨hu, _⟩
          obtain ⟨u1, u2, _, u4, _, _, _⟩ := TSp.props h hfam hS hT ht hu
          have hfu : p.family[u]! ≠ .none := by rw [u2]; exact hf
          obtain ⟨_, _, k3, _⟩ := ih u u1 (by omega)
          have hut : u ≠ t := by omega
          simp only [hut, ite_false]
          rw [(k3 hfu).2, u4]
        · -- the truncated spine goes down
          intro u ⟨hu, _⟩ hz
          obtain ⟨u1, u2, _, _, _, _, _⟩ := TSp.props h hfam hS hT ht hu
          have hfu : p.family[u]! ≠ .none := by rw [u2]; exact hf
          obtain ⟨a, b⟩ := tLink h hfam hTr u (by omega) hfu hz
          obtain ⟨_, _, _, _, a5, a6, _⟩ := TSp.props h hfam hS hT (by omega) a
          exact ⟨⟨hu.trans a, b⟩, a6, a5⟩
        · -- the stop is below the truncated spine
          intro c hc u ⟨hu, _⟩
          obtain ⟨u1, u2, _, u4, _, _, _⟩ := TSp.props h hfam hS hT ht hu
          have hfu : p.family[u]! ≠ .none := by rw [u2]; exact hf
          obtain ⟨k1, _, _, k4⟩ := trunc_spine h hfam hS hT u (by omega) hfu
          rw [← u4] at hc
          unfold stopOf at hc
          by_cases hlt : tLn[u]! < p.spineLen[u]!
          · rw [ite_eq_left hlt] at hc
            cases hc
            obtain ⟨_, _, _, d, _⟩ := k4 hlt
            omega
          · rw [ite_eq_right hlt] at hc; cases hc
        · -- below the stop the dictionary cuts are dominated
          intro c hc
          obtain ⟨c1, c2, c3, _, _, _⟩ := hstopFacts c hc
          refine ⟨fun v => v = c ∨ (DSp p c v ∧ (wd v).isSome = true), Or.inl rfl, ?_, ?_⟩
          · intro v v' hv hv'
            have hvt : v < t := by
              rcases hv with rfl | ⟨hv, _⟩
              · exact c1
              · have := (DSp.props h hfam hS (by omega) hv).1; omega
            have hfv : p.family[v]! ≠ .none := by
              rcases hv with rfl | ⟨hv, _⟩
              · rw [c3]; exact hf
              · rw [(DSp.props h hfam hS (by omega) hv).2.1, c3]; exact hf
            have hvne : v ≠ t := by omega
            simp only [hvne, ite_false] at hv'
            obtain ⟨a, b⟩ := dLink h hfam hD v (by omega) hfv v' hv'
            refine Or.inr ⟨?_, b⟩
            rcases hv with rfl | ⟨hv, _⟩
            · exact a
            · exact hv.trans a
          · intro v hv
            have hct : c ≠ t := by omega
            have hwc : (wd c).getD 0 = w := by rw [hwd c (by omega)]; simp [c2]
            rcases hv with rfl | ⟨hv, hwv⟩
            · exact Nat.le_refl _
            · obtain ⟨v1, _, v3⟩ := DSp.props h hfam hS (by omega) hv
              have hvt : v ≠ t := by omega
              have hwv' : (wd v).getD 0 = w := by
                rw [hwd v (by omega)] at hwv ⊢
                by_cases hc : opaq[v]! = true ∨ X v = true
                · rw [ite_eq_left hc]; rfl
                · rw [ite_eq_right hc] at hwv; cases hwv
              have hmono := dSides_mono h hfam hD (by omega) hv
              simp only [hct, hvt, ite_false, hwc, hwv']
              have := tag4Size_mono (show p.spineLen[t]! - p.spineLen[c]! ≤
                p.spineLen[t]! - p.spineLen[v]! by omega)
              omega
        · -- the start: no stop needs no fuel
          intro hz c hc
          obtain ⟨_, _, _, d, _, _⟩ := hstopFacts c hc
          omega
        · -- the start: on the truncated spine
          intro hz
          obtain ⟨a, b⟩ := tLink h hfam hTr t ht hf hz
          obtain ⟨_, _, _, _, a5, a6, _⟩ := TSp.props h hfam hS hT ht a
          exact ⟨⟨a, b⟩, a6, a5⟩
        · -- the natural endings
          cases hc : stopOf p tLn tTl t with
          | none =>
            simp only
            obtain ⟨e1, e2⟩ := hnostop hc
            have hz : stopSides p tLn tTl dS t = 0 := by unfold stopSides; rw [hc]
            rw [hR3, hz, e1, e2, (ih _ htl1 (by omega)).1, Nat.add_zero]
          | some c =>
            simp only
            obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hstopFacts c hc
            have hct : c ≠ t := by omega
            have hwc : (wd c).getD 0 = w := by rw [hwd c (by omega)]; simp [c2]
            have hz : stopSides p tLn tTl dS t = dS c := by unfold stopSides; rw [hc]
            have hfc : p.family[c]! ≠ .none := by rw [c3]; exact hf
            have hR5c := (ih c c1 (by omega)).2.2.2 hfc c2
            have hTcc : tC c = w := by
              rw [(hTr c (by omega)).parts.1]; unfold tCost; simp [c2]
            simp only [hct, ite_false, hwc]
            rw [c6, hTcc, hR3, hz, c5]
            have hmono := tag4Size_mono (show tLn[t]! ≤ p.spineLen[t]! by omega)
            rw [show p.spineLen[t]! - p.spineLen[c]! = tLn[t]! by omega]
            rw [Nat.min_def]
            split <;> omega
      refine ⟨hcost hinl, hinl, fun _ => ⟨hR3, hR4⟩, fun _ ho => ?_⟩
      -- the opacity of `t` itself
      have hg := hG t ht ho
      unfold tGuard at hg
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hg
      have hg2 : w ≤ tS t + tC tTl[t]! := by
        rcases hg.2 with h' | h'
        · exact absurd h' hf
        · exact h'
      cases hc : stopOf p tLn tTl t with
      | none =>
        obtain ⟨_, e2⟩ := hnostop hc
        have hz : stopSides p tLn tTl dS t = 0 := by unfold stopSides; rw [hc]
        rw [hR3, hz, ← e2, (ih _ htl2 (by omega)).1]
        omega
      | some c =>
        obtain ⟨c1, c2, c3, _, c5, _⟩ := hstopFacts c hc
        have hz : stopSides p tLn tTl dS t = dS c := by unfold stopSides; rw [hc]
        have hfc : p.family[c]! ≠ .none := by rw [c3]; exact hf
        have hR5c := (ih c c1 (by omega)).2.2.2 hfc c2
        rw [hR3, hz, c5]
        omega

end Rel

end Ix.Sharing.Exact.AreaProof

end
