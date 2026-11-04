/-
  The area search computes the specification's search, part 2: the
  dictionary side. The full evaluation `Prep.eval` and the closure evaluation
  of `SCtx.phiE` (the closure folded from the base evaluation) satisfy the
  dictionary row recurrence at every term (`eval_rows`, `closure_rows`).
-/
module

public import Ix.Sharing.Exact.AreaRowsRel
import all Ix.Sharing.Exact.Basic
import all Ix.Sharing.Exact.Dag
import all Ix.Sharing.Exact.Dictionary
import all Ix.Sharing.Exact.UniformSearch
import all Ix.Sharing.Exact.UniformSearchLocal
import all Ix.Sharing.Exact.AreaSearch
import all Ix.Sharing.Exact.AreaRowsRel

public section

namespace Ix.Sharing.Exact.AreaProof

open Ix.Sharing.Exact
open Ix.Sharing.Exact.LocalSearch (ESize eget evalStep_get setBang_read)

/-! ## Descendants -/

/-- `u` is a proper descendant of `t`. -/
inductive Desc (dag : Dag) (t : Nat) : Nat → Prop
  | child {c : Nat} : c ∈ (dag.node t).children → Desc dag t c
  | trans {u c : Nat} : Desc dag t u → c ∈ (dag.node u).children → Desc dag t c

theorem Desc.lt {dag : Dag} (h : DagOK dag) {t u : Nat} (ht : t < dag.size) (hu : Desc dag t u) :
    u < t := by
  induction hu with
  | child hc => exact h.child_lt ht hc
  | trans _ hc ih => exact Nat.lt_trans (h.child_lt (by omega) hc) ih

theorem Desc.trans' {dag : Dag} {t u v : Nat} (h1 : Desc dag t u) (h2 : Desc dag u v) :
    Desc dag t v := by
  induction h2 with
  | child hc => exact .trans h1 hc
  | trans _ hc ih => exact .trans ih hc

section Desc

variable {p : Prep} (h : DagOK p.dag)
  (hfam : ∀ t, t < p.dag.size → p.family[t]! = (p.dag.node t).head.family)

include h hfam in
theorem nx_mem {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none) :
    nx p t ∈ (p.dag.node t).children :=
  spineNext_mem (by rw [← hfam t ht]; exact hf) (h.arity t ht)

include h hfam in
theorem side_mem {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none) :
    (p.dag.node t).sideChild ∈ (p.dag.node t).children :=
  sideChild_mem (by rw [← hfam t ht]; exact hf) (h.arity t ht)

include h hfam in
theorem DSp.desc {t v : Nat} (ht : t < p.dag.size) (hv : DSp p t v) : Desc p.dag t v := by
  induction hv with
  | @one t hf _ => exact .child (nx_mem h hfam ht hf)
  | @step t u hf _ _ ih =>
    have hn := nx_lt h hfam ht hf
    exact (Desc.child (nx_mem h hfam ht hf)).trans' (ih (by omega))

include h hfam in
/-- The natural tail of a telescope is a descendant. -/
theorem tail_desc (hS : ∀ t, t < p.dag.size → SpineRow p.dag p.family (fun _ => true) p.spineLen p.tail t) :
    ∀ t, t < p.dag.size → p.family[t]! ≠ .none → Desc p.dag t p.tail[t]! := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht hf
    have hn := nx_lt h hfam ht hf
    obtain ⟨_, s2⟩ := spineRow_full (hS t ht) hf
    by_cases hs : p.family[nx p t]! = p.family[t]!
    · rw [ite_eq_left hs] at s2
      rw [s2]
      have hfn : p.family[nx p t]! ≠ .none := by rw [hs]; exact hf
      exact (Desc.child (nx_mem h hfam ht hf)).trans' (ih _ hn (by omega) hfn)
    · rw [ite_eq_right hs] at s2
      rw [s2]
      exact .child (nx_mem h hfam ht hf)

end Desc

/-! ## Congruence of a dictionary row -/

theorem DRow.of_parts {p : Prep} {wd : Nat → Option Nat} {dC dS : Nat → Nat}
    {dB : Nat → Option Nat} {t : Nat} (h1 : dC t = costW (wd t) (dInl p wd dC dS dB t))
    (h2 : p.family[t]! ≠ .none → dS t = dSide p dC dS t ∧ dB t = dBl p wd dB t) :
    DRow p wd dC dS dB t := by
  unfold DRow
  rw [evalRowG_eq, ← h1]
  by_cases hf : p.family[t]! = .none
  · simp only [hf, ite_true]
  · obtain ⟨a, b⟩ := h2 hf
    simp only [hf, ite_false, ← a, ← b]

section Congr

variable {p : Prep} (h : DagOK p.dag)
  (hfam : ∀ t, t < p.dag.size → p.family[t]! = (p.dag.node t).head.family)
  {t : Nat} (ht : t < p.dag.size) (S : Nat → Prop)
  {wd1 wd2 : Nat → Option Nat} {C1 C2 S1 S2 : Nat → Nat} {B1 B2 : Nat → Option Nat}
  (hag : ∀ u, S u → C1 u = C2 u ∧ S1 u = S2 u ∧ B1 u = B2 u ∧ wd1 u = wd2 u)
  (hch : ∀ c ∈ (p.dag.node t).children, S c)

include h hfam ht hag hch in
theorem dSide_congr (hf : p.family[t]! ≠ .none) : dSide p C1 S1 t = dSide p C2 S2 t := by
  unfold dSide
  rw [(hag _ (hch _ (side_mem h hfam ht hf))).1, (hag _ (hch _ (nx_mem h hfam ht hf))).2.1]

include h hfam ht hag hch in
theorem dBl_congr (hf : p.family[t]! ≠ .none) : dBl p wd1 B1 t = dBl p wd2 B2 t := by
  unfold dBl
  obtain ⟨_, _, b, c⟩ := hag _ (hch _ (nx_mem h hfam ht hf))
  rw [b, c]

include h hfam ht hag hch in
/-- The inline cost of a dictionary row depends only on the readers and widths
at a set `S` of terms other than `t` holding its children and natural tail and
closed under the links of the first readers at telescopes. -/
theorem dInl_congr (hne : ∀ u, S u → u ≠ t)
    (htail : p.family[t]! ≠ .none → S p.tail[t]!)
    (hcl : ∀ u v, S u → p.family[u]! ≠ .none → B1 u = some v → S v ∧ p.family[v]! ≠ .none) :
    dInl p wd1 C1 S1 B1 t = dInl p wd2 C2 S2 B2 t := by
  unfold dInl
  by_cases hf : p.family[t]! = .none
  · rw [ite_eq_left hf, ite_eq_left hf, ← Array.foldl_toList, ← Array.foldl_toList]
    have hc : ∀ c ∈ (p.dag.node t).children.toList, C1 c = C2 c :=
      fun c hc => (hag c (hch c (Array.mem_toList_iff.mp hc))).1
    generalize (p.dag.node t).children.toList = l at hc
    generalize (p.dag.node t).head.ownBytes = acc
    induction l generalizing acc with
    | nil => rfl
    | cons c l ihl =>
      simp only [List.foldl_cons]
      rw [hc c List.mem_cons_self]
      exact ihl (fun c hc' => hc c (List.mem_cons_of_mem _ hc')) _
  · rw [ite_eq_right hf, ite_eq_right hf, dSide_congr h hfam ht S hag hch hf, dBl_congr h hfam ht S hag hch hf,
      (hag _ (htail hf)).1]
    have hbl : ∀ v, dBl p wd2 B2 t = some v → S v ∧ p.family[v]! ≠ .none := by
      intro v hv
      rw [← dBl_congr h hfam ht S hag hch hf] at hv
      unfold dBl at hv
      split at hv
      · rename_i hs
        have hfn : p.family[nx p t]! ≠ .none := by rw [hs]; exact hf
        split at hv
        · cases hv; exact ⟨hch _ (nx_mem h hfam ht hf), hfn⟩
        · exact hcl _ _ (hch _ (nx_mem h hfam ht hf)) hfn hv
      · cases hv
    refine scan_congr _ _ _ _ _ _ _ _ _ (fun u => S u ∧ p.family[u]! ≠ .none) ?_ ?_ _ _ _ _ hbl
    · intro u v hu huv
      rw [ite_eq_right (hne u hu.1)] at huv
      exact hcl u v hu.1 hu.2 huv
    · intro u hu
      have hut := hne u hu.1
      simp only [hut, ite_false]
      obtain ⟨_, a, b, c⟩ := hag u hu.1
      exact ⟨a, b, c⟩

include h hfam ht hag hch in
/-- A dictionary row transferred to other readers and widths that agree at `t`
and on such a set `S`. -/
theorem DRow.congrS (hne : ∀ u, S u → u ≠ t)
    (htail : p.family[t]! ≠ .none → S p.tail[t]!)
    (hcl : ∀ u v, S u → p.family[u]! ≠ .none → B1 u = some v → S v ∧ p.family[v]! ≠ .none)
    (hwt : wd1 t = wd2 t) (hC : C1 t = C2 t)
    (hSB : p.family[t]! ≠ .none → S1 t = S2 t ∧ B1 t = B2 t)
    (h1 : DRow p wd1 C1 S1 B1 t) : DRow p wd2 C2 S2 B2 t := by
  obtain ⟨a1, a2⟩ := h1.parts
  apply DRow.of_parts
  · rw [← hC, a1, hwt, dInl_congr h hfam ht S hag hch hne htail hcl]
  · intro hf
    obtain ⟨b1, b2⟩ := a2 hf
    obtain ⟨c1, c2⟩ := hSB hf
    rw [← c1, ← c2, b1, b2, dSide_congr h hfam ht S hag hch hf, dBl_congr h hfam ht S hag hch hf]
    exact ⟨rfl, rfl⟩

end Congr

/-! ## The full evaluation -/

theorem evalStep_sizes (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (width : Array (Option Nat)) (affected : Array Bool) (st : DictEval) (t : Nat) :
    (evalStep dag family spineLen tail width affected st t).cost.size = st.cost.size ∧
      (evalStep dag family spineLen tail width affected st t).sides.size = st.sides.size ∧
      (evalStep dag family spineLen tail width affected st t).below.size = st.below.size := by
  unfold evalStep
  split
  · simp only
    split
    · simp
    · simp
  · exact ⟨rfl, rfl, rfl⟩

section Full

variable {p : Prep} (h : DagOK p.dag)
  (hfam : ∀ t, t < p.dag.size → p.family[t]! = (p.dag.node t).head.family)
  (hS : ∀ t, t < p.dag.size → SpineRow p.dag p.family (fun _ => true) p.spineLen p.tail t)

include h hfam hS in
/-- One evaluation step keeps the rows below it and establishes its own, when
the rows below it hold. -/
theorem step_rows {width : Array (Option Nat)} {aff : Array Bool} {st : DictEval} {m : Nat}
    (hm : m < p.dag.size) (haff : aff[m]! = true) (hsz : ESize p.dag.size st)
    (hrows : ∀ t, t < m → DRow p (widthOf width) (st.cost[·]!) (st.sides[·]!) (st.below[·]!) t) :
    let st' := evalStep p.dag p.family p.spineLen p.tail width aff st m
    ESize p.dag.size st' ∧
      ∀ t, t ≤ m → DRow p (widthOf width) (st'.cost[·]!) (st'.sides[·]!) (st'.below[·]!) t := by
  intro st'
  obtain ⟨hsz', hget⟩ := evalStep_get p.dag p.family p.spineLen p.tail width aff st hsz hm
  refine ⟨hsz', fun t ht => ?_⟩
  -- the readers of the new state agree with the old ones off `m`
  have hlo : ∀ u, u ≠ m → st'.cost[u]! = st.cost[u]! ∧ st'.sides[u]! = st.sides[u]! ∧
      st'.below[u]! = st.below[u]! := by
    intro u hu
    have := hget u
    rw [ite_eq_right hu] at this
    unfold eget at this
    simp only [Prod.mk.injEq] at this
    exact this
  have htn : t < p.dag.size := by omega
  -- the set of terms below `t`
  have hag : ∀ u, u < t → st.cost[u]! = st'.cost[u]! ∧ st.sides[u]! = st'.sides[u]! ∧
      st.below[u]! = st'.below[u]! ∧ widthOf width u = widthOf width u := by
    intro u hu
    obtain ⟨a, b, c⟩ := hlo u (by omega)
    exact ⟨a.symm, b.symm, c.symm, rfl⟩
  have hch : ∀ c ∈ (p.dag.node t).children, c < t := fun c hc => h.child_lt htn hc
  have hne : ∀ u, u < t → u ≠ t := fun u hu => by omega
  have htail : p.family[t]! ≠ .none → p.tail[t]! < t := fun hf =>
    (tail_desc h hfam hS t htn hf).lt h htn
  have hcl : ∀ u v, u < t → p.family[u]! ≠ .none → st.below[u]! = some v →
      v < t ∧ p.family[v]! ≠ .none := by
    intro u v hu hfu huv
    obtain ⟨a, _⟩ := dLinkBelow h hfam m (by omega) hrows u (by omega) hfu v huv
    obtain ⟨a1, a2, _⟩ := DSp.props h hfam hS (by omega) a
    exact ⟨by omega, by rw [a2]; exact hfu⟩
  by_cases htm : t = m
  · subst htm
    have hrow := hget t
    rw [ite_eq_left rfl, ite_eq_left haff, evalRowG_eq] at hrow
    unfold eget at hrow
    simp only [Prod.mk.injEq] at hrow
    obtain ⟨r1, r2, r3⟩ := hrow
    apply DRow.of_parts
    · rw [r1, dInl_congr h hfam htn (fun u => u < t) hag hch hne htail hcl]
    · intro hf
      rw [ite_eq_right hf] at r2 r3
      rw [r2, r3, dSide_congr h hfam htn (fun u => u < t) hag hch hf,
        dBl_congr h hfam htn (fun u => u < t) hag hch hf]
      exact ⟨rfl, rfl⟩
  · obtain ⟨a, b, c⟩ := hlo t htm
    exact (hrows t (by omega)).congrS h hfam htn (fun u => u < t) hag hch hne htail hcl rfl a.symm
      (fun _ => ⟨b.symm, c.symm⟩)

include h hfam hS in
/-- **The full evaluation** satisfies the dictionary recurrence at every term. -/
theorem eval_rows (width : Array (Option Nat)) (aff : Array Bool)
    (haff : ∀ t, t < p.dag.size → aff[t]! = true) (init : DictEval) (hsz : ESize p.dag.size init) :
    let ev := evalFrom p.dag p.family p.spineLen p.tail init width aff
    ESize p.dag.size ev ∧
      ∀ t, t < p.dag.size → DRow p (widthOf width) (ev.cost[·]!) (ev.sides[·]!) (ev.below[·]!) t := by
  intro ev
  have key : ∀ m, m ≤ p.dag.size →
      let st := foldRange (evalStep p.dag p.family p.spineLen p.tail width aff) 0 m
        { init with work := 0 }
      ESize p.dag.size st ∧
        ∀ t, t < m → DRow p (widthOf width) (st.cost[·]!) (st.sides[·]!) (st.below[·]!) t := by
    intro m
    induction m with
    | zero => intro _; exact ⟨hsz, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨hs, hr⟩ := ih (by omega)
      simp only at hs hr ⊢
      rw [Ix.Sharing.Exact.LocalSearch.foldRange_succ, Nat.zero_add]
      obtain ⟨a, b⟩ := step_rows h hfam hS (by omega) (haff m (by omega)) hs hr
      exact ⟨a, fun t ht => b t (by omega)⟩
  exact key p.dag.size (Nat.le_refl _)

include h hfam in
/-- A dictionary link leads down the full spine, for rows that hold on a set
of terms closed under spine successors. -/
theorem dLinkGood {wd : Nat → Option Nat} {dC dS : Nat → Nat} {dB : Nat → Option Nat}
    (Good : Nat → Prop) (hG1 : ∀ y, Good y → y < p.dag.size ∧ DRow p wd dC dS dB y)
    (hG2 : ∀ y, Good y → p.family[y]! ≠ .none → Good (nx p y)) :
    ∀ x, Good x → p.family[x]! ≠ .none → ∀ v, dB x = some v →
      DSp p x v ∧ (wd v).isSome = true := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro hx hf v hv
    obtain ⟨hxn, hrow⟩ := hG1 x hx
    have hn := nx_lt h hfam hxn hf
    rw [(hrow.parts.2 hf).2] at hv
    unfold dBl at hv
    by_cases hs : p.family[nx p x]! = p.family[x]!
    · rw [ite_eq_left hs] at hv
      by_cases hw : (wd (nx p x)).isSome = true
      · rw [ite_eq_left hw] at hv
        cases hv
        exact ⟨.one hf hs, hw⟩
      · rw [ite_eq_right hw] at hv
        have hfn : p.family[nx p x]! ≠ .none := by rw [hs]; exact hf
        obtain ⟨a, b⟩ := ih _ hn (hG2 x hx hf) hfn v hv
        exact ⟨.step hf hs a, b⟩
    · rw [ite_eq_right hs] at hv
      cases hv

include h hfam hS in
/-- **The closure evaluation.** Folding `evalStep` with widths `W` over a
strictly increasing list of terms `Cl` that is closed upward (every term with
a descendant in it is in it), from an evaluation whose rows hold with widths
`W₀` that agree with `W` outside `Cl`, gives rows that hold with `W` at every
term. -/
theorem closure_rows (W0 W : Array (Option Nat)) (aff : Array Bool)
    (haff : ∀ t, t < p.dag.size → aff[t]! = true) (base : DictEval)
    (hbsz : ESize p.dag.size base)
    (hbase : ∀ t, t < p.dag.size →
      DRow p (widthOf W0) (base.cost[·]!) (base.sides[·]!) (base.below[·]!) t)
    (Cl : List Nat) (hsorted : Cl.Pairwise (· < ·)) (hlt : ∀ x ∈ Cl, x < p.dag.size)
    (hup : ∀ t u, t < p.dag.size → Desc p.dag t u → u ∈ Cl → t ∈ Cl)
    (hW : ∀ u, u < p.dag.size → u ∉ Cl → widthOf W u = widthOf W0 u) :
    let E := Cl.foldl (evalStep p.dag p.family p.spineLen p.tail W aff) base
    ESize p.dag.size E ∧
      ∀ t, t < p.dag.size → DRow p (widthOf W) (E.cost[·]!) (E.sides[·]!) (E.below[·]!) t := by
  intro E
  -- descendants of a term outside `Cl` are outside it
  have hout : ∀ t u, t < p.dag.size → t ∉ Cl → Desc p.dag t u → u ∉ Cl :=
    fun t u ht htn hd hu => htn (hup t u ht hd hu)
  -- a term outside `Cl` has the rows of the base evaluation with `W`
  have hbaseW : ∀ t, t < p.dag.size → t ∉ Cl →
      DRow p (widthOf W) (base.cost[·]!) (base.sides[·]!) (base.below[·]!) t := by
    intro t ht htn
    refine (hbase t ht).congrS h hfam ht (fun u => Desc p.dag t u) ?_ (fun c hc => .child hc)
      (fun u hu => by have := hu.lt h ht; omega) (fun hf => tail_desc h hfam hS t ht hf) ?_
      (hW t ht htn).symm rfl (fun _ => ⟨rfl, rfl⟩)
    · intro u hu
      have hun := hu.lt h ht
      exact ⟨rfl, rfl, rfl, (hW u (by omega) (hout t u ht htn hu)).symm⟩
    · intro u v hu hfu huv
      have hun := hu.lt h ht
      obtain ⟨a, _⟩ := dLink h hfam hbase u (by omega) hfu v huv
      exact ⟨hu.trans' (DSp.desc h hfam (by omega) a),
        by rw [(DSp.props h hfam hS (by omega) a).2.1]; exact hfu⟩
  -- the fold, by the list still to process
  have key : ∀ (R : List Nat) (st : DictEval), ESize p.dag.size st → R.Pairwise (· < ·) →
      (∀ x ∈ R, x ∈ Cl) → (∀ x ∈ Cl, x ∉ R → ∀ y ∈ R, x < y) →
      (∀ t, t < p.dag.size → t ∉ R →
        DRow p (widthOf W) (st.cost[·]!) (st.sides[·]!) (st.below[·]!) t) →
      let E' := R.foldl (evalStep p.dag p.family p.spineLen p.tail W aff) st
      ESize p.dag.size E' ∧
        ∀ t, t < p.dag.size → DRow p (widthOf W) (E'.cost[·]!) (E'.sides[·]!) (E'.below[·]!) t := by
    intro R
    induction R with
    | nil => intro st hs _ _ _ hr; exact ⟨hs, fun t ht => hr t ht List.not_mem_nil⟩
    | cons c R ih =>
      intro st hs hsort hsub hord hr
      have hcCl := hsub c List.mem_cons_self
      have hcn := hlt c hcCl
      have hlow : ∀ t, t < c → DRow p (widthOf W) (st.cost[·]!) (st.sides[·]!) (st.below[·]!) t := by
        intro t htc
        apply hr t (by omega)
        intro hm
        rcases List.mem_cons.mp hm with rfl | hm
        · omega
        · have := (List.pairwise_cons.mp hsort).1 t hm; omega
      obtain ⟨hs', hrow'⟩ := step_rows h hfam hS hcn (haff c hcn) hs hlow
      simp only [List.foldl_cons]
      apply ih _ hs' (List.pairwise_cons.mp hsort).2 (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
      · intro x hx hxR y hy
        by_cases hxc : x = c
        · subst hxc; exact (List.pairwise_cons.mp hsort).1 y hy
        · exact hord x hx (fun hm => by
            rcases List.mem_cons.mp hm with h' | h'
            · exact hxc h'
            · exact hxR h') y (List.mem_cons_of_mem _ hy)
      · intro t ht htR
        by_cases htc : t ≤ c
        · exact hrow' t htc
        · -- above `c` and processed: outside `Cl`
          have htR' : t ∉ c :: R := fun hm => by
            rcases List.mem_cons.mp hm with rfl | hm
            · omega
            · exact htR hm
          have htCl : t ∉ Cl := fun hm => by
            have := hord t hm htR' c List.mem_cons_self; omega
          have hrt := hr t ht htR'
          obtain ⟨_, hget⟩ := evalStep_get p.dag p.family p.spineLen p.tail W aff st hs hcn
          have hlo : ∀ u, u ≠ c →
              (evalStep p.dag p.family p.spineLen p.tail W aff st c).cost[u]! = st.cost[u]! ∧
              (evalStep p.dag p.family p.spineLen p.tail W aff st c).sides[u]! = st.sides[u]! ∧
              (evalStep p.dag p.family p.spineLen p.tail W aff st c).below[u]! = st.below[u]! := by
            intro u hu
            have := hget u
            rw [ite_eq_right hu] at this
            unfold eget at this
            simp only [Prod.mk.injEq] at this
            exact this
          have hcd : ∀ u, Desc p.dag t u → u ≠ c := fun u hu huc => by
            subst huc; exact hout t u ht htCl hu hcCl
          obtain ⟨a, b, cc⟩ := hlo t (by omega)
          refine hrt.congrS h hfam ht (fun u => Desc p.dag t u) ?_ (fun c hc => .child hc)
            (fun u hu => by have := hu.lt h ht; omega) (fun hf => tail_desc h hfam hS t ht hf) ?_
            rfl a.symm (fun _ => ⟨b.symm, cc.symm⟩)
          · intro u hu
            obtain ⟨a, b, c⟩ := hlo u (hcd u hu)
            exact ⟨a.symm, b.symm, c.symm, rfl⟩
          · intro u v hu hfu huv
            have hun := hu.lt h ht
            have huCl : u ∉ Cl := hout t u ht htCl hu
            obtain ⟨a, _⟩ := dLinkGood h hfam (fun y => y < p.dag.size ∧ y ∉ Cl ∧ y ∉ c :: R)
              (fun y hy => ⟨hy.1, hr y hy.1 hy.2.2⟩)
              (fun y hy hfy => by
                have hyn := nx_lt h hfam hy.1 hfy
                have hnCl : nx p y ∉ Cl := hout y (nx p y) hy.1 hy.2.1
                  (.child (nx_mem h hfam hy.1 hfy))
                exact ⟨by omega, hnCl, fun hm => hnCl (hsub _ hm)⟩)
              u ⟨by omega, huCl, fun hm => huCl (hsub _ hm)⟩ hfu v huv
            exact ⟨hu.trans' (DSp.desc h hfam (by omega) a),
              by rw [(DSp.props h hfam hS (by omega) a).2.1]; exact hfu⟩
  exact key Cl base hbsz hsorted (fun x hx => hx) (fun x hx hxn => absurd hx hxn)
    (fun t ht htn => hbaseW t ht htn)

end Full

end Ix.Sharing.Exact.AreaProof

end
