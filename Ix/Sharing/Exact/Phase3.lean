/-
  Exact minimum sharing: re-evaluation after one dictionary change, marked
  by a walk up the parent lists.

  `Prep.evalUp ev width t` re-evaluates `t` and every term above it after
  the dictionary changed only at `t`: it marks the terms of `[t, n)` that
  have `t` among their descendants (`ancestorMarks`, which tests the
  children of every term of the range) and re-evaluates the marked ones in
  increasing ID. `Prep.evalUpFast` marks the same terms by a walk up the
  parent lists from `t` (`ancWalk`: work proportional to the ancestors of
  `t` and their parent edges) and re-evaluates them in the same order
  (`evalMarked`), so the evaluation, its work count included, is the same.

  `Prep.evalUpFast_eq` proves it equal to `evalUp` for every DAG whose
  children precede their parents, given the parent lists
  `parentEdgeLists dag` and a cleared mark array, which it returns cleared.
  If the walk runs out of fuel, `evalUpFast` runs `evalUp`.
-/
module

public import Ix.Sharing.Exact.Dictionary
import all Ix.Sharing.Exact.Basic
import all Ix.Sharing.Exact.Dag
import all Ix.Sharing.Exact.Dictionary

public section

namespace Ix.Sharing.Exact

/-! ## Evaluation of one term -/

/-- `evalStep` at a term whose `affected` mark is set, with the evaluation
taken apart first so that its arrays are updated in place
(`evalStep_eq_evalNode`). -/
def evalNode (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (width : Array (Option Nat)) (st : DictEval) (t : Nat) : DictEval :=
  match st with
  | ⟨cost, sides, below, work⟩ =>
    let node := dag.node t
    let fam := family[t]!
    if fam == .none then
      let inl := node.children.foldl (fun acc c => acc + cost[c]!) node.head.ownBytes
      let c := match widthOf width t with
        | some w => min inl w
        | none => inl
      ⟨cost.set! t c, sides, below, work + 1⟩
    else
      let nxt := node.spineNext
      let same := family[nxt]! == fam
      let s := node.sideExtra + cost[node.sideChild]! + (if same then sides[nxt]! else 0)
      let bl : Option Nat :=
        if same then (if (widthOf width nxt).isSome then some nxt else below[nxt]!)
        else none
      let l := spineLen[t]!
      let natural := tag4Size l + s + cost[tail[t]!]!
      let sides := sides.set! t s
      let below := below.set! t bl
      let (inl, work) := cutScan spineLen sides below width l s l bl natural work
      let c := match widthOf width t with
        | some w => min inl w
        | none => inl
      ⟨cost.set! t c, sides, below, work + 1⟩

/-! ## Parent lists and the ancestor walk -/

/-- `parents[c]`: every `u` that has `c` among its children (once per such
child position), in increasing `u`. -/
def parentEdgeLists (dag : Dag) : Array (Array Nat) :=
  foldRange (fun (ps : Array (Array Nat)) u =>
      (dag.node u).children.foldl (fun ps c => ps.modify c (·.push u)) ps)
    0 dag.size (Array.replicate dag.size #[])

/-- Mark and append `u` unless it is marked. -/
@[inline] def ancVisit (acc : Array Bool × Array Nat) (u : Nat) : Array Bool × Array Nat :=
  match acc with
  | (mark, out) => if mark[u]! then (mark, out) else (mark.set! u true, out.push u)

/-- Walk up the parent lists: visit the parents of `out[k]`, `out[k+1]`, …
until every listed term is visited (`true`) or the fuel runs out
(`false`). -/
def ancWalk (parents : Array (Array Nat)) :
    Nat → Nat → Array Bool → Array Nat → Bool × Array Bool × Array Nat
  | 0, _, mark, out => (false, mark, out)
  | fuel + 1, k, mark, out =>
    if h : k < out.size then
      match (parents[out[k]]?.getD #[]).foldl ancVisit (mark, out) with
      | (mark, out) => ancWalk parents fuel (k + 1) mark out
    else (true, mark, out)

/-- Clear the marks of `s`. -/
def unmark (mark : Array Bool) (s : Array Nat) : Array Bool :=
  s.foldl (fun m u => m.set! u false) mark

/-! ## The work of a re-evaluation, counted without evaluating

After the dictionary gains `t`, `Prep.evalUp` re-evaluates `t` and every term
above it, and counts for each of them 1 plus, for a telescope term, one per
available term strictly below it on its spine (the internal cuts `cutScan`
visits). `ancestorWork` counts the same from a walk up the parent lists and a
table of those spine counts, which `spineAdd` keeps up to date. -/

/-- `sp[x]`: the telescope terms whose spine continues into `x` (same family,
`x` their spine successor), each listed once. -/
def spineParentLists (dag : Dag) (family : Array Family) : Array (Array Nat) :=
  foldRange (fun (sp : Array (Array Nat)) u =>
      let fam := family[u]!
      let nxt := (dag.node u).spineNext
      if fam != .none && family[nxt]! == fam then sp.modify nxt (·.push u) else sp)
    0 dag.size (Array.replicate dag.size #[])

/-- Add one to the spine count of every term above `x` along spine-parent
links (a depth-first walk with a stack); `none` if the fuel runs out. -/
def spineAddGo (sp : Array (Array Nat)) : Nat → List Nat → Array Nat → Option (Array Nat)
  | _, [], sc => some sc
  | 0, _ :: _, _ => none
  | fuel + 1, x :: stack, sc =>
    spineAddGo sp fuel ((sp[x]?.getD #[]).toList ++ stack) (sc.modify x (· + 1))

/-- `sc` after `t` became available: every term with `t` strictly below it on
its spine counts one more. -/
def spineAdd (sp : Array (Array Nat)) (sc : Array Nat) (t : Nat) : Option (Array Nat) :=
  spineAddGo sp (sc.size + 1) (sp[t]?.getD #[]).toList sc

/-- The walk of `ancestorWork`: the parents of `queue[k]` from position `j`
on are next; each term not yet marked with `epoch` is marked, queued and adds
1 plus its spine count to `sum`. `none` when the fuel runs out. -/
def awGo (parents : Array (Array Nat)) (sc : Array Nat) (epoch : Nat) :
    Nat → Nat → Nat → Array Nat → Array Nat → Nat → Option (Nat × Array Nat × Array Nat)
  | 0, _, _, _, _, _ => none
  | fuel + 1, k, j, mark, queue, sum =>
    if hk : k < queue.size then
      let ps := parents[queue[k]]?.getD #[]
      if hj : j < ps.size then
        let u := ps[j]
        if mark[u]! == epoch then awGo parents sc epoch fuel k (j + 1) mark queue sum
        else awGo parents sc epoch fuel k (j + 1) (mark.set! u epoch) (queue.push u)
          (sum + 1 + sc[u]!)
      else awGo parents sc epoch fuel (k + 1) 0 mark queue sum
    else some (sum, mark, queue)

/-- The work `Prep.evalUp` counts after `t` became available: 1 per term at
or above `t` plus its spine count, from a walk up the parent lists that marks
with `epoch` (every mark must be below it) and reuses the queue array. -/
def ancestorWork (parents : Array (Array Nat)) (sc : Array Nat) (epoch t fuel : Nat)
    (mark queue : Array Nat) : Option (Nat × Array Nat × Array Nat) :=
  awGo parents sc epoch fuel 0 0 (mark.set! t epoch) ((queue.shrink 0).push t) (1 + sc[t]!)

/-- Evaluate the marked terms of `[t, n)` in increasing ID (`evalMarked_eq`:
`foldRange` of `evalStep` with the marks as the affected terms). -/
def evalMarked (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (width : Array (Option Nat)) (mark : Array Bool) (t n : Nat) (st : DictEval) : DictEval :=
  foldRange (fun st u => if mark[u]! then evalNode dag family spineLen tail width st u else st)
    t (n - t) st

/-- `Prep.evalUp` with the ancestors of `t` marked by a walk up the parent
lists instead of a scan of `[t, n)` (`evalUpFast_eq`), given the parent lists
and a cleared mark array, which is returned cleared. -/
def Prep.evalUpFast (p : Prep) (parents : Array (Array Nat)) (ev : DictEval)
    (width : Array (Option Nat)) (t : Nat) (mark : Array Bool) : DictEval × Array Bool :=
  match ancWalk parents (p.dag.size + 1) 0 (mark.set! t true) #[t] with
  | (done, mark, out) =>
    if done then
      (evalMarked p.dag p.family p.spineLen p.tail width mark t p.dag.size { ev with work := 0 },
        unmark mark out)
    else (p.evalUp ev width t, Array.replicate p.dag.size false)

/-! ## Proofs -/

theorem evalStep_eq_evalNode (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (width : Array (Option Nat)) (affected : Array Bool) (st : DictEval) (t : Nat) :
    evalStep dag family spineLen tail width affected st t =
      if affected[t]! then evalNode dag family spineLen tail width st t else st := by
  cases st
  unfold evalStep evalNode
  rfl

theorem evalMarked_eq (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (width : Array (Option Nat)) (mark : Array Bool) (t n : Nat) (st : DictEval) :
    evalMarked dag family spineLen tail width mark t n st =
      foldRange (evalStep dag family spineLen tail width mark) t (n - t) st := by
  unfold evalMarked
  congr 1

/-- Induction over `foldRange`. -/
theorem foldRange_induction {σ : Type} (f : σ → Nat → σ) (P : Nat → σ → Prop) :
    ∀ (i k : Nat) (st : σ), P k st → (∀ j s, k ≤ j → j < k + i → P j s → P (j + 1) (f s j)) →
      P (k + i) (foldRange f k i st)
  | 0, k, st, h0, _ => by simpa [foldRange] using h0
  | i + 1, k, st, h0, hs => by
    have h1 : P (k + 1) (f st k) := hs k st (Nat.le_refl _) (by omega) h0
    have := foldRange_induction f P i (k + 1) (f st k) h1
      (fun j s hj hj' hp => hs j s (by omega) (by omega) hp)
    simpa [foldRange, Nat.add_assoc, Nat.add_comm 1 i] using this

/-- `u` is `t` or has `t` below it. -/
inductive AncOf (dag : Dag) (t : Nat) : Nat → Prop
  | refl : AncOf dag t t
  | step {c u : Nat} : AncOf dag t c → c ∈ (dag.node u).children → AncOf dag t u

theorem dag_node_of_lt {dag : Dag} {u : Nat} (hu : u < dag.size) : dag.node u = dag.nodes[u] := by
  simp [Dag.node, Dag.size] at hu ⊢
  simp [hu]

theorem child_lt_of_childrenPrecede {dag : Dag} (hcp : childrenPrecede dag.nodes = true)
    {u c : Nat} (hu : u < dag.size) (hc : c ∈ (dag.node u).children) : c < u := by
  unfold childrenPrecede at hcp
  rw [Array.all_eq_true] at hcp
  have := hcp u (by simpa [Array.size_zipIdx, Dag.size] using hu)
  simp only [Array.getElem_zipIdx, Nat.zero_add] at this
  rw [Array.all_eq_true'] at this
  rw [dag_node_of_lt hu] at hc
  simpa using this c hc

theorem AncOf.le {dag : Dag} (hcp : childrenPrecede dag.nodes = true) {t u : Nat}
    (h : AncOf dag t u) (hu : u < dag.size) : t ≤ u := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ hc ih =>
    have := child_lt_of_childrenPrecede hcp hu hc
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt (ih (by omega)) this)

theorem AncOf.iff {dag : Dag} {t u : Nat} :
    AncOf dag t u ↔ u = t ∨ ∃ c ∈ (dag.node u).children, AncOf dag t c := by
  constructor
  · intro h
    cases h with
    | refl => exact Or.inl rfl
    | step hc hm => exact Or.inr ⟨_, hm, hc⟩
  · rintro (rfl | ⟨c, hm, hc⟩)
    · exact .refl
    · exact .step hc hm

theorem ancestorMarks_spec {dag : Dag} (hcp : childrenPrecede dag.nodes = true) {t : Nat}
    (ht : t < dag.size) :
    (ancestorMarks dag t).size = dag.size ∧
      ∀ u, (ancestorMarks dag t)[u]! = true ↔ (u < dag.size ∧ AncOf dag t u) := by
  let P : Nat → Array Bool → Prop := fun j acc =>
    acc.size = dag.size ∧ ∀ u, acc[u]! = true ↔ (u < j ∧ u < dag.size ∧ AncOf dag t u)
  have h0 : P t (Array.replicate dag.size false) := by
    refine ⟨by simp, fun u => ?_⟩
    constructor
    · intro h
      by_cases hu : u < dag.size
      · simp [getElem!_pos, hu] at h
      · simp [getElem!_neg, hu] at h
    · rintro ⟨hut, hu, ha⟩
      exact absurd (ha.le hcp hu) (by omega)
  have := foldRange_induction (fun (acc : Array Bool) u =>
      acc.set! u (u == t || (dag.node u).children.any (acc[·]!))) P (dag.size - t) t _ h0
    (by
      intro j acc hj hj' ⟨hsz, hacc⟩
      have hjn : j < dag.size := by omega
      refine ⟨by simp [Array.set!_eq_setIfInBounds, hsz], fun u => ?_⟩
      rw [getElem!_setBang]
      by_cases huj : u = j
      · subst huj
        rw [ite_eq_left ⟨rfl, by rw [hsz]; exact hjn⟩]
        simp only [Bool.or_eq_true, beq_iff_eq, Array.any_eq_true', hacc]
        constructor
        · rintro (rfl | ⟨c, hm, _, _, hc⟩)
          · exact ⟨by omega, hjn, .refl⟩
          · exact ⟨by omega, hjn, .step hc hm⟩
        · rintro ⟨_, _, ha⟩
          rcases AncOf.iff.mp ha with h | ⟨c, hm, hc⟩
          · exact Or.inl h
          · have hcu := child_lt_of_childrenPrecede hcp hjn hm
            exact Or.inr ⟨c, hm, hcu, by omega, hc⟩
      · simp only [huj, false_and, ite_false, hacc]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩)
  have heq : t + (dag.size - t) = dag.size := by omega
  rw [heq] at this
  obtain ⟨hsz, hm⟩ := this
  unfold ancestorMarks
  refine ⟨hsz, fun u => ?_⟩
  rw [hm]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨h1, h2⟩; exact ⟨h1, h1, h2⟩

/-! ### The parent lists -/

/-- `parents[c]` lists exactly the terms with `c` among their children. -/
def ParentsOK (dag : Dag) (parents : Array (Array Nat)) : Prop :=
  ∀ c, c < dag.size → ∀ p, p ∈ (parents[c]?.getD #[]) ↔ (p < dag.size ∧ c ∈ (dag.node p).children)

theorem modify_push_fold (u : Nat) :
    ∀ (l : List Nat) (ps : Array (Array Nat)),
      (l.foldl (fun ps c => ps.modify c (·.push u)) ps).size = ps.size ∧
      ∀ c p, p ∈ ((l.foldl (fun ps c => ps.modify c (·.push u)) ps)[c]?.getD #[]) ↔
        (p ∈ (ps[c]?.getD #[]) ∨ (p = u ∧ c ∈ l ∧ c < ps.size))
  | [], ps => ⟨rfl, fun c p => by simp⟩
  | d :: l, ps => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := modify_push_fold u l (ps.modify d (·.push u))
    rw [Array.size_modify] at h1
    refine ⟨h1, fun c p => ?_⟩
    rw [h2, Array.getElem?_modify, Array.size_modify, List.mem_cons]
    by_cases hdc : d = c
    · subst hdc
      rw [ite_eq_left rfl]
      by_cases hd : d < ps.size
      · rw [Array.getElem?_eq_getElem hd]
        simp only [Option.map_some, Option.getD_some, Array.mem_push]
        grind
      · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hd)]
        simp only [Option.map_none]
        grind
    · rw [ite_eq_right hdc]
      grind

theorem parentEdgeLists_ok (dag : Dag) : ParentsOK dag (parentEdgeLists dag) := by
  let P : Nat → Array (Array Nat) → Prop := fun j ps =>
    ps.size = dag.size ∧ ∀ c, c < dag.size → ∀ p,
      p ∈ (ps[c]?.getD #[]) ↔ (p < j ∧ c ∈ (dag.node p).children)
  have h0 : P 0 (Array.replicate dag.size #[]) := by
    refine ⟨by simp, fun c hc p => ?_⟩
    rw [Array.getElem?_replicate]
    split <;> simp
  have := foldRange_induction (fun (ps : Array (Array Nat)) u =>
      (dag.node u).children.foldl (fun ps c => ps.modify c (·.push u)) ps) P dag.size 0 _ h0
    (by
      intro j ps _ hj ⟨hsz, hps⟩
      rw [← Array.foldl_toList]
      obtain ⟨h1, h2⟩ := modify_push_fold j (dag.node j).children.toList ps
      refine ⟨by rw [h1, hsz], fun c hc p => ?_⟩
      rw [h2, hps c hc, Array.mem_toList_iff, hsz]
      constructor
      · rintro (⟨h3, h4⟩ | ⟨rfl, h4, _⟩)
        · exact ⟨by omega, h4⟩
        · exact ⟨by omega, h4⟩
      · rintro ⟨h3, h4⟩
        by_cases hpj : p = j
        · subst hpj; exact Or.inr ⟨rfl, h4, hc⟩
        · exact Or.inl ⟨by omega, h4⟩)
  rw [Nat.zero_add] at this
  obtain ⟨_, hm⟩ := this
  intro c hc p
  unfold parentEdgeLists
  rw [hm c hc p]

/-! ### The ancestor walk -/

/-- Invariant of `ancWalk`: the marks are the listed terms, every listed term
is an ancestor of `t`, and the parents of the first `k` listed terms are
listed. -/
structure WalkInv (dag : Dag) (parents : Array (Array Nat)) (t k : Nat) (mark : Array Bool)
    (out : Array Nat) : Prop where
  size : mark.size = dag.size
  marked : ∀ u, mark[u]! = true ↔ u ∈ out
  anc : ∀ u ∈ out, u < dag.size ∧ AncOf dag t u
  start : t ∈ out
  closed : ∀ j (hj : j < out.size), j < k → ∀ p ∈ (parents[out[j]]?.getD #[]), p ∈ out
  le : k ≤ out.size

theorem ancVisit_pair (mark : Array Bool) (out : Array Nat) (u : Nat) :
    ancVisit (mark, out) u = if mark[u]! then (mark, out) else (mark.set! u true, out.push u) := by
  unfold ancVisit; rfl

theorem ancVisit_fold {dag : Dag} {t : Nat} :
    ∀ (l : List Nat) (mark : Array Bool) (out : Array Nat),
      mark.size = dag.size → (∀ u, mark[u]! = true ↔ u ∈ out) →
      (∀ u ∈ out, u < dag.size ∧ AncOf dag t u) → (∀ p ∈ l, p < dag.size ∧ AncOf dag t p) →
      let r := l.foldl ancVisit (mark, out)
      r.1.size = dag.size ∧ (∀ u, r.1[u]! = true ↔ u ∈ r.2) ∧
        (∀ u ∈ r.2, u < dag.size ∧ AncOf dag t u) ∧ (∀ p ∈ l, p ∈ r.2) ∧
        ∃ l', r.2.toList = out.toList ++ l'
  | [], mark, out, hs, hm, ha, _ => by
    simp only [List.foldl_nil]
    exact ⟨hs, hm, ha, by simp, [], by simp⟩
  | p :: l, mark, out, hs, hm, ha, hl => by
    simp only [List.foldl_cons]
    have hp := hl p (by simp)
    have hl' : ∀ q ∈ l, q < dag.size ∧ AncOf dag t q := fun q hq => hl q (by simp [hq])
    rw [ancVisit_pair]
    by_cases hmp : mark[p]! = true
    · simp only [hmp, ite_true]
      obtain ⟨h1, h2, h3, h4, l', h5⟩ := ancVisit_fold l mark out hs hm ha hl'
      refine ⟨h1, h2, h3, ?_, l', h5⟩
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · rw [Array.mem_def, h5, List.mem_append]
        exact Or.inl (Array.mem_def.mp ((hm q).mp hmp))
      · exact h4 q hq
    · simp only [hmp, Bool.false_eq_true, ite_false]
      have hs' : (mark.set! p true).size = dag.size := by
        simp [Array.set!_eq_setIfInBounds, hs]
      have hm' : ∀ u, (mark.set! p true)[u]! = true ↔ u ∈ out.push p := by
        intro u
        rw [getElem!_setBang, Array.mem_push]
        by_cases hup : u = p
        · subst hup; simp [hs, hp.1]
        · simp [hup, hm u]
      have ha' : ∀ u ∈ out.push p, u < dag.size ∧ AncOf dag t u := by
        intro u hu
        rcases Array.mem_push.mp hu with hu | rfl
        · exact ha u hu
        · exact hp
      obtain ⟨h1, h2, h3, h4, l', h5⟩ := ancVisit_fold l (mark.set! p true) (out.push p) hs' hm' ha' hl'
      refine ⟨h1, h2, h3, ?_, [p] ++ l', by rw [h5, Array.toList_push, List.append_assoc]⟩
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · rw [Array.mem_def, h5, List.mem_append]
        exact Or.inl (by simp [Array.toList_push])
      · exact h4 q hq

theorem ancWalk_spec {dag : Dag} {parents : Array (Array Nat)} {t : Nat}
    (hpar : ParentsOK dag parents) :
    ∀ (fuel k : Nat) (mark : Array Bool) (out : Array Nat) (mark' : Array Bool) (out' : Array Nat),
      WalkInv dag parents t k mark out → ancWalk parents fuel k mark out = (true, mark', out') →
      WalkInv dag parents t out'.size mark' out'
  | 0, _, _, _, _, _, _, h => by simp [ancWalk] at h
  | fuel + 1, k, mark, out, mark', out', hinv, h => by
    unfold ancWalk at h
    split at h
    · rename_i hk
      have hx := hinv.anc out[k] (Array.getElem_mem hk)
      have hl : ∀ p ∈ (parents[out[k]]?.getD #[]).toList, p < dag.size ∧ AncOf dag t p := by
        intro p hp
        have := (hpar out[k] hx.1 p).mp (Array.mem_toList_iff.mp hp)
        exact ⟨this.1, .step hx.2 this.2⟩
      have hf := ancVisit_fold (dag := dag) (t := t) (parents[out[k]]?.getD #[]).toList mark out
        hinv.size hinv.marked hinv.anc hl
      rw [Array.foldl_toList] at hf
      split at h
      rename_i m2 o2 heq
      rw [heq] at hf
      obtain ⟨h1, h2, h3, h4, l', h5⟩ := hf
      have hpre : ∀ j (hj : j < out.size), ∃ hj' : j < o2.size, o2[j] = out[j] := by
        intro j hj
        have hsz : o2.size = out.size + l'.length := by
          rw [← Array.length_toList, h5, List.length_append, Array.length_toList]
        refine ⟨by omega, ?_⟩
        have hj2 : j < out.toList.length := by rw [Array.length_toList]; exact hj
        have h6 : o2[j]? = out[j]? := by
          rw [← Array.getElem?_toList, ← Array.getElem?_toList, h5, List.getElem?_append_left hj2]
        rw [Array.getElem?_eq_getElem hj, Array.getElem?_eq_getElem (by omega)] at h6
        exact Option.some.inj h6
      have hsub : ∀ u ∈ out, u ∈ o2 := by
        intro u hu
        rw [Array.mem_def, h5, List.mem_append]
        exact Or.inl (Array.mem_def.mp hu)
      apply ancWalk_spec hpar fuel (k + 1) m2 o2 mark' out' _ h
      refine ⟨h1, h2, h3, hsub t hinv.start, ?_, ?_⟩
      · intro j hj hjk p hp
        by_cases hjk' : j < k
        · have hjo : j < out.size := Nat.lt_of_lt_of_le hjk' hinv.le
          obtain ⟨_, he⟩ := hpre j hjo
          simp only [he] at hp
          exact hsub p (hinv.closed j hjo hjk' p hp)
        · have hjk : j = k := by omega
          subst hjk
          obtain ⟨_, he⟩ := hpre j hk
          simp only [he] at hp
          exact h4 p (Array.mem_toList_iff.mpr hp)
      · obtain ⟨hj', _⟩ := hpre k hk
        omega
    · rename_i hk
      simp only [Prod.mk.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := h
      exact { hinv with closed := fun j hj _ => hinv.closed j hj (by omega), le := Nat.le_refl _ }

theorem WalkInv.complete {dag : Dag} {parents : Array (Array Nat)} {t : Nat}
    {mark : Array Bool} {out : Array Nat} (hcp : childrenPrecede dag.nodes = true)
    (hpar : ParentsOK dag parents) (hinv : WalkInv dag parents t out.size mark out) :
    ∀ u, u < dag.size → AncOf dag t u → u ∈ out := by
  intro u hu ha
  induction ha with
  | refl => exact hinv.start
  | step hc hm ih =>
    rename_i c v
    have hcv := child_lt_of_childrenPrecede hcp hu hm
    have hco := ih (by omega)
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hco
    exact hinv.closed j hj hj _ ((hpar _ (by omega) v).mpr ⟨hu, hm⟩)

theorem unmark_spec (mark : Array Bool) (s : Array Nat) :
    (unmark mark s).size = mark.size ∧
      ∀ u, (unmark mark s)[u]! = true → mark[u]! = true ∧ u ∉ s := by
  unfold unmark
  rw [← Array.foldl_toList]
  suffices h : ∀ (l : List Nat) (m : Array Bool), (l.foldl (fun m u => m.set! u false) m).size = m.size ∧
      ∀ u, (l.foldl (fun m u => m.set! u false) m)[u]! = true → m[u]! = true ∧ u ∉ l by
    obtain ⟨h1, h2⟩ := h s.toList mark
    exact ⟨h1, fun u hu => by
      obtain ⟨a, b⟩ := h2 u hu
      exact ⟨a, fun hm => b (Array.mem_toList_iff.mpr hm)⟩⟩
  intro l
  induction l with
  | nil => intro m; exact ⟨rfl, fun u hu => ⟨by simpa using hu, by simp⟩⟩
  | cons v l ih =>
    intro m
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (m.set! v false)
    refine ⟨by rw [h1]; simp [Array.set!_eq_setIfInBounds], fun u hu => ?_⟩
    obtain ⟨a, b⟩ := h2 u hu
    rw [getElem!_setBang] at a
    by_cases huv : u = v
    · subst huv
      by_cases hs : u < m.size
      · simp [hs] at a
      · simp only [hs, and_false, ite_false] at a
        rw [getElem!_neg m u hs] at a
        exact absurd a (by decide)
    · simp only [huv, false_and, ite_false] at a
      exact ⟨a, by simp [huv, b]⟩

theorem getElem!_replicate_false (n u : Nat) : (Array.replicate n false)[u]! = false := by
  by_cases hu : u < n
  · rw [getElem!_pos _ _ (by simpa using hu), Array.getElem_replicate]
  · rw [getElem!_neg _ _ (by simpa using hu)]; rfl

/-- Two arrays of the same size whose entries agree under `[·]!`. -/
theorem array_ext_getElem! {α : Type} [Inhabited α] {a b : Array α} (hs : a.size = b.size)
    (h : ∀ u : Nat, a[u]! = b[u]!) : a = b := by
  apply Array.ext hs
  intro i h1 h2
  have := h i
  rwa [getElem!_pos a i h1, getElem!_pos b i h2] at this

theorem Prep.evalUpFast_eq (p : Prep) (ev : DictEval) (width : Array (Option Nat)) (t : Nat)
    (ht : t < p.dag.size) (hcp : childrenPrecede p.dag.nodes = true) :
    p.evalUpFast (parentEdgeLists p.dag) ev width t (Array.replicate p.dag.size false) =
      (p.evalUp ev width t, Array.replicate p.dag.size false) := by
  have hpar := parentEdgeLists_ok p.dag
  have hm0 : WalkInv p.dag (parentEdgeLists p.dag) t 0
      ((Array.replicate p.dag.size false).set! t true) #[t] :=
    { size := by simp [Array.set!_eq_setIfInBounds]
      marked := fun u => by
        rw [getElem!_setBang, Array.mem_singleton]
        by_cases hut : u = t
        · subst hut; simp [ht]
        · simp [hut, getElem!_replicate_false]
      anc := fun u hu => by
        rw [Array.mem_singleton] at hu
        subst hu
        exact ⟨ht, .refl⟩
      start := by simp
      closed := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
      le := Nat.zero_le _ }
  unfold Prep.evalUpFast
  split
  rename_i done mark out heq
  cases done
  · rfl
  · have hinv := ancWalk_spec hpar _ _ _ _ _ _ hm0 heq
    obtain ⟨hasz, hanc⟩ := ancestorMarks_spec hcp ht
    have hiff : ∀ u, mark[u]! = true ↔ (u < p.dag.size ∧ AncOf p.dag t u) := by
      intro u
      rw [hinv.marked u]
      exact ⟨hinv.anc u, fun ⟨h1, h2⟩ => hinv.complete hcp hpar u h1 h2⟩
    have hmark : mark = ancestorMarks p.dag t := by
      apply array_ext_getElem! (by rw [hinv.size, hasz])
      intro u
      rw [Bool.eq_iff_iff, hiff, hanc]
    have hun : unmark mark out = Array.replicate p.dag.size false := by
      obtain ⟨h1, h2⟩ := unmark_spec mark out
      apply array_ext_getElem! (by rw [h1, hinv.size, Array.size_replicate])
      intro u
      rw [getElem!_replicate_false]
      cases hu : (unmark mark out)[u]!
      · rfl
      · obtain ⟨h3, h4⟩ := h2 u hu
        exact absurd ((hinv.marked u).mp h3) h4
    simp only [ite_true]
    rw [evalMarked_eq, hun, hmark]
    rfl

end Ix.Sharing.Exact

end
