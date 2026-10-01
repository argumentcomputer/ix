import Ix.Compile.Verify.UniformTables

/-!
# Stage 4: the component search finds every minimum's choice

The invariant of the explicit-state component search (`solveP`, `solveBody`,
`nodeP`, `splitP`): every table entry is a real set of the group with its
exact `Δ`, and for every minimum respecting a node's decisions the table has
an entry at that minimum's count of the group that is at most its `Δ`.
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Compile.Verify.SharingExact (bind_eq_ok)

/-! ## The setting of one component's search -/

/-- The data of one component's search. -/
structure Env where
  dag : Dag
  roots : Array Nat
  w : Nat
  θ : _root_.Int
  cs : List Nat
  cx : SCtx
  comp : Nat → Nat
  i : Nat

/-- What the search of a component may assume. -/
structure Env.WF (E : Env) : Prop where
  G : GlobalWF E.dag E.roots E.w E.θ E.cs
  cx : SCtxWF E.dag E.roots E.w E.θ E.cs E.cx
  area : AreaWF E.dag E.roots E.cx
  comp : ∀ a b, a < E.dag.size → (ucls E.dag E.roots E.w E.θ)[a]! = .uncertain →
    (ucls E.dag E.roots E.w E.θ)[b]! = .uncertain →
    NReach (Prep.ofDag E.dag) (E.cx.up.opaq[·]!) a b → E.comp a = E.comp b
  memi : ∀ t, t < E.dag.size → (ucls E.dag E.roots E.w E.θ)[t]! = .uncertain →
    (t ∈ E.cx.members.toList ↔ E.comp t = E.i)
  slack : E.cx.slack = tag0Size (E.cs.length + (uunc E.dag E.roots E.w E.θ).length) -
    tag0Size E.cs.length

/-- The change of the component cost from adding `S` to `I`. -/
def Env.delta (E : Env) (I S : List Nat) : _root_.Int :=
  (scost E.cx E.dag (I ++ S) : _root_.Int) - (scost E.cx E.dag I : _root_.Int)

/-- `Y` is a minimum storing `I` and not `O`. -/
def Env.Cons (E : Env) (Y I O : List Nat) : Prop :=
  IsMinimum E.dag E.w E.roots Y ∧ (∀ t ∈ I, t ∈ Y) ∧ (∀ t ∈ O, t ∉ Y)

/-- The part of `Y` in `g`. -/
def partOf (Y g : List Nat) : List Nat := g.filter (fun t => decide (t ∈ Y))

/-- Every entry is a duplicate-free set of `g`'s terms with its exact `Δ`. -/
def Env.TabOK (E : Env) (g I : List Nat) (tb : CTable) : Prop :=
  Entries tb (fun e => e.2.toList.Pairwise (· < ·) ∧ (∀ x ∈ e.2.toList, x ∈ g) ∧
    e.1 = E.delta I e.2.toList)

/-- Every minimum respecting `(I, O)` has an entry at its count of `g`, at most
its `Δ`. -/
def Env.Covers (E : Env) (g I O : List Nat) (tb : CTable) : Prop :=
  ∀ Y, E.Cons Y I O → HasAtT tb (partOf Y g).length (E.delta I (partOf Y g)) (partOf Y g)

/-- A group's reduced context: separated, duplicate-free, of members. -/
def Env.GroupCtx (E : Env) (g I O : Array Nat) : Prop :=
  strictInc g = true ∧ strictInc I = true ∧ strictInc O = true ∧
    E.cx.sepCheck g I O = true ∧ (∀ t ∈ I.toList, t ∈ E.cx.members.toList) ∧
    (∀ t ∈ O.toList, t ∈ E.cx.members.toList) ∧ (∀ t ∈ I.toList, t ∉ O.toList)

/-- The memo holds valid tables of their keys' contexts. -/
def Env.MemoOK (E : Env) (memo : Std.HashMap (Array Nat × Array Nat) CTable) : Prop :=
  ∀ g ent tb, memo.get? (g, ent) = some tb →
    E.GroupCtx g (keyContext ent).1 (keyContext ent).2 ∧
      E.TabOK g.toList (keyContext ent).1.toList tb ∧
      E.Covers g.toList (keyContext ent).1.toList (keyContext ent).2.toList tb

/-! ## Basic facts -/

theorem scost_perm {cx : SCtx} {dag : Dag} {V V' : List Nat} (h : V.Perm V') :
    scost cx dag V = scost cx dag V' := by
  unfold scost; exact compCost_perm h

theorem Env.delta_perm (E : Env) {I S S' : List Nat} (h : S.Perm S') :
    E.delta I S = E.delta I S' := by
  unfold Env.delta
  rw [scost_perm (List.Perm.append_left I h)]

theorem chargeP_memo {limits : Limits} {work : Nat} {st st' : SState}
    (h : chargeP limits work st = .ok st') : st'.memo = st.memo := by
  unfold chargeP at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

/-- The step of `pickBranch`. -/
def branchStep (acc : Option (Nat × _root_.Int)) (x : Nat × _root_.Int) : Option (Nat × _root_.Int) :=
  match acc with
  | none => some (x.1, x.2)
  | some (a, ga) =>
    if x.2.natAbs > ga.natAbs || (x.2.natAbs == ga.natAbs && x.1 < a) then some (x.1, x.2) else acc

theorem pickBranch_eq (l : Array (Nat × _root_.Int)) : pickBranch l = l.toList.foldl branchStep none := by
  unfold pickBranch
  rw [← Array.foldl_toList]
  rfl

theorem pickFold_mem : ∀ (L : List (Nat × _root_.Int)) (acc : Option (Nat × _root_.Int))
    (x : Nat × _root_.Int), L.foldl branchStep acc = some x → acc = some x ∨ x ∈ L
  | [], _, _, h => Or.inl h
  | y :: L, acc, x, h => by
    rw [List.foldl_cons] at h
    rcases pickFold_mem L _ x h with h' | h'
    · cases acc with
      | none => simp only [branchStep, Option.some.injEq] at h'; exact Or.inr (by rw [← h']; simp)
      | some a =>
        obtain ⟨a, ga⟩ := a
        simp only [branchStep] at h'
        split at h'
        · simp only [Option.some.injEq] at h'; exact Or.inr (by rw [← h']; simp)
        · exact Or.inl h'
    · exact Or.inr (List.mem_cons_of_mem _ h')

theorem pickFold_some : ∀ (L : List (Nat × _root_.Int)) (acc : Option (Nat × _root_.Int)),
    (acc ≠ none ∨ L ≠ []) → L.foldl branchStep acc ≠ none
  | [], acc, h => by
    rcases h with h | h
    · exact h
    · exact absurd rfl h
  | y :: L, acc, _ => by
    rw [List.foldl_cons]
    apply pickFold_some L
    left
    cases acc with
    | none => simp [branchStep]
    | some a =>
      obtain ⟨a, ga⟩ := a
      simp only [branchStep]
      split <;> simp

theorem pickBranch_mem {l : Array (Nat × _root_.Int)} {x : Nat × _root_.Int}
    (h : pickBranch l = some x) : x ∈ l.toList := by
  rw [pickBranch_eq] at h
  rcases pickFold_mem _ _ _ h with h | h
  · cases h
  · exact h

theorem pickBranch_isSome {l : Array (Nat × _root_.Int)} (h : l.toList ≠ []) :
    pickBranch l ≠ none := by
  rw [pickBranch_eq]
  exact pickFold_some _ _ (Or.inr h)

/-! ## Groups: shifting the base, pruning, trimming -/

theorem Env.WF.θ1 {E : Env} (hE : E.WF) : 1 ≤ E.θ := by
  rcases hE.G.theta with h | ⟨h, _⟩ <;> omega

theorem Env.WF.csc {E : Env} (hE : E.WF) :
    ∀ t ∈ E.cs, t < E.dag.size ∧ (ucls E.dag E.roots E.w E.θ)[t]! = .certainStored :=
  fun t ht => (hE.G.mem_cs t).mp ht

/-- **Shifting the base of a group.** Under the group's reduced context, the
`Δ` of a part of the group is the same from any duplicate-free base of
members that contains the context's stored terms and avoids the group and the
context's unstored terms. -/
theorem Env.delta_shift {E : Env} (hE : E.WF) {h Ih Oh : Array Nat} (hctx : E.GroupCtx h Ih Oh)
    {B S : List Nat} (hBn : B.Nodup) (hIB : ∀ t ∈ Ih.toList, t ∈ B)
    (hBm : ∀ t ∈ B, t ∈ E.cx.members.toList) (hBh : ∀ t ∈ B, t ∉ h.toList)
    (hBO : ∀ t ∈ B, t ∉ Oh.toList) (hS : ∀ t ∈ S, t ∈ h.toList) :
    E.delta B S = E.delta Ih.toList S := by
  obtain ⟨_, hIs, _, hchk, hIm, hOm, hIO⟩ := hctx
  have hIn := strictInc_nodup hIs
  let D := B.filter (fun t => decide (t ∉ Ih.toList))
  have hperm : B.Perm (Ih.toList ++ D) := by
    apply (List.perm_ext_iff_of_nodup hBn (nodup_app hIn (List.Nodup.sublist List.filter_sublist hBn)
      (fun x hx hxD => by simp only [D, List.mem_filter, decide_eq_true_eq] at hxD; exact hxD.2 hx))).mpr
    intro t
    simp only [List.mem_append, D, List.mem_filter, decide_eq_true_eq]
    constructor
    · intro ht
      by_cases hti : t ∈ Ih.toList
      · exact Or.inl hti
      · exact Or.inr ⟨ht, hti⟩
    · rintro (h | ⟨h, _⟩)
      · exact hIB t h
      · exact h
  have hmod := group_modular hE.G.wf hE.G.hroots hE.θ1 hE.cx hE.csc hchk
    (fun t ht => ⟨hIm t ht, hIO t ht⟩) hOm (D := D) (S := S)
    (fun t ht => by
      simp only [D, List.mem_filter, decide_eq_true_eq] at ht
      exact ⟨hBm t ht.1, hBh t ht.1, ht.2, hBO t ht.1⟩) hS
  unfold Env.delta
  rw [scost_perm (List.Perm.append_right S hperm), scost_perm hperm]
  omega

/-- **Pruning is sound.** Under a group's reduced context, every minimum's
`Δ` of the group is within `slack` of the best entry of a valid table. -/
theorem Env.prune_ok {E : Env} (hE : E.WF) {g I O : Array Nat} (hctx : E.GroupCtx g I O)
    {tb : CTable} (htab : E.TabOK g.toList I.toList tb) {bd : _root_.Int} (hbd : tb.best = some bd)
    {Y : List Nat} (hY : E.Cons Y I.toList O.toList) :
    E.delta I.toList (partOf Y g.toList) ≤ bd + (E.cx.slack : _root_.Int) := by
  obtain ⟨hgs, hIs, _, hchk, hIm, hOm, hIO⟩ := hctx
  obtain ⟨k, e, he, heb⟩ := best_attained hbd
  obtain ⟨_, hen, hesub, hev⟩ := htab k e he
  have hrep := group_rep hE.G hE.cx E.comp E.i hE.comp hE.memi hchk (strictInc_nodup hgs)
    (strictInc_nodup hIs) (fun t ht => ⟨hIm t ht, hIO t ht⟩) hOm hY.1 hY.2.1 hY.2.2
    (S := e.2.toList) hesub (hen.imp Nat.ne_of_lt)
  rw [← hE.slack] at hrep
  unfold Env.delta at hev ⊢
  unfold partOf
  omega

/-- **Trimming keeps the coverage** of a valid table. -/
theorem Env.covers_trim {E : Env} (hE : E.WF) {g I O : Array Nat} (hctx : E.GroupCtx g I O)
    {tb : CTable} (htab : E.TabOK g.toList I.toList tb)
    (hcov : E.Covers g.toList I.toList O.toList tb) :
    E.Covers g.toList I.toList O.toList (tb.trim E.cx.slack) := by
  intro Y hY
  exact (trim_tie E.cx.slack (fun k e he => (htab k e he).2.1)).2 (hcov Y hY)
    (fun b hb => E.prune_ok hE hctx htab hb hY)

theorem Env.TabOK.sorted {E : Env} {g I : List Nat} {tb : CTable} (h : E.TabOK g I tb) :
    SortedT tb := fun k e he => (h k e he).2.1

/-! ## Reclassification -/

theorem filter_map_perm {α : Type} (p : α → Bool) (f : α → Nat) (l : List α) :
    ((l.filter p).map f ++ (l.filter (fun x => !p x)).map f).Perm (l.map f) := by
  rw [← List.map_append]
  exact (List.filter_append_perm p l).map f

/-- The gain record of a member at a node. -/
def reGain (cx : SCtx) (outAll : Array Nat) (t : Nat) : Nat × _root_.Int × Bool :=
  (t, storedGainC cx.up.prep (cx.rebound (msOf cx.cand outAll)) cx.up.w t
      (cx.revisible (msOf cx.cand outAll)).1[t]! (cx.revisible (msOf cx.cand outAll)).2[t]!,
    1 ≤ (cx.revisible (msOf cx.cand outAll)).1[t]! &&
      (cx.revisible (msOf cx.cand outAll)).2[t]! ≤ (cx.revisible (msOf cx.cand outAll)).1[t]!)

/-- Whether a gain record is forced. -/
def reForced (cx : SCtx) (e : Nat × _root_.Int × Bool) : Bool := e.2.2 && e.2.1 ≥ cx.theta

theorem reclassify_eq (cx : SCtx) (outAll localIn und : Array Nat) :
    cx.reclassify outAll localIn und =
      (if (((und.map (reGain cx outAll)).filter (reForced cx)).map (·.1)).isEmpty then localIn
        else mergeSorted localIn (((und.map (reGain cx outAll)).filter (reForced cx)).map (·.1)),
       ((und.map (reGain cx outAll)).filter (fun e => !reForced cx e)).map (fun e => (e.1, e.2.1)),
       cx.rebound (msOf cx.cand outAll)) := rfl

theorem reclassify_sorted (cx : SCtx) (outAll localIn und : Array Nat) :
    (cx.reclassify outAll localIn und).1 = localIn ∨
      (cx.reclassify outAll localIn und).1.toList.Pairwise (· ≤ ·) := by
  rw [reclassify_eq]
  simp only
  split
  · exact Or.inl rfl
  · exact Or.inr (mergeSorted_sorted _ _)

theorem reclassify_spec (cx : SCtx) (outAll localIn und : Array Nat) :
    ∃ F : List Nat,
      (cx.reclassify outAll localIn und).1.toList.Perm (localIn.toList ++ F) ∧
      und.toList.Perm (F ++ ((cx.reclassify outAll localIn und).2.1.toList.map (·.1))) ∧
      ∀ t ∈ F, 1 ≤ (cx.revisible (msOf cx.cand outAll)).1[t]! ∧
        (cx.revisible (msOf cx.cand outAll)).2[t]! ≤ (cx.revisible (msOf cx.cand outAll)).1[t]! ∧
        storedGainC cx.up.prep (cx.rebound (msOf cx.cand outAll)) cx.up.w t
          (cx.revisible (msOf cx.cand outAll)).1[t]!
          (cx.revisible (msOf cx.cand outAll)).2[t]! ≥ cx.theta := by
  rw [reclassify_eq]
  generalize hgains : und.map (reGain cx outAll) = gains
  have hgl : gains.toList = und.toList.map (reGain cx outAll) := by
    rw [← hgains, Array.toList_map]
  refine ⟨((gains.filter (reForced cx)).map (·.1)).toList, ?_, ?_, ?_⟩
  · simp only
    split
    · rename_i hemp
      have : ((gains.filter (reForced cx)).map (·.1)).toList = [] := by
        rw [Array.isEmpty_iff.mp hemp]
      rw [this, List.append_nil]
    · exact mergeSorted_perm _ _
  · simp only [Array.toList_map, Array.toList_filter, List.map_map]
    have h1 := filter_map_perm (reForced cx) (·.1) gains.toList
    have h2 : gains.toList.map (·.1) = und.toList := by
      rw [hgl, List.map_map]
      conv => rhs; rw [← List.map_id und.toList]
      rfl
    rw [h2] at h1
    exact h1.symm
  · intro t ht
    simp only [Array.toList_map, Array.toList_filter, List.mem_map, List.mem_filter] at ht
    obtain ⟨e, ⟨he, hf⟩, rfl⟩ := ht
    rw [hgl, List.mem_map] at he
    obtain ⟨t', _, rfl⟩ := he
    simp only [reForced, reGain, Bool.and_eq_true, decide_eq_true_eq] at hf
    exact ⟨hf.1.1, hf.1.2, of_decide_eq_true hf.2⟩

/-! ## The memo -/

theorem Env.memoOK_insert {E : Env} {memo : Std.HashMap (Array Nat × Array Nat) CTable}
    (hm : E.MemoOK memo) {g ent : Array Nat} {tb : CTable}
    (hctx : E.GroupCtx g (keyContext ent).1 (keyContext ent).2)
    (htab : E.TabOK g.toList (keyContext ent).1.toList tb)
    (hcov : E.Covers g.toList (keyContext ent).1.toList (keyContext ent).2.toList tb) :
    E.MemoOK (memo.insert (g, ent) tb) := by
  intro g' ent' tb' h
  rw [Std.HashMap.get?_insert] at h
  split at h
  · rename_i hk
    have hk' : (g, ent) = (g', ent') := by simpa using hk
    cases hk'
    cases h
    exact ⟨hctx, htab, hcov⟩
  · exact hm g' ent' tb' h

/-! ## The specifications of the search functions -/

theorem Env.GroupCtx.facts {E : Env} (hE : E.WF) {g I O : Array Nat} (h : E.GroupCtx g I O) :
    (∀ t ∈ g.toList, t ∈ E.cx.members.toList ∧ t < E.dag.size ∧ t ∉ I.toList ∧ t ∉ O.toList) ∧
      g.toList.Nodup ∧ I.toList.Nodup ∧ O.toList.Nodup := by
  obtain ⟨hgs, hIs, hOs, hchk, _, _, _⟩ := h
  have hdag : E.cx.up.prep.dag = E.dag := by rw [hE.cx.prep]; rfl
  obtain ⟨ha, _⟩ := sepCheck_spec (cx := E.cx) (by rw [hdag]; exact hE.G.wf)
    (by rw [hdag, hE.cx.closure])
    (by intro t ht; rw [hdag]; exact (hE.cx.mem t (Array.mem_toList_iff.mpr ht)).1) hchk
  rw [hdag] at ha
  refine ⟨fun t ht => ?_, strictInc_nodup hgs, strictInc_nodup hIs, strictInc_nodup hOs⟩
  obtain ⟨h1, h2, h3, h4⟩ := ha t (Array.mem_toList_iff.mp ht)
  exact ⟨Array.mem_toList_iff.mpr h1, h2, fun h => h3 (Array.mem_toList_iff.mp h),
    fun h => h4 (Array.mem_toList_iff.mp h)⟩

/-- The precondition of a search node of group `g` under `(I, O)`. -/
structure Env.NodePre (E : Env) (g I O : Array Nat) (phi0 : Nat) (outAll localIn und : Array Nat)
    (tb : CTable) (memo : Std.HashMap (Array Nat × Array Nat) CTable) : Prop where
  ctx : E.GroupCtx g I O
  phi0 : phi0 = scost E.cx E.dag I.toList
  outO : ∀ t ∈ O.toList, t ∈ outAll.toList
  outM : ∀ t ∈ outAll.toList, t ∈ E.cx.members.toList
  outI : ∀ t ∈ outAll.toList, t ∉ I.toList
  locG : ∀ t ∈ localIn.toList, t ∈ g.toList
  undG : ∀ t ∈ und.toList, t ∈ g.toList
  nodup : (localIn.toList ++ und.toList).Nodup
  outLU : ∀ t ∈ outAll.toList, t ∉ localIn.toList ∧ t ∉ und.toList
  locSorted : localIn.toList.Pairwise (· < ·)
  cover : ∀ x ∈ g.toList, x ∈ localIn.toList ∨ x ∈ und.toList ∨ x ∈ outAll.toList
  tab : E.TabOK g.toList I.toList tb
  memo : E.MemoOK memo

/-- The postcondition of a search node. -/
def Env.NodePost (E : Env) (g I : Array Nat) (outAll localIn : Array Nat) (tb tb' : CTable)
    (memo' : Std.HashMap (Array Nat × Array Nat) CTable) : Prop :=
  E.TabOK g.toList I.toList tb' ∧ ImprovesT tb tb' ∧
    (∀ Y, E.Cons Y (I.toList ++ localIn.toList) outAll.toList →
      HasAtT tb' (partOf Y g.toList).length (E.delta I.toList (partOf Y g.toList))
        (partOf Y g.toList)) ∧
    E.MemoOK memo'

def Env.SolvePSpec (E : Env) (limits : Limits) (fuel : Nat) : Prop :=
  ∀ (g inAll outAll : Array Nat) (st : SState) (tb : CTable) (st' : SState),
    E.cx.solveP limits fuel g inAll outAll st = .ok (tb, st') →
    (∀ t ∈ inAll.toList, t ∈ E.cx.members.toList) → (∀ t ∈ outAll.toList, t ∈ E.cx.members.toList) →
    (∀ t ∈ inAll.toList, t ∉ outAll.toList) → E.MemoOK st.memo →
    E.MemoOK st'.memo ∧ ∃ I O : Array Nat, (∀ t ∈ I.toList, t ∈ inAll.toList) ∧
      (∀ t ∈ O.toList, t ∈ outAll.toList) ∧ E.GroupCtx g I O ∧ E.TabOK g.toList I.toList tb ∧
      E.Covers g.toList I.toList O.toList tb

def Env.SolveBodySpec (E : Env) (limits : Limits) (fuel : Nat) : Prop :=
  ∀ (g I O : Array Nat) (st : SState) (tb : CTable) (st' : SState),
    E.cx.solveBody limits fuel g I O st = .ok (tb, st') → E.GroupCtx g I O → E.MemoOK st.memo →
    E.MemoOK st'.memo ∧ E.TabOK g.toList I.toList tb ∧ E.Covers g.toList I.toList O.toList tb

def Env.NodePSpec (E : Env) (limits : Limits) (fuel : Nat) : Prop :=
  ∀ (g I O : Array Nat) (phi0 : Nat) (outAll : Array Nat) (nOut : Nat) (localIn und : Array Nat)
    (tb : CTable) (st : SState) (tb' : CTable) (st' : SState),
    E.cx.nodeP limits fuel phi0 I outAll nOut localIn und tb st = .ok (tb', st') →
    E.NodePre g I O phi0 outAll localIn und tb st.memo →
    E.NodePost g I outAll localIn tb tb' st'.memo

/-- The combinations of a split: each contains `L` and is within `L ∪ U`, with
its exact `Δ`. -/
def Env.CombOK (E : Env) (I L U : List Nat) (comb : CTable) : Prop :=
  ∀ e, some e ∈ comb.toList → e.2.toList.Pairwise (· < ·) ∧ (∀ x ∈ L, x ∈ e.2.toList) ∧
    (∀ x ∈ e.2.toList, x ∈ L ∨ x ∈ U) ∧ e.1 = E.delta I e.2.toList

/-- Every minimum respecting the node has a combination at its count. -/
def Env.CombCov (E : Env) (I L U O : List Nat) (comb : CTable) : Prop :=
  ∀ Y, E.Cons Y (I ++ L) O → ∃ e, some e ∈ comb.toList ∧ e.2.size = (L ++ partOf Y U).length ∧
    (e.1 < E.delta I (L ++ partOf Y U) ∨
      (e.1 = E.delta I (L ++ partOf Y U) ∧ LeL e.2.toList (L ++ partOf Y U)))

/-- The precondition of a split of a node of group `g` under `(I, O)`. -/
structure Env.SplitPre (E : Env) (g I O : Array Nat) (L U : List Nat) (outAll : Array Nat)
    (grps : List (Array Nat)) (comb : CTable) (memo : Std.HashMap (Array Nat × Array Nat) CTable) :
    Prop where
  ctx : E.GroupCtx g I O
  outO : ∀ t ∈ O.toList, t ∈ outAll.toList
  outM : ∀ t ∈ outAll.toList, t ∈ E.cx.members.toList
  outI : ∀ t ∈ outAll.toList, t ∉ I.toList
  sub : ∀ t ∈ L ++ U ++ grps.flatMap (·.toList), t ∈ g.toList ∧ t ∉ outAll.toList
  nodup : (L ++ U ++ grps.flatMap (·.toList)).Nodup
  combOK : E.CombOK I.toList L U comb
  combCov : E.CombCov I.toList L U outAll.toList comb
  memo : E.MemoOK memo

def Env.SplitPSpec (E : Env) (limits : Limits) (fuel : Nat) : Prop :=
  ∀ (g I O : Array Nat) (L U : List Nat) (inAll outAll : Array Nat) (grps : List (Array Nat))
    (comb : CTable) (st : SState) (comb' : CTable) (st' : SState),
    E.cx.splitP limits fuel inAll outAll grps comb st = .ok (comb', st') →
    inAll.toList = I.toList ++ L →
    E.SplitPre g I O L U outAll grps comb st.memo →
    E.CombOK I.toList L (U ++ grps.flatMap (·.toList)) comb' ∧
      E.CombCov I.toList L (U ++ grps.flatMap (·.toList)) outAll.toList comb' ∧ E.MemoOK st'.memo

/-! ## No fuel -/

theorem Env.specs_zero (E : Env) (limits : Limits) :
    E.SolvePSpec limits 0 ∧ E.SolveBodySpec limits 0 ∧ E.NodePSpec limits 0 ∧
      E.SplitPSpec limits 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ h; rw [SCtx.solveP] at h; cases h
  · intro _ _ _ _ _ _ h; rw [SCtx.solveBody] at h; cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ h; rw [SCtx.nodeP] at h; cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ h; rw [SCtx.splitP.eq_1] at h; cases h

/-! ## The group search -/

theorem empty_tabOK (E : Env) (g I : List Nat) : E.TabOK g I #[] := by
  intro k e he
  simp [getElem!_def] at he

theorem Env.solveBody_step {E : Env} (hE : E.WF) {limits : Limits} {fuel : Nat}
    (hnode : E.NodePSpec limits fuel) : E.SolveBodySpec limits (fuel + 1) := by
  intro g I O st tb st' h hctx hmemo
  rw [SCtx.solveBody] at h
  obtain ⟨hgf, hgn, hIn, hOn⟩ := hctx.facts hE
  obtain ⟨_, _, _, _, hIm, hOm, hIO⟩ := id hctx
  have hphi := phiE_cost hE.G.wf hE.cx I hIm (fun t => (I.foldl (·.insert ·)
      ({} : Std.HashSet Nat)).contains t) (fun t => hashSet_ofArray_contains I t)
  generalize hpe : E.cx.phiE (fun t => (I.foldl (·.insert ·) ({} : Std.HashSet Nat)).contains t) I
    = pw at h hphi
  obtain ⟨phi0, work⟩ := pw
  simp only at h hphi
  obtain ⟨st1, hst1, h⟩ := bind_eq_ok h
  obtain ⟨⟨tb0, st2⟩, hnd, h⟩ := bind_eq_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hpre : E.NodePre g I O phi0 O #[] g #[] st1.memo :=
    { ctx := hctx
      phi0 := hphi
      outO := fun t ht => ht
      outM := hOm
      outI := fun t ht hI => hIO t hI ht
      locG := fun t ht => by simp at ht
      undG := fun t ht => ht
      nodup := by simpa using hgn
      outLU := fun t ht => ⟨by simp, fun hg => (hgf t hg).2.2.2 ht⟩
      locSorted := by simp
      cover := fun x hx => Or.inr (Or.inl hx)
      tab := empty_tabOK E _ _
      memo := by rw [chargeP_memo hst1]; exact hmemo }
  obtain ⟨htab, _, hcov, hmemo'⟩ := hnode g I O phi0 O O.size #[] g #[] st1 tb0 st2 hnd hpre
  have hcov' : E.Covers g.toList I.toList O.toList tb0 := by
    intro Y hY
    exact hcov Y (by simpa using hY)
  exact ⟨hmemo', trim_entries htab _, E.covers_trim hE hctx htab hcov'⟩

theorem Env.solveP_step {E : Env} (hE : E.WF) {limits : Limits} {fuel : Nat}
    (hbody : E.SolveBodySpec limits fuel) : E.SolvePSpec limits (fuel + 1) := by
  intro g inAll outAll st tb st' h hinM houtM hio hmemo
  rw [SCtx.solveP] at h
  simp only at h
  generalize hmk : E.cx.memoKey (fun x => (E.cx.opaqueArr inAll outAll)[x]!)
    (inAll.foldl (·.insert ·) ∅) (outAll.foldl (·.insert ·) ∅) g = mk at h
  obtain ⟨entries, rel⟩ := mk
  generalize hkc : keyContext entries = kc at h
  obtain ⟨inRed, outRed⟩ := kc
  simp only at h
  split at h
  all_goals first | (cases h; done) | skip
  rename_i hchk
  have hchk' : (strictInc g && strictInc inRed && strictInc outRed &&
      inRed.all (inAll.foldl (·.insert ·) (∅ : Std.HashSet Nat)).contains &&
      outRed.all (outAll.foldl (·.insert ·) (∅ : Std.HashSet Nat)).contains) = true := by
    simpa using hchk
  simp only [Bool.and_eq_true] at hchk'
  obtain ⟨⟨⟨⟨hgs, hIs⟩, hOs⟩, hIin⟩, hOout⟩ := hchk'
  have hIsub : ∀ t ∈ inRed.toList, t ∈ inAll.toList := by
    intro t ht
    rw [Array.all_eq_true'] at hIin
    have := hIin t (Array.mem_toList_iff.mp ht)
    rw [hashSet_ofArray_contains] at this
    simpa using this
  have hOsub : ∀ t ∈ outRed.toList, t ∈ outAll.toList := by
    intro t ht
    rw [Array.all_eq_true'] at hOout
    have := hOout t (Array.mem_toList_iff.mp ht)
    rw [hashSet_ofArray_contains] at this
    simpa using this
  split at h
  · -- memo hit
    rename_i tb0 hget
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hctx, htab, hcov⟩ := hmemo g entries tb0 hget
    rw [hkc] at hctx htab hcov
    exact ⟨hmemo, inRed, outRed, hIsub, hOsub, hctx, htab, hcov⟩
  · -- memo miss
    split at h
    all_goals first | (cases h; done) | skip
    rename_i hsep0
    have hsep : E.cx.sepCheck g inRed outRed = true := by simpa using hsep0
    obtain ⟨⟨tb0, st2⟩, hb, h⟩ := bind_eq_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hctx : E.GroupCtx g inRed outRed :=
      ⟨hgs, hIs, hOs, hsep, fun t ht => hinM t (hIsub t ht), fun t ht => houtM t (hOsub t ht),
        fun t ht ht' => hio t (hIsub t ht) (hOsub t ht')⟩
    obtain ⟨hmemo2, htab, hcov⟩ := hbody g inRed outRed st tb0 st2 hb hctx hmemo
    refine ⟨?_, inRed, outRed, hIsub, hOsub, hctx, htab, hcov⟩
    apply E.memoOK_insert hmemo2 <;> rw [hkc]
    · exact hctx
    · exact htab
    · exact hcov

/-! ## Splits -/

theorem Env.delta_append (E : Env) (I A B : List Nat) :
    E.delta I (A ++ B) = E.delta I A + E.delta (I ++ A) B := by
  unfold Env.delta
  rw [List.append_assoc]
  omega

theorem partOf_append (Y A B : List Nat) : partOf Y (A ++ B) = partOf Y A ++ partOf Y B := by
  unfold partOf; exact List.filter_append _ _

theorem partOf_sub {Y A : List Nat} : ∀ t ∈ partOf Y A, t ∈ A ∧ t ∈ Y := by
  intro t ht
  simp only [partOf, List.mem_filter, decide_eq_true_eq] at ht
  exact ht

theorem Env.splitP_step {E : Env} (hE : E.WF) {limits : Limits} {fuel : Nat}
    (hsolve : E.SolvePSpec limits fuel) (hsplit : E.SplitPSpec limits fuel) :
    E.SplitPSpec limits (fuel + 1) := by
  intro g I O L U inAll outAll grps comb st comb' st' h hin hpre
  cases grps with
  | nil =>
    rw [SCtx.splitP.eq_2] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.flatMap_nil, List.append_nil]
    exact ⟨hpre.combOK, hpre.combCov, hpre.memo⟩
  | cons hg rest =>
    rw [SCtx.splitP.eq_3] at h
    obtain ⟨⟨sub, st1⟩, hs, h⟩ := bind_eq_ok h
    simp only at h
    obtain ⟨hgf, hgn, hIn, hOn⟩ := hpre.ctx.facts hE
    obtain ⟨_, _, _, _, hIm, hOm, hIO⟩ := id hpre.ctx
    have hsubL : ∀ t ∈ L, t ∈ g.toList ∧ t ∉ outAll.toList :=
      fun t ht => hpre.sub t (by simp [ht])
    have hsubU : ∀ t ∈ U, t ∈ g.toList ∧ t ∉ outAll.toList :=
      fun t ht => hpre.sub t (by simp [ht])
    have hsubh : ∀ t ∈ hg.toList, t ∈ g.toList ∧ t ∉ outAll.toList :=
      fun t ht => hpre.sub t (by simp [ht])
    have hnd := hpre.nodup
    simp only [List.flatMap_cons] at hnd
    -- the parts are pairwise disjoint
    have hLU_h : ∀ t, t ∈ L ∨ t ∈ U → t ∉ hg.toList := by
      intro t ht hth
      have := List.nodup_append.mp hnd
      rcases ht with ht | ht
      · exact this.2.2 t (by simp [ht]) t (by simp [hth]) rfl
      · exact this.2.2 t (by simp [ht]) t (by simp [hth]) rfl
    have hinM : ∀ t ∈ inAll.toList, t ∈ E.cx.members.toList := by
      intro t ht
      rw [hin, List.mem_append] at ht
      rcases ht with ht | ht
      · exact hIm t ht
      · exact (hgf t (hsubL t ht).1).1
    have hio : ∀ t ∈ inAll.toList, t ∉ outAll.toList := by
      intro t ht
      rw [hin, List.mem_append] at ht
      rcases ht with ht | ht
      · exact fun h => hpre.outI t h ht
      · exact (hsubL t ht).2
    obtain ⟨hmemo1, Ih, Oh, hIh, hOh, hctxh, htabh, hcovh⟩ :=
      hsolve hg inAll outAll st sub st1 hs hinM hpre.outM hio hpre.memo
    obtain ⟨hhf, hhn, hIhn, hOhn⟩ := hctxh.facts hE
    -- the shift to a base containing `I ++ L`
    have hshift : ∀ (A : List Nat) (S : List Nat), A.Nodup → (∀ x ∈ L, x ∈ A) →
        (∀ x ∈ A, x ∈ L ∨ x ∈ U) → (∀ x ∈ S, x ∈ hg.toList) →
        E.delta (I.toList ++ A) S = E.delta Ih.toList S := by
      intro A S hAn hLA hAsub hS
      apply E.delta_shift hE hctxh
      · apply nodup_app hIn hAn
        intro x hx hxA
        rcases hAsub x hxA with h | h
        · exact (hgf x (hsubL x h).1).2.2.1 hx
        · exact (hgf x (hsubU x h).1).2.2.1 hx
      · intro t ht
        have := hIh t ht
        rw [hin, List.mem_append] at this
        rcases this with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (hLA t h)
      · intro t ht
        rcases List.mem_append.mp ht with h | h
        · exact hIm t h
        · rcases hAsub t h with h | h
          · exact (hgf t (hsubL t h).1).1
          · exact (hgf t (hsubU t h).1).1
      · intro t ht hth
        rcases List.mem_append.mp ht with h | h
        · exact (hgf t (hsubh t hth).1).2.2.1 h
        · exact hLU_h t (hAsub t h) hth
      · intro t ht hto
        have hto' := hOh t hto
        rcases List.mem_append.mp ht with h | h
        · exact hpre.outI t hto' h
        · rcases hAsub t h with h | h
          · exact (hsubL t h).2 hto'
          · exact (hsubU t h).2 hto'
      · exact hS
    -- the new combinations
    have hLUn : (L ++ U).Nodup := (List.nodup_append.mp hnd).1
    have hLn : L.Nodup := (List.nodup_append.mp hLUn).1
    have hUn : U.Nodup := (List.nodup_append.mp hLUn).2.1
    have hLUd : ∀ a ∈ L, ∀ b ∈ U, a ≠ b := (List.nodup_append.mp hLUn).2.2
    have hce := conv_entries (a := comb) (b := sub) (Pa := fun e => some e ∈ comb.toList)
      (Pb := fun e => some e ∈ sub.toList) (fun e he => he) (fun e he => he)
    have hcsorted : ∀ e, some e ∈ comb.toList → e.2.toList.Pairwise (· < ·) :=
      fun e he => (hpre.combOK e he).1
    have hssorted : ∀ e, some e ∈ sub.toList → e.2.toList.Pairwise (· < ·) :=
      fun e he => (htabh.mem he).1
    have hcsdisj : ∀ ea, some ea ∈ comb.toList → ∀ eb, some eb ∈ sub.toList →
        ∀ x ∈ ea.2.toList, x ∉ eb.2.toList :=
      fun ea hea eb heb x hx hx' => hLU_h x ((hpre.combOK ea hea).2.2.1 x hx) ((htabh.mem heb).2.1 x hx')
    obtain ⟨hconvSorted, hconvT⟩ := conv_tie hcsorted hssorted hcsdisj
    have hcombOK : E.CombOK I.toList L (U ++ hg.toList) (comb.conv sub) := by
      intro e he
      obtain ⟨k, hk⟩ := mem_toList_getElem! he
      obtain ⟨_, ec, es, hec, hes, rfl⟩ := hce k e hk
      obtain ⟨hecn, hecL, hecs, hecv⟩ := hpre.combOK ec hec
      obtain ⟨hesn, hesh, hesv⟩ := htabh.mem hes
      have hperm := mergeSorted_perm ec.2 es.2
      have hdisj : ∀ x ∈ ec.2.toList, x ∉ es.2.toList :=
        fun x hx hx' => hLU_h x (hecs x hx) (hesh x hx')
      refine ⟨mergeSorted_strict hecn hesn hdisj,
        fun x hx => hperm.mem_iff.mpr (List.mem_append_left _ (hecL x hx)), fun x hx => ?_, ?_⟩
      · rcases List.mem_append.mp (hperm.mem_iff.mp hx) with h | h
        · rcases hecs x h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_append_left _ h)
        · exact Or.inr (List.mem_append_right _ (hesh x h))
      · simp only
        rw [E.delta_perm hperm, E.delta_append, hecv, hesv,
          hshift ec.2.toList es.2.toList (hecn.imp Nat.ne_of_lt) hecL hecs hesh]
    have hcombCov : E.CombCov I.toList L (U ++ hg.toList) outAll.toList (comb.conv sub) := by
      intro Y hY
      obtain ⟨ec, hec, hecsz, hecv⟩ := hpre.combCov Y hY
      have hYc : E.Cons Y Ih.toList Oh.toList :=
        ⟨hY.1, fun t ht => hY.2.1 t (by have := hIh t ht; rw [hin] at this; exact this),
          fun t ht => hY.2.2 t (hOh t ht)⟩
      obtain ⟨es, hes, hesv⟩ := hcovh Y hYc
      have hesz := (htabh _ es hes).1
      obtain ⟨ecv, hecv', hle⟩ := hconvT ec hec es (getElem!_mem_toList hes)
      have hecvsz := (hce _ ecv hecv').1
      have hpU : ∀ t ∈ partOf Y U, t ∈ U := fun t ht => (partOf_sub t ht).1
      have hpUn : (partOf Y U).Nodup := List.Nodup.sublist List.filter_sublist hUn
      have hAn : (L ++ partOf Y U).Nodup :=
        nodup_app hLn hpUn (fun x hx hxU => hLUd x hx x (hpU x hxU) rfl)
      have heq := hshift (L ++ partOf Y U) (partOf Y hg.toList) hAn
        (fun x hx => List.mem_append_left _ hx)
        (fun x hx => by
          rcases List.mem_append.mp hx with h | h
          · exact Or.inl h
          · exact Or.inr (hpU x h))
        (fun x hx => (partOf_sub x hx).1)
      have hval : E.delta I.toList (L ++ partOf Y (U ++ hg.toList)) =
          E.delta I.toList (L ++ partOf Y U) + E.delta Ih.toList (partOf Y hg.toList) := by
        rw [partOf_append, ← List.append_assoc, E.delta_append, heq]
      refine ⟨ecv, getElem!_mem_toList hecv', ?_, ?_⟩
      · rw [hecvsz, hecsz, hesz, partOf_append]
        simp only [List.length_append]
        omega
      · rw [hval]
        -- the combination of the two entries against the minimum's parts
        have hpair : (ec.1 + es.1 < E.delta I.toList (L ++ partOf Y U) +
              E.delta Ih.toList (partOf Y hg.toList)) ∨
            (ec.1 + es.1 = E.delta I.toList (L ++ partOf Y U) +
              E.delta Ih.toList (partOf Y hg.toList) ∧
              LeL (mergeSorted ec.2 es.2).toList (L ++ partOf Y U ++ partOf Y hg.toList)) := by
          rcases hecv with h1 | ⟨h1, h1'⟩ <;> rcases hesv with h2 | ⟨h2, h2'⟩
          · exact Or.inl (by omega)
          · exact Or.inl (by omega)
          · exact Or.inl (by omega)
          · refine Or.inr ⟨by omega, ?_⟩
            have hm := (mergeSorted_perm ec.2 es.2)
            apply precL_union (X1 := ec.2.toList) (Y1 := L ++ partOf Y U) (X2 := es.2.toList)
              (Y2 := partOf Y hg.toList)
            · intro a ha hb
              have ha' : a ∈ L ∨ a ∈ U := by
                rcases ha with ha | ha
                · exact (hpre.combOK ec hec).2.2.1 a ha
                · rcases List.mem_append.mp ha with h | h
                  · exact Or.inl h
                  · exact Or.inr (hpU a h)
              have hb' : a ∈ hg.toList := by
                rcases hb with hb | hb
                · exact (htabh.mem (getElem!_mem_toList hes)).2.1 a hb
                · exact (partOf_sub a hb).1
              exact hLU_h a ha' hb'
            · intro u; rw [hm.mem_iff, List.mem_append]
            · intro u; rw [List.mem_append]
            · exact h1'
            · exact h2'
        rcases hle with h | ⟨h, h'⟩ <;> rcases hpair with hp | ⟨hp, hp'⟩
        · exact Or.inl (by omega)
        · exact Or.inl (by omega)
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, leL_congr (fun _ => Iff.rfl)
            (fun u => by rw [partOf_append, List.append_assoc]) (leL_trans h' hp')⟩
    have hpre' : E.SplitPre g I O L (U ++ hg.toList) outAll rest (comb.conv sub) st1.memo :=
      { ctx := hpre.ctx, outO := hpre.outO, outM := hpre.outM, outI := hpre.outI
        sub := fun t ht => hpre.sub t (by
          simp only [List.flatMap_cons, List.mem_append] at ht ⊢
          rcases ht with (h | h | h) | h
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h))
        nodup := by
          have := hpre.nodup
          simp only [List.flatMap_cons, List.append_assoc] at this ⊢
          exact this
        combOK := hcombOK
        combCov := hcombCov
        memo := hmemo1 }
    obtain ⟨h1, h2, h3⟩ :=
      hsplit g I O L (U ++ hg.toList) inAll outAll rest (comb.conv sub) st1 comb' st' h hin hpre'
    simp only [List.flatMap_cons, List.append_assoc] at h1 h2 ⊢
    exact ⟨h1, h2, h3⟩

/-! ## Search nodes -/

theorem Env.nodeP_step {E : Env} (hE : E.WF) {limits : Limits} {fuel : Nat}
    (hnode : E.NodePSpec limits fuel) (hsplit : E.SplitPSpec limits fuel) :
    E.NodePSpec limits (fuel + 1) := by
  intro g I O phi0 outAll nOut localIn und tb st tb' st' h pre
  rw [SCtx.nodeP] at h
  obtain ⟨F, hLperm, hUperm, hF⟩ := reclassify_spec E.cx outAll localIn und
  generalize hrc : E.cx.reclassify outAll localIn und = rc at h hLperm hUperm
  obtain ⟨localIn', open_, b⟩ := rc
  simp only at h hLperm hUperm
  obtain ⟨hgf, hgn, hIn, hOn⟩ := pre.ctx.facts hE
  obtain ⟨_, _, _, _, hIm, hOm, hIO⟩ := id pre.ctx
  -- the node after reclassification
  generalize hUn : open_.toList.map (·.1) = Un at hUperm
  have hUnA : (open_.map (·.1)).toList = Un := by rw [← hUn, Array.toList_map]
  have hFund : ∀ t ∈ F, t ∈ und.toList := fun t ht => hUperm.mem_iff.mpr (List.mem_append_left _ ht)
  have hUnund : ∀ t ∈ Un, t ∈ und.toList := fun t ht => hUperm.mem_iff.mpr (List.mem_append_right _ ht)
  have hpermLU : (localIn'.toList ++ Un).Perm (localIn.toList ++ und.toList) := by
    refine (hLperm.append_right Un).trans ?_
    rw [List.append_assoc]
    exact (hUperm.symm).append_left _
  have hLUn : (localIn'.toList ++ Un).Nodup := hpermLU.nodup_iff.mpr pre.nodup
  have hL'n : localIn'.toList.Nodup := (List.nodup_append.mp hLUn).1
  have hL's : localIn'.toList.Pairwise (· < ·) := by
    have hrs := reclassify_sorted E.cx outAll localIn und
    rw [hrc] at hrs
    simp only at hrs
    rcases hrs with h | h
    · rw [h]; exact pre.locSorted
    · exact (List.Pairwise.and h hL'n).imp (fun h => Nat.lt_of_le_of_ne h.1 h.2)
  have hUnn : Un.Nodup := (List.nodup_append.mp hLUn).2.1
  have hL'g : ∀ t ∈ localIn'.toList, t ∈ g.toList := by
    intro t ht
    rcases List.mem_append.mp (hLperm.mem_iff.mp ht) with h | h
    · exact pre.locG t h
    · exact pre.undG t (hFund t h)
  have hUng : ∀ t ∈ Un, t ∈ g.toList := fun t ht => pre.undG t (hUnund t ht)
  have hout' : ∀ t ∈ outAll.toList, t ∉ localIn'.toList ∧ t ∉ Un := by
    intro t ht
    obtain ⟨h1, h2⟩ := pre.outLU t ht
    refine ⟨fun h => ?_, fun h => h2 (hUnund t h)⟩
    rcases List.mem_append.mp (hLperm.mem_iff.mp h) with h | h
    · exact h1 h
    · exact h2 (hFund t h)
  have hcov' : ∀ x ∈ g.toList, x ∈ localIn'.toList ∨ x ∈ Un ∨ x ∈ outAll.toList := by
    intro x hx
    rcases pre.cover x hx with h | h | h
    · exact Or.inl (hLperm.mem_iff.mpr (List.mem_append_left _ h))
    · rcases List.mem_append.mp (hUperm.mem_iff.mp h) with h | h
      · exact Or.inl (hLperm.mem_iff.mpr (List.mem_append_right _ h))
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  -- forced members are in every minimum respecting the node
  have hforce : ∀ Y, E.Cons Y (I.toList ++ localIn.toList) outAll.toList →
      E.Cons Y (I.toList ++ localIn'.toList) outAll.toList := by
    intro Y hY
    refine ⟨hY.1, fun t ht => ?_, hY.2.2⟩
    rcases List.mem_append.mp ht with h | h
    · exact hY.2.1 t (List.mem_append_left _ h)
    · rcases List.mem_append.mp (hLperm.mem_iff.mp h) with h | h
      · exact hY.2.1 t (List.mem_append_right _ h)
      · obtain ⟨h1, h2, h3⟩ := hF t h
        exact forced_mem hE.G hE.cx hE.area hY.1 hY.2.2 (hgf t (pre.undG t (hFund t h))).1 h1 h2 h3
  -- a minimum's part of the group
  have hpart : ∀ Y, E.Cons Y (I.toList ++ localIn'.toList) outAll.toList →
      (partOf Y g.toList).Perm (localIn'.toList ++ partOf Y Un) := by
    intro Y hY
    apply (List.perm_ext_iff_of_nodup (List.Nodup.sublist List.filter_sublist hgn)
      (List.Nodup.sublist (List.Sublist.append_left List.filter_sublist _) hLUn)).mpr
    intro x
    simp only [partOf, List.mem_append, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨hxg, hxY⟩
      rcases hcov' x hxg with h | h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hxY⟩
      · exact absurd hxY (hY.2.2 x h)
    · rintro (h | ⟨h, hxY⟩)
      · exact ⟨hL'g x h, hY.2.1 x (List.mem_append_right _ h)⟩
      · exact ⟨hUng x h, hxY⟩
  -- the node's lower bound
  have hinAll : (I ++ localIn').toList = I.toList ++ localIn'.toList := Array.toList_append
  have hinM : ∀ t ∈ (I ++ localIn').toList, t ∈ E.cx.members.toList := by
    intro t ht
    rw [hinAll, List.mem_append] at ht
    rcases ht with h | h
    · exact hIm t h
    · exact (hgf t (hL'g t h)).1
  have havail : ∀ t, (((I ++ localIn').foldl (·.insert ·) (∅ : Std.HashSet Nat)).contains t ||
      ((open_.map (·.1)).foldl (·.insert ·) (∅ : Std.HashSet Nat)).contains t) =
        decide (t ∈ (I ++ localIn').toList ∨ t ∈ Un) := by
    intro t
    rw [hashSet_ofArray_contains, hashSet_ofArray_contains, hUnA]
    simp
  have hlow := fun (X : List Nat) (hX : ∀ t ∈ X, t ∈ Un) => phiE_lower hE.G.wf hE.cx
    (I ++ localIn') Un hinM (fun t ht => (hgf t (hUng t ht)).1) _ havail (X := X) hX
  generalize hphi : E.cx.phiE (fun t =>
      ((I ++ localIn').foldl (·.insert ·) (∅ : Std.HashSet Nat)).contains t ||
      ((open_.map (·.1)).foldl (·.insert ·) (∅ : Std.HashSet Nat)).contains t) (I ++ localIn')
    = pw at h hlow
  obtain ⟨phi, work⟩ := pw
  simp only at h hlow
  have hbound : ∀ Y, E.Cons Y (I.toList ++ localIn'.toList) outAll.toList →
      (phi : _root_.Int) - phi0 ≤ E.delta I.toList (partOf Y g.toList) := by
    intro Y hY
    have h1 := hlow (partOf Y Un) (fun t ht => (partOf_sub t ht).1)
    rw [hinAll, List.append_assoc, ← scost_perm (List.Perm.append_left _ (hpart Y hY))] at h1
    unfold Env.delta
    rw [pre.phi0]
    omega
  have hYcons : ∀ Y, E.Cons Y (I.toList ++ localIn.toList) outAll.toList →
      E.Cons Y I.toList O.toList := fun Y hY =>
    ⟨hY.1, fun t ht => hY.2.1 t (List.mem_append_left _ ht), fun t ht => hY.2.2 t (pre.outO t ht)⟩
  obtain ⟨st1, hst1, h⟩ := bind_eq_ok h
  have hm1 : st1.memo = st.memo := chargeP_memo hst1
  by_cases hemp : (open_.map (·.1)).isEmpty = true
  · rw [if_pos hemp] at h
    -- every undecided member is decided: one entry
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hUnnil : Un = [] := by
      rw [← hUnA]; have := Array.isEmpty_iff.mp hemp; rw [this]
    subst hUnnil
    have hexact : phi = scost E.cx E.dag (I.toList ++ localIn'.toList) := by
      have := phiE_cost hE.G.wf hE.cx (I ++ localIn') hinM (fun t =>
        ((I ++ localIn').foldl (·.insert ·) (∅ : Std.HashSet Nat)).contains t ||
        ((open_.map (·.1)).foldl (·.insert ·) (∅ : Std.HashSet Nat)).contains t)
        (fun t => by rw [havail t]; simp)
      rw [hphi] at this
      rw [← hinAll]; exact this
    have hval : (phi : _root_.Int) - phi0 = E.delta I.toList localIn'.toList := by
      unfold Env.delta; rw [hexact, pre.phi0]
    refine ⟨add_entries pre.tab ⟨hL's, hL'g, hval⟩, add_improvesT pre.tab.sorted hL's, ?_,
      by rw [hm1]; exact pre.memo⟩
    intro Y hY
    have hp := hpart Y (hforce Y hY)
    have hnil : partOf Y ([] : List Nat) = [] := rfl
    rw [hnil, List.append_nil] at hp
    rw [hp.length_eq, E.delta_perm hp, ← hval, Array.length_toList]
    exact (add_hasAtT pre.tab.sorted hL's (e := ((phi : _root_.Int) - phi0, localIn'))).congr
      (fun u => hp.mem_iff.symm)
  rw [if_neg hemp] at h
  by_cases hpr : tb.prunes ((phi : _root_.Int) - phi0) E.cx.slack = true
  · rw [if_pos hpr] at h
    -- pruned: no minimum respects the node
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨pre.tab, improvesT_refl _, ?_, by rw [hm1]; exact pre.memo⟩
    intro Y hY
    exfalso
    have hb := hbound Y (hforce Y hY)
    unfold CTable.prunes at hpr
    split at hpr
    · rename_i bd hbd
      have := E.prune_ok hE pre.ctx pre.tab hbd (hYcons Y hY)
      simp only [decide_eq_true_eq] at hpr
      omega
    · cases hpr
  rw [if_neg hpr] at h
  split at h
  next hpc =>
    generalize hgr : E.cx.groups _ _ (Array.map (fun x => x.fst) open_) = groups at h hpc
    have hgperm : (groups.toList.flatMap (·.toList)).Perm Un := by
      rw [← hUnA]; exact partitionCheck_perm hpc
    generalize hrt : (if groups.size > 1 then true else _ : Bool) = route at h
    cases route
    case true =>
      rw [if_pos rfl] at h
      -- split into groups
      have hphiN := phiE_cost hE.G.wf hE.cx (I ++ localIn') hinM
        (fun t => ((I ++ localIn').foldl (·.insert ·) (∅ : Std.HashSet Nat)).contains t)
        (fun t => by rw [hashSet_ofArray_contains])
      generalize hpn : E.cx.phiE (fun t =>
        ((I ++ localIn').foldl (·.insert ·) (∅ : Std.HashSet Nat)).contains t) (I ++ localIn') = pn
        at h hphiN
      obtain ⟨phiN, workN⟩ := pn
      simp only at h hphiN
      obtain ⟨st2, hst2, h⟩ := bind_eq_ok h
      obtain ⟨⟨comb, st3⟩, hsp, h⟩ := bind_eq_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hbase : (phiN : _root_.Int) - phi0 = E.delta I.toList localIn'.toList := by
        unfold Env.delta; rw [hphiN, pre.phi0, hinAll]
      have hflat : ∀ t ∈ groups.toList.flatMap (·.toList), t ∈ Un := fun t ht => hgperm.mem_iff.mp ht
      have hspre : E.SplitPre g I O localIn'.toList [] outAll groups.toList
          #[some ((phiN : _root_.Int) - phi0, localIn')] st2.memo :=
        { ctx := pre.ctx, outO := pre.outO, outM := pre.outM, outI := pre.outI
          sub := by
            intro t ht
            simp only [List.append_nil, List.mem_append] at ht
            rcases ht with h | h
            · exact ⟨hL'g t h, fun ho => (hout' t ho).1 h⟩
            · exact ⟨hUng t (hflat t h), fun ho => (hout' t ho).2 (hflat t h)⟩
          nodup := by
            rw [List.append_nil]
            exact (List.Perm.append_left _ hgperm).nodup_iff.mpr hLUn
          combOK := by
            intro e he
            simp at he
            subst he
            refine ⟨hL's, fun x hx => hx, fun x hx => Or.inl hx, hbase⟩
          combCov := by
            intro Y _
            refine ⟨((phiN : _root_.Int) - phi0, localIn'), by simp, ?_, ?_⟩
            · simp [partOf, Array.length_toList]
            · simp only [partOf, List.filter_nil, List.append_nil]; rw [hbase]
              exact Or.inr ⟨rfl, leL_refl _⟩
          memo := by rw [chargeP_memo hst2, hm1]; exact pre.memo }
      obtain ⟨hcok, hccov, hmemo3⟩ := hsplit g I O localIn'.toList [] (I ++ localIn') outAll
        groups.toList _ st2 comb st3 hsp hinAll hspre
      simp only [List.nil_append] at hcok hccov
      show E.NodePost g I outAll localIn tb (addAll tb comb) st3.memo
      obtain ⟨_, hallImp, hallHas⟩ := addAll_tie pre.tab.sorted (fun e he => (hcok e he).1)
      refine ⟨addAll_entries pre.tab (fun e he => ?_), hallImp, ?_, hmemo3⟩
      · obtain ⟨hn, _, hsub, hv⟩ := hcok e he
        refine ⟨hn, fun x hx => ?_, hv⟩
        rcases hsub x hx with h | h
        · exact hL'g x h
        · exact hUng x (hflat x h)
      · intro Y hY
        have hY' := hforce Y hY
        obtain ⟨e, he, hesz, hev⟩ := hccov Y hY'
        have hpp : (localIn'.toList ++ partOf Y (groups.toList.flatMap (·.toList))).Perm
            (partOf Y g.toList) :=
          ((List.Perm.append_left _ (hgperm.filter _))).trans (hpart Y hY').symm
        have := hallHas e he
        rw [hesz, hpp.length_eq] at this
        refine (this.weakenT hev).congr (fun u => hpp.mem_iff) |>.weakenT ?_
        rw [E.delta_perm hpp]
        exact Or.inr ⟨rfl, leL_refl _⟩
    case false =>
      rw [if_neg (by decide)] at h
      split at h
      · rename_i t gt hpick
        have htU : t ∈ Un := by
          rw [← hUn]; exact List.mem_map.mpr ⟨(t, gt), pickBranch_mem hpick, rfl⟩
        have hund2 : ((open_.map (·.1)).erase t).toList = Un.erase t := by
          rw [toList_erase, hUnA]
        have htg := hUng t htU
        have htout : t ∉ outAll.toList := fun h => (hout' t h).2 htU
        have htL : t ∉ localIn'.toList := fun h =>
          (List.nodup_append.mp hLUn).2.2 t h t htU rfl
        have hmerge : (mergeSorted localIn' #[t]).toList.Perm (localIn'.toList ++ [t]) :=
          mergeSorted_perm _ _
        have hUe : ∀ x ∈ Un.erase t, x ∈ Un := fun x hx => List.erase_subset hx
        have preA : ∀ (tbX : CTable) memoX, E.TabOK g.toList I.toList tbX → E.MemoOK memoX →
            E.NodePre g I O phi0 outAll (mergeSorted localIn' #[t]) ((open_.map (·.1)).erase t)
              tbX memoX := by
          intro tbX memoX htX hmX
          refine { ctx := pre.ctx, phi0 := pre.phi0, outO := pre.outO, outM := pre.outM,
                   outI := pre.outI, locG := ?_, undG := ?_, nodup := ?_, outLU := ?_,
                   cover := ?_, tab := htX, memo := hmX,
                   locSorted := mergeSorted_strict hL's (by simp)
                     (fun x hx hxt => htL (by simp at hxt; rw [← hxt]; exact hx)) }
          · intro x hx
            rcases List.mem_append.mp (hmerge.mem_iff.mp hx) with h | h
            · exact hL'g x h
            · rw [List.mem_singleton] at h; rw [h]; exact htg
          · intro x hx; rw [hund2] at hx; exact hUng x (hUe x hx)
          · rw [hund2]
            refine ((hmerge.append_right _).trans ?_).nodup_iff.mpr hLUn
            rw [List.append_assoc]
            exact List.Perm.append_left _ (List.perm_cons_erase htU).symm
          · intro x hx
            refine ⟨fun h => ?_, fun h => ?_⟩
            · rcases List.mem_append.mp (hmerge.mem_iff.mp h) with h | h
              · exact (hout' x hx).1 h
              · rw [List.mem_singleton] at h; rw [h] at hx; exact htout hx
            · rw [hund2] at h; exact (hout' x hx).2 (hUe x h)
          · intro x hx
            rcases hcov' x hx with h | h | h
            · exact Or.inl (hmerge.mem_iff.mpr (List.mem_append_left _ h))
            · by_cases hxt : x = t
              · exact Or.inl (hmerge.mem_iff.mpr (List.mem_append_right _ (by simp [hxt])))
              · exact Or.inr (Or.inl (by rw [hund2]; exact (List.mem_erase_of_ne hxt).mpr h))
            · exact Or.inr (Or.inr h)
        have preB : ∀ (tbX : CTable) memoX, E.TabOK g.toList I.toList tbX → E.MemoOK memoX →
            E.NodePre g I O phi0 (outAll.push t) localIn' ((open_.map (·.1)).erase t)
              tbX memoX := by
          intro tbX memoX htX hmX
          have hpush : (outAll.push t).toList = outAll.toList ++ [t] := Array.toList_push
          refine { ctx := pre.ctx, phi0 := pre.phi0, outO := ?_, outM := ?_, outI := ?_,
                   locG := hL'g, undG := ?_, nodup := ?_, outLU := ?_, cover := ?_,
                   tab := htX, memo := hmX, locSorted := hL's }
          · intro x hx; rw [hpush]; exact List.mem_append_left _ (pre.outO x hx)
          · intro x hx
            rw [hpush, List.mem_append, List.mem_singleton] at hx
            rcases hx with h | h
            · exact pre.outM x h
            · rw [h]; exact (hgf t htg).1
          · intro x hx
            rw [hpush, List.mem_append, List.mem_singleton] at hx
            rcases hx with h | h
            · exact pre.outI x h
            · rw [h]; exact (hgf t htg).2.2.1
          · intro x hx; rw [hund2] at hx; exact hUng x (hUe x hx)
          · rw [hund2]
            exact List.Nodup.sublist (List.Sublist.append_left List.erase_sublist _) hLUn
          · intro x hx
            rw [hpush, List.mem_append, List.mem_singleton] at hx
            rw [hund2]
            rcases hx with h | h
            · exact ⟨(hout' x h).1, fun h' => (hout' x h).2 (hUe x h')⟩
            · rw [h]; exact ⟨htL, hUnn.not_mem_erase⟩
          · intro x hx
            rw [hpush, hund2]
            rcases hcov' x hx with h | h | h
            · exact Or.inl h
            · by_cases hxt : x = t
              · exact Or.inr (Or.inr (by simp [hxt]))
              · exact Or.inr (Or.inl ((List.mem_erase_of_ne hxt).mpr h))
            · exact Or.inr (Or.inr (List.mem_append_left _ h))
        have hcase : ∀ Y, E.Cons Y (I.toList ++ localIn.toList) outAll.toList →
            E.Cons Y (I.toList ++ (mergeSorted localIn' #[t]).toList) outAll.toList ∨
            E.Cons Y (I.toList ++ localIn'.toList) (outAll.push t).toList := by
          intro Y hY
          have hY' := hforce Y hY
          by_cases htY : t ∈ Y
          · left
            refine ⟨hY'.1, fun x hx => ?_, hY'.2.2⟩
            rcases List.mem_append.mp hx with h | h
            · exact hY'.2.1 x (List.mem_append_left _ h)
            · rcases List.mem_append.mp (hmerge.mem_iff.mp h) with h | h
              · exact hY'.2.1 x (List.mem_append_right _ h)
              · rw [List.mem_singleton] at h; rw [h]; exact htY
          · right
            refine ⟨hY'.1, hY'.2.1, fun x hx => ?_⟩
            rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
            rcases hx with h | h
            · exact hY'.2.2 x h
            · rw [h]; exact htY
        have hpre0 := pre.memo
        rw [← hm1] at hpre0
        split at h
        · -- stored first
          obtain ⟨⟨tb1, st4⟩, h1, h⟩ := bind_eq_ok h
          obtain ⟨tA, iA, cA, mA⟩ := hnode g I O phi0 outAll nOut _ _ tb st1 tb1 st4 h1
            (preA tb st1.memo pre.tab hpre0)
          obtain ⟨tB, iB, cB, mB⟩ := hnode g I O phi0 (outAll.push t) nOut localIn' _ tb1 st4 tb' st'
            h (preB tb1 st4.memo tA mA)
          refine ⟨tB, improvesT_trans iA iB, fun Y hY => ?_, mB⟩
          rcases hcase Y hY with hA | hB
          · exact (cA Y hA).mono iB
          · exact cB Y hB
        · -- unstored first
          obtain ⟨⟨tb1, st4⟩, h1, h⟩ := bind_eq_ok h
          obtain ⟨tB, iB, cB, mB⟩ := hnode g I O phi0 (outAll.push t) nOut localIn' _ tb st1 tb1 st4
            h1 (preB tb st1.memo pre.tab hpre0)
          obtain ⟨tA, iA, cA, mA⟩ := hnode g I O phi0 outAll nOut _ _ tb1 st4 tb' st' h
            (preA tb1 st4.memo tB mB)
          refine ⟨tA, improvesT_trans iB iA, fun Y hY => ?_, mA⟩
          rcases hcase Y hY with hA | hB
          · exact cA Y hA
          · exact (cB Y hB).mono iA
      · rename_i x hx
        exfalso
        have hne : open_.toList ≠ [] := by
          intro hnil
          apply hemp
          rw [Array.isEmpty_iff]
          apply Array.ext'
          simp [hnil]
        obtain ⟨⟨t, gt⟩, hpb⟩ := Option.ne_none_iff_exists'.mp (pickBranch_isSome hne)
        exact hx t gt hpb
  next => cases h

/-! ## The search invariant -/

/-- **The search invariant** (all four functions, every fuel). -/
theorem Env.search_spec {E : Env} (hE : E.WF) (limits : Limits) :
    ∀ fuel, E.SolvePSpec limits fuel ∧ E.SolveBodySpec limits fuel ∧ E.NodePSpec limits fuel ∧
      E.SplitPSpec limits fuel := by
  intro fuel
  induction fuel with
  | zero => exact E.specs_zero limits
  | succ fuel ih =>
    obtain ⟨hs, hb, hn, hp⟩ := ih
    exact ⟨E.solveP_step hE hb, E.solveBody_step hE hn, E.nodeP_step hE hn hp,
      E.splitP_step hE hs hp⟩

theorem Env.memoOK_empty (E : Env) : E.MemoOK {} := by
  intro g ent tb h
  simp at h

theorem toList_eq_nil_of_sub_empty {a : Array Nat} (h : ∀ t ∈ a.toList, t ∈ (#[] : Array Nat).toList) :
    a.toList = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro t ht
  simpa using h t ht

/-- **The component's table.** The table the search returns for a component
is valid (every entry a duplicate-free set of members with its exact `Δ` from
nothing stored), and for every minimum it has an entry at the minimum's count
of the component, at most the minimum's `Δ`. -/
theorem Env.component_table {E : Env} (hE : E.WF) {limits : Limits} {fuel : Nat} {st0 : SState}
    {tb : CTable} {st : SState}
    (h : E.cx.solveP limits fuel E.cx.members #[] #[] st0 = .ok (tb, st)) (hm0 : st0.memo = {}) :
    E.TabOK E.cx.members.toList [] tb ∧
      ∀ Y, IsMinimum E.dag E.w E.roots Y →
        HasAtT tb (partOf Y E.cx.members.toList).length (E.delta [] (partOf Y E.cx.members.toList))
          (partOf Y E.cx.members.toList) := by
  obtain ⟨_, I, O, hI, hO, _, htab, hcov⟩ := (E.search_spec hE limits fuel).1 E.cx.members #[] #[] st0
    tb st h (fun t ht => by simp at ht) (fun t ht => by simp at ht) (fun t ht => by simp at ht)
    (by rw [hm0]; exact E.memoOK_empty)
  have hIn := toList_eq_nil_of_sub_empty hI
  have hOn := toList_eq_nil_of_sub_empty hO
  rw [hIn] at htab hcov
  rw [hOn] at hcov
  refine ⟨htab, fun Y hY => hcov Y ⟨hY, fun t ht => by simp at ht, fun t ht => by simp at ht⟩⟩

end Ix.Compile.Verify.UniformModel
