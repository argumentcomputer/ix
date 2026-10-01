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
  Entries tb (fun e => e.2.toList.Nodup ∧ (∀ x ∈ e.2.toList, x ∈ g) ∧ e.1 = E.delta I e.2.toList)

/-- Every minimum respecting `(I, O)` has an entry at its count of `g`, at most
its `Δ`. -/
def Env.Covers (E : Env) (g I O : List Nat) (tb : CTable) : Prop :=
  ∀ Y, E.Cons Y I O → HasAt tb (partOf Y g).length (E.delta I (partOf Y g))

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
    (S := e.2.toList) hesub hen
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
  exact trim_hasAt (hcov Y hY) (fun b hb => E.prune_ok hE hctx htab hb hY)

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

end Ix.Compile.Verify.UniformModel
