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
  cover : ∀ x ∈ g.toList, x ∈ localIn.toList ∨ x ∈ und.toList ∨ x ∈ outAll.toList
  tab : E.TabOK g.toList I.toList tb
  memo : E.MemoOK memo

/-- The postcondition of a search node. -/
def Env.NodePost (E : Env) (g I : Array Nat) (outAll localIn : Array Nat) (tb tb' : CTable)
    (memo' : Std.HashMap (Array Nat × Array Nat) CTable) : Prop :=
  E.TabOK g.toList I.toList tb' ∧ Improves tb tb' ∧
    (∀ Y, E.Cons Y (I.toList ++ localIn.toList) outAll.toList →
      HasAt tb' (partOf Y g.toList).length (E.delta I.toList (partOf Y g.toList))) ∧
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
  ∀ e, some e ∈ comb.toList → e.2.toList.Nodup ∧ (∀ x ∈ L, x ∈ e.2.toList) ∧
    (∀ x ∈ e.2.toList, x ∈ L ∨ x ∈ U) ∧ e.1 = E.delta I e.2.toList

/-- Every minimum respecting the node has a combination at its count. -/
def Env.CombCov (E : Env) (I L U O : List Nat) (comb : CTable) : Prop :=
  ∀ Y, E.Cons Y (I ++ L) O → ∃ e, some e ∈ comb.toList ∧ e.2.size = (L ++ partOf Y U).length ∧
    e.1 ≤ E.delta I (L ++ partOf Y U)

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
    have hcombOK : E.CombOK I.toList L (U ++ hg.toList) (comb.conv sub) := by
      intro e he
      obtain ⟨k, hk⟩ := mem_toList_getElem! he
      obtain ⟨_, ec, es, hec, hes, rfl⟩ := hce k e hk
      obtain ⟨hecn, hecL, hecs, hecv⟩ := hpre.combOK ec hec
      obtain ⟨hesn, hesh, hesv⟩ := htabh.mem hes
      have hperm := mergeSorted_perm ec.2 es.2
      have hdisj : ∀ x ∈ ec.2.toList, x ∉ es.2.toList :=
        fun x hx hx' => hLU_h x (hecs x hx) (hesh x hx')
      refine ⟨hperm.nodup_iff.mpr (nodup_app hecn hesn hdisj),
        fun x hx => hperm.mem_iff.mpr (List.mem_append_left _ (hecL x hx)), fun x hx => ?_, ?_⟩
      · rcases List.mem_append.mp (hperm.mem_iff.mp hx) with h | h
        · rcases hecs x h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_append_left _ h)
        · exact Or.inr (List.mem_append_right _ (hesh x h))
      · simp only
        rw [E.delta_perm hperm, E.delta_append, hecv, hesv,
          hshift ec.2.toList es.2.toList hecn hecL hecs hesh]
    have hcombCov : E.CombCov I.toList L (U ++ hg.toList) outAll.toList (comb.conv sub) := by
      intro Y hY
      obtain ⟨ec, hec, hecsz, hecv⟩ := hpre.combCov Y hY
      have hYc : E.Cons Y Ih.toList Oh.toList :=
        ⟨hY.1, fun t ht => hY.2.1 t (by have := hIh t ht; rw [hin] at this; exact this),
          fun t ht => hY.2.2 t (hOh t ht)⟩
      obtain ⟨es, hes, hesv⟩ := hcovh Y hYc
      have hesz := (htabh _ es hes).1
      obtain ⟨ecv, hecv', hle⟩ := conv_hasAt hec (getElem!_mem_toList hes)
      have hecvsz := (hce _ ecv hecv').1
      refine ⟨ecv, getElem!_mem_toList hecv', ?_, ?_⟩
      · rw [hecvsz, hecsz, hesz, partOf_append]
        simp only [List.length_append]
        omega
      · have hpU : ∀ t ∈ partOf Y U, t ∈ U := fun t ht => (partOf_sub t ht).1
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
        rw [partOf_append, ← List.append_assoc, E.delta_append, heq]
        omega
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

end Ix.Compile.Verify.UniformModel
