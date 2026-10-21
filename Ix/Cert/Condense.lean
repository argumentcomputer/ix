import Ix.Cert.Statement
import Ix.CondenseM
import Ix.CompileCert.Canon.SccMain

/-! # The condensation's blocks and references (Route A, B9b, `HookFree`'s discharge, step 2)

The driver compiles the strongly connected components of the ground reference
graph (`Ix.CondenseM.run (groundSplit env).1`), and Pass 3's hook 2 reads each
block's references (`CondensedBlocks.blockRefs`, installed by
`FoldState.init` under the block's key). This file relates them to the
closure relation (`Ix.Cert.DependsOn`):

* `envSerial_get`: the driver's reference graph (`GraphM.envSerial`) holds,
  for each input constant, its `refsOf` (the graph does not read the
  environment, `Ix.graphConst_env`);
* `groundSplit_get`: the ground graph's references are the driver graph's. -/

namespace Ix.Cert.Condense

open Ix

/-! ## The driver's reference graph -/

/-- A lookup in a map made by inserting a list's entries: an entry of the
result is the last inserted under a key `==` to the looked-up one, or the
initial map's. -/
theorem foldl_insert_get_of {α β γ : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {P : α → γ → Prop} (key : β → α) (val : β → γ) :
    ∀ (l : List β) (m : Std.HashMap α γ), (∀ n v, m.get? n = some v → P n v) →
      (∀ x ∈ l, ∀ n, (key x == n) = true → P n (val x)) →
      ∀ n v, (l.foldl (fun m x => m.insert (key x) (val x)) m).get? n = some v → P n v := by
  intro l
  induction l with
  | nil => intro m hm _; exact hm
  | cons x l ih =>
    intro m hm hl
    rw [List.foldl_cons]
    refine ih _ (fun n v h => ?_) (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i same
      cases h
      exact hl x List.mem_cons_self n same
    · rw [← Std.HashMap.get?_eq_getElem?] at h
      exact hm n v h

/-- A key `==` to a listed entry's key looks the entry up. -/
theorem get_of_mem_toList {α β : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Std.HashMap α β} {k n : α} {v : β} (hm : (k, v) ∈ m.toList) (hk : (k == n) = true) :
    m.get? n = some v := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList]
  exact ⟨k, BEq.symm hk, hm⟩

/-- **The driver's reference graph holds each constant's `refsOf`.** -/
theorem envSerial_get {env : Ix.Environment} {n : Ix.Name} {rs : Ix.Set Ix.Name}
    (h : (GraphM.envSerial env).get? n = some rs) :
    ∃ ci, env.consts.get? n = some ci ∧ rs = refsOf ci := by
  unfold GraphM.envSerial at h
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, List.forIn_pure_yield_eq_foldl] at h
  change Std.HashMap.get? (List.foldl (fun b a => Std.HashMap.insert b a.fst (GraphM.run env GraphState.init (graphConst a.snd)).fst) ∅ env.consts.toList) n = some rs at h
  refine foldl_insert_get_of (P := fun n rs => ∃ ci, env.consts.get? n = some ci ∧ rs = refsOf ci)
    (fun x : Ix.Name × Ix.ConstantInfo => x.1)
    (fun x => (GraphM.run env .init (graphConst x.2)).1) env.consts.toList ∅ (fun n v h => ?_) (fun x hx n hn => ?_) n rs h
  · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h; cases h
  · refine ⟨x.2, get_of_mem_toList hx hn, ?_⟩
    unfold refsOf
    rw [graphConst_env x.2 env { consts := {} } .init]

/-- A fold keeps an invariant that each step on a listed element keeps. -/
theorem foldl_inv {β σ : Type} (I : σ → Prop) (f : σ → β → σ) :
    ∀ (l : List β) (init : σ), I init → (∀ s x, x ∈ l → I s → I (f s x)) → I (l.foldl f init) := by
  intro l
  induction l with
  | nil => intro init h _; exact h
  | cons x l ih =>
    intro init h step
    exact ih _ (step init x List.mem_cons_self h) fun s y hy hs => step s y (List.mem_cons_of_mem _ hy) hs

/-- A filtering fold over a set keeps only its elements. -/
theorem filterFold_contains {rs : Ix.Set Ix.Name} {p : Ix.Name → Bool} {r : Ix.Name}
    (h : (rs.fold (init := ({} : Ix.Set Ix.Name)) fun s r => if p r then s else s.insert r).contains r = true) :
    rs.contains r = true := by
  rw [Std.HashSet.fold_eq_foldl_toList] at h
  refine foldl_inv (fun s : Ix.Set Ix.Name => ∀ r, s.contains r = true → rs.contains r = true) _ rs.toList {}
    (fun r h => by simp at h) (fun s x hx hs r hr => ?_) r h
  split at hr
  · exact hs r hr
  · rw [Std.HashSet.contains_insert] at hr
    rcases Bool.or_eq_true_iff.mp hr with e | hr
    · rw [← Std.HashSet.contains_congr e]
      exact Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_of_mem_toList hx)
    · exact hs r hr

/-- **The ground graph's references are the driver graph's**: an entry of
`(groundSplit env).1` at `n` holds only references of `envSerial env`'s entry
at `n`. -/
theorem groundSplit_get {env : Ix.Environment} {n : Ix.Name} {rs : Ix.Set Ix.Name}
    (h : (groundSplit env).1.get? n = some rs) :
    ∃ rs₀, (GraphM.envSerial env).get? n = some rs₀ ∧ ∀ r, rs.contains r = true → rs₀.contains r = true := by
  unfold groundSplit at h
  dsimp only at h
  split at h
  · exact ⟨rs, h, fun _ h => h⟩
  · rw [Std.HashMap.fold_eq_foldl_toList] at h
    refine foldl_inv (fun m : Ix.Map Ix.Name (Ix.Set Ix.Name) => ∀ n rs, m.get? n = some rs →
        ∃ rs₀, (GraphM.envSerial env).get? n = some rs₀ ∧ ∀ r, rs.contains r = true → rs₀.contains r = true)
      _ _ {} (fun n rs h => by rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h; cases h)
      (fun m x hx hm n rs h => ?_) n rs h
    split at h
    · exact hm n rs h
    · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i same
        cases h
        exact ⟨x.2, get_of_mem_toList hx same, fun r hr => filterFold_contains hr⟩
      · rw [← Std.HashMap.get?_eq_getElem?] at h
        exact hm n rs h

/-- **A ground graph edge is a closure edge**: a reference of the ground
graph's entry at `n` is a constant `n` depends on. -/
theorem groundSplit_dependsOn {env : Ix.Environment} {n r : Ix.Name} {rs : Ix.Set Ix.Name}
    (h : (groundSplit env).1.get? n = some rs) (hr : rs.contains r = true) : DependsOn env n r := by
  obtain ⟨rs₀, h₀, sub⟩ := groundSplit_get h
  obtain ⟨ci, hci, rfl⟩ := envSerial_get h₀
  exact ⟨ci, hci, .inl (sub r hr)⟩

end Ix.Cert.Condense
