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

/-! ## A block's references -/

/-- `CondenseM.run`'s last loop: each block's references, the union of its
members' references outside the block. -/
def blockRefsOf (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) (blocks : Ix.Map Ix.Name (Ix.Set Ix.Name)) :
    Ix.Map Ix.Name (Ix.Set Ix.Name) := Id.run do
  let mut blockRefs : Ix.Map Ix.Name (Ix.Set Ix.Name) := {}
  for (lo, all) in blocks do
    let mut rs : Ix.Set Ix.Name := {}
    for a in all do
      rs := rs.union (refs.getD a {})
    rs := rs.filter (!all.contains ·)
    blockRefs := blockRefs.insert lo rs
  return blockRefs

theorem blockRefs_eq (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) :
    (CondenseM.run refs).blockRefs = blockRefsOf refs (CondenseM.run refs).blocks := rfl

/-- A fold inserting a listed entry under a key `==` to `n` ends with `n` a key. -/
theorem foldl_insert_contains_of {α β γ : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (key : β → α) (val : β → γ) {n : α} {x : β} :
    ∀ (l : List β) (m : Std.HashMap α γ), x ∈ l → (key x == n) = true →
      (l.foldl (fun m x => m.insert (key x) (val x)) m).contains n = true := by
  have keep : ∀ (l : List β) (m : Std.HashMap α γ), m.contains n = true →
      (l.foldl (fun m x => m.insert (key x) (val x)) m).contains n = true := by
    intro l
    induction l with
    | nil => intro m h; exact h
    | cons y l ih =>
      intro m h
      exact ih _ (by rw [Std.HashMap.contains_insert, h, Bool.or_true])
  intro l
  induction l with
  | nil => intro _ h; cases h
  | cons y l ih =>
    intro m hx hk
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact keep _ _ (by rw [Std.HashMap.contains_insert, hk, Bool.true_or])
    · exact ih _ hx hk

/-- **A block's references are its members' references**: a block of
`blocks` at `rep` has an entry in `blockRefsOf refs blocks`, and each of its
references is a reference of one of its members. -/
theorem blockRefsOf_get {refs blocks : Ix.Map Ix.Name (Ix.Set Ix.Name)} {rep : Ix.Name}
    {all : Ix.Set Ix.Name} (hb : blocks.get? rep = some all) :
    ∃ rs, (blockRefsOf refs blocks).get? rep = some rs ∧
      ∀ r, rs.contains r = true → ∃ a, all.contains a = true ∧ (refs.getD a {}).contains r = true := by
  have hb' := hb
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hb'
  obtain ⟨k, rk, hk⟩ := hb'
  -- the union of a block's members' references, filtered
  have union : ∀ (A : Ix.Set Ix.Name) r, (List.foldl (fun (s : Ix.Set Ix.Name) a => s.union (refs.getD a {})) {} A.toList).contains r = true →
      ∃ a, A.contains a = true ∧ (refs.getD a {}).contains r = true := by
    intro A r h
    refine foldl_inv (fun s : Ix.Set Ix.Name => ∀ r, s.contains r = true →
        ∃ a, A.contains a = true ∧ (refs.getD a {}).contains r = true) _ A.toList {}
      (fun r h => by simp at h) (fun s a ha hs r hr => ?_) r h
    change (s ∪ refs.getD a {}).contains r = true at hr
    rw [Std.HashSet.contains_union] at hr
    rcases Bool.or_eq_true_iff.mp hr with hr | hr
    · exact hs r hr
    · exact ⟨a, Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_of_mem_toList ha), hr⟩
  unfold blockRefsOf
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, Std.HashSet.forIn_eq_forIn_toList,
    List.forIn_pure_yield_eq_foldl, pure_bind]
  let F : Ix.Name × Ix.Set Ix.Name → Ix.Set Ix.Name := fun a =>
    Std.HashSet.filter (fun x => !a.snd.contains x)
      (List.foldl (fun (b : Ix.Set Ix.Name) a => Std.HashSet.union b (refs.getD a ∅)) ∅ a.snd.toList)
  change ∃ rs, (List.foldl (fun (m : Ix.Map Ix.Name (Ix.Set Ix.Name)) x => m.insert x.1 (F x)) ∅ blocks.toList).get? rep = some rs ∧ _
  have hc := foldl_insert_contains_of (fun x : Ix.Name × Ix.Set Ix.Name => x.1) F blocks.toList ∅ hk
    (BEq.symm rk)
  obtain ⟨rs, hrs⟩ : ∃ rs, (List.foldl (fun (m : Ix.Map Ix.Name (Ix.Set Ix.Name)) x => m.insert x.1 (F x)) ∅ blocks.toList).get? rep = some rs :=
    Option.isSome_iff_exists.mp (by
      rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?]; exact hc)
  refine ⟨rs, hrs, ?_⟩
  refine foldl_insert_get_of (P := fun n v => (n == rep) = true → ∀ r, v.contains r = true →
      ∃ a, all.contains a = true ∧ (refs.getD a {}).contains r = true) (fun x => x.1) F blocks.toList ∅
    (fun n v h => by rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h; cases h)
    (fun x hx n hn hnr r hr => ?_) rep rs hrs (BEq.refl rep)
  have hx2 : blocks.get? rep = some x.2 := get_of_mem_toList hx (BEq.trans hn hnr)
  rw [hb] at hx2
  cases Option.some.inj hx2
  exact union _ r (Std.HashSet.contains_of_contains_filter hr)

/-- **The condensation's block references are its members' references.** -/
theorem condense_blockRefs {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {rep : Ix.Name} {all : Ix.Set Ix.Name}
    (hb : (CondenseM.run refs).blocks.get? rep = some all) :
    ∃ rs, (CondenseM.run refs).blockRefs.get? rep = some rs ∧
      ∀ r, rs.contains r = true → ∃ a, all.contains a = true ∧ (refs.getD a {}).contains r = true := by
  rw [blockRefs_eq]
  exact blockRefsOf_get hb

/-! ## The condensation, stage by stage

`CondenseM.run` as the composition of its loops (`blocks_eq`, by `rfl`): the
nodes and their positions (`nodesOf`), the edges (`adjOf`), Tarjan's
components, each node's representative (`rootNames`), the nodes in discovery
order (`discOf`), and the blocks (`blocksOfDisc`). -/

/-- `CondenseM.run`'s first loop. -/
def nodesOf (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) : Array (Ix.Name × Ix.Set Ix.Name) × Std.HashMap Ix.Name Nat := Id.run do
  let mut entries : Array (Ix.Name × Ix.Set Ix.Name) := #[]
  let mut idx : Std.HashMap Ix.Name Nat := {}
  let mut lastPct : Nat := 0
  for (name, rs) in refs do
    idx := idx.insert name entries.size
    entries := entries.push (name, rs)
    if false && (0 : Nat) > 0 then
      let pct := (entries.size * 100) / 0
      if pct >= lastPct + 10 then
        lastPct := pct
  return (entries, idx)

def adjOf (entries : Array (Ix.Name × Ix.Set Ix.Name)) (idx : Std.HashMap Ix.Name Nat) : Array (Array Nat) :=
  entries.map fun (_, rs) => Id.run do
    let mut succs : Array Nat := #[]
    for ref in rs do
      if let some j := idx.get? ref then
        succs := succs.push j
    return succs

def rootNames (names : Array Ix.Name) (c : Ix.Compile.Canon.Condensation)
    (hr : ∀ p ∈ c.comps.zip c.roots, p.2 < names.size) : Vector Ix.Name names.size := Id.run do
  let mut rootName : Vector Ix.Name names.size := names.toVector
  for h : p in c.comps.zip c.roots do
    have hr : p.2 < names.size := hr p h
    let rn := names[p.2]
    for v in p.1 do
      rootName := rootName.setIfInBounds v rn
  return rootName

def discOf (names : Array Ix.Name) (c : Ix.Compile.Canon.Condensation) (rootName : Vector Ix.Name names.size)
    (hv : ∀ v ∈ c.order, v < names.size) : Std.HashMap UInt64 (Ix.Name × Ix.Name) := Id.run do
  let mut byDiscovery : Std.HashMap UInt64 (Ix.Name × Ix.Name) := {}
  let mut d : Nat := 0
  for h : v in c.order do
    have hv : v < names.size := hv v h
    byDiscovery := byDiscovery.insert d.toUInt64 (names[v], rootName[v])
    d := d + 1
  return byDiscovery

def blocksOfDisc (byDiscovery : Std.HashMap UInt64 (Ix.Name × Ix.Name)) : Ix.Map Ix.Name (Ix.Set Ix.Name) := Id.run do
  let mut blocks : Ix.Map Ix.Name (Ix.Set Ix.Name) := {}
  let mut lowLinks : Map Ix.Name Ix.Name := {}
  for (_, (name, lowName)) in byDiscovery do
    lowLinks := lowLinks.insert name lowName
    blocks := blocks.alter lowName fun x => match x with
      | .some s => .some (s.insert name)
      | .none => .some {name}
  return blocks

/-- The condensation's nodes, as names. -/
def namesOf (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) : Array Ix.Name := (nodesOf refs).1.map (·.1)

/-- The condensation's edges. -/
def edgesOf (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) : Array (Array Nat) :=
  adjOf (nodesOf refs).1 (nodesOf refs).2

/-- Tarjan's components of the condensation's graph. -/
def compsOf (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) : Ix.Compile.Canon.Condensation :=
  (Ix.Compile.Canon.condensation (edgesOf refs)).get (Ix.CompileCert.Canon.condensation_isSome _)

theorem compsOf_eq (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) :
    Ix.Compile.Canon.condensation (edgesOf refs) = some (compsOf refs) :=
  (Option.some_get _).symm

theorem namesOf_size (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) :
    (namesOf refs).size = (edgesOf refs).size := by
  simp only [namesOf, edgesOf, adjOf, Array.size_map]

/-- **`CondenseM.run`'s blocks, stage by stage.** -/
theorem blocks_eq (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) :
    ∃ hr hv, (CondenseM.run refs).blocks =
      blocksOfDisc (discOf (namesOf refs) (compsOf refs) (rootNames (namesOf refs) (compsOf refs) hr) hv) := by
  refine ⟨fun p h => ?_, fun v h => ?_, rfl⟩
  · rw [namesOf_size]; exact Ix.CompileCert.Canon.condensation_roots_lt (compsOf_eq refs) (Array.of_mem_zip h).2
  · rw [namesOf_size]; exact Ix.CompileCert.Canon.condensation_order_lt (compsOf_eq refs) h

end Ix.Cert.Condense
