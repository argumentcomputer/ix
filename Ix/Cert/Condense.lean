import Ix.Cert.Statement
import Ix.CondenseM
import Ix.CompileCert.Canon.SccMain
import Ix.Cert.CondenseRoots

/-! # The condensation's blocks and references

The driver compiles the strongly connected components of the ground reference
graph (`Ix.CondenseM.run (groundSplit env).1`). The scheduler uses each
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

/-! ## Paths in the reference graph and closures -/

/-- A path in the reference graph `refs` through its nodes (its keys), its
end taken up to `Ix.Name`'s `==` (names compared by their stored hashes). -/
inductive Path (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) : Ix.Name → Ix.Name → Prop
  | refl {x y : Ix.Name} : (x == y) = true → Path refs x y
  | step {x z y : Ix.Name} {rs : Ix.Set Ix.Name} : refs.get? x = some rs → rs.contains z = true →
      (refs.get? z).isSome = true → Path refs z y → Path refs x y

/-- **A closure holds every constant a path of the ground graph reaches from
one of its constants.** -/
theorem closure_path {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    (hcl : IsClosure env roots sub) {x y : Ix.Name}
    (hp : Path (groundSplit { consts := env.consts }).1 x y) (hx : (sub.consts.get? x).isSome = true) :
    (sub.consts.get? y).isSome = true := by
  induction hp with
  | refl e =>
    rw [Std.HashMap.get?_eq_getElem?] at hx ⊢
    rw [← Std.HashMap.getElem?_congr e]
    exact hx
  | @step x z y rs hrs hz hzk _ ih =>
    apply ih
    have hxr : Reaches env roots x := by
      by_contra hr
      rw [(hcl x).2 hr] at hx
      cases hx
    have hd : DependsOn { consts := env.consts } x z := groundSplit_dependsOn hrs hz
    have hzr : Reaches env roots z := Reaches.step hxr hd
    obtain ⟨rs', hrs'⟩ := Option.isSome_iff_exists.mp hzk
    obtain ⟨rs₀, h₀, -⟩ := groundSplit_get hrs'
    obtain ⟨ci, hci, -⟩ := envSerial_get h₀
    rw [(hcl z).1 hzr]
    change (env.consts.get? z).isSome = true
    rw [show env.consts.get? z = some ci from hci]
    rfl

/-! ## The nodes and the edges -/

/-- The first loop's step. -/
def nodeStep (b : Array (Ix.Name × Ix.Set Ix.Name) × Std.HashMap Ix.Name Nat × Nat) (a : Ix.Name × Ix.Set Ix.Name) :
    Array (Ix.Name × Ix.Set Ix.Name) × Std.HashMap Ix.Name Nat × Nat :=
  (b.fst.push (a.fst, a.snd), b.snd.fst.insert a.fst b.fst.size, b.snd.snd)

/-- Every position a name has is a node of that name. -/
def Positions (b : Array (Ix.Name × Ix.Set Ix.Name) × Std.HashMap Ix.Name Nat × Nat) : Prop :=
  ∀ n j, b.2.1.get? n = some j → ∃ hj : j < b.1.size, (b.1[j].1 == n) = true

theorem nodeStep_foldl : ∀ (l : List (Ix.Name × Ix.Set Ix.Name)) b,
    (l.foldl nodeStep b).1.toList = b.1.toList ++ l ∧ (Positions b → Positions (l.foldl nodeStep b)) := by
  intro l
  induction l with
  | nil => intro b; exact ⟨by simp, id⟩
  | cons a l ih =>
    intro b
    rw [List.foldl_cons]
    refine ⟨by rw [(ih _).1]; simp [nodeStep], fun hb => (ih _).2 ?_⟩
    intro n j h
    simp only [nodeStep] at h ⊢
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i same
      cases h
      exact ⟨by simp, by simpa using same⟩
    · rw [← Std.HashMap.get?_eq_getElem?] at h
      obtain ⟨hj, e⟩ := hb n j h
      exact ⟨by simp; omega, by rw [Array.getElem_push_lt hj]; exact e⟩

/-- **The condensation's nodes**: the graph's entries in its iteration order,
each name's position a node of that name. -/
theorem nodesOf_spec (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) :
    (nodesOf refs).1.toList = refs.toList ∧
      ∀ n j, (nodesOf refs).2.get? n = some j →
        ∃ hj : j < (nodesOf refs).1.size, ((nodesOf refs).1[j].1 == n) = true := by
  have key := nodeStep_foldl refs.toList (#[], ∅, 0)
  have e : nodesOf refs = ((refs.toList.foldl nodeStep (#[], ∅, 0)).1, (refs.toList.foldl nodeStep (#[], ∅, 0)).2.1) := by
    unfold nodesOf
    simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, List.forIn_pure_yield_eq_foldl, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [e]
  exact ⟨by simpa using key.1, key.2 fun n j h => by
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h; cases h⟩

/-- A loop in `Id` keeps an invariant of its state that each step keeps. -/
theorem forIn_inv {α σ : Type} (I : σ → Prop) (f : α → σ → Id (ForInStep σ)) :
    ∀ (l : List α), (∀ x ∈ l, ∀ s, I s → I (f x s).value) → ∀ s, I s → I (forIn (m := Id) l s f) := by
  intro l
  induction l with
  | nil => intro _ s hs; exact hs
  | cons x l ih =>
    intro hstep s hs
    rw [List.forIn_cons]
    have hx := hstep x List.mem_cons_self s hs
    cases hf : f x s with
    | done s' => rw [hf] at hx; exact hx
    | yield s' =>
      rw [hf] at hx
      exact ih (fun y hy => hstep y (List.mem_cons_of_mem _ hy)) s' hx

/-- **An edge of the condensation's graph is a reference**: a successor `j`
of node `i` is the position of a reference of node `i`'s entry. -/
theorem adjOf_mem {E : Array (Ix.Name × Ix.Set Ix.Name)} {I : Std.HashMap Ix.Name Nat} {i j : Nat}
    (hi : i < E.size) (hj : j ∈ (adjOf E I)[i]?.getD #[]) :
    ∃ ref, E[i].2.contains ref = true ∧ I.get? ref = some j := by
  unfold adjOf at hj
  rw [Array.getElem?_map, Array.getElem?_eq_getElem hi] at hj
  simp only [Option.map_some, Option.getD_some, Id.run, Std.HashSet.forIn_eq_forIn_toList] at hj
  refine forIn_inv (fun s : Array Nat => ∀ j ∈ s, ∃ ref, E[i].2.contains ref = true ∧ I.get? ref = some j)
    _ _ (fun ref href s hs => ?_) #[] (fun _ h => by simp at h) j hj
  have hc : E[i].2.contains ref = true := Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_of_mem_toList href)
  split
  · rename_i k hk
    intro j hj
    rcases Array.mem_push.mp hj with hj | rfl
    · exact hs j hj
    · exact ⟨ref, hc, hk⟩
  · exact hs

/-- A path extended by an edge. -/
theorem Path.snoc {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {x y y' z : Ix.Name} {rs : Ix.Set Ix.Name}
    (p : Path refs x y) (hy : (y == y') = true) (hrs : refs.get? y' = some rs) (hz : rs.contains z = true)
    (hzk : (refs.get? z).isSome = true) : Path refs x z := by
  induction p with
  | refl e =>
    refine Path.step ?_ hz hzk (Path.refl (BEq.refl z))
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr (BEq.trans e hy), ← Std.HashMap.get?_eq_getElem?]
    exact hrs
  | step h₁ h₂ h₃ _ ih => exact Path.step h₁ h₂ h₃ (ih hy)

/-- A node is an entry of the graph. -/
theorem node_get {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {v : Nat} (hv : v < (nodesOf refs).1.size) :
    refs.get? (nodesOf refs).1[v].1 = some (nodesOf refs).1[v].2 := by
  have hm : ((nodesOf refs).1[v].1, (nodesOf refs).1[v].2) ∈ refs.toList := by
    rw [← (nodesOf_spec refs).1]
    exact Array.getElem_mem_toList hv
  exact get_of_mem_toList hm (BEq.refl _)

/-- **Reachability in the condensation's graph is a path of references.** -/
theorem reach_path {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {u w : Nat}
    (r : Ix.CompileCert.Canon.Reach (Ix.CompileCert.Canon.filt (edgesOf refs)) u w)
    (hu : u < (nodesOf refs).1.size) :
    ∃ hw : w < (nodesOf refs).1.size, Path refs (nodesOf refs).1[u].1 (nodesOf refs).1[w].1 := by
  induction r with
  | refl => exact ⟨hu, Path.refl (BEq.refl _)⟩
  | @tail v w _ e ih =>
    obtain ⟨hv, p⟩ := ih
    obtain ⟨hw₁, -⟩ := Ix.CompileCert.Canon.edge_filt.mp e
    obtain ⟨ref, href, hidx⟩ := adjOf_mem hv hw₁
    obtain ⟨hw, hname⟩ := (nodesOf_spec refs).2 ref w hidx
    refine ⟨hw, p.snoc (BEq.refl _) (node_get hv) ?_ (by rw [node_get hw]; rfl)⟩
    rw [← Std.HashSet.contains_congr (BEq.symm hname)]
    exact href

/-! ## Each node's representative -/

theorem setIfInBounds_foldl_get {n : Nat} {w : Ix.Name} {v : Nat} (hv : v < n) :
    ∀ (l : List Nat) (s : Vector Ix.Name n),
      (l.foldl (fun b a => b.setIfInBounds a w) s)[v] = if v ∈ l then w else s[v] := by
  intro l
  induction l with
  | nil => intro s; simp
  | cons a l ih =>
    intro s
    rw [List.foldl_cons, ih]
    by_cases hl : v ∈ l
    · simp [hl]
    · by_cases ha : a = v
      · subst ha; simp [hl]
      · simp [hl, ha, Ne.symm ha]

/-- **Each node's representative is its component's root's name.** -/
theorem rootNames_get {names : Array Ix.Name} {c : Ix.Compile.Canon.Condensation}
    {hr : ∀ p ∈ c.comps.zip c.roots, p.2 < names.size}
    (huniq : ∀ (k k' : Nat) (c₁ c₂ : Array Nat) (v : Nat),
      c.comps[k]? = some c₁ → c.comps[k']? = some c₂ → v ∈ c₁ → v ∈ c₂ → k = k')
    {k r v : Nat} {comp : Array Nat} (hk : c.comps[k]? = some comp) (hrk : c.roots[k]? = some r)
    (hvc : v ∈ comp) (hv : v < names.size) (hrn : r < names.size) :
    (rootNames names c hr)[v] = names[r] := by
  unfold rootNames
  simp only [Id.run, Array.forIn_pure_yield_eq_foldl, pure_bind, Array.forIn'_pure_yield_eq_foldl]
  -- the pairs of the zip that hold `v` all name `r`
  have good : ∀ p ∈ c.comps.zip c.roots, v ∈ p.1 → p.2 = r := by
    intro p hp hvp
    obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.mp hp
    rw [Array.getElem_zip] at e
    subst e
    have hi₁ : i < c.comps.size := by rw [Array.size_zip] at hi; omega
    have hi₂ : i < c.roots.size := by rw [Array.size_zip] at hi; omega
    have := huniq i k _ comp v (Array.getElem?_eq_getElem hi₁) hk hvp hvc
    subst this
    rw [Array.getElem?_eq_getElem hi₂] at hrk
    exact Option.some.inj hrk
  have hk₁ : k < c.comps.size := by
    rcases Nat.lt_or_ge k c.comps.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hk; cases hk
  have hk₂ : k < c.roots.size := by
    rcases Nat.lt_or_ge k c.roots.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hrk; cases hrk
  have hmem : (comp, r) ∈ c.comps.zip c.roots := by
    rw [Array.mem_iff_getElem]
    refine ⟨k, by rw [Array.size_zip]; omega, ?_⟩
    rw [Array.getElem_zip, Option.some.inj ((Array.getElem?_eq_getElem hk₁).symm.trans hk),
      Option.some.inj ((Array.getElem?_eq_getElem hk₂).symm.trans hrk)]
  change (Array.foldl (fun b (x : {p // p ∈ c.comps.zip c.roots}) =>
      Array.foldl (fun b a => b.setIfInBounds a (names[x.val.snd]'(hr _ x.property))) b x.val.fst) names.toVector
      (c.comps.zip c.roots).attach)[v] = names[r]
  rw [← Array.foldl_toList]
  -- along the list: a step on a pair holding `v` writes `names[r]`, the others leave it
  have step : ∀ (x : {p // p ∈ c.comps.zip c.roots}) (s : Vector Ix.Name names.size),
      (Array.foldl (fun b a => b.setIfInBounds a (names[x.val.snd]'(hr _ x.property))) s x.val.fst)[v] =
        if v ∈ x.val.fst then names[r] else s[v] := by
    intro x s
    rw [← Array.foldl_toList, setIfInBounds_foldl_get hv]
    by_cases hx : v ∈ x.val.fst
    · have e := good x.val x.property hx
      simp only [Array.mem_toList_iff, hx, ↓reduceIte]
      congr 1
    · simp [hx]
  have keep : ∀ (l : List {p // p ∈ c.comps.zip c.roots}) (s : Vector Ix.Name names.size), s[v] = names[r] →
      (l.foldl (fun b x => Array.foldl (fun b a => b.setIfInBounds a (names[x.val.snd]'(hr _ x.property))) b x.val.fst) s)[v] =
        names[r] := by
    intro l
    induction l with
    | nil => intro s h; exact h
    | cons x l ih =>
      intro s h
      rw [List.foldl_cons]
      refine ih _ ?_
      rw [step]
      split <;> simp_all
  have hit : ∀ (l : List {p // p ∈ c.comps.zip c.roots}) (s : Vector Ix.Name names.size),
      ⟨(comp, r), hmem⟩ ∈ l →
      (l.foldl (fun b x => Array.foldl (fun b a => b.setIfInBounds a (names[x.val.snd]'(hr _ x.property))) b x.val.fst) s)[v] =
        names[r] := by
    intro l
    induction l with
    | nil => intro _ h; cases h
    | cons x l ih =>
      intro s h
      rw [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | h
      · refine keep _ _ ?_
        rw [step]
        simp [hvc]
      · exact ih _ h
  exact hit _ _ (by rw [Array.mem_toList_iff]; exact Array.mem_attach _ _)

/-! ## The nodes in discovery order, and the blocks -/

/-- **The discovery map holds nodes with their representatives.** -/
theorem discOf_get {names : Array Ix.Name} {c : Ix.Compile.Canon.Condensation}
    {rn : Vector Ix.Name names.size} {hv : ∀ v ∈ c.order, v < names.size} {key : UInt64}
    {val : Ix.Name × Ix.Name} (h : (discOf names c rn hv).get? key = some val) :
    ∃ (v : Nat) (hv : v < names.size), val = (names[v], rn[v]) := by
  unfold discOf at h
  simp only [Id.run, Array.forIn'_pure_yield_eq_foldl] at h
  change (Array.foldl (fun b (x : {v // v ∈ c.order}) =>
    (b.fst.insert b.snd.toUInt64 ((names[x.val]'(hv _ x.property)), rn[x.val]'(hv _ x.property)), b.snd + 1))
      ((∅ : Std.HashMap UInt64 (Ix.Name × Ix.Name)), 0) c.order.attach).fst.get? key = some val at h
  rw [← Array.foldl_toList] at h
  refine foldl_inv (fun s : Std.HashMap UInt64 (Ix.Name × Ix.Name) × Nat => ∀ key val, s.1.get? key = some val →
      ∃ (v : Nat) (hv : v < names.size), val = (names[v], rn[v])) _ _ _
    (fun key val h => by rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h; cases h)
    (fun s x _ hs key val h => ?_) key val h
  dsimp only at h
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
  split at h
  · cases h
    exact ⟨x.val, hv _ x.property, rfl⟩
  · rw [← Std.HashMap.get?_eq_getElem?] at h
    exact hs key val h

/-- **A block's members come from the discovery map**: each member of the
block at `rep` hashes like a node's name whose representative hashes like
`rep`. -/
theorem blocksOfDisc_mem {bd : Std.HashMap UInt64 (Ix.Name × Ix.Name)} {rep x : Ix.Name}
    {all : Ix.Set Ix.Name} (h : (blocksOfDisc bd).get? rep = some all) (hx : all.contains x = true) :
    ∃ key val, bd.get? key = some val ∧ (val.2 == rep) = true ∧ (val.1 == x) = true := by
  unfold blocksOfDisc at h
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, List.forIn_pure_yield_eq_foldl] at h
  change (List.foldl (fun (b : Ix.Map Ix.Name (Ix.Set Ix.Name) × Ix.Map Ix.Name Ix.Name) a =>
      (Std.HashMap.alter b.fst a.2.snd fun x => match x with
        | some s => some (Std.HashSet.insert s a.2.fst)
        | none => some {a.2.fst},
       Std.HashMap.insert b.snd a.2.fst a.2.snd)) (∅, ∅) bd.toList).fst.get? rep = some all at h
  refine foldl_inv (fun s : Ix.Map Ix.Name (Ix.Set Ix.Name) × Ix.Map Ix.Name Ix.Name => ∀ rep all x,
      s.1.get? rep = some all → all.contains x = true →
        ∃ key val, bd.get? key = some val ∧ (val.2 == rep) = true ∧ (val.1 == x) = true) _ _ _
    (fun rep all x h _ => by rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h; cases h)
    (fun s e he hs rep all x h hx => ?_) rep all x h hx
  have hbe : bd.get? e.1 = some e.2 := by
    rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.mem_toList_iff_getElem?_eq_some]
    exact he
  dsimp only at h
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_alter] at h
  split at h
  · rename_i same
    split at h
    · rename_i s hs'
      cases h
      rw [Std.HashSet.contains_insert] at hx
      rcases Bool.or_eq_true_iff.mp hx with e' | hx
      · exact ⟨e.1, e.2, hbe, same, e'⟩
      · rw [Std.HashMap.getElem?_congr same, ← Std.HashMap.get?_eq_getElem?] at hs'
        exact hs _ _ x hs' hx
    · cases h
      rw [show ({e.2.1} : Ix.Set Ix.Name) = (∅ : Ix.Set Ix.Name).insert e.2.1 from rfl,
        Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false] at hx
      exact ⟨e.1, e.2, hbe, same, hx⟩
  · rw [← Std.HashMap.get?_eq_getElem?] at h
    exact hs rep all x h hx

/-! ## Blocks are strongly connected -/

theorem Path.congr_left {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {a b c : Ix.Name} (e : (a == b) = true)
    (p : Path refs a c) : Path refs b c := by
  cases p with
  | refl h => exact Path.refl (BEq.trans (BEq.symm e) h)
  | step h₁ h₂ h₃ p =>
    refine Path.step ?_ h₂ h₃ p
    rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.getElem?_congr e, ← Std.HashMap.get?_eq_getElem?]
    exact h₁

theorem Path.congr_right {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {a b c : Ix.Name} (p : Path refs a b)
    (e : (b == c) = true) : Path refs a c := by
  induction p with
  | refl h => exact Path.refl (BEq.trans h e)
  | step h₁ h₂ h₃ _ ih => exact Path.step h₁ h₂ h₃ (ih e)

/-- The condensation's node names are pairwise distinct (as keys of the graph). -/
theorem namesOf_inj {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {i j : Nat} (hi : i < (namesOf refs).size)
    (hj : j < (namesOf refs).size) (e : ((namesOf refs)[i] == (namesOf refs)[j]) = true) : i = j := by
  have hd := Std.HashMap.distinct_keys_toList (m := refs)
  rw [← (nodesOf_spec refs).1, List.pairwise_iff_getElem] at hd
  have hi' : i < (nodesOf refs).1.toList.length := by simpa [namesOf] using hi
  have hj' : j < (nodesOf refs).1.toList.length := by simpa [namesOf] using hj
  simp only [namesOf, Array.getElem_map] at e
  rcases Nat.lt_trichotomy i j with h | h | h
  · have := hd i j hi' hj' h
    simp only [Array.getElem_toList] at this
    rw [this] at e; cases e
  · exact h
  · have := hd j i hj' hi' h
    simp only [Array.getElem_toList] at this
    rw [BEq.comm, this] at e; cases e

/-- **A block of the condensation is strongly connected**: each member
reaches each other along the graph's references. -/
theorem condense_scc {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {rep x y : Ix.Name} {all : Ix.Set Ix.Name}
    (hb : (CondenseM.run refs).blocks.get? rep = some all) (hx : all.contains x = true)
    (hy : all.contains y = true) : Path refs x y := by
  obtain ⟨hr, hv, e⟩ := blocks_eq refs
  rw [e] at hb
  have hc := compsOf_eq refs
  obtain ⟨_, _, hbx, hrx, hnx⟩ := blocksOfDisc_mem hb hx
  obtain ⟨vx, hvx, rfl⟩ := discOf_get hbx
  obtain ⟨_, _, hby, hry, hny⟩ := blocksOfDisc_mem hb hy
  obtain ⟨vy, hvy, rfl⟩ := discOf_get hby
  dsimp only at hrx hnx hry hny
  -- each node's component and root
  have comp_of : ∀ v (hv : v < (namesOf refs).size), ∃ (k : Nat) (cm : Array Nat) (r : Nat),
      (compsOf refs).comps[k]? = some cm ∧
      (compsOf refs).roots[k]? = some r ∧ v ∈ cm ∧ ∃ hrn : r < (namesOf refs).size,
        (rootNames (namesOf refs) (compsOf refs) hr)[v] = (namesOf refs)[r] := by
    intro v hv
    obtain ⟨cm, hcm, hvc⟩ := Ix.CompileCert.Canon.condensation_cover hc v (by rw [← namesOf_size]; exact hv)
    obtain ⟨k, hk, ek⟩ := Array.mem_iff_getElem.mp hcm
    have hkr : k < (compsOf refs).roots.size := by
      rw [(CondenseRoots.condensation_roots_mem hc).1]; exact hk
    have hrn : (compsOf refs).roots[k] < (namesOf refs).size := by
      rw [namesOf_size]
      exact Ix.CompileCert.Canon.condensation_roots_lt hc (Array.getElem_mem hkr)
    refine ⟨k, cm, _, by rw [Array.getElem?_eq_getElem hk, ek], Array.getElem?_eq_getElem hkr, hvc, hrn, ?_⟩
    exact rootNames_get (Ix.CompileCert.Canon.condensation_unique hc)
      (by rw [Array.getElem?_eq_getElem hk, ek]) (Array.getElem?_eq_getElem hkr) hvc hv hrn
  obtain ⟨kx, cx, rx, hkx, hrkx, hvcx, hrnx, ex⟩ := comp_of vx hvx
  obtain ⟨ky, cy, ry, hky, hrky, hvcy, hrny, ey⟩ := comp_of vy hvy
  rw [ex] at hrx
  rw [ey] at hry
  have hsame : rx = ry := namesOf_inj hrnx hrny (BEq.trans hrx (BEq.symm hry))
  subst hsame
  have hmx := (CondenseRoots.condensation_roots_mem hc).2 kx rx cx hrkx hkx
  have hmy := (CondenseRoots.condensation_roots_mem hc).2 ky rx cy hrky hky
  have hk := Ix.CompileCert.Canon.condensation_unique hc kx ky cx cy rx hkx hky hmx hmy
  subst hk
  rw [hkx] at hky
  cases hky
  obtain ⟨-, -, r, -⟩ := (Ix.CompileCert.Canon.condensation_scc hc vx vy).mp
    ⟨cx, Array.mem_of_getElem? hkx, hvcx, hvcy⟩
  have hu : vx < (nodesOf refs).1.size := by simpa [namesOf] using hvx
  obtain ⟨_, p⟩ := reach_path r hu
  simp only [namesOf, Array.getElem_map] at hnx hny
  exact (p.congr_left hnx).congr_right hny

/-- A block of the discovery map's blocks is not empty. -/
theorem blocksOfDisc_nonempty {bd : Std.HashMap UInt64 (Ix.Name × Ix.Name)} {rep : Ix.Name}
    {all : Ix.Set Ix.Name} (h : (blocksOfDisc bd).get? rep = some all) : all.isEmpty = false := by
  unfold blocksOfDisc at h
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, List.forIn_pure_yield_eq_foldl] at h
  change (List.foldl (fun (b : Ix.Map Ix.Name (Ix.Set Ix.Name) × Ix.Map Ix.Name Ix.Name) a =>
      (Std.HashMap.alter b.fst a.2.snd fun x => match x with
        | some s => some (Std.HashSet.insert s a.2.fst)
        | none => some {a.2.fst},
       Std.HashMap.insert b.snd a.2.fst a.2.snd)) (∅, ∅) bd.toList).fst.get? rep = some all at h
  refine foldl_inv (fun s : Ix.Map Ix.Name (Ix.Set Ix.Name) × Ix.Map Ix.Name Ix.Name => ∀ rep all,
      s.1.get? rep = some all → all.isEmpty = false) _ _ _
    (fun rep all h => by rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h; cases h)
    (fun s e _ hs rep all h => ?_) rep all h
  dsimp only at h
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_alter] at h
  split at h
  · rw [Std.HashSet.isEmpty_eq_false_iff_exists_contains_eq_true]
    split at h
    · cases h
      exact ⟨_, Std.HashSet.contains_insert_self⟩
    · cases h
      exact ⟨e.2.1, by
        rw [show ({e.2.1} : Ix.Set Ix.Name) = (∅ : Ix.Set Ix.Name).insert e.2.1 from rfl]
        exact Std.HashSet.contains_insert_self⟩
  · rw [← Std.HashMap.get?_eq_getElem?] at h
    exact hs rep all h

/-- **A block of the condensation is not empty.** -/
theorem condense_nonempty {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {rep : Ix.Name} {all : Ix.Set Ix.Name}
    (hb : (CondenseM.run refs).blocks.get? rep = some all) : all.isEmpty = false := by
  obtain ⟨hr, hv, e⟩ := blocks_eq refs
  rw [e] at hb
  exact blocksOfDisc_nonempty hb

end Ix.Cert.Condense
