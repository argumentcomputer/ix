import Ix.CompileCert.Canon.SccNames
import Ix.CompileCert.Canon.SeedFree
import Ix.Compile.Canon.Block

/-!
# M7 L1, the components of a block

`Ix.Compile.Canon.blockComponents env all` lists the block's members and constructors as nodes
(`nodesOf`: each member followed by its constructors), takes the strongly connected components
of the reference graph on them (`sccsOf`, proved in `SccNames.lean`), keeps each component's
members in `all` order (`compMembers`), drops components without members, and orders the rest
by the position of their first member.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name ConstantInfo)

/-! ## The node list and the references -/

/-- One step of the node list: the member, then its constructors. -/
def nodeStep (env : Env) (nodes : Array Name) (n : Name) : Array Name :=
  match env.const? n with
  | some (.inductInfo v) => nodes.push n ++ v.ctors
  | _ => nodes.push n

/-- The nodes of the block `all`: each member followed by its constructors. -/
def nodesOf (env : Env) (all : Array Name) : Array Name := all.foldl (nodeStep env) #[]

/-- The out-edges of a node. -/
def refsOf (env : Env) (n : Name) : Std.HashSet Name :=
  match env.const? n with
  | some c => refsConst c
  | none => ∅

/-- The set of the members, as the code builds it. -/
def allSetOf (all : Array Name) : Std.HashSet Name := all.foldl (fun x1 x2 => x1.insert x2) ∅

/-- The members of `all` in the node set `c`, in `all` order, as the code computes them. -/
def compMembersS (all : Array Name) (s : Std.HashSet Name) (c : Array Name) : Option (Array Name) :=
  if (all.filter fun n => c.contains n && s.contains n).isEmpty = true then none
  else some (all.filter fun n => c.contains n && s.contains n)

/-- The members of `all` in the node set `c`, in `all` order. -/
def compMembers (all : Array Name) (c : Array Name) : Option (Array Name) :=
  if (all.filter fun n => c.contains n).isEmpty = true then none
  else some (all.filter fun n => c.contains n)

/-- The code's order of the components: the position of the first member in `all`. -/
def posOf (all : Array Name) (c : Array Name) : Nat := ((c[0]?).bind all.idxOf?).getD 0

theorem forIn_yield {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} {xs : Array α}
    {f : α → β → m (ForInStep β)} (g : β → α → β) (h : ∀ a b, f a b = pure (.yield (g b a)))
    (init : β) : forIn xs init f = pure (xs.foldl g init) := by
  have : f = fun a b => pure (.yield (g b a)) := funext fun a => funext fun b => h a b
  subst this; exact Array.forIn_pure_yield_eq_foldl _ _

/-- `blockComponents`, unfolded. -/
theorem blockComponents_eq (env : Env) (all : Array Name) :
    blockComponents env all =
      match sccsOf (nodesOf env all) (refsOf env) with
      | some cs => pure ((cs.filterMap (compMembersS all (allSetOf all))).qsort
          fun a b => decide (posOf all a < posOf all b))
      | none => throw "component computation ran out of fuel" := by
  unfold blockComponents
  dsimp only
  rw [forIn_yield (nodeStep env) (fun n s => by
    unfold nodeStep
    cases h : env.const? n with
    | none => rfl
    | some c => cases c <;> rfl)]
  simp only [pure_bind]
  split
  · rename_i comps h
    rw [show sccsOf (nodesOf env all) (refsOf env) = some comps from h]
    rfl
  · rename_i h2
    cases hs : sccsOf (nodesOf env all) (refsOf env) with
    | none => rfl
    | some cs => exact (h2 cs hs).elim

/-! ## Reachability over names -/

/-- Reflexive-transitive closure of a relation on names. -/
inductive NReach (E : Name → Name → Prop) : Name → Name → Prop
  | refl (a : Name) : NReach E a a
  | tail {a b c : Name} : NReach E a b → E b c → NReach E a c

theorem NReach.trans {E : Name → Name → Prop} {a b c : Name} (h₁ : NReach E a b) (h₂ : NReach E b c) :
    NReach E a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ e ih => exact .tail ih e

theorem NReach.single {E : Name → Name → Prop} {a b : Name} (e : E a b) : NReach E a b :=
  .tail (.refl a) e

/-- The node graph: an edge from the node `a` to the node `b` when `refs a` contains `b`. -/
def NodeEdge (names : Array Name) (refs : Name → Std.HashSet Name) (a b : Name) : Prop :=
  a ∈ names ∧ b ∈ names ∧ (refs a).contains b = true

theorem relReach_nreach {names : Array Name} {refs : Name → Std.HashSet Name} {i j : Nat}
    (r : RelReach (NEdge names refs) i j) :
    ∀ a, names[i]? = some a → ∃ b, names[j]? = some b ∧ NReach (NodeEdge names refs) a b := by
  induction r with
  | refl => intro a ha; exact ⟨a, ha, .refl a⟩
  | tail _ e ih =>
    intro a ha
    obtain ⟨b, hb, r⟩ := ih a ha
    obtain ⟨a', b', ha', hb', hc⟩ := e
    rw [hb] at ha'; cases ha'
    exact ⟨b', hb', .tail r ⟨Array.mem_of_getElem? hb, Array.mem_of_getElem? hb', hc⟩⟩

theorem nreach_relReach {names : Array Name} {refs : Name → Std.HashSet Name} {a b : Name}
    (r : NReach (NodeEdge names refs) a b) :
    ∀ i, names[i]? = some a → ∃ j, names[j]? = some b ∧ RelReach (NEdge names refs) i j := by
  induction r with
  | refl => intro i hi; exact ⟨i, hi, .refl i⟩
  | tail _ e ih =>
    intro i hi
    obtain ⟨j, hj, r⟩ := ih i hi
    obtain ⟨-, hc, hcon⟩ := e
    obtain ⟨k, hk⟩ := Array.getElem?_of_mem hc
    exact ⟨k, hk, .tail r ⟨_, _, hj, hk, hcon⟩⟩

theorem getElem?_of_lt {names : Array Name} {i : Nat} (hi : i < names.size) :
    names[i]? = some names[i] := Array.getElem?_eq_getElem hi

/-- **`sccsOf` over names**: two nodes are in one component iff each reaches the other in the
node graph. -/
theorem sccsOf_nscc {names : Array Name} {refs : Name → Std.HashSet Name} {cs : Array (Array Name)}
    (hnd : NodupB names) (h : sccsOf names refs = some cs) {a b : Name} (ha : a ∈ names)
    (hb : b ∈ names) :
    (∃ c ∈ cs, a ∈ c ∧ b ∈ c) ↔
      NReach (NodeEdge names refs) a b ∧ NReach (NodeEdge names refs) b a := by
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hb
  rw [sccsOf_scc hnd h i j hi hj]
  constructor
  · rintro ⟨r1, r2⟩
    obtain ⟨b', hb', n1⟩ := relReach_nreach r1 _ (getElem?_of_lt hi)
    obtain ⟨a', ha', n2⟩ := relReach_nreach r2 _ (getElem?_of_lt hj)
    rw [getElem?_of_lt hj] at hb'; cases hb'
    rw [getElem?_of_lt hi] at ha'; cases ha'
    exact ⟨n1, n2⟩
  · rintro ⟨n1, n2⟩
    obtain ⟨j', hj', r1⟩ := nreach_relReach n1 i (getElem?_of_lt hi)
    obtain ⟨i', hi', r2⟩ := nreach_relReach n2 j (getElem?_of_lt hj)
    have e1 : j' = j := names_eq_of hnd hj' (getElem?_of_lt hj)
    have e2 : i' = i := names_eq_of hnd hi' (getElem?_of_lt hi)
    subst e1; subst e2
    exact ⟨r1, r2⟩

/-- Distinct nodes are distinct under `==`. -/
theorem eq_of_beq_nodes {names : Array Name} (hnd : NodupB names) {a b : Name} (ha : a ∈ names)
    (hb : b ∈ names) (h : (a == b) = true) : a = b := by
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hb
  have := hnd i j hi hj h
  subst this; rfl

theorem contains_iff_mem {names : Array Name} (hnd : NodupB names) {c : Array Name}
    (hc : ∀ x ∈ c, x ∈ names) {a : Name} (ha : a ∈ names) : c.contains a = true ↔ a ∈ c := by
  unfold Array.contains
  rw [Array.any_eq_true']
  constructor
  · rintro ⟨x, hx, e⟩
    rw [eq_of_beq_nodes hnd ha (hc x hx) e]; exact hx
  · intro h; exact ⟨a, h, name_beq_refl a⟩

/-! ## The node list -/

theorem mem_nodeStep {env : Env} {acc : Array Name} {n x : Name} :
    x ∈ nodeStep env acc n ↔
      x ∈ acc ∨ x = n ∨ ∃ v, env.const? n = some (.inductInfo v) ∧ x ∈ v.ctors := by
  unfold nodeStep
  cases h : env.const? n with
  | none =>
    simp only [Array.mem_push, reduceCtorEq, false_and, exists_false, or_false]
  | some c =>
    cases c <;>
      simp only [Array.mem_push, Array.mem_append, Option.some.injEq, reduceCtorEq, false_and,
        exists_false, or_false, ConstantInfo.inductInfo.injEq, exists_eq_left', or_assoc]

theorem mem_foldl_nodeStep {env : Env} {x : Name} : ∀ (l : List Name) (acc : Array Name),
    x ∈ l.foldl (nodeStep env) acc ↔
      x ∈ acc ∨ ∃ n ∈ l, x = n ∨ ∃ v, env.const? n = some (.inductInfo v) ∧ x ∈ v.ctors
  | [], acc => by simp only [List.foldl_nil, List.not_mem_nil, false_and, exists_false, or_false]
  | n :: l, acc => by
    rw [List.foldl_cons, mem_foldl_nodeStep l, mem_nodeStep]
    constructor
    · rintro ((h | h | h) | ⟨m, hm, h⟩)
      · exact .inl h
      · exact .inr ⟨n, List.mem_cons_self .., .inl h⟩
      · exact .inr ⟨n, List.mem_cons_self .., .inr h⟩
      · exact .inr ⟨m, List.mem_cons_of_mem _ hm, h⟩
    · rintro (h | ⟨m, hm, h⟩)
      · exact .inl (.inl h)
      · rcases List.mem_cons.1 hm with rfl | hm
        · rcases h with h | h
          · exact .inl (.inr (.inl h))
          · exact .inl (.inr (.inr h))
        · exact .inr ⟨m, hm, h⟩

/-- The nodes are the members and their constructors. -/
theorem mem_nodesOf {env : Env} {all : Array Name} {x : Name} :
    x ∈ nodesOf env all ↔ ∃ n ∈ all, x = n ∨ ∃ v, env.const? n = some (.inductInfo v) ∧ x ∈ v.ctors := by
  unfold nodesOf
  rw [← Array.foldl_toList, mem_foldl_nodeStep]
  simp only [Array.not_mem_empty, false_or, Array.mem_toList_iff]

theorem mem_nodesOf_of_mem {env : Env} {all : Array Name} {n : Name} (h : n ∈ all) :
    n ∈ nodesOf env all :=
  mem_nodesOf.2 ⟨n, h, .inl rfl⟩

/-! ## The components -/

theorem foldl_insert_contains : ∀ (l : List Name) (s : Std.HashSet Name) (n : Name),
    (s.contains n = true ∨ n ∈ l) → (l.foldl (fun x1 x2 => x1.insert x2) s).contains n = true
  | [], s, n, h => by
    rcases h with h | h
    · exact h
    · cases h
  | a :: l, s, n, h => by
    rw [List.foldl_cons]
    apply foldl_insert_contains l
    rcases h with h | h
    · left; rw [Std.HashSet.contains_insert, h, Bool.or_true]
    · rcases List.mem_cons.1 h with rfl | h
      · left; rw [Std.HashSet.contains_insert, name_beq_refl, Bool.true_or]
      · right; exact h

theorem allSetOf_contains {all : Array Name} {n : Name} (h : n ∈ all) : (allSetOf all).contains n = true := by
  unfold allSetOf
  rw [← Array.foldl_toList]
  exact foldl_insert_contains _ _ _ (.inr (Array.mem_toList_iff.2 h))

theorem compMembersS_eq (all c : Array Name) : compMembersS all (allSetOf all) c = compMembers all c := by
  have : all.filter (fun n => c.contains n && (allSetOf all).contains n) = all.filter (fun n => c.contains n) := by
    apply Array.toList_inj.1
    rw [Array.toList_filter, Array.toList_filter]
    exact List.filter_congr fun x hx => by
      rw [allSetOf_contains (Array.mem_toList_iff.1 hx), Bool.and_true]
  unfold compMembersS compMembers
  simp only [this]

theorem mem_compMembers {all c ms : Array Name} (h : compMembers all c = some ms) {m : Name} :
    m ∈ ms ↔ m ∈ all ∧ c.contains m = true := by
  unfold compMembers at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h; subst h
    exact Array.mem_filter

section
variable {env : Env} {all : Array Name} {comps : Array (Array Name)}
  (hnd : NodupB (nodesOf env all)) (h : blockComponents env all = .ok comps)
include h

omit hnd in
theorem blockComponents_sccs : ∃ cs, sccsOf (nodesOf env all) (refsOf env) = some cs ∧
    ∀ c, c ∈ comps ↔ ∃ c0 ∈ cs, compMembers all c0 = some c := by
  rw [blockComponents_eq] at h
  cases hs : sccsOf (nodesOf env all) (refsOf env) with
  | none => rw [hs] at h; cases h
  | some cs =>
    rw [hs] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    refine ⟨cs, rfl, fun c => ?_⟩
    rw [mem_qsort, Array.mem_filterMap]
    simp only [compMembersS_eq]

include hnd

omit h in
/-- A member is in the component of a node set exactly when it is in the node set. -/
theorem mem_comp_iff {cs : Array (Array Name)} (hs : sccsOf (nodesOf env all) (refsOf env) = some cs)
    {c0 c : Array Name} (hc0 : c0 ∈ cs) (hc : compMembers all c0 = some c) {m : Name} :
    m ∈ c ↔ m ∈ all ∧ m ∈ c0 := by
  rw [mem_compMembers hc]
  constructor
  · rintro ⟨hm, hcon⟩
    exact ⟨hm, (contains_iff_mem hnd (sccsOf_range hs c0 hc0) (mem_nodesOf_of_mem hm)).1 hcon⟩
  · rintro ⟨hm, hm0⟩
    exact ⟨hm, (contains_iff_mem hnd (sccsOf_range hs c0 hc0) (mem_nodesOf_of_mem hm)).2 hm0⟩

omit hnd in
/-- **Each component is a nonempty sublist of the members, in `all` order.** -/
theorem blockComponents_sub : ∀ c ∈ comps, c ≠ #[] ∧ c.toList.Sublist all.toList := by
  obtain ⟨cs, -, hc⟩ := blockComponents_sccs h
  intro c hcm
  obtain ⟨c0, -, e⟩ := (hc c).1 hcm
  unfold compMembers at e
  split at e
  · cases e
  · rename_i hne
    simp only [Option.some.injEq] at e; subst e
    refine ⟨fun e => hne (by rw [e]; rfl), ?_⟩
    rw [Array.toList_filter]
    exact List.filter_sublist

/-- **Every member is in a component.** -/
theorem blockComponents_cover : ∀ m ∈ all, ∃ c ∈ comps, m ∈ c := by
  obtain ⟨cs, hs, hc⟩ := blockComponents_sccs h
  intro m hm
  obtain ⟨c0, hc0, hm0⟩ := sccsOf_cover hs m (mem_nodesOf_of_mem hm)
  have hcon : c0.contains m = true :=
    (contains_iff_mem hnd (sccsOf_range hs c0 hc0) (mem_nodesOf_of_mem hm)).2 hm0
  have hne : (all.filter fun n => c0.contains n).isEmpty = false := by
    cases e : (all.filter fun n => c0.contains n).isEmpty
    · rfl
    · have := Array.isEmpty_iff.1 e
      have hmf : m ∈ all.filter (fun n => c0.contains n) := Array.mem_filter.2 ⟨hm, hcon⟩
      rw [this] at hmf; exact absurd hmf (Array.not_mem_empty m)
  have e : compMembers all c0 = some (all.filter fun n => c0.contains n) := by
    unfold compMembers; simp only [hne, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, (hc _).2 ⟨c0, hc0, e⟩, Array.mem_filter.2 ⟨hm, hcon⟩⟩

/-- **Every member is in one component.** -/
theorem blockComponents_unique : ∀ c ∈ comps, ∀ c' ∈ comps, ∀ m, m ∈ c → m ∈ c' → c = c' := by
  obtain ⟨cs, hs, hc⟩ := blockComponents_sccs h
  intro c hcm c' hcm' m hm hm'
  obtain ⟨c0, hc0, e⟩ := (hc c).1 hcm
  obtain ⟨c0', hc0', e'⟩ := (hc c').1 hcm'
  have h1 := (mem_comp_iff hnd hs hc0 e).1 hm
  have h2 := (mem_comp_iff hnd hs hc0' e').1 hm'
  have := sccsOf_unique hnd hs c0 hc0 c0' hc0' m h1.2 h2.2
  subst this
  rw [e] at e'; cases e'; rfl

/-- **The components are the strongly connected components** of the reference graph on the
members and their constructors, restricted to the members (Def 2.1): two members are in one
component iff each reaches the other. -/
theorem blockComponents_scc {m m' : Name} (hm : m ∈ all) (hm' : m' ∈ all) :
    (∃ c ∈ comps, m ∈ c ∧ m' ∈ c) ↔
      NReach (NodeEdge (nodesOf env all) (refsOf env)) m m' ∧
        NReach (NodeEdge (nodesOf env all) (refsOf env)) m' m := by
  obtain ⟨cs, hs, hc⟩ := blockComponents_sccs h
  rw [← sccsOf_nscc hnd hs (mem_nodesOf_of_mem hm) (mem_nodesOf_of_mem hm')]
  constructor
  · rintro ⟨c, hcm, h1, h2⟩
    obtain ⟨c0, hc0, e⟩ := (hc c).1 hcm
    exact ⟨c0, hc0, ((mem_comp_iff hnd hs hc0 e).1 h1).2, ((mem_comp_iff hnd hs hc0 e).1 h2).2⟩
  · rintro ⟨c0, hc0, h1, h2⟩
    have hcon : c0.contains m = true :=
      (contains_iff_mem hnd (sccsOf_range hs c0 hc0) (mem_nodesOf_of_mem hm)).2 h1
    have hne : (all.filter fun n => c0.contains n).isEmpty = false := by
      cases e : (all.filter fun n => c0.contains n).isEmpty
      · rfl
      · have := Array.isEmpty_iff.1 e
        have hmf : m ∈ all.filter (fun n => c0.contains n) := Array.mem_filter.2 ⟨hm, hcon⟩
        rw [this] at hmf; exact absurd hmf (Array.not_mem_empty m)
    have e : compMembers all c0 = some (all.filter fun n => c0.contains n) := by
      unfold compMembers; simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, (hc _).2 ⟨c0, hc0, e⟩, (mem_comp_iff hnd hs hc0 e).2 ⟨hm, h1⟩,
      (mem_comp_iff hnd hs hc0 e).2 ⟨hm', h2⟩⟩

end

/-! ## Distinct names, as lists -/

theorem nodupB_iff {names : Array Name} :
    NodupB names ↔ names.toList.Pairwise (fun a b => (a == b) = false) := by
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij
    cases e : (names.toList[i] == names.toList[j])
    · rfl
    · simp only [Array.getElem_toList] at e
      have := h i j (by rwa [Array.length_toList] at hi) (by rwa [Array.length_toList] at hj) e
      omega
  · intro h i j hi hj e
    rcases Nat.lt_trichotomy i j with hij | rfl | hij
    · have := h i j (by rwa [Array.length_toList]) (by rwa [Array.length_toList]) hij
      simp only [Array.getElem_toList] at this; rw [e] at this; cases this
    · rfl
    · have := h j i (by rwa [Array.length_toList]) (by rwa [Array.length_toList]) hij
      simp only [Array.getElem_toList] at this; rw [name_beq_symm e] at this; cases this

theorem pairwise_nbeq_perm {l l' : List Name} (p : l.Perm l')
    (h : l.Pairwise (fun a b => (a == b) = false)) : l'.Pairwise (fun a b => (a == b) = false) :=
  p.pairwise h fun {a b} e => by
    cases hb : (b == a)
    · rfl
    · rw [name_beq_symm hb] at e; cases e

theorem pairwise_nbeq_nodup {l : List Name} (h : l.Pairwise (fun a b => (a == b) = false)) : l.Nodup :=
  List.nodup_iff_pairwise_ne.2 (h.imp fun {a b} e hab => by
    subst hab; rw [name_beq_refl] at e; cases e)

theorem sublist_flatMap {α β : Type} (f : α → List β) :
    ∀ {l₁ l₂ : List α}, l₁.Sublist l₂ → (l₁.flatMap f).Sublist (l₂.flatMap f)
  | _, _, .slnil => List.Sublist.slnil
  | _, _, .cons a h => by
    rw [List.flatMap_cons]; exact (sublist_flatMap f h).trans (List.sublist_append_right _ _)
  | _, _, .cons_cons a h => by
    rw [List.flatMap_cons, List.flatMap_cons]; exact (sublist_flatMap f h).append_left _

/-- The node list of one member: the member, then its constructors. -/
def nodeList (env : Env) (n : Name) : List Name :=
  match env.const? n with
  | some (.inductInfo v) => n :: v.ctors.toList
  | _ => [n]

theorem nodeList_cons (env : Env) (n : Name) : ∃ r, nodeList env n = n :: r := by
  unfold nodeList
  cases env.const? n with
  | none => exact ⟨[], rfl⟩
  | some c => cases c <;> exact ⟨_, rfl⟩

theorem nodeStep_toList (env : Env) (acc : Array Name) (n : Name) :
    (nodeStep env acc n).toList = acc.toList ++ nodeList env n := by
  unfold nodeStep nodeList
  cases env.const? n with
  | none => simp only [Array.toList_push]
  | some c =>
    cases c <;> simp only [Array.toList_push, Array.toList_append, List.append_assoc,
      List.singleton_append]

theorem nodesOf_toList (env : Env) (all : Array Name) :
    (nodesOf env all).toList = all.toList.flatMap (nodeList env) := by
  unfold nodesOf
  rw [← Array.foldl_toList]
  suffices h : ∀ (l : List Name) (acc : Array Name),
      (l.foldl (nodeStep env) acc).toList = acc.toList ++ l.flatMap (nodeList env) by
    rw [h]; rfl
  intro l
  induction l with
  | nil => intro acc; simp only [List.foldl_nil, List.flatMap_nil, List.append_nil]
  | cons n l ih =>
    intro acc
    rw [List.foldl_cons, ih, nodeStep_toList, List.flatMap_cons, List.append_assoc]

theorem members_sublist_nodes (env : Env) :
    ∀ (l : List Name), l.Sublist (l.flatMap (nodeList env))
  | [] => List.Sublist.slnil
  | n :: l => by
    obtain ⟨r, hr⟩ := nodeList_cons env n
    rw [List.flatMap_cons, hr, List.cons_append]
    exact ((members_sublist_nodes env l).trans (List.sublist_append_right r _)).cons_cons n

/-- The members of a block with distinct nodes are distinct. -/
theorem members_nbeq {env : Env} {all : Array Name} (hnd : NodupB (nodesOf env all)) :
    all.toList.Pairwise (fun a b => (a == b) = false) := by
  have := nodupB_iff.1 hnd
  rw [nodesOf_toList] at this
  exact this.sublist (members_sublist_nodes env _)

/-- A sub-block's nodes are distinct. -/
theorem nodupB_sub {env : Env} {all sub : Array Name} (hnd : NodupB (nodesOf env all))
    (hs : sub.toList.Sublist all.toList) : NodupB (nodesOf env sub) := by
  have := nodupB_iff.1 hnd
  rw [nodesOf_toList] at this
  apply nodupB_iff.2
  rw [nodesOf_toList]
  exact this.sublist (sublist_flatMap _ hs)

/-! ## Components at distinct positions are disjoint -/

theorem list_mapM_option_getElem? {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → ∀ k : Nat, l'[k]? = (l[k]?).bind f
  | [], l', h, k => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h
    simp only [List.getElem?_nil, Option.bind_none]
  | a :: as, l', h, k => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => rw [ha] at h; cases h
    | some b =>
      cases hs : as.mapM f with
      | none => rw [ha, hs] at h; cases h
      | some bs =>
        rw [ha, hs] at h
        simp only [Option.bind_some, Option.some.injEq, bind, pure] at h
        subst h
        cases k with
        | zero => simp only [List.getElem?_cons_zero, Option.bind_some, ha]
        | succ k =>
          simp only [List.getElem?_cons_succ]
          exact list_mapM_option_getElem? f as bs hs k

theorem array_mapM_option_getElem? {α β : Type} (f : α → Option β) (xs : Array α) (ys : Array β)
    (h : xs.mapM f = some ys) (k : Nat) : ys[k]? = (xs[k]?).bind f := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : xs.toList.mapM f with
  | none => rw [hl] at h; cases h
  | some l' =>
    rw [hl] at h
    simp only [Functor.map, Option.map_some, Option.some.injEq] at h
    subst h
    rw [List.getElem?_toArray, list_mapM_option_getElem? f _ l' hl k, Array.getElem?_toList]

theorem sccsOf_index {names : Array Name} {refs : Name → Std.HashSet Name} {cs : Array (Array Name)}
    (h : sccsOf names refs = some cs) : ∃ C, condensation (adjOf names refs) = some C ∧
      ∀ k : Nat, cs[k]? = (C.comps[k]?).bind fun (c0 : Array Nat) => c0.mapM (names[·]?) := by
  rw [sccsOf_eq] at h
  cases ht : tarjan (adjOf names refs) with
  | none => rw [ht] at h; cases h
  | some comps =>
    rw [ht] at h
    simp only [Option.bind_some] at h
    unfold tarjan at ht
    cases hc : condensation (adjOf names refs) with
    | none => rw [hc] at ht; cases ht
    | some C =>
      rw [hc] at ht; simp only [Option.map_some, Option.some.injEq] at ht
      subst ht
      exact ⟨C, rfl, fun k => array_mapM_option_getElem? _ _ _ h k⟩

/-- No node is in the components at two positions. -/
theorem sccsOf_index_unique {names : Array Name} {refs : Name → Std.HashSet Name}
    {cs : Array (Array Name)} (hnd : NodupB names) (h : sccsOf names refs = some cs) {k k' : Nat}
    {c c' : Array Name} (hk : cs[k]? = some c) (hk' : cs[k']? = some c') {x : Name} (hx : x ∈ c)
    (hx' : x ∈ c') : k = k' := by
  obtain ⟨C, hC, hidx⟩ := sccsOf_index h
  rw [hidx] at hk hk'
  cases hc0 : C.comps[k]? with
  | none => rw [hc0] at hk; cases hk
  | some c0 =>
    cases hc0' : C.comps[k']? with
    | none => rw [hc0'] at hk'; cases hk'
    | some c0' =>
      rw [hc0, Option.bind_some] at hk
      rw [hc0', Option.bind_some] at hk'
      obtain ⟨j, hj, hjx⟩ := (mem_comp_names hk x).1 hx
      obtain ⟨j', hj', hjx'⟩ := (mem_comp_names hk' x).1 hx'
      have := names_eq_of hnd hjx hjx'
      subst this
      exact condensation_unique hC k k' c0 c0' j hc0 hc0' hj hj'

theorem sccsOf_pairwise {names : Array Name} {refs : Name → Std.HashSet Name}
    {cs : Array (Array Name)} (hnd : NodupB names) (h : sccsOf names refs = some cs) :
    cs.toList.Pairwise (fun c c' => ∀ x, x ∈ c → x ∈ c' → False) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij x hx hx'
  have e := sccsOf_index_unique hnd h (k := i) (k' := j)
    (by rw [← Array.getElem?_toList]; exact List.getElem?_eq_getElem hi)
    (by rw [← Array.getElem?_toList]; exact List.getElem?_eq_getElem hj) hx hx'
  omega

theorem filterMap_length_le_one {α β : Type} (P : α → Prop) (g : α → Option β) :
    ∀ (l : List α), l.Pairwise (fun a b => ¬ (P a ∧ P b)) → (∀ a ∈ l, g a ≠ none → P a) →
      (l.filterMap g).length ≤ 1
  | [], _, _ => by simp only [List.filterMap_nil, List.length_nil]; omega
  | a :: t, hp, hg => by
    rw [List.pairwise_cons] at hp
    cases hga : g a with
    | none =>
      rw [List.filterMap_cons_none hga]
      exact filterMap_length_le_one P g t hp.2 (fun b hb => hg b (List.mem_cons_of_mem _ hb))
    | some b =>
      rw [List.filterMap_cons_some hga]
      have hPa : P a := hg a (List.mem_cons_self ..) (by rw [hga]; exact Option.some_ne_none _)
      have : t.filterMap g = [] := List.filterMap_eq_nil_iff.2 fun c hc => by
        cases hgc : g c with
        | none => rfl
        | some _ =>
          exact absurd ⟨hPa, hg c (List.mem_cons_of_mem _ hc) (by rw [hgc]; exact Option.some_ne_none _)⟩
            (hp.1 c hc)
      rw [this]; simp only [List.length_cons, List.length_nil]; omega

theorem blockComponents_list {env : Env} {all : Array Name} {comps : Array (Array Name)}
    (h : blockComponents env all = .ok comps) : ∃ cs, sccsOf (nodesOf env all) (refsOf env) = some cs ∧
      comps.toList.Perm (cs.toList.filterMap (compMembers all)) := by
  rw [blockComponents_eq] at h
  cases hs : sccsOf (nodesOf env all) (refsOf env) with
  | none => rw [hs] at h; cases h
  | some cs =>
    rw [hs] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    refine ⟨cs, rfl, ?_⟩
    have e : compMembersS all (allSetOf all) = compMembers all := funext (compMembersS_eq all)
    exact (qsort_perm _ _).toList.trans (by rw [Array.toList_filterMap, e])

/-! ## Member order and separate declaration -/

/-- The name a constant carries. -/
def ciName : ConstantInfo → Name
  | .axiomInfo v => v.cnst.name
  | .defnInfo v => v.cnst.name
  | .thmInfo v => v.cnst.name
  | .opaqueInfo v => v.cnst.name
  | .quotInfo v => v.cnst.name
  | .inductInfo v => v.cnst.name
  | .ctorInfo v => v.cnst.name
  | .recInfo v => v.cnst.name

/-- What Pass 1 needs of the environment: each member answers with a constant of its own name,
and an inductive member's constructors are constructors of it under their own names. -/
structure EnvWF (env : Env) (all : Array Name) : Prop where
  name : ∀ n ∈ all, ∀ ci, env.const? n = some ci → ciName ci = n
  ctor : ∀ n ∈ all, ∀ v, env.const? n = some (.inductInfo v) → ∀ k ∈ v.ctors,
    ∃ cv, env.const? k = some (.ctorInfo cv) ∧ cv.cnst.name = k ∧ cv.induct = n

theorem EnvWF.sub {env : Env} {all sub : Array Name} (h : EnvWF env all) (hs : ∀ n ∈ sub, n ∈ all) :
    EnvWF env sub := ⟨fun n hn => h.name n (hs n hn), fun n hn => h.ctor n (hs n hn)⟩

theorem NReach.mono {E E' : Name → Name → Prop} (h : ∀ a b, E a b → E' a b) {a b : Name}
    (r : NReach E a b) : NReach E' a b := by
  induction r with
  | refl => exact .refl _
  | tail _ e ih => exact .tail ih (h _ _ e)

/-- **Member order** (Def 4.3, member reorder): the components of a permuted block are those of
the block, each a permutation of the other's. -/
theorem blockComponents_perm {env : Env} {all all' : Array Name} {comps comps' : Array (Array Name)}
    (hp : all.toList.Perm all'.toList) (hnd : NodupB (nodesOf env all))
    (h : blockComponents env all = .ok comps) (h' : blockComponents env all' = .ok comps') :
    ∀ c ∈ comps, ∃ c' ∈ comps', c.toList.Perm c'.toList := by
  have pn : (nodesOf env all).toList.Perm (nodesOf env all').toList := by
    rw [nodesOf_toList, nodesOf_toList]; exact List.Perm.flatMap_right _ hp
  have hnd' : NodupB (nodesOf env all') := nodupB_iff.2 (pairwise_nbeq_perm pn (nodupB_iff.1 hnd))
  have memN : ∀ x, x ∈ nodesOf env all ↔ x ∈ nodesOf env all' := fun x => by
    rw [Array.mem_def, Array.mem_def]; exact pn.mem_iff
  have memA : ∀ x, x ∈ all ↔ x ∈ all' := fun x => by
    rw [Array.mem_def, Array.mem_def]; exact hp.mem_iff
  have edge : ∀ a b, NodeEdge (nodesOf env all) (refsOf env) a b ↔ NodeEdge (nodesOf env all') (refsOf env) a b :=
    fun a b => by unfold NodeEdge; rw [memN a, memN b]
  have reach : ∀ a b, NReach (NodeEdge (nodesOf env all) (refsOf env)) a b ↔
      NReach (NodeEdge (nodesOf env all') (refsOf env)) a b :=
    fun a b => ⟨NReach.mono fun x y => (edge x y).1, NReach.mono fun x y => (edge x y).2⟩
  have hmem : ∀ c ∈ comps, ∀ x ∈ c, x ∈ all := fun c hc x hx =>
    Array.mem_toList_iff.1 ((blockComponents_sub h c hc).2.subset (Array.mem_toList_iff.2 hx))
  have hmem' : ∀ c ∈ comps', ∀ x ∈ c, x ∈ all' := fun c hc x hx =>
    Array.mem_toList_iff.1 ((blockComponents_sub h' c hc).2.subset (Array.mem_toList_iff.2 hx))
  intro c hc
  obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil c.toList (by
    intro e; exact (blockComponents_sub h c hc).1 (Array.toList_inj.1 (by rw [e])))
  have hm' : m ∈ c := Array.mem_toList_iff.1 hm
  have hmA : m ∈ all := hmem c hc m hm'
  obtain ⟨c', hc', hmc'⟩ := blockComponents_cover hnd' h' m ((memA m).1 hmA)
  refine ⟨c', hc', ?_⟩
  have nd : ∀ (d : Array Name) (sub : d.toList.Sublist all.toList), d.toList.Nodup := fun d sub =>
    pairwise_nbeq_nodup ((members_nbeq hnd).sublist sub)
  have nd' : ∀ (d : Array Name) (sub : d.toList.Sublist all'.toList), d.toList.Nodup := fun d sub =>
    pairwise_nbeq_nodup ((members_nbeq hnd').sublist sub)
  refine (List.perm_ext_iff_of_nodup (nd c (blockComponents_sub h c hc).2)
    (nd' c' (blockComponents_sub h' c' hc').2)).2 fun x => ?_
  rw [Array.mem_toList_iff, Array.mem_toList_iff]
  constructor
  · intro hx
    have hxA := hmem c hc x hx
    obtain ⟨r1, r2⟩ := (blockComponents_scc hnd h hmA hxA).1 ⟨c, hc, hm', hx⟩
    obtain ⟨c'', hc'', h1, h2⟩ := (blockComponents_scc hnd' h' ((memA m).1 hmA) ((memA x).1 hxA)).2
      ⟨(reach m x).1 r1, (reach x m).1 r2⟩
    rw [blockComponents_unique hnd' h' c'' hc'' c' hc' m h1 hmc'] at h2
    exact h2
  · intro hx
    have hxA' := hmem' c' hc' x hx
    obtain ⟨r1, r2⟩ := (blockComponents_scc hnd' h' ((memA m).1 hmA) hxA').1 ⟨c', hc', hmc', hx⟩
    obtain ⟨c'', hc'', h1, h2⟩ := (blockComponents_scc hnd h hmA ((memA x).2 hxA')).2
      ⟨(reach m x).2 r1, (reach x m).2 r2⟩
    rw [blockComponents_unique hnd h c'' hc'' c hc m h1 hm'] at h2
    exact h2

/-! ## Separate declaration of a component -/

theorem refsOf_ind {env : Env} {n : Name} {v : Ix.InductiveVal} (h : env.const? n = some (.inductInfo v))
    {k : Name} (hk : k ∈ v.ctors) : (refsOf env n).contains k = true := by
  unfold refsOf
  rw [h]
  show (Array.foldl (fun x1 x2 => x1.insert x2) (refsExpr v.cnst.type) v.ctors).contains k = true
  rw [← Array.foldl_toList]
  exact foldl_insert_contains _ _ _ (.inr (Array.mem_toList_iff.2 hk))

theorem refsOf_ctor {env : Env} {k : Name} {cv : Ix.ConstructorVal}
    (h : env.const? k = some (.ctorInfo cv)) : (refsOf env k).contains cv.induct = true := by
  unfold refsOf
  rw [h]
  show ((refsExpr cv.cnst.type).insert cv.induct).contains cv.induct = true
  rw [Std.HashSet.contains_insert, name_beq_refl, Bool.true_or]

/-- An inductive member and each of its constructors reach each other. -/
theorem ctor_edges {env : Env} {all : Array Name} (hwf : EnvWF env all) {n : Name} (hn : n ∈ all)
    {v : Ix.InductiveVal} (hv : env.const? n = some (.inductInfo v)) {k : Name} (hk : k ∈ v.ctors) :
    NodeEdge (nodesOf env all) (refsOf env) n k ∧ NodeEdge (nodesOf env all) (refsOf env) k n := by
  have hnN := mem_nodesOf_of_mem (env := env) hn
  have hkN : k ∈ nodesOf env all := mem_nodesOf.2 ⟨n, hn, .inr ⟨v, hv, hk⟩⟩
  obtain ⟨cv, hcv, -, hind⟩ := hwf.ctor n hn v hv k hk
  refine ⟨⟨hnN, hkN, refsOf_ind hv hk⟩, ⟨hkN, hnN, ?_⟩⟩
  rw [← hind]; exact refsOf_ctor hcv

section
variable {env : Env} {all : Array Name} {comps : Array (Array Name)}
  (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all) (h : blockComponents env all = .ok comps)
include hnd hwf h

/-- A node reaching and reached from a member of a component is a node of the component. -/
theorem mem_nodes_comp {c : Array Name} (hc : c ∈ comps) {m : Name} (hm : m ∈ c) {x : Name}
    (hx : x ∈ nodesOf env all) (r1 : NReach (NodeEdge (nodesOf env all) (refsOf env)) m x)
    (r2 : NReach (NodeEdge (nodesOf env all) (refsOf env)) x m) : x ∈ nodesOf env c := by
  have hmA : m ∈ all :=
    Array.mem_toList_iff.1 ((blockComponents_sub h c hc).2.subset (Array.mem_toList_iff.2 hm))
  obtain ⟨n, hn, hxn⟩ := mem_nodesOf.1 hx
  have hreach : NReach (NodeEdge (nodesOf env all) (refsOf env)) m n ∧
      NReach (NodeEdge (nodesOf env all) (refsOf env)) n m := by
    rcases hxn with rfl | ⟨v, hv, hk⟩
    · exact ⟨r1, r2⟩
    · obtain ⟨e1, e2⟩ := ctor_edges hwf hn hv hk
      exact ⟨r1.tail e2, (NReach.single e1).trans r2⟩
  obtain ⟨c', hc', hmc', hnc'⟩ := (blockComponents_scc hnd h hmA hn).2 hreach
  have := blockComponents_unique hnd h c' hc' c hc m hmc' hm
  subst this
  rcases hxn with rfl | ⟨v, hv, hk⟩
  · exact mem_nodesOf_of_mem hnc'
  · exact mem_nodesOf.2 ⟨n, hnc', .inr ⟨v, hv, hk⟩⟩

/-- Inside a component, paths stay among the component's nodes. -/
theorem reach_restrict {c : Array Name} (hc : c ∈ comps) {m : Name} (hm : m ∈ c) :
    ∀ y, NReach (NodeEdge (nodesOf env all) (refsOf env)) m y →
      NReach (NodeEdge (nodesOf env all) (refsOf env)) y m →
      NReach (NodeEdge (nodesOf env c) (refsOf env)) m y := by
  intro y r
  induction r with
  | refl => intro _; exact .refl _
  | tail r e ih =>
    intro back
    have back' := (NReach.single e).trans back
    exact .tail (ih back') ⟨mem_nodes_comp hnd hwf h hc hm e.1 r back',
      mem_nodes_comp hnd hwf h hc hm e.2.1 (r.tail e) back, e.2.2⟩

/-- **Separate declaration** (Def 4.3: separate declaration of the components): a component
declared on its own is one component, with its members in the same order. -/
theorem blockComponents_separate {c : Array Name} (hc : c ∈ comps) {comps_c : Array (Array Name)}
    (h' : blockComponents env c = .ok comps_c) : comps_c = #[c] := by
  obtain ⟨hne, hsub⟩ := blockComponents_sub h c hc
  have hndc : NodupB (nodesOf env c) := nodupB_sub hnd hsub
  have hcA : ∀ x ∈ c, x ∈ all := fun x hx =>
    Array.mem_toList_iff.1 (hsub.subset (Array.mem_toList_iff.2 hx))
  have nodupc : c.toList.Nodup := pairwise_nbeq_nodup ((members_nbeq hnd).sublist hsub)
  have mutl : ∀ m ∈ c, ∀ m' ∈ c, NReach (NodeEdge (nodesOf env c) (refsOf env)) m m' := by
    intro m hm m' hm'
    obtain ⟨r1, r2⟩ := (blockComponents_scc hnd h (hcA m hm) (hcA m' hm')).1 ⟨c, hc, hm, hm'⟩
    exact reach_restrict hnd hwf h hc hm m' r1 r2
  have each : ∀ c₁ ∈ comps_c, c₁ = c := by
    intro c₁ hc₁
    obtain ⟨hne₁, hsub₁⟩ := blockComponents_sub h' c₁ hc₁
    obtain ⟨m₁, hm₁⟩ := List.exists_mem_of_ne_nil c₁.toList (by
      intro e; exact hne₁ (Array.toList_inj.1 (by rw [e])))
    have hm₁' : m₁ ∈ c₁ := Array.mem_toList_iff.1 hm₁
    have hm₁c : m₁ ∈ c := Array.mem_toList_iff.1 (hsub₁.subset hm₁)
    have allin : ∀ x ∈ c, x ∈ c₁ := by
      intro x hx
      obtain ⟨c₂, hc₂, h1, h2⟩ := (blockComponents_scc hndc h' hm₁c hx).2
        ⟨mutl m₁ hm₁c x hx, mutl x hx m₁ hm₁c⟩
      rw [blockComponents_unique hndc h' c₂ hc₂ c₁ hc₁ m₁ h1 hm₁'] at h2
      exact h2
    apply Array.toList_inj.1
    apply hsub₁.eq_of_length
    apply Nat.le_antisymm hsub₁.length_le
    exact List.Nodup.length_le_of_subset nodupc fun x hx =>
      Array.mem_toList_iff.2 (allin x (Array.mem_toList_iff.1 hx))
  obtain ⟨cs, hs, hperm⟩ := blockComponents_list h'
  obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil c.toList (by
    intro e; exact hne (Array.toList_inj.1 (by rw [e])))
  have hm' : m ∈ c := Array.mem_toList_iff.1 hm
  have hlen : comps_c.toList.length ≤ 1 := by
    rw [hperm.length_eq]
    apply filterMap_length_le_one (fun c0 => m ∈ c0) (compMembers c) cs.toList
    · exact (sccsOf_pairwise hndc hs).imp fun {a b} hd hab => hd m hab.1 hab.2
    · intro c0 hc0 hsome
      cases e : compMembers c c0 with
      | none => exact absurd e hsome
      | some ms =>
        have hms : ms ∈ comps_c :=
          Array.mem_toList_iff.1 (hperm.mem_iff.2 (List.mem_filterMap.2 ⟨c0, hc0, e⟩))
        rw [each ms hms] at e
        exact ((mem_comp_iff hndc hs (Array.mem_toList_iff.1 hc0) e).1 hm').2
  obtain ⟨c₁, hc₁, -⟩ := blockComponents_cover hndc h' m hm'
  apply Array.toList_inj.1
  have hc₁' : c₁ ∈ comps_c.toList := Array.mem_toList_iff.2 hc₁
  cases hl : comps_c.toList with
  | nil => rw [hl] at hc₁'; cases hc₁'
  | cons d t =>
    cases t with
    | nil =>
      have : d ∈ comps_c := by rw [← Array.mem_toList_iff, hl]; exact List.mem_singleton_self _
      rw [each d this]
    | cons _ _ => rw [hl] at hlen; simp only [List.length_cons] at hlen; omega

end

/-! ## Member order: the same classes -/

theorem mapM_cons_ok {α β ε : Type} {f : α → Except ε β} {a : α} {l : List α} {r : List β} :
    (a :: l).mapM f = .ok r ↔ ∃ b bs, f a = .ok b ∧ l.mapM f = .ok bs ∧ r = b :: bs := by
  rw [List.mapM_cons]
  constructor
  · intro h
    obtain ⟨b, hb, h⟩ := except_bind_ok.1 h
    obtain ⟨bs, hbs, h⟩ := except_bind_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨b, bs, hb, hbs, h.symm⟩
  · rintro ⟨b, bs, hb, hbs, rfl⟩
    rw [hb]
    show (List.mapM f l >>= fun bs => pure (b :: bs)) = _
    rw [hbs]; rfl

theorem except_map_ok {α β ε : Type} {f : α → β} {e : Except ε α} {r : β} :
    (f <$> e) = .ok r → ∃ x, e = .ok x ∧ r = f x := by
  cases e with
  | error e' => intro h; cases h
  | ok x => intro h; exact ⟨x, rfl, (Except.ok.inj h).symm⟩

/-- `mapM` in `Except` over a permuted list: a permuted result. -/
theorem mapM_perm {α β ε : Type} (f : α → Except ε β) {l l' : List α} (p : l.Perm l') :
    ∀ {r : List β}, l.mapM f = .ok r → ∃ r', l'.mapM f = .ok r' ∧ r.Perm r' := by
  induction p with
  | nil => intro r h; exact ⟨r, h, List.Perm.refl _⟩
  | cons x _ ih =>
    intro r h
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_ok.1 h
    obtain ⟨bs', hbs', pb⟩ := ih hbs
    exact ⟨b :: bs', mapM_cons_ok.2 ⟨b, bs', hb, hbs', rfl⟩, pb.cons b⟩
  | swap x y l =>
    intro r h
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_ok.1 h
    obtain ⟨b', bs', hb', hbs', rfl⟩ := mapM_cons_ok.1 hbs
    exact ⟨b' :: b :: bs', mapM_cons_ok.2 ⟨b', b :: bs', hb', mapM_cons_ok.2 ⟨b, bs', hb, hbs', rfl⟩, rfl⟩,
      List.Perm.swap _ _ _⟩
  | trans _ _ ih₁ ih₂ =>
    intro r h
    obtain ⟨r₁, h₁, p₁⟩ := ih₁ h
    obtain ⟨r₂, h₂, p₂⟩ := ih₂ h₁
    exact ⟨r₂, h₂, p₁.trans p₂⟩

theorem mapM_names {β : Type} {g : Name → Except String β} (name : β → Name) :
    ∀ (l : List Name) (cs : List β), (∀ k ∈ l, ∀ cv, g k = .ok cv → name cv = k) →
      l.mapM g = .ok cs → cs.map name = l
  | [], cs, _, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | k :: l, cs, hg, h => by
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_ok.1 h
    rw [List.map_cons, hg k (List.mem_cons_self ..) b hb,
      mapM_names name l bs (fun k' hk' => hg k' (List.mem_cons_of_mem _ hk')) hbs]

/-- The member and constructor names of the constant Pass 1 builds for a member are its nodes. -/
theorem keysOf_mutConstOf {env : Env} {all : Array Name} (hwf : EnvWF env all) {n : Name}
    (hn : n ∈ all) {m : Ix.MutConst} (h : mutConstOf env n = .ok m) : keysOf m = nodeList env n := by
  have hname := hwf.name n hn
  unfold mutConstOf at h
  unfold nodeList
  cases hc : env.const? n with
  | none => rw [hc] at h; cases h
  | some ci =>
    rw [hc] at h
    have hnm := hname ci hc
    cases ci with
    | inductInfo v =>
      obtain ⟨ctors, hctors, h⟩ := except_bind_ok.1 h
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      rw [Array.mapM_eq_mapM_toList] at hctors
      obtain ⟨l, hl, hctors⟩ := except_map_ok hctors
      subst hctors
      have hmap := mapM_names (fun cv : Ix.ConstructorVal => cv.cnst.name) _ l (fun k hk cv hcv => by
        have hk' : k ∈ v.ctors := Array.mem_toList_iff.1 hk
        obtain ⟨cv', hcv', hnm', -⟩ := hwf.ctor n hn v hc k hk'
        rw [hcv'] at hcv
        simp only [pure, Except.pure, Except.ok.injEq] at hcv
        rw [← hcv]; exact hnm') hl
      simp only [ciName] at hnm
      simp only [keysOf, MutConst.fromInductiveVal, Ix.MutConst.name, Ix.MutConst.ctors, hnm]
      rw [List.toList_toArray, hmap]
    | defnInfo v =>
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      simp only [ciName] at hnm
      simp only [keysOf, MutConst.fromDefinitionVal, Ix.MutConst.name, Ix.MutConst.ctors, hnm]; rfl
    | thmInfo v =>
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      simp only [ciName] at hnm
      simp only [keysOf, MutConst.fromTheoremVal, Ix.MutConst.name, Ix.MutConst.ctors, hnm]; rfl
    | opaqueInfo v =>
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      simp only [ciName] at hnm
      simp only [keysOf, MutConst.fromOpaqueVal, Ix.MutConst.name, Ix.MutConst.ctors, hnm]; rfl
    | recInfo v =>
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      simp only [ciName] at hnm
      simp only [keysOf, Ix.MutConst.name, Ix.MutConst.ctors, hnm]; rfl
    | axiomInfo v => cases h
    | quotInfo v => cases h
    | ctorInfo v => cases h

/-- The keys of the members Pass 1 builds for a sub-block are the sub-block's nodes. -/
theorem keys_mapM_mutConstOf {env : Env} {all : Array Name} (hwf : EnvWF env all) :
    ∀ (l : List Name) (ms : List Ix.MutConst), (∀ n ∈ l, n ∈ all) → l.mapM (mutConstOf env) = .ok ms →
      ms.flatMap keysOf = l.flatMap (nodeList env)
  | [], ms, _, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | n :: l, ms, hl, h => by
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_ok.1 h
    rw [List.flatMap_cons, List.flatMap_cons, keysOf_mutConstOf hwf (hl n (List.mem_cons_self ..)) hb,
      keys_mapM_mutConstOf hwf l bs (fun k hk => hl k (List.mem_cons_of_mem _ hk)) hbs]

/-- What Pass 1 computes for one component (`canonBlock`, before the nested auxiliaries): the
members as `MutConst`s, then their classes in canonical order. -/
def classesOf (rules : Rules) (env : Env) (members : Array Name) :
    Except String (List (List Ix.MutConst) × SortStats) := do
  let cs ← members.toList.mapM (mutConstOf env)
  sortClasses rules env.addr? cs

/-- **Member order, at the level of the block** (Def 4.3, member reorder; §3.5 (iii)): under the
compiler's name-hash seed, a permuted block has the same components up to the order of their
members, and each component's classes (members, order, representatives, statistics) are the
same. -/
theorem canon_member_order {rules : Rules} (hseed : rules.seed = .byNameHash) {env : Env}
    {all all' : Array Name} {comps comps' : Array (Array Name)} (hp : all.toList.Perm all'.toList)
    (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all) (h : blockComponents env all = .ok comps)
    (h' : blockComponents env all' = .ok comps') :
    ∀ c ∈ comps, ∃ c' ∈ comps', c.toList.Perm c'.toList ∧
      ∀ r, classesOf rules env c = .ok r → classesOf rules env c' = .ok r := by
  intro c hc
  obtain ⟨c', hc', pc⟩ := blockComponents_perm hp hnd h h' c hc
  refine ⟨c', hc', pc, fun r hr => ?_⟩
  obtain ⟨-, hsub⟩ := blockComponents_sub h c hc
  unfold classesOf at hr ⊢
  obtain ⟨ms, hms, hr⟩ := except_bind_ok.1 hr
  obtain ⟨ms', hms', pms⟩ := mapM_perm (mutConstOf env) pc hms
  have hk : KeysDistinct ms := by
    unfold KeysDistinct
    rw [keys_mapM_mutConstOf hwf _ ms (fun n hn => Array.mem_toList_iff.1 (hsub.subset hn)) hms]
    have := nodupB_iff.1 (nodupB_sub hnd hsub)
    rwa [nodesOf_toList] at this
  rw [hms']
  show sortClasses rules env.addr? ms' = .ok r
  rw [← sortClasses_perm hseed env.addr? pms hk]
  exact hr

end Ix.CompileCert.Canon
