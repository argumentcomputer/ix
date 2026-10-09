import Ix.CompileCert.Canon.Total
import Ix.CompileCert.Canon.ComponentBridge

/-!
UNCOMPILED additive callback-domain graph/class transport. Every graph proof
uses the original two EnvWF fields and NodupB hypotheses where previously
required. The environment is unrestricted; no finite callback representation,
protection law, freshness or new hash premise is introduced. Source-backed
specialization is an exact field/lookup bridge, not the generic domain.
-/

namespace Ix.CompileCert.Canon.CallbackGraph

open Ix.Compile.Canon
open Ix (Name ConstantInfo MutConst)

/-- One step of the node list: the member, then its constructors. -/
def nodeStep (env : ComponentCore.Env) (nodes : Array Name) (n : Name) : Array Name :=
  match env.const? n with
  | some (.inductInfo v) => nodes.push n ++ v.ctors
  | _ => nodes.push n

/-- The nodes of the block `all`: each member followed by its constructors. -/
def nodesOf (env : ComponentCore.Env) (all : Array Name) : Array Name := all.foldl (nodeStep env) #[]

/-- The out-edges of a node. -/
def refsOf (env : ComponentCore.Env) (n : Name) : Std.HashSet Name :=
  match env.const? n with
  | some c => refsConst c
  | none => ∅

/-- `ComponentCore.blockComponents`, unfolded. -/
theorem blockComponents_eq (env : ComponentCore.Env) (all : Array Name) :
    ComponentCore.blockComponents env all =
      match sccsOf (nodesOf env all) (refsOf env) with
      | some cs => pure ((cs.filterMap (compMembersS all (allSetOf all))).qsort
          fun a b => decide (posOf all a < posOf all b))
      | none => throw "component computation ran out of fuel" := by
  unfold ComponentCore.blockComponents
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

/-! ## The node list -/

theorem mem_nodeStep {env : ComponentCore.Env} {acc : Array Name} {n x : Name} :
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

theorem mem_foldl_nodeStep {env : ComponentCore.Env} {x : Name} : ∀ (l : List Name) (acc : Array Name),
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
theorem mem_nodesOf {env : ComponentCore.Env} {all : Array Name} {x : Name} :
    x ∈ nodesOf env all ↔ ∃ n ∈ all, x = n ∨ ∃ v, env.const? n = some (.inductInfo v) ∧ x ∈ v.ctors := by
  unfold nodesOf
  rw [← Array.foldl_toList, mem_foldl_nodeStep]
  simp only [Array.not_mem_empty, false_or, Array.mem_toList_iff]

theorem mem_nodesOf_of_mem {env : ComponentCore.Env} {all : Array Name} {n : Name} (h : n ∈ all) :
    n ∈ nodesOf env all :=
  mem_nodesOf.2 ⟨n, h, .inl rfl⟩

section
variable {env : ComponentCore.Env} {all : Array Name} {comps : Array (Array Name)}
  (hnd : NodupB (nodesOf env all)) (h : ComponentCore.blockComponents env all = .ok comps)
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

/-- The node list of one member: the member, then its constructors. -/
def nodeList (env : ComponentCore.Env) (n : Name) : List Name :=
  match env.const? n with
  | some (.inductInfo v) => n :: v.ctors.toList
  | _ => [n]

theorem nodeList_cons (env : ComponentCore.Env) (n : Name) : ∃ r, nodeList env n = n :: r := by
  unfold nodeList
  cases env.const? n with
  | none => exact ⟨[], rfl⟩
  | some c => cases c <;> exact ⟨_, rfl⟩

theorem nodeStep_toList (env : ComponentCore.Env) (acc : Array Name) (n : Name) :
    (nodeStep env acc n).toList = acc.toList ++ nodeList env n := by
  unfold nodeStep nodeList
  cases env.const? n with
  | none => simp only [Array.toList_push]
  | some c =>
    cases c <;> simp only [Array.toList_push, Array.toList_append, List.append_assoc,
      List.singleton_append]

theorem nodesOf_toList (env : ComponentCore.Env) (all : Array Name) :
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

theorem members_sublist_nodes (env : ComponentCore.Env) :
    ∀ (l : List Name), l.Sublist (l.flatMap (nodeList env))
  | [] => List.Sublist.slnil
  | n :: l => by
    obtain ⟨r, hr⟩ := nodeList_cons env n
    rw [List.flatMap_cons, hr, List.cons_append]
    exact ((members_sublist_nodes env l).trans (List.sublist_append_right r _)).cons_cons n

/-- The members of a block with distinct nodes are distinct. -/
theorem members_nbeq {env : ComponentCore.Env} {all : Array Name} (hnd : NodupB (nodesOf env all)) :
    all.toList.Pairwise (fun a b => (a == b) = false) := by
  have := nodupB_iff.1 hnd
  rw [nodesOf_toList] at this
  exact this.sublist (members_sublist_nodes env _)

/-- A sub-block's nodes are distinct. -/
theorem nodupB_sub {env : ComponentCore.Env} {all sub : Array Name} (hnd : NodupB (nodesOf env all))
    (hs : sub.toList.Sublist all.toList) : NodupB (nodesOf env sub) := by
  have := nodupB_iff.1 hnd
  rw [nodesOf_toList] at this
  apply nodupB_iff.2
  rw [nodesOf_toList]
  exact this.sublist (sublist_flatMap _ hs)

theorem blockComponents_list {env : ComponentCore.Env} {all : Array Name} {comps : Array (Array Name)}
    (h : ComponentCore.blockComponents env all = .ok comps) : ∃ cs, sccsOf (nodesOf env all) (refsOf env) = some cs ∧
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

/-- What Pass 1 needs of the environment: each member answers with a constant of its own name,
and an inductive member's constructors are constructors of it under their own names. -/
structure EnvWF (env : ComponentCore.Env) (all : Array Name) : Prop where
  name : ∀ n ∈ all, ∀ ci, env.const? n = some ci → ciName ci = n
  ctor : ∀ n ∈ all, ∀ v, env.const? n = some (.inductInfo v) → ∀ k ∈ v.ctors,
    ∃ cv, env.const? k = some (.ctorInfo cv) ∧ cv.cnst.name = k ∧ cv.induct = n

theorem EnvWF.sub {env : ComponentCore.Env} {all sub : Array Name} (h : EnvWF env all) (hs : ∀ n ∈ sub, n ∈ all) :
    EnvWF env sub := ⟨fun n hn => h.name n (hs n hn), fun n hn => h.ctor n (hs n hn)⟩

/-- **Member order** (Def 4.3, member reorder): the components of a permuted block are those of
the block, each a permutation of the other's. -/
theorem blockComponents_perm {env : ComponentCore.Env} {all all' : Array Name} {comps comps' : Array (Array Name)}
    (hp : all.toList.Perm all'.toList) (hnd : NodupB (nodesOf env all))
    (h : ComponentCore.blockComponents env all = .ok comps) (h' : ComponentCore.blockComponents env all' = .ok comps') :
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

theorem refsOf_ind {env : ComponentCore.Env} {n : Name} {v : Ix.InductiveVal} (h : env.const? n = some (.inductInfo v))
    {k : Name} (hk : k ∈ v.ctors) : (refsOf env n).contains k = true := by
  unfold refsOf
  rw [h]
  show (Array.foldl (fun x1 x2 => x1.insert x2) (refsExpr v.cnst.type) v.ctors).contains k = true
  rw [← Array.foldl_toList]
  exact foldl_insert_contains _ _ _ (.inr (Array.mem_toList_iff.2 hk))

theorem refsOf_ctor {env : ComponentCore.Env} {k : Name} {cv : Ix.ConstructorVal}
    (h : env.const? k = some (.ctorInfo cv)) : (refsOf env k).contains cv.induct = true := by
  unfold refsOf
  rw [h]
  show ((refsExpr cv.cnst.type).insert cv.induct).contains cv.induct = true
  rw [Std.HashSet.contains_insert, name_beq_refl, Bool.true_or]

/-- An inductive member and each of its constructors reach each other. -/
theorem ctor_edges {env : ComponentCore.Env} {all : Array Name} (hwf : EnvWF env all) {n : Name} (hn : n ∈ all)
    {v : Ix.InductiveVal} (hv : env.const? n = some (.inductInfo v)) {k : Name} (hk : k ∈ v.ctors) :
    NodeEdge (nodesOf env all) (refsOf env) n k ∧ NodeEdge (nodesOf env all) (refsOf env) k n := by
  have hnN := mem_nodesOf_of_mem (env := env) hn
  have hkN : k ∈ nodesOf env all := mem_nodesOf.2 ⟨n, hn, .inr ⟨v, hv, hk⟩⟩
  obtain ⟨cv, hcv, -, hind⟩ := hwf.ctor n hn v hv k hk
  refine ⟨⟨hnN, hkN, refsOf_ind hv hk⟩, ⟨hkN, hnN, ?_⟩⟩
  rw [← hind]; exact refsOf_ctor hcv

section
variable {env : ComponentCore.Env} {all : Array Name} {comps : Array (Array Name)}
  (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all) (h : ComponentCore.blockComponents env all = .ok comps)
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
    (h' : ComponentCore.blockComponents env c = .ok comps_c) : comps_c = #[c] := by
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

/-- The member and constructor names of the constant Pass 1 builds for a member are its nodes. -/
theorem keysOf_mutConstOf {env : ComponentCore.Env} {all : Array Name} (hwf : EnvWF env all) {n : Name}
    (hn : n ∈ all) {m : Ix.MutConst} (h : ComponentCore.mutConstOf env n = .ok m) : keysOf m = nodeList env n := by
  have hname := hwf.name n hn
  unfold ComponentCore.mutConstOf at h
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
theorem keys_mapM_mutConstOf {env : ComponentCore.Env} {all : Array Name} (hwf : EnvWF env all) :
    ∀ (l : List Name) (ms : List Ix.MutConst), (∀ n ∈ l, n ∈ all) → l.mapM (ComponentCore.mutConstOf env) = .ok ms →
      ms.flatMap keysOf = l.flatMap (nodeList env)
  | [], ms, _, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | n :: l, ms, hl, h => by
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_ok.1 h
    rw [List.flatMap_cons, List.flatMap_cons, keysOf_mutConstOf hwf (hl n (List.mem_cons_self ..)) hb,
      keys_mapM_mutConstOf hwf l bs (fun k hk => hl k (List.mem_cons_of_mem _ hk)) hbs]

/-- **`ComponentCore.blockComponents` never fails.** -/
theorem blockComponents_ok (env : ComponentCore.Env) (all : Array Name) :
    ∃ comps, ComponentCore.blockComponents env all = .ok comps := by
  obtain ⟨cs, hs⟩ := sccsOf_some (nodesOf env all) (refsOf env)
  rw [blockComponents_eq, hs]
  exact ⟨_, rfl⟩

/-- **Separate declaration, unconditionally**: a component declared on its own is that one
component. -/
theorem blockComponents_separate_total {env : ComponentCore.Env} {all : Array Name} {comps : Array (Array Name)}
    (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all) (h : ComponentCore.blockComponents env all = .ok comps)
    {c : Array Name} (hc : c ∈ comps) : ComponentCore.blockComponents env c = .ok #[c] := by
  obtain ⟨comps_c, h'⟩ := blockComponents_ok env c
  rw [h', blockComponents_separate hnd hwf h hc h']

/-- The actual producer's node list is exactly the generic callback node list. -/
theorem nodesOf_source_eq (env : Ix.Compile.Canon.Env) (all : Array Name) :
    nodesOf (env.asCore) all = Ix.CompileCert.Canon.nodesOf env all := rfl

/-- No source reference edge is changed by the generic environment projection. -/
theorem refsOf_source_eq (env : Ix.Compile.Canon.Env) (name : Name) :
    refsOf (env.asCore) name = Ix.CompileCert.Canon.refsOf env name := rfl

/-- The original two well-formedness fields, with no added condition. -/
theorem EnvWF_source_iff (env : Ix.Compile.Canon.Env) (all : Array Name) :
    EnvWF (env.asCore) all ↔ Ix.CompileCert.Canon.EnvWF env all := by
  constructor
  · intro h
    exact ⟨h.name, h.ctor⟩
  · intro h
    exact ⟨h.name, h.ctor⟩

end Ix.CompileCert.Canon.CallbackGraph
