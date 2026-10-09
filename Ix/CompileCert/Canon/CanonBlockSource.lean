import Ix.CompileCert.Canon.Loop
import Ix.CompileCert.Canon.Total
import Ix.CompileCert.Canon.Coarsest
import Ix.Compile.Canon.Block

/-!
# M7 L1, the block driver `canonBlock`

`Ix.Compile.Canon.canonBlock rules env all` computes the components of the block
(`blockComponents`), then for each component its classes (`sortClasses` over the members as
`mutConstOf` builds them, which is `classesOf`), the classes with every external reference equal
(`sortClassesBlind`), and its nested data (`componentNested`, then `evaporate` against all the
components' classes). `canonBlock_spec` states that, component by component, against the code as
it is. The block theorems proved over `blockComponents` and `classesOf` (`BlockComp.lean`,
`Total.lean`, `Coarsest.lean`) are restated over `canonBlock`:

* its components are the strongly connected components of the block's reference graph
  (`canonBlock_scc`), with acyclic condensation (`canonBlock_acyclic`);
* each component's classes are the coarsest consistent partition of its members
  (`canonBlock_coarsest`);
* member order (Def 4.3): a permuted block has the same components up to member order, with the
  same classes, blind classes and statistics (`canonBlock_source_member_order`);
* separate declaration (Def 4.3): a component declared on its own is one component with the same
  members, classes, blind classes and statistics (`canonBlock_source_separate`).

The nested part of the same presentations is `NestedCanon.lean`.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name ConstantInfo MutConst)

/-- What `canonBlock` computes for the component `members` before its nested data. -/
structure FirstSpec (rules : Rules) (env : Env) (members : Array Name) (c : ComponentCanon) : Prop where
  hmem : c.members = members
  hnone : c.nested = none
  hcls : ∃ cs F B, members.toList.mapM (mutConstOf env) = .ok cs ∧
    sortClasses rules env.addr? cs = .ok (F, c.stats) ∧ c.classes = classNames F ∧
    sortClassesBlind rules cs = .ok B ∧ c.blindClasses = classNames B

/-- What `canonBlock` computes for one component: `FirstSpec`, then its nested data from
`componentNested` and `evaporate` (`classesAll`: every component's classes). -/
structure ComponentSpec (rules : Rules) (env : Env) (all : Array Name)
    (classesAll : Array (Array (Array Name))) (i : Nat) (members : Array Name) (c : ComponentCanon) :
    Prop where
  hmem : c.members = members
  hcls : ∃ cs F B, members.toList.mapM (mutConstOf env) = .ok cs ∧
    sortClasses rules env.addr? cs = .ok (F, c.stats) ∧ c.classes = classNames F ∧
    sortClassesBlind rules cs = .ok B ∧ c.blindClasses = classNames B
  hnest : ∃ n0, componentNested rules env all c.classes = .ok n0 ∧
    n0.mapM (evaporate env rules all classesAll i) = .ok c.nested

/-- **`canonBlock`, component by component**: the block keeps `all`; its components are those of
`blockComponents`, in that order; each holds its members' classes (`sortClasses` of the members as
`mutConstOf` builds them), blind classes and statistics, and its nested data from
`componentNested` and `evaporate` against the components' classes. -/
theorem canonBlock_spec {rules : Rules} {env : Env} {all : Array Name} {b : BlockCanon}
    (h : canonBlock rules env all = .ok b) :
    b.all = all ∧ ∃ comps, blockComponents env all = .ok comps ∧
      b.components.size = comps.size ∧
      ∀ (i : Nat) (c : ComponentCanon), b.components[i]? = some c →
        ∃ members, comps[i]? = some members ∧
          ComponentSpec rules env all (b.components.map (·.classes)) i members c := by
  unfold canonBlock at h
  obtain ⟨comps, hcomps, h⟩ := except_bind_ok.1 h
  obtain ⟨out, hout, h⟩ := except_bind_ok.1 h
  obtain ⟨out', hout', h⟩ := except_bind_ok.1 h
  rw [← except_pure_ok h]
  have p1 := forIn_push_array comps _ (FirstSpec rules env) (by
      intro members r s hs
      obtain ⟨cs, hcs, hs⟩ := except_bind_ok.1 hs
      obtain ⟨⟨F, st⟩, hF, hs⟩ := except_bind_ok.1 hs
      obtain ⟨B, hB, hs⟩ := except_bind_ok.1 hs
      rw [← except_pure_ok hs]
      exact ⟨_, rfl, ⟨rfl, rfl, cs, F, B, hcs, hF, rfl, hB, rfl⟩⟩) hout
  -- the second loop
  have p2 := forIn_push_array out.zipIdx _
    (fun (x : ComponentCanon × Nat) (c' : ComponentCanon) =>
      c'.members = x.1.members ∧ c'.classes = x.1.classes ∧ c'.blindClasses = x.1.blindClasses ∧
      c'.stats = x.1.stats ∧ ∃ n0, componentNested rules env all x.1.classes = .ok n0 ∧
        n0.mapM (evaporate env rules all (out.map (·.classes)) x.2) = .ok c'.nested)
    (by
      intro x r s hs
      obtain ⟨c, i⟩ := x
      obtain ⟨n0, hn0, hs⟩ := except_bind_ok.1 hs
      obtain ⟨n1, hn1, hs⟩ := except_bind_ok.1 hs
      rw [← except_pure_ok hs]
      exact ⟨_, rfl, rfl, rfl, rfl, rfl, n0, hn0, hn1⟩) hout'
  have hcl : out'.map (·.classes) = out.map (·.classes) := by
    apply Array.ext'
    rw [Array.toList_map, Array.toList_map]
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_map, List.getElem?_map]
    cases hy : out'.toList[i]? with
    | none =>
      have : out.zipIdx.toList[i]? = none := by
        rw [List.getElem?_eq_none_iff] at hy ⊢; rw [p2.1]; exact hy
      rw [Array.toList_zipIdx, List.getElem?_zipIdx] at this
      simp only [Option.map_eq_none_iff] at this
      rw [this]
    | some y =>
      obtain ⟨x, hx, hq⟩ := p2.get hy
      rw [Array.toList_zipIdx, List.getElem?_zipIdx] at hx
      cases hxo : out.toList[i]? with
      | none => rw [hxo] at hx; cases hx
      | some c =>
        rw [hxo] at hx
        simp only [Option.map_some, Option.some.injEq] at hx
        subst hx
        simp only [Option.map_some, hq.2.1]
  refine ⟨rfl, comps, hcomps, ?_, ?_⟩
  · have e1 := p1.1; have e2 := p2.1
    rw [Array.toList_zipIdx, List.length_zipIdx] at e2
    simp only [Array.length_toList] at e1 e2
    show out'.size = comps.size
    omega
  · intro i c hc
    have hc' : out'.toList[i]? = some c := by rw [Array.getElem?_toList]; exact hc
    obtain ⟨x, hx, hq⟩ := p2.get hc'
    rw [Array.toList_zipIdx, List.getElem?_zipIdx] at hx
    cases hxo : out.toList[i]? with
    | none => rw [hxo] at hx; cases hx
    | some c0 =>
      rw [hxo] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      subst hx
      obtain ⟨members, hm, hf⟩ := p1.get hxo
      refine ⟨members, by rw [← Array.getElem?_toList]; exact hm, ?_⟩
      obtain ⟨hmem, hcls, hbl, hst, n0, hn0, hn1⟩ := hq
      obtain ⟨cs, F, B, hcs, hF, hFc, hB, hBc⟩ := hf.hcls
      refine ⟨by rw [hmem]; exact hf.hmem, ⟨cs, F, B, hcs, by rw [hst]; exact hF,
        by rw [hcls]; exact hFc, hB, by rw [hbl]; exact hBc⟩, n0, by rw [hcls]; exact hn0, ?_⟩
      show Option.mapM _ n0 = (Except.ok c.nested : Except String _)
      simp only [Nat.zero_add] at hn1
      have : (BlockCanon.components { all := all, components := out' }).map (·.classes) =
          out.map (·.classes) := hcl
      rw [this]; exact hn1

/-- The component of `canonBlock` at a position, and the block's components as `blockComponents`
returns them. -/
theorem canonBlock_comps {rules : Rules} {env : Env} {all : Array Name} {b : BlockCanon}
    (h : canonBlock rules env all = .ok b) :
    ∃ comps, blockComponents env all = .ok comps ∧ b.components.map (·.members) = comps := by
  obtain ⟨-, comps, hcomps, hsize, hspec⟩ := canonBlock_spec h
  refine ⟨comps, hcomps, ?_⟩
  apply Array.ext'
  rw [Array.toList_map]
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, Array.getElem?_toList, Array.getElem?_toList]
  cases hc : b.components[i]? with
  | none =>
    have : comps[i]? = none := by
      rw [Array.getElem?_eq_none_iff] at hc ⊢; omega
    rw [this]; rfl
  | some c =>
    obtain ⟨members, hm, hs⟩ := hspec i c hc
    rw [hm, Option.map_some, hs.hmem]

/-- **The components of `canonBlock` are the strongly connected components** of the block's
reference graph (members and constructors), restricted to the members (Def 2.1). -/
theorem canonBlock_scc {rules : Rules} {env : Env} {all : Array Name} {b : BlockCanon}
    (hnd : NodupB (nodesOf env all)) (h : canonBlock rules env all = .ok b) {m m' : Name}
    (hm : m ∈ all) (hm' : m' ∈ all) :
    (∃ c ∈ b.components, m ∈ c.members ∧ m' ∈ c.members) ↔
      NReach (NodeEdge (nodesOf env all) (refsOf env)) m m' ∧
        NReach (NodeEdge (nodesOf env all) (refsOf env)) m' m := by
  obtain ⟨comps, hcomps, hmap⟩ := canonBlock_comps h
  rw [← blockComponents_scc hnd hcomps hm hm', ← hmap]
  constructor
  · rintro ⟨c, hc, h1, h2⟩; exact ⟨c.members, Array.mem_map_of_mem hc, h1, h2⟩
  · rintro ⟨c, hc, h1, h2⟩
    obtain ⟨c', hc', rfl⟩ := Array.mem_map.1 hc
    exact ⟨c', hc', h1, h2⟩

/-- **The condensation of `canonBlock`'s components is acyclic.** -/
theorem canonBlock_acyclic {rules : Rules} {env : Env} {all : Array Name} {b : BlockCanon}
    (hnd : NodupB (nodesOf env all)) (h : canonBlock rules env all = .ok b)
    {c c' : ComponentCanon} (hc : c ∈ b.components) (hc' : c' ∈ b.components) {m m' : Name}
    (hm : m ∈ c.members) (hm' : m' ∈ c'.members)
    (r1 : NReach (NodeEdge (nodesOf env all) (refsOf env)) m m')
    (r2 : NReach (NodeEdge (nodesOf env all) (refsOf env)) m' m) : c.members = c'.members := by
  obtain ⟨comps, hcomps, hmap⟩ := canonBlock_comps h
  have h1 : c.members ∈ comps := hmap ▸ Array.mem_map_of_mem hc
  have h2 : c'.members ∈ comps := hmap ▸ Array.mem_map_of_mem hc'
  exact blockComponents_acyclic hnd hcomps h1 h2 hm hm' r1 r2

/-- A component's members are members of the block. -/
theorem canonBlock_members_sub {rules : Rules} {env : Env} {all : Array Name} {b : BlockCanon}
    (h : canonBlock rules env all = .ok b) {c : ComponentCanon} (hc : c ∈ b.components) :
    c.members ≠ #[] ∧ c.members.toList.Sublist all.toList := by
  obtain ⟨comps, hcomps, hmap⟩ := canonBlock_comps h
  exact blockComponents_sub hcomps c.members (hmap ▸ Array.mem_map_of_mem hc)

/-- The spec of the component at a position, by membership. -/
theorem canonBlock_mem_spec {rules : Rules} {env : Env} {all : Array Name} {b : BlockCanon}
    (h : canonBlock rules env all = .ok b) {c : ComponentCanon} (hc : c ∈ b.components) :
    ∃ i, ComponentSpec rules env all (b.components.map (·.classes)) i c.members c := by
  obtain ⟨-, comps, -, -, hspec⟩ := canonBlock_spec h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (Array.mem_toList_iff.2 hc)
  rw [Array.getElem?_toList] at hi
  obtain ⟨members, -, hs⟩ := hspec i c hi
  exact ⟨i, by have := hs.hmem; rw [this]; exact hs⟩

/-- **Each component's classes are the coarsest consistent partition of its members**
(Def 2.2, over `canonBlock`). -/
theorem canonBlock_coarsest {rules : Rules} (hpf : rules.portFixes = true) {env : Env}
    (hA : AddrCongr env.addr?) {all : Array Name} {b : BlockCanon}
    (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all)
    (h : canonBlock rules env all = .ok b) {c : ComponentCanon} (hc : c ∈ b.components) :
    ∃ cs F, c.members.toList.mapM (mutConstOf env) = .ok cs ∧ c.classes = classNames F ∧
      sortClasses rules env.addr? cs = .ok (F, c.stats) ∧
      Partition F cs ∧ Consistent rules env.addr? F ∧ Coarsest rules env.addr? cs F := by
  obtain ⟨i, hs⟩ := canonBlock_mem_spec h hc
  obtain ⟨cs, F, -, hcs, hF, hFc, -, -⟩ := hs.hcls
  have hsub := (canonBlock_members_sub h hc).2
  have hk : KeysDistinct cs := by
    unfold KeysDistinct
    rw [keys_mapM_mutConstOf hwf _ cs (fun n hn => Array.mem_toList_iff.1 (hsub.subset hn)) hcs]
    have := nodupB_iff.1 (nodupB_sub hnd hsub)
    rwa [nodesOf_toList] at this
  exact ⟨cs, F, hcs, hFc, hF, sortClasses_coarsest hpf hA hk hF⟩

/-- `sortClassesBlind` under the name-hash seed does not depend on the order of the members. -/
theorem sortClassesBlind_perm {rules : Rules} (hseed : rules.seed = .byNameHash)
    {xs ys : List MutConst} (hp : xs.Perm ys) (hk : KeysDistinct xs) :
    sortClassesBlind rules xs = sortClassesBlind rules ys := by
  unfold sortClassesBlind
  rw [sortClasses_perm (rules := { rules with tieBreak := .blind }) hseed _ hp hk]

/-- The members' `MutConst`s of a component have distinct keys. -/
theorem component_keys {env : Env} {all : Array Name} (hnd : NodupB (nodesOf env all))
    (hwf : EnvWF env all) {members : Array Name} (hsub : members.toList.Sublist all.toList)
    {cs : List MutConst} (hcs : members.toList.mapM (mutConstOf env) = .ok cs) : KeysDistinct cs := by
  unfold KeysDistinct
  rw [keys_mapM_mutConstOf hwf _ cs (fun n hn => Array.mem_toList_iff.1 (hsub.subset hn)) hcs]
  have := nodupB_iff.1 (nodupB_sub hnd hsub)
  rwa [nodesOf_toList] at this

/-- **Member order, over `canonBlock`** (Def 4.3, member reorder): under the compiler's name-hash
seed, when both presentations compile, every component of the block has a component of the
permuted block with the same members up to order and the same classes, blind classes and
statistics. -/
theorem canonBlock_source_member_order {rules : Rules} (hseed : rules.seed = .byNameHash) {env : Env}
    {all all' : Array Name} (hp : all.toList.Perm all'.toList) (hnd : NodupB (nodesOf env all))
    (hwf : EnvWF env all) {b b' : BlockCanon} (h : canonBlock rules env all = .ok b)
    (h' : canonBlock rules env all' = .ok b') :
    ∀ c ∈ b.components, ∃ c' ∈ b'.components, c.members.toList.Perm c'.members.toList ∧
      c'.classes = c.classes ∧ c'.blindClasses = c.blindClasses ∧ c'.stats = c.stats := by
  intro c hc
  obtain ⟨comps, hcomps, hmap⟩ := canonBlock_comps h
  obtain ⟨comps', hcomps', hmap'⟩ := canonBlock_comps h'
  have hcm : c.members ∈ comps := hmap ▸ Array.mem_map_of_mem hc
  obtain ⟨m', hm', pm⟩ := blockComponents_perm hp hnd hcomps hcomps' c.members hcm
  rw [← hmap'] at hm'
  obtain ⟨c', hc', rfl⟩ := Array.mem_map.1 hm'
  refine ⟨c', hc', pm, ?_⟩
  obtain ⟨i, hs⟩ := canonBlock_mem_spec h hc
  obtain ⟨i', hs'⟩ := canonBlock_mem_spec h' hc'
  obtain ⟨cs, F, B, hcs, hF, hFc, hB, hBc⟩ := hs.hcls
  obtain ⟨cs', F', B', hcs', hF', hFc', hB', hBc'⟩ := hs'.hcls
  have hsub := (canonBlock_members_sub h hc).2
  have hk := component_keys hnd hwf hsub hcs
  obtain ⟨cs'', hcs'', pcs⟩ := mapM_perm (mutConstOf env) pm hcs
  rw [hcs'] at hcs''; cases hcs''
  have e1 := sortClasses_perm hseed env.addr? pcs hk
  rw [hF, hF'] at e1
  simp only [Except.ok.injEq, Prod.mk.injEq] at e1
  obtain ⟨rfl, est⟩ := e1
  have e2 := sortClassesBlind_perm hseed pcs hk
  rw [hB, hB'] at e2
  cases e2
  exact ⟨by rw [hFc, hFc'], by rw [hBc, hBc'], est.symm⟩

/-- **Separate declaration, over `canonBlock`** (Def 4.3): a component of the block, declared on its
own, is one component with the same members, classes, blind classes and statistics. -/
theorem canonBlock_source_separate {rules : Rules} {env : Env} {all : Array Name} {b : BlockCanon}
    (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all) (h : canonBlock rules env all = .ok b)
    {c : ComponentCanon} (hc : c ∈ b.components) {b' : BlockCanon}
    (h' : canonBlock rules env c.members = .ok b') :
    ∃ c', b'.components = #[c'] ∧ c'.members = c.members ∧ c'.classes = c.classes ∧
      c'.blindClasses = c.blindClasses ∧ c'.stats = c.stats := by
  obtain ⟨comps, hcomps, hmap⟩ := canonBlock_comps h
  have hcm : c.members ∈ comps := hmap ▸ Array.mem_map_of_mem hc
  have hsep := blockComponents_separate_total hnd hwf hcomps hcm
  obtain ⟨comps', hcomps', hmap'⟩ := canonBlock_comps h'
  rw [hsep] at hcomps'; cases hcomps'
  have hsize : b'.components.size = 1 := by
    have := congrArg Array.size hmap'; simpa using this
  have h0 : 0 < b'.components.size := by omega
  let c' := b'.components[0]
  have hc'0 : b'.components = #[c'] := by
    apply Array.ext
    · simp [hsize]
    · intro i h1 h2
      have : i = 0 := by simp at h2; omega
      subst this; rfl
  have hc' : c' ∈ b'.components := by rw [hc'0]; simp
  have hmem : c'.members = c.members := by
    have := congrArg (·[0]?) hmap'
    simp only [Array.getElem?_map, hc'0] at this
    simpa using this
  refine ⟨c', hc'0, hmem, ?_⟩
  obtain ⟨i, hs⟩ := canonBlock_mem_spec h hc
  obtain ⟨i', hs'⟩ := canonBlock_mem_spec h' hc'
  obtain ⟨cs, F, B, hcs, hF, hFc, hB, hBc⟩ := hs.hcls
  obtain ⟨cs', F', B', hcs', hF', hFc', hB', hBc'⟩ := hs'.hcls
  rw [hmem, hcs] at hcs'; cases hcs'
  rw [hF] at hF'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hF'
  obtain ⟨rfl, est⟩ := hF'
  rw [hB] at hB'; cases hB'
  exact ⟨by rw [hFc, hFc'], by rw [hBc, hBc'], est.symm⟩

end Ix.CompileCert.Canon
