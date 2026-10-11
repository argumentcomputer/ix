import Ix.CompileCert.Canon.CallbackBlock
import Ix.CompileCert.Canon.CallbackGraph

/-!
UNCOMPILED additive companions for the original member-order and separate
canonBlock conclusions. These transport the checked graph/class proofs to
arbitrary callbacks, then use the exact generic component canonical-auxiliary
lemma. The fixed protection functions are the actual inputs of both runs;
there is no existential support replacement or caller protection premise.
The successful-run hypotheses and every original output equality are retained.
-/

namespace Ix.CompileCert.Canon.CallbackBlock

open Ix.Compile.Canon
open Ix (Name ConstantInfo MutConst)

/-- The component of `canonBlock` at a position, and the block's components as `ComponentCore.blockComponents`
returns them. -/
theorem canonBlock_comps {rules : Rules} {protect : ComponentCore.Protection} {env : ComponentCore.Env} {all : Array Name} {b : BlockCanon}
    (h : ComponentCore.canonBlock protect rules env all = .ok b) :
    ∃ comps, ComponentCore.blockComponents env all = .ok comps ∧ b.components.map (·.members) = comps := by
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

/-- A component's members are members of the block. -/
theorem canonBlock_members_sub {rules : Rules} {protect : ComponentCore.Protection} {env : ComponentCore.Env} {all : Array Name} {b : BlockCanon}
    (h : ComponentCore.canonBlock protect rules env all = .ok b) {c : ComponentCanon} (hc : c ∈ b.components) :
    c.members ≠ #[] ∧ c.members.toList.Sublist all.toList := by
  obtain ⟨comps, hcomps, hmap⟩ := canonBlock_comps h
  exact CallbackGraph.blockComponents_sub hcomps c.members (hmap ▸ Array.mem_map_of_mem hc)

/-- The members' `MutConst`s of a component have distinct keys. -/
theorem component_keys {env : ComponentCore.Env} {all : Array Name} (hnd : NodupB (CallbackGraph.nodesOf env all))
    (hwf : CallbackGraph.EnvWF env all) {members : Array Name} (hsub : members.toList.Sublist all.toList)
    {cs : List MutConst} (hcs : members.toList.mapM (ComponentCore.mutConstOf env) = .ok cs) : KeysDistinct cs := by
  unfold KeysDistinct
  rw [CallbackGraph.keys_mapM_mutConstOf hwf _ cs (fun n hn => Array.mem_toList_iff.1 (hsub.subset hn)) hcs]
  have := nodupB_iff.1 (CallbackGraph.nodupB_sub hnd hsub)
  rwa [CallbackGraph.nodesOf_toList] at this

/-- **Member order, over `canonBlock`** (Def 4.3, member reorder): under the compiler's name-hash
seed, when both presentations compile, every component of the block has a component of the
permuted block with the same members up to order and the same classes, blind classes and
statistics. -/
theorem canonBlock_member_order {rules : Rules} (hseed : rules.seed = .byNameHash) {protect : ComponentCore.Protection} {env : ComponentCore.Env}
    {all all' : Array Name} (hp : all.toList.Perm all'.toList) (hnd : NodupB (CallbackGraph.nodesOf env all))
    (hwf : CallbackGraph.EnvWF env all) {b b' : BlockCanon} (h : ComponentCore.canonBlock protect rules env all = .ok b)
    (h' : ComponentCore.canonBlock protect rules env all' = .ok b') :
    ∀ c ∈ b.components, ∃ c' ∈ b'.components, c.members.toList.Perm c'.members.toList ∧
      c'.classes = c.classes ∧ c'.blindClasses = c.blindClasses ∧ c'.stats = c.stats := by
  intro c hc
  obtain ⟨comps, hcomps, hmap⟩ := canonBlock_comps h
  obtain ⟨comps', hcomps', hmap'⟩ := canonBlock_comps h'
  have hcm : c.members ∈ comps := hmap ▸ Array.mem_map_of_mem hc
  obtain ⟨m', hm', pm⟩ := CallbackGraph.blockComponents_perm hp hnd hcomps hcomps' c.members hcm
  rw [← hmap'] at hm'
  obtain ⟨c', hc', rfl⟩ := Array.mem_map.1 hm'
  refine ⟨c', hc', pm, ?_⟩
  obtain ⟨i, hs⟩ := canonBlock_mem_spec h hc
  obtain ⟨i', hs'⟩ := canonBlock_mem_spec h' hc'
  obtain ⟨cs, F, B, hcs, hF, hFc, hB, hBc⟩ := hs.hcls
  obtain ⟨cs', F', B', hcs', hF', hFc', hB', hBc'⟩ := hs'.hcls
  have hsub := (canonBlock_members_sub h hc).2
  have hk := component_keys hnd hwf hsub hcs
  obtain ⟨cs'', hcs'', pcs⟩ := mapM_perm (ComponentCore.mutConstOf env) pm hcs
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
theorem canonBlock_separate {rules : Rules} {protect : ComponentCore.Protection} {env : ComponentCore.Env} {all : Array Name} {b : BlockCanon}
    (hnd : NodupB (CallbackGraph.nodesOf env all)) (hwf : CallbackGraph.EnvWF env all) (h : ComponentCore.canonBlock protect rules env all = .ok b)
    {c : ComponentCanon} (hc : c ∈ b.components) {b' : BlockCanon}
    (h' : ComponentCore.canonBlock protect rules env c.members = .ok b') :
    ∃ c', b'.components = #[c'] ∧ c'.members = c.members ∧ c'.classes = c.classes ∧
      c'.blindClasses = c.blindClasses ∧ c'.stats = c.stats := by
  obtain ⟨comps, hcomps, hmap⟩ := canonBlock_comps h
  have hcm : c.members ∈ comps := hmap ▸ Array.mem_map_of_mem hc
  have hsep := CallbackGraph.blockComponents_separate_total hnd hwf hcomps hcm
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

/-- **Member order, nested part** (Def 4.3): under the compiler's rules (name-hash seed, discovery
order), every component of a block has a component of the permuted block with the same members up
to order, the same classes, and the same canonical nested auxiliaries and signatures. -/
theorem canonBlock_member_order_nested {rules : Rules} (hseed : rules.seed = .byNameHash)
    (hr : rules.nested = .discovery) {protect : ComponentCore.Protection} {env : ComponentCore.Env} {all all' : Array Name}
    (hp : all.toList.Perm all'.toList) (hnd : NodupB (CallbackGraph.nodesOf env all)) (hwf : CallbackGraph.EnvWF env all)
    {b b' : BlockCanon} (h : ComponentCore.canonBlock protect rules env all = .ok b) (h' : ComponentCore.canonBlock protect rules env all' = .ok b') :
    ∀ c ∈ b.components, ∃ c' ∈ b'.components, c.members.toList.Perm c'.members.toList ∧
      c'.classes = c.classes ∧ c'.blindClasses = c.blindClasses ∧ c'.stats = c.stats ∧
      canonAux c'.nested = canonAux c.nested := by
  intro c hc
  obtain ⟨c', hc', pm, hcl, hbl, hst⟩ := canonBlock_member_order hseed hp hnd hwf h h' c hc
  refine ⟨c', hc', pm, hcl, hbl, hst, ?_⟩
  obtain ⟨n0, hn0, e0⟩ := canonBlock_canonAux h hc
  obtain ⟨n0', hn0', e0'⟩ := canonBlock_canonAux h' hc'
  rw [e0, e0']
  rw [hcl] at hn0'
  exact ComponentCoreProof.componentNested_canonAux hr hn0' hn0

/-- **Separate declaration, nested part** (Def 4.3): a component declared on its own has the same
canonical nested auxiliaries and signatures as within its block. -/
theorem canonBlock_separate_nested {rules : Rules} (hr : rules.nested = .discovery) {protect : ComponentCore.Protection} {env : ComponentCore.Env}
    {all : Array Name} {b : BlockCanon} (hnd : NodupB (CallbackGraph.nodesOf env all)) (hwf : CallbackGraph.EnvWF env all)
    (h : ComponentCore.canonBlock protect rules env all = .ok b) {c : ComponentCanon} (hc : c ∈ b.components)
    {b' : BlockCanon} (h' : ComponentCore.canonBlock protect rules env c.members = .ok b') :
    ∃ c', b'.components = #[c'] ∧ c'.members = c.members ∧ c'.classes = c.classes ∧
      c'.blindClasses = c.blindClasses ∧ c'.stats = c.stats ∧ canonAux c'.nested = canonAux c.nested := by
  obtain ⟨c', hb', hmem, hcl, hbl, hst⟩ := canonBlock_separate hnd hwf h hc h'
  refine ⟨c', hb', hmem, hcl, hbl, hst, ?_⟩
  have hc' : c' ∈ b'.components := by rw [hb']; simp
  obtain ⟨n0, hn0, e0⟩ := canonBlock_canonAux h hc
  obtain ⟨n0', hn0', e0'⟩ := canonBlock_canonAux h' hc'
  rw [e0, e0']
  rw [hcl] at hn0'
  exact ComponentCoreProof.componentNested_canonAux hr hn0' hn0

/-- Actual production corollary. The accepted full Except equality supplies
its own source protection functions; no new premise is requested. -/
theorem canonBlock_source_member_order_nested {rules : Rules} (hseed : rules.seed = .byNameHash)
    (hr : rules.nested = .discovery) {env : Ix.Compile.Canon.Env} {all all' : Array Name}
    (hp : all.toList.Perm all'.toList) (hnd : NodupB (Ix.CompileCert.Canon.nodesOf env all)) (hwf : Ix.CompileCert.Canon.EnvWF env all)
    {b b' : BlockCanon} (h : Ix.Compile.Canon.canonBlock rules env all = .ok b) (h' : Ix.Compile.Canon.canonBlock rules env all' = .ok b') :
    ∀ c ∈ b.components, ∃ c' ∈ b'.components, c.members.toList.Perm c'.members.toList ∧
      c'.classes = c.classes ∧ c'.blindClasses = c.blindClasses ∧ c'.stats = c.stats ∧
      canonAux c'.nested = canonAux c.nested := by
  rw [ComponentCoreProof.canonBlock_eq_core] at h h'
  have nodes : NodupB (CallbackGraph.nodesOf (env.asCore) all) := by
    rw [CallbackGraph.nodesOf_source_eq]
    exact hnd
  have wellFormed : CallbackGraph.EnvWF (env.asCore) all :=
    (CallbackGraph.EnvWF_source_iff env all).2 hwf
  exact canonBlock_member_order_nested hseed hr hp nodes wellFormed h h'

/-- Actual production corollary. The accepted full Except equality supplies
its own source protection functions; no new premise is requested. -/
theorem canonBlock_source_separate_nested {rules : Rules} (hr : rules.nested = .discovery) {env : Ix.Compile.Canon.Env}
    {all : Array Name} {b : BlockCanon} (hnd : NodupB (Ix.CompileCert.Canon.nodesOf env all)) (hwf : Ix.CompileCert.Canon.EnvWF env all)
    (h : Ix.Compile.Canon.canonBlock rules env all = .ok b) {c : ComponentCanon} (hc : c ∈ b.components)
    {b' : BlockCanon} (h' : Ix.Compile.Canon.canonBlock rules env c.members = .ok b') :
    ∃ c', b'.components = #[c'] ∧ c'.members = c.members ∧ c'.classes = c.classes ∧
      c'.blindClasses = c.blindClasses ∧ c'.stats = c.stats ∧ canonAux c'.nested = canonAux c.nested := by
  rw [ComponentCoreProof.canonBlock_eq_core] at h h'
  have nodes : NodupB (CallbackGraph.nodesOf (env.asCore) all) := by
    rw [CallbackGraph.nodesOf_source_eq]
    exact hnd
  have wellFormed : CallbackGraph.EnvWF (env.asCore) all :=
    (CallbackGraph.EnvWF_source_iff env all).2 hwf
  exact canonBlock_separate_nested hr nodes wellFormed h hc h'

end Ix.CompileCert.Canon.CallbackBlock
