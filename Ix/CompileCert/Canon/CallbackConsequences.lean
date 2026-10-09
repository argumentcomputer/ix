import Ix.CompileCert.Canon.CallbackPresentations

/-!
Uncompiled next proof slice for the remaining public block consumers. These
are the original SCC, acyclic-condensation and coarsest-partition conclusions
over the actual callback-generic block driver. Every original hypothesis is
retained; no protection, allocation, representation or alignment premise is
added. This file is separate from the proposed header-migration candidate.
-/

namespace Ix.CompileCert.Canon.CallbackBlock

open Ix.Compile.Canon
open Ix (Name)

theorem canonBlock_scc {rules : Rules} {protect : ComponentCore.Protection}
    {env : ComponentCore.Env} {all : Array Name} {b : BlockCanon}
    (hnd : NodupB (CallbackGraph.nodesOf env all))
    (h : ComponentCore.canonBlock protect rules env all = .ok b) {m m' : Name}
    (hm : m ∈ all) (hm' : m' ∈ all) :
    (∃ c ∈ b.components, m ∈ c.members ∧ m' ∈ c.members) ↔
      NReach (NodeEdge (CallbackGraph.nodesOf env all) (CallbackGraph.refsOf env)) m m' ∧
        NReach (NodeEdge (CallbackGraph.nodesOf env all) (CallbackGraph.refsOf env)) m' m := by
  obtain ⟨comps,hcomps,hmap⟩ := canonBlock_comps h
  rw [← CallbackGraph.blockComponents_scc hnd hcomps hm hm',← hmap]
  constructor
  · rintro ⟨c,hc,h1,h2⟩
    exact ⟨c.members,Array.mem_map_of_mem hc,h1,h2⟩
  · rintro ⟨c,hc,h1,h2⟩
    obtain ⟨c',hc',rfl⟩ := Array.mem_map.1 hc
    exact ⟨c',hc',h1,h2⟩

theorem canonBlock_acyclic {rules : Rules} {protect : ComponentCore.Protection}
    {env : ComponentCore.Env} {all : Array Name} {b : BlockCanon}
    (hnd : NodupB (CallbackGraph.nodesOf env all))
    (h : ComponentCore.canonBlock protect rules env all = .ok b)
    {c c' : ComponentCanon} (hc : c ∈ b.components) (hc' : c' ∈ b.components)
    {m m' : Name} (hm : m ∈ c.members) (hm' : m' ∈ c'.members)
    (r1 : NReach (NodeEdge (CallbackGraph.nodesOf env all) (CallbackGraph.refsOf env)) m m')
    (r2 : NReach (NodeEdge (CallbackGraph.nodesOf env all) (CallbackGraph.refsOf env)) m' m) :
    c.members = c'.members := by
  obtain ⟨comps,hcomps,hmap⟩ := canonBlock_comps h
  have h1 : c.members ∈ comps := hmap ▸ Array.mem_map_of_mem hc
  have h2 : c'.members ∈ comps := hmap ▸ Array.mem_map_of_mem hc'
  have hmAll : m ∈ all :=
    Array.mem_toList_iff.1
      ((CallbackGraph.blockComponents_sub hcomps c.members h1).2.subset
        (Array.mem_toList_iff.2 hm))
  have hmAll' : m' ∈ all :=
    Array.mem_toList_iff.1
      ((CallbackGraph.blockComponents_sub hcomps c'.members h2).2.subset
        (Array.mem_toList_iff.2 hm'))
  obtain ⟨both,hasBoth,left,right⟩ :=
    (CallbackGraph.blockComponents_scc hnd hcomps hmAll hmAll').2 ⟨r1,r2⟩
  rw [CallbackGraph.blockComponents_unique hnd hcomps
    both hasBoth c.members h1 m left hm] at right
  exact CallbackGraph.blockComponents_unique hnd hcomps
    c.members h1 c'.members h2 m' right hm'

theorem canonBlock_coarsest {rules : Rules} (hpf : rules.portFixes = true)
    {protect : ComponentCore.Protection} {env : ComponentCore.Env}
    (hA : AddrCongr env.addr?) {all : Array Name} {b : BlockCanon}
    (hnd : NodupB (CallbackGraph.nodesOf env all)) (hwf : CallbackGraph.EnvWF env all)
    (h : ComponentCore.canonBlock protect rules env all = .ok b)
    {c : ComponentCanon} (hc : c ∈ b.components) :
    ∃ cs F, c.members.toList.mapM (ComponentCore.mutConstOf env) = .ok cs ∧
      c.classes = classNames F ∧ sortClasses rules env.addr? cs = .ok (F,c.stats) ∧
      Partition F cs ∧ Consistent rules env.addr? F ∧ Coarsest rules env.addr? cs F := by
  obtain ⟨i,spec⟩ := canonBlock_mem_spec h hc
  obtain ⟨cs,F,_,source,sorted,classes,_,_⟩ := spec.hcls
  have distinct := component_keys hnd hwf (canonBlock_members_sub h hc).2 source
  exact ⟨cs,F,source,classes,sorted,sortClasses_coarsest hpf hA distinct sorted⟩

end Ix.CompileCert.Canon.CallbackBlock
