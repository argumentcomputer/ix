import Ix.CompileCert.Canon.CallbackGraph

/-!
UNCOMPILED additive proof proposal. Class transport retains the complete
class/statistics result and the original node/name hypotheses. Component
termination is derived internally, not supplied as a second success premise.
All callbacks are arbitrary; this is not an expansion-totality theorem.
-/

namespace Ix.CompileCert.Canon.CallbackGraph

open Ix.Compile.Canon
open Ix (Name)

/-- What Pass 1 computes for one component (`canonBlock`, before the nested auxiliaries): the
members as `MutConst`s, then their classes in canonical order. -/
def classesOf (rules : Rules) (env : ComponentCore.Env) (members : Array Name) :
    Except String (List (List Ix.MutConst) × SortStats) := do
  let cs ← members.toList.mapM (ComponentCore.mutConstOf env)
  sortClasses rules env.addr? cs

/-- **Member order, at the level of the block** (Def 4.3, member reorder; §3.5 (iii)): under the
compiler's name-hash seed, a permuted block has the same components up to the order of their
members, and each component's classes (members, order, representatives, statistics) are the
same. -/
theorem canon_member_order {rules : Rules} (hseed : rules.seed = .byNameHash) {env : ComponentCore.Env}
    {all all' : Array Name} {comps comps' : Array (Array Name)} (hp : all.toList.Perm all'.toList)
    (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all) (h : ComponentCore.blockComponents env all = .ok comps)
    (h' : ComponentCore.blockComponents env all' = .ok comps') :
    ∀ c ∈ comps, ∃ c' ∈ comps', c.toList.Perm c'.toList ∧
      ∀ r, classesOf rules env c = .ok r → classesOf rules env c' = .ok r := by
  intro c hc
  obtain ⟨c', hc', pc⟩ := blockComponents_perm hp hnd h h' c hc
  refine ⟨c', hc', pc, fun r hr => ?_⟩
  obtain ⟨-, hsub⟩ := blockComponents_sub h c hc
  unfold classesOf at hr ⊢
  obtain ⟨ms, hms, hr⟩ := except_bind_ok.1 hr
  obtain ⟨ms', hms', pms⟩ := mapM_perm (ComponentCore.mutConstOf env) pc hms
  have hk : KeysDistinct ms := by
    unfold KeysDistinct
    rw [keys_mapM_mutConstOf hwf _ ms (fun n hn => Array.mem_toList_iff.1 (hsub.subset hn)) hms]
    have := nodupB_iff.1 (nodupB_sub hnd hsub)
    rwa [nodesOf_toList] at this
  rw [hms']
  show sortClasses rules env.addr? ms' = .ok r
  rw [← sortClasses_perm hseed env.addr? pms hk]
  exact hr

/-- **Member order, unconditionally**: under the name-hash seed, a permuted block has the same
components up to the order of their members, with the same classes. -/
theorem canon_member_order_total {rules : Rules} (hseed : rules.seed = .byNameHash) {env : ComponentCore.Env}
    {all all' : Array Name} {comps : Array (Array Name)} (hp : all.toList.Perm all'.toList)
    (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all) (h : ComponentCore.blockComponents env all = .ok comps) :
    ∃ comps', ComponentCore.blockComponents env all' = .ok comps' ∧ ∀ c ∈ comps, ∃ c' ∈ comps',
      c.toList.Perm c'.toList ∧ ∀ r, classesOf rules env c = .ok r → classesOf rules env c' = .ok r := by
  obtain ⟨comps', h'⟩ := blockComponents_ok env all'
  exact ⟨comps', h', canon_member_order hseed hp hnd hwf h h'⟩

/-- **The condensation of a block is acyclic**: members of two different components never reach
each other both ways, so reachability between components is antisymmetric. -/
theorem blockComponents_acyclic {env : ComponentCore.Env} {all : Array Name} {comps : Array (Array Name)}
    (hnd : NodupB (nodesOf env all)) (h : ComponentCore.blockComponents env all = .ok comps)
    {c c' : Array Name} (hc : c ∈ comps) (hc' : c' ∈ comps) {m m' : Name} (hm : m ∈ c) (hm' : m' ∈ c')
    (r1 : NReach (NodeEdge (nodesOf env all) (refsOf env)) m m')
    (r2 : NReach (NodeEdge (nodesOf env all) (refsOf env)) m' m) : c = c' := by
  have hmA : m ∈ all :=
    Array.mem_toList_iff.1 ((blockComponents_sub h c hc).2.subset (Array.mem_toList_iff.2 hm))
  have hmA' : m' ∈ all :=
    Array.mem_toList_iff.1 ((blockComponents_sub h c' hc').2.subset (Array.mem_toList_iff.2 hm'))
  obtain ⟨c'', hc'', h1, h2⟩ := (blockComponents_scc hnd h hmA hmA').2 ⟨r1, r2⟩
  rw [blockComponents_unique hnd h c'' hc'' c hc m h1 hm] at h2
  exact blockComponents_unique hnd h c hc c' hc' m' h2 hm'


/-- Exact full result of the source-backed class computation, including errors. -/
theorem classesOf_source_eq (rules : Rules) (env : Ix.Compile.Canon.Env)
    (members : Array Name) :
    Ix.CompileCert.Canon.classesOf rules env members =
      classesOf rules (env.asCore) members := by
  unfold Ix.CompileCert.Canon.classesOf classesOf
  rfl

end Ix.CompileCert.Canon.CallbackGraph
