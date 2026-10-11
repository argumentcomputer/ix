import Ix.CompileCert.Canon.SccFuel
import Ix.CompileCert.Canon.BlockComp

/-!
# M7 L1, the component computations always return

With `condensation_isSome` (`SccFuel.lean`): `sccsOf` always returns (`sccsOf_some`), so
`blockComponents` never fails (`blockComponents_ok`), and the block-level presentations hold
without assuming that the second computation returns (`canon_member_order_total`,
`blockComponents_separate_total`).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name)

theorem list_mapM_option_some {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, ∃ y, f x = some y) → ∃ l', l.mapM f = some l'
  | [], _ => ⟨[], rfl⟩
  | a :: as, h => by
    obtain ⟨b, hb⟩ := h a (List.mem_cons_self ..)
    obtain ⟨bs, hbs⟩ := list_mapM_option_some f as (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨b :: bs, ?_⟩
    rw [List.mapM_cons, hb, hbs]; rfl

theorem array_mapM_option_some {α β : Type} (f : α → Option β) (xs : Array α)
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  rw [Array.mapM_eq_mapM_toList]
  obtain ⟨l', hl⟩ := list_mapM_option_some f xs.toList (fun x hx => h x (Array.mem_toList_iff.1 hx))
  rw [hl]
  exact ⟨l'.toArray, rfl⟩

/-- **`sccsOf` always returns.** -/
theorem sccsOf_some (names : Array Name) (refs : Name → Std.HashSet Name) :
    ∃ cs, sccsOf names refs = some cs := by
  obtain ⟨C, hC⟩ := condensation_some (adjOf names refs)
  rw [sccsOf_eq]
  have ht : tarjan (adjOf names refs) = some C.comps := by unfold tarjan; rw [hC]; rfl
  rw [ht, Option.bind_some]
  have hn : (adjOf names refs).size = names.size := by simp [adjOf]
  apply array_mapM_option_some
  intro c hc
  apply array_mapM_option_some
  intro v hv
  have hv' : v < names.size := hn ▸ condensation_range hC c hc v hv
  exact ⟨names[v], Array.getElem?_eq_getElem hv'⟩

/-- **`blockComponents` never fails.** -/
theorem blockComponents_ok (env : Env) (all : Array Name) :
    ∃ comps, blockComponents env all = .ok comps := by
  obtain ⟨cs, hs⟩ := sccsOf_some (nodesOf env all) (refsOf env)
  rw [blockComponents_eq, hs]
  exact ⟨_, rfl⟩

/-- **Member order, unconditionally**: under the name-hash seed, a permuted block has the same
components up to the order of their members, with the same classes. -/
theorem canon_member_order_total {rules : Rules} (hseed : rules.seed = .byNameHash) {env : Env}
    {all all' : Array Name} {comps : Array (Array Name)} (hp : all.toList.Perm all'.toList)
    (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all) (h : blockComponents env all = .ok comps) :
    ∃ comps', blockComponents env all' = .ok comps' ∧ ∀ c ∈ comps, ∃ c' ∈ comps',
      c.toList.Perm c'.toList ∧ ∀ r, classesOf rules env c = .ok r → classesOf rules env c' = .ok r := by
  obtain ⟨comps', h'⟩ := blockComponents_ok env all'
  exact ⟨comps', h', canon_member_order hseed hp hnd hwf h h'⟩

/-- **Separate declaration, unconditionally**: a component declared on its own is that one
component. -/
theorem blockComponents_separate_total {env : Env} {all : Array Name} {comps : Array (Array Name)}
    (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all) (h : blockComponents env all = .ok comps)
    {c : Array Name} (hc : c ∈ comps) : blockComponents env c = .ok #[c] := by
  obtain ⟨comps_c, h'⟩ := blockComponents_ok env c
  rw [h', blockComponents_separate hnd hwf h hc h']

/-- **The condensation of a block is acyclic**: members of two different components never reach
each other both ways, so reachability between components is antisymmetric. -/
theorem blockComponents_acyclic {env : Env} {all : Array Name} {comps : Array (Array Name)}
    (hnd : NodupB (nodesOf env all)) (h : blockComponents env all = .ok comps)
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

end Ix.CompileCert.Canon
