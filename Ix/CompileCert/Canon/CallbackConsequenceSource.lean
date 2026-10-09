import Ix.CompileCert.Canon.CallbackConsequences
import Ix.CompileCert.Canon.CallbackClasses
import Ix.CompileCert.Canon.CallbackEvaporate

/-!
UNCOMPILED proof proposal. These consequences instantiate the generic driver
with the real source collector through complete Except-result equalities.
They retain the source-backed predicates and every original output condition.
No finite representation of an arbitrary callback is asserted in the reverse
direction. All original source-backed theorem bodies remain in their modules.
-/

namespace Ix.CompileCert.Canon.CallbackConsequenceSource

open Ix.Compile.Canon
open Ix (Name)

/-- Component existence and exact class/statistics transport need no second
successful-run hypothesis, even in the source specialization. -/
theorem canon_member_order_total {rules : Rules} (hseed : rules.seed = .byNameHash)
    {env : Env} {all all' : Array Name} {comps : Array (Array Name)}
    (hp : all.toList.Perm all'.toList) (hnd : NodupB (nodesOf env all))
    (hwf : EnvWF env all) (h : blockComponents env all = .ok comps) :
    ∃ comps', blockComponents env all' = .ok comps' ∧
      ∀ c ∈ comps, ∃ c' ∈ comps', c.toList.Perm c'.toList ∧
        ∀ r, classesOf rules env c = .ok r → classesOf rules env c' = .ok r := by
  have generic : ComponentCore.blockComponents (env.asCore) all =
      .ok comps := by
    rw [← ComponentCoreProof.blockComponents_eq_core]
    exact h
  obtain ⟨comps', returned, transport⟩ := CallbackGraph.canon_member_order_total hseed hp
    (env := env.asCore)
    hnd ((CallbackGraph.EnvWF_source_iff env all).2 hwf) generic
  refine ⟨comps', ?_, ?_⟩
  · rw [ComponentCoreProof.blockComponents_eq_core]
    exact returned
  · intro c hc
    obtain ⟨c', hc', perm, same⟩ := transport c hc
    refine ⟨c', hc', perm, fun r hr => ?_⟩
    rw [CallbackGraph.classesOf_source_eq] at hr ⊢
    exact same r hr

theorem canonBlock_scc {rules : Rules} {env : Env} {all : Array Name} {b : BlockCanon}
    (hnd : NodupB (nodesOf env all)) (h : canonBlock rules env all = .ok b)
    {m m' : Name} (hm : m ∈ all) (hm' : m' ∈ all) :
    (∃ c ∈ b.components, m ∈ c.members ∧ m' ∈ c.members) ↔
      NReach (NodeEdge (nodesOf env all) (refsOf env)) m m' ∧
        NReach (NodeEdge (nodesOf env all) (refsOf env)) m' m := by
  rw [ComponentCoreProof.canonBlock_eq_core] at h
  exact CallbackBlock.canonBlock_scc (env := env.asCore) hnd h hm hm'

theorem canonBlock_acyclic {rules : Rules} {env : Env} {all : Array Name} {b : BlockCanon}
    (hnd : NodupB (nodesOf env all)) (h : canonBlock rules env all = .ok b)
    {c c' : ComponentCanon} (hc : c ∈ b.components) (hc' : c' ∈ b.components)
    {m m' : Name} (hm : m ∈ c.members) (hm' : m' ∈ c'.members)
    (r1 : NReach (NodeEdge (nodesOf env all) (refsOf env)) m m')
    (r2 : NReach (NodeEdge (nodesOf env all) (refsOf env)) m' m) :
    c.members = c'.members := by
  rw [ComponentCoreProof.canonBlock_eq_core] at h
  exact CallbackBlock.canonBlock_acyclic (env := env.asCore)
    hnd h hc hc' hm hm' r1 r2

theorem canonBlock_coarsest {rules : Rules} (hpf : rules.portFixes = true) {env : Env}
    (hA : AddrCongr env.addr?) {all : Array Name} {b : BlockCanon}
    (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all)
    (h : canonBlock rules env all = .ok b) {c : ComponentCanon} (hc : c ∈ b.components) :
    ∃ cs F, c.members.toList.mapM (mutConstOf env) = .ok cs ∧ c.classes = classNames F ∧
      sortClasses rules env.addr? cs = .ok (F, c.stats) ∧
      Partition F cs ∧ Consistent rules env.addr? F ∧ Coarsest rules env.addr? cs F := by
  rw [ComponentCoreProof.canonBlock_eq_core] at h
  exact CallbackBlock.canonBlock_coarsest hpf (env := env.asCore) hA hnd
    ((CallbackGraph.EnvWF_source_iff env all).2 hwf) h hc

/-- The successful other-component expansion is exactly the production
expansion, with its actual source closure and selected group registry. -/
theorem claims_iff (env : Env) (rules : Rules) (all : Array Name)
    (here : Nat) (s : Sig) (e : Array (Array Name) × Nat) :
    CallbackEvaporate.Claims (env.protection)
      (env.asCore) rules all here s e ↔
        Claims env rules all here s e := by
  constructor
  · rintro ⟨different, mentions, x, expanded, matched⟩
    refine ⟨different, mentions, x, ?_, matched⟩
    exact expanded
  · rintro ⟨different, mentions, x, expanded, matched⟩
    refine ⟨different, mentions, x, ?_, matched⟩
    exact expanded

theorem claimedElsewhere_iff (env : Env) (rules : Rules) (all : Array Name)
    (comps : Array (Array (Array Name))) (here : Nat) (s : Sig) :
    CallbackEvaporate.ClaimedElsewhere (env.protection)
      (env.asCore) rules all comps here s ↔
        ClaimedElsewhere env rules all comps here s := by
  unfold CallbackEvaporate.ClaimedElsewhere ClaimedElsewhere
  simp only [claims_iff]

theorem targetOk_iff (env : Env) (s : Sig) :
    CallbackEvaporate.TargetOk (env.asCore) s ↔ TargetOk env s :=
  Iff.rfl

/-- All five conditions, including absence of a claim in any other component,
are the old predicates after the internally derived production specialization. -/
theorem evaporates_iff (env : Env) (rules : Rules) (all : Array Name)
    (comps : Array (Array (Array Name))) (here : Nat) (n : NestedCanon) (j : Nat) :
    CallbackEvaporate.Evaporates (env.protection)
      (env.asCore) rules all comps here n j ↔
        Evaporates env rules all comps here n j := by
  unfold CallbackEvaporate.Evaporates Evaporates
  simp only [claimedElsewhere_iff, targetOk_iff]
  rfl

theorem flagsInv_iff (env : Env) (rules : Rules) (all : Array Name)
    (comps : Array (Array (Array Name))) (here : Nat) (n : NestedCanon)
    (pre : List (Option Nat × Nat)) (flags : Array Bool) :
    CallbackEvaporate.FlagsInv (env.protection)
      (env.asCore) rules all comps here n pre flags ↔
        FlagsInv env rules all comps here n pre flags := by
  unfold CallbackEvaporate.FlagsInv FlagsInv
  simp only [evaporates_iff]

/-- The original complete source statement, obtained from the generic loop
proof, not from its field-preservation fragment alone. -/
theorem evaporate_spec {env : Env} {rules : Rules} {all : Array Name}
    {comps : Array (Array (Array Name))} {here : Nat} {n n' : NestedCanon}
    (h : evaporate env rules all comps here n = .ok n') :
    n'.source = n.source ∧ n'.canonClasses = n.canonClasses ∧ n'.canon = n.canon ∧
      n'.perm = n.perm ∧ n'.addrDecided = n.addrDecided ∧
      n'.evaporated.size = n.evaporated.size ∧
      ∀ j, n'.evaporated[j]? = some true ↔
        (n.evaporated[j]? = some true ∨
          (j < n.evaporated.size ∧ Evaporates env rules all comps here n j)) := by
  rw [ComponentCoreProof.evaporate_eq_core] at h
  obtain ⟨source, classes, sigs, perm, addr, size, flags⟩ :=
    CallbackEvaporate.evaporate_spec h
  refine ⟨source, classes, sigs, perm, addr, size, fun j => ?_⟩
  simpa only [evaporates_iff] using flags j

theorem canonBlock_evaporated {rules : Rules} (hr : rules.nested = .discovery)
    {env : Env} {all : Array Name} {b : BlockCanon}
    (h : canonBlock rules env all = .ok b)
    {c : ComponentCanon} (hc : c ∈ b.components) {n : NestedCanon}
    (hn : c.nested = some n) :
    ∃ i, n.evaporated.size = n.perm.size ∧
      ∀ j, n.evaporated[j]? = some true ↔
        (j < n.perm.size ∧ Evaporates env rules all (b.components.map (·.classes)) i n j) := by
  rw [ComponentCoreProof.canonBlock_eq_core] at h
  obtain ⟨i, size, flags⟩ := CallbackEvaporate.canonBlock_evaporated hr h hc hn
  refine ⟨i, size, fun j => ?_⟩
  simpa only [evaporates_iff] using flags j

theorem canonBlock_evaporated_perm {rules : Rules} (hr : rules.nested = .discovery)
    {env : Env} {all : Array Name} {b : BlockCanon}
    (h : canonBlock rules env all = .ok b)
    {c : ComponentCanon} (hc : c ∈ b.components) {n : NestedCanon}
    (hn : c.nested = some n) {j : Nat} (he : n.evaporated[j]? = some true) :
    n.perm[j]? = some none := by
  obtain ⟨i, _, flags⟩ := canonBlock_evaporated hr h hc hn
  exact ((flags j).1 he).2.1

end Ix.CompileCert.Canon.CallbackConsequenceSource
