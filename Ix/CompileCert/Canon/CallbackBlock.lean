import Ix.CompileCert.Canon.CallbackPublic
import Ix.CompileCert.Canon.Loop

/-!
UNCOMPILED additive callback-domain block proof. No existing public root or
runtime definition is changed. The complete first/second loop specification is
transported from the checked source-backed driver proof to the exact generic
driver. History is then carried through the actual nested/evaporation results.
All callbacks and both protection presentations remain unrestricted.
-/

namespace Ix.CompileCert.Canon.CallbackBlock

open Ix.Compile.Canon
open Ix (Name ConstantInfo MutConst)

/-- What `canonBlock` computes for the component `members` before its nested data. -/
structure FirstSpec (rules : Rules) (env : ComponentCore.Env) (members : Array Name) (c : ComponentCanon) : Prop where
  hmem : c.members = members
  hnone : c.nested = none
  hcls : ∃ cs F B, members.toList.mapM (ComponentCore.mutConstOf env) = .ok cs ∧
    sortClasses rules env.addr? cs = .ok (F, c.stats) ∧ c.classes = classNames F ∧
    sortClassesBlind rules cs = .ok B ∧ c.blindClasses = classNames B

/-- What `canonBlock` computes for one component: `FirstSpec`, then its nested data from
`componentNested` and `evaporate` (`classesAll`: every component's classes). -/
structure ComponentSpec (protect : ComponentCore.Protection) (rules : Rules) (env : ComponentCore.Env) (all : Array Name)
    (classesAll : Array (Array (Array Name))) (i : Nat) (members : Array Name) (c : ComponentCanon) :
    Prop where
  hmem : c.members = members
  hcls : ∃ cs F B, members.toList.mapM (ComponentCore.mutConstOf env) = .ok cs ∧
    sortClasses rules env.addr? cs = .ok (F, c.stats) ∧ c.classes = classNames F ∧
    sortClassesBlind rules cs = .ok B ∧ c.blindClasses = classNames B
  hnest : ∃ n0, ComponentCore.componentNested protect rules env all c.classes = .ok n0 ∧
    n0.mapM (ComponentCore.evaporate protect env rules all classesAll i) = .ok c.nested

/-- **`canonBlock`, component by component**: the block keeps `all`; its components are those of
`blockComponents`, in that order; each holds its members' classes (`sortClasses` of the members as
`mutConstOf` builds them), blind classes and statistics, and its nested data from
`componentNested` and `evaporate` against the components' classes. -/
theorem canonBlock_spec {rules : Rules} {protect : ComponentCore.Protection} {env : ComponentCore.Env} {all : Array Name} {b : BlockCanon}
    (h : ComponentCore.canonBlock protect rules env all = .ok b) :
    b.all = all ∧ ∃ comps, ComponentCore.blockComponents env all = .ok comps ∧
      b.components.size = comps.size ∧
      ∀ (i : Nat) (c : ComponentCanon), b.components[i]? = some c →
        ∃ members, comps[i]? = some members ∧
          ComponentSpec protect rules env all (b.components.map (·.classes)) i members c := by
  unfold ComponentCore.canonBlock at h
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
      c'.stats = x.1.stats ∧ ∃ n0, ComponentCore.componentNested protect rules env all x.1.classes = .ok n0 ∧
        n0.mapM (ComponentCore.evaporate protect env rules all (out.map (·.classes)) x.2) = .ok c'.nested)
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

/-- The spec of the component at a position, by membership. -/
theorem canonBlock_mem_spec {rules : Rules} {protect : ComponentCore.Protection} {env : ComponentCore.Env} {all : Array Name} {b : BlockCanon}
    (h : ComponentCore.canonBlock protect rules env all = .ok b) {c : ComponentCanon} (hc : c ∈ b.components) :
    ∃ i, ComponentSpec protect rules env all (b.components.map (·.classes)) i c.members c := by
  obtain ⟨-, comps, -, -, hspec⟩ := canonBlock_spec h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (Array.mem_toList_iff.2 hc)
  rw [Array.getElem?_toList] at hi
  obtain ⟨members, -, hs⟩ := hspec i c hi
  exact ⟨i, by have := hs.hmem; rw [this]; exact hs⟩

/-- Every emitted nested value is the result of the exact component expansion
followed by the exact evaporation call at its original component index. This is
a witness extracted from the real second loop, not a new caller assumption. -/
theorem canonBlock_nested_component {rules : Rules}
    {protect : ComponentCore.Protection} {env : ComponentCore.Env}
    {all : Array Name} {b : BlockCanon}
    (run : ComponentCore.canonBlock protect rules env all = .ok b)
    {component : ComponentCanon} (member : component ∈ b.components)
    {nested : NestedCanon} (hasNested : component.nested = some nested) :
    ∃ (i : Nat) (before : NestedCanon),
      ComponentCore.componentNested protect rules env all component.classes = .ok (some before) ∧
      ComponentCore.evaporate protect env rules all (b.components.map (·.classes)) i before =
        .ok nested := by
  obtain ⟨i, spec⟩ := canonBlock_mem_spec run member
  obtain ⟨initial, expanded, evaporated⟩ := spec.hnest
  rw [hasNested] at evaporated
  cases initial with
  | none => cases except_pure_ok evaporated
  | some before =>
    obtain ⟨after, result, returned⟩ := except_bind_ok.1 evaporated
    have same := except_pure_ok returned
    simp only [Option.some.injEq] at same
    subst same
    exact ⟨i, before, expanded, result⟩

/-- The original canonical-auxiliary conclusion over the unrestricted generic
component environment and protection functions. Evaporation cannot alter it. -/
theorem canonBlock_canonAux {rules : Rules}
    {protect : ComponentCore.Protection} {env : ComponentCore.Env}
    {all : Array Name} {b : BlockCanon}
    (run : ComponentCore.canonBlock protect rules env all = .ok b)
    {component : ComponentCanon} (member : component ∈ b.components) :
    ∃ initial, ComponentCore.componentNested protect rules env all component.classes = .ok initial ∧
      canonAux component.nested = canonAux initial := by
  obtain ⟨i, spec⟩ := canonBlock_mem_spec run member
  obtain ⟨initial, expanded, evaporated⟩ := spec.hnest
  exact ⟨initial, expanded, ComponentCoreProof.canonAux_evaporate evaporated⟩

/-- Discovery order, complete canonical signatures and address flag, with the
same successful-run premises as the old source-backed public conclusion. -/
theorem canonBlock_nested_discovery {rules : Rules} (discovery : rules.nested = .discovery)
    {protect : ComponentCore.Protection} {env : ComponentCore.Env}
    {all : Array Name} {b : BlockCanon}
    (run : ComponentCore.canonBlock protect rules env all = .ok b)
    {component : ComponentCanon} (member : component ∈ b.components)
    {nested : NestedCanon} (hasNested : component.nested = some nested) :
    ∃ x, ComponentCore.canonExpand protect rules env component.classes = .ok x ∧
      nested.canonClasses = x.aux.map (fun m => #[m.name]) ∧
      sigsInOrder x nested.canonClasses = .ok nested.canon ∧ nested.addrDecided = false := by
  obtain ⟨i, before, expanded, evaporated⟩ := canonBlock_nested_component run member hasNested
  obtain ⟨x, expansion, classesEq, signatures, addrFalse, -⟩ :=
    ComponentCoreProof.componentNested_some discovery expanded
  obtain ⟨-, classesPreserved, signaturesPreserved, -, addrPreserved⟩ :=
    ComponentCoreProof.evaporate_fields evaporated
  exact ⟨x, expansion, classesPreserved.trans classesEq,
    by rw [classesPreserved, signaturesPreserved]; exact signatures,
    addrPreserved.trans addrFalse⟩

/-- Actual allocation history is retained at the final block output. The
protected set is the exact fixed function consumed by this run, and the name
equations retain the actual pre-allocation state. No finite representation,
freshness, key law, lookup success or history witness is a caller premise. -/
theorem canonBlock_nested_history {rules : Rules} (discovery : rules.nested = .discovery)
    {protect : ComponentCore.Protection} {env : ComponentCore.Env}
    {all : Array Name} {b : BlockCanon}
    (run : ComponentCore.canonBlock protect rules env all = .ok b)
    {component : ComponentCanon} (member : component ∈ b.components)
    {nested : NestedCanon} (hasNested : component.nested = some nested) :
    ∃ x, ComponentCore.canonExpand protect rules env component.classes = .ok x ∧
      nested.canonClasses = x.aux.map (fun m => #[m.name]) ∧
      sigsInOrder x nested.canonClasses = .ok nested.canon ∧ nested.addrDecided = false ∧
      CallbackPublic.DiscoverySpec (protect.canonical (repsOf component.classes))
        env.ind? rules.dedup (repsOf component.classes) (aliasesOf component.classes)
        env.groupOf (some env.addr?) x ∧
      (∀ (i : Nat) (entry : XMember), x.types[i]? = some entry →
        entry.sourceOwner ∈ repsOf component.classes) ∧
      (∃ D : List Nat, D.length = x.aux.size ∧ D.Pairwise (· ≤ ·) ∧
        ∀ (k d : Nat), D[k]? = some d → d < x.nOriginals + k) := by
  obtain ⟨i, before, expanded, evaporated⟩ := canonBlock_nested_component run member hasNested
  obtain ⟨x, expansion, classesEq, signatures, history, owners, bounds⟩ :=
    CallbackPublic.componentNested_discovery discovery expanded
  obtain ⟨_, _, _, _, addrFalse, -⟩ :=
    ComponentCoreProof.componentNested_some discovery expanded
  obtain ⟨-, classesPreserved, signaturesPreserved, -, addrPreserved⟩ :=
    ComponentCoreProof.evaporate_fields evaporated
  exact ⟨x, expansion, classesPreserved.trans classesEq,
    by rw [classesPreserved, signaturesPreserved]; exact signatures,
    addrPreserved.trans addrFalse, history, owners, bounds⟩

/-- Production specializes the generic result using its actual lazy source
closure. The caller supplies neither protection data nor a closure-completeness
proof. The source and generic block results are related by the accepted full
Except equality, so no error branch is hidden by the specialization. -/
theorem canonBlock_source_nested_history {rules : Rules} (discovery : rules.nested = .discovery)
    {env : SourceEnv} {all : Array Name} {b : BlockCanon}
    (run : Ix.Compile.Canon.canonBlock rules (Env.ofSource env) all = .ok b)
    {component : ComponentCanon} (member : component ∈ b.components)
    {nested : NestedCanon} (hasNested : component.nested = some nested) :
    ∃ x, Ix.CompileCert.Canon.canonExpand rules (Env.ofSource env) component.classes = .ok x ∧
      nested.canonClasses = x.aux.map (fun m => #[m.name]) ∧
      sigsInOrder x nested.canonClasses = .ok nested.canon ∧ nested.addrDecided = false ∧
      CallbackPublic.DiscoverySpec
        (fun () => (sourceContext env.source (repsOf component.classes) env.groupOf.blocks).protectedNames)
        env.ind? rules.dedup (repsOf component.classes) (aliasesOf component.classes)
        env.groupOf.apply (some env.addr?) x ∧
      (∀ (i : Nat) (entry : XMember), x.types[i]? = some entry →
        entry.sourceOwner ∈ repsOf component.classes) ∧
      (∃ D : List Nat, D.length = x.aux.size ∧ D.Pairwise (· ≤ ·) ∧
        ∀ (k d : Nat), D[k]? = some d → d < x.nOriginals + k) := by
  rw [ComponentCoreProof.canonBlock_eq_core] at run
  obtain ⟨x, expanded, classesEq, signatures, addrFalse, history, owners, bounds⟩ :=
    canonBlock_nested_history discovery run member hasNested
  refine ⟨x, ?_, classesEq, signatures, addrFalse, history, owners, bounds⟩
  rw [ComponentCoreProof.canonExpand_eq_core]
  exact expanded

end Ix.CompileCert.Canon.CallbackBlock

