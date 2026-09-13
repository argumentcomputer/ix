/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Claims

namespace Ix.Theory.Certified

open Model Model.SetTheory

universe u v
variable {β : Type u} [DecidableEq β]

theorem mem_outstanding {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {nodes : List (CheckedNode.{u,v} fuel signature store)} {ref : ConstRef β} :
    ref ∈ outstanding nodes ↔ ref ∈ nodeFrontiers nodes ∧ ref ∉ nodeSubjects nodes := by
  simp [outstanding]

theorem CheckedBatch.exact_subjects {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {inputs : List (ClaimNode β)}
    (batch : CheckedBatch.{u,v} fuel signature store inputs) :
    nodeSubjects batch.nodes = inputs.flatMap (·.subjects) := by
  have h := congrArg (fun nodes => nodes.flatMap (·.subjects)) batch.exactNodes
  simpa only [nodeSubjects, List.flatMap_map, Function.comp_def] using h

theorem CheckedBatch.exact_frontiers {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {inputs : List (ClaimNode β)}
    (batch : CheckedBatch.{u,v} fuel signature store inputs) :
    nodeFrontiers batch.nodes = inputs.flatMap (fun node => node.frontier.map (·.ref)) := by
  calc
    nodeFrontiers batch.nodes = batch.nodes.flatMap (fun node => node.input.frontier.map (·.ref)) := by
      exact congrArg (fun f => batch.nodes.flatMap f) (funext fun node => node.frontier_refs)
    _ = inputs.flatMap (fun node => node.frontier.map (·.ref)) := by
      simpa only [List.flatMap_map, Function.comp_def] using
        congrArg (fun nodes => nodes.flatMap (fun node => node.frontier.map (·.ref))) batch.exactNodes

theorem CheckedBatch.frontier_coverage {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {inputs : List (ClaimNode β)}
    (batch : CheckedBatch.{u,v} fuel signature store inputs) {ref : ConstRef β} :
    ref ∈ batch.receipt.frontier.refs ↔
      (∃ node ∈ inputs, ref ∈ node.frontier.map (·.ref)) ∧
      ¬ ∃ node ∈ inputs, ref ∈ node.subjects := by
  rw [batch.exactFrontier, mem_outstanding, batch.exact_subjects, batch.exact_frontiers]
  simp

/-- Conservative logical-use manifest, including every axiom admitted by a
leaf and by the final replay. Neither kind of use is structurally discharged. -/
def CheckedBatch.logicalUses {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {inputs : List (ClaimNode β)}
    (batch : CheckedBatch.{u,v} fuel signature store inputs) : List (ConstRef β) :=
  (logicalAxioms store batch.receipt.checked.result.entries ++
    batch.nodes.flatMap (fun node => logicalAxioms store node.receipt.checked.result.entries)).eraseDups

theorem CheckedBatch.leaf_axiom_retained {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {inputs : List (ClaimNode β)}
    (batch : CheckedBatch.{u,v} fuel signature store inputs)
    {node : CheckedNode.{u,v} fuel signature store} (hn : node ∈ batch.nodes) {ref : ConstRef β}
    (hr : ref ∈ logicalAxioms store node.receipt.checked.result.entries) :
    ref ∈ batch.logicalUses := by
  simp only [logicalUses, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨node, hn, hr⟩

theorem CheckedBatch.logicalUses_authorized {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {inputs : List (ClaimNode β)}
    (batch : CheckedBatch.{u,v} fuel signature store inputs) {ref : ConstRef β}
    (h : ref ∈ batch.logicalUses) :
    ∃ entry, Standard.EntrySource store ref entry ∨ Quotient.EntrySource store ref entry := by
  simp only [logicalUses, List.mem_eraseDups, List.mem_append, List.mem_flatMap] at h
  rcases h with h | ⟨node, _, h⟩
  · obtain ⟨entry, _, hs⟩ := batch.receipt.logical_axioms_authorized h
    exact ⟨entry, hs⟩
  · obtain ⟨entry, _, hs⟩ := node.receipt.logical_axioms_authorized h
    exact ⟨entry, hs⟩

/-- Every discharged dependency has a provider at a strictly earlier position;
only an explicit external frontier may lack such a provider. -/
theorem DependencyOrder.before {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {known : List (ConstRef β)} {nodes : List (CheckedNode.{u,v} fuel signature store)}
    (order : DependencyOrder known nodes) {index : Nat} {node : CheckedNode.{u,v} fuel signature store}
    (hn : nodes[index]? = some node) {ref : ConstRef β} (hr : ref ∈ node.receipt.frontier.refs) :
    ref ∈ known ∨ ∃ previous, previous < index ∧
      ∃ provider, nodes[previous]? = some provider ∧ ref ∈ provider.input.subjects := by
  induction order generalizing index with
  | nil => simp at hn
  | @cons known first rest available tail ih =>
    cases index with
    | zero =>
      cases Option.some.inj hn
      exact Or.inl (available ref hr)
    | succ index =>
      rcases ih hn with hk | ⟨previous, hp, provider, hs, ho⟩
      · rcases List.mem_append.mp hk with hk | hk
        · exact Or.inl hk
        · exact Or.inr ⟨0, Nat.zero_lt_succ _, first, rfl, hk⟩
      · exact Or.inr ⟨previous + 1, Nat.succ_lt_succ hp, provider, hs, ho⟩

theorem unique_subject_provider {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {nodes : List (CheckedNode.{u,v} fuel signature store)} (unique : (nodeSubjects nodes).Nodup)
    {i j : Nat} {a b : CheckedNode.{u,v} fuel signature store}
    (ha : nodes[i]? = some a) (hb : nodes[j]? = some b) {ref : ConstRef β}
    (hra : ref ∈ a.input.subjects) (hrb : ref ∈ b.input.subjects) : i = j := by
  have hp := (List.pairwise_flatMap.mp unique).2
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hj, hbj⟩ := List.getElem?_eq_some_iff.mp hb
  rcases Nat.lt_trichotomy i j with hij | he | hji
  · have h := List.pairwise_iff_getElem.mp hp i j hi hj hij
    rw [hai, hbj] at h
    exact False.elim (h ref hra ref hrb rfl)
  · exact he
  · have h := List.pairwise_iff_getElem.mp hp j i hj hi hji
    rw [hai, hbj] at h
    exact False.elim (h ref hrb ref hra rfl)

/-- The relation points from a supplying node to a consuming node. Its rank
is the actual checked schedule position, not a prover-supplied acyclicity flag. -/
def DependencyEdge {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    (nodes : List (CheckedNode.{u,v} fuel signature store)) (provider consumer : Nat) : Prop :=
  ∃ a b ref, nodes[provider]? = some a ∧ nodes[consumer]? = some b ∧
    ref ∈ a.input.subjects ∧ ref ∈ b.receipt.frontier.refs ∧
    ∀ previous, previous < provider → ∀ other, nodes[previous]? = some other → ref ∉ other.input.subjects

theorem first_subject_provider {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {nodes : List (CheckedNode.{u,v} fuel signature store)} {ref : ConstRef β}
    (h : ref ∈ nodeSubjects nodes) :
    ∃ index : Nat, ∃ node : CheckedNode.{u,v} fuel signature store,
      nodes[index]? = some node ∧ ref ∈ node.input.subjects ∧
      ∀ previous : Nat, previous < index → ∀ other : CheckedNode.{u,v} fuel signature store,
        nodes[previous]? = some other → ref ∉ other.input.subjects := by
  induction nodes with
  | nil => cases h
  | cons first rest ih =>
    by_cases hf : ref ∈ first.input.subjects
    · exact ⟨0, first, rfl, hf, fun previous hp => False.elim (Nat.not_lt_zero previous hp)⟩
    · have hr : ref ∈ nodeSubjects rest := (List.mem_append.mp h).resolve_left hf
      obtain ⟨index, node, hn, hs, least⟩ := ih hr
      refine ⟨index + 1, node, hn, hs, ?_⟩
      intro previous hp other ho
      cases previous with
      | zero => cases Option.some.inj ho; exact hf
      | succ previous => exact least previous (Nat.lt_of_succ_lt_succ hp) other ho

/-- Shared subjects choose their first checked provider. This supplies an
actual edge for every discharged frontier member, as opposed to merely
asserting that a separately supplied graph is acyclic. -/
theorem DependencyOrder.edge_for {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {known : List (ConstRef β)} {nodes : List (CheckedNode.{u,v} fuel signature store)}
    (order : DependencyOrder known nodes) {consumer : Nat}
    {node : CheckedNode.{u,v} fuel signature store} (hn : nodes[consumer]? = some node)
    {ref : ConstRef β} (hr : ref ∈ node.receipt.frontier.refs) :
    ref ∈ known ∨ ∃ provider, DependencyEdge nodes provider consumer := by
  rcases order.before hn hr with hk | ⟨previous, _, owner, ho, hs⟩
  · exact Or.inl hk
  · obtain ⟨index, first, hf, hr', least⟩ := first_subject_provider
      (List.mem_flatMap.mpr ⟨owner, List.mem_of_getElem? ho, hs⟩)
    exact Or.inr ⟨index, first, node, ref, hf, hn, hr', hr, least⟩

theorem DependencyOrder.rank {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {known : List (ConstRef β)} {nodes : List (CheckedNode.{u,v} fuel signature store)}
    (order : DependencyOrder known nodes)
    (external : ∀ ref ∈ known, ref ∉ nodeSubjects nodes) {provider consumer : Nat}
    (edge : DependencyEdge nodes provider consumer) : provider < consumer := by
  obtain ⟨a, b, ref, ha, hb, hra, hrb, first⟩ := edge
  rcases order.before hb hrb with hk | ⟨previous, hp, owner, ho, hr⟩
  · exact False.elim (external ref hk
      (List.mem_flatMap.mpr ⟨a, List.mem_of_getElem? ha, hra⟩))
  · by_cases h : provider < consumer
    · exact h
    · have earlier : previous < provider := Nat.lt_of_lt_of_le hp (Nat.le_of_not_gt h)
      exact False.elim (first previous earlier owner ho hr)

theorem CheckedBatch.external_disjoint {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {inputs : List (ClaimNode β)}
    (batch : CheckedBatch.{u,v} fuel signature store inputs) {ref : ConstRef β}
    (h : ref ∈ batch.receipt.frontier.refs ++ [signature.falseType, signature.falseElim]) :
    ref ∉ nodeSubjects batch.nodes := by
  intro hs
  rcases List.mem_append.mp h with hf | hp
  · exact (mem_outstanding.mp ((batch.exactFrontier ref).mp hf)).2 hs
  · have fresh := batch.receipt.fresh ref hs
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [batch.receipt.frontier.interface.present.1] at fresh; cases fresh
    · rcases List.mem_cons.mp hp with rfl | hp
      · rw [batch.receipt.frontier.interface.present.2] at fresh; cases fresh
      · cases hp

theorem CheckedBatch.acyclic {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {inputs : List (ClaimNode β)}
    (batch : CheckedBatch.{u,v} fuel signature store inputs) :
    WellFounded (DependencyEdge batch.nodes) :=
  Subrelation.wf
    (fun h => batch.order.rank (fun _ h => batch.external_disjoint h) h)
    Nat.lt_wfRel.wf

theorem CheckedBatch.no_circular_discharge {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {inputs : List (ClaimNode β)}
    (batch : CheckedBatch.{u,v} fuel signature store inputs) {a b : Nat}
    (ab : DependencyEdge batch.nodes a b) (ba : DependencyEdge batch.nodes b a) : False := by
  have hab := batch.order.rank (fun _ h => batch.external_disjoint h) ab
  have hba := batch.order.rank (fun _ h => batch.external_disjoint h) ba
  exact Nat.lt_asymm hab hba

/-- Composition retains the leaf sequence. Validation of any grouping runs
the same source-bound checker over that complete sequence. -/
def composeClaims (left right : List (ClaimNode β)) : List (ClaimNode β) := left ++ right

omit [DecidableEq β] in
theorem composeClaims_assoc (a b c : List (ClaimNode β)) :
    composeClaims (composeClaims a b) c = composeClaims a (composeClaims b c) :=
  List.append_assoc ..

theorem checkBatch?_assoc (fuel : Nat) (signature : PrimitiveSignature β) (store : Store β)
    (frontier : List (FrontierWitness β)) (a b c : List (ClaimNode β)) :
    acceptsBatch.{u,v} fuel signature store frontier (composeClaims (composeClaims a b) c) =
      acceptsBatch.{u,v} fuel signature store frontier (composeClaims a (composeClaims b c)) := by
  rw [composeClaims_assoc]

/-- Erasing structural obligations has no effect on the model's axiom-use
manifest. Every recorded axiom retains its exact realized source schema. -/
theorem CheckedBatch.logical_axioms_authorized {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {inputs : List (ClaimNode β)}
    (batch : CheckedBatch.{u,v} fuel signature store inputs) {ref : ConstRef β}
    (h : ref ∈ logicalAxioms store batch.receipt.checked.result.entries) :
    ∃ entry, batch.receipt.checked.result.entries ref = some entry ∧
      (Standard.EntrySource store ref entry ∨ Quotient.EntrySource store ref entry) :=
  batch.receipt.logical_axioms_authorized h

theorem CheckedBatch.no_False {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {inputs : List (ClaimNode β)}
    (batch : CheckedBatch.{u,v} fuel signature store inputs)
    (closed : batch.receipt.frontier.refs = []) {ref : ConstRef β}
    (subject : ref ∈ nodeSubjects batch.nodes)
    (type : store.type ref = some signature.falseExpr)
    (V : Type v) [SetTheory V] : False := by
  obtain ⟨constants, hM, subjects⟩ := batch.closed_has_model closed V
  obtain ⟨entry, _, hs, hm⟩ := subjects ref subject
  have he : entry.type.erase = .const signature.falseType [] :=
    Option.some.inj (hs.type.symm.trans type)
  have hc := AExpr.eq_const_of_erase_eq he
  have member := hm (List.replicate entry.universes 0) (by simp) (fun _ => empty)
  rw [hc] at member
  simp only [interp, List.map_nil, hM.falseValue] at member
  exact not_mem_empty _ member

end Ix.Theory.Certified
