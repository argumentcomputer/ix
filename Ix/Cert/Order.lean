import Ix.Cert.Statement
import Ix.Cert.Schedule
import Ix.Cert.RefsRead
import Ix.CompileCert.Canon.SccMain
import Ix.CompileCert.Canon.SccFuel

/-! # The compiled closure has an order (Route A, B4)

`IxonAccepts` (`Ix.Cert.Statement`) runs the certified entry over the
compiled closure in an order that meets `ClosureOrder`: each record once,
every address the closure reaches, and no record before one it references
(`RecordRef`). `compileReport` checks that no stored record is on a
reference cycle (`Ix.Cert.referenceCycle`: the stored records' reference
graph, `Ix.Cert.recordGraph`, through Pass 1's proved
`Ix.Compile.Canon.condensation`). This file proves that the check orders the
records, so such an order exists for every seed set:

* `parMap_eq`, `recordRefs_eq`: the graph's reading on tasks is the
  records' reading in order, and that is their decoding's references and
  owner (`Ix.Cert.RefsRead.storedRefs_eq`: the reader skips the expressions);
* `recordGraph_edge`: a reference of a stored record that resolves to a
  stored record is an edge of the graph, between their positions in the
  store's keys;
* `singletons`: when the check passes, every component of the condensation
  is one record;
* `recordsOrdered_of_acyclic`: then the stored records, sorted by their
  component's position (`condensation_topo`: an edge never goes to a later
  component), list each record once with none before one it references
  (`RecordsOrdered`);
* `closureOrder_of_ordered`: ordered records give every seed set's closure a
  `ClosureOrder`: the reached addresses that are not stored (a projection's
  block left out of the store) first, as they reference nothing, then the
  closure's records in the records' order;
* **`closureOrder_exists`**: for a compiled artifact, from `compileReport`'s
  check (`checkReport_ok`). -/

namespace Ix.Cert.Order

/-- The stored records listed once each, no record before one it references. -/
def RecordsOrdered (ixe : Ixon.Env) : Prop :=
  ∃ L : List Address, L.Nodup ∧ (∀ a, a ∈ L ↔ ixe.consts.contains a = true) ∧
    L.Pairwise fun a b => ¬ RecordRef ixe a b

open Ix.CompileCert.Canon (Edge filt edge_filt)
open Ix.Cert.RefsRead (storedRefs_eq)

/-- The check's owner is the statement's (`ownerOf`). -/
theorem refOwner_eq (a : Address) (c : Ixon.Constant) : refOwner a c = ownerOf a c := rfl

/-- The check's stored record is the statement's (`recordAt`). -/
theorem storedRecord_eq (ixe : Ixon.Env) (a : Address) : storedRecord ixe a = recordAt ixe a := rfl

section
variable (ixe : Ixon.Env)

/-- A stored record's address is a key of the store. -/
theorem mem_keys_of_stored {a : Address} {c : Ixon.Constant} (h : storedRecord ixe a = some c) :
    a ∈ ixe.consts.keys := by
  rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains, Std.HashMap.contains_eq_isSome_getElem?]
  unfold storedRecord at h
  rw [Std.HashMap.get?_eq_getElem?] at h
  cases e : ixe.consts[a]? with
  | none => rw [e] at h; cases h
  | some _ => rfl

/-- `recordGraph`'s index map sends a key to its position among the keys. -/
theorem index_mem {a : Address} (ha : a ∈ ixe.consts.keys) :
    (Std.HashMap.ofList ixe.consts.keys.zipIdx).get? a = some (ixe.consts.keys.idxOf a) := by
  rw [Std.HashMap.get?_eq_getElem?]
  apply Std.HashMap.getElem?_ofList_of_mem (k := a) (beq_self_eq_true a)
  · have := Std.HashMap.distinct_keys (m := ixe.consts)
    rw [← List.zipIdx_map_fst 0 ixe.consts.keys] at this
    exact List.pairwise_map.1 this
  · rw [List.mem_zipIdx_iff_getElem?]
    exact List.getElem?_eq_some_iff.2 ⟨List.idxOf_lt_length_iff.2 ha, List.getElem_idxOf _⟩

/-- **`parMap` is `Array.map`**, whatever the tasks: `(Task.spawn f).get =
f ()`, and the chunks cover the array (`Ix.Cert.Schedule.slices_map`). -/
theorem parMap_eq {α β : Type} (f : α → β) (xs : Array α) : parMap f xs = xs.map f := by
  unfold parMap
  simp only [Array.map_map, Function.comp_def]
  exact Ix.Cert.Schedule.slices_map _ xs _ _
    (Ix.Cert.Schedule.chunks_cover xs.size recordTasks (by decide))

/-- **`recordRefs` reads each record once, in order**, whatever the tasks. -/
theorem recordRefs_eq (addrs : Array Address) :
    recordRefs (addrs.map fun a => (a, ixe.consts.get? a)) = addrs.map (storedRefs ixe) := by
  simp only [recordRefs, parMap_eq, Array.map_map, Function.comp_def]
  rfl

/-- `recordGraph` has a node per key. -/
theorem recordGraph_size : (recordGraph ixe).2.size = ixe.consts.keys.length := by
  simp only [recordGraph, recordRefs_eq, parMap_eq, Array.size_map, List.size_toArray]

/-- A reference of the record at position `i` that resolves to a stored record is an
edge of `recordGraph`, to that record's position. -/
theorem recordGraph_edge {i : Nat} (hi : i < ixe.consts.keys.length) {c : Ixon.Constant}
    (hc : storedRecord ixe ixe.consts.keys[i] = some c) {r : Address} (hr : r ∈ c.refs)
    {cr : Ixon.Constant} (hcr : storedRecord ixe r = some cr)
    (hb : refOwner r cr ∈ ixe.consts.keys) :
    Edge (filt (recordGraph ixe).2) i (ixe.consts.keys.idxOf (refOwner r cr)) := by
  have hrk := mem_keys_of_stored ixe hcr
  rw [edge_filt, recordGraph_size]
  refine ⟨?_, List.idxOf_lt_length_iff.2 hb⟩
  simp only [recordGraph, recordRefs_eq, parMap_eq, storedRefs_eq, Array.getElem?_map,
    List.getElem?_toArray, List.getElem?_eq_getElem hi, Option.map_some, hc, Option.getD_some,
    Array.mem_filterMap]
  refine ⟨r, hr, ?_⟩
  have hj := List.idxOf_lt_length_iff.2 hrk
  simp only [index_mem ixe hrk, Option.bind_eq_bind, Option.pure_def, Option.bind_some,
    List.getElem?_eq_getElem hj, List.getElem_idxOf, Option.map_some, storedRefs_eq, hcr,
    Option.join_some, index_mem ixe hb]


/-- A successful reference check leaves only one-record components. -/
theorem singletons {ixe : Ixon.Env} (h : referenceCycle ixe = none) :
    ∃ C, Ix.Compile.Canon.condensation (recordGraph ixe).2 = some C ∧ ∀ c ∈ C.comps, c.size = 1 := by
  unfold referenceCycle at h
  generalize recordGraph ixe = G at h ⊢
  obtain ⟨addrs, adj⟩ := G
  simp only at h ⊢
  cases hc : Ix.Compile.Canon.condensation adj with
  | none => rw [hc] at h; cases h
  | some C =>
    rw [hc] at h
    refine ⟨C, rfl, fun c hcm => ?_⟩
    have := List.find?_eq_none.1 (Option.map_eq_none_iff.1 h) c (Array.mem_toList_iff.2 hcm)
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at this
    exact this.1

end

open Ix.CompileCert.Canon (condensation_cover condensation_unique condensation_topo) in
/-- A successful reference check orders the stored records. -/
theorem recordsOrdered_of_acyclic {ixe : Ixon.Env} (h : referenceCycle ixe = none) :
    RecordsOrdered ixe := by
  classical
  obtain ⟨C, hC, hone⟩ := singletons h
  let keys := ixe.consts.keys
  let comp : Nat → Nat := fun v =>
    if hv : ∃ k c, C.comps[k]? = some c ∧ v ∈ c then Classical.choose hv else 0
  have comp_spec : ∀ v < keys.length, ∃ c, C.comps[comp v]? = some c ∧ v ∈ c := by
    intro v hv
    have hv' : v < (recordGraph ixe).2.size := by rw [recordGraph_size]; exact hv
    obtain ⟨c, hcm, hvc⟩ := condensation_cover hC v hv'
    obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 hcm
    have ex : ∃ k c, C.comps[k]? = some c ∧ v ∈ c := ⟨k, c, hk, hvc⟩
    simp only [comp]
    split
    · exact Classical.choose_spec ‹_›
    · exact absurd ex ‹_›
  have lt : ∀ a b, a ∈ keys → b ∈ keys → RecordRef ixe a b →
      comp (keys.idxOf b) < comp (keys.idxOf a) := by
    intro a b ha hb ⟨c, hc, r, hr, cr, hcr, hown, hne⟩
    have hia := List.idxOf_lt_length_iff.2 ha
    have hib := List.idxOf_lt_length_iff.2 hb
    have hc' : storedRecord ixe keys[keys.idxOf a] = some c := by
      rw [List.getElem_idxOf]; exact hc
    have e := recordGraph_edge ixe hia hc' hr hcr (show ownerOf r cr ∈ keys by rw [hown]; exact hb)
    rw [refOwner_eq, hown] at e
    obtain ⟨ca, hka, hva⟩ := comp_spec _ hia
    obtain ⟨cb, hkb, hvb⟩ := comp_spec _ hib
    obtain ⟨k', c', hle, hk', hw⟩ := condensation_topo hC _ ca _ _ hka hva e
    have hk := condensation_unique hC _ _ _ _ _ hk' hkb hw hvb
    subst hk
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      rw [heq, hka] at hkb
      cases hkb
      have h1 := hone ca (Array.mem_of_getElem? hka)
      obtain ⟨i, hi, e1⟩ := Array.mem_iff_getElem.1 hva
      obtain ⟨j, hj, e2⟩ := Array.mem_iff_getElem.1 hvb
      have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst hi0 hj0
      have ga : keys[keys.idxOf a]? = some a := List.getElem?_eq_some_iff.2 ⟨hia, List.getElem_idxOf hia⟩
      have gb : keys[keys.idxOf b]? = some b := List.getElem?_eq_some_iff.2 ⟨hib, List.getElem_idxOf hib⟩
      rw [← e1, e2, gb] at ga
      exact hne (Option.some.inj ga)
  let rk : Address → Nat := fun a => comp (keys.idxOf a)
  have perm := List.mergeSort_perm keys fun a b => decide (rk a ≤ rk b)
  refine ⟨keys.mergeSort fun a b => decide (rk a ≤ rk b), perm.nodup_iff.2 Std.HashMap.nodup_keys,
    fun a => ?_, ?_⟩
  · rw [perm.mem_iff, Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains]
  · have sorted := List.pairwise_mergeSort (le := fun a b => decide (rk a ≤ rk b))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) keys
    refine sorted.imp_of_mem fun ha hb hab hr => ?_
    have := lt _ _ (perm.mem_iff.1 ha) (perm.mem_iff.1 hb) hr
    simp only [decide_eq_true_eq, rk] at hab
    omega

/-- The elements of a list that meet a predicate, each once. -/
theorem exists_nodup_filter (l : List Address) (P : Address → Prop) :
    ∃ N : List Address, N.Nodup ∧ ∀ a, a ∈ N ↔ a ∈ l ∧ P a := by
  classical
  induction l with
  | nil => exact ⟨[], List.nodup_nil, fun a => by simp⟩
  | cons x l ih =>
    obtain ⟨N, hN, hm⟩ := ih
    by_cases hx : P x ∧ x ∉ N
    · refine ⟨x :: N, List.nodup_cons.2 ⟨hx.2, hN⟩, fun a => ?_⟩
      simp only [List.mem_cons, hm]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Or.inl rfl, hx.1⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h1, h2⟩
    · refine ⟨N, hN, fun a => ?_⟩
      simp only [List.mem_cons, hm]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · have hxN : a ∈ N := by
            by_contra hn
            exact hx ⟨h2, hn⟩
          exact (hm a).1 hxN
        · exact ⟨h1, h2⟩

/-- Ordered stored records give every seed set's compiled closure an order:
the addresses the closure reaches but that are not stored (a projection's
block left out of the store) first, as they reference nothing, then the
closure's records in the records' order. -/
theorem closureOrder_of_ordered {ixe : Ixon.Env} (h : RecordsOrdered ixe) (S : Address → Prop) :
    ∃ order, ClosureOrder ixe S order := by
  classical
  obtain ⟨L, hL, hLm, hLo⟩ := h
  let owners := ixe.consts.keys.filterMap fun a => (recordAt ixe a).map (ownerOf a)
  obtain ⟨N, hN, hNm⟩ := exists_nodup_filter owners fun b =>
    CompiledReach ixe S b ∧ ixe.consts.contains b = false
  have noref : ∀ a b, ixe.consts.contains a = false → ¬ RecordRef ixe a b := by
    rintro a b ha ⟨c, hc, -⟩
    have := mem_keys_of_stored ixe hc
    rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains, ha] at this
    cases this
  refine ⟨N ++ L.filter fun a => decide (CompiledReach ixe S a), ?_, fun a => ?_, ?_⟩
  · refine List.nodup_append.2 ⟨hN, List.Pairwise.filter _ hL, fun a ha b hb e => ?_⟩
    subst e
    have h1 := ((hNm a).1 ha).2.2
    have h2 := (hLm a).1 (List.mem_filter.1 hb).1
    rw [h1] at h2
    cases h2
  · rw [List.mem_append, hNm, List.mem_filter, hLm]
    constructor
    · rintro (⟨-, hr, -⟩ | ⟨-, hr⟩)
      · exact hr
      · simpa using hr
    · intro hr
      cases hc : ixe.consts.contains a
      · left
        refine ⟨?_, hr, rfl⟩
        cases hr with
        | seed _ hs => rw [hc] at hs; cases hs
        | step _ he =>
          obtain ⟨c, hc', h⟩ := he
          rcases h with ⟨hown, -⟩ | ⟨-, hs⟩
          · exact List.mem_filterMap.2 ⟨_, mem_keys_of_stored ixe hc', by rw [hc', Option.map_some, hown]⟩
          · rw [hc] at hs; cases hs
      · right
        exact ⟨rfl, by simpa using hr⟩
  · refine List.pairwise_append.2 ⟨?_, List.Pairwise.filter _ hLo,
      fun a ha b _ => noref a b ((hNm a).1 ha).2.2⟩
    exact List.pairwise_of_forall_mem_list fun a ha b _ => noref a b ((hNm a).1 ha).2.2

/-- `compile` passed the reference check. -/
theorem acyclic_of_compile {env : Ix.Environment} {ixe : Ixon.Env}
    (compiled : compile env = .ok ixe) : referenceCycle ixe = none := by
  obtain ⟨_, h⟩ := compile_eq_ok.mp compiled
  exact (checkReport_ok (compileReport_ok h).2).2.2.1

/-- **The compiled records are ordered**: no record before one it references. -/
theorem recordsOrdered {env : Ix.Environment} {ixe : Ixon.Env}
    (compiled : compile env = .ok ixe) : RecordsOrdered ixe :=
  recordsOrdered_of_acyclic (acyclic_of_compile compiled)

/-- **B4: `ClosureOrder` exists** for every seed set of a compiled artifact. -/
theorem closureOrder_exists {env : Ix.Environment} {ixe : Ixon.Env}
    (compiled : compile env = .ok ixe) (S : Address → Prop) : ∃ order, ClosureOrder ixe S order :=
  closureOrder_of_ordered (recordsOrdered compiled) S

end Ix.Cert.Order
