import IxVMRefinement.Assembly.FamilyFold
import IxVMRefinement.Decl.Modeled

/-! # The advice records a modeled family's check validates

`check_family` runs `check_advice_records(rc, advice, Nil, wset)` on the advice addresses its
payload lists: each address not seen before is checked by `check_advice_record` and added to the
advice set `aset`, which the member checks then consult (`member_val`: a model is advice). This
module reads that walk without an oracle:

* `check_advice_records_walk`: the returned set reads the seen addresses and the listed ones
  (as `AddrMapAll`), and every listed address had its `check_advice_record` call among the
  walk's calls (`Typing.AdviceIn`).

Each advice record is a checked unit of its own (the fold variant installs it before its block,
`Typing.FamGraph.advEarlier`), so no install happens here. Provenance: the walk of
`check_advice_records_spec` (`Decl/Modeled.lean:921`) without `AdviceStepOracle`, `Ctx` or
`LoadFacts`. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Library Aiur.Library.List Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core

set_option linter.unusedVariables false

/-- A set of addresses read at a heap is read at every extension, its predicate weakened. -/
theorem addrSet_mono_imp {S T : Bytes.Address → Prop} {h₁ h₂ : Heap F} {t : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (himp : ∀ a, S a → T a)
    (ht : AddrMapAll addrMapEnum (fun _ a _ => S a) h₁ t) :
    AddrMapAll addrMapEnum (fun _ a _ => T a) h₂ t := by
  induction ht with
  | nil => exact .nil
  | node hk hP hl hr _ _ ihl ihr =>
    exact .node (Bytes.repAddressRef_heapMono₂ addrTy ext hk) (himp _ hP)
      (ext.loadValue_eq hl) (ext.loadValue_eq hr) ihl ihr

/-- **The advice walk**: from the listed advice addresses `advAs` and a seen set `seenSet`, the
returned set reads `seenSet ∪ advAs`, and every listed address had its `check_advice_record`
call among the calls. -/
theorem check_advice_records_walk {rc wset : SourceValue F} :
    ∀ (advAs : List Bytes.Address) (seenSet : Bytes.Address → Prop)
      {x_advice x_seen r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h advAs x_advice →
      AddrMapAll addrMapEnum (fun _ b _ => seenSet b) h x_seen →
      ObsFn W "KernelModeled::check_advice_records" [rc, x_advice, x_seen, wset] h r h' cs →
      AddrMapAll addrMapEnum (fun _ b _ => seenSet b ∨ b ∈ advAs) h' r ∧
      (∀ b ∈ advAs, Typing.AdviceIn cs (ixAddr b)) ∧
      Heap.Extends h h'
  | [], seenSet, x_advice, x_seen, r, h, h', cs, hadv_rep, hseen, ev => by
    match Obs.«KernelModeled::check_advice_records».obs ev with
    | .Nil (he21 := he21) (he22 := he22) .. =>
      rw [he21, he22]
      exact ⟨addrSet_mono_imp (Heap.Extends.refl h) (fun _ hp => Or.inl hp) hseen,
        (fun _ hb => nomatch hb), Heap.Extends.refl h⟩
    | .Cons (ld12 := ld12) .. =>
      obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hadv_rep ld12
      cases he
  | a :: rest, seenSet, x_advice, x_seen, r, h, h', cs, hadv_rep, hseen, ev => by
    match Obs.«KernelModeled::check_advice_records».obs ev with
    | .Nil (ld12 := ld12) .. =>
      cases Lib.rep_nil_of_load hadv_rep ld12
    | .Cons (x_a := x_a) (m_aiikskik := m55) (m90 := m90) (v143 := v143) (m160 := m160)
        (ld12 := ld12) (ev_mfihupbr := ev65) (heq_sefkntmx := heq88) (ev_xzbngsxs := ev65w)
        (heq_xyxoxrbw := heq88w) (ev102 := ev102) (ev170 := ev170) (ev140 := ev140)
        (hc201 := hc201) .. =>
      subst heq88 heq88w hc201
      obtain ⟨a', rest', heq_cons, ha_rep, hrest_rep⟩ := Lib.rep_cons_of_load hadv_rep ld12
      injection heq_cons with ha_eq hrest_eq
      subst ha_eq hrest_eq
      have ext_55 : Heap.Extends h m55 :=
        (ObsFn.heap_extends ev65).trans (ObsFn.heap_extends ev65w)
      have ext_90 : Heap.Extends h m90 := ext_55.trans (ObsFn.heap_extends ev102)
      have ext_160 : Heap.Extends m90 m160 := ObsFn.heap_extends ev170
      have ext_h_160 : Heap.Extends h m160 := ext_90.trans ext_160
      have hseen1 : AddrMapAll addrMapEnum (fun _ b _ => seenSet b ∨ b = a) m160 v143 :=
        rbtree_map_insert_field_addrMapAll
          (Bytes.repAddressRef_heapMono₂ addrTy ext_90 ha_rep)
          (addrSet_mono_imp ext_90 (fun _ hp => hp) hseen) ev170
      obtain ⟨hout, hall, ext_rest⟩ :=
        check_advice_records_walk rest (fun b => seenSet b ∨ b = a)
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_160 hrest_rep)
          hseen1 ev140
      refine ⟨addrSet_mono_imp (Heap.Extends.refl h') ?_ hout, ?_, ext_h_160.trans ext_rest⟩
      · intro b hb
        rcases hb with (hs | rfl) | hrm
        · exact Or.inl hs
        · exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem _ hrm)
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hrm
        · exact ⟨rc, x_a, x_seen, wset, m55, by simp,
            ⟨_, Bytes.repAddressRef_heapMono₂ addrTy ext_55 ha_rep, rfl⟩⟩
        · obtain ⟨rc', xa', seen', wset', hh, hmem, haddr⟩ := hall b hrm
          exact ⟨rc', xa', seen', wset', hh, by simp [hmem], haddr⟩

end IxVM.Refinement.Decl
