import IxVMRefinement.Subst.Inst

/-! # Context cuts: `ctx_trim`, `ctx_reachable`, `ctx_seek_cut`, `ctx_next_cut`, `ctx_close_cut`

The cut functions return counts (field elements), read only by `Lists::take`; `ctx_trim`
keeps the innermost entries of the context list (`Lists::take`), the whole list, or none, so
the result is a segment of the same ghost context ending at the same depth
(`TypesRep.take`). -/

namespace IxVM.Refinement.Core.SubstAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency (Bounded)

set_option linter.unusedVariables false

local macro "lt_calls" : term => `(by simp <;> omega)
local macro "sub_calls" : term => `(fun _ hx => by simp [hx])

theorem ktake {α : Type} {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R)
    {xs : List α} {l r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::take<&KernelTypes::KExprNode>» [l, .field n] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    ZMod.val n ≤ xs.length ∧ RepList kexprListEnum R h' (xs.take (ZMod.val n)) r := by
  have ev' : ObsFn W (Instance.mk "Lists::take" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      [l, .field n] h r h' cs := by
    rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev
  have hl' : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      R h xs l := by
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl
  have := Lib.Lists.take_spec hR ev' hl'
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at this
  exact this

theorem g_ctx_close_cut {κ : _root_.Address → KKey} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)} (ev : ObsFn W "KernelSubst::ctx_close_cut" args h r h' calls)
    (ih : GIH κ calls) : G.ctx_close_cut args h r h' calls := by
  intro rest l hargs bd
  subst hargs
  match Obs.«KernelSubst::ctx_close_cut».obs ev with
  | .n0 (he15 := hr) .. => exact ⟨0, hr⟩
  | .other_Nil (he41 := hr) .. => exact ⟨0, hr⟩
  | .other_Cons_n0 (ev76 := e1) (he121 := hr) (hc123 := hc) .. =>
    subst hc hr
    exact ih.get .ctx_next_cut lt_calls e1 _ rfl (bounded_sub sub_calls bd)
  | .other_Cons_n1 (op136 := op) .. => exact binop_field op

theorem g_ctx_next_cut {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)} (ev : ObsFn W "KernelSubst::ctx_next_cut" args h r h' calls) :
    G.ctx_next_cut args h r h' calls := by
  intro types hargs bd
  subst hargs
  match Obs.«KernelSubst::ctx_next_cut».obs ev with
  | .run (op33 := op) .. => exact binop_field op

theorem g_ctx_seek_cut {κ : _root_.Address → KKey} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)} (ev : ObsFn W "KernelSubst::ctx_seek_cut" args h r h' calls)
    (ih : GIH κ calls) : G.ctx_seek_cut args h r h' calls := by
  intro types need hargs bd
  subst hargs
  match Obs.«KernelSubst::ctx_seek_cut».obs ev with
  | .n0 (ev14 := e1) (he59 := hr) (hc61 := hc) .. =>
    subst hc hr
    exact ih.get .ctx_next_cut lt_calls e1 _ rfl (bounded_sub sub_calls bd)
  | .n1 (op74 := op) .. => exact binop_field op

theorem g_ctx_reachable {κ : _root_.Address → KKey} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)} (ev : ObsFn W "KernelSubst::ctx_reachable" args h r h' calls)
    (ih : GIH κ calls) : G.ctx_reachable args h r h' calls := by
  intro types base hargs bd
  subst hargs
  match Obs.«KernelSubst::ctx_reachable».obs ev with
  | .run (ev28 := e1) (hc66 := hc) .. =>
    subst hc
    exact ih.get .ctx_seek_cut lt_calls e1 _ _ rfl (bounded_sub sub_calls bd)

theorem g_ctx_trim (κ : _root_.Address → KKey) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::ctx_trim" args h r h' calls) (ih : GIH κ calls) :
    G.ctx_trim κ args h r h' calls := by
  rintro types base hargs bd Γ d ⟨ht, hs⟩
  subst hargs
  refine ⟨?_, hs⟩
  match Obs.«KernelSubst::ctx_trim».obs ev with
  | .n0 (he19 := hr) (hm18 := hm) .. =>
    subst hr hm
    exact .nil (by simp)
  | .other_n0 (he77 := hr) (he78 := he) (ev63 := e1) (ev42 := e2) .. =>
    subst hr he
    exact ht.mono (e1.heap_extends.trans e2.heap_extends)
  | .other_n1 (ev63 := e1) (ev42 := e2) (ev111 := e3) (ev90 := e4) (hc128 := hc) .. =>
    subst hc
    obtain ⟨x, rfl⟩ := ih.get .ctx_reachable lt_calls e3 _ _ rfl (bounded_sub sub_calls bd)
    have ext := (e1.heap_extends.trans e2.heap_extends).trans e3.heap_extends
    exact TypesRep.take (ht.mono ext) (fun xs hl =>
      ⟨_, (ktake (segEntryRep_heapMono₂ κ Γ) e4 hl).2⟩)

end IxVM.Refinement.Core.SubstAux
