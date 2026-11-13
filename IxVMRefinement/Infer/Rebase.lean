import IxVMRefinement.Infer.Basic
import IxC.Kernel.Rules.Transport

/-! # Inference after lowering the context

`KernelInfer::k_infer_rebase` infers a term with loose bound variables under the context list cut
to what it reads. The innermost `g` opened variables, where `g` is the smaller of the term's
smallest free index (`expr_glb`) and the list's length, do not occur in the term; the term is
lowered past them (`expr_lower`, the same image at depth `d - g`), inferred under the context
list without its first `g` entries (a segment of the same ghost context ending at `d - g`) and the
type lifted back (`expr_lift`, the same image at depth `d`). The derivation at depth `d - g` moves
to depth `d` by top weakening (`Infer.lift`, `IxC/Kernel/Rules/Transport.lean`): the subject and
the type are scoped below `d - g`, so the renaming fixes them, and the stored terms are closed
(`EnvFacts.storeClosed`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq Infer)

set_option linter.unusedVariables false

namespace InferBase

/-- Weakening the predicate an `IdxAll` asserts of every index. -/
theorem idxAll_imp {h : Heap F} {P Q : Nat → F → Prop} (hPQ : ∀ m i, P m i → Q m i) :
    ∀ {m : Nat} {p : SourceValue F}, Specs.Subst.IdxAll h P m p → Specs.Subst.IdxAll h Q m p := by
  intro m p hp
  induction hp with
  | bvar cell hP => exact .bvar cell (hPQ _ _ hP)
  | sort cell => exact .sort cell
  | const cell => exact .const cell
  | lit cell => exact .lit cell
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ iht ihb => exact .lam cell iht ihb
  | forallE cell _ _ iht ihb => exact .forallE cell iht ihb
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | proj cell _ ihe => exact .proj cell ihe

/-- **Dropping the innermost `k` entries of a segment** ending at `d` leaves a segment ending at
`d - k`. -/
theorem segEntries_drop (Γ : Nat → KExpr) :
    ∀ (k d n : Nat), k ≤ n → n ≤ d → (segEntries Γ d n).drop k = segEntries Γ (d - k) (n - k)
  | 0, d, n, _, _ => by simp
  | k + 1, d, n, hk, hn => by
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [segEntries_succ, List.drop_succ_cons, segEntries_drop Γ k d' n' (by omega) (by omega)]
    congr 1 <;> omega

theorem segEntries_length (Γ : Nat → KExpr) (d n : Nat) : (segEntries Γ d n).length = n := by
  simp [segEntries]

/-- `Lists::drop` on a context list. -/
theorem seg_drop {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {xs : List (Nat × KExpr)}
    {l r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [l, .field n] h r h' cs)
    (hl : RepList kexprListEnum (SegEntryRep κ Γ) h xs l) :
    ZMod.val n ≤ xs.length ∧
      RepList kexprListEnum (SegEntryRep κ Γ) h (xs.drop (ZMod.val n)) r ∧ h' = h := by
  have := Lib.Lists.drop_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    (R := SegEntryRep κ Γ) _ rfl
    (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at this
  exact this

end InferBase

open InferBase

/-- `KernelInfer::k_infer_rebase`: inference under the context lowered past the innermost opened
variables the term does not mention, moved back up by `Infer.lift`. -/
theorem k_infer_rebase_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::k_infer_rebase" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.k_infer_rebase c args h r h' calls := by
  intro rc e types base hargs good hrc d Γ htypes E hE
  subst hargs
  obtain ⟨n, hnd, hl⟩ := htypes.1.toRepList
  rcases Obs.«KernelInfer::k_infer_rebase».obs ev with
    ⟨m2, cs12, v15, v16, m18, cs26, m45, cs53, cs81, v86, m102, cs110, ev28, ev55, ev14, ev112,
      ev83, hc129⟩ |
    ⟨v1, m2, cs12, v15, v16, m18, cs26, m45, cs53, v134, m135, cs145, v149, v150, m159, cs167,
      m194, cs202, v205, v206, m208, cs216, cs254, ev28, ev55, ev14, hne130, ev169, ev218, op248,
      ev204, ev147, ev256, hc280⟩
  · -- nothing to lower: the core under the cut context list
    subst hc129
    obtain ⟨hm18, g0, rfl, -, -⟩ := ih.get (.subst .expr_glb) (by lt_calls) ev28 e 0 rfl
      (good.sub fun x hx => by simp [hx]) (by rw [ZMod.val_zero]; omega)
    rw [hm18] at ev55
    obtain ⟨hv16, hm45⟩ := SubstAux.klength ev55 hl
    rw [hm45, hv16] at ev14
    obtain ⟨hm2, -⟩ := ih.get (.subst .lbr_min) (by lt_calls) ev14 _ _ rfl
      (good.sub fun x hx => by simp [hx])
    rw [hm2] at ev112
    have htr := ih.get (.subst .ctx_trim) (by lt_calls) ev112 types base rfl
      (good.sub fun x hx => by simp [hx]) Γ d htypes
    have e1 := ObsFn.heap_extends ev112
    exact ih.get (.infer .k_infer_core) (by lt_calls) ev83 rc e v86 rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ htr E (Tm.mono e1 hE)
  · -- lower by `g`, infer at depth `d - g`, lift back
    subst hc280
    obtain ⟨hm18, g0, rfl, hg0, hglb⟩ := ih.get (.subst .expr_glb) (by lt_calls) ev28 e 0 rfl
      (good.sub fun x hx => by simp [hx]) (by rw [ZMod.val_zero]; omega)
    rw [hm18] at ev55
    obtain ⟨hv16, hm45⟩ := SubstAux.klength ev55 hl
    rw [hm45] at ev14
    rw [hv16, segEntries_length] at ev14
    have hb : n < 549755813888 := by
      have := RomBound.bounded_length_lt good.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [types], m18⟩) (p := types)
        (by simp) (by simp) (by rw [hm18]; exact hl)
      simpa [segEntries] using this
    obtain ⟨hm2, -, -, hmin⟩ := ih.get (.subst .lbr_min) (by lt_calls) ev14 (g0 : F) (n : F) rfl
      (good.sub fun x hx => by simp [hx])
    rw [hm2] at ev169
    rw [NatAux.val_natCast (n := g0) (by omega), NatAux.val_natCast (n := n) (by omega)] at hmin
    obtain ⟨gN, hv1, hgg, hgn⟩ : ∃ gN : Nat, v1 = .field (gN : F) ∧ gN ≤ g0 ∧ gN ≤ n := by
      by_cases hlt : g0 < n
      · exact ⟨g0, by rw [hmin, ite_eq_left hlt], le_refl _, by omega⟩
      · exact ⟨n, by rw [hmin, ite_eq_right hlt], by omega, le_refl _⟩
    subst hv1
    have hgv : ZMod.val (gN : F) = gN := NatAux.val_natCast (by omega)
    -- the lowered term: the same image at depth `d - gN`
    have hno0 := hglb d Γ E (by rw [ZMod.val_zero]; exact hE)
    rw [ZMod.val_zero] at hno0
    have hno : Specs.Subst.NoIdx h (ZMod.val (0 : F) - 0) (ZMod.val (0 : F) + gN) e := by
      rw [ZMod.val_zero]
      exact idxAll_imp (P := fun m i => ZMod.val i < 0 + m ∨ 0 + g0 + m ≤ ZMod.val i)
        (Q := fun m i => ZMod.val i < 0 - 0 + m ∨ 0 + gN + m ≤ ZMod.val i)
        (fun m i (hi : ZMod.val i < 0 + m ∨ 0 + g0 + m ≤ ZMod.val i) =>
          (by omega : ZMod.val i < 0 - 0 + m ∨ 0 + gN + m ≤ ZMod.val i)) hno0
    have hlow := ih.get (.subst .expr_lower) (by lt_calls) ev169 e (gN : F) 0 rfl
      (good.sub fun x hx => by simp [hx]) 0 gN (by rw [hgv]; omega) (Nat.zero_le _) d Γ E
      (by omega) (by rw [ZMod.val_zero]; exact hE) hno
    rw [ZMod.val_zero] at hlow
    have e1 := ObsFn.heap_extends ev169
    -- the context list without its first `gN` entries
    obtain ⟨-, hdrop, hm208⟩ := seg_drop ev218
      (RepLinkedList.mono (segEntryRep_heapMono₂ c.κ Γ) e1 hl)
    rw [hgv, segEntries_drop Γ gN d n hgn hnd] at hdrop
    rw [hm208] at ev204
    have hts : c.types Γ m159 (d - gN) v205 :=
      ⟨TypesRep.ofRepList (by omega) hdrop, fun j hj => htypes.2 j (by omega)⟩
    have htr := ih.get (.subst .ctx_trim) (by lt_calls) ev204 v205 v206 rfl
      (good.sub fun x hx => by simp [hx]) Γ (d - gN) hts
    have e2 := e1.trans (ObsFn.heap_extends ev204)
    obtain ⟨T', hT', hinf⟩ := ih.get (.infer .k_infer_core) (by lt_calls) ev147 rc v149 v150 rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e2 hrc) (d - gN) Γ htr E
      (Tm.mono (ObsFn.heap_extends ev204) hlow)
    -- the type, lifted back to depth `d`
    have hT0 : c.tmk (d - gN) Γ (ZMod.val (0 : F)) m135 T' v134 := by
      rw [ZMod.val_zero]; exact hT'
    have hlift := ih.get (.subst .expr_lift) (by lt_calls) ev256 v134 (gN : F) 0 rfl
      (good.sub fun x hx => by simp [hx]) (by rw [hgv]; omega) 0 gN (by rw [hgv]; omega)
      (d - gN) Γ T' hT0
    have hgd : gN ≤ d := by omega
    rw [Nat.sub_add_cancel hgd, ZMod.val_zero] at hlift
    -- the derivation, moved up by top weakening
    have hsE : E.wscopedB (d - gN) = true := Tm.wscopedB hts.2 hlow
    have hsT : T'.wscopedB (d - gN) = true := Tm.wscopedB hts.2 hT'
    have hup := Ix.Kernel.Rules.Infer.lift (Ix.Kernel.EnvExt.refl c.env) hc.env.storeClosed
      (g := gN) hinf
    rw [Ix.Kernel.Rules.renFV_lift_of_wscoped (p := d - gN) (g := gN) (le_refl _) hsE,
      Ix.Kernel.Rules.renFV_lift_of_wscoped (p := d - gN) (g := gN) (le_refl _) hsT,
      Nat.sub_add_cancel hgd] at hup
    exact ⟨T', hlift, hup⟩

end IxVM.Refinement.Core
