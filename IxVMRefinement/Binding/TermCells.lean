import IxVMRefinement.Decl.Common
import IxVMRefinement.Ingress.Cells

/-! # The cells of a heap term

The `Const` and `Proj` cells of a heap term (`Core.AddrIn`) are the addresses a change of keying
has to agree on (`Typing.TmCExact.rekey`). This file says where they come from in two cases that
an image of the term does not determine: the image forgets the type of a `let`, whose cells are
still cells of the term.

* `addrIn_none`, `addrIn_const_inv`, `addrIn_proj_inv`, `addrIn_app_inv`, `addrIn_lam_inv`,
  `addrIn_forall_inv`, `addrIn_let_inv`: a cell of a term at a pointer to a known cell.
* `AddrIn.mono'`, `TmExact.addrIn_back`: the cells of a term do not change when the heap grows.
* `kexpr_struct_eq_cells`: **two terms `KernelCheck::kexpr_struct_eq` finds equal have the
  same cells**: every cell of the first is a cell of the second. The check compares cell by
  cell, `let` cells included.
* `RawConvExpr.cells_of_twin`: **two conversions of one expression have the same cells**, up to
  the address they stand for.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core

/-! ## A cell of a term at a known cell -/

private theorem cell_args' {h : Heap F} {addr : Nat} {e n n' : String}
    {xs ys : List (SourceValue F)}
    (c₁ : h[addr]? = some (.construct e n xs)) (c₂ : h[addr]? = some (.construct e n' ys)) :
    n = n' ∧ xs = ys := by
  have := Option.some.inj (c₁.symm.trans c₂)
  injection this with _ hn hx
  exact ⟨hn, hx⟩

/-- A term cell with no address and no subterm has no cell below it. -/
theorem addrIn_none {h : Heap F} {addr : Nat} {c : String} {xs : List (SourceValue F)}
    {x : Bytes.Address} (cell : h[addr]? = some (.construct kexprEnum c xs))
    (hc : c ≠ "Const" ∧ c ≠ "Proj" ∧ c ≠ "App" ∧ c ≠ "Lam" ∧ c ≠ "Forall" ∧ c ≠ "Let")
    (hin : AddrIn h (.ptr (.enum kexprEnum) addr) x) : False := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
  cases hin with
  | const c' _ => exact h1 (cell_args' cell c').1
  | projHead c' _ => exact h2 (cell_args' cell c').1
  | projArg c' _ => exact h2 (cell_args' cell c').1
  | appFn c' _ => exact h3 (cell_args' cell c').1
  | appArg c' _ => exact h3 (cell_args' cell c').1
  | lamTy c' _ => exact h4 (cell_args' cell c').1
  | lamBody c' _ => exact h4 (cell_args' cell c').1
  | forallTy c' _ => exact h5 (cell_args' cell c').1
  | forallBody c' _ => exact h5 (cell_args' cell c').1
  | letTy c' _ => exact h6 (cell_args' cell c').1
  | letVal c' _ => exact h6 (cell_args' cell c').1
  | letBody c' _ => exact h6 (cell_args' cell c').1

private theorem list2_eq {α : Type} {a b c d : α} (h : [a, b] = [c, d]) : a = c ∧ b = d := by
  injection h with h1 h2
  injection h2 with h3 _
  exact ⟨h1, h3⟩

private theorem list3_eq {α : Type} {a b c d e f : α} (h : [a, b, c] = [d, e, f]) :
    a = d ∧ b = e ∧ c = f := by
  injection h with h1 h2
  injection h2 with h3 h4
  injection h4 with h5 _
  exact ⟨h1, h3, h5⟩

theorem addrIn_const_inv {h : Heap F} {addr : Nat} {ap lsp : SourceValue F}
    {x : Bytes.Address} (cell : h[addr]? = some (.construct kexprEnum "Const" [ap, lsp]))
    (hin : AddrIn h (.ptr (.enum kexprEnum) addr) x) : Bytes.RepAddressRef addrTy h x ap := by
  cases hin with
  | const c' ra =>
    obtain ⟨-, hxs⟩ := cell_args' cell c'
    rw [(list2_eq hxs).1]
    exact ra
  | _ => rename_i c' _; exact absurd (cell_args' cell c').1 (by decide)

theorem addrIn_proj_inv {h : Heap F} {addr : Nat} {ap fv ep : SourceValue F}
    {x : Bytes.Address} (cell : h[addr]? = some (.construct kexprEnum "Proj" [ap, fv, ep]))
    (hin : AddrIn h (.ptr (.enum kexprEnum) addr) x) :
    Bytes.RepAddressRef addrTy h x ap ∨ AddrIn h ep x := by
  cases hin with
  | projHead c' ra =>
    obtain ⟨-, hxs⟩ := cell_args' cell c'
    rw [(list3_eq hxs).1]
    exact .inl ra
  | projArg c' sub =>
    obtain ⟨-, hxs⟩ := cell_args' cell c'
    rw [(list3_eq hxs).2.2]
    exact .inr sub
  | _ => rename_i c' _; exact absurd (cell_args' cell c').1 (by decide)

theorem addrIn_app_inv {h : Heap F} {addr : Nat} {fp ap : SourceValue F}
    {x : Bytes.Address} (cell : h[addr]? = some (.construct kexprEnum "App" [fp, ap]))
    (hin : AddrIn h (.ptr (.enum kexprEnum) addr) x) : AddrIn h fp x ∨ AddrIn h ap x := by
  cases hin with
  | appFn c' sub =>
    obtain ⟨-, hxs⟩ := cell_args' cell c'
    rw [(list2_eq hxs).1]
    exact .inl sub
  | appArg c' sub =>
    obtain ⟨-, hxs⟩ := cell_args' cell c'
    rw [(list2_eq hxs).2]
    exact .inr sub
  | _ => rename_i c' _; exact absurd (cell_args' cell c').1 (by decide)

theorem addrIn_lam_inv {h : Heap F} {addr : Nat} {tp bp lp : SourceValue F}
    {x : Bytes.Address} (cell : h[addr]? = some (.construct kexprEnum "Lam" [tp, bp, lp]))
    (hin : AddrIn h (.ptr (.enum kexprEnum) addr) x) : AddrIn h tp x ∨ AddrIn h bp x := by
  cases hin with
  | lamTy c' sub =>
    obtain ⟨-, hxs⟩ := cell_args' cell c'
    rw [(list3_eq hxs).1]
    exact .inl sub
  | lamBody c' sub =>
    obtain ⟨-, hxs⟩ := cell_args' cell c'
    rw [(list3_eq hxs).2.1]
    exact .inr sub
  | _ => rename_i c' _; exact absurd (cell_args' cell c').1 (by decide)

theorem addrIn_forall_inv {h : Heap F} {addr : Nat} {tp bp lp : SourceValue F}
    {x : Bytes.Address} (cell : h[addr]? = some (.construct kexprEnum "Forall" [tp, bp, lp]))
    (hin : AddrIn h (.ptr (.enum kexprEnum) addr) x) : AddrIn h tp x ∨ AddrIn h bp x := by
  cases hin with
  | forallTy c' sub =>
    obtain ⟨-, hxs⟩ := cell_args' cell c'
    rw [(list3_eq hxs).1]
    exact .inl sub
  | forallBody c' sub =>
    obtain ⟨-, hxs⟩ := cell_args' cell c'
    rw [(list3_eq hxs).2.1]
    exact .inr sub
  | _ => rename_i c' _; exact absurd (cell_args' cell c').1 (by decide)

theorem addrIn_let_inv {h : Heap F} {addr : Nat} {tp vp bp : SourceValue F}
    {x : Bytes.Address} (cell : h[addr]? = some (.construct kexprEnum "Let" [tp, vp, bp]))
    (hin : AddrIn h (.ptr (.enum kexprEnum) addr) x) :
    AddrIn h tp x ∨ AddrIn h vp x ∨ AddrIn h bp x := by
  cases hin with
  | letTy c' sub =>
    obtain ⟨-, hxs⟩ := cell_args' cell c'
    rw [(list3_eq hxs).1]
    exact .inl sub
  | letVal c' sub =>
    obtain ⟨-, hxs⟩ := cell_args' cell c'
    rw [(list3_eq hxs).2.1]
    exact .inr (.inl sub)
  | letBody c' sub =>
    obtain ⟨-, hxs⟩ := cell_args' cell c'
    rw [(list3_eq hxs).2.2]
    exact .inr (.inr sub)
  | _ => rename_i c' _; exact absurd (cell_args' cell c').1 (by decide)

/-! ## The cells do not change when the heap grows -/

theorem AddrIn.mono' {h h' : Heap F} (ext : Heap.Extends h h') {p : SourceValue F}
    {x : Bytes.Address} (hin : AddrIn h p x) : AddrIn h' p x := by
  induction hin with
  | const cell ra =>
    exact .const (ext.getElem?_eq cell) (Bytes.repAddressRef_heapMono₂ addrTy ext ra)
  | projHead cell ra =>
    exact .projHead (ext.getElem?_eq cell) (Bytes.repAddressRef_heapMono₂ addrTy ext ra)
  | projArg cell _ ih => exact .projArg (ext.getElem?_eq cell) ih
  | appFn cell _ ih => exact .appFn (ext.getElem?_eq cell) ih
  | appArg cell _ ih => exact .appArg (ext.getElem?_eq cell) ih
  | lamTy cell _ ih => exact .lamTy (ext.getElem?_eq cell) ih
  | lamBody cell _ ih => exact .lamBody (ext.getElem?_eq cell) ih
  | forallTy cell _ ih => exact .forallTy (ext.getElem?_eq cell) ih
  | forallBody cell _ ih => exact .forallBody (ext.getElem?_eq cell) ih
  | letTy cell _ ih => exact .letTy (ext.getElem?_eq cell) ih
  | letVal cell _ ih => exact .letVal (ext.getElem?_eq cell) ih
  | letBody cell _ ih => exact .letBody (ext.getElem?_eq cell) ih

private theorem addr_eq_of_rep {h h' : Heap F} (ext : Heap.Extends h h') {a x : Bytes.Address}
    {ap : SourceValue F} (ra : Bytes.RepAddressRef addrTy h a ap)
    (hx : Bytes.RepAddressRef addrTy h' x ap) : a = x :=
  Bytes.repAddressRef_inj U32.Goldilocks.compatible
    (Bytes.repAddressRef_heapMono₂ addrTy ext ra) hx

/-- **A cell of a represented term over a grown heap is a cell over the first heap.** -/
theorem TmExact.addrIn_back {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h h' : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F}
    (rep : Decl.TmExact κ d Γ h k E p) (ext : Heap.Extends h h') :
    ∀ x, AddrIn h' p x → AddrIn h p x := by
  induction rep with
  | bvarLocal cell =>
    intro x hin; exact (addrIn_none (ext.getElem?_eq cell) (by decide) hin).elim
  | bvarFree cell =>
    intro x hin; exact (addrIn_none (ext.getElem?_eq cell) (by decide) hin).elim
  | sort cell =>
    intro x hin; exact (addrIn_none (ext.getElem?_eq cell) (by decide) hin).elim
  | const cell ra rls =>
    intro x hin
    have e := addr_eq_of_rep ext ra (addrIn_const_inv (ext.getElem?_eq cell) hin)
    subst e
    exact .const cell ra
  | app cell _ _ ihf iha =>
    intro x hin
    rcases addrIn_app_inv (ext.getElem?_eq cell) hin with h1 | h1
    · exact .appFn cell (ihf x h1)
    · exact .appArg cell (iha x h1)
  | lam cell _ _ rl iht ihb =>
    intro x hin
    rcases addrIn_lam_inv (ext.getElem?_eq cell) hin with h1 | h1
    · exact .lamTy cell (iht x h1)
    · exact .lamBody cell (ihb x h1)
  | forallE cell _ _ rl iht ihb =>
    intro x hin
    rcases addrIn_forall_inv (ext.getElem?_eq cell) hin with h1 | h1
    · exact .forallTy cell (iht x h1)
    · exact .forallBody cell (ihb x h1)
  | letE cell _ _ _ iht ihv ihb =>
    intro x hin
    rcases addrIn_let_inv (ext.getElem?_eq cell) hin with h1 | h1 | h1
    · exact .letTy cell (iht x h1)
    · exact .letVal cell (ihv x h1)
    · exact .letBody cell (ihb x h1)
  | litNat cell =>
    intro x hin; exact (addrIn_none (ext.getElem?_eq cell) (by decide) hin).elim
  | litStr cell =>
    intro x hin; exact (addrIn_none (ext.getElem?_eq cell) (by decide) hin).elim
  | proj cell ra _ ih =>
    intro x hin
    rcases addrIn_proj_inv (ext.getElem?_eq cell) hin with h1 | h1
    · have e := addr_eq_of_rep ext ra h1
      subst e
      exact .projHead cell ra
    · exact .projArg cell (ih x h1)

private theorem cell_load {h : Heap F} {addr : Nat} {c : String} {xs : List (SourceValue F)}
    {v : SourceValue F} (cell : h[addr]? = some (.construct kexprEnum c xs))
    (hl : loadValue h (.ptr (.enum kexprEnum) addr) = .ok v) : h[addr]? = some v := by
  rw [loadValue_enum_cell cell] at hl
  injection hl with hv
  rw [← hv]
  exact cell

/-- A represented term is a pointer to the cell its load returns. -/
theorem TmExact.cell_of_load {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p v : SourceValue F}
    (rep : Decl.TmExact κ d Γ h k E p) (hl : loadValue h p = .ok v) :
    ∃ addr, p = .ptr (.enum kexprEnum) addr ∧ h[addr]? = some v := by
  cases rep with
  | bvarLocal cell => exact ⟨_, rfl, cell_load cell hl⟩
  | bvarFree cell => exact ⟨_, rfl, cell_load cell hl⟩
  | sort cell => exact ⟨_, rfl, cell_load cell hl⟩
  | const cell => exact ⟨_, rfl, cell_load cell hl⟩
  | app cell => exact ⟨_, rfl, cell_load cell hl⟩
  | lam cell => exact ⟨_, rfl, cell_load cell hl⟩
  | forallE cell => exact ⟨_, rfl, cell_load cell hl⟩
  | letE cell => exact ⟨_, rfl, cell_load cell hl⟩
  | litNat cell => exact ⟨_, rfl, cell_load cell hl⟩
  | litStr cell => exact ⟨_, rfl, cell_load cell hl⟩
  | proj cell => exact ⟨_, rfl, cell_load cell hl⟩

/-! ## Two terms `kexpr_struct_eq` finds equal -/

local macro "cells_lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

private theorem struct_eq_cells_aux {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → r = .field 1 →
      ((fname = "KernelCheck::kexpr_struct_eq" →
        ∀ (k : Nat) (Ea Eb : KExpr) (pa pb : SourceValue F),
          args = [pa, pb] → Decl.TmExact κ d Γ h k Ea pa → Decl.TmExact κ d Γ h k Eb pb →
          ∀ x, AddrIn h pa x → AddrIn h pb x) ∧
       (fname = "KernelCheck::kexpr_binder_struct_eq" →
        ∀ (k : Nat) (Ta Ba Tb Bb : KExpr) (pta pba pla ptb pbb plb : SourceValue F),
          args = [pta, pba, pla, ptb, pbb, plb] →
          Decl.TmExact κ d Γ h k Ta pta → Decl.TmExact κ d Γ h (k + 1) Ba pba →
          Decl.TmExact κ d Γ h k Tb ptb → Decl.TmExact κ d Γ h (k + 1) Bb pbb →
          (∀ x, AddrIn h pta x → AddrIn h ptb x) ∧ (∀ x, AddrIn h pba x → AddrIn h pbb x))) :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => r = .field 1 →
      ((fname = "KernelCheck::kexpr_struct_eq" →
        ∀ (k : Nat) (Ea Eb : KExpr) (pa pb : SourceValue F),
          args = [pa, pb] → Decl.TmExact κ d Γ h k Ea pa → Decl.TmExact κ d Γ h k Eb pb →
          ∀ x, AddrIn h pa x → AddrIn h pb x) ∧
       (fname = "KernelCheck::kexpr_binder_struct_eq" →
        ∀ (k : Nat) (Ta Ba Tb Bb : KExpr) (pta pba pla ptb pbb plb : SourceValue F),
          args = [pta, pba, pla, ptb, pbb, plb] →
          Decl.TmExact κ d Γ h k Ta pta → Decl.TmExact κ d Γ h (k + 1) Ba pba →
          Decl.TmExact κ d Γ h k Tb ptb → Decl.TmExact κ d Γ h (k + 1) Bb pbb →
          (∀ x, AddrIn h pta x → AddrIn h ptb x) ∧ (∀ x, AddrIn h pba x → AddrIn h pbb x))))
    (fun fname args h r h' cs ev ih hr => by
      subst hr
      refine ⟨fun hfn k Ea Eb pa pb hargs ha hb => ?_,
        fun hfn k Ta Ba Tb Bb pta pba pla ptb pbb plb hargs hta hba htb hbb => ?_⟩
      · subst hfn hargs
        rcases Obs.«KernelCheck::kexpr_struct_eq».obs ev with
          ⟨x_ia, x_ib, ld12, ld36, op65, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, he79, _, _⟩ |
          ⟨_, _, _, _, _, he86, _, _⟩ |
          ⟨x_la, x_lb, cs128, ld12, ld112, ev130, _⟩ |
          ⟨_, _, _, _, _, he152, _, _⟩ |
          ⟨x_ca, x_lsa, x_cb, x_lsb, m202, cs213, cs239, ld12, ld183, ev215, ev241, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, he263, _, _⟩ |
          ⟨_, _, _, _, _, _, he270, _, _⟩ |
          ⟨x_fa, x_aa, x_fb, x_ab, m320, cs331, cs357, ld12, ld301, ev333, ev359, hc376⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, he381, _, _⟩ |
          ⟨_, _, _, _, _, _, he388, _, _⟩ |
          ⟨x_ta, x_ba, x_la, x_tb, x_bb, x_lb, cs450, ld12, ld424, ev452, hc501⟩ |
          ⟨_, _, _, _, _, _, _, he506, _, _⟩ |
          ⟨x_da, x_xa, x_la, x_db, x_xb, x_lb, cs568, ld12, ld542, ev570, hc619⟩ |
          ⟨_, _, _, _, _, _, _, he624, _, _⟩ |
          ⟨x_ta, x_va, x_ba, x_tb, x_vb, x_bb, m684, cs695, m719, cs730, cs756,
            ld12, ld660, ev697, ev732, ev758, hc775⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he780, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he787, _, _⟩ |
          ⟨_, _, _, _, _, _, _, he794, _, _⟩ |
          ⟨x_la, x_lb, cs836, ld12, ld820, ev838, hc855⟩ |
          ⟨_, _, _, _, _, he860, _, _⟩ |
          ⟨x_sa, x_fa2, x_ea, x_sb, x_fb2, x_eb, m920, cs931, cs980,
            ld12, ld896, ev933, op970, ev982, hc999⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, he1004, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he1011, _, _⟩ |
          ⟨_, _, _, _, _, _, _, he1018, _, _⟩
        · obtain ⟨qa, rfl, cella⟩ := TmExact.cell_of_load ha ld12
          intro x hin
          exact (addrIn_none cella (by decide) hin).elim
        · exact absurd (Value.field.inj he79) one_ne_zero
        · exact absurd (Value.field.inj he86) one_ne_zero
        · obtain ⟨qa, rfl, cella⟩ := TmExact.cell_of_load ha ld12
          intro x hin
          exact (addrIn_none cella (by decide) hin).elim
        · exact absurd (Value.field.inj he152) one_ne_zero
        · obtain ⟨aa, lsa, -, hra, -⟩ := ha.const_of_load ld12
          obtain ⟨ab, lsb, -, hrb, -⟩ := hb.const_of_load ld183
          obtain ⟨haddr, rfl⟩ := Lib.address_eq_spec ev215 hra hrb
          have haeq : aa = ab := by
            by_cases hab : aa = ab
            · exact hab
            · rw [ite_eq_right hab] at haddr
              exact absurd (Value.field.inj haddr) one_ne_zero
          subst haeq
          obtain ⟨qa, rfl, cella⟩ := TmExact.cell_of_load ha ld12
          obtain ⟨qb, rfl, cellb⟩ := TmExact.cell_of_load hb ld183
          intro x hin
          have e := Bytes.repAddressRef_inj U32.Goldilocks.compatible hra
            (addrIn_const_inv cella hin)
          subst e
          exact .const cellb hrb
        · exact absurd (Value.field.inj he263) one_ne_zero
        · exact absurd (Value.field.inj he270) one_ne_zero
        · obtain ⟨Efa, Eaa, -, hfa, haa⟩ := ha.app_of_load ld12
          obtain ⟨Efb, Eab, -, hfb, hab⟩ := hb.app_of_load ld301
          obtain ⟨qa, rfl, cella⟩ := TmExact.cell_of_load ha ld12
          obtain ⟨qb, rfl, cellb⟩ := TmExact.cell_of_load hb ld301
          subst hc376
          have e1 := ObsFn.heap_extends ev333
          have hF := (ih _ _ _ _ _ _ (by cells_lt_calls) ev333 rfl).1 rfl k Efa Efb x_fa x_fb rfl
            hfa hfb
          have hA := (ih _ _ _ _ _ _ (by cells_lt_calls) ev359 rfl).1 rfl k Eaa Eab x_aa x_ab rfl
            (haa.mono e1) (hab.mono e1)
          intro x hin
          rcases addrIn_app_inv cella hin with h1 | h1
          · exact .appFn cellb (hF x h1)
          · exact .appArg cellb (TmExact.addrIn_back hab e1 x (hA x (AddrIn.mono' e1 h1)))
        · exact absurd (Value.field.inj he381) one_ne_zero
        · exact absurd (Value.field.inj he388) one_ne_zero
        · obtain ⟨Ta, Ba, ℓa, -, hta, hba, -⟩ := ha.lam_of_load ld12
          obtain ⟨Tb, Bb, ℓb, -, htb, hbb, -⟩ := hb.lam_of_load ld424
          obtain ⟨qa, rfl, cella⟩ := TmExact.cell_of_load ha ld12
          obtain ⟨qb, rfl, cellb⟩ := TmExact.cell_of_load hb ld424
          subst hc501
          obtain ⟨hT, hB⟩ := (ih _ _ _ _ _ _ (by cells_lt_calls) ev452 rfl).2 rfl k
            Ta Ba Tb Bb x_ta x_ba x_la x_tb x_bb x_lb rfl hta hba htb hbb
          intro x hin
          rcases addrIn_lam_inv cella hin with h1 | h1
          · exact .lamTy cellb (hT x h1)
          · exact .lamBody cellb (hB x h1)
        · exact absurd (Value.field.inj he506) one_ne_zero
        · obtain ⟨Ta, Ba, ℓa, -, hta, hba, -⟩ := ha.forallE_of_load ld12
          obtain ⟨Tb, Bb, ℓb, -, htb, hbb, -⟩ := hb.forallE_of_load ld542
          obtain ⟨qa, rfl, cella⟩ := TmExact.cell_of_load ha ld12
          obtain ⟨qb, rfl, cellb⟩ := TmExact.cell_of_load hb ld542
          subst hc619
          obtain ⟨hT, hB⟩ := (ih _ _ _ _ _ _ (by cells_lt_calls) ev570 rfl).2 rfl k
            Ta Ba Tb Bb x_da x_xa x_la x_db x_xb x_lb rfl hta hba htb hbb
          intro x hin
          rcases addrIn_forall_inv cella hin with h1 | h1
          · exact .forallTy cellb (hT x h1)
          · exact .forallBody cellb (hB x h1)
        · exact absurd (Value.field.inj he624) one_ne_zero
        · obtain ⟨Ta, Va, Ba, -, hta, hva, hba⟩ := ha.letE_of_load ld12
          obtain ⟨Tb, Vb, Bb, -, htb, hvb, hbb⟩ := hb.letE_of_load ld660
          obtain ⟨qa, rfl, cella⟩ := TmExact.cell_of_load ha ld12
          obtain ⟨qb, rfl, cellb⟩ := TmExact.cell_of_load hb ld660
          subst hc775
          have e1 := ObsFn.heap_extends ev697
          have e2 := ObsFn.heap_extends ev732
          have hT := (ih _ _ _ _ _ _ (by cells_lt_calls) ev697 rfl).1 rfl k Ta Tb x_ta x_tb rfl
            hta htb
          have hV := (ih _ _ _ _ _ _ (by cells_lt_calls) ev732 rfl).1 rfl k Va Vb x_va x_vb rfl
            (hva.mono e1) (hvb.mono e1)
          have hB := (ih _ _ _ _ _ _ (by cells_lt_calls) ev758 rfl).1 rfl (k + 1) Ba Bb x_ba x_bb
            rfl (hba.mono (e1.trans e2)) (hbb.mono (e1.trans e2))
          intro x hin
          rcases addrIn_let_inv cella hin with h1 | h1 | h1
          · exact .letTy cellb (hT x h1)
          · exact .letVal cellb (TmExact.addrIn_back hvb e1 x (hV x (AddrIn.mono' e1 h1)))
          · exact .letBody cellb (TmExact.addrIn_back hbb (e1.trans e2) x
              (hB x (AddrIn.mono' (e1.trans e2) h1)))
        · exact absurd (Value.field.inj he780) one_ne_zero
        · exact absurd (Value.field.inj he787) one_ne_zero
        · exact absurd (Value.field.inj he794) one_ne_zero
        · obtain ⟨qa, rfl, cella⟩ := TmExact.cell_of_load ha ld12
          intro x hin
          exact (addrIn_none cella (by decide) hin).elim
        · exact absurd (Value.field.inj he860) one_ne_zero
        · obtain ⟨aa, fa, Ea₁, rfl, -, hra, hEa₁⟩ := ha.proj_of_load ld12
          obtain ⟨ab, fb, Eb₁, rfl, -, hrb, hEb₁⟩ := hb.proj_of_load ld896
          obtain ⟨qa, rfl, cella⟩ := TmExact.cell_of_load ha ld12
          obtain ⟨qb, rfl, cellb⟩ := TmExact.cell_of_load hb ld896
          subst hc999
          obtain ⟨haddr, rfl⟩ := Lib.address_eq_spec ev933 hra hrb
          have haeq : aa = ab := by
            by_cases hab : aa = ab
            · exact hab
            · rw [ite_eq_right hab] at haddr
              exact absurd (Value.field.inj haddr) one_ne_zero
          subst haeq
          have hE := (ih _ _ _ _ _ _ (by cells_lt_calls) ev982 rfl).1 rfl k Ea₁ Eb₁ x_ea x_eb rfl
            hEa₁ hEb₁
          intro x hin
          rcases addrIn_proj_inv cella hin with h1 | h1
          · have e := Bytes.repAddressRef_inj U32.Goldilocks.compatible hra h1
            subst e
            exact .projHead cellb hrb
          · exact .projArg cellb (hE x h1)
        · exact absurd (Value.field.inj he1004) one_ne_zero
        · exact absurd (Value.field.inj he1011) one_ne_zero
        · exact absurd (Value.field.inj he1018) one_ne_zero
      · subst hfn hargs
        rcases Obs.«KernelCheck::kexpr_binder_struct_eq».obs ev with
          ⟨m2, cs13, m37, cs48, cs74, ev15, ev50, ev76, hc93⟩ |
          ⟨_, _, _, _, _, _, _, _, he98, _, _⟩ |
          ⟨_, _, _, _, _, he105, _, _⟩
        · subst hc93
          have e1 := ObsFn.heap_extends ev15
          have e2 := ObsFn.heap_extends ev50
          have hT := (ih _ _ _ _ _ _ (by cells_lt_calls) ev50 rfl).1 rfl k Ta Tb pta ptb rfl
            (hta.mono e1) (htb.mono e1)
          have hB := (ih _ _ _ _ _ _ (by cells_lt_calls) ev76 rfl).1 rfl (k + 1) Ba Bb pba pbb rfl
            (hba.mono (e1.trans e2)) (hbb.mono (e1.trans e2))
          exact ⟨fun x hin => TmExact.addrIn_back htb e1 x (hT x (AddrIn.mono' e1 hin)),
            fun x hin => TmExact.addrIn_back hbb (e1.trans e2) x
              (hB x (AddrIn.mono' (e1.trans e2) hin))⟩
        · exact absurd (Value.field.inj he98) one_ne_zero
        · exact absurd (Value.field.inj he105) one_ne_zero)

/-- **Two terms `kexpr_struct_eq` finds equal have the same cells**: a cell of the first is a
cell of the second. -/
theorem kexpr_struct_eq_cells {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {Ea Eb : KExpr} {pa pb : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : Decl.TmExact κ d Γ h k Ea pa) (hb : Decl.TmExact κ d Γ h k Eb pb)
    (ev : ObsFn W "KernelCheck::kexpr_struct_eq" [pa, pb] h (.field 1) h' cs) :
    ∀ x, AddrIn h pa x → AddrIn h pb x :=
  (struct_eq_cells_aux _ _ _ _ _ _ ev rfl).1 rfl k Ea Eb pa pb rfl ha hb

/-! ## Two conversions of one expression -/

/-- **Two conversions of one expression have the same cells**: a cell of one stands for the
address of a cell of the other. -/
theorem RawConvExpr.cells_of_twin {refs recurAddrs : List _root_.Address}
    {univs : List Ixon.Univ} {sharing : List Ixon.Expr}
    {blobs₂ : List (_root_.Address × ByteArray)} {h₂ : Heap F} {bound₂ : Nat} {e : Ixon.Expr}
    {p₂ : SourceValue F}
    (r₂ : Ingress.RawConvExpr refs recurAddrs univs sharing blobs₂ h₂ bound₂ e p₂) :
    ∀ {blobs₁ : List (_root_.Address × ByteArray)} {h₁ : Heap F} {bound₁ : Nat}
      {p₁ : SourceValue F},
      Ingress.RawConvExpr refs recurAddrs univs sharing blobs₁ h₁ bound₁ e p₁ →
      ∀ x, AddrIn h₂ p₂ x → ∃ y, AddrIn h₁ p₁ y ∧ ixAddr y = ixAddr x := by
  induction r₂ with
  | var hidx cell =>
    intro _ _ _ _ _ x hin
    exact (addrIn_none cell (by decide) hin).elim
  | sort huIdx hu rl cell =>
    intro _ _ _ _ _ x hin
    exact (addrIn_none cell (by decide) hin).elim
  | ref hrIdx href hd ra hls rls cell =>
    intro _ _ _ _ r₁ x hin
    have hxd := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra (addrIn_const_inv cell hin)
    cases r₁ with
    | ref hrIdx' href' hd' ra' hls' rls' cell' =>
      refine ⟨_, .const cell' ra', ?_⟩
      rw [hd', ← hxd, hd]
      exact Option.some.inj (href'.symm.trans href)
  | recur hrIdx hrec hd ra hls rls cell =>
    intro _ _ _ _ r₁ x hin
    have hxd := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra (addrIn_const_inv cell hin)
    cases r₁ with
    | recur hrIdx' hrec' hd' ra' hls' rls' cell' =>
      refine ⟨_, .const cell' ra', ?_⟩
      rw [hd', ← hxd, hd]
      exact Option.some.inj (hrec'.symm.trans hrec)
  | prj htIdx hfIdx href hd ra rin cell ih =>
    intro _ _ _ _ r₁ x hin
    cases r₁ with
    | prj htIdx' hfIdx' href' hd' ra' rin' cell' =>
      rcases addrIn_proj_inv cell hin with h1 | h1
      · have hxd := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra h1
        refine ⟨_, .projHead cell' ra', ?_⟩
        rw [hd', ← hxd, hd]
        exact Option.some.inj (href'.symm.trans href)
      · obtain ⟨y, hy, he⟩ := ih rin' x h1
        exact ⟨y, .projArg cell' hy, he⟩
  | str hbIdx href hmem rbs hs cell =>
    intro _ _ _ _ _ x hin
    exact (addrIn_none cell (by decide) hin).elim
  | nat hbIdx href hmem hcanon rlimbs hlast hval cell =>
    intro _ _ _ _ _ x hin
    exact (addrIn_none cell (by decide) hin).elim
  | app rf ra cell ihf iha =>
    intro _ _ _ _ r₁ x hin
    cases r₁ with
    | app rf' ra' cell' =>
      rcases addrIn_app_inv cell hin with h1 | h1
      · obtain ⟨y, hy, he⟩ := ihf rf' x h1
        exact ⟨y, .appFn cell' hy, he⟩
      · obtain ⟨y, hy, he⟩ := iha ra' x h1
        exact ⟨y, .appArg cell' hy, he⟩
  | lam rl rt rb cell iht ihb =>
    intro _ _ _ _ r₁ x hin
    cases r₁ with
    | lam rl' rt' rb' cell' =>
      rcases addrIn_lam_inv cell hin with h1 | h1
      · obtain ⟨y, hy, he⟩ := iht rt' x h1
        exact ⟨y, .lamTy cell' hy, he⟩
      · obtain ⟨y, hy, he⟩ := ihb rb' x h1
        exact ⟨y, .lamBody cell' hy, he⟩
  | all rl rt rb cell iht ihb =>
    intro _ _ _ _ r₁ x hin
    cases r₁ with
    | all rl' rt' rb' cell' =>
      rcases addrIn_forall_inv cell hin with h1 | h1
      · obtain ⟨y, hy, he⟩ := iht rt' x h1
        exact ⟨y, .forallTy cell' hy, he⟩
      · obtain ⟨y, hy, he⟩ := ihb rb' x h1
        exact ⟨y, .forallBody cell' hy, he⟩
  | letE rt rv rb cell iht ihv ihb =>
    intro _ _ _ _ r₁ x hin
    cases r₁ with
    | letE rt' rv' rb' cell' =>
      rcases addrIn_let_inv cell hin with h1 | h1 | h1
      · obtain ⟨y, hy, he⟩ := iht rt' x h1
        exact ⟨y, .letTy cell' hy, he⟩
      · obtain ⟨y, hy, he⟩ := ihv rv' x h1
        exact ⟨y, .letVal cell' hy, he⟩
      · obtain ⟨y, hy, he⟩ := ihb rb' x h1
        exact ⟨y, .letBody cell' hy, he⟩
  | share hidx hsh rs ih =>
    intro _ _ _ _ r₁ x hin
    cases r₁ with
    | share hidx' hsh' rs' =>
      have hs := Option.some.inj (hsh.symm.trans hsh')
      subst hs
      exact ih rs' x hin

end IxVM.Refinement.Binding
