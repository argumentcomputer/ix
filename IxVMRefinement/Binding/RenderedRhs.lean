import IxVMRefinement.Binding.RenderedSpecs
import IxVMRefinement.Obs.KernelRoleSpec2
import IxVMRefinement.RoleVal.GroupAdmit

/-! # The right side of a recurrence, from the generated paths of `op_equation_rhs`

`KernelRoleSpec::op_equation_rhs` has generated evaluation paths, one per rendered arm. This file
reads one arm as the statement `OpEquationRhsRenders` asks: the right side of `Nat.pred`'s first
recurrence (`Nat.pred Nat.zero = Nat.zero`).

* `op_equation_rhs_natPred_zero`: the arm at the key `64 * 41 + 0` allocates `fun (x y : Nat) =>
  Nat.zero` with both binders' data the level `1`, the constants of `Nat` and `Nat.zero` read
  through the table; under the table's keying the pointer represents that term exactly, and it is
  the closed raw side up to binder data.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)

private theorem ext_of_snoc {h h' : Heap F} {x : SourceValue F} (hm : h' = h ++ [x]) :
    Heap.Extends h h' := by
  rw [hm]
  exact Heap.Extends.snoc _ _

private theorem cell_of_snoc {h h' : Heap F} {x : SourceValue F} (hm : h' = h ++ [x]) :
    h'[h.length]? = some x := by
  rw [hm]
  simp

/-- The key an arm of a rendered `match 64 * r + k` is selected at. -/
private theorem key_value {a b : F} {x v : SourceValue F}
    (o1 : evalBinOp .mul (.field 64 : SourceValue F) (.field a) = .ok x)
    (o2 : evalBinOp .add x (.field b) = .ok v) : v = .field (64 * a + b) := by
  simp only [evalBinOp, Except.ok.injEq] at o1
  subst o1
  simp only [evalBinOp, Except.ok.injEq] at o2
  exact o2.symm

private theorem natPred_key :
    (64 * roleNum Ix.Kernel.Role.natPred + ((0 : Nat) : F) : F) = 2624 := by decide

/-- **The right side of `Nat.pred`'s first recurrence, as `op_equation_rhs` builds it.** -/
theorem op_equation_rhs_natPred_zero {t : Ix.Kernel.RoleTable} (htwf : t.wf = true)
    {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (htbl : TableRep t h x_tbl)
    (ev : ObsFn W "KernelRoleSpec::op_equation_rhs"
      [x_tbl, .field (roleNum .natPred), .field ((0 : Nat) : F)] h res h' cs) :
    Heap.Extends h h' ∧
      RendersUpToBinderData t h' (opSideRaw (.const (Ix.Kernel.natZeroName : KKey) [])) res := by
  have hne : ∀ {K : F} {x : SourceValue F},
      evalBinOp .mul (.field 64 : SourceValue F) (.field (roleNum Ix.Kernel.Role.natPred)) = .ok x →
      evalBinOp .add x (.field ((0 : Nat) : F)) = .ok (.field K) → K = 2624 := by
    intro K x o1 o2
    have h1 := Value.field.inj (key_value o1 o2)
    rw [h1]
    exact natPred_key
  match Obs.«KernelRoleSpec::op_equation_rhs».obs ev with
  | .n2624 (m33 := m33) (m48 := m48) (v62 := v62) (m65 := m65) (cs73 := cs73) (m99 := m99)
      (m115 := m115) (m146 := m146) (m169 := m169) (v181 := v181) (m184 := m184)
      (cs192 := cs192) (hm43 := hm33) (hm58 := hm48) (ev75 := e1) (hm109 := hm99)
      (hm123 := hm115) (he131 := hr) (hm130 := hh') (hm154 := hm146) (hm177 := hm169)
      (ev194 := e2) .. =>
    -- the extension chain
    have x1 : Heap.Extends h m33 := ext_of_snoc hm33
    have e1' : ObsFn W "KernelRoles::role_bound_addr" [x_tbl, .field (roleNum .nat)] m33 v62 m65
        cs73 := by
      have e : (roleNum Ix.Kernel.Role.nat : F) = 0 := by decide
      rw [e]
      exact e1
    obtain ⟨x2, aN, ⟨aN', raN, haN⟩, hadN⟩ := RoleVal.role_bound_addr_uncond (htbl.mono x1) e1'
    have x3 : Heap.Extends m65 m48 := ext_of_snoc hm48
    have x4 : Heap.Extends m48 m115 := ext_of_snoc hm115
    have x5 : Heap.Extends m115 m99 := ext_of_snoc hm99
    have e2' : ObsFn W "KernelRoles::role_bound_addr" [x_tbl, .field (roleNum .natZero)] m99 v181
        m184 cs192 := by
      have e : (roleNum Ix.Kernel.Role.natZero : F) = 1 := by decide
      rw [e]
      exact e2
    obtain ⟨x6, aZ, ⟨aZ', raZ, haZ⟩, hadZ⟩ := RoleVal.role_bound_addr_uncond
      (htbl.mono (x1.trans (x2.trans (x3.trans (x4.trans x5))))) e2'
    have x7 : Heap.Extends m184 m169 := ext_of_snoc hm169
    have x8 : Heap.Extends m169 m146 := ext_of_snoc hm146
    have x9 : Heap.Extends m146 h' := ext_of_snoc hh'
    have y65 : Heap.Extends m65 h' :=
      x3.trans (x4.trans (x5.trans (x6.trans (x7.trans (x8.trans x9)))))
    have y184 : Heap.Extends m184 h' := x7.trans (x8.trans x9)
    -- the cells, at the final heap
    have cNil := (x2.trans y65).getElem?_eq (cell_of_snoc hm33)
    have cNat := (x4.trans (x5.trans (x6.trans y184))).getElem?_eq (cell_of_snoc hm48)
    have cZero := (x5.trans (x6.trans y184)).getElem?_eq (cell_of_snoc hm115)
    have cSucc := (x6.trans y184).getElem?_eq (cell_of_snoc hm99)
    have cZc := (x8.trans x9).getElem?_eq (cell_of_snoc hm169)
    have cIn := x9.getElem?_eq (cell_of_snoc hm146)
    have cOut := cell_of_snoc hh'
    -- the level list, the binders' level, the two addresses
    have rnil : RepKLevelList h' [] (.ptr (.enum Core.klevelListEnum) h.length) := by
      rw [Core.klevelListEnum_eq]
      refine .nil ?_
      rw [← Core.klevelListEnum_eq]
      exact cNil
    have rl : RepKLevel h' (.succ .zero) (.ptr (.enum klevelEnum) m115.length) :=
      .succ cSucc (.zero cZero)
    have raN' := Bytes.repAddressRef_heapMono₂ addrTy y65 raN
    have raZ' := Bytes.repAddressRef_heapMono₂ addrTy y184 raZ
    have kN : keyOf t (ixAddr aN') = .role .nat := by
      rw [haN]
      exact keyOf_of_addressOf htwf hadN
    have kZ : keyOf t (ixAddr aZ') = .role .natZero := by
      rw [haZ]
      exact keyOf_of_addressOf htwf hadZ
    have tNat : ∀ (d : Nat) (Γ : Nat → KExpr) (k : Nat), Decl.TmExact (keyOf t) d Γ h' k
        (.const (keyOf t (ixAddr aN')) []) (.ptr (.enum kexprEnum) m65.length) :=
      fun d Γ k => .const cNat raN' rnil
    have tZ : ∀ (d : Nat) (Γ : Nat → KExpr) (k : Nat), Decl.TmExact (keyOf t) d Γ h' k
        (.const (keyOf t (ixAddr aZ')) []) (.ptr (.enum kexprEnum) m184.length) :=
      fun d Γ k => .const cZc raZ' rnil
    have hT : Decl.TmCExact (keyOf t) h'
        (.lam (.const (keyOf t (ixAddr aN')) [])
          (.lam (.const (keyOf t (ixAddr aN')) []) (.const (keyOf t (ixAddr aZ')) [])
            (bmeta (.succ .zero))) (bmeta (.succ .zero))) res :=
      fun d Γ => by
        rw [hr]
        exact .lam cOut (tNat d Γ 0) (.lam cIn (tNat d Γ 1) (tZ d Γ 2) rl) rl
    rw [kN, kZ] at hT
    exact ⟨x1.trans (x2.trans y65), Exists.intro _ ⟨hT, by decide +kernel⟩⟩
  | .n2625 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n2688 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n2689 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n2752 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n2753 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n2816 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n2817 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n2880 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n2881 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n2944 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n2945 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n2946 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n2947 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n3008 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n3009 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .n3010 (op25 := o1) (op17 := o2) .. => exact absurd (hne o1 o2) (by decide)
  | .other (op25 := o1) (op17 := o2) (hne232 := hno) .. =>
    exact absurd ((key_value o1 o2).trans (congrArg Value.field natPred_key)) hno

end IxVM.Refinement.Binding
