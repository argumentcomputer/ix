import IxVMRefinement.Binding.OpValidation

/-! # The cells of `KernelSubst::subst_const`'s result

`validate_op_equations` compares and checks terms built by `subst_const(e, a, v)` under the
group's role context, so the facts it gives are read at the keying of the closure's
environment, where the operation's own address does not resolve. The terms are first read at
the table's keying (`OpOpen.subst_const_spec`), then moved (`Core.Tm.rekey`), which asks where
their cells lie.

* `Tm.cell_of_load'`: a represented term is a pointer to the cell its load returns.
* `subst_const_cells`: **a cell of `subst_const(e, a, v)`'s result**, at any later heap, is a
  cell of `v`, a cell of `e` other than the address `a` holds, or the head of a projection
  cell of `e`.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Expr)

local macro "lt_calls'" : term =>
  `(by simp only [List.length_cons, List.length_append, List.length_nil] <;> omega)

private theorem cell_load' {h : Heap F} {addr : Nat} {c : String} {xs : List (SourceValue F)}
    {v : SourceValue F} (cell : h[addr]? = some (.construct kexprEnum c xs))
    (hl : loadValue h (.ptr (.enum kexprEnum) addr) = .ok v) : h[addr]? = some v := by
  rw [loadValue_enum_cell cell] at hl
  injection hl with hv
  rw [← hv]
  exact cell

/-- A represented term is a pointer to the cell its load returns. -/
theorem Tm.cell_of_load' {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p v : SourceValue F}
    (rep : Tm κ d Γ h k E p) (hl : loadValue h p = .ok v) :
    ∃ addr, p = .ptr (.enum kexprEnum) addr ∧ h[addr]? = some v := by
  cases rep with
  | bvarLocal cell => exact ⟨_, rfl, cell_load' cell hl⟩
  | bvarFree cell => exact ⟨_, rfl, cell_load' cell hl⟩
  | sort cell => exact ⟨_, rfl, cell_load' cell hl⟩
  | @const _ _ _ _ _ _ _ _ cell => exact ⟨_, rfl, cell_load' cell hl⟩
  | app cell => exact ⟨_, rfl, cell_load' cell hl⟩
  | lam cell => exact ⟨_, rfl, cell_load' cell hl⟩
  | forallE cell => exact ⟨_, rfl, cell_load' cell hl⟩
  | letE cell => exact ⟨_, rfl, cell_load' cell hl⟩
  | litNat cell => exact ⟨_, rfl, cell_load' cell hl⟩
  | litStr cell => exact ⟨_, rfl, cell_load' cell hl⟩
  | @proj _ _ _ _ _ _ _ _ _ cell => exact ⟨_, rfl, cell_load' cell hl⟩

private theorem ext_snoc' {h h' : Heap F} {x : SourceValue F} (hm : h' = h ++ [x]) :
    Heap.Extends h h' := by
  rw [hm]; exact Heap.Extends.snoc _ _

private theorem snoc_cell {h : Heap F} {x : SourceValue F} : (h ++ [x])[h.length]? = some x := by
  simp

/-- **The cells of `subst_const`'s result** (module docstring), by the same induction as
`OpOpen.subst_const_spec`. -/
theorem subst_const_cells (κ : _root_.Address → KKey) (d : Nat) (Γ : Nat → KExpr)
    (a v : SourceValue F) (b : Bytes.Address) (val : KExpr)
    (hinj : ∀ b', κ (ixAddr b') = κ (ixAddr b) → b' = b) :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W fname args h r h' cs →
      fname = "KernelSubst::subst_const" → ∀ (e : SourceValue F) (k : Nat) (X : KExpr),
        args = [e, a, v] → Tm κ d Γ h k X e → Bytes.RepAddressRef addrTy h b a →
        TmC κ h val v → ∀ h₂, Heap.Extends h' h₂ → ∀ x, AddrIn h₂ r x →
          AddrIn h₂ v x ∨ (AddrIn h₂ e x ∧ x ≠ b) ∨ ProjIn h₂ e x :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelSubst::subst_const" →
      ∀ (e : SourceValue F) (k : Nat) (X : KExpr),
        args = [e, a, v] → Tm κ d Γ h k X e → Bytes.RepAddressRef addrTy h b a →
        TmC κ h val v → ∀ h₂, Heap.Extends h' h₂ → ∀ x, AddrIn h₂ r x →
          AddrIn h₂ v x ∨ (AddrIn h₂ e x ∧ x ≠ b) ∨ ProjIn h₂ e x)
    (fun fname args h r h' cs ev ih hfn e k X hargs hX ha hv => by
      subst hfn hargs
      match Obs.«KernelSubst::subst_const».obs ev with
      | .Const_n1_Nil (he85 := hr) .. =>
        subst hr
        intro h₂ _ x hin
        exact Or.inl hin
      | .Const_n1_Cons (heq132 := h01) .. =>
        exact absurd (Value.field.inj h01) zero_ne_one
      | .Const_other (ld12 := ld) (ev44 := aeq) (hne138 := hne) (he143 := hr) (he144 := hh) .. =>
        have extA := aeq.heap_extends
        subst hr hh
        intro h₂ ext x hin
        refine Or.inr (Or.inl ⟨hin, ?_⟩)
        obtain ⟨a', us, hXe, ra, -⟩ := hX.const_of_load ld
        obtain ⟨h1, hm⟩ := Lib.address_eq_spec aeq ra ha
        subst h1
        have hab : a' ≠ b := fun hab => hne (by rw [ite_eq_left hab])
        obtain ⟨addr, he, hcell⟩ := Tm.cell_of_load' hX ld
        subst he
        have ext' := extA.trans ext
        have hxr := addrIn_const_inv (ext'.getElem?_eq hcell) hin
        have e' : a' = x := Bytes.repAddressRef_inj U32.Goldilocks.compatible
          (Bytes.repAddressRef_heapMono₂ addrTy ext' ra) hxr
        rw [← e']
        exact hab
      | .App (m210 := m₂) (v171 := r₁) (v172 := r₂) (ld12 := ld) (he167 := hr) (hm166 := hm)
          (ev184 := e1) (ev220 := e2) (hc245 := hc) .. =>
        have ext3 := ext_snoc' hm
        have ext1 := e1.heap_extends
        have ext2 := e2.heap_extends
        subst hc hr hm
        obtain ⟨Ef, Ea, hXe, hf, hx⟩ := hX.app_of_load ld
        obtain ⟨addr, he, hcell⟩ := Tm.cell_of_load' hX ld
        subst he
        intro h₂ ext x hin
        have hnew := ext.getElem?_eq (snoc_cell (h := m₂)
          (x := .construct "KernelTypes::KExprNode" "App" [r₁, r₂]))
        have hc₂ := ((ext1.trans ext2).trans (ext3.trans ext)).getElem?_eq hcell
        rcases addrIn_app_inv hnew hin with h1 | h1
        · rcases ih _ _ _ _ _ _ lt_calls' e1 rfl _ k Ef rfl hf ha hv h₂
            (ext2.trans (ext3.trans ext)) x h1 with hv' | ⟨hf', hne⟩ | hp
          · exact Or.inl hv'
          · exact Or.inr (Or.inl ⟨.appFn hc₂ hf', hne⟩)
          · exact Or.inr (Or.inr (.appFn hc₂ hp))
        · rcases ih _ _ _ _ _ _ lt_calls' e2 rfl _ k Ea rfl (hx.mono ext1)
            (Bytes.repAddressRef_heapMono₂ addrTy ext1 ha) (hv.mono ext1) h₂
            (ext3.trans ext) x h1 with hv' | ⟨hf', hne⟩ | hp
          · exact Or.inl hv'
          · exact Or.inr (Or.inl ⟨.appArg hc₂ hf', hne⟩)
          · exact Or.inr (Or.inr (.appArg hc₂ hp))
      | .Lam (m316 := m₂) (v276 := r₁) (v277 := r₂) (x_bl := xbl) (ld12 := ld) (he272 := hr)
          (hm271 := hm) (ev290 := e1) (ev326 := e2) (hc358 := hc) .. =>
        have ext3 := ext_snoc' hm
        have ext1 := e1.heap_extends
        have ext2 := e2.heap_extends
        subst hc hr hm
        obtain ⟨T, B, ℓ, hXe, ht, hb, hl⟩ := hX.lam_of_load ld
        obtain ⟨addr, he, hcell⟩ := Tm.cell_of_load' hX ld
        subst he
        intro h₂ ext x hin
        have hnew := ext.getElem?_eq (snoc_cell (h := m₂)
          (x := .construct "KernelTypes::KExprNode" "Lam" [r₁, r₂, xbl]))
        have hc₂ := ((ext1.trans ext2).trans (ext3.trans ext)).getElem?_eq hcell
        rcases addrIn_lam_inv hnew hin with h1 | h1
        · rcases ih _ _ _ _ _ _ lt_calls' e1 rfl _ k T rfl ht ha hv h₂
            (ext2.trans (ext3.trans ext)) x h1 with hv' | ⟨hf', hne⟩ | hp
          · exact Or.inl hv'
          · exact Or.inr (Or.inl ⟨.lamTy hc₂ hf', hne⟩)
          · exact Or.inr (Or.inr (.lamTy hc₂ hp))
        · rcases ih _ _ _ _ _ _ lt_calls' e2 rfl _ (k + 1) B rfl (hb.mono ext1)
            (Bytes.repAddressRef_heapMono₂ addrTy ext1 ha) (hv.mono ext1) h₂
            (ext3.trans ext) x h1 with hv' | ⟨hf', hne⟩ | hp
          · exact Or.inl hv'
          · exact Or.inr (Or.inl ⟨.lamBody hc₂ hf', hne⟩)
          · exact Or.inr (Or.inr (.lamBody hc₂ hp))
      | .Forall (m429 := m₂) (v389 := r₁) (v390 := r₂) (x_bl := xbl) (ld12 := ld)
          (he385 := hr) (hm384 := hm) (ev403 := e1) (ev439 := e2) (hc471 := hc) .. =>
        have ext3 := ext_snoc' hm
        have ext1 := e1.heap_extends
        have ext2 := e2.heap_extends
        subst hc hr hm
        obtain ⟨T, B, ℓ, hXe, ht, hb, hl⟩ := hX.forallE_of_load ld
        obtain ⟨addr, he, hcell⟩ := Tm.cell_of_load' hX ld
        subst he
        intro h₂ ext x hin
        have hnew := ext.getElem?_eq (snoc_cell (h := m₂)
          (x := .construct "KernelTypes::KExprNode" "Forall" [r₁, r₂, xbl]))
        have hc₂ := ((ext1.trans ext2).trans (ext3.trans ext)).getElem?_eq hcell
        rcases addrIn_forall_inv hnew hin with h1 | h1
        · rcases ih _ _ _ _ _ _ lt_calls' e1 rfl _ k T rfl ht ha hv h₂
            (ext2.trans (ext3.trans ext)) x h1 with hv' | ⟨hf', hne⟩ | hp
          · exact Or.inl hv'
          · exact Or.inr (Or.inl ⟨.forallTy hc₂ hf', hne⟩)
          · exact Or.inr (Or.inr (.forallTy hc₂ hp))
        · rcases ih _ _ _ _ _ _ lt_calls' e2 rfl _ (k + 1) B rfl (hb.mono ext1)
            (Bytes.repAddressRef_heapMono₂ addrTy ext1 ha) (hv.mono ext1) h₂
            (ext3.trans ext) x h1 with hv' | ⟨hf', hne⟩ | hp
          · exact Or.inl hv'
          · exact Or.inr (Or.inl ⟨.forallBody hc₂ hf', hne⟩)
          · exact Or.inr (Or.inr (.forallBody hc₂ hp))
      | .Let (m578 := m₂) (v502 := r₁) (v503 := r₂) (v504 := r₃) (ld12 := ld) (he498 := hr)
          (hm497 := hm) (ev516 := e1) (ev552 := e2) (ev588 := e3) (hc613 := hc) .. =>
        have ext4 := ext_snoc' hm
        have ext1 := e1.heap_extends
        have ext2 := e2.heap_extends
        have ext3 := e3.heap_extends
        subst hc hr hm
        obtain ⟨T, V, B, hXe, ht, hvv, hb⟩ := hX.letE_of_load ld
        obtain ⟨addr, he, hcell⟩ := Tm.cell_of_load' hX ld
        subst he
        intro h₂ ext x hin
        have hnew := ext.getElem?_eq (snoc_cell (h := m₂)
          (x := .construct "KernelTypes::KExprNode" "Let" [r₁, r₂, r₃]))
        have hc₂ := ((ext1.trans ext2).trans (ext3.trans (ext4.trans ext))).getElem?_eq hcell
        rcases addrIn_let_inv hnew hin with h1 | h1 | h1
        · rcases ih _ _ _ _ _ _ lt_calls' e1 rfl _ k T rfl ht ha hv h₂
            (ext2.trans (ext3.trans (ext4.trans ext))) x h1 with hv' | ⟨hf', hne⟩ | hp
          · exact Or.inl hv'
          · exact Or.inr (Or.inl ⟨.letTy hc₂ hf', hne⟩)
          · exact Or.inr (Or.inr (.letTy hc₂ hp))
        · rcases ih _ _ _ _ _ _ lt_calls' e2 rfl _ k V rfl (hvv.mono ext1)
            (Bytes.repAddressRef_heapMono₂ addrTy ext1 ha) (hv.mono ext1) h₂
            (ext3.trans (ext4.trans ext)) x h1 with hv' | ⟨hf', hne⟩ | hp
          · exact Or.inl hv'
          · exact Or.inr (Or.inl ⟨.letVal hc₂ hf', hne⟩)
          · exact Or.inr (Or.inr (.letVal hc₂ hp))
        · rcases ih _ _ _ _ _ _ lt_calls' e3 rfl _ (k + 1) B rfl (hb.mono (ext1.trans ext2))
            (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) ha)
            (hv.mono (ext1.trans ext2)) h₂ (ext4.trans ext) x h1 with hv' | ⟨hf', hne⟩ | hp
          · exact Or.inl hv'
          · exact Or.inr (Or.inl ⟨.letBody hc₂ hf', hne⟩)
          · exact Or.inr (Or.inr (.letBody hc₂ hp))
      | .Proj (m662 := m₂) (v646 := r₁) (x_s := xs) (x_i := xi) (ld12 := ld) (he640 := hr)
          (hm639 := hm) (ev672 := e1) (hc697 := hc) .. =>
        have ext2 := ext_snoc' hm
        have ext1 := e1.heap_extends
        subst hc hr hm
        obtain ⟨s, i, Es, hxi, hXe, ra, hes⟩ := hX.proj_of_load ld
        subst hxi
        obtain ⟨addr, he, hcell⟩ := Tm.cell_of_load' hX ld
        subst he
        intro h₂ ext x hin
        have hnew := ext.getElem?_eq (snoc_cell (h := m₂)
          (x := .construct "KernelTypes::KExprNode" "Proj" [xs, .field i, r₁]))
        have hc₂ := (ext1.trans (ext2.trans ext)).getElem?_eq hcell
        have ra₂ := Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans (ext2.trans ext)) ra
        rcases addrIn_proj_inv hnew hin with h1 | h1
        · have e' : s = x := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra₂ h1
          subst e'
          exact Or.inr (Or.inr (.head hc₂ ra₂))
        · rcases ih _ _ _ _ _ _ lt_calls' e1 rfl _ k Es rfl hes ha hv h₂ (ext2.trans ext) x h1
            with hv' | ⟨hf', hne⟩ | hp
          · exact Or.inl hv'
          · exact Or.inr (Or.inl ⟨.projArg hc₂ hf', hne⟩)
          · exact Or.inr (Or.inr (.projArg hc₂ hp))
      | .other (ld12 := ld) (hne146 := n1) (hne246 := n2) (hne359 := n3) (hne472 := n4)
          (hne614 := n5) (hne698 := n6) (he703 := hr) (he704 := hh) .. =>
        subst hr hh
        intro h₂ ext x hin
        exfalso
        cases hX with
        | bvarLocal cell =>
          exact addrIn_none (ext.getElem?_eq cell) (by decide) hin
        | bvarFree cell =>
          exact addrIn_none (ext.getElem?_eq cell) (by decide) hin
        | sort cell =>
          exact addrIn_none (ext.getElem?_eq cell) (by decide) hin
        | litNat cell =>
          exact addrIn_none (ext.getElem?_eq cell) (by decide) hin
        | litStr cell =>
          exact addrIn_none (ext.getElem?_eq cell) (by decide) hin
        | @const _ _ _ _ _ _ _ _ cell =>
          exact n1 _ rfl (Option.some.inj ((cell_load' cell ld).symm.trans cell))
        | app cell => exact n2 _ rfl (Option.some.inj ((cell_load' cell ld).symm.trans cell))
        | lam cell => exact n3 _ rfl (Option.some.inj ((cell_load' cell ld).symm.trans cell))
        | forallE cell => exact n4 _ rfl (Option.some.inj ((cell_load' cell ld).symm.trans cell))
        | letE cell => exact n5 _ rfl (Option.some.inj ((cell_load' cell ld).symm.trans cell))
        | @proj _ _ _ _ _ _ _ _ _ cell =>
          exact n6 _ rfl (Option.some.inj ((cell_load' cell ld).symm.trans cell)))


/-! ## A recurrence side's rendered term -/

/-- **A rigid term**: no binder and no free variable. -/
def pwRigid : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .app f a => pwRigid f && pwRigid a
  | _ => false

/-- **A term that is a rigid term up to binder data is that term.** -/
theorem eq_of_erasePw_rigid : ∀ (L : KExpr), pwRigid L = true → ∀ (T : KExpr),
    T.erasePw = L.erasePw → T = L
  | .bvar _, _, T, h => by
    cases T <;> simp only [Ix.Kernel.Expr.erasePw] at h <;> first | exact h | exact nomatch h
  | .sort _, _, T, h => by
    cases T <;> simp only [Ix.Kernel.Expr.erasePw] at h <;> first | exact h | exact nomatch h
  | .const _ _, _, T, h => by
    cases T <;> simp only [Ix.Kernel.Expr.erasePw] at h <;> first | exact h | exact nomatch h
  | .lit _, _, T, h => by
    cases T <;> simp only [Ix.Kernel.Expr.erasePw] at h <;> first | exact h | exact nomatch h
  | .app f a, hL, T, h => by
    simp only [pwRigid, Bool.and_eq_true] at hL
    cases T with
    | app f' a' =>
      simp only [Ix.Kernel.Expr.erasePw] at h
      injection h with h1 h2
      rw [eq_of_erasePw_rigid f hL.1 f' h1, eq_of_erasePw_rigid a hL.2 a' h2]
    | _ => simp only [Ix.Kernel.Expr.erasePw] at h; exact nomatch h
  | .fvar _ _, hL, _, _ => by simp [pwRigid] at hL
  | .lam _ _ _, hL, _, _ => by simp [pwRigid] at hL
  | .forallE _ _ _, hL, _, _ => by simp [pwRigid] at hL
  | .letE _ _ _ _, hL, _, _ => by simp [pwRigid] at hL
  | .proj _ _ _, hL, _, _ => by simp [pwRigid] at hL

/-- **A recurrence side closed over its two variables has the shape `open_two_lams` reads**:
`λ (x y : Nat), L` with a rigid `L` that opens to the side. -/
def sideShapeOk (l : KExpr) : Bool :=
  match opSideRaw l with
  | .lam A (.lam B L _) _ =>
    decide (A = OpOpen.natTy) && decide (B = OpOpen.natTy) && pwRigid L &&
      decide (OpOpen.open₂ OpOpen.natTy OpOpen.natTy L = l)
  | _ => false

set_option maxRecDepth 100000 in
/-- Every side of every recurrence has that shape (decided over the seven operations). -/
theorem sideShape_all : ∀ c ∈ Ix.Kernel.natOpNames, ∀ eq ∈ Ix.Kernel.natOpEquations 0 c,
    sideShapeOk eq.1 = true ∧ sideShapeOk eq.2 = true := by
  decide +kernel

theorem sideShape_spec {l : KExpr} (h : sideShapeOk l = true) :
    ∃ L m₁ m₂, opSideRaw l = .lam OpOpen.natTy (.lam OpOpen.natTy L m₂) m₁ ∧
      pwRigid L = true ∧ OpOpen.open₂ OpOpen.natTy OpOpen.natTy L = l := by
  unfold sideShapeOk at h
  split at h
  · rename_i A B L m₂ m₁ hraw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hA, hB⟩, hr⟩, ho⟩ := h
    subst hA hB
    exact ⟨L, m₁, m₂, hraw, hr, ho⟩
  · cases h

/-- **A rendered side is the closed side up to the binders' data**, so it is
`λ (x y : Nat), L` itself with the binders' data of the rendering. -/
theorem rendered_side_shape {l T : KExpr} (hs : sideShapeOk l = true)
    (hT : T.erasePw = (opSideRaw l).erasePw) :
    ∃ L m₁ m₂, T = .lam OpOpen.natTy (.lam OpOpen.natTy L m₂) m₁ ∧ pwRigid L = true ∧
      OpOpen.open₂ OpOpen.natTy OpOpen.natTy L = l := by
  obtain ⟨L, m₁, m₂, hraw, hr, ho⟩ := sideShape_spec hs
  rw [hraw] at hT
  cases T with
  | lam A X ma =>
    simp only [Ix.Kernel.Expr.erasePw] at hT
    injection hT with hA hX _
    cases X with
    | lam B L' mb =>
      simp only [Ix.Kernel.Expr.erasePw] at hX
      injection hX with hB hL _
      have eA := eq_of_erasePw_rigid OpOpen.natTy rfl A hA
      have eB := eq_of_erasePw_rigid OpOpen.natTy rfl B hB
      have eL := eq_of_erasePw_rigid L hr L' hL
      subst eA eB eL
      exact ⟨L', ma, mb, rfl, hr, ho⟩
    | _ => simp only [Ix.Kernel.Expr.erasePw] at hX; exact nomatch hX
  | _ => simp only [Ix.Kernel.Expr.erasePw] at hT; exact nomatch hT

/-- **The cells of a rendered left side** are the addresses of the roles the side names. -/
theorem opEquationLhs_cells {t : Ix.Kernel.RoleTable} {r : Ix.Kernel.Role} {k : Nat}
    {eq : KExpr × KExpr} (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames)
    (hget : (Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey))[k]? = some eq)
    (htwf : t.wf = true) {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (htbl : TableRep t h x_tbl)
    (ev : ObsFn W "KernelRoleSpec::op_equation_lhs"
      [x_tbl, .field (roleNum r), .field ((k : Nat) : F)] h res h' cs) :
    ∀ x, AddrIn h' res x → ∃ r', t.addressOf? r' = some (ixAddr x) ∧
      ∀ P, (opSideRaw eq.1).constsResolveBy P = true → P (Ix.Kernel.Key.role r') = true := by
  obtain ⟨hk, hread⟩ := opSide_read opEquationLhsArmsRead_true hmem hget
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.op_equation_lhs.lookup
    op_equation_lhs_noControl ev
  have hp : (IxVM.KernelRoleSpec.op_equation_lhs.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["tbl", "r", "k"] := rfl
  have hb : IxVM.KernelRoleSpec.op_equation_lhs.body =
      .matchValue (.binary .add (.binary .mul (.literal 64) (.var "r")) (.var "k"))
        (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_lhs.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨bs, body, cs', sel, dArm⟩ :=
    keyed_match_inv (a := roleNum r) (b := ((k : Nat) : F)) (by simp) (by simp) d0
  have hread' : armReadsAs (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_lhs.body)
      (ZMod.val (64 * roleNum r + ((k : Nat) : F))) (opSideRaw eq.1) 0 = true := by
    rw [val_key r hk]
    exact hread
  exact cells_of_armReadsAs htwf hread' (by simp) htbl sel dArm

/-- **The cells of a rendered right side** are the addresses of the roles the side names. -/
theorem opEquationRhs_cells {t : Ix.Kernel.RoleTable} {r : Ix.Kernel.Role} {k : Nat}
    {eq : KExpr × KExpr} (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames)
    (hget : (Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey))[k]? = some eq)
    (htwf : t.wf = true) {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (htbl : TableRep t h x_tbl)
    (ev : ObsFn W "KernelRoleSpec::op_equation_rhs"
      [x_tbl, .field (roleNum r), .field ((k : Nat) : F)] h res h' cs) :
    ∀ x, AddrIn h' res x → ∃ r', t.addressOf? r' = some (ixAddr x) ∧
      ∀ P, (opSideRaw eq.2).constsResolveBy P = true → P (Ix.Kernel.Key.role r') = true := by
  obtain ⟨hk, hread⟩ := opSide_read opEquationRhsArmsRead_true hmem hget
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.op_equation_rhs.lookup
    op_equation_rhs_noControl ev
  have hp : (IxVM.KernelRoleSpec.op_equation_rhs.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["tbl", "r", "k"] := rfl
  have hb : IxVM.KernelRoleSpec.op_equation_rhs.body =
      .matchValue (.binary .add (.binary .mul (.literal 64) (.var "r")) (.var "k"))
        (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_rhs.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨bs, body, cs', sel, dArm⟩ :=
    keyed_match_inv (a := roleNum r) (b := ((k : Nat) : F)) (by simp) (by simp) d0
  have hread' : armReadsAs (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_rhs.body)
      (ZMod.val (64 * roleNum r + ((k : Nat) : F))) (opSideRaw eq.2) 0 = true := by
    rw [val_key r hk]
    exact hread
  exact cells_of_armReadsAs htwf hread' (by simp) htbl sel dArm

end IxVM.Refinement.Binding
