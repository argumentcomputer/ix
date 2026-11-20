import IxVMRefinement.Binding.OpEquations

/-! # A certificate's proof term, from its load to its scope check

`validate_op_equations` checks a well-founded operation's certificate by loading the theorem's
value (`Ingress::get_ci`), replacing the operation by its value (`KernelSubst::subst_const`) and
checking the result closed and level-free (`KernelCheck::validate_expr_well_scoped(p, 0, 0)`).
The theorem's record is not walked, so its value is known only as the conversion the load built:
its universe levels as converted (parameters below `2^56`, `Ingress.RawKLevel`), its variables of any
index. This file reads that pointer as a term and carries the reading through the replacement and
the check.

* `TmR`: a pointer read as a term, its sorts' and constants' levels as converted, every variable
  read as a bound variable.
* `rawConv_tmR`: a converted expression is read so; `tmExact_toTmR`: so is an exact
  representation at opening depth `0`.
* `subst_const_raw`: `subst_const(e, a, v)` on a pointer read so, the address `a` holds and a
  closed value read so: the result reads as the replacement, and its cells are cells of `v`,
  cells of `e` other than the address, or projection heads of `e`.
* `TmR.lower`: `validate_expr_well_scoped(p, j, nl)` on a pointer read so: the pointer represents
  the same term exactly at local depth `j` (every variable bound inside it or below `j`, every
  level parameter below `2^32`). `TmR.closed_of_scope`: at depth `0` and no level parameter, a
  closed term with no level parameter.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Expr)

local macro "cert_lt_calls" : term =>
  `(by simp only [List.length_cons, List.length_append, List.length_nil] <;> omega)

/-! ## The reading -/

/-- **A pointer read as a term with its levels as converted**: the cells of `TmExact` at opening
depth `0`, with the sorts' and constants' levels as `Convert` builds them (parameters below
`2^56`) and every variable read as the bound variable of its index. -/
inductive TmR (κ : _root_.Address → KKey) (h : Heap F) : KExpr → SourceValue F → Prop where
  | bvar {addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i]))
      (hsmall : ZMod.val i < 9223372036854775808) :
      TmR κ h (.bvar (ZMod.val i)) (.ptr (.enum kexprEnum) addr)
  | sort {addr : Nat} {lp : SourceValue F} {l : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Srt" [lp]))
      (rl : Ingress.RawKLevel h l lp) :
      TmR κ h (.sort l) (.ptr (.enum kexprEnum) addr)
  | const {addr : Nat} {ap lsp : SourceValue F} {a : Bytes.Address} {ls : List KLevel}
      [res : Resolved (κ (ixAddr a))]
      (cell : h[addr]? = some (.construct kexprEnum "Const" [ap, lsp]))
      (ra : Bytes.RepAddressRef addrTy h a ap) (rls : Ingress.RawKLevelList h ls lsp) :
      TmR κ h (.const (κ (ixAddr a)) ls) (.ptr (.enum kexprEnum) addr)
  | app {addr : Nat} {fp ap : SourceValue F} {Ef Ea : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "App" [fp, ap]))
      (rf : TmR κ h Ef fp) (ra : TmR κ h Ea ap) :
      TmR κ h (.app Ef Ea) (.ptr (.enum kexprEnum) addr)
  | lam {addr : Nat} {tp bp lp : SourceValue F} {T B : KExpr} {ℓ : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Lam" [tp, bp, lp]))
      (rt : TmR κ h T tp) (rb : TmR κ h B bp) (rl : KernelLevels.RepKLevel h ℓ lp) :
      TmR κ h (.lam T B (bmeta ℓ)) (.ptr (.enum kexprEnum) addr)
  | forallE {addr : Nat} {tp bp lp : SourceValue F} {T B : KExpr} {ℓ : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [tp, bp, lp]))
      (rt : TmR κ h T tp) (rb : TmR κ h B bp) (rl : KernelLevels.RepKLevel h ℓ lp) :
      TmR κ h (.forallE T B (bmeta ℓ)) (.ptr (.enum kexprEnum) addr)
  | letE {addr : Nat} {tp vp bp : SourceValue F} {T V B : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Let" [tp, vp, bp]))
      (rt : TmR κ h T tp) (rv : TmR κ h V vp) (rb : TmR κ h B bp) :
      TmR κ h (instShift V 0 B) (.ptr (.enum kexprEnum) addr)
  | litNat {addr : Nat} {lp : SourceValue F} {limbs : List UInt64}
      (cell : h[addr]? = some (.construct kexprEnum "Lit" [.construct klitEnum "Nat" [lp]]))
      (rl : RepList limbListEnum RepU64 h limbs lp) (hc : limbs.getLast? ≠ some 0) :
      TmR κ h (.lit (.natVal (limbsVal limbs))) (.ptr (.enum kexprEnum) addr)
  | litStr {addr : Nat} {bp : SourceValue F} {bytes : List UInt8} {s : String}
      (cell : h[addr]? = some (.construct kexprEnum "Lit" [.construct klitEnum "Str" [bp]]))
      (rb : Bytes.RepByteStream byteListEnum h bytes bp) (hs : StrBytes s bytes) :
      TmR κ h (.lit (.strVal s)) (.ptr (.enum kexprEnum) addr)
  | proj {addr : Nat} {ap ep : SourceValue F} {a : Bytes.Address} {i : F} {E : KExpr}
      [res : Resolved (κ (ixAddr a))] [perm : ProjPermitted κ (ixAddr a)]
      (cell : h[addr]? = some (.construct kexprEnum "Proj" [ap, .field i, ep]))
      (ra : Bytes.RepAddressRef addrTy h a ap) (re : TmR κ h E ep) :
      TmR κ h (.proj (κ (ixAddr a)) (ZMod.val i) E) (.ptr (.enum kexprEnum) addr)

theorem TmR.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {E : KExpr} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : TmR κ h₁ E p) : TmR κ h₂ E p := by
  induction rep with
  | bvar cell hs => exact .bvar (ext.getElem?_eq cell) hs
  | sort cell rl => exact .sort (ext.getElem?_eq cell) (rl.mono ext)
  | const cell ra rls =>
    exact .const (ext.getElem?_eq cell) (Bytes.repAddressRef_heapMono₂ addrTy ext ra)
      (rls.mono ext)
  | app cell _ _ ihf iha => exact .app (ext.getElem?_eq cell) ihf iha
  | lam cell _ _ rl iht ihb => exact .lam (ext.getElem?_eq cell) iht ihb (rl.mono ext)
  | forallE cell _ _ rl iht ihb => exact .forallE (ext.getElem?_eq cell) iht ihb (rl.mono ext)
  | letE cell _ _ _ iht ihv ihb => exact .letE (ext.getElem?_eq cell) iht ihv ihb
  | litNat cell rl hc =>
    exact .litNat (ext.getElem?_eq cell) (repList_heapMono₂ _ repU64_heapMono₂ ext rl) hc
  | litStr cell rb hs =>
    exact .litStr (ext.getElem?_eq cell) (Bytes.repByteStream_heapMono₂ _ ext rb) hs
  | proj cell ra _ ihe =>
    exact .proj (ext.getElem?_eq cell) (Bytes.repAddressRef_heapMono₂ addrTy ext ra) ihe

/-! ## Inversions -/

private theorem cert_cell_load {h : Heap F} {addr : Nat} {c : String}
    {xs : List (SourceValue F)} {v : SourceValue F}
    (cell : h[addr]? = some (.construct kexprEnum c xs))
    (hl : loadValue h (.ptr (.enum kexprEnum) addr) = .ok v) : h[addr]? = some v := by
  rw [loadValue_enum_cell cell] at hl
  injection hl with hv
  rw [← hv]
  exact cell

section TmRInv
variable {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr} {p : SourceValue F}

theorem TmR.cell_of_load {v : SourceValue F} (rep : TmR κ h E p) (hl : loadValue h p = .ok v) :
    ∃ addr, p = .ptr (.enum kexprEnum) addr ∧ h[addr]? = some v := by
  cases rep with
  | bvar cell => exact ⟨_, rfl, cert_cell_load cell hl⟩
  | sort cell => exact ⟨_, rfl, cert_cell_load cell hl⟩
  | const cell => exact ⟨_, rfl, cert_cell_load cell hl⟩
  | app cell => exact ⟨_, rfl, cert_cell_load cell hl⟩
  | lam cell => exact ⟨_, rfl, cert_cell_load cell hl⟩
  | forallE cell => exact ⟨_, rfl, cert_cell_load cell hl⟩
  | letE cell => exact ⟨_, rfl, cert_cell_load cell hl⟩
  | litNat cell => exact ⟨_, rfl, cert_cell_load cell hl⟩
  | litStr cell => exact ⟨_, rfl, cert_cell_load cell hl⟩
  | proj cell => exact ⟨_, rfl, cert_cell_load cell hl⟩

theorem TmR.const_of_load {ap lsp : SourceValue F} (rep : TmR κ h E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Const" [ap, lsp])) :
    ∃ a ls, E = .const (κ (ixAddr a)) ls ∧ Bytes.RepAddressRef addrTy h a ap ∧
      Ingress.RawKLevelList h ls lsp := by
  cases rep with
  | const cell ra rls =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2; subst h1 h2
    exact ⟨_, _, rfl, ra, rls⟩
  | bvar cell | sort cell | app cell | lam cell | forallE cell | letE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmR.app_of_load {fp ap : SourceValue F} (rep : TmR κ h E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "App" [fp, ap])) :
    ∃ Ef Ea, E = .app Ef Ea ∧ TmR κ h Ef fp ∧ TmR κ h Ea ap := by
  cases rep with
  | app cell rf ra =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2; subst h1 h2
    exact ⟨_, _, rfl, rf, ra⟩
  | bvar cell | sort cell | const cell | lam cell | forallE cell | letE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmR.lam_of_load {tp bp lp : SourceValue F} (rep : TmR κ h E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Lam" [tp, bp, lp])) :
    ∃ T B ℓ, E = .lam T B (bmeta ℓ) ∧ TmR κ h T tp ∧ TmR κ h B bp ∧
      KernelLevels.RepKLevel h ℓ lp := by
  cases rep with
  | lam cell rt rb rl =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2 h3; injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, rfl, rt, rb, rl⟩
  | bvar cell | sort cell | const cell | app cell | forallE cell | letE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmR.forallE_of_load {tp bp lp : SourceValue F} (rep : TmR κ h E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Forall" [tp, bp, lp])) :
    ∃ T B ℓ, E = .forallE T B (bmeta ℓ) ∧ TmR κ h T tp ∧ TmR κ h B bp ∧
      KernelLevels.RepKLevel h ℓ lp := by
  cases rep with
  | forallE cell rt rb rl =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2 h3; injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, rfl, rt, rb, rl⟩
  | bvar cell | sort cell | const cell | app cell | lam cell | letE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmR.letE_of_load {tp vp bp : SourceValue F} (rep : TmR κ h E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Let" [tp, vp, bp])) :
    ∃ T V B, E = instShift V 0 B ∧ TmR κ h T tp ∧ TmR κ h V vp ∧ TmR κ h B bp := by
  cases rep with
  | letE cell rt rv rb =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2 h3; injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, rfl, rt, rv, rb⟩
  | bvar cell | sort cell | const cell | app cell | lam cell | forallE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmR.proj_of_load {ap fp ep : SourceValue F} (rep : TmR κ h E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Proj" [ap, fp, ep])) :
    ∃ (a : Bytes.Address) (i : F) (E₁ : KExpr),
      fp = .field i ∧ E = .proj (κ (ixAddr a)) (ZMod.val i) E₁ ∧
      Bytes.RepAddressRef addrTy h a ap ∧ TmR κ h E₁ ep ∧
      Resolved (κ (ixAddr a)) ∧ ProjPermitted κ (ixAddr a) := by
  cases rep with
  | @proj addr ap' ep' a i E₁ res perm cell ra re =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2 h3; injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, rfl, rfl, ra, re, res, perm⟩
  | bvar cell | sort cell | const cell | app cell | lam cell | forallE cell | letE cell
  | litNat cell | litStr cell =>
    exact (load_cell_ne cell hl (by decide)).elim

end TmRInv

/-! ## Readings of converted and of exact terms -/

private theorem cert_val_lt {n : Nat} (h : n < 72057594037927936) : ZMod.val (n : F) = n :=
  ZMod.val_natCast_of_lt (by change _ < 18446744069414584321; omega)

/-- **A converted expression reads as a term** under a keying where every address resolves. -/
theorem rawConv_tmR {κ : _root_.Address → KKey} [∀ a, Resolved (κ a)]
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ} {sharing : List Ixon.Expr}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {bound : Nat} {e : Ixon.Expr}
    {p : SourceValue F} (raw : Ingress.RawConvExpr refs recurAddrs univs sharing blobs h bound e p) :
    ∃ E, TmR κ h E p := by
  induction raw with
  | var hidx cell =>
    refine ⟨_, .bvar cell ?_⟩
    rw [cert_val_lt hidx]
    omega
  | sort huIdx hu rl cell => exact ⟨_, .sort cell rl⟩
  | ref hrIdx href hd ra hls rls cell => exact ⟨_, .const cell ra rls⟩
  | recur hrIdx hrec hd ra hls rls cell => exact ⟨_, .const cell ra rls⟩
  | prj htIdx hfIdx href hd ra _ cell ih =>
    obtain ⟨E, hE⟩ := ih
    exact ⟨_, .proj cell ra hE⟩
  | str hbIdx href hmem rbs hs cell => exact ⟨_, .litStr cell rbs hs⟩
  | nat hbIdx href hmem hcanon rlimbs hlast hval cell => exact ⟨_, .litNat cell rlimbs hlast⟩
  | app _ _ cell ihf iha =>
    obtain ⟨Ef, hf⟩ := ihf
    obtain ⟨Ea, ha⟩ := iha
    exact ⟨_, .app cell hf ha⟩
  | lam rl _ _ cell iht ihb =>
    obtain ⟨T, ht⟩ := iht
    obtain ⟨B, hb⟩ := ihb
    exact ⟨_, .lam cell ht hb rl⟩
  | all rl _ _ cell iht ihb =>
    obtain ⟨T, ht⟩ := iht
    obtain ⟨B, hb⟩ := ihb
    exact ⟨_, .forallE cell ht hb rl⟩
  | letE _ _ _ cell iht ihv ihb =>
    obtain ⟨T, ht⟩ := iht
    obtain ⟨V, hv⟩ := ihv
    obtain ⟨B, hb⟩ := ihb
    exact ⟨_, .letE cell ht hv hb⟩
  | share hidx hsh _ ih => exact ih

private theorem repKLevel_raw {h : Heap F} {l : KLevel} {p : SourceValue F}
    (rep : KernelLevels.RepKLevel h l p) : Ingress.RawKLevel h l p := by
  induction rep with
  | zero cell => exact .zero cell
  | succ cell _ ih => exact .succ cell ih
  | max cell _ _ ihu ihv => exact .max cell ihu ihv
  | imax cell _ _ ihu ihv => exact .imax cell ihu ihv
  | param hn cell => exact .param (by omega) cell

private theorem repKLevelList_raw {h : Heap F} {ls : List KLevel} {p : SourceValue F}
    (rep : KernelLevels.RepKLevelList h ls p) : Ingress.RawKLevelList h ls p := by
  have h1 : RepList KernelLevels.klevelListEnum Ingress.RawKLevel h ls p :=
    OpOpen.repList_imp (fun _ _ _ x => repKLevel_raw x) rep
  unfold Ingress.RawKLevelList
  rw [Core.klevelListEnum_eq]
  exact h1

/-- **An exact representation at opening depth `0` reads as a term.** -/
theorem tmExact_toTmR {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F} {k : Nat}
    {E : KExpr} {p : SourceValue F} (rep : Decl.TmExact κ 0 Γ h k E p) : TmR κ h E p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvar cell hs
  | bvarFree _ _ _ hd => omega
  | sort cell rl => exact .sort cell (repKLevel_raw rl)
  | const cell ra rls => exact .const cell ra (repKLevelList_raw rls)
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra ihe

/-! ## `KernelSubst::subst_const` on a reading -/

private theorem cert_ext_snoc {h h' : Heap F} {x : SourceValue F} (hm : h' = h ++ [x]) :
    Heap.Extends h h' := by
  rw [hm]; exact Heap.Extends.snoc _ _

private theorem cert_snoc_cell {h : Heap F} {x : SourceValue F} :
    (h ++ [x])[h.length]? = some x := by
  simp

private theorem subst_const_raw_aux (κ : _root_.Address → KKey) (a v : SourceValue F)
    (b : Bytes.Address) (val : KExpr) (hvc : val.looseBVarsBounded 0 = true)
    (hinj : ∀ b', κ (ixAddr b') = κ (ixAddr b) → b' = b) :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W fname args h r h' cs →
      fname = "KernelSubst::subst_const" → ∀ (e : SourceValue F) (X : KExpr),
        args = [e, a, v] → TmR κ h X e → Bytes.RepAddressRef addrTy h b a → TmR κ h val v →
        TmR κ h' (Expr.substConstAll (κ (ixAddr b)) val X) r ∧
          ∀ h₂, Heap.Extends h' h₂ → ∀ x, AddrIn h₂ r x →
            AddrIn h₂ v x ∨ (AddrIn h₂ e x ∧ x ≠ b) ∨ ProjIn h₂ e x :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelSubst::subst_const" →
      ∀ (e : SourceValue F) (X : KExpr),
        args = [e, a, v] → TmR κ h X e → Bytes.RepAddressRef addrTy h b a → TmR κ h val v →
        TmR κ h' (Expr.substConstAll (κ (ixAddr b)) val X) r ∧
          ∀ h₂, Heap.Extends h' h₂ → ∀ x, AddrIn h₂ r x →
            AddrIn h₂ v x ∨ (AddrIn h₂ e x ∧ x ≠ b) ∨ ProjIn h₂ e x)
    (fun fname args h r h' cs ev ih hfn e X hargs hX ha hv => by
      subst hfn hargs
      match Obs.«KernelSubst::subst_const».obs ev with
      | .Const_n1_Nil (ld12 := ld) (ev44 := aeq) (ld76 := ldn) (he85 := hr) (he86 := hh) .. =>
        subst hr hh
        obtain ⟨a', us, hXe, ra, rls⟩ := hX.const_of_load ld
        subst hXe
        obtain ⟨h1, hm⟩ := Lib.address_eq_spec aeq ra ha
        subst hm
        by_cases hab : a' = b
        · have hls : us = [] := Core.RepList.nil_of_load rls ldn
          subst hls hab
          rw [OpOpen.substConstAll_const_self]
          exact ⟨hv, fun _ _ x hin => Or.inl hin⟩
        · rw [ite_eq_right hab] at h1
          exact absurd (Value.field.inj h1) one_ne_zero
      | .Const_n1_Cons (heq132 := h01) .. =>
        exact absurd (Value.field.inj h01) zero_ne_one
      | .Const_other (ld12 := ld) (ev44 := aeq) (hne138 := hne) (he143 := hr) (he144 := hh) .. =>
        subst hr hh
        obtain ⟨a', us, hXe, ra, -⟩ := hX.const_of_load ld
        obtain ⟨h1, hm⟩ := Lib.address_eq_spec aeq ra ha
        subst hm h1
        have hab : a' ≠ b := fun hab => hne (by rw [ite_eq_left hab])
        obtain ⟨addr, he, hcell⟩ := hX.cell_of_load ld
        subst hXe
        rw [OpOpen.substConstAll_const_ne val us (fun hk => hab (hinj a' hk))]
        refine ⟨hX, fun h₂ ext x hin => Or.inr (Or.inl ⟨hin, ?_⟩)⟩
        subst he
        have hxr := addrIn_const_inv (ext.getElem?_eq hcell) hin
        have e' : a' = x := Bytes.repAddressRef_inj U32.Goldilocks.compatible
          (Bytes.repAddressRef_heapMono₂ addrTy ext ra) hxr
        rw [← e']
        exact hab
      | .App (m210 := m₂) (v171 := r₁) (v172 := r₂) (ld12 := ld) (he167 := hr) (hm166 := hm)
          (ev184 := e1) (ev220 := e2) (hc245 := hc) .. =>
        have ext3 := cert_ext_snoc hm
        have ext1 := e1.heap_extends
        have ext2 := e2.heap_extends
        subst hc hr hm
        obtain ⟨Ef, Ea, hXe, hf, hx⟩ := hX.app_of_load ld
        obtain ⟨addr, he, hcell⟩ := hX.cell_of_load ld
        subst hXe he
        obtain ⟨t1, c1⟩ := ih _ _ _ _ _ _ cert_lt_calls e1 rfl _ Ef rfl hf ha hv
        obtain ⟨t2, c2⟩ := ih _ _ _ _ _ _ cert_lt_calls e2 rfl _ Ea rfl (hx.mono ext1)
          (Bytes.repAddressRef_heapMono₂ addrTy ext1 ha) (hv.mono ext1)
        refine ⟨?_, fun h₂ ext x hin => ?_⟩
        · show TmR κ _ (.app (Expr.substConstAll (κ (ixAddr b)) val Ef)
            (Expr.substConstAll (κ (ixAddr b)) val Ea)) _
          exact .app (by simp) ((t1.mono ext2).mono ext3) (t2.mono ext3)
        have hnew := ext.getElem?_eq (cert_snoc_cell (h := m₂)
          (x := .construct "KernelTypes::KExprNode" "App" [r₁, r₂]))
        have hc₂ := ((ext1.trans ext2).trans (ext3.trans ext)).getElem?_eq hcell
        rcases addrIn_app_inv hnew hin with h1 | h1
        · rcases c1 h₂ (ext2.trans (ext3.trans ext)) x h1 with hv' | ⟨hf', hne⟩ | hp
          · exact Or.inl hv'
          · exact Or.inr (Or.inl ⟨.appFn hc₂ hf', hne⟩)
          · exact Or.inr (Or.inr (.appFn hc₂ hp))
        · rcases c2 h₂ (ext3.trans ext) x h1 with hv' | ⟨hf', hne⟩ | hp
          · exact Or.inl hv'
          · exact Or.inr (Or.inl ⟨.appArg hc₂ hf', hne⟩)
          · exact Or.inr (Or.inr (.appArg hc₂ hp))
      | .Lam (m316 := m₂) (v276 := r₁) (v277 := r₂) (x_bl := xbl) (ld12 := ld) (he272 := hr)
          (hm271 := hm) (ev290 := e1) (ev326 := e2) (hc358 := hc) .. =>
        have ext3 := cert_ext_snoc hm
        have ext1 := e1.heap_extends
        have ext2 := e2.heap_extends
        subst hc hr hm
        obtain ⟨T, B, ℓ, hXe, ht, hb, hl⟩ := hX.lam_of_load ld
        obtain ⟨addr, he, hcell⟩ := hX.cell_of_load ld
        subst hXe he
        obtain ⟨t1, c1⟩ := ih _ _ _ _ _ _ cert_lt_calls e1 rfl _ T rfl ht ha hv
        obtain ⟨t2, c2⟩ := ih _ _ _ _ _ _ cert_lt_calls e2 rfl _ B rfl (hb.mono ext1)
          (Bytes.repAddressRef_heapMono₂ addrTy ext1 ha) (hv.mono ext1)
        refine ⟨?_, fun h₂ ext x hin => ?_⟩
        · show TmR κ _ (.lam (Expr.substConstAll (κ (ixAddr b)) val T)
            (Expr.substConstAll (κ (ixAddr b)) val B) (bmeta ℓ)) _
          exact .lam (by simp) ((t1.mono ext2).mono ext3) (t2.mono ext3)
            (hl.mono ((ext1.trans ext2).trans ext3))
        · have hnew := ext.getElem?_eq (cert_snoc_cell (h := m₂)
            (x := .construct "KernelTypes::KExprNode" "Lam" [r₁, r₂, xbl]))
          have hc₂ := ((ext1.trans ext2).trans (ext3.trans ext)).getElem?_eq hcell
          rcases addrIn_lam_inv hnew hin with h1 | h1
          · rcases c1 h₂ (ext2.trans (ext3.trans ext)) x h1 with hv' | ⟨hf', hne⟩ | hp
            · exact Or.inl hv'
            · exact Or.inr (Or.inl ⟨.lamTy hc₂ hf', hne⟩)
            · exact Or.inr (Or.inr (.lamTy hc₂ hp))
          · rcases c2 h₂ (ext3.trans ext) x h1 with hv' | ⟨hf', hne⟩ | hp
            · exact Or.inl hv'
            · exact Or.inr (Or.inl ⟨.lamBody hc₂ hf', hne⟩)
            · exact Or.inr (Or.inr (.lamBody hc₂ hp))
      | .Forall (m429 := m₂) (v389 := r₁) (v390 := r₂) (x_bl := xbl) (ld12 := ld)
          (he385 := hr) (hm384 := hm) (ev403 := e1) (ev439 := e2) (hc471 := hc) .. =>
        have ext3 := cert_ext_snoc hm
        have ext1 := e1.heap_extends
        have ext2 := e2.heap_extends
        subst hc hr hm
        obtain ⟨T, B, ℓ, hXe, ht, hb, hl⟩ := hX.forallE_of_load ld
        obtain ⟨addr, he, hcell⟩ := hX.cell_of_load ld
        subst hXe he
        obtain ⟨t1, c1⟩ := ih _ _ _ _ _ _ cert_lt_calls e1 rfl _ T rfl ht ha hv
        obtain ⟨t2, c2⟩ := ih _ _ _ _ _ _ cert_lt_calls e2 rfl _ B rfl (hb.mono ext1)
          (Bytes.repAddressRef_heapMono₂ addrTy ext1 ha) (hv.mono ext1)
        refine ⟨?_, fun h₂ ext x hin => ?_⟩
        · show TmR κ _ (.forallE (Expr.substConstAll (κ (ixAddr b)) val T)
            (Expr.substConstAll (κ (ixAddr b)) val B) (bmeta ℓ)) _
          exact .forallE (by simp) ((t1.mono ext2).mono ext3) (t2.mono ext3)
            (hl.mono ((ext1.trans ext2).trans ext3))
        · have hnew := ext.getElem?_eq (cert_snoc_cell (h := m₂)
            (x := .construct "KernelTypes::KExprNode" "Forall" [r₁, r₂, xbl]))
          have hc₂ := ((ext1.trans ext2).trans (ext3.trans ext)).getElem?_eq hcell
          rcases addrIn_forall_inv hnew hin with h1 | h1
          · rcases c1 h₂ (ext2.trans (ext3.trans ext)) x h1 with hv' | ⟨hf', hne⟩ | hp
            · exact Or.inl hv'
            · exact Or.inr (Or.inl ⟨.forallTy hc₂ hf', hne⟩)
            · exact Or.inr (Or.inr (.forallTy hc₂ hp))
          · rcases c2 h₂ (ext3.trans ext) x h1 with hv' | ⟨hf', hne⟩ | hp
            · exact Or.inl hv'
            · exact Or.inr (Or.inl ⟨.forallBody hc₂ hf', hne⟩)
            · exact Or.inr (Or.inr (.forallBody hc₂ hp))
      | .Let (m578 := m₂) (v502 := r₁) (v503 := r₂) (v504 := r₃) (ld12 := ld) (he498 := hr)
          (hm497 := hm) (ev516 := e1) (ev552 := e2) (ev588 := e3) (hc613 := hc) .. =>
        have ext4 := cert_ext_snoc hm
        have ext1 := e1.heap_extends
        have ext2 := e2.heap_extends
        have ext3 := e3.heap_extends
        subst hc hr hm
        obtain ⟨T, V, B, hXe, ht, hvv, hb⟩ := hX.letE_of_load ld
        obtain ⟨addr, he, hcell⟩ := hX.cell_of_load ld
        subst hXe he
        obtain ⟨t1, c1⟩ := ih _ _ _ _ _ _ cert_lt_calls e1 rfl _ T rfl ht ha hv
        obtain ⟨t2, c2⟩ := ih _ _ _ _ _ _ cert_lt_calls e2 rfl _ V rfl (hvv.mono ext1)
          (Bytes.repAddressRef_heapMono₂ addrTy ext1 ha) (hv.mono ext1)
        obtain ⟨t3, c3⟩ := ih _ _ _ _ _ _ cert_lt_calls e3 rfl _ B rfl (hb.mono (ext1.trans ext2))
          (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) ha)
          (hv.mono (ext1.trans ext2))
        refine ⟨?_, fun h₂ ext x hin => ?_⟩
        · rw [OpOpen.substConstAll_instShift hvc]
          exact .letE (by simp) (((t1.mono ext2).mono ext3).mono ext4) ((t2.mono ext3).mono ext4)
            (t3.mono ext4)
        · have hnew := ext.getElem?_eq (cert_snoc_cell (h := m₂)
            (x := .construct "KernelTypes::KExprNode" "Let" [r₁, r₂, r₃]))
          have hc₂ := ((ext1.trans ext2).trans (ext3.trans (ext4.trans ext))).getElem?_eq hcell
          rcases addrIn_let_inv hnew hin with h1 | h1 | h1
          · rcases c1 h₂ (ext2.trans (ext3.trans (ext4.trans ext))) x h1 with
              hv' | ⟨hf', hne⟩ | hp
            · exact Or.inl hv'
            · exact Or.inr (Or.inl ⟨.letTy hc₂ hf', hne⟩)
            · exact Or.inr (Or.inr (.letTy hc₂ hp))
          · rcases c2 h₂ (ext3.trans (ext4.trans ext)) x h1 with hv' | ⟨hf', hne⟩ | hp
            · exact Or.inl hv'
            · exact Or.inr (Or.inl ⟨.letVal hc₂ hf', hne⟩)
            · exact Or.inr (Or.inr (.letVal hc₂ hp))
          · rcases c3 h₂ (ext4.trans ext) x h1 with hv' | ⟨hf', hne⟩ | hp
            · exact Or.inl hv'
            · exact Or.inr (Or.inl ⟨.letBody hc₂ hf', hne⟩)
            · exact Or.inr (Or.inr (.letBody hc₂ hp))
      | .Proj (m662 := m₂) (v646 := r₁) (x_s := xs) (x_i := xi) (ld12 := ld) (he640 := hr)
          (ev_fcagpdzw := aeq) (hm639 := hm) (ev672 := e1) (hc697 := hc) .. =>
        have ext2 := cert_ext_snoc hm
        have ext0 := aeq.heap_extends
        have ext1 := ext0.trans e1.heap_extends
        subst hc hr hm
        obtain ⟨s, i, Es, hxi, hXe, ra, hes, hres, hperm⟩ := hX.proj_of_load ld
        obtain ⟨addr, he, hcell⟩ := hX.cell_of_load ld
        subst hxi hXe he
        obtain ⟨t1, c1⟩ := ih _ _ _ _ _ _ cert_lt_calls e1 rfl _ Es rfl (hes.mono ext0)
          (Bytes.repAddressRef_heapMono₂ addrTy ext0 ha) (hv.mono ext0)
        refine ⟨?_, fun h₂ ext x hin => ?_⟩
        · show TmR κ _ (.proj (κ (ixAddr s)) (ZMod.val i)
            (Expr.substConstAll (κ (ixAddr b)) val Es)) _
          exact .proj (by simp) (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) ra)
            (t1.mono ext2)
        · have hnew := ext.getElem?_eq (cert_snoc_cell (h := m₂)
            (x := .construct "KernelTypes::KExprNode" "Proj" [xs, .field i, r₁]))
          have hc₂ := (ext1.trans (ext2.trans ext)).getElem?_eq hcell
          have ra₂ := Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans (ext2.trans ext)) ra
          rcases addrIn_proj_inv hnew hin with h1 | h1
          · have e' : s = x := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra₂ h1
            subst e'
            exact Or.inr (Or.inr (.head hc₂ ra₂))
          · rcases c1 h₂ (ext2.trans ext) x h1 with hv' | ⟨hf', hne⟩ | hp
            · exact Or.inl hv'
            · exact Or.inr (Or.inl ⟨.projArg hc₂ hf', hne⟩)
            · exact Or.inr (Or.inr (.projArg hc₂ hp))
      | .other (ld12 := ld) (hne146 := n1) (hne246 := n2) (hne359 := n3) (hne472 := n4)
          (hne614 := n5) (hne698 := n6) (he703 := hr) (he704 := hh) .. =>
        subst hr hh
        cases hX with
        | bvar cell hs =>
          exact ⟨.bvar cell hs, fun h₂ ext x hin =>
            (addrIn_none (ext.getElem?_eq cell) (by decide) hin).elim⟩
        | sort cell rl =>
          exact ⟨.sort cell rl, fun h₂ ext x hin =>
            (addrIn_none (ext.getElem?_eq cell) (by decide) hin).elim⟩
        | litNat cell rl hc =>
          exact ⟨.litNat cell rl hc, fun h₂ ext x hin =>
            (addrIn_none (ext.getElem?_eq cell) (by decide) hin).elim⟩
        | litStr cell rb hs =>
          exact ⟨.litStr cell rb hs, fun h₂ ext x hin =>
            (addrIn_none (ext.getElem?_eq cell) (by decide) hin).elim⟩
        | const cell =>
          exact (n1 _ rfl (Option.some.inj ((cert_cell_load cell ld).symm.trans cell))).elim
        | app cell =>
          exact (n2 _ rfl (Option.some.inj ((cert_cell_load cell ld).symm.trans cell))).elim
        | lam cell =>
          exact (n3 _ rfl (Option.some.inj ((cert_cell_load cell ld).symm.trans cell))).elim
        | forallE cell =>
          exact (n4 _ rfl (Option.some.inj ((cert_cell_load cell ld).symm.trans cell))).elim
        | letE cell =>
          exact (n5 _ rfl (Option.some.inj ((cert_cell_load cell ld).symm.trans cell))).elim
        | proj cell =>
          exact (n6 _ rfl (Option.some.inj ((cert_cell_load cell ld).symm.trans cell))).elim)

/-- **`KernelSubst::subst_const(e, a, v)` on a reading** (module docstring): the result reads as
`e`'s term with the constant at `a`'s key, at no universe level, replaced by the closed value
`val`, when no other address has that key; and a cell of the result, at any later heap, is a
cell of `v`, a cell of `e` other than `b`, or the head of a projection cell of `e`. -/
theorem subst_const_raw {κ : _root_.Address → KKey} {h h' : Heap F} {X val : KExpr}
    {e a v r : SourceValue F} {b : Bytes.Address} {cs : List (Call F)}
    (hinj : ∀ b', κ (ixAddr b') = κ (ixAddr b) → b' = b) (hvc : val.looseBVarsBounded 0 = true)
    (ha : Bytes.RepAddressRef addrTy h b a) (hv : TmR κ h val v) (hX : TmR κ h X e)
    (ev : ObsFn W "KernelSubst::subst_const" [e, a, v] h r h' cs) :
    TmR κ h' (Expr.substConstAll (κ (ixAddr b)) val X) r ∧ Heap.Extends h h' ∧
      ∀ h₂, Heap.Extends h' h₂ → ∀ x, AddrIn h₂ r x →
        AddrIn h₂ v x ∨ (AddrIn h₂ e x ∧ x ≠ b) ∨ ProjIn h₂ e x := by
  obtain ⟨t, c⟩ := subst_const_raw_aux κ a v b val hvc hinj _ _ _ _ _ _ ev rfl e X rfl hX ha hv
  exact ⟨t, ev.heap_extends, c⟩

/-! ## `KernelCheck::validate_expr_well_scoped` on a reading -/

/-- `validate_univ_params_seen(l, nl)` on a converted level: its parameters are below `2^32`. -/
theorem raw_univ_params_seen {h : Heap F} {u : KLevel} {pu : SourceValue F}
    (hu : Ingress.RawKLevel h u pu) :
    ∀ {nl : Nat} {h₁ h₂ : Heap F} {r : SourceValue F} {cs : List (Call F)},
      Heap.Extends h h₁ →
      ObsFn W "KernelCheck::validate_univ_params_seen" [pu, .field (nl : F)] h₁ r h₂ cs →
      KernelLevels.ParamsLt 4294967296 u := by
  induction hu with
  | zero cell => intros; trivial
  | succ cell _ ih =>
    intro nl h₁ h₂ r cs ext ev
    have cell₁ := ext.getElem?_eq cell
    rcases Obs.«KernelCheck::validate_univ_params_seen».obs ev with
      ⟨ld12, _, _, _⟩ | ⟨x_inner, cs40, ld12, ev42, hc59⟩ |
      ⟨x_a, x_b, v77, m78, cs88, cs110, ld12, ev90, ev112, hc129⟩ |
      ⟨x_a, x_b, v147, m148, cs158, cs180, ld12, ev160, ev182, hc199⟩ |
      ⟨x_i, v223, m226, cs234, ld12, ev236, heq259, _, _, _⟩
    all_goals try exact (load_cell_ne cell₁ ld12 (by decide)).elim
    obtain ⟨-, hxs⟩ := load_cell cell₁ ld12
    injection hxs with hx
    subst hx
    exact ih ext ev42
  | max cell _ _ ihl ihr =>
    intro nl h₁ h₂ r cs ext ev
    have cell₁ := ext.getElem?_eq cell
    rcases Obs.«KernelCheck::validate_univ_params_seen».obs ev with
      ⟨ld12, _, _, _⟩ | ⟨x_inner, cs40, ld12, ev42, hc59⟩ |
      ⟨x_a, x_b, v77, m78, cs88, cs110, ld12, ev90, ev112, hc129⟩ |
      ⟨x_a, x_b, v147, m148, cs158, cs180, ld12, ev160, ev182, hc199⟩ |
      ⟨x_i, v223, m226, cs234, ld12, ev236, heq259, _, _, _⟩
    all_goals try exact (load_cell_ne cell₁ ld12 (by decide)).elim
    obtain ⟨-, hxs⟩ := load_cell cell₁ ld12
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl⟩ := hxs
    exact ⟨ihl ext ev90, ihr (ext.trans ev90.heap_extends) ev112⟩
  | imax cell _ _ ihl ihr =>
    intro nl h₁ h₂ r cs ext ev
    have cell₁ := ext.getElem?_eq cell
    rcases Obs.«KernelCheck::validate_univ_params_seen».obs ev with
      ⟨ld12, _, _, _⟩ | ⟨x_inner, cs40, ld12, ev42, hc59⟩ |
      ⟨x_a, x_b, v77, m78, cs88, cs110, ld12, ev90, ev112, hc129⟩ |
      ⟨x_a, x_b, v147, m148, cs158, cs180, ld12, ev160, ev182, hc199⟩ |
      ⟨x_i, v223, m226, cs234, ld12, ev236, heq259, _, _, _⟩
    all_goals try exact (load_cell_ne cell₁ ld12 (by decide)).elim
    obtain ⟨-, hxs⟩ := load_cell cell₁ ld12
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl⟩ := hxs
    exact ⟨ihl ext ev160, ihr (ext.trans ev160.heap_extends) ev182⟩
  | param hn cell =>
    intro nl h₁ h₂ r cs ext ev
    have cell₁ := ext.getElem?_eq cell
    rcases Obs.«KernelCheck::validate_univ_params_seen».obs ev with
      ⟨ld12, _, _, _⟩ | ⟨x_inner, cs40, ld12, ev42, hc59⟩ |
      ⟨x_a, x_b, v77, m78, cs88, cs110, ld12, ev90, ev112, hc129⟩ |
      ⟨x_a, x_b, v147, m148, cs158, cs180, ld12, ev160, ev182, hc199⟩ |
      ⟨x_i, v223, m226, cs234, ld12, ev236, heq259, _, _, _⟩
    all_goals try exact (load_cell_ne cell₁ ld12 (by decide)).elim
    obtain ⟨-, hxs⟩ := load_cell cell₁ ld12
    injection hxs with hx
    subst hx
    obtain ⟨hlt, -, -, -, -⟩ := Lib.less_than_fields_field ev236
    rw [cert_val_lt hn] at hlt
    exact hlt

/-- `validate_univ_params_list(ls, nl)` on converted levels: their parameters are below `2^32`. -/
theorem raw_univ_params_list {us : List KLevel} :
    ∀ {h : Heap F} {pus : SourceValue F}, Ingress.RawKLevelList h us pus →
      ∀ {nl : Nat} {h₁ h₂ : Heap F} {r : SourceValue F} {cs : List (Call F)},
        Heap.Extends h h₁ →
        ObsFn W "KernelCheck::validate_univ_params_list" [pus, .field (nl : F)] h₁ r h₂ cs →
        ∀ l ∈ us, KernelLevels.ParamsLt 4294967296 l := by
  induction us with
  | nil => intros; simp_all
  | cons u rest ih =>
    intro h pus hus nl h₁ h₂ r cs ext ev
    have hrep : RepList Core.klevelListEnum Ingress.RawKLevel h₁ (u :: rest) pus :=
      Ingress.RawKLevelList.mono ext hus
    rcases Obs.«KernelCheck::validate_univ_params_list».obs ev with
      ⟨ld12, _, _, _⟩ | ⟨x_u, x_rest, v42, m43, cs53, cs75, ld12, ev55, ev77, hc94⟩
    · have hn := Core.RepList.nil_of_load hrep ld12
      cases hn
    · obtain ⟨u', rest', heq, hu, hrest⟩ := Core.RepList.cons_of_load hrep ld12
      injection heq with e1 e2
      subst e1 e2
      have hrest' : Ingress.RawKLevelList h₁ rest x_rest := hrest
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact raw_univ_params_seen hu (Heap.Extends.refl _) ev55
      · exact ih hrest' ev55.heap_extends ev77 l hl

/-- **`validate_expr_well_scoped(p, j, nl)` on a reading** (module docstring): the pointer
represents the term exactly at local depth `j`, under any ghost context. -/
theorem TmR.lower {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr} {p : SourceValue F}
    (rep : TmR κ h E p) (Γ : Nat → KExpr) :
    ∀ {j nl : Nat} {h₁ h₂ : Heap F} {r : SourceValue F} {cs : List (Call F)},
      Heap.Extends h h₁ →
      ObsFn W "KernelCheck::validate_expr_well_scoped" [p, .field (j : F), .field (nl : F)]
        h₁ r h₂ cs →
      Decl.TmExact κ 0 Γ h j E p := by
  induction rep with
  | bvar cell hs =>
    intro j nl h₁ h₂ r cs ext ev
    have cell₁ := ext.getElem?_eq cell
    rcases Obs.«KernelCheck::validate_expr_well_scoped».obs ev with
      ⟨x_i, v36, m39, cs47, ld12, ev49, heq72, _, _, _⟩ | ⟨_, _, ld12, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, ld12, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, ld12, _, _, _⟩ | ⟨_, _, _, _, ld12, _, _⟩
    all_goals try exact (load_cell_ne cell₁ ld12 (by decide)).elim
    obtain ⟨-, hxs⟩ := load_cell cell₁ ld12
    injection hxs with hx
    subst hx heq72
    obtain ⟨-, -, hlt, -, -⟩ := Lib.less_than_fields_field ev49
    have h1 := hlt.mp rfl
    have h2 : ZMod.val (j : F) ≤ j := by rw [ZMod.val_natCast]; exact Nat.mod_le _ _
    exact .bvarLocal cell hs (by omega)
  | sort cell rl =>
    intro j nl h₁ h₂ r cs ext ev
    have cell₁ := ext.getElem?_eq cell
    rcases Obs.«KernelCheck::validate_expr_well_scoped».obs ev with
      ⟨_, _, _, _, ld12, _, _, _, _, _⟩ | ⟨x_l, cs93, ld12, ev95, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, ld12, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, ld12, _, _, _⟩ | ⟨_, _, _, _, ld12, _, _⟩
    all_goals try exact (load_cell_ne cell₁ ld12 (by decide)).elim
    obtain ⟨-, hxs⟩ := load_cell cell₁ ld12
    injection hxs with hx
    subst hx
    exact .sort cell (rl.toRepKLevel (raw_univ_params_seen rl ext ev95))
  | const cell ra rls =>
    intro j nl h₁ h₂ r cs ext ev
    have cell₁ := ext.getElem?_eq cell
    rcases Obs.«KernelCheck::validate_expr_well_scoped».obs ev with
      ⟨_, _, _, _, ld12, _, _, _, _, _⟩ | ⟨_, _, ld12, _, _⟩ |
      ⟨x_addr, x_lvls, v130, m131, p138, cs144, v155, m156, cs166, v188, m191, cs199, cs221,
        ld12, ev146, _, ev168, ev201, _, ev223, _⟩ |
      ⟨_, _, _, _, _, _, ld12, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, ld12, _, _, _⟩ | ⟨_, _, _, _, ld12, _, _⟩
    all_goals try exact (load_cell_ne cell₁ ld12 (by decide)).elim
    obtain ⟨-, hxs⟩ := load_cell cell₁ ld12
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl⟩ := hxs
    have e1 := ev146.heap_extends.trans (ev168.heap_extends.trans ev201.heap_extends)
    exact .const cell ra (rls.toRepKLevelList (raw_univ_params_list rls (ext.trans e1) ev223))
  | app cell _ _ ihf iha =>
    intro j nl h₁ h₂ r cs ext ev
    have cell₁ := ext.getElem?_eq cell
    rcases Obs.«KernelCheck::validate_expr_well_scoped».obs ev with
      ⟨_, _, _, _, ld12, _, _, _, _, _⟩ | ⟨_, _, ld12, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _, _⟩ |
      ⟨x_f, x_a, v258, m259, cs269, cs299, ld12, ev271, ev301, hc326⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, ld12, _, _, _⟩ | ⟨_, _, _, _, ld12, _, _⟩
    all_goals try exact (load_cell_ne cell₁ ld12 (by decide)).elim
    obtain ⟨-, hxs⟩ := load_cell cell₁ ld12
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl⟩ := hxs
    exact .app cell (ihf ext ev271) (iha (ext.trans ev271.heap_extends) ev301)
  | lam cell _ _ rl iht ihb =>
    intro j nl h₁ h₂ r cs ext ev
    have cell₁ := ext.getElem?_eq cell
    rcases Obs.«KernelCheck::validate_expr_well_scoped».obs ev with
      ⟨_, _, _, _, ld12, _, _, _, _, _⟩ | ⟨_, _, ld12, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, ld12, _, _, _⟩ |
      ⟨x_t, x_b, x_l, v349, m350, cs360, v379, m380, cs390, cs420, v424,
        ld12, ev362, ev392, op446, ev422, hc455⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, ld12, _, _, _⟩ | ⟨_, _, _, _, ld12, _, _⟩
    all_goals try exact (load_cell_ne cell₁ ld12 (by decide)).elim
    obtain ⟨-, hxs⟩ := load_cell cell₁ ld12
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl, rfl⟩ := hxs
    have hv : v424 = .field ((j + 1 : Nat) : F) := by
      simp only [evalBinOp, Except.ok.injEq] at op446
      rw [← op446]
      push_cast
      rfl
    rw [hv] at ev422
    have e1 := ev362.heap_extends
    have e2 := ev392.heap_extends
    exact .lam cell (iht (ext.trans e1) ev392) (ihb (ext.trans (e1.trans e2)) ev422) rl
  | forallE cell _ _ rl iht ihb =>
    intro j nl h₁ h₂ r cs ext ev
    have cell₁ := ext.getElem?_eq cell
    rcases Obs.«KernelCheck::validate_expr_well_scoped».obs ev with
      ⟨_, _, _, _, ld12, _, _, _, _, _⟩ | ⟨_, _, ld12, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, ld12, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨x_t, x_b, x_l, v478, m479, cs489, v508, m509, cs519, cs549, v553,
        ld12, ev491, ev521, op575, ev551, hc584⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, ld12, _, _, _⟩ | ⟨_, _, _, _, ld12, _, _⟩
    all_goals try exact (load_cell_ne cell₁ ld12 (by decide)).elim
    obtain ⟨-, hxs⟩ := load_cell cell₁ ld12
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl, rfl⟩ := hxs
    have hv : v553 = .field ((j + 1 : Nat) : F) := by
      simp only [evalBinOp, Except.ok.injEq] at op575
      rw [← op575]
      push_cast
      rfl
    rw [hv] at ev551
    have e1 := ev491.heap_extends
    have e2 := ev521.heap_extends
    exact .forallE cell (iht (ext.trans e1) ev521) (ihb (ext.trans (e1.trans e2)) ev551) rl
  | letE cell _ _ _ iht ihv ihb =>
    intro j nl h₁ h₂ r cs ext ev
    have cell₁ := ext.getElem?_eq cell
    rcases Obs.«KernelCheck::validate_expr_well_scoped».obs ev with
      ⟨_, _, _, _, ld12, _, _, _, _, _⟩ | ⟨_, _, ld12, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, ld12, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨x_t, x_v, x_b, v607, m608, cs618, v645, m646, cs656, cs686, v690,
        ld12, ev620, ev658, op712, ev688, hc721⟩ |
      ⟨_, ld12, _, _, _⟩ | ⟨_, _, _, _, ld12, _, _⟩
    all_goals try exact (load_cell_ne cell₁ ld12 (by decide)).elim
    obtain ⟨-, hxs⟩ := load_cell cell₁ ld12
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl, rfl⟩ := hxs
    have hv : v690 = .field ((j + 1 : Nat) : F) := by
      simp only [evalBinOp, Except.ok.injEq] at op712
      rw [← op712]
      push_cast
      rfl
    rw [hv] at ev688
    have e1 := ev620.heap_extends
    have e2 := ev658.heap_extends
    exact .letE cell (iht ext ev620) (ihv (ext.trans e1) ev658)
      (ihb (ext.trans (e1.trans e2)) ev688)
  | litNat cell rl hc =>
    intro j nl h₁ h₂ r cs ext ev
    exact .litNat cell rl hc
  | litStr cell rb hs =>
    intro j nl h₁ h₂ r cs ext ev
    exact .litStr cell rb hs
  | proj cell ra _ ihe =>
    intro j nl h₁ h₂ r cs ext ev
    have cell₁ := ext.getElem?_eq cell
    rcases Obs.«KernelCheck::validate_expr_well_scoped».obs ev with
      ⟨_, _, _, _, ld12, _, _, _, _, _⟩ | ⟨_, _, ld12, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, ld12, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, ld12, _, _, _⟩ | ⟨_, _, x_e1, cs767, ld12, ev769, hc794⟩
    all_goals try exact (load_cell_ne cell₁ ld12 (by decide)).elim
    obtain ⟨-, hxs⟩ := load_cell cell₁ ld12
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨-, -, rfl⟩ := hxs
    exact .proj cell ra (ihe ext ev769)

/-- **`validate_expr_well_scoped(p, 0, 0)` on a reading**: the pointer represents the term as a
closed term, and the term has no level parameter. -/
theorem TmR.closed_of_scope {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr}
    {p : SourceValue F} (rep : TmR κ h E p) {h₁ h₂ : Heap F} {r : SourceValue F}
    {cs : List (Call F)} (ext : Heap.Extends h h₁)
    (ev : ObsFn W "KernelCheck::validate_expr_well_scoped" [p, .field 0, .field 0] h₁ r h₂ cs) :
    TmC κ h E p ∧ E.allLevelParamsDefined [] = true := by
  have ev' : ObsFn W "KernelCheck::validate_expr_well_scoped"
      [p, .field ((0 : Nat) : F), .field ((0 : Nat) : F)] h₁ r h₂ cs := by
    simpa using ev
  have hx : ∀ Γ, Decl.TmExact κ 0 Γ h 0 E p := fun Γ => rep.lower Γ ext ev'
  refine ⟨fun d Γ => (hx Γ).toTm.of_depth_zero d, ?_⟩
  have hl := Decl.validate_expr_well_scoped_spec (Γ := fun _ => .sort .zero) (nl := 0)
    (by decide) ((hx _).mono ext) ev'
  simpa using hl

end IxVM.Refinement.Binding
