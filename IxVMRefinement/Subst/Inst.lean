import IxVMRefinement.Subst.Lift

/-! # Instantiation: `expr_inst1*`, `expr_inst_many*`

`expr_inst1(e, arg, j)` is the kernel's `instantiate1` at index `j` of a term read at local
depth `j + 1`, with a top-level argument (no loose bound variable, so the kernel's non-lifting
substitution and IxVM's, which lifts the argument by `j`, agree). `expr_inst_many(e, substs, j)`
is `instantiateList`. Each first compares `j` with `expr_lbr(e)` (a term with no index at or
above `j` is returned as it is), then tests whether the substituted indices occur at all (if
not, it lowers); only then it walks. A `Let` node's image is `instShift`, which commutes with
both instantiations on closed values (`instShift_instantiate1`, `instShift_instantiateList`). -/

namespace IxVM.Refinement.Core.SubstAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency (Bounded)
open Specs.Subst (IdxAll IdxLt NoIdx NoIdxF BVarIm idxBound)

set_option linter.unusedVariables false

local macro "lt_calls" : term => `(by simp <;> omega)
local macro "sub_calls" : term => `(fun _ hx => by simp [hx])

/-! ## Lists of terms -/

theorem klength {α : Type} {R : Heap F → α → SourceValue F → Prop} {xs : List α}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) : r = .field (xs.length : F) ∧ h' = h := by
  have ev' : ObsFn W (Instance.mk "Lists::length" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      [l] h r h' cs := by
    rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev
  have hl' : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      R h xs l := by
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl
  exact Lib.Lists.length_spec ev' hl'

theorem klookup {α : Type} {R : Heap F → α → SourceValue F → Prop} {xs : List α}
    {l r : SourceValue F} {i : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [l, .field i] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    (∃ x, xs[ZMod.val i]? = some x ∧ R h x r) ∧ h' = h := by
  have ev' : ObsFn W (Instance.mk "Lists::lookup" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      [l, .field i] h r h' cs := by
    rw [Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol]; exact ev
  have hl' : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      R h xs l := by
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl
  exact Lib.Lists.lookup_spec ev' hl'

/-- The terms of a list of top-level terms have no loose bound variable. -/
theorem tmL_closed {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F} :
    ∀ {As : List KExpr} {p : SourceValue F}, TmL κ d Γ h As p →
      ∀ A ∈ As, A.looseBVarsBounded 0 = true := by
  intro As p hl
  induction hl with
  | nil _ => intro A hA; simp at hA
  | cons _ hx _ ih =>
    intro A hA
    rcases List.mem_cons.mp hA with rfl | hA
    · exact Tm.looseBVarsBounded hx
    · exact ih A hA

theorem tmL_mono {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h₁ h₂ : Heap F}
    {As : List KExpr} {p : SourceValue F} (ext : Heap.Extends h₁ h₂) (hl : TmL κ d Γ h₁ As p) :
    TmL κ d Γ h₂ As p :=
  TmL.mono ext hl

/-- A field difference below `2^32` of a minuend and a subtrahend below `2^32` is the natural
difference. -/
theorem val_sub_of_small {i j : F} (hx : ZMod.val (i - j) < 4294967296)
    (hj : ZMod.val j < 4294967296) :
    ZMod.val j ≤ ZMod.val i ∧ ZMod.val (i - j) = ZMod.val i - ZMod.val j := by
  have hsum : ZMod.val (i - j + j) = ZMod.val (i - j) + ZMod.val j :=
    val_add (by have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl; omega)
  rw [sub_add_cancel] at hsum
  omega

/-! ## Kernel facts -/

section Kernel
open Ix.Kernel

theorem inst1_bvar_lt {A : KExpr} {i j : Nat} (h : i < j) :
    (Expr.bvar i : KExpr).instantiate1 A j = .bvar i := by
  have h1 : i ≠ j := by omega
  have h2 : ¬ j < i := by omega
  simp [Expr.instantiate1, h1, h2]

theorem inst1_bvar_self {A : KExpr} {j : Nat} : (Expr.bvar j : KExpr).instantiate1 A j = A := by
  simp [Expr.instantiate1]

theorem iL_bvar_mid {As : List KExpr} {i j : Nat} (hc : ∀ A ∈ As, A.looseBVarsBounded 0 = true)
    (hji : j ≤ i) (hlt : i - j < As.length) :
    (Expr.bvar i : KExpr).instantiateList As j = As[i - j] := by
  have h1 : ¬ i < j := by omega
  simp [Expr.instantiateList, h1, hlt]
  exact Expr.instantiateList_eq_self (lbb_mono (Nat.zero_le j) (hc _ (by simp)))

theorem iL_bvar_ge {As : List KExpr} {i j : Nat} (hge : j + As.length ≤ i) :
    (Expr.bvar i : KExpr).instantiateList As j = .bvar (i - As.length) := by
  have h1 : ¬ i < j := by omega
  have h2 : ¬ i - j < As.length := by omega
  simp [Expr.instantiateList, h1, h2]

theorem iL_fvar {As : List KExpr} {j x : Nat} {T : KExpr} :
    (Expr.fvar x T : KExpr).instantiateList As j = .fvar x T := by
  simp [Expr.instantiateList]

theorem iL_closed {E : KExpr} (hE : E.looseBVarsBounded 0 = true) (As : List KExpr) (j : Nat) :
    E.instantiateList As j = E :=
  Expr.instantiateList_eq_self (lbb_mono (Nat.zero_le j) hE)

theorem iL_app {As : List KExpr} {j : Nat} {f a : KExpr} :
    (Expr.app f a : KExpr).instantiateList As j = .app (f.instantiateList As j) (a.instantiateList As j) := by
  simp only [Expr.instantiateList]

theorem iL_lam {As : List KExpr} {j : Nat} {T B : KExpr} {m : BinderMeta} :
    (Expr.lam T B m : KExpr).instantiateList As j =
      .lam (T.instantiateList As j) (B.instantiateList As (j + 1)) m := by
  simp only [Expr.instantiateList]

theorem iL_forallE {As : List KExpr} {j : Nat} {T B : KExpr} {m : BinderMeta} :
    (Expr.forallE T B m : KExpr).instantiateList As j =
      .forallE (T.instantiateList As j) (B.instantiateList As (j + 1)) m := by
  simp only [Expr.instantiateList]

theorem iL_proj {As : List KExpr} {j : Nat} {s : KKey} {i : Nat} {e : KExpr} :
    (Expr.proj s i e : KExpr).instantiateList As j = .proj s i (e.instantiateList As j) := by
  simp only [Expr.instantiateList]

end Kernel

/-! ## `expr_inst1` -/

theorem g_expr_inst1_bvar (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_inst1_bvar" args h r h' calls) (ih : GIH κ calls) :
    G.expr_inst1_bvar κ args h r h' calls := by
  intro i arg j hargs bd d Γ B A hB hA
  subst hargs
  obtain ⟨hsm, hcase⟩ := hB
  match Obs.«KernelSubst::expr_inst1_bvar».obs ev with
  | .n1 (ev15 := e1) (he40 := hr) (hm39 := hm) .. =>
    obtain ⟨i', j', hi', hj', -, -, hr', rfl⟩ := ltf e1
    injection hi' with hi'; injection hj' with hj'; subst hi' hj' hr hm
    have hlt := ltf_one hr'.symm
    rcases hcase with ⟨_, rfl⟩ | ⟨hk, _, _⟩
    · rw [inst1_bvar_lt hlt]; exact tm_store_bvarLocal hsm hlt
    · omega
  | .n0_n0 (ev15 := e1) (op74 := op) (ev86 := e2) (hc110 := hc) .. =>
    subst hc
    obtain ⟨i', j', hi', hj', -, hj32, hr', rfl⟩ := ltf e1
    injection hi' with hi'; injection hj' with hj'; subst hi' hj'
    have hij : i = j := by
      have := sub_ok op; injection this with h0; exact (sub_eq_zero.mp h0.symm)
    subst hij
    rcases hcase with ⟨_, rfl⟩ | ⟨hk, hd, _⟩
    · rw [inst1_bvar_self]
      have := ih.get .expr_lift lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) (by omega)
        (ZMod.val i) 0 (by omega) d Γ A (by rw [ZMod.val_zero]; exact hA)
      rw [ZMod.val_zero, Nat.zero_add] at this
      exact this
    · omega
  | .n0_other (ev15 := e1) (op74 := op) (hne111 := hne) (he119 := hr) (hm118 := hm)
      (op137 := op2) (hc139 := hc) .. =>
    subst hc hr hm
    obtain ⟨i', j', hi', hj', hi32, hj32, hr', rfl⟩ := ltf e1
    injection hi' with hi'; injection hj' with hj'; subst hi' hj'
    have hge := ltf_zero hr'.symm
    have hij : i ≠ j := fun hij => hne (by rw [sub_ok op, hij, sub_self])
    have hv : ZMod.val i ≠ ZMod.val j := fun hv => hij (ZMod.val_injective _ hv)
    rw [sub_ok op2]
    have hv1 : ZMod.val (i - 1) = ZMod.val i - 1 := by rw [val_sub (by rw [val_one]; omega), val_one]
    rcases hcase with ⟨hlt, _⟩ | ⟨hk, hd, rfl⟩
    · omega
    · exact tm_store_bvarFree_eq (by omega) (by omega) (by omega) (by rw [hv1]; unfold fvIdx; omega)

theorem g_expr_inst1_let (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_inst1_let" args h r h' calls) (ih : GIH κ calls) :
    G.expr_inst1_let κ args h r h' calls := by
  intro ty val body arg j hargs bd hj0 d Γ T V B A ht hv hb hA
  subst hargs
  match Obs.«KernelSubst::expr_inst1_let».obs ev with
  | .run (he5 := hr) (hm4 := hm) (ev23 := e1) (ev59 := e2) (op126 := op) (ev95 := e3)
      (hc128 := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e3
    have x1 := ih.get .expr_inst1 lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) d Γ T A ht hA
    have x2 := ih.get .expr_inst1 lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) d Γ V A
      (hv.mono e1.heap_extends) (hA.mono e1.heap_extends)
    have x3 := ih.get .expr_inst1 lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) d Γ B A
      (by rw [val_succ32 hj0, show ZMod.val j + 1 + 1 = ZMod.val j + 2 by omega]
          exact hb.mono (e1.heap_extends.trans e2.heap_extends))
      (hA.mono (e1.heap_extends.trans e2.heap_extends))
    rw [val_succ32 hj0] at x3
    rw [instShift_instantiate1 (Tm.looseBVarsBounded hA)]
    exact tm_store_letE ((x1.mono e2.heap_extends).mono e3.heap_extends) (x2.mono e3.heap_extends) x3

theorem g_expr_inst1_walk (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_inst1_walk" args h r h' calls) (ih : GIH κ calls) :
    G.expr_inst1_walk κ args h r h' calls := by
  intro e arg j hargs bd hj0 d Γ E A hE hA
  subst hargs
  match Obs.«KernelSubst::expr_inst1_walk».obs ev with
  | .BVar (ld12 := ld) (ev30 := e1) (hc55 := hc) .. =>
    subst hc
    obtain ⟨i, rfl, hsm, hcase⟩ := Tm.bvar_of_load hE ld
    exact ih.get .expr_inst1_bvar lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) d Γ E A
      ⟨hsm, hcase⟩ hA
  | .Srt (ld12 := ld) (he72 := hr) (hm71 := hm) .. =>
    subst hr hm
    obtain ⟨u, rfl, -⟩ := Tm.sort_of_load hE ld
    exact tm_copy_sort hE ld (Heap.Extends.refl _)
  | .Const (ld12 := ld) (he106 := hr) (hm105 := hm) .. =>
    subst hr hm
    obtain ⟨a, us, rfl, -, -⟩ := Tm.const_of_load hE ld
    exact tm_copy_const hE ld (Heap.Extends.refl _)
  | .Lit (ld12 := ld) (he554 := hr) (hm553 := hm) .. =>
    subst hr hm
    rcases Tm.lit_of_load hE ld with ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ <;>
      exact tm_copy_lit hE ld (Heap.Extends.refl _)
  | .App (ld12 := ld) (he148 := hr) (hm147 := hm) (ev165 := e1) (ev201 := e2) (hc226 := hc) .. =>
    subst hc hr hm
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld
    have sf := ih.get .expr_inst1 lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) d Γ Ef A hf hA
    have sa := ih.get .expr_inst1 lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) d Γ Ea A
      (ha.mono e1.heap_extends) (hA.mono e1.heap_extends)
    exact Tm.store_app (sf.mono e2.heap_extends) sa
  | .Lam (ld12 := ld) (he253 := hr) (hm252 := hm) (ev271 := e1) (op338 := op) (ev307 := e2)
      (hc347 := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e2
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.lam_of_load hE ld
    have st := ih.get .expr_inst1 lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) d Γ T A ht hA
    have sb := ih.get .expr_inst1 lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) d Γ B A
      (by rw [val_succ32 hj0]; exact hb.mono e1.heap_extends) (hA.mono e1.heap_extends)
    rw [val_succ32 hj0] at sb
    exact tm_store_lam (st.mono e2.heap_extends) sb (hl.mono (e1.heap_extends.trans e2.heap_extends))
  | .Forall (ld12 := ld) (he374 := hr) (hm373 := hm) (ev392 := e1) (op459 := op) (ev428 := e2)
      (hc468 := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e2
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.forallE_of_load hE ld
    have st := ih.get .expr_inst1 lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) d Γ T A ht hA
    have sb := ih.get .expr_inst1 lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) d Γ B A
      (by rw [val_succ32 hj0]; exact hb.mono e1.heap_extends) (hA.mono e1.heap_extends)
    rw [val_succ32 hj0] at sb
    exact tm_store_forallE (st.mono e2.heap_extends) sb
      (hl.mono (e1.heap_extends.trans e2.heap_extends))
  | .Let (ld12 := ld) (ev496 := e1) (hc537 := hc) .. =>
    subst hc
    obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := Tm.letE_of_load hE ld
    exact ih.get .expr_inst1_let lt_calls e1 _ _ _ _ _ rfl (bounded_sub sub_calls bd) hj0
      d Γ T V B A ht hv hb hA
  | .Proj (ld12 := ld) (he593 := hr) (hm592 := hm) (ev625 := e1) (hc650 := hc) .. =>
    subst hc hr hm
    obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := Tm.proj_of_load hE ld
    exact tm_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e1.heap_extends ra)
      (ih.get .expr_inst1 lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) d Γ Es A hes hA)

theorem g_expr_inst1 (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_inst1" args h r h' calls) (ih : GIH κ calls) :
    G.expr_inst1 κ args h r h' calls := by
  intro e arg j hargs bd d Γ B A hB hA
  subst hargs
  match Obs.«KernelSubst::expr_inst1».obs ev with
  | .n0 (ev14 := e1) (ev37 := e2) (he59 := hr) (he60 := he) (hc61 := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, sl⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', y, hj', hy, -, -, hr', rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hge := ltf_zero hr'.symm
    obtain ⟨b, hb, b1, -, -, -, lb⟩ := sl d Γ (ZMod.val j + 1) B hB
    rw [hb] at hy; injection hy with hy; subst hy
    rw [val_natCast (lt_mod_of_le_idx b1)] at hge
    obtain ⟨l1, -, l3⟩ := lb (by omega)
    rw [Ix.Kernel.Expr.instantiate1_eq_self (lbb_mono (by omega) l1)]
    exact l3 d Γ (ZMod.val j) (by omega)
  | .n1_n1 (ev14 := e1) (ev37 := e2) (ev81 := e3) (ev107 := e4) (hc132 := hc) .. =>
    subst hc
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', y, hj', -, hj32, -, -, rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    obtain ⟨rfl, -⟩ := ih.get .expr_has_bvar_at lt_calls e3 _ _ rfl (bounded_sub sub_calls bd)
    exact ih.get .expr_inst1_walk lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd) hj32 d Γ B A hB hA
  | .n1_other (ev14 := e1) (ev37 := e2) (ev81 := e3) (hne133 := hne) (op172 := op) (ev142 := e4)
      (hc174 := hc) .. =>
    subst hc
    rw [add_ok op] at e4
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', y, hj', -, hj32, -, -, rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    obtain ⟨rfl, h01, sn⟩ := ih.get .expr_has_bvar_at lt_calls e3 _ _ rfl (bounded_sub sub_calls bd)
    have hn := sn (zero_of_ne_one h01 hne) d Γ (ZMod.val j + 1) B hB
    have hlow := ih.get .expr_lower lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd) 1 0
      (by rw [val_one]) (by rw [val_succ32 hj32]; omega) d Γ B (Nat.zero_le _)
      (by rw [val_succ32 hj32]; exact hB)
      (by rw [val_succ32 hj32, Nat.add_sub_cancel, Nat.add_zero]; exact hn)
    rw [val_succ32 hj32, Nat.add_sub_cancel, Nat.sub_zero] at hlow
    rw [Ix.Kernel.Expr.instantiate1_eq_self (tm_lbb hB (Nat.le_succ _) hn)]
    exact hlow

/-! ## `expr_inst_many` -/

theorem g_expr_inst_many_bvar (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_inst_many_bvar" args h r h' calls) (ih : GIH κ calls) :
    G.expr_inst_many_bvar κ args h r h' calls := by
  intro i substs j hargs bd hj0 d Γ B As hB hAs
  subst hargs
  obtain ⟨hsm, hcase⟩ := hB
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  match Obs.«KernelSubst::expr_inst_many_bvar».obs ev with
  | .n1 (ev14 := e1) (op38 := op) (ev55 := e2) (ev96 := e3) (ev81 := e4) (hc126 := hc) .. =>
    subst hc
    have hlen : As.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [substs], h⟩) (by simp) (by simp) hAs
    obtain ⟨rfl, rfl⟩ := klength e1 hAs
    rw [sub_ok op] at e2 e3
    obtain ⟨x, y, hx, hy, hx32, -, hr', rfl⟩ := ltf e2
    injection hx with hx; injection hy with hy; subst hx hy
    have hlt := ltf_one hr'.symm
    rw [val_natCast (by omega)] at hlt
    obtain ⟨hji, hval⟩ := val_sub_of_small hx32 hj0
    obtain ⟨⟨A, hAget, hA⟩, rfl⟩ := klookup e3 hAs
    rw [hval] at hAget
    have hlift := ih.get .expr_lift lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd) (by omega)
      (ZMod.val j) 0 (by omega) d Γ A (by rw [ZMod.val_zero]; exact hA)
    rw [ZMod.val_zero, Nat.zero_add] at hlift
    rcases hcase with ⟨_, rfl⟩ | ⟨hk, _, _⟩
    · have hlt' : ZMod.val i - ZMod.val j < As.length := by omega
      have hAeq : As[ZMod.val i - ZMod.val j] = A := by
        rw [List.getElem?_eq_getElem hlt'] at hAget; exact Option.some_inj.mp hAget
      rw [iL_bvar_mid (tmL_closed hAs) hji hlt', hAeq]
      exact hlift
    · omega
  | .n0 (ev14 := e1) (op38 := op) (ev55 := e2) (he136 := hr) (hm135 := hm) (op154 := op2)
      (hc157 := hc) .. =>
    subst hc hr hm
    have hlen : As.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [substs], h⟩) (by simp) (by simp) hAs
    obtain ⟨rfl, rfl⟩ := klength e1 hAs
    rw [sub_ok op] at e2
    obtain ⟨x, y, hx, hy, hx32, -, hr', rfl⟩ := ltf e2
    injection hx with hx; injection hy with hy; subst hx hy
    have hge := ltf_zero hr'.symm
    rw [val_natCast (by omega)] at hge
    obtain ⟨hji, hval⟩ := val_sub_of_small hx32 hj0
    rw [sub_ok op2]
    have hv : ZMod.val (i - (As.length : F)) = ZMod.val i - As.length := by
      rw [val_sub (by rw [val_natCast (by omega)]; omega), val_natCast (by omega)]
    rcases hcase with ⟨hlt, _⟩ | ⟨hk, hd, rfl⟩
    · omega
    · rw [iL_fvar]
      exact tm_store_bvarFree_eq (by omega) (by omega) (by omega) (by rw [hv]; unfold fvIdx; omega)

theorem g_expr_inst_many_let (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_inst_many_let" args h r h' calls) (ih : GIH κ calls) :
    G.expr_inst_many_let κ args h r h' calls := by
  intro ty val body substs j hargs bd hj0 d Γ T V B As ht hv hb hAs
  subst hargs
  match Obs.«KernelSubst::expr_inst_many_let».obs ev with
  | .run (he5 := hr) (hm4 := hm) (ev23 := e1) (ev59 := e2) (op126 := op) (ev95 := e3)
      (hc128 := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e3
    have x1 := ih.get .expr_inst_many lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) d Γ T As ht hAs
    have x2 := ih.get .expr_inst_many lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) d Γ V As
      (hv.mono e1.heap_extends) (tmL_mono e1.heap_extends hAs)
    have x3 := ih.get .expr_inst_many lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) d Γ B As
      (by rw [val_succ32 hj0, Nat.add_right_comm]
          exact hb.mono (e1.heap_extends.trans e2.heap_extends))
      (tmL_mono (e1.heap_extends.trans e2.heap_extends) hAs)
    rw [val_succ32 hj0] at x3
    rw [instShift_instantiateList As (tmL_closed hAs)]
    exact tm_store_letE ((x1.mono e2.heap_extends).mono e3.heap_extends) (x2.mono e3.heap_extends) x3

theorem g_expr_inst_many_walk (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_inst_many_walk" args h r h' calls) (ih : GIH κ calls) :
    G.expr_inst_many_walk κ args h r h' calls := by
  intro e substs j hargs bd hj0 d Γ E As hE hAs
  subst hargs
  match Obs.«KernelSubst::expr_inst_many_walk».obs ev with
  | .BVar (ld12 := ld) (ev30 := e1) (hc55 := hc) .. =>
    subst hc
    obtain ⟨i, rfl, hsm, hcase⟩ := Tm.bvar_of_load hE ld
    exact ih.get .expr_inst_many_bvar lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) hj0
      d Γ E As ⟨hsm, hcase⟩ hAs
  | .Srt (ld12 := ld) (he72 := hr) (hm71 := hm) .. =>
    subst hr hm
    obtain ⟨u, rfl, -⟩ := Tm.sort_of_load hE ld
    rw [iL_closed (E := .sort u) rfl]
    exact tm_copy_sort hE ld (Heap.Extends.refl _)
  | .Const (ld12 := ld) (he106 := hr) (hm105 := hm) .. =>
    subst hr hm
    obtain ⟨a, us, rfl, -, -⟩ := Tm.const_of_load hE ld
    rw [iL_closed (E := .const _ us) rfl]
    exact tm_copy_const hE ld (Heap.Extends.refl _)
  | .Lit (ld12 := ld) (he554 := hr) (hm553 := hm) .. =>
    subst hr hm
    rcases Tm.lit_of_load hE ld with ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ <;>
      (rw [iL_closed (E := .lit _) rfl]; exact tm_copy_lit hE ld (Heap.Extends.refl _))
  | .App (ld12 := ld) (he148 := hr) (hm147 := hm) (ev165 := e1) (ev201 := e2) (hc226 := hc) .. =>
    subst hc hr hm
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld
    have sf := ih.get .expr_inst_many lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) d Γ Ef As hf hAs
    have sa := ih.get .expr_inst_many lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) d Γ Ea As
      (ha.mono e1.heap_extends) (tmL_mono e1.heap_extends hAs)
    rw [iL_app]
    exact Tm.store_app (sf.mono e2.heap_extends) sa
  | .Lam (ld12 := ld) (he253 := hr) (hm252 := hm) (ev271 := e1) (op338 := op) (ev307 := e2)
      (hc347 := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e2
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.lam_of_load hE ld
    have st := ih.get .expr_inst_many lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) d Γ T As ht hAs
    have sb := ih.get .expr_inst_many lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) d Γ B As
      (by rw [val_succ32 hj0, Nat.add_right_comm]; exact hb.mono e1.heap_extends)
      (tmL_mono e1.heap_extends hAs)
    rw [val_succ32 hj0] at sb
    rw [iL_lam]
    exact tm_store_lam (st.mono e2.heap_extends) sb (hl.mono (e1.heap_extends.trans e2.heap_extends))
  | .Forall (ld12 := ld) (he374 := hr) (hm373 := hm) (ev392 := e1) (op459 := op) (ev428 := e2)
      (hc468 := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e2
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.forallE_of_load hE ld
    have st := ih.get .expr_inst_many lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) d Γ T As ht hAs
    have sb := ih.get .expr_inst_many lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) d Γ B As
      (by rw [val_succ32 hj0, Nat.add_right_comm]; exact hb.mono e1.heap_extends)
      (tmL_mono e1.heap_extends hAs)
    rw [val_succ32 hj0] at sb
    rw [iL_forallE]
    exact tm_store_forallE (st.mono e2.heap_extends) sb
      (hl.mono (e1.heap_extends.trans e2.heap_extends))
  | .Let (ld12 := ld) (ev496 := e1) (hc537 := hc) .. =>
    subst hc
    obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := Tm.letE_of_load hE ld
    exact ih.get .expr_inst_many_let lt_calls e1 _ _ _ _ _ rfl (bounded_sub sub_calls bd) hj0
      d Γ T V B As ht hv hb hAs
  | .Proj (ld12 := ld) (he593 := hr) (hm592 := hm) (ev625 := e1) (hc650 := hc) .. =>
    subst hc hr hm
    obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := Tm.proj_of_load hE ld
    rw [iL_proj]
    exact tm_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e1.heap_extends ra)
      (ih.get .expr_inst_many lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) d Γ Es As hes hAs)

theorem g_expr_inst_many (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_inst_many" args h r h' calls) (ih : GIH κ calls) :
    G.expr_inst_many κ args h r h' calls := by
  intro e substs j hargs bd d Γ B As hB hAs
  subst hargs
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  match Obs.«KernelSubst::expr_inst_many».obs ev with
  | .n0 (ev14 := e1) (he38 := hr) (he39 := he) (hc40 := hc) .. =>
    subst hc hr he
    have hlen : As.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [substs], h⟩) (by simp) (by simp) hAs
    obtain ⟨h0, rfl⟩ := klength e1 hAs
    injection h0 with h0
    have hz : As.length = 0 := by
      have := congrArg ZMod.val h0; rw [ZMod.val_zero, val_natCast (by omega)] at this; omega
    obtain rfl := List.eq_nil_of_length_eq_zero hz
    rw [Ix.Kernel.Expr.instantiateList_nil]
    exact hB
  | .other_n0 (ev14 := e1) (ev58 := e2) (ev81 := e3) (he103 := hr) (he104 := he) (hc105 := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, rfl⟩ := klength e1 hAs
    obtain ⟨rfl, sl⟩ := ih.get .expr_lbr lt_calls e2 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', y, hj', hy, -, -, hr', rfl⟩ := ltf e3
    injection hj' with hj'; subst hj'
    have hge := ltf_zero hr'.symm
    obtain ⟨b, hb, b1, -, -, -, lb⟩ := sl d Γ (ZMod.val j + As.length) B hB
    rw [hb] at hy; injection hy with hy; subst hy
    rw [val_natCast (lt_mod_of_le_idx b1)] at hge
    obtain ⟨l1, -, l3⟩ := lb (by omega)
    rw [Ix.Kernel.Expr.instantiateList_eq_self (lbb_mono (by omega) l1)]
    exact l3 d Γ (ZMod.val j) (by omega)
  | .other_n1_n1 (ev14 := e1) (ev58 := e2) (ev81 := e3) (op156 := op) (ev125 := e4) (ev168 := e5)
      (hc193 := hc) .. =>
    subst hc
    obtain ⟨rfl, rfl⟩ := klength e1 hAs
    rw [add_ok op] at e4
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e2 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', y, hj', -, hj32, -, -, rfl⟩ := ltf e3
    injection hj' with hj'; subst hj'
    obtain ⟨rfl, -⟩ := ih.get .has_bvar_in_range lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd)
    exact ih.get .expr_inst_many_walk lt_calls e5 _ _ _ rfl (bounded_sub sub_calls bd) hj32
      d Γ B As hB hAs
  | .other_n1_other (ev14 := e1) (ev58 := e2) (ev81 := e3) (op156 := op) (ev125 := e4)
      (hne194 := hne) (op234 := op2) (ev203 := e5) (hc237 := hc) .. =>
    subst hc
    have hlen : As.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [substs], h⟩) (by simp) (by simp) hAs
    obtain ⟨rfl, rfl⟩ := klength e1 hAs
    rw [add_ok op] at e4
    rw [add_ok op2] at e5
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e2 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', y, hj', -, hj32, -, -, rfl⟩ := ltf e3
    injection hj' with hj'; subst hj'
    obtain ⟨rfl, h01, sn⟩ := ih.get .has_bvar_in_range lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd)
    have hv : ZMod.val (j + (As.length : F)) = ZMod.val j + As.length := by
      rw [val_add (by rw [val_natCast (by omega)]; omega), val_natCast (by omega)]
    have hnf := sn (zero_of_ne_one h01 hne) d Γ (ZMod.val j + As.length) B hB
    rw [hv] at hnf
    have hn := noIdx_of_noIdxF_tm hB (by omega) hnf
    have hlow := ih.get .expr_lower lt_calls e5 _ _ _ rfl (bounded_sub sub_calls bd) As.length 0
      (by rw [val_natCast (by omega), Nat.add_zero]) (by rw [hv]; omega) d Γ B (Nat.zero_le _)
      (by rw [hv]; exact hB) (by rw [hv, Nat.add_sub_cancel, Nat.add_zero]; exact hn)
    rw [hv, Nat.add_sub_cancel, Nat.sub_zero] at hlow
    rw [Ix.Kernel.Expr.instantiateList_eq_self (tm_lbb hB (Nat.le_add_right _ _) hn)]
    exact hlow

end IxVM.Refinement.Core.SubstAux
