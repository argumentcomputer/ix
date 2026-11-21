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

private theorem inst1_seg_heap {κ : _root_.Address → KKey} {calls cs_seg : List (Call F)}
    {l e arg r_seg : SourceValue F} {j : F} {h h' : Heap F}
    (ih : GIH κ calls) (bd : Bounded calls)
    (hlen : cs_seg.length < calls.length) (hsub : ∀ c ∈ cs_seg, c ∈ calls)
    (sg : Obs.«KernelSubst::expr_inst1».Seg_lwkawbtz l e arg (.field j) h r_seg h' cs_seg) :
    h' = h := by
  cases sg with
  | n0 _ _ _ _ ev _ he _ =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := ltf ev
    exact he
  | n1 _ _ _ cs2 _ ev1 ev2 hc =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := ltf ev1
    have hlt2 : cs2.length < calls.length := by rw [hc] at hlen; simp at hlen; omega
    have hsub2 : Bounded cs2 := bounded_sub (fun x hx => hsub x (by rw [hc]; simp [hx])) bd
    exact (ih.get .expr_has_bvar_at hlt2 ev2 _ _ rfl hsub2).1

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
  | .n1_n1_BVar (ev14 := e1) (ev37 := e2) (sg_nijhquyq := sg) (ld_cazaqiwm := ld)
      (ev_wttpotmn := e3) (hc_krxqlobb := hc) .. =>
    subst hc
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', y, hj', hy, hj32, hy32, hr', rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hlt := ltf_one hr'.symm
    have hh := inst1_seg_heap ih bd lt_calls sub_calls sg; subst hh
    obtain ⟨i, rfl, hsm, hcase⟩ := Tm.bvar_of_load hB ld
    obtain ⟨-, hlbr⟩ := expr_lbr_bvar_val ld e1
    rw [hlbr] at hy; injection hy with hy; subst hy
    obtain ⟨hi1, hji, hi32⟩ := bvar_lbr_lt32 hlt hy32
    have hij : i = j := by
      cases sg with
      | n0 _ _ _ op ev _ _ _ =>
        rw [add_ok op] at ev
        obtain ⟨x1, y1, hx1, hy1, -, -, hr1, -⟩ := ltf ev
        rw [hlbr] at hy1
        injection hx1 with hx1; injection hy1 with hy1; subst hx1 hy1
        have hge := ltf_zero hr1.symm
        rw [val_succ32 hj32, hi1] at hge
        exact ZMod.val_injective _ (by omega)
      | n1 _ _ _ _ _ ev1 ev2 _ =>
        obtain ⟨_, _, _, _, _, _, _, rfl⟩ := ltf ev1
        exact (expr_has_bvar_at_bvar_one ld ev2).2
    subst hij
    rcases hcase with ⟨_, rfl⟩ | ⟨hk, _, _⟩
    · rw [inst1_bvar_self]
      have := ih.get .expr_lift lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) (by omega)
        (ZMod.val i) 0 (by omega) d Γ A (by rw [ZMod.val_zero]; exact hA)
      rw [ZMod.val_zero, Nat.zero_add] at this
      exact this
    · omega
  | .n1_n1_App (ev14 := e1) (ev37 := e2) (sg_nijhquyq := sg) (ld_cazaqiwm := ld)
      (he_erfbbtpw := hr) (hm_fspgjocs := hm) (ev_fjvmtqoz := e3) (ev_pqoxngrc := e4)
      (hc_myvfxkru := hc) .. =>
    subst hc hr hm
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', _, hj', -, -, -, -, rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hh := inst1_seg_heap ih bd lt_calls sub_calls sg; subst hh
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hB ld
    have sf := ih.get .expr_inst1 lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) d Γ Ef A hf hA
    have sa := ih.get .expr_inst1 lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd) d Γ Ea A
      (ha.mono e3.heap_extends) (hA.mono e3.heap_extends)
    exact Tm.store_app (sf.mono e4.heap_extends) sa
  | .n1_n1_Lam (ev14 := e1) (ev37 := e2) (sg_nijhquyq := sg) (ld_cazaqiwm := ld)
      (he_ewqmuvnh := hr) (hm_dzcuiuos := hm) (ev_jltiurnn := e3) (op_zuplncpn := op)
      (ev_xiuhqzbf := e4) (hc_cocetlqw := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e4
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', _, hj', -, hj32, -, -, rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hh := inst1_seg_heap ih bd lt_calls sub_calls sg; subst hh
    obtain ⟨T, B', ℓ, rfl, ht, hb, hl⟩ := Tm.lam_of_load hB ld
    have st := ih.get .expr_inst1 lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) d Γ T A ht hA
    have sb := ih.get .expr_inst1 lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd) d Γ B' A
      (by rw [val_succ32 hj32]; exact hb.mono e3.heap_extends) (hA.mono e3.heap_extends)
    rw [val_succ32 hj32] at sb
    exact tm_store_lam (st.mono e4.heap_extends) sb (hl.mono (e3.heap_extends.trans e4.heap_extends))
  | .n1_n1_Forall (ev14 := e1) (ev37 := e2) (sg_nijhquyq := sg) (ld_cazaqiwm := ld)
      (he_jirdvifw := hr) (hm_vlpbdsmi := hm) (ev_bdxhqrii := e3) (op_ygqucktb := op)
      (ev_ozhmrcxq := e4) (hc_qvjuupic := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e4
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', _, hj', -, hj32, -, -, rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hh := inst1_seg_heap ih bd lt_calls sub_calls sg; subst hh
    obtain ⟨T, B', ℓ, rfl, ht, hb, hl⟩ := Tm.forallE_of_load hB ld
    have st := ih.get .expr_inst1 lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) d Γ T A ht hA
    have sb := ih.get .expr_inst1 lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd) d Γ B' A
      (by rw [val_succ32 hj32]; exact hb.mono e3.heap_extends) (hA.mono e3.heap_extends)
    rw [val_succ32 hj32] at sb
    exact tm_store_forallE (st.mono e4.heap_extends) sb
      (hl.mono (e3.heap_extends.trans e4.heap_extends))
  | .n1_n1_Let (ev14 := e1) (ev37 := e2) (sg_nijhquyq := sg) (ld_cazaqiwm := ld)
      (ev_rhrekngq := e3) (hc_icdctvkp := hc) .. =>
    subst hc
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', _, hj', -, hj32, -, -, rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hh := inst1_seg_heap ih bd lt_calls sub_calls sg; subst hh
    obtain ⟨T, V, B', rfl, ht, hv, hb⟩ := Tm.letE_of_load hB ld
    exact ih.get .expr_inst1_let lt_calls e3 _ _ _ _ _ rfl (bounded_sub sub_calls bd) hj32
      d Γ T V B' A ht hv hb hA
  | .n1_n1_Proj (ev14 := e1) (ev37 := e2) (sg_nijhquyq := sg) (ld_cazaqiwm := ld)
      (he_vyjrbsci := hr) (hm_iywlmnii := hm) (ev_dwrkbatj := e3) (hc_dhrzqlmk := hc) .. =>
    subst hc hr hm
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', _, hj', -, -, -, -, rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hh := inst1_seg_heap ih bd lt_calls sub_calls sg; subst hh
    obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := Tm.proj_of_load hB ld
    have : Resolved _ := ⟨hB.proj_key_ne⟩
    have : ProjPermitted _ _ := hB.proj_permitted ld ra
    exact tm_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e3.heap_extends ra)
      (ih.get .expr_inst1 lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) d Γ Es A hes hA)
  | .n1_n1_other (ev14 := e1) (ev37 := e2) (sg_nijhquyq := sg) (ld_cazaqiwm := ld)
      (hne_mrzdkzct := n1) (hne_oicewdsa := n2) (hne_vdmlyytd := n3) (hne_wsfwgpgb := n4)
      (hne_tasugfar := n5) (hne_otxnyqsa := n6) (hc_aynotxpb := hc) .. =>
    subst hc
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', y, hj', hy, -, -, hr', rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hh := inst1_seg_heap ih bd lt_calls sub_calls sg; subst hh
    obtain ⟨-, hlbr⟩ := expr_lbr_other_zero ld n1 n2 n3 n4 n5 n6 e1
    rw [hlbr] at hy; injection hy with hy; subst hy
    have hlt := ltf_one hr'.symm
    rw [ZMod.val_zero] at hlt; omega
  | .n1_other (ev14 := e1) (ev37 := e2) (sg_nijhquyq := sg) (hne133 := hne)
      (op172 := op) (ev142 := e4) (hc174 := hc) .. =>
    subst hc
    rw [add_ok op] at e4
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', _, hj', -, hj32, -, -, rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    cases sg with
    | n0 _ _ _ _ _ hr0 _ _ => exact absurd hr0 hne
    | n1 _ _ _ _ _ ev1 ev2 hc_sg =>
      subst hc_sg
      obtain ⟨_, _, _, _, _, _, _, rfl⟩ := ltf ev1
      obtain ⟨rfl, h01, sn⟩ := ih.get .expr_has_bvar_at lt_calls ev2 _ _ rfl (bounded_sub sub_calls bd)
      have hn := sn (zero_of_ne_one h01 hne) d Γ (ZMod.val j + 1) B hB
      have hlow := ih.get .expr_lower lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd) 1 0
        (by rw [val_one]) (by rw [val_succ32 hj32]; omega) d Γ B (Nat.zero_le _)
        (by rw [val_succ32 hj32]; exact hB)
        (by rw [val_succ32 hj32, Nat.add_sub_cancel, Nat.add_zero]; exact hn)
      rw [val_succ32 hj32, Nat.add_sub_cancel, Nat.sub_zero] at hlow
      rw [Ix.Kernel.Expr.instantiate1_eq_self (tm_lbb hB (Nat.le_succ _) hn)]
      exact hlow

/-! ## `expr_inst_many` -/

private theorem inst_many_seg_heap {κ : _root_.Address → KKey} {calls cs_seg : List (Call F)}
    {l e substs n r_seg : SourceValue F} {j : F} {h h' : Heap F}
    (ih : GIH κ calls) (bd : Bounded calls)
    (hlen : cs_seg.length < calls.length) (hsub : ∀ c ∈ cs_seg, c ∈ calls)
    (sg : Obs.«KernelSubst::expr_inst_many_n».Seg_lwkawbtz l e substs n (.field j) h r_seg h' cs_seg) :
    h' = h := by
  cases sg with
  | n0 _ _ _ _ ev _ he _ =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := ltf ev
    exact he
  | n1 _ _ _ cs2 _ _ ev1 op2 ev2 hc =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := ltf ev1
    obtain ⟨z, hz⟩ := binop_field op2
    rw [hz] at ev2
    have hlt2 : cs2.length < calls.length := by rw [hc] at hlen; simp at hlen; omega
    have hsub2 : Bounded cs2 := bounded_sub (fun x hx => hsub x (by rw [hc]; simp [hx])) bd
    exact (ih.get .has_bvar_in_range hlt2 ev2 _ _ _ rfl hsub2).1

theorem g_expr_inst_many_let (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_inst_many_let" args h r h' calls) (ih : GIH κ calls) :
    G.expr_inst_many_let κ args h r h' calls := by
  intro ty val body substs n j hargs bd hj0 d Γ T V B As hn hlen ht hv hb hAs
  subst hargs
  match Obs.«KernelSubst::expr_inst_many_let».obs ev with
  | .run (he5 := hr) (hm4 := hm) (ev_emcrrcjp := e1) (ev_qhoozicr := e2) (op_pioimjax := op)
      (ev_hkvuaucb := e3) (hc128 := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e3
    have x1 := ih.get .expr_inst_many_n lt_calls e1 _ _ _ _ rfl (bounded_sub sub_calls bd)
      d Γ T As hn hlen ht hAs
    have x2 := ih.get .expr_inst_many_n lt_calls e2 _ _ _ _ rfl (bounded_sub sub_calls bd)
      d Γ V As hn hlen (hv.mono e1.heap_extends) (tmL_mono e1.heap_extends hAs)
    have x3 := ih.get .expr_inst_many_n lt_calls e3 _ _ _ _ rfl (bounded_sub sub_calls bd)
      d Γ B As hn hlen
      (by rw [val_succ32 hj0, Nat.add_right_comm]
          exact hb.mono (e1.heap_extends.trans e2.heap_extends))
      (tmL_mono (e1.heap_extends.trans e2.heap_extends) hAs)
    rw [val_succ32 hj0] at x3
    rw [instShift_instantiateList As (tmL_closed hAs)]
    exact tm_store_letE ((x1.mono e2.heap_extends).mono e3.heap_extends) (x2.mono e3.heap_extends) x3

theorem g_expr_inst_many_n (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_inst_many_n" args h r h' calls) (ih : GIH κ calls) :
    G.expr_inst_many_n κ args h r h' calls := by
  intro e substs n j hargs bd d Γ B As hn hlen hB hAs
  subst hargs hn
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  match Obs.«KernelSubst::expr_inst_many_n».obs ev with
  | .n0 (ev_qozyctmr := e1) (ev_xotwiaot := e2) (he_whiproaa := hr) (he_bzwoglyf := he)
      (hc_fvdjlccv := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, sl⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', y, hj', hy, -, -, hr', rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hge := ltf_zero hr'.symm
    obtain ⟨b, hb, b1, -, -, -, lb⟩ := sl d Γ (ZMod.val j + As.length) B hB
    rw [hb] at hy; injection hy with hy; subst hy
    rw [val_natCast (lt_mod_of_le_idx b1)] at hge
    obtain ⟨l1, -, l3⟩ := lb (by omega)
    rw [Ix.Kernel.Expr.instantiateList_eq_self (lbb_mono (by omega) l1)]
    exact l3 d Γ (ZMod.val j) (by omega)
  | .n1_n1_BVar (ev_qozyctmr := e1) (ev_xotwiaot := e2) (sg_nijhquyq := sg) (ld_cazaqiwm := ld)
      (op_lnzkiylo := op) (ev_sjukbdta := e3) (ev_wttpotmn := e4) (hc_krxqlobb := hc) .. =>
    subst hc
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', y, hj', hy, hj32, hy32, hr', rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hlt := ltf_one hr'.symm
    have hh := inst_many_seg_heap ih bd lt_calls sub_calls sg; subst hh
    obtain ⟨i, rfl, hsm, hcase⟩ := Tm.bvar_of_load hB ld
    obtain ⟨-, hlbr⟩ := expr_lbr_bvar_val ld e1
    rw [hlbr] at hy; injection hy with hy; subst hy
    obtain ⟨hi1, hji, hi32⟩ := bvar_lbr_lt32 hlt hy32
    have hjn : ZMod.val (j + (As.length : F)) = ZMod.val j + As.length := by
      rw [val_add (by rw [val_natCast (by omega)]; omega), val_natCast (by omega)]
    have hlt_hi : ZMod.val i < ZMod.val j + As.length := by
      cases sg with
      | n0 _ _ _ op1 ev1 _ _ _ =>
        rw [add_ok op1] at ev1
        obtain ⟨x1, y1, hx1, hy1, -, -, hr1, -⟩ := ltf ev1
        rw [hlbr] at hy1
        injection hx1 with hx1; injection hy1 with hy1; subst hx1 hy1
        have hge := ltf_zero hr1.symm
        rw [hjn, hi1] at hge
        omega
      | n1 _ _ _ _ _ _ ev1 op2 ev2 _ =>
        obtain ⟨_, _, _, _, _, _, _, rfl⟩ := ltf ev1
        rw [add_ok op2] at ev2
        have hrange := (has_bvar_in_range_bvar_one ld ev2).2.2
        rw [hjn] at hrange
        exact hrange
    rw [sub_ok op] at e3
    have hval : ZMod.val (i - j) = ZMod.val i - ZMod.val j := val_sub hji
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
  | .n1_n1_App (ev_qozyctmr := e1) (ev_xotwiaot := e2) (sg_nijhquyq := sg) (ld_cazaqiwm := ld)
      (he_erfbbtpw := hr) (hm_fspgjocs := hm) (ev_dskjiozj := e3) (ev_mlqkcegc := e4)
      (hc_myvfxkru := hc) .. =>
    subst hc hr hm
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', _, hj', -, -, -, -, rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hh := inst_many_seg_heap ih bd lt_calls sub_calls sg; subst hh
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hB ld
    have sf := ih.get .expr_inst_many_n lt_calls e3 _ _ _ _ rfl (bounded_sub sub_calls bd)
      d Γ Ef As rfl hlen hf hAs
    have sa := ih.get .expr_inst_many_n lt_calls e4 _ _ _ _ rfl (bounded_sub sub_calls bd)
      d Γ Ea As rfl hlen (ha.mono e3.heap_extends) (tmL_mono e3.heap_extends hAs)
    rw [iL_app]
    exact Tm.store_app (sf.mono e4.heap_extends) sa
  | .n1_n1_Lam (ev_qozyctmr := e1) (ev_xotwiaot := e2) (sg_nijhquyq := sg) (ld_cazaqiwm := ld)
      (he_ewqmuvnh := hr) (hm_dzcuiuos := hm) (ev_ijbdyuez := e3) (op_fdxwyetc := op)
      (ev_nhteuybo := e4) (hc_cocetlqw := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e4
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', _, hj', -, hj32, -, -, rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hh := inst_many_seg_heap ih bd lt_calls sub_calls sg; subst hh
    obtain ⟨T, B', ℓ, rfl, ht, hb, hl⟩ := Tm.lam_of_load hB ld
    have st := ih.get .expr_inst_many_n lt_calls e3 _ _ _ _ rfl (bounded_sub sub_calls bd)
      d Γ T As rfl hlen ht hAs
    have sb := ih.get .expr_inst_many_n lt_calls e4 _ _ _ _ rfl (bounded_sub sub_calls bd)
      d Γ B' As rfl hlen
      (by rw [val_succ32 hj32, Nat.add_right_comm]; exact hb.mono e3.heap_extends)
      (tmL_mono e3.heap_extends hAs)
    rw [val_succ32 hj32] at sb
    rw [iL_lam]
    exact tm_store_lam (st.mono e4.heap_extends) sb (hl.mono (e3.heap_extends.trans e4.heap_extends))
  | .n1_n1_Forall (ev_qozyctmr := e1) (ev_xotwiaot := e2) (sg_nijhquyq := sg) (ld_cazaqiwm := ld)
      (he_jirdvifw := hr) (hm_vlpbdsmi := hm) (ev_yfxpobrf := e3) (op_fxgckqoy := op)
      (ev_iliahjfx := e4) (hc_qvjuupic := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e4
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', _, hj', -, hj32, -, -, rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hh := inst_many_seg_heap ih bd lt_calls sub_calls sg; subst hh
    obtain ⟨T, B', ℓ, rfl, ht, hb, hl⟩ := Tm.forallE_of_load hB ld
    have st := ih.get .expr_inst_many_n lt_calls e3 _ _ _ _ rfl (bounded_sub sub_calls bd)
      d Γ T As rfl hlen ht hAs
    have sb := ih.get .expr_inst_many_n lt_calls e4 _ _ _ _ rfl (bounded_sub sub_calls bd)
      d Γ B' As rfl hlen
      (by rw [val_succ32 hj32, Nat.add_right_comm]; exact hb.mono e3.heap_extends)
      (tmL_mono e3.heap_extends hAs)
    rw [val_succ32 hj32] at sb
    rw [iL_forallE]
    exact tm_store_forallE (st.mono e4.heap_extends) sb
      (hl.mono (e3.heap_extends.trans e4.heap_extends))
  | .n1_n1_Let (ev_qozyctmr := e1) (ev_xotwiaot := e2) (sg_nijhquyq := sg) (ld_cazaqiwm := ld)
      (ev_rtosanvh := e3) (hc_icdctvkp := hc) .. =>
    subst hc
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', _, hj', -, hj32, -, -, rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hh := inst_many_seg_heap ih bd lt_calls sub_calls sg; subst hh
    obtain ⟨T, V, B', rfl, ht, hv, hb⟩ := Tm.letE_of_load hB ld
    exact ih.get .expr_inst_many_let lt_calls e3 _ _ _ _ _ _ rfl (bounded_sub sub_calls bd) hj32
      d Γ T V B' As rfl hlen ht hv hb hAs
  | .n1_n1_Proj (ev_qozyctmr := e1) (ev_xotwiaot := e2) (sg_nijhquyq := sg) (ld_cazaqiwm := ld)
      (he_vyjrbsci := hr) (hm_iywlmnii := hm) (ev_tfdkwozr := e3) (hc_dhrzqlmk := hc) .. =>
    subst hc hr hm
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', _, hj', -, -, -, -, rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hh := inst_many_seg_heap ih bd lt_calls sub_calls sg; subst hh
    obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := Tm.proj_of_load hB ld
    have : Resolved _ := ⟨hB.proj_key_ne⟩
    have : ProjPermitted _ _ := hB.proj_permitted ld ra
    rw [iL_proj]
    exact tm_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e3.heap_extends ra)
      (ih.get .expr_inst_many_n lt_calls e3 _ _ _ _ rfl (bounded_sub sub_calls bd)
        d Γ Es As rfl hlen hes hAs)
  | .n1_n1_other (ev_qozyctmr := e1) (ev_xotwiaot := e2) (sg_nijhquyq := sg) (ld_cazaqiwm := ld)
      (hne_mrzdkzct := n1) (hne_oicewdsa := n2) (hne_vdmlyytd := n3) (hne_wsfwgpgb := n4)
      (hne_tasugfar := n5) (hne_otxnyqsa := n6) (hc_aynotxpb := hc) .. =>
    subst hc
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', y, hj', hy, -, -, hr', rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    have hh := inst_many_seg_heap ih bd lt_calls sub_calls sg; subst hh
    obtain ⟨-, hlbr⟩ := expr_lbr_other_zero ld n1 n2 n3 n4 n5 n6 e1
    rw [hlbr] at hy; injection hy with hy; subst hy
    have hlt := ltf_one hr'.symm
    rw [ZMod.val_zero] at hlt; omega
  | .n1_other (ev_qozyctmr := e1) (ev_xotwiaot := e2) (sg_nijhquyq := sg) (hne_qnsahksn := hne)
      (op_zfrdzcvj := op) (ev_cevvkorh := e4) (hc_lfsktsxj := hc) .. =>
    subst hc
    rw [add_ok op] at e4
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨j', _, hj', -, hj32, -, -, rfl⟩ := ltf e2
    injection hj' with hj'; subst hj'
    cases sg with
    | n0 _ _ _ _ _ hr0 _ _ => exact absurd hr0 hne
    | n1 _ _ _ _ _ _ ev1 op2 ev2 hc_sg =>
      subst hc_sg
      obtain ⟨_, _, _, _, _, _, _, rfl⟩ := ltf ev1
      rw [add_ok op2] at ev2
      obtain ⟨rfl, h01, sn⟩ := ih.get .has_bvar_in_range lt_calls ev2 _ _ _ rfl (bounded_sub sub_calls bd)
      have hv : ZMod.val (j + (As.length : F)) = ZMod.val j + As.length := by
        rw [val_add (by rw [val_natCast (by omega)]; omega), val_natCast (by omega)]
      have hnf := sn (zero_of_ne_one h01 hne) d Γ (ZMod.val j + As.length) B hB
      rw [hv] at hnf
      have hn' := noIdx_of_noIdxF_tm hB (by omega) hnf
      have hlow := ih.get .expr_lower lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd) As.length 0
        (by rw [val_natCast (by omega), Nat.add_zero]) (by rw [hv]; omega) d Γ B (Nat.zero_le _)
        (by rw [hv]; exact hB) (by rw [hv, Nat.add_sub_cancel, Nat.add_zero]; exact hn')
      rw [hv, Nat.add_sub_cancel, Nat.sub_zero] at hlow
      rw [Ix.Kernel.Expr.instantiateList_eq_self (tm_lbb hB (Nat.le_add_right _ _) hn')]
      exact hlow

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
  | .other (ev14 := e1) (ev_eoqoorsc := e2) (hc_kjrxaxhl := hc) .. =>
    subst hc
    have hlen : As.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [substs], h⟩) (by simp) (by simp) hAs
    obtain ⟨rfl, rfl⟩ := klength e1 hAs
    exact ih.get .expr_inst_many_n lt_calls e2 _ _ _ _ rfl (bounded_sub sub_calls bd)
      d Γ B As rfl hlen hB hAs

end IxVM.Refinement.Core.SubstAux
