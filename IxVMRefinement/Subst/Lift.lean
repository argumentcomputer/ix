import IxVMRefinement.Subst.Glb

/-! # Lifting and lowering: `expr_lift*`, `expr_lower*`

Both keep the image and move the reading: lifting by `s = s₁ + s₂` at the cutoff `c` reads
the result at local depth `c + s₁` and opening depth `d + s₂`; lowering is the inverse, given
no heap index in the removed window. A free index `i ≥ c` stands for the opened variable
`d - 1 - (i - c)`, which both moves preserve (`fvIdx`). Each first compares the cutoff with
`expr_lbr(e)`: at or above it the term has no free index there and is returned as it is
(`LbrLeK`: read the same at any local depth at or above its bound). -/

namespace IxVM.Refinement.Core.SubstAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency (Bounded)
open Specs.Subst (IdxAll IdxLt NoIdx NoIdxF BVarIm idxBound)

set_option linter.unusedVariables false

local macro "lt_calls" : term => `(by simp <;> omega)
local macro "sub_calls" : term => `(fun _ hx => by simp [hx])

/-- **Heap facts survive a heap extension.** -/
theorem idxAll_heap {h h' : Heap F} {P : Nat → F → Prop} (ext : Heap.Extends h h') :
    ∀ {m : Nat} {p : SourceValue F}, IdxAll h P m p → IdxAll h' P m p := by
  intro m p hp
  induction hp with
  | bvar cell hP => exact .bvar (ext.getElem?_eq cell) hP
  | sort cell => exact .sort (ext.getElem?_eq cell)
  | const cell => exact .const (ext.getElem?_eq cell)
  | lit cell => exact .lit (ext.getElem?_eq cell)
  | app cell _ _ ihf iha => exact .app (ext.getElem?_eq cell) ihf iha
  | lam cell _ _ iht ihb => exact .lam (ext.getElem?_eq cell) iht ihb
  | forallE cell _ _ iht ihb => exact .forallE (ext.getElem?_eq cell) iht ihb
  | letE cell _ _ _ iht ihv ihb => exact .letE (ext.getElem?_eq cell) iht ihv ihb
  | proj cell _ ihe => exact .proj (ext.getElem?_eq cell) ihe

theorem val_succ32 {c : F} (hc : ZMod.val c < 4294967296) : ZMod.val (c + 1) = ZMod.val c + 1 :=
  val_add_one (by have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl; omega)

/-- A stored free variable, at the opened variable it reads as. -/
theorem tm_store_bvarFree_eq {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {i : F} {j : Nat}
    (hs : ZMod.val i < 9223372036854775808) (hk : k ≤ ZMod.val i) (hd : ZMod.val i - k < d)
    (hj : fvIdx d k (ZMod.val i) = j) :
    Tm κ d Γ (h ++ [.construct kexprEnum "BVar" [.field i]]) k (.fvar j (Γ j))
      (.ptr (.enum kexprEnum) h.length) := by
  subst hj; exact tm_store_bvarFree hs hk hd

/-! ## Lifting -/

theorem g_expr_lift_let (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_lift_let" args h r h' calls) (ih : GIH κ calls) :
    G.expr_lift_let κ args h r h' calls := by
  intro ty val body s c hargs bd hs hc0 s₁ s₂ hsum d Γ T V B ht hv hb
  subst hargs
  match Obs.«KernelSubst::expr_lift_let».obs ev with
  | .run (he5 := hr) (hm4 := hm) (ev23 := e1) (ev59 := e2) (op126 := op) (ev95 := e3)
      (hc128 := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e3
    have x1 := ih.get .expr_lift lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ T ht
    have x2 := ih.get .expr_lift lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ V
      (hv.mono e1.heap_extends)
    have x3 := ih.get .expr_lift lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ B
      (by rw [val_succ32 hc0]; exact hb.mono (e1.heap_extends.trans e2.heap_extends))
    rw [val_succ32 hc0, show ZMod.val c + 1 + s₁ = ZMod.val c + s₁ + 1 by omega] at x3
    exact tm_store_letE ((x1.mono e2.heap_extends).mono e3.heap_extends) (x2.mono e3.heap_extends) x3

theorem g_expr_lift (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_lift" args h r h' calls) (ih : GIH κ calls) :
    G.expr_lift κ args h r h' calls := by
  intro e s c hargs bd hs
  subst hargs
  match Obs.«KernelSubst::expr_lift».obs ev with
  | .n0 (hv14 := hv) (he16 := hr) (he17 := he) .. =>
    subst hr he
    injection hv with hv; subst hv
    intro s₁ s₂ hsum d Γ E hE
    rw [ZMod.val_zero] at hsum
    obtain ⟨rfl, rfl⟩ : s₁ = 0 ∧ s₂ = 0 := by omega
    exact hE
  | .other_n0 (ev36 := e1) (ev59 := e2) (he81 := hr) (he82 := he) (hc83 := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, sl⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', y, hc', hy, -, -, hr, rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    have hge := ltf_zero hr.symm
    intro s₁ s₂ hsum d Γ E hE
    obtain ⟨b, hb, b1, -, -, -, lb⟩ := sl d Γ (ZMod.val c) E hE
    rw [hb] at hy; injection hy with hy; subst hy
    rw [val_natCast (lt_mod_of_le_idx b1)] at hge
    exact (lb (by omega)).2.2 (d + s₂) Γ (ZMod.val c + s₁) (by omega)
  | .other_n1_BVar (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) (he_zxuqhldl := hr)
      (hm_jxognspy := hm) (op_ddurrpyr := op) (hc_tssuzvdf := hc) .. =>
    subst hc hr hm
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', y, hc', hy, -, hy32, hr', rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    have hlt := ltf_one hr'.symm
    intro s₁ s₂ hsum d Γ E hE
    obtain ⟨i, rfl, hsm, hcase⟩ := Tm.bvar_of_load hE ld
    obtain ⟨-, hlbr⟩ := expr_lbr_bvar_val ld e1
    rw [hlbr] at hy; injection hy with hy; subst hy
    obtain ⟨_, hci, hi32⟩ := bvar_lbr_lt32 hlt hy32
    rw [add_ok op]
    have hv : ZMod.val (i + s) = ZMod.val i + ZMod.val s :=
      val_add (by have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl; omega)
    rcases hcase with ⟨hlt', _⟩ | ⟨hk, hd, rfl⟩
    · omega
    · exact tm_store_bvarFree_eq (by omega) (by omega) (by omega) (by rw [hv]; unfold fvIdx; omega)
  | .other_n1_App (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) (he_lhthkmdy := hr)
      (hm_lkqgdqjj := hm) (ev_dldoddhd := e3) (ev_bretmskq := e4) (hc_dlddceds := hc) .. =>
    subst hc hr hm
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', _, hc', _, _, _, _, rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    intro s₁ s₂ hsum d Γ E hE
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld
    have sf := ih.get .expr_lift lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ Ef hf
    have sa := ih.get .expr_lift lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ Ea
      (ha.mono e3.heap_extends)
    exact Tm.store_app (sf.mono e4.heap_extends) sa
  | .other_n1_Lam (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) (he_eawjwxzg := hr)
      (hm_fjzjufvc := hm) (ev_dinjqkux := e3) (op_vzhxvrtx := op) (ev_jjaxcdue := e4)
      (hc_zxxtlxny := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e4
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', _, hc', _, hc32, _, _, rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    intro s₁ s₂ hsum d Γ E hE
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.lam_of_load hE ld
    have st := ih.get .expr_lift lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ T ht
    have sb := ih.get .expr_lift lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ B
      (by rw [val_succ32 hc32]; exact hb.mono e3.heap_extends)
    rw [val_succ32 hc32, show ZMod.val c + 1 + s₁ = ZMod.val c + s₁ + 1 by omega] at sb
    exact tm_store_lam (st.mono e4.heap_extends) sb (hl.mono (e3.heap_extends.trans e4.heap_extends))
  | .other_n1_Forall (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) (he_wljmpcwa := hr)
      (hm_lnuidxgg := hm) (ev_hgsapotx := e3) (op_glxuasev := op) (ev_gssmelog := e4)
      (hc_wnqbyufa := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e4
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', _, hc', _, hc32, _, _, rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    intro s₁ s₂ hsum d Γ E hE
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.forallE_of_load hE ld
    have st := ih.get .expr_lift lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ T ht
    have sb := ih.get .expr_lift lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ B
      (by rw [val_succ32 hc32]; exact hb.mono e3.heap_extends)
    rw [val_succ32 hc32, show ZMod.val c + 1 + s₁ = ZMod.val c + s₁ + 1 by omega] at sb
    exact tm_store_forallE (st.mono e4.heap_extends) sb
      (hl.mono (e3.heap_extends.trans e4.heap_extends))
  | .other_n1_Let (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) (ev_gowysupi := e3)
      (hc_imonhfda := hc) .. =>
    subst hc
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', _, hc', _, hc32, _, _, rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    intro s₁ s₂ hsum d Γ E hE
    obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := Tm.letE_of_load hE ld
    exact ih.get .expr_lift_let lt_calls e3 _ _ _ _ _ rfl (bounded_sub sub_calls bd) hs hc32
      s₁ s₂ hsum d Γ T V B ht hv hb
  | .other_n1_Proj (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) (he_wfuvnwup := hr)
      (hm_rhzmdxhb := hm) (ev_oofnxjme := e3) (hc_ufbwpkdo := hc) .. =>
    subst hc hr hm
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', _, hc', _, _, _, _, rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    intro s₁ s₂ hsum d Γ E hE
    obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := Tm.proj_of_load hE ld
    have : Resolved _ := ⟨hE.proj_key_ne⟩
    have : ProjPermitted _ _ := hE.proj_permitted ld ra
    exact tm_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e3.heap_extends ra)
      (ih.get .expr_lift lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ Es hes)
  | .other_n1_other (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) (hne_nctsiiom := n1)
      (hne_hhkiegac := n2) (hne_mlwerijc := n3) (hne_ttyzfnqz := n4) (hne_pcthgpyl := n5)
      (hne_wsdscrdh := n6) (hc_cpeakbbh := hc) .. =>
    subst hc
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', y, hc', hy, -, -, hr', rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    obtain ⟨-, hlbr⟩ := expr_lbr_other_zero ld n1 n2 n3 n4 n5 n6 e1
    rw [hlbr] at hy; injection hy with hy; subst hy
    have hlt := ltf_one hr'.symm
    rw [ZMod.val_zero] at hlt; omega

/-! ## Lowering -/

theorem g_expr_lower_let (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_lower_let" args h r h' calls) (ih : GIH κ calls) :
    G.expr_lower_let κ args h r h' calls := by
  intro ty val body s c hargs bd hc0 s₁ s₂ hsum hs₁ d Γ T V B hs₂ ht hv hb nt nv nb
  subst hargs
  match Obs.«KernelSubst::expr_lower_let».obs ev with
  | .run (he5 := hr) (hm4 := hm) (ev23 := e1) (ev59 := e2) (op126 := op) (ev95 := e3)
      (hc128 := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e3
    have x1 := ih.get .expr_lower lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum hs₁
      d Γ T hs₂ ht nt
    have x2 := ih.get .expr_lower lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum hs₁
      d Γ V hs₂ (hv.mono e1.heap_extends) (idxAll_heap e1.heap_extends nv)
    have x3 := ih.get .expr_lower lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum
      (by rw [val_succ32 hc0]; omega) d Γ B hs₂
      (by rw [val_succ32 hc0]; exact hb.mono (e1.heap_extends.trans e2.heap_extends))
      (by rw [val_succ32 hc0]; exact idxAll_heap (e1.heap_extends.trans e2.heap_extends) nb)
    rw [val_succ32 hc0, show ZMod.val c + 1 - s₁ = ZMod.val c - s₁ + 1 by omega] at x3
    exact tm_store_letE ((x1.mono e2.heap_extends).mono e3.heap_extends) (x2.mono e3.heap_extends) x3

/-- A window's fact at offset `1`, as the window one binder deeper. -/
theorem noIdx_unbody {h : Heap F} {lo hi lo' hi' : Nat} {p : SourceValue F}
    (hn : IdxAll h (fun m i => ZMod.val i < lo + m ∨ hi + m ≤ ZMod.val i) 1 p)
    (hlo : lo' = lo + 1) (hhi : hi' = hi + 1) : NoIdx h lo' hi' p := by
  subst hlo hhi; exact idxAll_imp hn (fun n i h1 => by omega)

theorem g_expr_lower (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_lower" args h r h' calls) (ih : GIH κ calls) :
    G.expr_lower κ args h r h' calls := by
  intro e s c hargs bd
  subst hargs
  match Obs.«KernelSubst::expr_lower».obs ev with
  | .n0 (hv14 := hv) (he16 := hr) (he17 := he) .. =>
    subst hr he
    injection hv with hv; subst hv
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    rw [ZMod.val_zero] at hsum
    obtain ⟨rfl, rfl⟩ : s₁ = 0 ∧ s₂ = 0 := by omega
    exact hE
  | .other_n0 (ev36 := e1) (ev59 := e2) (he81 := hr) (he82 := he) (hc83 := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, sl⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', y, hc', hy, -, -, hr, rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    have hge := ltf_zero hr.symm
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    obtain ⟨b, hb, b1, -, b3, -, -⟩ := sl d Γ (ZMod.val c) E hE
    rw [hb] at hy; injection hy with hy; subst hy
    rw [val_natCast (lt_mod_of_le_idx b1)] at hge
    have hI : IdxLt _ (ZMod.val c - s₁) _ :=
      idxAll_mono (idxAll_and b3 hn) (fun n i hi => by obtain ⟨h1, h2⟩ := hi; omega)
    exact (lbrLe_of_idxLt hE hI (by omega)).2.2 (d - s₂) Γ (ZMod.val c - s₁) (Nat.le_refl _)
  | .other_n1_BVar (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) (he_zxuqhldl := hr)
      (hm_jxognspy := hm) (op_pfueucrn := op) (hc_tssuzvdf := hc) .. =>
    subst hc hr hm
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', y, hc', hy, -, hy32, hr', rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    have hlt := ltf_one hr'.symm
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    obtain ⟨i, rfl, hsm, hcase⟩ := Tm.bvar_of_load hE ld
    obtain ⟨-, hlbr⟩ := expr_lbr_bvar_val ld e1
    rw [hlbr] at hy; injection hy with hy; subst hy
    obtain ⟨_, hge, hi32⟩ := bvar_lbr_lt32 hlt hy32
    obtain ⟨i', hx, hw⟩ := idxAll_bvar_inv hn ld
    injection hx with hx; subst hx
    have hw' : ZMod.val c + s₂ ≤ ZMod.val i := by
      have : ZMod.val i < ZMod.val c - s₁ + 0 ∨ ZMod.val c + s₂ + 0 ≤ ZMod.val i := hw
      omega
    rcases hcase with ⟨hlt', _⟩ | ⟨hk, hd, rfl⟩
    · omega
    · rw [sub_ok op]
      have hv : ZMod.val (i - s) = ZMod.val i - ZMod.val s := val_sub (by omega)
      exact tm_store_bvarFree_eq (by omega) (by omega) (by omega) (by rw [hv]; unfold fvIdx; omega)
  | .other_n1_App (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) (he_lhthkmdy := hr)
      (hm_lkqgdqjj := hm) (ev_ozlepaea := e3) (ev_lnvpubyf := e4) (hc_dlddceds := hc) .. =>
    subst hc hr hm
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', _, hc', _, _, _, _, rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld
    obtain ⟨nf, na⟩ := idxAll_app_inv hn ld
    have sf := ih.get .expr_lower lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum hs₁
      d Γ Ef hs₂ hf nf
    have sa := ih.get .expr_lower lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum hs₁
      d Γ Ea hs₂ (ha.mono e3.heap_extends) (idxAll_heap e3.heap_extends na)
    exact Tm.store_app (sf.mono e4.heap_extends) sa
  | .other_n1_Lam (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) (he_eawjwxzg := hr)
      (hm_fjzjufvc := hm) (ev_thyntvrp := e3) (op_vzhxvrtx := op) (ev_vtehlont := e4)
      (hc_zxxtlxny := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e4
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', _, hc', _, hc32, _, _, rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.lam_of_load hE ld
    obtain ⟨nt, nb⟩ := idxAll_lam_inv hn ld
    have st := ih.get .expr_lower lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum hs₁
      d Γ T hs₂ ht nt
    have sb := ih.get .expr_lower lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum
      (by rw [val_succ32 hc32]; omega) d Γ B hs₂
      (by rw [val_succ32 hc32]; exact hb.mono e3.heap_extends)
      (by rw [val_succ32 hc32]
          exact noIdx_unbody (idxAll_heap e3.heap_extends nb) (by omega) (by omega))
    rw [val_succ32 hc32, show ZMod.val c + 1 - s₁ = ZMod.val c - s₁ + 1 by omega] at sb
    exact tm_store_lam (st.mono e4.heap_extends) sb (hl.mono (e3.heap_extends.trans e4.heap_extends))
  | .other_n1_Forall (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) (he_wljmpcwa := hr)
      (hm_lnuidxgg := hm) (ev_uvqcsayu := e3) (op_glxuasev := op) (ev_kogtemxp := e4)
      (hc_wnqbyufa := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e4
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', _, hc', _, hc32, _, _, rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.forallE_of_load hE ld
    obtain ⟨nt, nb⟩ := idxAll_forallE_inv hn ld
    have st := ih.get .expr_lower lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum hs₁
      d Γ T hs₂ ht nt
    have sb := ih.get .expr_lower lt_calls e4 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum
      (by rw [val_succ32 hc32]; omega) d Γ B hs₂
      (by rw [val_succ32 hc32]; exact hb.mono e3.heap_extends)
      (by rw [val_succ32 hc32]
          exact noIdx_unbody (idxAll_heap e3.heap_extends nb) (by omega) (by omega))
    rw [val_succ32 hc32, show ZMod.val c + 1 - s₁ = ZMod.val c - s₁ + 1 by omega] at sb
    exact tm_store_forallE (st.mono e4.heap_extends) sb
      (hl.mono (e3.heap_extends.trans e4.heap_extends))
  | .other_n1_Let (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) (ev_jxykqhji := e3)
      (hc_imonhfda := hc) .. =>
    subst hc
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', _, hc', _, hc32, _, _, rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := Tm.letE_of_load hE ld
    obtain ⟨nt, nv, nb⟩ := idxAll_letE_inv hn ld
    exact ih.get .expr_lower_let lt_calls e3 _ _ _ _ _ rfl (bounded_sub sub_calls bd) hc32
      s₁ s₂ hsum hs₁ d Γ T V B hs₂ ht hv hb nt nv
      (noIdx_unbody nb (by omega) (by omega))
  | .other_n1_Proj (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) (he_wfuvnwup := hr)
      (hm_rhzmdxhb := hm) (ev_skxsyodm := e3) (hc_ufbwpkdo := hc) .. =>
    subst hc hr hm
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', _, hc', _, _, _, _, rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := Tm.proj_of_load hE ld
    have : Resolved _ := ⟨hE.proj_key_ne⟩
    have : ProjPermitted _ _ := hE.proj_permitted ld ra
    exact tm_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e3.heap_extends ra)
      (ih.get .expr_lower lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum hs₁
        d Γ Es hs₂ hes (idxAll_proj_inv hn ld))
  | .other_n1_other (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) (hne_nctsiiom := n1)
      (hne_hhkiegac := n2) (hne_mlwerijc := n3) (hne_ttyzfnqz := n4) (hne_pcthgpyl := n5)
      (hne_wsdscrdh := n6) (hc_cpeakbbh := hc) .. =>
    subst hc
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', y, hc', hy, -, -, hr', rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    obtain ⟨-, hlbr⟩ := expr_lbr_other_zero ld n1 n2 n3 n4 n5 n6 e1
    rw [hlbr] at hy; injection hy with hy; subst hy
    have hlt := ltf_one hr'.symm
    rw [ZMod.val_zero] at hlt; omega

end IxVM.Refinement.Core.SubstAux
