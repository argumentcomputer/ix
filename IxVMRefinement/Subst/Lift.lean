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

theorem g_expr_lift_bvar (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_lift_bvar" args h r h' calls) :
    G.expr_lift_bvar κ args h r h' calls := by
  intro i s c hargs bd hs s₁ s₂ hsum d Γ E hE
  subst hargs
  obtain ⟨hsm, hcase⟩ := hE
  cases Obs.«KernelSubst::expr_lift_bvar».obs ev with
  | n1 m2 cs13 ev15 he40 hm39 hc52 =>
    obtain ⟨i', c', hi', hc', -, -, hr, rfl⟩ := ltf ev15
    injection hi' with hi'; injection hc' with hc'; subst hi' hc' he40 hm39
    have hlt := ltf_one hr.symm
    rcases hcase with ⟨_, rfl⟩ | ⟨hk, _, _⟩
    · exact tm_store_bvarLocal hsm (by omega)
    · omega
  | n0 m2 cs13 v66 ev15 he62 hm61 op80 hc83 =>
    obtain ⟨i', c', hi', hc', hi32, -, hr, rfl⟩ := ltf ev15
    injection hi' with hi'; injection hc' with hc'; subst hi' hc' he62 hm61
    have hge := ltf_zero hr.symm
    rw [add_ok op80]
    have hv : ZMod.val (i + s) = ZMod.val i + ZMod.val s :=
      val_add (by have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl; omega)
    rcases hcase with ⟨hlt, _⟩ | ⟨hk, hd, rfl⟩
    · omega
    · exact tm_store_bvarFree_eq (by omega) (by omega) (by omega) (by rw [hv]; unfold fvIdx; omega)

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

theorem g_expr_lift_walk (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_lift_walk" args h r h' calls) (ih : GIH κ calls) :
    G.expr_lift_walk κ args h r h' calls := by
  intro e s c hargs bd hs hc0
  subst hargs
  match Obs.«KernelSubst::expr_lift_walk».obs ev with
  | .BVar (ld12 := ld) (ev30 := e1) (hc55 := hc) .. =>
    subst hc
    intro s₁ s₂ hsum d Γ E hE
    obtain ⟨i, rfl, hsm, hcase⟩ := Tm.bvar_of_load hE ld
    exact ih.get .expr_lift_bvar lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ E
      ⟨hsm, hcase⟩
  | .Srt (ld12 := ld) (he72 := hr) (hm71 := hm) .. =>
    subst hr hm
    intro s₁ s₂ hsum d Γ E hE
    exact tm_copy_sort hE ld (Heap.Extends.refl _)
  | .Const (ld12 := ld) (he106 := hr) (hm105 := hm) .. =>
    subst hr hm
    intro s₁ s₂ hsum d Γ E hE
    exact tm_copy_const hE ld (Heap.Extends.refl _)
  | .Lit (ld12 := ld) (he554 := hr) (hm553 := hm) .. =>
    subst hr hm
    intro s₁ s₂ hsum d Γ E hE
    exact tm_copy_lit hE ld (Heap.Extends.refl _)
  | .App (ld12 := ld) (he148 := hr) (hm147 := hm) (ev165 := e1) (ev201 := e2) (hc226 := hc) .. =>
    subst hc hr hm
    intro s₁ s₂ hsum d Γ E hE
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld
    have sf := ih.get .expr_lift lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ Ef hf
    have sa := ih.get .expr_lift lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ Ea
      (ha.mono e1.heap_extends)
    exact Tm.store_app (sf.mono e2.heap_extends) sa
  | .Lam (ld12 := ld) (he253 := hr) (hm252 := hm) (ev271 := e1) (op338 := op) (ev307 := e2)
      (hc347 := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e2
    intro s₁ s₂ hsum d Γ E hE
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.lam_of_load hE ld
    have st := ih.get .expr_lift lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ T ht
    have sb := ih.get .expr_lift lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ B
      (by rw [val_succ32 hc0]; exact hb.mono e1.heap_extends)
    rw [val_succ32 hc0, show ZMod.val c + 1 + s₁ = ZMod.val c + s₁ + 1 by omega] at sb
    exact tm_store_lam (st.mono e2.heap_extends) sb (hl.mono (e1.heap_extends.trans e2.heap_extends))
  | .Forall (ld12 := ld) (he374 := hr) (hm373 := hm) (ev392 := e1) (op459 := op) (ev428 := e2)
      (hc468 := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e2
    intro s₁ s₂ hsum d Γ E hE
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.forallE_of_load hE ld
    have st := ih.get .expr_lift lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ T ht
    have sb := ih.get .expr_lift lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ B
      (by rw [val_succ32 hc0]; exact hb.mono e1.heap_extends)
    rw [val_succ32 hc0, show ZMod.val c + 1 + s₁ = ZMod.val c + s₁ + 1 by omega] at sb
    exact tm_store_forallE (st.mono e2.heap_extends) sb
      (hl.mono (e1.heap_extends.trans e2.heap_extends))
  | .Let (ld12 := ld) (ev496 := e1) (hc537 := hc) .. =>
    subst hc
    intro s₁ s₂ hsum d Γ E hE
    obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := Tm.letE_of_load hE ld
    exact ih.get .expr_lift_let lt_calls e1 _ _ _ _ _ rfl (bounded_sub sub_calls bd) hs hc0
      s₁ s₂ hsum d Γ T V B ht hv hb
  | .Proj (ld12 := ld) (he593 := hr) (hm592 := hm) (ev625 := e1) (hc650 := hc) .. =>
    subst hc hr hm
    intro s₁ s₂ hsum d Γ E hE
    obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := Tm.proj_of_load hE ld
    exact tm_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e1.heap_extends ra)
      (ih.get .expr_lift lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) hs s₁ s₂ hsum d Γ Es hes)

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
  | .other_n1 (ev36 := e1) (ev59 := e2) (ev94 := e3) (hc119 := hc) .. =>
    subst hc
    obtain ⟨rfl, sl⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', y, hc', hy, hc32, -, hr, rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    exact ih.get .expr_lift_walk lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) hs hc32

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

theorem g_expr_lower_walk (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_lower_walk" args h r h' calls) (ih : GIH κ calls) :
    G.expr_lower_walk κ args h r h' calls := by
  intro e s c hargs bd hc0 hnlt
  subst hargs
  match Obs.«KernelSubst::expr_lower_walk».obs ev with
  | .BVar (ld12 := ld) (he29 := hr) (hm28 := hm) (op47 := op) (hc50 := hc) .. =>
    subst hc hr hm
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    obtain ⟨i, rfl, hsm, hcase⟩ := Tm.bvar_of_load hE ld
    have hge : ZMod.val c ≤ ZMod.val i := by
      apply Nat.le_of_not_lt
      intro hlt
      exact hnlt (idxAll_bvar_of_load ld (by show ZMod.val i < ZMod.val c + 0; omega))
    obtain ⟨i', hx, hw⟩ := idxAll_bvar_inv hn ld
    injection hx with hx; subst hx
    have hw' : ZMod.val c + s₂ ≤ ZMod.val i := by
      have : ZMod.val i < ZMod.val c - s₁ + 0 ∨ ZMod.val c + s₂ + 0 ≤ ZMod.val i := hw
      omega
    rcases hcase with ⟨hlt, _⟩ | ⟨hk, hd, rfl⟩
    · omega
    · rw [sub_ok op]
      have hv : ZMod.val (i - s) = ZMod.val i - ZMod.val s := val_sub (by omega)
      exact tm_store_bvarFree_eq (by omega) (by omega) (by omega) (by rw [hv]; unfold fvIdx; omega)
  | .Srt (ld12 := ld) (he67 := hr) (hm66 := hm) .. =>
    subst hr hm
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    exact tm_copy_sort hE ld (Heap.Extends.refl _)
  | .Const (ld12 := ld) (he101 := hr) (hm100 := hm) .. =>
    subst hr hm
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    exact tm_copy_const hE ld (Heap.Extends.refl _)
  | .Lit (ld12 := ld) (he549 := hr) (hm548 := hm) .. =>
    subst hr hm
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    exact tm_copy_lit hE ld (Heap.Extends.refl _)
  | .App (ld12 := ld) (he143 := hr) (hm142 := hm) (ev160 := e1) (ev196 := e2) (hc221 := hc) .. =>
    subst hc hr hm
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld
    obtain ⟨nf, na⟩ := idxAll_app_inv hn ld
    have sf := ih.get .expr_lower lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum hs₁
      d Γ Ef hs₂ hf nf
    have sa := ih.get .expr_lower lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum hs₁
      d Γ Ea hs₂ (ha.mono e1.heap_extends) (idxAll_heap e1.heap_extends na)
    exact Tm.store_app (sf.mono e2.heap_extends) sa
  | .Lam (ld12 := ld) (he248 := hr) (hm247 := hm) (ev266 := e1) (op333 := op) (ev302 := e2)
      (hc342 := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e2
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.lam_of_load hE ld
    obtain ⟨nt, nb⟩ := idxAll_lam_inv hn ld
    have st := ih.get .expr_lower lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum hs₁
      d Γ T hs₂ ht nt
    have sb := ih.get .expr_lower lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum
      (by rw [val_succ32 hc0]; omega) d Γ B hs₂
      (by rw [val_succ32 hc0]; exact hb.mono e1.heap_extends)
      (by rw [val_succ32 hc0]
          exact noIdx_unbody (idxAll_heap e1.heap_extends nb) (by omega) (by omega))
    rw [val_succ32 hc0, show ZMod.val c + 1 - s₁ = ZMod.val c - s₁ + 1 by omega] at sb
    exact tm_store_lam (st.mono e2.heap_extends) sb (hl.mono (e1.heap_extends.trans e2.heap_extends))
  | .Forall (ld12 := ld) (he369 := hr) (hm368 := hm) (ev387 := e1) (op454 := op) (ev423 := e2)
      (hc463 := hc) .. =>
    subst hc hr hm
    rw [add_ok op] at e2
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.forallE_of_load hE ld
    obtain ⟨nt, nb⟩ := idxAll_forallE_inv hn ld
    have st := ih.get .expr_lower lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum hs₁
      d Γ T hs₂ ht nt
    have sb := ih.get .expr_lower lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum
      (by rw [val_succ32 hc0]; omega) d Γ B hs₂
      (by rw [val_succ32 hc0]; exact hb.mono e1.heap_extends)
      (by rw [val_succ32 hc0]
          exact noIdx_unbody (idxAll_heap e1.heap_extends nb) (by omega) (by omega))
    rw [val_succ32 hc0, show ZMod.val c + 1 - s₁ = ZMod.val c - s₁ + 1 by omega] at sb
    exact tm_store_forallE (st.mono e2.heap_extends) sb
      (hl.mono (e1.heap_extends.trans e2.heap_extends))
  | .Let (ld12 := ld) (ev491 := e1) (hc532 := hc) .. =>
    subst hc
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := Tm.letE_of_load hE ld
    obtain ⟨nt, nv, nb⟩ := idxAll_letE_inv hn ld
    exact ih.get .expr_lower_let lt_calls e1 _ _ _ _ _ rfl (bounded_sub sub_calls bd) hc0
      s₁ s₂ hsum hs₁ d Γ T V B hs₂ ht hv hb nt nv
      (noIdx_unbody nb (by omega) (by omega))
  | .Proj (ld12 := ld) (he588 := hr) (hm587 := hm) (ev620 := e1) (hc645 := hc) .. =>
    subst hc hr hm
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := Tm.proj_of_load hE ld
    exact tm_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e1.heap_extends ra)
      (ih.get .expr_lower lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd) s₁ s₂ hsum hs₁
        d Γ Es hs₂ hes (idxAll_proj_inv hn ld))

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
    have hI : IdxLt _ (ZMod.val c - s₁) e :=
      idxAll_mono (idxAll_and b3 hn) (fun n i hi => by obtain ⟨h1, h2⟩ := hi; omega)
    exact (lbrLe_of_idxLt hE hI (by omega)).2.2 (d - s₂) Γ (ZMod.val c - s₁) (Nat.le_refl _)
  | .other_n1 (ev36 := e1) (ev59 := e2) (ev94 := e3) (hc119 := hc) .. =>
    subst hc
    obtain ⟨rfl, sl⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨c', y, hc', hy, hc32, -, hr, rfl⟩ := ltf e2
    injection hc' with hc'; subst hc'
    have hlt := ltf_one hr.symm
    intro s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    obtain ⟨b, hb, b1, -, -, bmin, -⟩ := sl d Γ (ZMod.val c) E hE
    rw [hb] at hy; injection hy with hy; subst hy
    rw [val_natCast (lt_mod_of_le_idx b1)] at hlt
    exact ih.get .expr_lower_walk lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd) hc32
      (bmin _ hlt) s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn

end IxVM.Refinement.Core.SubstAux
