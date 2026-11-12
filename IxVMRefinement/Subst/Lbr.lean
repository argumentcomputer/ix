import IxVMRefinement.Subst.Spec

/-! # Loose-bound ranges: `expr_lbr`, `expr_lbr_let`, `lbr_max`, `lbr_dec`, `lbr_min`

`expr_lbr(e)` is the least bound on the heap term's indices (`IdxLt`), computed bottom-up:
`i + 1` at `BVar(i)` (no wrap: the term seam bounds `i` by `2^63`), `0` at a leaf, the maximum
over the children, a binder body's bound less one. `lbr_max` and `lbr_min` compare with
`UInt32::less_than_fields`, so each value they see is below `2^32`; with every bound at most
`2^63` the field values are the naturals.

The counting functions are read off their paths directly (`lbr_max_obs`, `lbr_min_obs`,
`lbr_dec_obs`): a derivation of them exists only on field arguments, which `expr_lbr`'s
unconditional `h' = h` needs before its arguments are known to be represented. -/

namespace IxVM.Refinement.Core.SubstAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency (Bounded)
open Specs.Subst (IdxAll IdxLt NoIdx NoIdxF BVarIm idxBound)

set_option linter.unusedVariables false

local macro "lt_calls" : term => `(by simp <;> omega)
local macro "sub_calls" : term => `(fun _ hx => by simp [hx])

/-! ## Arithmetic -/

theorem lt_mod_of_le_idx {b : Nat} (hb : b ≤ idxBound) : b < Aiur.Library.U32.Goldilocks.modulus := by
  have : idxBound = 9223372036854775808 := rfl
  omega

/-- `lbr_max`'s answer on two naturals below the field's size. -/
theorem max_spec {a b : Nat} (ha : a < Aiur.Library.U32.Goldilocks.modulus)
    (hb : b < Aiur.Library.U32.Goldilocks.modulus) :
    ∃ m : Nat, (if ZMod.val (a : F) < ZMod.val (b : F) then (b : F) else (a : F)) = (m : F) ∧
      a ≤ m ∧ b ≤ m ∧ (m = a ∨ m = b) := by
  refine ⟨if a < b then b else a, ?_, ?_, ?_, ?_⟩
  · rw [val_natCast ha, val_natCast hb]; by_cases hab : a < b <;> simp [hab]
  all_goals split <;> omega

/-- `lbr_min`'s answer on two naturals below the field's size. -/
theorem min_spec {a b : Nat} (ha : a < Aiur.Library.U32.Goldilocks.modulus)
    (hb : b < Aiur.Library.U32.Goldilocks.modulus) :
    ∃ m : Nat, (if ZMod.val (a : F) < ZMod.val (b : F) then (a : F) else (b : F)) = (m : F) ∧
      m ≤ a ∧ m ≤ b ∧ (m = a ∨ m = b) := by
  refine ⟨if a < b then a else b, ?_, ?_, ?_, ?_⟩
  · rw [val_natCast ha, val_natCast hb]; by_cases hab : a < b <;> simp [hab]
  all_goals split <;> omega

/-! ## The counting functions, off their paths -/

theorem lbr_max_obs {a b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelSubst::lbr_max" [a, b] h r h' cs) :
    ∃ x y : F, a = .field x ∧ b = .field y ∧ ZMod.val x < 4294967296 ∧
      ZMod.val y < 4294967296 ∧ r = .field (if ZMod.val x < ZMod.val y then y else x) ∧
      h' = h := by
  cases Obs.«KernelSubst::lbr_max».obs ev with
  | n1 m2 cs13 ev15 he37 he38 hc39 =>
    obtain ⟨x, y, rfl, rfl, hx, hy, hr, rfl⟩ := ltf ev15
    subst he37 he38
    have hlt := ltf_one hr.symm
    exact ⟨x, y, rfl, rfl, hx, hy, by simp [hlt], rfl⟩
  | n0 m2 cs13 ev15 he46 he47 hc48 =>
    obtain ⟨x, y, rfl, rfl, hx, hy, hr, rfl⟩ := ltf ev15
    subst he46 he47
    have hlt := ltf_zero hr.symm
    exact ⟨x, y, rfl, rfl, hx, hy, by simp [hlt], rfl⟩

theorem lbr_min_obs {a b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelSubst::lbr_min" [a, b] h r h' cs) :
    ∃ x y : F, a = .field x ∧ b = .field y ∧ ZMod.val x < 4294967296 ∧
      ZMod.val y < 4294967296 ∧ r = .field (if ZMod.val x < ZMod.val y then x else y) ∧
      h' = h := by
  cases Obs.«KernelSubst::lbr_min».obs ev with
  | n1 m2 cs13 ev15 he37 he38 hc39 =>
    obtain ⟨x, y, rfl, rfl, hx, hy, hr, rfl⟩ := ltf ev15
    subst he37 he38
    have hlt := ltf_one hr.symm
    exact ⟨x, y, rfl, rfl, hx, hy, by simp [hlt], rfl⟩
  | n0 m2 cs13 ev15 he46 he47 hc48 =>
    obtain ⟨x, y, rfl, rfl, hx, hy, hr, rfl⟩ := ltf ev15
    subst he46 he47
    have hlt := ltf_zero hr.symm
    exact ⟨x, y, rfl, rfl, hx, hy, by simp [hlt], rfl⟩

theorem lbr_dec_obs {a r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelSubst::lbr_dec" [a] h r h' cs) :
    ∃ x : F, a = .field x ∧ r = .field ((ZMod.val x - 1 : Nat) : F) ∧ h' = h := by
  cases Obs.«KernelSubst::lbr_dec».obs ev with
  | n0 hv he hh hc => subst hv he hh; exact ⟨0, rfl, by simp, rfl⟩
  | other hne hh op hc =>
    obtain ⟨x, -, rfl, -⟩ := binop_fields op
    have hx0 : x ≠ 0 := fun h0 => hne (by rw [h0])
    have hv : 1 ≤ ZMod.val x := by
      rcases Nat.eq_zero_or_pos (ZMod.val x) with h0 | h0
      · exact absurd ((ZMod.val_eq_zero x).mp h0) hx0
      · exact h0
    refine ⟨x, rfl, ?_, hh⟩
    rw [sub_ok op, Nat.cast_sub hv, natCast_val, Nat.cast_one]

/-! ## The step lemmas -/

theorem g_lbr_max {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)} (ev : ObsFn W "KernelSubst::lbr_max" args h r h' calls) :
    G.lbr_max args h r h' calls := by
  intro x y hargs _
  subst hargs
  obtain ⟨x', y', hx, hy, h1, h2, hr, hh⟩ := lbr_max_obs ev
  injection hx with hx; injection hy with hy; subst hx hy
  exact ⟨hh, h1, h2, hr⟩

theorem g_lbr_min {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)} (ev : ObsFn W "KernelSubst::lbr_min" args h r h' calls) :
    G.lbr_min args h r h' calls := by
  intro x y hargs _
  subst hargs
  obtain ⟨x', y', hx, hy, h1, h2, hr, hh⟩ := lbr_min_obs ev
  injection hx with hx; injection hy with hy; subst hx hy
  exact ⟨hh, h1, h2, hr⟩

theorem g_lbr_dec {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)} (ev : ObsFn W "KernelSubst::lbr_dec" args h r h' calls) :
    G.lbr_dec args h r h' calls := by
  intro x hargs _
  subst hargs
  obtain ⟨x', hx, hr, hh⟩ := lbr_dec_obs ev
  injection hx with hx; subst hx
  exact ⟨hh, hr⟩

theorem g_expr_lbr_let (κ : _root_.Address → KKey) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_lbr_let" args h r h' calls) (ih : GIH κ calls) :
    G.expr_lbr_let κ args h r h' calls := by
  intro ty val body hargs bd
  subst hargs
  match Obs.«KernelSubst::expr_lbr_let».obs ev with
  | .run (ev34 := e1) (ev54 := e2) (ev20 := e3) (ev87 := e4) (ev74 := e5) (ev6 := e6)
      (hc96 := hc) .. =>
    subst hc
    obtain ⟨rfl, st⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨rfl, sv⟩ := ih.get .expr_lbr lt_calls e2 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨x1, y1, rfl, rfl, -, -, rfl, rfl⟩ := lbr_max_obs e3
    obtain ⟨rfl, sb⟩ := ih.get .expr_lbr lt_calls e4 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨z, rfl, rfl, rfl⟩ := lbr_dec_obs e5
    obtain ⟨x2, y2, hx2, hy2, -, -, hr, rfl⟩ := lbr_max_obs e6
    injection hx2 with hx2; injection hy2 with hy2; subst hx2 hy2
    refine ⟨rfl, fun d Γ k T V B ht hv hb => ?_⟩
    obtain ⟨bt, hbt, bt1, bt2, bt3, bt4, -⟩ := st d Γ k T ht
    obtain ⟨bv, hbv, bv1, bv2, bv3, bv4, -⟩ := sv d Γ k V hv
    obtain ⟨bb, hbb, bb1, bb2, bb3, bb4, -⟩ := sb d Γ (k + 1) B hb
    injection hbt with hbt; injection hbv with hbv; injection hbb with hbb
    subst hbt hbv hbb
    obtain ⟨bm, hbm, m1, m2, m3⟩ := max_spec (lt_mod_of_le_idx bt1) (lt_mod_of_le_idx bv1)
    rw [hbm, val_natCast (lt_mod_of_le_idx bb1)] at hr
    obtain ⟨b, hb', b1, b2, b3⟩ := max_spec (a := bm) (b := bb - 1)
      (by have := lt_mod_of_le_idx bt1; have := lt_mod_of_le_idx bv1; omega)
      (by have := lt_mod_of_le_idx bb1; omega)
    rw [hb'] at hr
    refine ⟨b, hr, by omega, by omega, idxAll_mono bt3 (fun n i hi => by omega),
      idxAll_mono bv3 (fun n i hi => by omega), idxAll_mono bb3 (fun n i hi => by omega), ?_⟩
    rintro b' hlt ⟨ht', hv', hb''⟩
    rcases (show b' < bt ∨ b' < bv ∨ b' + 1 < bb by omega) with h1 | h1 | h1
    · exact bt4 b' h1 ht'
    · exact bv4 b' h1 hv'
    · exact bb4 (b' + 1) h1 hb''

theorem g_expr_lbr (κ : _root_.Address → KKey) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_lbr" args h r h' calls) (ih : GIH κ calls) :
    G.expr_lbr κ args h r h' calls := by
  intro e hargs bd
  subst hargs
  match Obs.«KernelSubst::expr_lbr».obs ev with
  | .BVar (ld12 := ld) (he34 := he) (op32 := op) .. =>
    subst he
    refine ⟨rfl, fun d Γ k E hE => ?_⟩
    obtain ⟨i, rfl, hs, hcase⟩ := Tm.bvar_of_load hE ld
    have hI : IdxLt h (ZMod.val i + 1) e := idxAll_bvar_of_load ld (by simp)
    refine ⟨ZMod.val i + 1, ?_, ?_, ?_, hI, ?_, lbrLe_of_idxLt hE hI⟩
    · rw [add_ok op, Nat.cast_add, natCast_val, Nat.cast_one]
    · show ZMod.val i + 1 ≤ 9223372036854775808; omega
    · rcases hcase with ⟨hi, _⟩ | ⟨hk, hd, _⟩ <;> omega
    · intro b' hb' hlt
      obtain ⟨i', hx, hP⟩ := idxAll_bvar_inv hlt ld
      injection hx with hx; subst hx
      have : ZMod.val i < b' + 0 := hP
      omega
  | .Srt (ld12 := ld) (he49 := hr) (he50 := he) .. =>
    subst hr he
    refine ⟨rfl, fun d Γ k E hE => ?_⟩
    have hI : IdxLt h 0 e := idxAll_sort_of_load ld
    exact ⟨0, by simp, Nat.zero_le _, Nat.zero_le _, hI, fun b' hb' => absurd hb' (Nat.not_lt_zero _),
      lbrLe_of_idxLt hE hI⟩
  | .Const (ld12 := ld) (he71 := hr) (he72 := he) .. =>
    subst hr he
    refine ⟨rfl, fun d Γ k E hE => ?_⟩
    have hI : IdxLt h 0 e := idxAll_const_of_load ld
    exact ⟨0, by simp, Nat.zero_le _, Nat.zero_le _, hI, fun b' hb' => absurd hb' (Nat.not_lt_zero _),
      lbrLe_of_idxLt hE hI⟩
  | .Lit (ld12 := ld) (he87 := hr) (he88 := he) .. =>
    subst hr he
    refine ⟨rfl, fun d Γ k E hE => ?_⟩
    have hI : IdxLt h 0 e := idxAll_lit_of_load ld
    exact ⟨0, by simp, Nat.zero_le _, Nat.zero_le _, hI, fun b' hb' => absurd hb' (Nat.not_lt_zero _),
      lbrLe_of_idxLt hE hI⟩
  | .App (ld12 := ld) (ev126 := e1) (ev146 := e2) (ev112 := e3) (hc155 := hc) .. =>
    subst hc
    obtain ⟨rfl, sf⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨rfl, sa⟩ := ih.get .expr_lbr lt_calls e2 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨x, y, rfl, rfl, -, -, hr, rfl⟩ := lbr_max_obs e3
    refine ⟨rfl, fun d Γ k E hE => ?_⟩
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld
    obtain ⟨bf, hbf, bf1, bf2, bf3, bf4, -⟩ := sf d Γ k Ef hf
    obtain ⟨ba, hba, ba1, ba2, ba3, ba4, -⟩ := sa d Γ k Ea ha
    injection hbf with hbf; injection hba with hba; subst hbf hba
    obtain ⟨b, hb', b1, b2, b3⟩ := max_spec (lt_mod_of_le_idx bf1) (lt_mod_of_le_idx ba1)
    rw [hb'] at hr
    have hI : IdxLt h b e := idxAll_app_of_load ld (idxAll_mono bf3 (fun n i hi => by omega))
      (idxAll_mono ba3 (fun n i hi => by omega))
    refine ⟨b, hr, by omega, by omega, hI, ?_, lbrLe_of_idxLt hE hI⟩
    intro b' hb' hlt
    obtain ⟨hf', ha'⟩ := idxAll_app_inv hlt ld
    rcases (show b' < bf ∨ b' < ba by omega) with h1 | h1
    · exact bf4 b' h1 hf'
    · exact ba4 b' h1 ha'
  | .Lam (ld12 := ld) (ev198 := e1) (ev231 := e2) (ev218 := e3) (ev184 := e4) (hc240 := hc) .. =>
    subst hc
    obtain ⟨rfl, st⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨rfl, sb⟩ := ih.get .expr_lbr lt_calls e2 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨z, rfl, rfl, rfl⟩ := lbr_dec_obs e3
    obtain ⟨x, y, rfl, hy, -, -, hr, rfl⟩ := lbr_max_obs e4
    injection hy with hy; subst hy
    refine ⟨rfl, fun d Γ k E hE => ?_⟩
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.lam_of_load hE ld
    obtain ⟨bt, hbt, bt1, bt2, bt3, bt4, -⟩ := st d Γ k T ht
    obtain ⟨bb, hbb, bb1, bb2, bb3, bb4, -⟩ := sb d Γ (k + 1) B hb
    injection hbt with hbt; injection hbb with hbb; subst hbt hbb
    rw [val_natCast (lt_mod_of_le_idx bb1)] at hr
    obtain ⟨b, hb', b1, b2, b3⟩ := max_spec (a := bt) (b := bb - 1) (lt_mod_of_le_idx bt1)
      (by have := lt_mod_of_le_idx bb1; omega)
    rw [hb'] at hr
    have hI : IdxLt h b e := idxAll_lam_of_load ld (idxAll_mono bt3 (fun n i hi => by omega))
      (idxAll_imp bb3 (fun n i hi => by omega))
    refine ⟨b, hr, by omega, by omega, hI, ?_, lbrLe_of_idxLt hE hI⟩
    intro b' hb' hlt
    obtain ⟨ht', hb''⟩ := idxAll_lam_inv hlt ld
    rcases (show b' < bt ∨ b' + 1 < bb by omega) with h1 | h1
    · exact bt4 b' h1 ht'
    · exact bb4 (b' + 1) h1 (idxAll_imp hb'' (fun n i hi => by omega))
  | .Forall (ld12 := ld) (ev283 := e1) (ev316 := e2) (ev303 := e3) (ev269 := e4) (hc325 := hc) .. =>
    subst hc
    obtain ⟨rfl, st⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨rfl, sb⟩ := ih.get .expr_lbr lt_calls e2 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨z, rfl, rfl, rfl⟩ := lbr_dec_obs e3
    obtain ⟨x, y, rfl, hy, -, -, hr, rfl⟩ := lbr_max_obs e4
    injection hy with hy; subst hy
    refine ⟨rfl, fun d Γ k E hE => ?_⟩
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.forallE_of_load hE ld
    obtain ⟨bt, hbt, bt1, bt2, bt3, bt4, -⟩ := st d Γ k T ht
    obtain ⟨bb, hbb, bb1, bb2, bb3, bb4, -⟩ := sb d Γ (k + 1) B hb
    injection hbt with hbt; injection hbb with hbb; subst hbt hbb
    rw [val_natCast (lt_mod_of_le_idx bb1)] at hr
    obtain ⟨b, hb', b1, b2, b3⟩ := max_spec (a := bt) (b := bb - 1) (lt_mod_of_le_idx bt1)
      (by have := lt_mod_of_le_idx bb1; omega)
    rw [hb'] at hr
    have hI : IdxLt h b e := idxAll_forallE_of_load ld (idxAll_mono bt3 (fun n i hi => by omega))
      (idxAll_imp bb3 (fun n i hi => by omega))
    refine ⟨b, hr, by omega, by omega, hI, ?_, lbrLe_of_idxLt hE hI⟩
    intro b' hb' hlt
    obtain ⟨ht', hb''⟩ := idxAll_forallE_inv hlt ld
    rcases (show b' < bt ∨ b' + 1 < bb by omega) with h1 | h1
    · exact bt4 b' h1 ht'
    · exact bb4 (b' + 1) h1 (idxAll_imp hb'' (fun n i hi => by omega))
  | .Let (ld12 := ld) (ev353 := e1) (hc378 := hc) .. =>
    subst hc
    obtain ⟨rfl, sl⟩ := ih.get .expr_lbr_let lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, fun d Γ k E hE => ?_⟩
    obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := Tm.letE_of_load hE ld
    obtain ⟨b, hr, b1, b2, i1, i2, i3, bmin⟩ := sl d Γ k T V B ht hv hb
    have hI : IdxLt h b e := idxAll_letE_of_load ld i1 i2 (idxAll_imp i3 (fun n i hi => by omega))
    refine ⟨b, hr, b1, b2, hI, ?_, lbrLe_of_idxLt hE hI⟩
    intro b' hb' hlt
    obtain ⟨t', v', bd'⟩ := idxAll_letE_inv hlt ld
    exact bmin b' hb' ⟨t', v', idxAll_imp bd' (fun n i hi => by omega)⟩
  | .Proj (ld12 := ld) (ev408 := e1) (hc417 := hc) .. =>
    subst hc
    obtain ⟨rfl, s1⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, fun d Γ k E hE => ?_⟩
    obtain ⟨a, i, Es, -, rfl, -, hes⟩ := Tm.proj_of_load hE ld
    obtain ⟨b, hr, b1, b2, b3, b4, -⟩ := s1 d Γ k Es hes
    have hI : IdxLt h b e := idxAll_proj_of_load ld b3
    exact ⟨b, hr, b1, b2, hI, fun b' hb' hlt => b4 b' hb' (idxAll_proj_inv hlt ld),
      lbrLe_of_idxLt hE hI⟩

end IxVM.Refinement.Core.SubstAux
