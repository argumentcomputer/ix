import IxVMRefinement.Subst.Occ

/-! # The smallest free index: `expr_glb*`

`expr_glb(e, c)` bounds from below, relative to the cutoff `c`, the indices at or above it:
no index is in `[c, c + g)`. It first compares `expr_lbr(e)` with `c + 1`: a term whose
indices are all below `c` answers `4294967295` (and the window holds vacuously); otherwise it
walks, and the walk's comparison at each binder keeps `c + 1` below `2^32`. A `0` answer
claims the empty window. -/

namespace IxVM.Refinement.Core.SubstAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency (Bounded)
open Specs.Subst (IdxAll IdxLt NoIdx NoIdxF BVarIm idxBound)

set_option linter.unusedVariables false

local macro "lt_calls" : term => `(by simp <;> omega)
local macro "sub_calls" : term => `(fun _ hx => by simp [hx])

/-- An empty window holds of every represented term. -/
theorem noIdx_of_le {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ d Γ h k E p) {lo hi : Nat}
    (hle : hi ≤ lo) : NoIdx h lo hi p :=
  idxAll_mono (tm_idxAll rep) (fun n i _ => by omega)

theorem cast_glb_top : (Value.field (4294967295 : F) : SourceValue F) =
    .field ((4294967295 : Nat) : F) := by simp

theorem val_succ_small {c : F} (hc : ZMod.val c + 1 < 4294967296) : ZMod.val (c + 1) = ZMod.val c + 1 :=
  val_add_one (by have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl; omega)

/-- A cutoff whose successor was compared (so is below `2^32`) has its successor below `2^32`
as a natural: below `2^32` it cannot wrap. -/
theorem succ_small {c : F} (hc0 : ZMod.val c < 4294967296) (hy : ZMod.val (c + 1) < 4294967296) :
    ZMod.val c + 1 < 4294967296 := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  rcases val_add_one_cases c with ⟨_, e⟩ | ⟨e, _⟩
  · rw [e] at hy; exact hy
  · omega

theorem g_expr_glb (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_glb" args h r h' calls) (ih : GIH κ calls) :
    G.expr_glb κ args h r h' calls := by
  intro e c hargs bd hc0
  subst hargs
  match Obs.«KernelSubst::expr_glb».obs ev with
  | .n1 (ev29 := e1) (op51 := op) (ev15 := e2) (he57 := hr) (he58 := he) (hc59 := hc) .. =>
    subst hc hr he
    rw [add_ok op] at e2
    obtain ⟨rfl, sl⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨x, y, hx, hy, -, hy32, hr, rfl⟩ := ltf e2
    injection hy with hy; subst hy
    have hlt := ltf_one hr.symm
    rw [val_succ_small (succ_small hc0 hy32)] at hlt
    refine ⟨rfl, 4294967295, cast_glb_top, by decide, fun d Γ E hE => ?_⟩
    obtain ⟨b, hb, b1, -, b3, -, -⟩ := sl d Γ (ZMod.val c) E hE
    rw [hb] at hx; injection hx with hx; subst hx
    rw [val_natCast (lt_mod_of_le_idx b1)] at hlt
    exact idxAll_mono b3 (fun n i hi => by omega)
  | .other_BVar (ev29 := e1) (op51 := op) (ev15 := e2) (hne60 := hne) (ld_hdultwxn := ld)
      (he_mmdvwhwq := he) (op_fbjhqzum := op2) (hc_tcnvhvza := hc) .. =>
    subst hc he
    rw [add_ok op] at e2
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨x, y, hx, hy, hx32, hy32, hr, rfl⟩ := ltf e2
    injection hy with hy; subst hy
    obtain ⟨i, -, rfl, -⟩ := binop_fields op2
    obtain ⟨-, hlbr⟩ := expr_lbr_bvar_val ld e1
    rw [hlbr] at hx; injection hx with hx; subst hx
    have hge : ¬ ZMod.val (i + 1) < ZMod.val (c + 1) := fun hlt => hne (by rw [hr, ite_eq_left hlt])
    obtain ⟨_, hci, hi32⟩ := bvar_lbr_ge32 (Nat.le_of_not_lt hge) (succ_small hc0 hy32) hx32
    refine ⟨rfl, ZMod.val i - ZMod.val c, ?_, by omega, fun d Γ E hE =>
      idxAll_bvar_of_load ld (by show _ ∨ ZMod.val c + (ZMod.val i - ZMod.val c) + 0 ≤ ZMod.val i; omega)⟩
    rw [sub_ok op2, Nat.cast_sub hci, natCast_val, natCast_val]
  | .other_App_n0 (ev29 := e1) (op51 := op) (ev15 := e2) (ev_trlqlrtc := e3)
      (he_ecwwvclb := hr) (he_mrkpbyhr := he) (hc_lejojgqf := hc) .. =>
    subst hc hr he
    rw [add_ok op] at e2
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := ltf e2
    obtain ⟨rfl, -⟩ := ih.get .expr_glb lt_calls e3 _ _ rfl (bounded_sub sub_calls bd) hc0
    exact ⟨rfl, 0, by simp, by decide, fun d Γ E hE => noIdx_of_le hE (by omega)⟩
  | .other_App_bind (ev29 := e1) (op51 := op) (ev15 := e2) (ld_hdultwxn := ld)
      (ev_trlqlrtc := e3) (ev_kjdsfvam := e4) (ev_oitnqhwn := e5) (hc_vvdtocog := hc) .. =>
    subst hc
    rw [add_ok op] at e2
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := ltf e2
    obtain ⟨rfl, gf, rfl, gf1, sf⟩ :=
      ih.get .expr_glb lt_calls e3 _ _ rfl (bounded_sub sub_calls bd) hc0
    obtain ⟨rfl, ga, rfl, ga1, sa⟩ :=
      ih.get .expr_glb lt_calls e4 _ _ rfl (bounded_sub sub_calls bd) hc0
    obtain ⟨x, y, hx, hy, -, -, hr, rfl⟩ := lbr_min_obs e5
    injection hx with hx; injection hy with hy; subst hx hy
    obtain ⟨g, hg, g1, g2, g3⟩ := min_spec (a := gf) (b := ga)
      (by have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl; omega)
      (by have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl; omega)
    rw [hg] at hr
    refine ⟨rfl, g, hr, by omega, fun d Γ E hE => ?_⟩
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld
    exact idxAll_app_of_load ld (idxAll_mono (sf d Γ Ef hf) (fun n i hi => by omega))
      (idxAll_mono (sa d Γ Ea ha) (fun n i hi => by omega))
  | .other_Lam_n0 (ev29 := e1) (op51 := op) (ev15 := e2) (ev_nmzxcqbr := e3)
      (he_ephaivvx := hr) (he_lkwvradl := he) (hc_kheyegem := hc) .. =>
    subst hc hr he
    rw [add_ok op] at e2
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := ltf e2
    obtain ⟨rfl, -⟩ := ih.get .expr_glb lt_calls e3 _ _ rfl (bounded_sub sub_calls bd) hc0
    exact ⟨rfl, 0, by simp, by decide, fun d Γ E hE => noIdx_of_le hE (by omega)⟩
  | .other_Lam_bind (ev29 := e1) (op51 := op) (ev15 := e2) (ld_hdultwxn := ld)
      (ev_nmzxcqbr := e3) (op_vwdfsoru := op2) (ev_xuosqwsl := e4) (ev_gzvmutwb := e5)
      (hc_nugjkglr := hc) .. =>
    subst hc
    rw [add_ok op] at e2
    rw [add_ok op2] at e4
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨_, y, _, hy, -, hy32, _, rfl⟩ := ltf e2
    injection hy with hy; subst hy
    have hc1 := succ_small hc0 hy32
    obtain ⟨rfl, gt, rfl, gt1, st⟩ :=
      ih.get .expr_glb lt_calls e3 _ _ rfl (bounded_sub sub_calls bd) hc0
    obtain ⟨rfl, gb, rfl, gb1, sb⟩ :=
      ih.get .expr_glb lt_calls e4 _ _ rfl (bounded_sub sub_calls bd) (by rw [val_succ_small hc1]; exact hc1)
    obtain ⟨x, y', hx, hy', -, -, hr, rfl⟩ := lbr_min_obs e5
    injection hx with hx; injection hy' with hy'; subst hx hy'
    obtain ⟨g, hg, g1, g2, g3⟩ := min_spec (a := gt) (b := gb)
      (by have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl; omega)
      (by have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl; omega)
    rw [hg] at hr
    refine ⟨rfl, g, hr, by omega, fun d Γ E hE => ?_⟩
    obtain ⟨T, B, ℓ, rfl, ht, hb, -⟩ := Tm.lam_of_load hE ld
    have n2 := sb d Γ B (by rw [val_succ_small hc1]; exact hb)
    rw [val_succ_small hc1] at n2
    exact idxAll_lam_of_load ld
      (idxAll_mono (st d Γ T ht) (fun n i hi => by omega))
      (idxAll_imp n2 (fun n i hi => by omega))
  | .other_Forall_n0 (ev29 := e1) (op51 := op) (ev15 := e2) (ev_miacmjtk := e3)
      (he_govkfifr := hr) (he_abcirwwj := he) (hc_tjboffvc := hc) .. =>
    subst hc hr he
    rw [add_ok op] at e2
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := ltf e2
    obtain ⟨rfl, -⟩ := ih.get .expr_glb lt_calls e3 _ _ rfl (bounded_sub sub_calls bd) hc0
    exact ⟨rfl, 0, by simp, by decide, fun d Γ E hE => noIdx_of_le hE (by omega)⟩
  | .other_Forall_bind (ev29 := e1) (op51 := op) (ev15 := e2) (ld_hdultwxn := ld)
      (ev_miacmjtk := e3) (op_fnwtvxee := op2) (ev_yrlaucgi := e4) (ev_xfqbjtis := e5)
      (hc_iklcezni := hc) .. =>
    subst hc
    rw [add_ok op] at e2
    rw [add_ok op2] at e4
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨_, y, _, hy, -, hy32, _, rfl⟩ := ltf e2
    injection hy with hy; subst hy
    have hc1 := succ_small hc0 hy32
    obtain ⟨rfl, gt, rfl, gt1, st⟩ :=
      ih.get .expr_glb lt_calls e3 _ _ rfl (bounded_sub sub_calls bd) hc0
    obtain ⟨rfl, gb, rfl, gb1, sb⟩ :=
      ih.get .expr_glb lt_calls e4 _ _ rfl (bounded_sub sub_calls bd) (by rw [val_succ_small hc1]; exact hc1)
    obtain ⟨x, y', hx, hy', -, -, hr, rfl⟩ := lbr_min_obs e5
    injection hx with hx; injection hy' with hy'; subst hx hy'
    obtain ⟨g, hg, g1, g2, g3⟩ := min_spec (a := gt) (b := gb)
      (by have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl; omega)
      (by have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl; omega)
    rw [hg] at hr
    refine ⟨rfl, g, hr, by omega, fun d Γ E hE => ?_⟩
    obtain ⟨T, B, ℓ, rfl, ht, hb, -⟩ := Tm.forallE_of_load hE ld
    have n2 := sb d Γ B (by rw [val_succ_small hc1]; exact hb)
    rw [val_succ_small hc1] at n2
    exact idxAll_forallE_of_load ld
      (idxAll_mono (st d Γ T ht) (fun n i hi => by omega))
      (idxAll_imp n2 (fun n i hi => by omega))
  | .other_Let (ev29 := e1) (op51 := op) (ev15 := e2) (ld_hdultwxn := ld)
      (ev_sfhifciv := e3) (hc_thparjte := hc) .. =>
    subst hc
    rw [add_ok op] at e2
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨_, y, _, hy, -, hy32, _, rfl⟩ := ltf e2
    injection hy with hy; subst hy
    obtain ⟨rfl, g, hr, g1, sl⟩ :=
      ih.get .expr_glb_let lt_calls e3 _ _ _ _ rfl (bounded_sub sub_calls bd) (succ_small hc0 hy32)
    refine ⟨rfl, g, hr, g1, fun d Γ E hE => ?_⟩
    obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := Tm.letE_of_load hE ld
    obtain ⟨n1, n2, n3⟩ := sl d Γ T V B ht hv hb
    exact idxAll_letE_of_load ld n1 n2 (idxAll_imp n3 (fun n i hi => by omega))
  | .other_Proj (ev29 := e1) (op51 := op) (ev15 := e2) (ld_hdultwxn := ld)
      (ev_zykxeexd := e3) (hc_kzchhfit := hc) .. =>
    subst hc
    rw [add_ok op] at e2
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := ltf e2
    obtain ⟨rfl, g, hr, g1, s1⟩ :=
      ih.get .expr_glb lt_calls e3 _ _ rfl (bounded_sub sub_calls bd) hc0
    refine ⟨rfl, g, hr, g1, fun d Γ E hE => ?_⟩
    obtain ⟨a, i, Es, -, rfl, -, hes⟩ := Tm.proj_of_load hE ld
    exact idxAll_proj_of_load ld (s1 d Γ Es hes)
  | .other_other (ev29 := e1) (op51 := op) (ev15 := e2) (ld_hdultwxn := ld)
      (hne_axudrchy := n1) (hne_oxuiduak := n2) (hne_zroyktgg := n3)
      (hne_ljsnsmib := n4) (hne_vuprrkrb := n5) (hne_hbwjspbe := n6)
      (he_lhxtzule := hr) (he_xhtrolce := he) (hc_bmwtsztg := hc) .. =>
    subst hc hr he
    rw [add_ok op] at e2
    obtain ⟨rfl, -⟩ := ih.get .expr_lbr lt_calls e1 _ rfl (bounded_sub sub_calls bd)
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := ltf e2
    exact ⟨rfl, 4294967295, cast_glb_top, by decide, fun d Γ E hE =>
      idxAll_of_other hE ld n1 n2 n3 n4 n5 n6⟩

theorem g_expr_glb_let (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_glb_let" args h r h' calls) (ih : GIH κ calls) :
    G.expr_glb_let κ args h r h' calls := by
  intro ty val body c hargs bd hc1
  subst hargs
  match Obs.«KernelSubst::expr_glb_let».obs ev with
  | .n0 (ev15 := e1) (he36 := hr) (he37 := he) (hc38 := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, -⟩ := ih.get .expr_glb lt_calls e1 _ _ rfl (bounded_sub sub_calls bd) (by omega)
    exact ⟨rfl, 0, by simp, by decide, fun d Γ T V B ht hv hb =>
      ⟨noIdx_of_le ht (by omega), noIdx_of_le hv (by omega), noIdx_of_le hb (by omega)⟩⟩
  | .bind_n0 (ev15 := e1) (ev57 := e2) (he78 := hr) (he79 := he) (hc80 := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, -⟩ := ih.get .expr_glb lt_calls e1 _ _ rfl (bounded_sub sub_calls bd) (by omega)
    obtain ⟨rfl, -⟩ := ih.get .expr_glb lt_calls e2 _ _ rfl (bounded_sub sub_calls bd) (by omega)
    exact ⟨rfl, 0, by simp, by decide, fun d Γ T V B ht hv hb =>
      ⟨noIdx_of_le ht (by omega), noIdx_of_le hv (by omega), noIdx_of_le hb (by omega)⟩⟩
  | .bind_bind (ev15 := e1) (ev57 := e2) (ev104 := e3) (op155 := op) (ev132 := e4) (ev90 := e5)
      (hc157 := hc) .. =>
    subst hc
    rw [add_ok op] at e4
    obtain ⟨rfl, gt, rfl, gt1, st⟩ :=
      ih.get .expr_glb lt_calls e1 _ _ rfl (bounded_sub sub_calls bd) (by omega)
    obtain ⟨rfl, gv, rfl, gv1, sv⟩ :=
      ih.get .expr_glb lt_calls e2 _ _ rfl (bounded_sub sub_calls bd) (by omega)
    obtain ⟨x, y, hx, hy, -, -, hr1, rfl⟩ := lbr_min_obs e3
    injection hx with hx; injection hy with hy; subst hx hy
    obtain ⟨rfl, gb, rfl, gb1, sb⟩ :=
      ih.get .expr_glb lt_calls e4 _ _ rfl (bounded_sub sub_calls bd) (by rw [val_succ_small hc1]; exact hc1)
    obtain ⟨x2, y2, hx2, hy2, -, -, hr, rfl⟩ := lbr_min_obs e5
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    obtain ⟨g1, hg1, g11, g12, g13⟩ := min_spec (a := gt) (b := gv) (by omega) (by omega)
    rw [hr1, hg1] at hx2
    injection hx2 with hx2; injection hy2 with hy2; subst hx2 hy2
    obtain ⟨g, hg, g21, g22, g23⟩ := min_spec (a := g1) (b := gb) (by omega) (by omega)
    rw [hg] at hr
    refine ⟨rfl, g, hr, by omega, fun d Γ T V B ht hv hb => ⟨?_, ?_, ?_⟩⟩
    · exact idxAll_mono (st d Γ T ht) (fun n i hi => by omega)
    · exact idxAll_mono (sv d Γ V hv) (fun n i hi => by omega)
    · have := sb d Γ B (by rw [val_succ_small hc1]; exact hb)
      rw [val_succ_small hc1] at this
      exact idxAll_mono this (fun n i hi => by omega)

end IxVM.Refinement.Core.SubstAux
