import IxVMRefinement.Infer.Leaves
import IxVMRefinement.Infer.Close

/-! # One step of inference by the head node, at both grades

`KernelInfer::k_infer_core` (full grade) and `KernelInferOnly::k_infer_only_core` (io grade)
dispatch on the head node of the term:

* `BVar`: the context entry (`Infer.fvar`); `Srt`: the successor sort (`Infer.sort`, the level
  simplified by `level_reduce`); `Const`: the loaded constant's type at the use's levels
  (`Infer.const`);
* `App`: at the full grade the spine loop from the head's type, at the io grade the head's type
  head-normalized to a `∀` and `io_app_cod` (`Infer.app`, or `Infer.appSkip` at a `never` datum);
* `Lam`: the body inferred under the opened binder (the context list extended by the domain,
  `types_extend`), its type closed again (`Tm.close`), the datum checked by `lam_datum_ok`
  (`Infer.lam`, `lam_infer`); `Forall`: both sorts and `forall_datum_ok` (`Infer.forallE`);
* `Let`: the ζ-reduct, the image of the node; `Lit`: the literal's role constant; `Proj`: at the
  full grade `k_infer_proj`.

**`Infer.const` reads the stored type at the constant's own level parameters.** IxVM loads it with
those renamed to positions (`posOf`) and instantiates the positions; the parameters are a
permutation of the positions (`ValRep`), so the two agree (`posOf_instantiateLevelParams_perm`).

The io grade's projection arm is a hypothesis of its step lemma (`hproj`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open Ix.Kernel.Rules (Red DefEq Infer)

set_option linter.unusedVariables false

/-- A loaded constant is never a projection table. -/
theorem CIRep.isTowerEntry {κ : _root_.Address → KKey} {h : Heap F} {v : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon} (r : CIRep κ h v ci) : ci.isTowerEntry = false := by
  cases r with
  | quot _ hk =>
    rcases hk with ⟨-, cv, caps, rfl⟩ | ⟨-, cv, nP, nF, rfl⟩ | ⟨-, cv, mI, rP, rs, rfl⟩ |
      ⟨-, cv, mI, rP, rs, rfl⟩ <;> rfl
  | _ => rfl

namespace InferBase

/-- **A context list reads the ghost context below its depth only.** -/
theorem typesRep_congr {κ : _root_.Address → KKey} {Γ Γ' : Nat → KExpr} {h : Heap F} :
    ∀ {d : Nat} {p : SourceValue F}, TypesRep κ Γ h d p → (∀ j, j < d → Γ' j = Γ j) →
      TypesRep κ Γ' h d p := by
  intro d p r
  induction r with
  | nil cell => intro _; exact .nil cell
  | @cons d addr tp rest cell rt rr ih =>
    intro hΓ
    refine .cons cell ?_ (ih fun j hj => hΓ j (by omega))
    rw [hΓ d (by omega)]
    exact Tm.congr_ghost (fun j hj => hΓ j (by omega)) rt

/-- **Opening a binder extends the context list**: a fresh `Cons(ty, types)` cell is the context
list at depth `d + 1` of the ghost context extended by the domain's image. -/
theorem types_extend {c : Ctx} {Γ : Nat → KExpr} {h : Heap F} {d : Nat}
    {types tp : SourceValue F} {T : KExpr} (htypes : c.types Γ h d types) (hT : c.tm d Γ h T tp) :
    c.types (Ghost.extend Γ d T) (h ++ [.construct kexprListEnum "Cons" [tp, types]]) (d + 1)
      (.ptr (.enum kexprListEnum) h.length) := by
  have ext := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [tp, types])
  refine ⟨.cons List.getElem?_concat_length ?_
    ((typesRep_congr htypes.1 (Ghost.extend_below Γ d T)).mono ext),
    htypes.2.extend (Tm.wscopedB htypes.2 hT)⟩
  rw [Ghost.extend_at]
  exact (Tm.congr_ghost (Ghost.extend_below Γ d T) hT).mono ext

theorem lamPw_some {e : KExpr} {p : Ix.Kernel.PropWhen} (h : e.lamPw = some p) :
    ∃ T B m, e = .lam T B m ∧ m.pw = p := by
  cases e with
  | lam T B m => exact ⟨T, B, m, rfl, Option.some.inj h⟩
  | _ => exact absurd h (by simp [Ix.Kernel.Expr.lamPw])

/-- `Lists::length` on a level list. -/
theorem klevel_length {ls : List KLevel} {l r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [l] h r h' cs)
    (hl : RepKLevelList h ls l) : r = .field (ls.length : F) ∧ h' = h := by
  rw [← Obs.Names.«Lists::length<&KernelTypes::KLevelNode>».symbol] at ev
  exact Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KLevelNode" [])) (R := RepKLevel)
    ev hl

theorem lvEq_imax {u v lu lv : KLevel} (hu : LvEq u lu) (hv : LvEq v lv) :
    LvEq (.imax u v) (IxVM.Refinement.KernelLevels.levelIMax lu lv) := by
  intro φ
  rw [IxVM.Refinement.KernelLevels.eval_levelIMax]
  simp only [Ix.Kernel.Level.eval, hu φ, hv φ]

theorem lvEq_succ_reduce {u l : KLevel} (hu : LvEq u l) :
    LvEq (.succ u) (IxVM.Refinement.KernelLevels.levelReduce (.succ l)) := by
  intro φ
  rw [IxVM.Refinement.KernelLevels.eval_levelReduce]
  simp only [Ix.Kernel.Level.eval, hu φ]

/-- **`Infer.lam` from the circuit's datum check**: at a body that is a `λ` the data agree; else
the datum is the zero-ness of the io-grade sort of the body's type, which also settles a body whose
image is a `λ` (`pw_of_lam_sortPw`: the type of a `λ` is a `∀` of the same datum, whose sort's
zero-ness is the datum). -/
theorem lam_infer {env : Ix.Kernel.Env .anon} {g : Ix.Kernel.Rules.Grade} {d : Nat}
    {T B S BT : KExpr} {u ℓ : KLevel}
    (hTS : g = .full → Infer env .full d T S) (hSu : g = .full → Red env d S (.sort u))
    (hinfB : Infer env g (d + 1) (B.instantiate1 (.fvar d T)) BT)
    (hdat : (∃ (T' B' : KExpr) (ℓ' : KLevel), B.instantiate1 (.fvar d T) = .lam T' B' (bmeta ℓ') ∧
        (bmeta ℓ).pw = (bmeta ℓ').pw) ∨ Specs.Infer.SortPw env (d + 1) BT (bmeta ℓ).pw) :
    Infer env g d (.lam T B (bmeta ℓ)) (.forallE T (BT.abstract1 d) (bmeta ℓ)) := by
  have e : (B.instantiate1 (.fvar d T)).lamPw = B.lamPw := by
    rw [InferAux.lamPw_instantiate1_fvar]
  rcases hdat with ⟨T', B', ℓ', hBo, hpw⟩ | ⟨btt, v, hI, hR, hz⟩
  · have hlp : B.lamPw = some (bmeta ℓ').pw := by
      rw [← e, hBo]; rfl
    exact Infer.lam (btt := .sort .zero) (v := .zero) hTS hSu hinfB
      (fun pwI hp => by
        rw [hlp] at hp
        injection hp with hp
        rw [← hp]
        exact hpw)
      (fun hn => by rw [hlp] at hn; cases hn) (fun hn => by rw [hlp] at hn; cases hn)
      (fun hn => by rw [hlp] at hn; cases hn)
  · exact Infer.lam hTS hSu hinfB
      (fun pwI hp => by
        obtain ⟨T', B', m', hBo, rfl⟩ := lamPw_some (e.trans hp)
        rw [hBo] at hinfB
        exact InferAux.pw_of_lam_sortPw hinfB ⟨btt, v, hI, hR, hz⟩)
      (fun _ => hI) (fun _ => hR) (fun _ => hz)

end InferBase

open InferBase

/-- `KernelInfer::k_infer_core`: one step of full-grade inference by the head node. -/
theorem k_infer_core_step (c : Ctx) (hc : CoreFacts c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::k_infer_core" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.k_infer_core c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  have p := Obs.«KernelInfer::k_infer_core».obs ev
  cases p
  case BVar x_i cs28 ld12 ev30 hc47 =>
    subst hc47
    obtain ⟨i, rfl, -, hcase⟩ := hE.bvar_of_load ld12
    obtain ⟨hid, hT⟩ := ih.get (.infer .types_lookup) (by lt_calls) ev30 types i rfl
      (good.sub fun x hx => by simp [hx]) d Γ htypes
    rcases hcase with ⟨hik, -⟩ | ⟨-, -, rfl⟩
    · exact absurd hik (Nat.not_lt_zero _)
    · exact ⟨_, hT, .fvar (show d - 1 - (ZMod.val i - 0) < d by omega)⟩
  case Srt x_l v68 m70 cs78 m83 ld12 he64 hm63 hm91 ev80 hc103 =>
    subst hc103 hm91
    obtain ⟨u, rfl, l, hl, hul⟩ := hE.sort_of_load ld12
    obtain ⟨hred, -⟩ := ih.get (.levelOps .level_reduce) (by lt_calls) ev80 _ rfl
      (good.sub fun x hx => by simp [hx]).2 _
      (IxVM.Refinement.KernelLevels.RepKLevel.allocSucc hl).1
    refine ⟨.sort (.succ u), ?_, .sort⟩
    rw [he64, hm63]
    exact .sort List.getElem?_concat_length (hred.mono (Heap.Extends.snoc _ _))
      (lvEq_succ_reduce hul)
  case Const x_addr x_lvls v121 m122 p129 cs135 v146 m147 cs157 v168 m169 cs179 v218 m219 cs229
      cs243 ld12 ev137 ld131 ev159 ev181 heq217 ev231 ev245 hc262 =>
    subst hc262
    obtain ⟨a, us, rfl, ha, ls, hls, hus⟩ := hE.const_of_load ld12
    obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev137 x_addr a rfl
      (good.sub fun x hx => by simp [hx]) ha
    rw [ld131] at hld
    injection hld with hv
    subst hv
    have e1 := ObsFn.heap_extends ev137
    obtain ⟨hnl, hm147⟩ := ih.get (.infer .const_num_lvls) (by lt_calls) ev159 _ ci rfl
      (good.sub fun x hx => by simp [hx]) hci
    rw [hm147] at ev181
    obtain ⟨hlen, hm169⟩ := klevel_length ev181 (hls.mono e1)
    have hb : ls.length < 549755813888 := by
      have := RomBound.bounded_length_lt good.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [x_lvls], m147⟩) (p := x_lvls)
        (by simp) (by simp) (by rw [hm147]; exact hls.mono e1)
      simpa using this
    obtain ⟨cn, nl, ty, rest, hcv, hval⟩ := hci.head
    have hps : ci.toConstantVal.levelParams.length < 4294967296 := hval.2.1
    rw [hlen, hnl] at heq217
    have hlsps : ls.length = ci.toConstantVal.levelParams.length :=
      (NatAux.natCast_inj (by omega) (by omega)).mp (NatAux.field_inj heq217)
    have hus' : us.length = ci.toConstantVal.levelParams.length :=
      (Ix.Kernel.Level.EvalEqList.length_eq (hus fun _ => 0)).trans hlsps
    rw [hm169] at ev231
    obtain ⟨hty, hm219⟩ := ih.get (.infer .const_type_of) (by lt_calls) ev231 _ ci rfl
      (good.sub fun x hx => by simp [hx]) hci
    rw [hm219] at ev245 hty
    have hinst := ih.get (.subst .expr_inst_levels) (by lt_calls) ev245 v218 x_lvls rfl
      (good.sub fun x hx => by simp [hx]) Γ 0 _ us (hty 0 Γ) ⟨ls, hls.mono e1, hus⟩
    rw [InferAux.posOf_instantiateLevelParams_perm hval.2.2.1 hus'] at hinst
    exact ⟨_, Tm.of_depth_zero hinst d, .const hfind hci.isTowerEntry hus'⟩
  case App w270 w271 m283 cs294 x_head x_args v321 m322 cs332 cs362 m392 ld12 ev296 ev334 hm400
      ev364 hc411 =>
    subst hc411 hm400
    obtain ⟨hd, sp, H, As, htup, hH, hAs, hEq⟩ := ih.get (.subst .collect_spine) (by lt_calls)
      ev296 e rfl (good.sub fun x hx => by simp [hx]) d Γ 0 E hE
    injection htup with hl
    injection hl with h1 hl'
    injection hl' with h2 h3
    subst h1 h2
    have e1 := ObsFn.heap_extends ev296
    obtain ⟨TH, hTH, hinfH⟩ := ih.get (.infer .k_infer) (by lt_calls) ev334 rc x_head types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) H hH
    have e2 := ObsFn.heap_extends ev334
    have x1 := Heap.Extends.snoc m322 (.construct kexprListEnum "Nil" [])
    obtain ⟨T, hT, hinf⟩ := ih.get (.infer .k_infer_app_spine_loop) (by lt_calls) ev364 rc v321
      x_args _ types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono (e1.trans (e2.trans x1)) hrc)
      d Γ (types_mono (e1.trans (e2.trans x1)) htypes) [] As TH H (TmL.store_nil m322)
      (Tm.mono x1 hTH) (TmL.mono (e2.trans x1) hAs)
      (by rw [Ix.Kernel.Expr.instantiateList_nil]; exact hinfH)
    refine ⟨T, hT, ?_⟩
    rw [hEq]
    exact hinf
  case Lam x_ty x_body x_bl v435 m436 cs446 m474 v504 m505 cs515 v542 m543 cs553 ld12 ev448 hm484
      ev517 ev555 he600 hm599 hc628 =>
    subst hc628 hm484
    obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hE.lam_of_load ld12
    obtain ⟨S, u, hTS, hSu, -⟩ := ih.get (.infer .k_ensure_sort) (by lt_calls) ev448 rc x_ty types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes T hT
    have e1 := ObsFn.heap_extends ev448
    have x1 := Heap.Extends.snoc m436 (.construct kexprListEnum "Cons" [x_ty, types])
    have ht2 := types_extend (types_mono e1 htypes) (Tm.mono e1 hT)
    have hBo := Tm.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)
      ((hB.mono e1).mono x1)
    obtain ⟨BT, hBT, hinfB⟩ := ih.get (.infer .k_infer) (by lt_calls) ev517 rc x_body _ rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (e1.trans x1) hrc) (d + 1) _ ht2 _ hBo
    have e2 := ObsFn.heap_extends ev517
    have E2 := (e1.trans x1).trans e2
    have hdat := ih.get (.infer .lam_datum_ok) (by lt_calls) ev555 rc x_body v504 x_bl _ rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E2 hrc) (d + 1) _ (types_mono e2 ht2) _ BT ℓ
      (Tm.mono e2 hBo) hBT (hℓ.mono E2)
    have e3 := ObsFn.heap_extends ev555
    have E3 := E2.trans e3
    refine ⟨.forallE T (BT.abstract1 d) (bmeta ℓ), ?_,
      lam_infer (fun _ => hTS) (fun _ => hSu) hinfB hdat⟩
    rw [he600, hm599]
    have x2 := Heap.Extends.snoc m543 (.construct kexprEnum "Forall" [x_ty, v504, x_bl])
    exact .forallE List.getElem?_concat_length ((Tm.mono E3 hT).mono x2)
      ((Tm.close (Ghost.extend_below Γ d T) (Tm.mono e3 hBT)).mono x2) ((hℓ.mono E3).mono x2)
  case Forall x_ty x_body x_bl v651 m652 cs662 m690 v720 m721 cs731 v758 m759 cs769 v796 m798
      cs806 ld12 ev664 hm700 ev733 ev771 he792 hm791 ev808 hc825 =>
    subst hc825 hm700
    obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hE.forallE_of_load ld12
    obtain ⟨S, u, hTS, hSu, lu, hlu, hule⟩ := ih.get (.infer .k_ensure_sort) (by lt_calls) ev664 rc
      x_ty types rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes T hT
    have e1 := ObsFn.heap_extends ev664
    have x1 := Heap.Extends.snoc m652 (.construct kexprListEnum "Cons" [x_ty, types])
    have ht2 := types_extend (types_mono e1 htypes) (Tm.mono e1 hT)
    have hBo := Tm.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)
      ((hB.mono e1).mono x1)
    obtain ⟨S2, v, hBS, hSv, lv, hlv, hvle⟩ := ih.get (.infer .k_ensure_sort) (by lt_calls) ev733
      rc x_body _ rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono (e1.trans x1) hrc) (d + 1) _
      ht2 _ hBo
    have e2 := ObsFn.heap_extends ev733
    have E2 := (e1.trans x1).trans e2
    have hz := ih.get (.infer .forall_datum_ok) (by lt_calls) ev771 v720 x_bl rfl
      (good.sub fun x hx => by simp [hx]) v ℓ ⟨lv, hlv, hvle⟩ (hℓ.mono E2)
    have e3 := ObsFn.heap_extends ev771
    obtain ⟨himax, -⟩ := ih.get (.levelOps .level_imax) (by lt_calls) ev808 v651 v720 rfl
      (good.sub fun x hx => by simp [hx]).2 lu lv (hlu.mono (x1.trans (e2.trans e3))) (hlv.mono e3)
    refine ⟨.sort (.imax u v), ?_, .forallE hTS hSu hBS hSv hz⟩
    rw [he792, hm791]
    exact .sort List.getElem?_concat_length (himax.mono (Heap.Extends.snoc _ _))
      (lvEq_imax hule hvle)
  case Let x_ty x_val x_body cs851 ld12 ev853 hc894 =>
    subst hc894
    obtain ⟨Ty, V, B, rfl, hTy, hV, hB⟩ := hE.letE_of_load ld12
    exact ih.get (.infer .k_infer_let_start) (by lt_calls) ev853 rc x_ty x_val x_body types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes Ty V B hTy hV hB
  case Lit x_lit cs910 ld12 ev912 hc929 =>
    subst hc929
    rcases hE.lit_of_load ld12 with ⟨lp, limbs, rfl, hl, -, rfl⟩ | ⟨bp, bytes, s, rfl, hb, hs, rfl⟩
    · exact ih.get (.infer .k_infer_lit) (by lt_calls) ev912 rc _ rfl
        (good.sub fun x hx => by simp [hx]) hrc _ (.inl ⟨lp, _, rfl, ⟨limbs, hl, rfl⟩, rfl⟩) d Γ
    · exact ih.get (.infer .k_infer_lit) (by lt_calls) ev912 rc _ rfl
        (good.sub fun x hx => by simp [hx]) hrc _ (.inr ⟨bp, bytes, s, rfl, hb, hs, rfl⟩) d Γ
  case Proj x_struct_addr x_fidx x_e1 cs955 ld12 ev957 hc998 =>
    subst hc998
    obtain ⟨a, i, Es, rfl, rfl, ha, hEs⟩ := hE.proj_of_load ld12
    exact ih.get (.infer .k_infer_proj) (by lt_calls) ev957 rc x_struct_addr _ x_e1 types rfl
      (good.sub fun x hx => by simp [hx]) hrc i rfl d Γ htypes a Es ha hEs

/-- `KernelInferOnly::k_infer_only_core`: one step of io-grade inference by the head node, given
the projection arm (`hproj`: at a term whose node is a projection, the spec holds). -/
theorem k_infer_only_core_step_of_proj (c : Ctx) (hc : CoreFacts c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInferOnly::k_infer_only_core" args h r h' calls) (ih : IH c calls)
    (hproj : ∀ rc e types sa fi e1, args = [rc, e, types] →
      loadValue h e = .ok (.construct kexprEnum "Proj" [sa, fi, e1]) →
        Specs.Infer.k_infer_only_core c args h r h' calls) :
    Specs.Infer.k_infer_only_core c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  have p := Obs.«KernelInferOnly::k_infer_only_core».obs ev
  cases p
  case BVar x_i cs28 ld12 ev30 hc47 =>
    subst hc47
    obtain ⟨i, rfl, -, hcase⟩ := hE.bvar_of_load ld12
    obtain ⟨hid, hT⟩ := ih.get (.infer .io_types_lookup) (by lt_calls) ev30 types i rfl
      (good.sub fun x hx => by simp [hx]) d Γ htypes
    rcases hcase with ⟨hik, -⟩ | ⟨-, -, rfl⟩
    · exact absurd hik (Nat.not_lt_zero _)
    · exact ⟨_, hT, .fvar (show d - 1 - (ZMod.val i - 0) < d by omega)⟩
  case Srt x_l v68 m70 cs78 m83 ld12 he64 hm63 hm91 ev80 hc103 =>
    subst hc103 hm91
    obtain ⟨u, rfl, l, hl, hul⟩ := hE.sort_of_load ld12
    obtain ⟨hred, -⟩ := ih.get (.levelOps .level_reduce) (by lt_calls) ev80 _ rfl
      (good.sub fun x hx => by simp [hx]).2 _
      (IxVM.Refinement.KernelLevels.RepKLevel.allocSucc hl).1
    refine ⟨.sort (.succ u), ?_, .sort⟩
    rw [he64, hm63]
    exact .sort List.getElem?_concat_length (hred.mono (Heap.Extends.snoc _ _))
      (lvEq_succ_reduce hul)
  case Const x_addr x_lvls v121 m122 p129 cs135 v146 m147 cs157 v179 m182 cs190 v209 m210 cs220
      cs234 ld12 ev137 ld131 ev159 ev192 heq208 ev222 ev236 hc253 =>
    subst hc253
    obtain ⟨a, us, rfl, ha, ls, hls, hus⟩ := hE.const_of_load ld12
    obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev137 x_addr a rfl
      (good.sub fun x hx => by simp [hx]) ha
    rw [ld131] at hld
    injection hld with hv
    subst hv
    have e1 := ObsFn.heap_extends ev137
    obtain ⟨hnl, hm147⟩ := ih.get (.infer .io_const_num_lvls) (by lt_calls) ev159 _ ci rfl
      (good.sub fun x hx => by simp [hx]) hci
    rw [hm147] at ev192
    obtain ⟨hlen, hm182⟩ := klevel_length ev192 (hls.mono e1)
    have hb : ls.length < 549755813888 := by
      have := RomBound.bounded_length_lt good.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [x_lvls], m147⟩) (p := x_lvls)
        (by simp) (by simp) (by rw [hm147]; exact hls.mono e1)
      simpa using this
    obtain ⟨cn, nl, ty, rest, hcv, hval⟩ := hci.head
    have hps : ci.toConstantVal.levelParams.length < 4294967296 := hval.2.1
    rw [hlen, hnl] at heq208
    have hlsps : ls.length = ci.toConstantVal.levelParams.length :=
      (NatAux.natCast_inj (by omega) (by omega)).mp (NatAux.field_inj heq208)
    have hus' : us.length = ci.toConstantVal.levelParams.length :=
      (Ix.Kernel.Level.EvalEqList.length_eq (hus fun _ => 0)).trans hlsps
    rw [hm182] at ev222
    obtain ⟨hty, hm210⟩ := ih.get (.infer .io_const_type_of) (by lt_calls) ev222 _ ci rfl
      (good.sub fun x hx => by simp [hx]) hci
    rw [hm210] at ev236 hty
    have hinst := ih.get (.subst .expr_inst_levels) (by lt_calls) ev236 v209 x_lvls rfl
      (good.sub fun x hx => by simp [hx]) Γ 0 _ us (hty 0 Γ) ⟨ls, hls.mono e1, hus⟩
    rw [InferAux.posOf_instantiateLevelParams_perm hval.2.2.1 hus'] at hinst
    exact ⟨_, Tm.of_depth_zero hinst d, .const hfind hci.isTowerEntry hus'⟩
  case App_Forall x_f x_a v271 m272 cs282 x_dom x_cod x_bl cs346 ld12 ev284 ld320 ev348 hc397 =>
    subst hc397
    obtain ⟨F0, A, rfl, hF, hA⟩ := hE.app_of_load ld12
    obtain ⟨TF, hTF, hinfF⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev284 rc x_f types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes F0 hF
    have e1 := ObsFn.heap_extends ev284
    obtain ⟨D, C, ℓ, rfl, hD, hC, hℓ⟩ := hTF.forallE_of_load ld320
    obtain ⟨hr, hcase⟩ := ih.get (.infer .io_app_cod) (by lt_calls) ev348 rc x_dom x_cod x_bl x_a
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes)
      D C ℓ A hD hC hℓ (Tm.mono e1 hA)
    refine ⟨_, hr, ?_⟩
    rcases hcase with hnv | ⟨TA, hTA, hdeq⟩
    · exact .appSkip hinfF .refl hnv
    · exact .app hinfF .refl hTA hdeq
  case App_other x_f x_a v271 m272 cs282 v309 v402 m403 cs413 x_dom x_cod x_bl cs477 ld12 ev284
      ld320 hne398 ev415 ld451 ev479 hc528 =>
    subst hc528
    obtain ⟨F0, A, rfl, hF, hA⟩ := hE.app_of_load ld12
    obtain ⟨TF, hTF, hinfF⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev284 rc x_f types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes F0 hF
    have e1 := ObsFn.heap_extends ev284
    obtain ⟨X, hX, hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev415 rc v271 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) TF hTF
    have e2 := e1.trans (ObsFn.heap_extends ev415)
    obtain ⟨D, C, ℓ, rfl, hD, hC, hℓ⟩ := hX.forallE_of_load ld451
    obtain ⟨hr, hcase⟩ := ih.get (.infer .io_app_cod) (by lt_calls) ev479 rc x_dom x_cod x_bl x_a
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e2 hrc) d Γ (types_mono e2 htypes)
      D C ℓ A hD hC hℓ (Tm.mono e2 hA)
    refine ⟨_, hr, ?_⟩
    rcases hcase with hnv | ⟨TA, hTA, hdeq⟩
    · exact .appSkip hinfF hred hnv
    · exact .app hinfF hred hTA hdeq
  case Lam x_ty x_body x_bl m553 v583 m584 cs594 v621 m622 cs632 ld12 hm563 ev596 ev634 he679
      hm678 hc707 =>
    subst hc707 hm563
    obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hE.lam_of_load ld12
    have x1 := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [x_ty, types])
    have ht2 := types_extend htypes hT
    have hBo := Tm.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T) (hB.mono x1)
    obtain ⟨BT, hBT, hinfB⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev596 rc x_body _ rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) (d + 1) _ ht2 _ hBo
    have e2 := ObsFn.heap_extends ev596
    have E2 := x1.trans e2
    have hdat := ih.get (.infer .lam_datum_ok) (by lt_calls) ev634 rc x_body v583 x_bl _ rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E2 hrc) (d + 1) _ (types_mono e2 ht2) _ BT ℓ
      (Tm.mono e2 hBo) hBT (hℓ.mono E2)
    have e3 := ObsFn.heap_extends ev634
    have E3 := E2.trans e3
    refine ⟨.forallE T (BT.abstract1 d) (bmeta ℓ), ?_,
      lam_infer (S := T) (u := .zero) (fun hg => nomatch hg) (fun hg => nomatch hg) hinfB hdat⟩
    rw [he679, hm678]
    have x2 := Heap.Extends.snoc m622 (.construct kexprEnum "Forall" [x_ty, v583, x_bl])
    exact .forallE List.getElem?_concat_length ((Tm.mono E3 hT).mono x2)
      ((Tm.close (Ghost.extend_below Γ d T) (Tm.mono e3 hBT)).mono x2) ((hℓ.mono E3).mono x2)
  case Forall x_ty x_body x_bl v730 m731 cs741 m769 v799 m800 cs810 v837 m838 cs848 v875 m877
      cs885 ld12 ev743 hm779 ev812 ev850 he871 hm870 ev887 hc904 =>
    subst hc904 hm779
    obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hE.forallE_of_load ld12
    obtain ⟨S, u, hTS, hSu, lu, hlu, hule⟩ := ih.get (.infer .ensure_sort_only) (by lt_calls) ev743
      rc x_ty types rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes T hT
    have e1 := ObsFn.heap_extends ev743
    have x1 := Heap.Extends.snoc m731 (.construct kexprListEnum "Cons" [x_ty, types])
    have ht2 := types_extend (types_mono e1 htypes) (Tm.mono e1 hT)
    have hBo := Tm.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)
      ((hB.mono e1).mono x1)
    obtain ⟨S2, v, hBS, hSv, lv, hlv, hvle⟩ := ih.get (.infer .ensure_sort_only) (by lt_calls)
      ev812 rc x_body _ rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono (e1.trans x1) hrc)
      (d + 1) _ ht2 _ hBo
    have e2 := ObsFn.heap_extends ev812
    have E2 := (e1.trans x1).trans e2
    have hz := ih.get (.infer .forall_datum_ok) (by lt_calls) ev850 v799 x_bl rfl
      (good.sub fun x hx => by simp [hx]) v ℓ ⟨lv, hlv, hvle⟩ (hℓ.mono E2)
    have e3 := ObsFn.heap_extends ev850
    obtain ⟨himax, -⟩ := ih.get (.levelOps .level_imax) (by lt_calls) ev887 v730 v799 rfl
      (good.sub fun x hx => by simp [hx]).2 lu lv (hlu.mono (x1.trans (e2.trans e3))) (hlv.mono e3)
    refine ⟨.sort (.imax u v), ?_, .forallE hTS hSu hBS hSv hz⟩
    rw [he871, hm870]
    exact .sort List.getElem?_concat_length (himax.mono (Heap.Extends.snoc _ _))
      (lvEq_imax hule hvle)
  case Let w912 x_val x_body v928 m929 cs939 cs968 ld12 ev941 ev970 hc995 =>
    subst hc995
    obtain ⟨Ty, V, B, rfl, -, hV, hB⟩ := hE.letE_of_load ld12
    have hB' : c.tmk d Γ (ZMod.val (0 : F) + 1) h B x_body := by rw [ZMod.val_zero]; exact hB
    have hi := ih.get (.subst .expr_inst1) (by lt_calls) ev941 x_body x_val 0 rfl
      (good.sub fun x hx => by simp [hx]) d Γ B V hB' hV
    rw [ZMod.val_zero] at hi
    have e1 := ObsFn.heap_extends ev941
    obtain ⟨T, hT, hinf⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev970 rc v928 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes)
      (B.instantiate1 V 0) hi
    refine ⟨T, hT, ?_⟩
    rw [instShift_eq_instantiate1 hV.looseBVarsBounded]
    exact hinf
  case Lit_Nat w1024 v1038 m1041 cs1049 v1053 m1062 cs1070 m1074 ld12 he1034 hm1033 ev1072 ev1051
      hm1082 hc1086 =>
    subst hc1086
    obtain ⟨hv, hm⟩ := ih.get (.roles .role_nat) (by lt_calls) ev1072 rfl
    rw [hv, hm] at ev1051
    obtain ⟨a, ha, hb, hf⟩ := ih.get (.roles .role_addr) (by lt_calls) ev1051 rc .nat rfl
      (good.sub fun x hx => by simp [hx]) hrc
    rcases hE.lit_of_load ld12 with ⟨lp, limbs, hx, -, -, rfl⟩ | ⟨bp, bytes, s, hx, -, -, -⟩
    · rw [he1034]
      exact ⟨_, PrimStrAux.tmc_role_const_nil hc ha hb hm1082 hm1033 d Γ,
        .natLit (PrimNat.natLit_of_natBlock hc hf (by decide) (by decide) (by decide))⟩
    · injection hx with _ h2
      exact absurd h2 (by decide)
  case Lit_Str w1094 v1108 m1111 cs1119 v1123 m1132 cs1140 m1144 ld12 he1104 hm1103 ev1142 ev1121
      hm1152 hc1156 =>
    subst hc1156
    obtain ⟨hv, hm⟩ := ih.get (.roles .role_string) (by lt_calls) ev1142 rfl
    rw [hv, hm] at ev1121
    obtain ⟨a, ha, hb, hf⟩ := ih.get (.roles .role_used_implicitly) (by lt_calls) ev1121 rc .string
      rfl (good.sub fun x hx => by simp [hx]) hrc
    rcases hE.lit_of_load ld12 with ⟨lp, limbs, hx, -, -, -⟩ | ⟨bp, bytes, s, hx, -, -, rfl⟩
    · injection hx with _ h2
      exact absurd h2 (by decide)
    · rw [he1104]
      exact ⟨_, PrimStrAux.tmc_role_const_nil hc ha hb hm1152 hm1103 d Γ, .strLit (hc.env.strLit hf)⟩
  case Proj x_struct_addr x_fidx x_e1
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact hproj rc e types x_struct_addr x_fidx x_e1 rfl ld12 rc e types rfl good hrc d Γ htypes E hE

end IxVM.Refinement.Core
