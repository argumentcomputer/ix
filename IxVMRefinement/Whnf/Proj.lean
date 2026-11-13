import IxVMRefinement.Whnf.Delta
import IxVMRefinement.Lib.Bytes

/-! # Step lemma of `KernelWhnf::red_proj`: the structural projection

`red_proj` fires at a scrutinee `C us As` whose head is a constructor of member `i` of a block
`b` that IxVM does not model (`block_is_modeled` answers `0`), the projected structure being
that member, with one constructor, no index, the constructor's parameter count, `As` of length
`nP + nF`, `us` of the constructor's level count, the field below `nF`, and the structure's sort
after its parameters never zero at `us` (`type_sort_never`). Then the structure's projection
table (`LoadFacts.projTablesAt`) has the entry `Red.proj` reads: its head data (`TowerHead`)
make `FireSem` vacuous (the stored sort `structSort` is the structure's sort, which is never zero
at `us`), and the constructor's binders carry the zero-ness of that sort, so its licensed
`Certs` over `As` is all `never` skips. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red Certs)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)

set_option linter.unusedVariables false

namespace WhnfAux

/-- A loaded `Ctor` represents a stored constructor. -/
theorem ctor_inv {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty blk ind cidx np nf u : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon}
    (r : CIRep κ h (.construct kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, u]) ci) :
    ∃ (cv : Ix.Kernel.ConstantVal .anon) (nP nF : Nat), ci = .ctorInfo cv nP nF ∧
      ValRep κ h nl ty cv ∧ np = .field (nP : F) ∧ nf = .field (nF : F) ∧
      nP < 72057594037927936 ∧ nF < 72057594037927936 ∧
      ∃ (b : Bytes.Address) (i j : F), Bytes.RepAddressRef addrTy h b blk ∧ ind = .field i ∧
        cidx = .field j ∧ cv.name = κ (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j)) := by
  generalize hv : (Value.construct kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, u] :
    SourceValue F) = v at r
  cases r
  case ctor hv' hnp hnf hcounts hkey =>
    injection hv with _ _ hl
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hl
    exact ⟨_, _, _, rfl, hv', hnp, hnf, hcounts.1, hcounts.2, hkey⟩
  all_goals (injection hv with _ hc _; exact absurd hc (by decide))

/-- A loaded `Induct` represents a stored inductive. -/
theorem ind_inv {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty np ni nc u blk idx : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon}
    (r : CIRep κ h (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) ci) :
    ∃ (cv : Ix.Kernel.ConstantVal .anon) (caps : Ix.Kernel.IndCaps .anon) (nP nI nC : Nat),
      ci = .indInfo cv caps ∧ ValRep κ h nl ty cv ∧ np = .field (nP : F) ∧
      ni = .field (nI : F) ∧ nc = .field (nC : F) ∧ nP < 72057594037927936 ∧
      nI < 72057594037927936 ∧ nC < 72057594037927936 ∧
      ∃ (b : Bytes.Address) (i : F), Bytes.RepAddressRef addrTy h b blk ∧ idx = .field i ∧
        cv.name = κ (iprjAddr (ixAddr b) (ZMod.val i)) := by
  generalize hv : (Value.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx] :
    SourceValue F) = v at r
  cases r
  case induct hv' hcounts hkey =>
    injection hv with _ _ hl
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hl
    obtain ⟨nP, nI, nC, h1, h2, h3, h4, h5, h6⟩ := hcounts
    exact ⟨_, _, nP, nI, nC, rfl, hv', h1, h2, h3, h4, h5, h6, hkey⟩
  all_goals (injection hv with _ hc _; exact absurd hc (by decide))

/-- A stored constant's name is the key it is found at. -/
theorem name_of_find {env : Ix.Kernel.Env .anon} {k : KKey} {ci : Ix.Kernel.ConstantInfo .anon}
    (h : env.find? k = some ci) : ci.name = k := by
  have h1 := List.find?_some h
  simpa using h1

/-- A `0`/`1` answer that is not `0` is `1`'s condition. -/
theorem ite01 {p : Prop} [Decidable p] (h : (if p then (1 : F) else 0) ≠ 0) : p := by
  by_contra hp
  exact h (by rw [ite_eq_right hp])

/-- The sort after the first `n` binders of a level-instantiated telescope. -/
theorem piSortAt_ilp_of_strip (ks : List Ix.Kernel.LevelParam) (vs : List KLevel) :
    ∀ (n : Nat) (T : KExpr) (bs : List (KExpr × Ix.Kernel.BinderMeta)) (σ : KLevel),
      T.stripPis n = some (bs, .sort σ) →
      piSortAt n (T.instantiateLevelParams ks vs) = some (Ix.Kernel.Level.subst ks vs σ)
  | 0, T, bs, σ, h => by
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  | n + 1, T, bs, σ, h => by
    cases T
    case forallE ty b m =>
      simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', e⟩, hb, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact piSortAt_ilp_of_strip ks vs n b bs' σ hb
    all_goals simp [Ix.Kernel.Expr.stripPis] at h

/-- The first `n` binders are `∀`s whose data are `never`. -/
def PisNv : Nat → KExpr → Prop
  | 0, _ => True
  | n + 1, .forallE _ b m => m.pw.isNever = true ∧ PisNv n b
  | _ + 1, _ => False

theorem pisNv_instantiate1 :
    ∀ (n : Nat) (T A : KExpr) (k : Nat), PisNv n T → PisNv n (T.instantiate1 A k)
  | 0, _, _, _, _ => trivial
  | n + 1, T, A, k, h => by
    cases T
    case forallE ty b m =>
      have h' : m.pw.isNever = true ∧ PisNv n b := h
      show m.pw.isNever = true ∧ PisNv n (b.instantiate1 A (k + 1))
      exact ⟨h'.1, pisNv_instantiate1 n b A (k + 1) h'.2⟩
    all_goals exact False.elim h

/-- **A licensed certificate of `never` slots**: every argument skips its certificate. -/
theorem certs_never {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (As : List KExpr) (T : KExpr), PisNv As.length T → Certs env d true T As
  | [], _, _ => .nil
  | A :: As, T, h => by
    cases T
    case forallE ty b m =>
      have h' : m.pw.isNever = true ∧ PisNv As.length b := h
      exact .skip rfl h'.1 (certs_never As _ (pisNv_instantiate1 As.length b A 0 h'.2))
    all_goals exact False.elim h

theorem pisNv_of_strip (ks : List Ix.Kernel.LevelParam) (vs : List KLevel) :
    ∀ (n : Nat) (T : KExpr) (bs : List (KExpr × Ix.Kernel.BinderMeta)) (body : KExpr),
      T.stripPis n = some (bs, body) →
      (∀ bm ∈ bs, (Ix.Kernel.Level.substPW ks vs bm.2.pw).isNever = true) →
      PisNv n (T.instantiateLevelParams ks vs)
  | 0, _, _, _, _, _ => trivial
  | n + 1, T, bs, body, h, hbs => by
    cases T
    case forallE ty b m =>
      simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', e⟩, hb, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      show (Ix.Kernel.Level.substPW ks vs m.pw).isNever = true ∧
        PisNv n (b.instantiateLevelParams ks vs)
      exact ⟨hbs (ty, m) (List.mem_cons_self ..),
        pisNv_of_strip ks vs n b bs' e hb (fun bm hm => hbs bm (List.mem_cons_of_mem _ hm))⟩
    all_goals simp [Ix.Kernel.Expr.stripPis] at h

end WhnfAux

/-- `KernelWhnf::red_proj`: tag `1` is `Red.proj` at the structure's projection table. -/
theorem red_proj_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::red_proj" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.red_proj c args h r h' calls := by
  intro rc sa fidx scrut types hargs good hrc d Γ htypes s fi S hs hfidx hS x hr
  subst hargs hfidx
  have p := Obs.«KernelWhnf::red_proj».obs ev
  cases p
  case Const_Ctor_Induct_n1_n0_n1 m2 cs13 x_head x_args x_caddr x_clvls m70 p78 cs84 x_cnl w101
      x_cblock x_cind w102 x_nparams x_nfields w103 m145 p153 cs159 x_snl x_sty x_snp x_sni x_snc
      w176 x_sblock x_sidx v217 m218 x225 y226 m227 x233 y234 m235 cs244 cs266 v269 cs289 v292
      v309 m310 x317 y318 m319 x325 y326 m327 cs336 cs350 v353 cs372 v375 v392 m393 x400 y401
      m402 cs411 v414 x421 y422 m423 cs432 cs456 v459 x466 m468 cs477 m490 x498 y499 x506 cs528
      m552 cs563 m579 cs590 v624 m633 cs641 v645 ev15 ld51 ev86 ld80 ev161 ld155 ev246 op283
      ev268 op240 op306 ev291 op232 ev338 op367 ev352 op332 op389 ev374 op324 ev434 op450 op428
      ev413 ev479 op473 ev458 op407 op521 op513 ev530 op505 ev565 ev592 he625 op666 ev643 he669
      hc670 =>
    subst hc670 he669
    obtain ⟨-, rfl⟩ := WhnfAux.tag_eq (hr.symm.trans he625)
    have h39 : (2 : ℕ) ^ 39 = 549755813888 := by norm_num
    -- the scrutinee: a constructor applied to a spine
    obtain ⟨hd', sp', H, Args, he, hH, hArgs, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls)
      ev15 scrut rfl (good.sub fun x hx => by simp [hx]) d Γ 0 S hS
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨ca, cus, rfl, hca, hcus⟩ := hH.const_of_load ld51
    have e15 := ObsFn.heap_extends ev15
    -- the constructor
    obtain ⟨ciC, hfindC, vC, hldC, hciC⟩ := ih.get (.callees .get_ci) (by lt_calls) ev86 x_caddr
      ca rfl (good.sub fun x hx => by simp [hx]) hca
    rw [ld80] at hldC
    injection hldC with hvC
    subst hvC
    obtain ⟨cvC, nP, nF, rfl, ⟨hcnl, hclt, hcperm, -⟩, rfl, rfl, hnP, hnF, bC, iC, jC, hbC, rfl,
      rfl, hnameC⟩ := WhnfAux.ctor_inv hciC
    subst hcnl
    have e86 := ObsFn.heap_extends ev86
    have ext70 := e15.trans e86
    -- the structure
    obtain ⟨ciS, hfindS, vS, hldS, hciS⟩ := ih.get (.callees .get_ci) (by lt_calls) ev161 sa s
      rfl (good.sub fun x hx => by simp [hx]) (Bytes.repAddressRef_heapMono₂ addrTy ext70 hs)
    rw [ld155] at hldS
    injection hldS with hvS
    subst hvS
    obtain ⟨cvS, caps, nPS, nIS, nCS, rfl, ⟨hsnl, hslt, hsperm, hsty⟩, rfl, rfl, rfl, hnPS, hnIS,
      hnCS, bS, iS, hbS, rfl, hnameS⟩ := WhnfAux.ind_inv hciS
    subst hsnl
    have e161 := ObsFn.heap_extends ev161
    -- the circuit's tests
    obtain ⟨rfl, -⟩ := Lib.address_eq_spec ev246 (Bytes.repAddressRef_heapMono₂ addrTy e161 hbC)
      hbS
    obtain rfl := NatAux.sub_ok op283
    obtain ⟨rfl, -⟩ := Lib.is_zero_field ev268
    obtain rfl := NatAux.mul_ok op240
    obtain rfl := NatAux.sub_ok op306
    obtain ⟨rfl, -⟩ := Lib.is_zero_field ev291
    obtain rfl := NatAux.mul_ok op232
    obtain ⟨rfl, -⟩ := Lib.is_zero_field ev338
    obtain rfl := NatAux.sub_ok op367
    obtain ⟨rfl, -⟩ := Lib.is_zero_field ev352
    obtain rfl := NatAux.mul_ok op332
    obtain rfl := NatAux.sub_ok op389
    obtain ⟨rfl, -⟩ := Lib.is_zero_field ev374
    obtain rfl := NatAux.mul_ok op324
    have ext310 : Heap.Extends m145 m310 := (ObsFn.heap_extends ev246).trans
      ((ObsFn.heap_extends ev268).trans ((ObsFn.heap_extends ev291).trans
        ((ObsFn.heap_extends ev338).trans ((ObsFn.heap_extends ev352).trans
          (ObsFn.heap_extends ev374)))))
    have e2_145 : Heap.Extends m2 m145 := e86.trans e161
    have ext310' := e2_145.trans ext310
    obtain ⟨rfl, -⟩ := PrimNat.kl_length ev434 (tml_mono ext310' hArgs)
    have hlenA : Args.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_args], m310⟩) (by simp)
      (by simp) (tml_mono ext310' hArgs)
    obtain rfl := NatAux.add_ok op450
    obtain rfl := NatAux.sub_ok op428
    obtain ⟨rfl, -⟩ := Lib.is_zero_field ev413
    obtain ⟨ls, hls, hEq⟩ := hcus
    have ext402 := ext310'.trans ((ObsFn.heap_extends ev434).trans (ObsFn.heap_extends ev413))
    obtain ⟨rfl, -⟩ := WhnfAux.lv_length ev479 (by rw [klevelListEnum_eq]; exact hls.mono ext402)
    have hlenL : ls.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [x_clvls], m402⟩) (by simp)
      (by simp) (hls.mono ext402)
    obtain rfl := NatAux.sub_ok op473
    obtain ⟨rfl, -⟩ := Lib.is_zero_field ev458
    obtain rfl := NatAux.mul_ok op407
    obtain rfl := NatAux.mul_ok op521
    obtain rfl := NatAux.mul_ok op513
    obtain ⟨a1, b1, ha1, hb1, ha32, hb32, rfl, -⟩ := Lib.less_than_fields_spec ev530
    obtain rfl := Value.field.inj ha1
    obtain rfl := Value.field.inj hb1
    have hmul := (NatAux.field_inj (NatAux.mul_ok op505)).symm
    have hA := left_ne_zero_of_mul_eq_one hmul
    have hLT := WhnfAux.ite01 (right_ne_zero_of_mul_eq_one hmul)
    have hB := left_ne_zero_of_mul hA
    have hC := right_ne_zero_of_mul hA
    have hLEN := WhnfAux.ite01 (left_ne_zero_of_mul hC)
    have hLV := WhnfAux.ite01 (right_ne_zero_of_mul hC)
    have hD := left_ne_zero_of_mul hB
    have hE := right_ne_zero_of_mul hB
    have hD2 := left_ne_zero_of_mul hD
    have hAB := WhnfAux.ite01 (left_ne_zero_of_mul hD2)
    have hCI := WhnfAux.ite01 (right_ne_zero_of_mul hD2)
    have hE2 := left_ne_zero_of_mul hE
    have hNP := WhnfAux.ite01 (right_ne_zero_of_mul hE)
    have hNI := WhnfAux.ite01 (left_ne_zero_of_mul hE2)
    have hNC := WhnfAux.ite01 (right_ne_zero_of_mul hE2)
    subst bC
    have hiC : iC = iS := sub_eq_zero.mp hCI
    subst iC
    -- the counts as naturals
    have hnI0 : nIS = 0 := (NatAux.natCast_eq_zero_iff (by omega)).mp hNI
    have hnC1 : nCS = 1 := by
      have h1 : ((nCS : ℕ) : F) = ((1 : ℕ) : F) := by rw [Nat.cast_one]; exact sub_eq_zero.mp hNC
      exact (NatAux.natCast_inj (by omega) (by omega)).mp h1
    have hnPS : nPS = nP := (NatAux.natCast_inj (by omega) (by omega)).mp (sub_eq_zero.mp hNP)
    subst nIS
    subst nCS
    subst nPS
    have hArgsLen : Args.length = nP + nF := by
      have h1 : ((Args.length : ℕ) : F) = ((nP + nF : ℕ) : F) := by
        rw [Nat.cast_add]; exact sub_eq_zero.mp hLEN
      exact (NatAux.natCast_inj (by omega) (by omega)).mp h1
    have hcusLen : cus.length = cvC.levelParams.length := by
      have h1 : ((ls.length : ℕ) : F) = ((cvC.levelParams.length : ℕ) : F) := sub_eq_zero.mp hLV
      rw [WhnfAux.evalEqList_length cus ls (hEq fun _ => 0)]
      exact (NatAux.natCast_inj (by omega) (by omega)).mp h1
    have hltF : ZMod.val fi < nF := by
      rwa [NatAux.val_natCast (n := nF) (by omega)] at hLT
    -- the projection table
    rw [Nat.cast_zero, Nat.cast_one] at ld155
    have ext490' : Heap.Extends m145 m490 := ext310.trans ((ObsFn.heap_extends ev434).trans
      ((ObsFn.heap_extends ev413).trans ((ObsFn.heap_extends ev479).trans
        ((ObsFn.heap_extends ev458).trans (ObsFn.heap_extends ev530)))))
    have hkC : c.κ (ixAddr ca) = c.κ (cprjAddr (ixAddr bS) (ZMod.val iS) (ZMod.val jC)) :=
      (WhnfAux.name_of_find hfindC).symm.trans hnameC
    have hkS : c.κ (ixAddr s) = c.κ (iprjAddr (ixAddr bS) (ZMod.val iS)) :=
      (WhnfAux.name_of_find hfindS).symm.trans hnameS
    have hfindC' := hfindC
    rw [hkC] at hfindC'
    obtain ⟨tbl, htbl, hsn, hctor, hnPt, hnFt, hlpt, -, hent, -, -, bsC, bodyC, hstripC, hbm⟩ :=
      hc.loads.projTablesAt x_sblock sa p153 _ x_sty _ w176 x_sblock m490 m552 m70 m145 cs563
        cs159 bS s iS ev565 (good.sub fun x hx => by simp [hx])
        (Bytes.repAddressRef_heapMono₂ addrTy ext490' hbS) ev161
        (good.sub fun x hx => by simp [hx]) (Bytes.repAddressRef_heapMono₂ addrTy ext70 hs) ld155
        hbS (ZMod.val jC) cvC nP nF hfindC'
    obtain ⟨hfp, -, -, -, ⟨cvT, capsT, hT, hlT, bsT, hsT⟩, -⟩ := hent (ZMod.val fi) hltF
    have hT' := hT
    rw [show (tbl.entry (ZMod.val fi)).structName = c.κ (ixAddr s) from hsn.trans hkS.symm,
      hfindS] at hT'
    injection hT' with hT'
    injection hT' with hcvT hcapsT
    subst cvT
    -- the structure's sort is never zero at the levels
    have ext552 := ext490'.trans (ObsFn.heap_extends ev565)
    obtain ⟨l, hl, hlnz⟩ := ih.get (.whnf .type_sort_never) (by lt_calls) ev592 x_sty _ x_clvls rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 (posOf cvS.levelParams cvS.type) (nP : F) cus
      (Tm.mono ext552 (hsty d Γ)) rfl ⟨ls, hls.mono (e2_145.trans ext552), hEq⟩ field_one_ne_zero
    rw [NatAux.val_natCast (n := nP) (by omega)] at hl
    have hlpS : cvS.levelParams = cvC.levelParams := hlT.trans hlpt
    have hsT' : cvS.type.stripPis nP = some (bsT, .sort tbl.structSort) := by
      have := hsT
      rw [show (tbl.entry (ZMod.val fi)).numParams = nP from hnPt] at this
      exact this
    have hl' := WhnfAux.piSortAt_ilp_of_strip cvS.levelParams (posLevels cvS.levelParams) nP
      cvS.type bsT tbl.structSort hsT'
    rw [show cvS.type.instantiateLevelParams cvS.levelParams (posLevels cvS.levelParams) =
      posOf cvS.levelParams cvS.type from rfl, hl] at hl'
    obtain rfl := Option.some.inj hl'
    have hcusS : cus.length = cvS.levelParams.length := by rw [hlpS]; exact hcusLen
    rw [WhnfAux.subst_posOf_level hsperm hcusS] at hlnz
    -- the reduct
    have ext579 := ext552.trans (ObsFn.heap_extends ev592)
    obtain rfl := NatAux.add_ok op666
    obtain ⟨⟨A, hA', hAt⟩, -⟩ := PrimNat.kl_lookup ev643 (tml_mono (e2_145.trans ext579) hArgs)
    have hvAdd : ZMod.val ((nP : F) + fi) = nP + ZMod.val fi := by
      have hcast : (nP : F) + fi = ((nP + ZMod.val fi : Nat) : F) := by
        rw [Nat.cast_add, NatAux.natCast_val]
      rw [hcast]
      exact NatAux.val_natCast (by omega)
    rw [hvAdd] at hA'
    refine ⟨A, Tm.mono (ObsFn.heap_extends ev643) hAt, ?_⟩
    have hredp : Red c.env d (.proj (c.κ (ixAddr s)) (ZMod.val fi)
        (Specs.Whnf.mkAppN (.const (c.κ (ixAddr ca)) cus) Args))
        ((Specs.Whnf.mkAppN (.const (c.κ (ixAddr ca)) cus) Args).getAppArgs.getD
          ((tbl.entry (ZMod.val fi)).numParams + ZMod.val fi) (.bvar 0)) := by
      refine Red.proj (entry := tbl.entry (ZMod.val fi)) (cvC := cvC) (nP := nP) (nF := nF)
        (us := cus) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hkS, ← hsn]; exact hfp
      · rw [getAppFn_mkAppN]
        show Ix.Kernel.Expr.const (c.κ (ixAddr ca)) cus = Ix.Kernel.Expr.const tbl.ctor cus
        rw [hctor, hkC]
      · show ZMod.val fi < tbl.numFields
        rw [hnFt]; exact hltF
      · rw [getAppArgs_mkAppN]
        show ([] ++ Args).length = tbl.numParams + tbl.numFields
        rw [hnPt, hnFt, List.nil_append, hArgsLen]
      · show cus.length = tbl.levelParams.length
        rw [hlpt]; exact hcusLen
      · intro hEq0 φ
        exfalso
        have hz := Ix.Kernel.Level.isEquiv_sound hEq0
        have hne := IxVM.Refinement.KernelLevels.isNeverZero_eval_ne_zero hlnz φ
        rw [Ix.Kernel.Level.eval_subst] at hne
        exact hne ((hz _).trans rfl)
      · show c.env.find? tbl.ctor = _
        rw [hctor, ← hkC]; exact hfindC
      · rw [getAppArgs_mkAppN]
        show Certs c.env d true _ ([] ++ Args)
        rw [List.nil_append]
        refine WhnfAux.certs_never Args _ ?_
        rw [hArgsLen]
        refine WhnfAux.pisNv_of_strip cvC.levelParams cus (nP + nF) cvC.type bsC bodyC hstripC ?_
        intro bm hm
        rw [hbm bm hm, ← Ix.Kernel.Level.zeronessOf_subst,
          ← Ix.Kernel.Level.isNeverZero_eq_isNever, ← hlpS]
        exact hlnz
    have hget : (Specs.Whnf.mkAppN (.const (c.κ (ixAddr ca)) cus) Args).getAppArgs.getD
        ((tbl.entry (ZMod.val fi)).numParams + ZMod.val fi) (.bvar 0) = A := by
      rw [getAppArgs_mkAppN]
      show ([] ++ Args).getD (tbl.numParams + ZMod.val fi) (.bvar 0) = A
      rw [List.nil_append, hnPt]
      simp [List.getD_eq_getElem?_getD, hA']
    rw [hget] at hredp
    exact hredp
  all_goals exact (one_ne_zero
    (WhnfAux.tag_eq (hr.symm.trans ‹r = .tuple [.field 0, _]›)).1).elim

end IxVM.Refinement.Core
