import IxVMRefinement.Iota.Basic

/-! # Step lemmas of `KernelWhnf`: the major premise's preparation, ι with it, quotient dispatch

`whnf_iota_major` head-normalizes a major premise and unfolds theorem heads (`Red.deltaThm`,
whose premises are the environment's `thmTyped`); `try_iota` prepares the major (the `Nat`
offset rewrite, `whnf_iota_major`, the literal-to-constructor step) and fires `red_iota` on it;
`try_quot_iota` dispatches a quotient eliminator to `red_quot` by its role. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)

set_option linter.unusedVariables false

/-! ## Helpers -/

theorem field_two_ne_zero : (2 : F) ≠ 0 := by
  intro h
  have h2 : ZMod.val ((2 : Nat) : F) = 2 := NatAux.val_natCast (by decide)
  rw [Nat.cast_ofNat, h, ZMod.val_zero] at h2
  exact absurd h2 (by decide)

/-- A loaded `Rec` constant's counts and rules, read off its representation. -/
theorem CIRep.recr_fields {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty np ni nm nmi rules k u blk idx : SourceValue F} {cv : Ix.Kernel.ConstantVal .anon}
    {mI rP : Nat} {rls : List (Ix.Kernel.RecRule .anon)}
    (r : CIRep κ h (.construct kciEnum "Rec" [nl, ty, np, ni, nm, nmi, rules, k, u, blk, idx])
      (.recInfo cv mI rP rls)) :
    ∃ p i m mi : F, ValRep κ h nl ty cv ∧ np = .field p ∧ ni = .field i ∧ nm = .field m ∧
      nmi = .field mi ∧ (rP : F) = p + m + mi ∧ (mI : F) = p + m + mi + i ∧ rP ≤ mI ∧
      mI < 288230376151711744 ∧ RulesRep κ h cv.levelParams 0 rules rls := by
  generalize hv : (Value.construct kciEnum "Rec" [nl, ty, np, ni, nm, nmi, rules, k, u, blk, idx] :
    SourceValue F) = v at r
  generalize hc : (Ix.Kernel.ConstantInfo.recInfo cv mI rP rls) = ci at r
  cases r
  case recr hvr hnp hni hnm hnmi hrP hmI hcounts hrules hkey =>
    injection hv with _ _ hl
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hl
    injection hc with h1 h2 h3 h4
    subst h1 h2 h3 h4
    exact ⟨_, _, _, _, hvr, hnp, hni, hnm, hnmi, hrP, hmI, hcounts.1, hcounts.2, hrules⟩
  all_goals (injection hv with _ hc' _; exact absurd hc' (by decide))

theorem RecRedHyps.mono {c : Ctx} {h₁ h₂ : Heap F} {k : KKey} {us : List KLevel}
    {lvls nl rt np ni nm nmi rules kf : SourceValue F} {cv : Ix.Kernel.ConstantVal .anon}
    {mI rP : Nat} {rls : List (Ix.Kernel.RecRule .anon)} (ext : Heap.Extends h₁ h₂)
    (hr : Specs.Whnf.RecRedHyps c h₁ k us lvls nl rt np ni nm nmi rules kf cv mI rP rls) :
    Specs.Whnf.RecRedHyps c h₂ k us lvls nl rt np ni nm nmi rules kf cv mI rP rls := by
  obtain ⟨⟨hf, u, blk, idx, hci⟩, hus⟩ := hr
  exact ⟨⟨hf, u, blk, idx, CIRep.mono ext hci⟩, LvListRep.mono ext hus⟩

/-- The major premise's position, as the field element `np + nm + nmi + ni` IxVM computes. -/
theorem major_idx_field {np nm nmi ni x17 x9 v1 : SourceValue F} {p i m mi : F} {mI : Nat}
    (hnp : np = .field p) (hni : ni = .field i) (hnm : nm = .field m) (hnmi : nmi = .field mi)
    (hmI : (mI : F) = p + m + mi + i)
    (op32 : evalBinOp .add np nm = .ok x17) (op24 : evalBinOp .add x17 nmi = .ok x9)
    (op16 : evalBinOp .add x9 ni = .ok v1) : v1 = .field (mI : F) := by
  subst hnp hni hnm hnmi
  have e1 := NatAux.add_ok op32
  subst e1
  have e2 := NatAux.add_ok op24
  subst e2
  have e3 := NatAux.add_ok op16
  rw [e3, hmI]

/-! ## `whnf_iota_major` -/

/-- `KernelWhnf::whnf_iota_major`: `whnf`, then, at a theorem head, its unfolding
(`Red.deltaThm`, premises from `EnvFacts.thmTyped`) and again. -/
theorem whnf_iota_major_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_iota_major" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_iota_major c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  rcases Obs.«KernelWhnf::whnf_iota_major».obs ev with
    ⟨v1, m2, cs12, m40, cs51, x_h, x_sp, x_addr, x_lvls, m108, cs119, v122, m125, p130, cs136,
      x_body, cs175, v179, m189, cs197, ev14, ev53, ld89, ev138, ld132, ev121, ev199, ev177,
      hc239⟩ |
    ⟨v1, m2, cs12, m40, cs51, x_h, x_sp, x_addr, x_lvls, v107, m108, cs119, v122, m125, p130,
      cs136, ev14, ev53, ld89, ev138, ld132, ev121, he244, he245, hc246⟩ |
    ⟨v1, m2, cs12, m40, cs51, x_h, x_sp, v78, ev14, ev53, ld89, hne247, he252, he253, hc254⟩
  · subst hc239
    obtain ⟨E1, hE1, hr1⟩ := ih.get (.whnf .whnf) (by lt_calls) ev14 rc e types rfl
      (good.sub fun z hz => by simp [hz]) hrc d Γ htypes E hE
    have e0 := ObsFn.heap_extends ev14
    obtain ⟨hd, sp, H, As, he, hH, hAs, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls) ev53
      v1 rfl (good.sub fun z hz => by simp [hz]) d Γ 0 E1 hE1
    obtain ⟨rfl, rfl⟩ := tuple2_inj he
    obtain ⟨a, us, rfl, ha, hus⟩ := hH.const_of_load ld89
    have e1 := ObsFn.heap_extends ev53
    obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev138 x_addr a rfl
      (good.sub fun z hz => by simp [hz]) ha
    rw [ld132] at hld
    injection hld with hv
    subst hv
    have e2 := ObsFn.heap_extends ev138
    have hu := ih.get (.whnf .red_unfold) (by lt_calls) ev121 _ x_lvls rfl
      (good.sub fun z hz => by simp [hz]) ci us hci (LvListRep.mono e2 hus) 2 x_body rfl
      field_two_ne_zero
    rcases hu with ⟨h21, -⟩ | ⟨-, cv, V, rfl, hlen, hbody⟩
    · exact absurd h21.symm field_one_ne_two
    · have e3 := ObsFn.heap_extends ev121
      have ext := e0.trans (e1.trans (e2.trans e3))
      obtain ⟨E2, hE2, hr2⟩ := ih.get (.whnf .whnf_with_spine) (by lt_calls) ev199 rc x_body x_sp
        types rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono ext hrc) d Γ
        (types_mono ext htypes) _ As (hbody d Γ) (tml_mono (e2.trans e3) hAs)
      have e4 := ObsFn.heap_extends ev199
      obtain ⟨E3, hE3, hr3⟩ := ih.get (.whnf .whnf_iota_major) (by lt_calls) ev177 rc v179 types
        rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono (ext.trans e4) hrc) d Γ
        (types_mono (ext.trans e4) htypes) E2 hE2
      obtain ⟨hnf, hlb, vt, s, u, h1, h2, h3, h4, h5⟩ := hc.env.thmTyped _ cv V hfind
      exact ⟨E3, hE3, .trans hr1 (.trans (red_mkAppN As (.deltaThm hfind hlen hnf hlb h1 h2 h3 h4 h5))
        (.trans hr2 hr3))⟩
  · subst he244 he245 hc246
    obtain ⟨E1, hE1, hr1⟩ := ih.get (.whnf .whnf) (by lt_calls) ev14 rc e types rfl
      (good.sub fun z hz => by simp [hz]) hrc d Γ htypes E hE
    have ext := (ObsFn.heap_extends ev53).trans
      ((ObsFn.heap_extends ev138).trans (ObsFn.heap_extends ev121))
    exact ⟨E1, Tm.mono ext hE1, hr1⟩
  · subst he252 he253 hc254
    obtain ⟨E1, hE1, hr1⟩ := ih.get (.whnf .whnf) (by lt_calls) ev14 rc e types rfl
      (good.sub fun z hz => by simp [hz]) hrc d Γ htypes E hE
    exact ⟨E1, Tm.mono (ObsFn.heap_extends ev53) hE1, hr1⟩

/-! ## `try_quot_iota` -/

/-- `KernelWhnf::try_quot_iota`: `red_quot` at the eliminator the table binds the head to
(`role_is`, whose answer `1` gives the binding and the role in force). -/
theorem try_quot_iota_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::try_quot_iota" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.try_quot_iota c args h r h' calls := by
  intro rc addr lvls sp types hargs good hrc d Γ htypes a us As ha hus hAs x hr
  subst hargs
  rcases Obs.«KernelWhnf::try_quot_iota».obs ev with
    ⟨m2, cs13, v18, m34, cs42, cs52, ev44, ev15, ev54, hc102⟩ |
    ⟨v1, m2, cs13, v18, m34, cs42, m108, cs119, v124, m140, cs148, cs158, ev44, ev15, hne103,
      ev150, ev121, ev160, hc208⟩ |
    ⟨v1, m2, cs13, v18, m34, cs42, v107, m108, cs119, v124, m140, cs148, m225, ev44, ev15,
      hne103, ev150, ev121, hne209, he217, hm233, he244, hc245⟩
  · subst hc102
    obtain ⟨rfl, rfl⟩ := ih.get (.roles .role_quot_lift) (by lt_calls) ev44 rfl
    obtain ⟨haddr, hin⟩ := ih.get (.roles .role_is) (by lt_calls) ev15 rc addr a .quotLift rfl
      (good.sub fun z hz => by simp [hz]) hrc ha NatAux.field_one_ne_zero
    have ext := ObsFn.heap_extends ev15
    exact ih.get (.whnf .red_quot) (by lt_calls) ev54 rc _ addr lvls sp types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) a us As
      (.inl ⟨rfl, haddr, hin⟩) (Bytes.repAddressRef_heapMono₂ addrTy ext ha)
      (LvListRep.mono ext hus) (tml_mono ext hAs) x hr
  · subst hc208
    obtain ⟨rfl, rfl⟩ := ih.get (.roles .role_quot_lift) (by lt_calls) ev44 rfl
    have e1 := ObsFn.heap_extends ev15
    obtain ⟨rfl, rfl⟩ := ih.get (.roles .role_quot_ind) (by lt_calls) ev150 rfl
    obtain ⟨haddr, hin⟩ := ih.get (.roles .role_is) (by lt_calls) ev121 rc addr a .quotInd rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono e1 hrc)
      (Bytes.repAddressRef_heapMono₂ addrTy e1 ha) NatAux.field_one_ne_zero
    have ext := e1.trans (ObsFn.heap_extends ev121)
    exact ih.get (.whnf .red_quot) (by lt_calls) ev160 rc _ addr lvls sp types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) a us As
      (.inr ⟨rfl, haddr, hin⟩) (Bytes.repAddressRef_heapMono₂ addrTy ext ha)
      (LvListRep.mono ext hus) (tml_mono ext hAs) x hr
  · exact (tag_zero_ne_one (he217.symm.trans hr)).elim

/-! ## `try_iota` -/

/-- `KernelWhnf::try_iota`: at a spine long enough for the major premise, the major is prepared
(a chain of `Red` steps: the offset rewrite, `whnf_iota_major`, the offset rewrite again, the
literal-to-constructor step) and `red_iota` fires on it; the modeled route's comparands gate
(`fire_ok`) answers whether the reduct is taken. Tag `2` is the application itself. -/
theorem try_iota_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::try_iota" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.try_iota c args h r h' calls := by
  intro rc rt lvls sp np nm nmi ni rules types hd rp hargs good hrc d Γ htypes k us nl kf cv mI
    rP rls p As hrr hlen hp hmh hH hAs t x hr ht
  subst hargs
  rcases Obs.«KernelWhnf::try_iota».obs ev with
    ⟨v1, x9, x17, v37, m38, cs48, m60, cs71, m106, op32, op24, op16, ev50, ev73, he98, hm114,
      he125, hc0⟩ |
    ⟨v1, x9, x17, v37, m38, cs48, v59, m60, cs71, v131, m132, cs142, v161, m162, cs172, v191,
      m192, cs202, v229, m230, cs240, v259, m260, cs270, m290, cs301, x_r3, m419, cs430, v496,
      m505, cs513, op32, op24, op16, ev50, ev73, hne127, ev144, ev174, ev204, ev242, ev272, ev303,
      ev432, he497, ev515, he532, hc1⟩ |
    ⟨v1, x9, x17, v37, m38, cs48, v59, m60, cs71, v131, m132, cs142, v161, m162, cs172, v191,
      m192, cs202, v229, m230, cs240, v259, m260, cs270, m290, cs301, x_r3, v418, m419, cs430,
      op32, op24, op16, ev50, ev73, hne127, ev144, ev174, ev204, ev242, ev272, ev303, ev432,
      hne534, he542, he556, hc2⟩ |
    ⟨v1, x9, x17, v37, m38, cs48, v59, m60, cs71, v131, m132, cs142, v161, m162, cs172, v191,
      m192, cs202, v229, m230, cs240, v259, m260, cs270, v289, m290, cs301, v564, m573, cs581,
      op32, op24, op16, ev50, ev73, hne127, ev144, ev174, ev204, ev242, ev272, ev303, he565,
      ev583, he600, hc3⟩
  · -- the spine is too short: tag `0`
    obtain ⟨ht0, -⟩ := tuple2_inj (hr.symm.trans he98)
    injection ht0 with ht0
    subst ht0
    rcases ht with h1 | h2
    · exact zero_ne_one h1
    · exact field_two_ne_zero h2.symm
  · -- fired, but the modeled gate refused: the application itself
    obtain ⟨-, rfl⟩ := tuple2_inj (hr.symm.trans he497)
    subst he532 hc1
    have ext := (ObsFn.heap_extends ev50).trans ((ObsFn.heap_extends ev73).trans
      ((ObsFn.heap_extends ev144).trans ((ObsFn.heap_extends ev174).trans
      ((ObsFn.heap_extends ev204).trans ((ObsFn.heap_extends ev242).trans
      ((ObsFn.heap_extends ev272).trans ((ObsFn.heap_extends ev303).trans
      (ObsFn.heap_extends ev432))))))))
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev515 hd sp rfl
      (good.sub fun z hz => by simp [hz]) d Γ 0 _ As (Tm.mono ext hH) (tml_mono ext hAs), .refl⟩
  · -- fired: `red_iota`'s reduct
    obtain ⟨-, rfl⟩ := tuple2_inj (hr.symm.trans he542)
    subst he556 hc2
    obtain ⟨⟨hfind, u, blk, idx, hci⟩, hus⟩ := hrr
    obtain ⟨p', i', m', mi', -, hnp, hni, hnm, hnmi, -, hmI, -, hmIb, -⟩ := CIRep.recr_fields hci
    have hv1 := major_idx_field hnp hni hnm hnmi hmI op32 op24 op16
    subst hv1
    have e0 := (ObsFn.heap_extends ev50).trans (ObsFn.heap_extends ev73)
    obtain ⟨⟨A, hA, hAt⟩, rfl⟩ := Lib.Lists.lookup_spec
      (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := TmE c.κ d Γ)
      (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol]; exact ev144)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact tml_mono e0 hAs)
    rw [NatAux.val_natCast (by omega)] at hA
    obtain ⟨A1, hA1, hr1⟩ := ih.get (.nat .cleanup_nat_offset_major) (by lt_calls) ev174 rc v131
      rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono e0 hrc) d Γ A hAt
    have e1 := ObsFn.heap_extends ev174
    obtain ⟨A2, hA2, hr2⟩ := ih.get (.whnf .whnf_iota_major) (by lt_calls) ev204 rc v161 types
      rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono (e0.trans e1) hrc) d Γ
      (types_mono (e0.trans e1) htypes) A1 hA1
    have e2 := ObsFn.heap_extends ev204
    obtain ⟨A3, hA3, hr3⟩ := ih.get (.nat .cleanup_nat_offset_major) (by lt_calls) ev242 rc v191
      rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono (e0.trans (e1.trans e2)) hrc) d Γ A2 hA2
    have e3 := ObsFn.heap_extends ev242
    obtain ⟨M, hM, hr4⟩ := ih.get (.whnf .nat_lit_to_ctor_or_self) (by lt_calls) ev272 rc v229
      rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono (e0.trans (e1.trans (e2.trans e3))) hrc)
      d Γ A3 hA3
    have e4 := ObsFn.heap_extends ev272
    have ext := e0.trans (e1.trans (e2.trans (e3.trans e4)))
    have hget : As.getD mI (.bvar 0) = A := by simp [List.getD_eq_getElem?_getD, hA]
    obtain ⟨E, hE, hred⟩ := ih.get (.whnf .red_iota) (by lt_calls) ev303 rc rt lvls sp np nm nmi
      ni rules rp v259 types rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono ext hrc) d Γ
      (types_mono ext htypes) k us nl kf cv mI rP rls p As M
      (RecRedHyps.mono ext ⟨⟨hfind, u, blk, idx, hci⟩, hus⟩) hlen
      (Bytes.repAddressRef_heapMono₂ addrTy ext hp) hmh (tml_mono ext hAs) hM
      (by rw [hget]; exact .trans hr1 (.trans hr2 (.trans hr3 hr4))) x_r3 rfl
    exact ⟨E, Tm.mono (ObsFn.heap_extends ev432) hE, hred⟩
  · -- no rule fired: the application itself
    obtain ⟨-, rfl⟩ := tuple2_inj (hr.symm.trans he565)
    subst he600 hc3
    have ext := (ObsFn.heap_extends ev50).trans ((ObsFn.heap_extends ev73).trans
      ((ObsFn.heap_extends ev144).trans ((ObsFn.heap_extends ev174).trans
      ((ObsFn.heap_extends ev204).trans ((ObsFn.heap_extends ev242).trans
      ((ObsFn.heap_extends ev272).trans (ObsFn.heap_extends ev303)))))))
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev583 hd sp rfl
      (good.sub fun z hz => by simp [hz]) d Γ 0 _ As (Tm.mono ext hH) (tml_mono ext hAs), .refl⟩

end IxVM.Refinement.Core
