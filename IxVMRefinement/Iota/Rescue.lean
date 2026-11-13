import IxVMRefinement.Iota.RedIota
import IxVMRefinement.Iota.Leaves

/-! # The K rescue: `k_synth_fab` and `try_k_synth_iota`

At a recursor whose record sets the K flag (one rule, with the K bit: `CIRep.recr`'s `hk`), IxVM
fabricates the rule's constructor applied to the major's type's parameters and fires ι on it.
The fabrication is `Red.rescueK`: the constructor is the rule's (by the store's rule key for the
major inductive's projection record, which the loaded inductive comes from), its head is the
major's inductive (`EnvFacts.ruleCtorHead`, `StoreInv.recK`), the fabrication's inference gives
the constructor's levels and the unlicensed certificates of its parameters (`infer_spine`), its
leaves are the major's (`infer_leaves`, `red_leaves`), and proof irrelevance equates it with the
major (`is_prop_type` on both types).

IxVM takes the parameters by the recursor's parameter count, `Red.rescueK` by the constructor's
(`KParams` states that the two agree at a K recursor). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq Infer Certs)

set_option linter.unusedVariables false

/-! ## Inferring a constant applied to a spine -/

theorem piResidual_snoc (a : KExpr) : ∀ (As : List KExpr) (T : KExpr),
    Ix.Kernel.piResidual T (As ++ [a]) =
      (Ix.Kernel.piResidual T As).bind (fun R => Ix.Kernel.piResidual R [a])
  | [], T => by simp [Ix.Kernel.piResidual]
  | b :: As, T => by
    cases T with
    | forallE ty body m =>
      simp only [List.cons_append, Ix.Kernel.piResidual]
      exact piResidual_snoc a As _
    | _ => simp [Ix.Kernel.piResidual]

/-- A residual short of a telescope's binders is a `∀`. -/
theorem piResidual_forall : ∀ (As : List KExpr) (T R : KExpr) (k : Nat),
    (T.stripPis (As.length + k + 1)).isSome = true → Ix.Kernel.piResidual T As = some R →
      ∃ ty body m, R = .forallE ty body m
  | [], T, R, k, hs, hr => by
    simp only [Ix.Kernel.piResidual, Option.some.injEq] at hr
    subst hr
    cases T with
    | forallE ty body m => exact ⟨ty, body, m, rfl⟩
    | _ => simp [Ix.Kernel.Expr.stripPis] at hs
  | a :: As, T, R, k, hs, hr => by
    cases T with
    | forallE ty body m =>
      simp only [Ix.Kernel.piResidual] at hr
      have e : (a :: As).length + k + 1 = (As.length + k + 1) + 1 := by simp; omega
      rw [e] at hs
      simp only [Ix.Kernel.Expr.stripPis, Option.isSome_map] at hs
      exact piResidual_forall As _ R k
        (Specs.Whnf.stripPis_isSome_instantiate1 a _ body 0 hs) hr
    | _ => simp [Ix.Kernel.piResidual] at hr

theorem certs_snoc {env : Ix.Kernel.Env .anon} {d : Nat} {lic : Bool} {a ta : KExpr} :
    ∀ (As : List KExpr) (T : KExpr) {ty body : KExpr} {m : Ix.Kernel.BinderMeta},
      Certs env d lic T As → Ix.Kernel.piResidual T As = some (.forallE ty body m) →
      Infer env .io d a ta → DefEq env d ta ty → Certs env d lic T (As ++ [a])
  | [], T, ty, body, m, hc, hr, hi, hd => by
    simp only [Ix.Kernel.piResidual, Option.some.injEq] at hr
    subst hr
    exact .cert hi hd .nil
  | arg :: rest, T, ty, body, m, hc, hr, hi, hd => by
    cases hc with
    | skip hl hn hrest =>
      simp only [Ix.Kernel.piResidual] at hr
      exact .skip hl hn (certs_snoc rest _ hrest hr hi hd)
    | cert hi' hd' hrest =>
      simp only [Ix.Kernel.piResidual] at hr
      exact .cert hi' hd' (certs_snoc rest _ hrest hr hi hd)

/-- **A constant applied to a spine, inferred at the full grade**: the levels fit, the type is
the residual of the constant's telescope, and the arguments certify against it. -/
theorem infer_spine {env : Ix.Kernel.Env .anon} {d : Nat} {n : KKey} {us : List KLevel}
    {ci : Ix.Kernel.ConstantInfo .anon} (hf : env.find? n = some ci) :
    ∀ (As : List KExpr) (t : KExpr),
      ((ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us).stripPis
        As.length).isSome = true →
      Infer env .full d (Ix.Kernel.Expr.mkAppN (.const n us) As) t →
      us.length = ci.toConstantVal.levelParams.length ∧
        Ix.Kernel.piResidual
          (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) As =
          some t ∧
        Certs env d false
          (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) As := by
  intro As
  induction As using List.reverseRecOn with
  | nil =>
    intro t _ hi
    obtain ⟨ci', hf', -, hus, rfl⟩ := Ix.Kernel.Rules.Infer.const_inv hi
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    exact ⟨hus, by simp [Ix.Kernel.piResidual], .nil⟩
  | append_singleton As a ih =>
    intro t hs hi
    rw [← mkAppN_mkAppN] at hi
    have hi' : Infer env .full d (.app (Ix.Kernel.Expr.mkAppN (.const n us) As) a) t := hi
    obtain ⟨tf, ty, body, mt, ta, htf, hw, hta, hde, rfl⟩ := Ix.Kernel.Rules.Infer.app_inv hi'
    have hs' : ((ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams
        us).stripPis As.length).isSome = true :=
      Specs.Whnf.stripPis_isSome_of_le (by simp) hs
    obtain ⟨hus, hres, hcert⟩ := ih tf hs' htf
    obtain ⟨ty', body', m', rfl⟩ := piResidual_forall As _ tf 0 (by simpa using hs) hres
    have e := Ix.Kernel.Rules.Red.rigid hw rfl
    injection e with e1 e2 e3
    subst e1 e2 e3
    refine ⟨hus, ?_, certs_snoc As _ hcert hres (infer_toIo hta) hde⟩
    rw [piResidual_snoc, hres]
    simp [Ix.Kernel.piResidual]

/-! ## The K rescue's fabrication -/

/-- **A K recursor's rule has the loaded recursor's parameter count**: IxVM takes the
fabrication's parameters by the recursor record's count, the model's rescue by the rule's
constructor's. -/
def KParams (c : Ctx) : Prop :=
  ∀ (h : Heap F) (nl ty np ni nm nmi rules u blk idx : SourceValue F)
    (cv : Ix.Kernel.ConstantVal .anon) (mI rP : Nat) (rl : Ix.Kernel.RecRule .anon) (p : F),
    c.ci h (.construct kciEnum "Rec" [nl, ty, np, ni, nm, nmi, rules, .field 1, u, blk, idx])
      (.recInfo cv mI rP [rl]) → np = .field p → rl.ctorParams = ZMod.val p

theorem CIRep.recr_k {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty np ni nm nmi rules k u blk idx : SourceValue F} {cv : Ix.Kernel.ConstantVal .anon}
    {mI rP : Nat} {rls : List (Ix.Kernel.RecRule .anon)}
    (r : CIRep κ h (.construct kciEnum "Rec" [nl, ty, np, ni, nm, nmi, rules, k, u, blk, idx])
      (.recInfo cv mI rP rls)) :
    k = .field 1 → ∃ rl, rls = [rl] ∧ rl.k = true := by
  generalize hv : (Value.construct kciEnum "Rec" [nl, ty, np, ni, nm, nmi, rules, k, u, blk, idx] :
    SourceValue F) = v at r
  generalize hc : (Ix.Kernel.ConstantInfo.recInfo cv mI rP rls) = ci at r
  cases r
  case recr hvr hnp hni hnm hnmi hrP hmI hcounts hrules hk hkey =>
    injection hv with _ _ hl
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hl
    injection hc with h1 h2 h3 h4
    subst h1 h2 h3 h4
    exact hk
  all_goals (injection hv with _ hc' _; exact absurd hc' (by decide))

/-- **`KernelWhnf::k_synth_fab`**, given `KParams`: the major's io type head-normalizes to its
inductive (the major premise's head), the rule's constructor applied to the type's parameters is
fabricated, and its type and the major's are propositions definitionally equal to each other:
`Red.rescueK`. -/
theorem k_synth_fab_of (c : Ctx) (hc : CoreFacts c) (hkp : KParams c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::k_synth_fab" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.k_synth_fab c args h r h' calls := by
  intro rc maj cidx np rp types hargs good hrc d Γ htypes k nl rt ni nm nmi rules cv mI rP rl p M
    hrec hrlk hcidx hp hmh hM x hr
  subst hargs hcidx
  rcases Obs.«KernelWhnf::k_synth_fab».obs ev with
    ⟨v1, m2, cs12, v39, m40, cs50, m78, cs89, x_ty_head, x_ty_args, x_ind_addr, x_ctor_us, m146, cs157, m181, p189, cs195, w212, w213, w214, w215, w216, w217, x_ind_block, x_ind_idx, v258, m259, cs269, v296, m297, cs307, v311, m313, m342, cs350, v369, m370, cs380, m408, cs419, m459, cs470, v503, m507, cs515, ev14, ev52, ev91, ld127, ev159, ev197, ld191, ev271, hm321, ev352, ev309, ev382, ev421, ev472, he505, ev517, he549, hc550⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he0, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he0, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he0, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he0, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he0, _, _⟩
  · subst he549 hc550
    obtain ⟨hv503, rfl⟩ := tuple2_inj (hr.symm.trans he505)
    obtain ⟨hfind, u0, blk0, idx0, hci⟩ := hrec
    obtain ⟨p', i', m', mi', -, hnp, -, -, -, -, -, -, -, -⟩ := CIRep.recr_fields hci
    have hnP := hkp h nl rt np ni nm nmi rules u0 blk0 idx0 cv mI rP rl p' hci hnp
    subst hnp
    have hrl : rl ∈ [rl] := List.mem_singleton_self rl
    have e14 := ObsFn.heap_extends ev14
    have e52 := ObsFn.heap_extends ev52
    have e91 := ObsFn.heap_extends ev91
    have e159 := ObsFn.heap_extends ev159
    have e197 := ObsFn.heap_extends ev197
    have e271 := ObsFn.heap_extends ev271
    have e352 := ObsFn.heap_extends ev352
    have e309 := ObsFn.heap_extends ev309
    have e382 := ObsFn.heap_extends ev382
    have e421 := ObsFn.heap_extends ev421
    have e472 := ObsFn.heap_extends ev472
    have e517 := ObsFn.heap_extends ev517
    have X78 := e14.trans (e52.trans e91)
    have e313 : Heap.Extends m259 m313 := by rw [hm321]; exact Heap.Extends.snoc _ _
    have Y313 := e159.trans (e197.trans (e271.trans e313))
    have X313 := X78.trans Y313
    have X297 := X313.trans (e352.trans e309)
    -- the major's type, head-normalized
    obtain ⟨TM, hTM, hinfM⟩ := ih.get (.infer .k_infer) (by lt_calls) ev14 rc maj types rfl
      (good.sub fun z hz => by simp [hz]) hrc d Γ htypes M hM
    obtain ⟨TW, hTW, hredT⟩ := ih.get (.whnf .whnf) (by lt_calls) ev52 rc v1 types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono e14 hrc) d Γ (types_mono e14 htypes) TM hTM
    obtain ⟨hd0, sp0, HT, TA, he1, hHT, hTA, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls)
      ev91 v39 rfl (good.sub fun z hz => by simp [hz]) d Γ 0 TW hTW
    obtain ⟨rfl, rfl⟩ := tuple2_inj he1
    obtain ⟨ia, ust, rfl, hia, hust⟩ := hHT.const_of_load ld127
    obtain ⟨hae, -⟩ := Lib.address_eq_spec ev159 hia (Bytes.repAddressRef_heapMono₂ addrTy X78 hp)
    have hiap : ia = p := by
      by_contra hne
      rw [ite_eq_right hne] at hae
      exact NatAux.field_one_ne_zero hae
    subst hiap
    -- the inductive's record, and the rule's constructor
    obtain ⟨cm, b, i, hcm, hb, hidx, hinfo⟩ := hc.loads.inductRecord x_ind_addr p189 m146 m181 cs195
      ia _ _ _ _ _ _ x_ind_block x_ind_idx ev197 (good.sub fun z hz => by simp [hz])
      (Bytes.repAddressRef_heapMono₂ addrTy e159 hia) ld191
    subst hidx
    obtain ⟨us0, hmh0⟩ := hmh
    obtain ⟨hnd, hfire, hkeys⟩ := hc.env.recRules k cv mI rP [rl] hfind
    have hctor := hkeys (ixAddr ia) cm _ us0 hmh0 hcm hinfo 0 rl rfl
    simp only [val_toUInt64_toNat] at hctor
    obtain ⟨cpa, hcpa, hcpaa⟩ := ih.get (.callees .projection_addr_ctor) (by lt_calls) ev271 i 0
      x_ind_block b rfl (good.sub fun z hz => by simp [hz]) hb
    have hκ : rl.ctor = c.κ (ixAddr cpa) := by rw [hctor, hcpaa, ZMod.val_zero]
    obtain ⟨-, cvj, nF, hcj⟩ := hfire rl hrl
    obtain ⟨-, -, harity⟩ := hc.env.ruleCtorArity k cv mI rP [rl] hfind rl hrl cvj _ _ hcj
    obtain ⟨cvj', cnP', T', us', cvT, caps, hcj', hres', hT', -⟩ :=
      hc.env.store.recK hfind hrl hrlk
    rw [hcj] at hcj'
    obtain ⟨rfl, rfl, rfl⟩ := Ix.Kernel.ConstantInfo.ctorInfo.inj (Option.some.inj hcj')
    obtain ⟨tus, htus⟩ := hc.env.ruleCtorHead k cv mI rP [rl] rl cvj _ _ _ us0 hfind hrl hcj hmh0
    rw [htus] at hres'
    injection hres' with hTT _
    subst hTT
    -- the fabrication
    have hhead : c.tmk d Γ 0 m313 (.const rl.ctor ust) (.ptr (.enum kexprEnum) m259.length) := by
      obtain ⟨ls, hls, hlseq⟩ := LvListRep.mono Y313 hust
      rw [hκ]
      exact .const (by rw [hm321]; simp) (Bytes.repAddressRef_heapMono₂ addrTy e313 hcpa) hls
        hlseq
    obtain ⟨hnple, hpar⟩ := Lib.Lists.take_spec (t := kexprTy) (R := TmE c.κ d Γ) tmE_heapMono₂
      (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev352)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact tml_mono Y313 hTA)
    rw [← hnP, Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hpar
    rw [← hnP] at hnple
    have hFAB := ih.get (.whnf .apply_spine) (by lt_calls) ev309 _ v311 rfl
      (good.sub fun z hz => by simp [hz]) d Γ 0 _ _ (Tm.mono e352 hhead) hpar
    obtain ⟨TF, hTF, hinfF⟩ := ih.get (.infer .k_infer) (by lt_calls) ev382 rc x types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono X297 hrc) d Γ (types_mono X297 htypes) _ hFAB
    have hdef := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev421 rc v39 v369 types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono (X297.trans e382) hrc) d Γ
      (types_mono (X297.trans e382) htypes) _ _
      (Tm.mono (e91.trans (Y313.trans (e352.trans (e309.trans e382)))) hTW) hTF
      NatAux.field_one_ne_zero
    obtain ⟨S, u, hS, hSu, hu0⟩ := ih.get (.defEq .is_prop_type) (by lt_calls) ev472 rc v1 types
      rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono (X297.trans (e382.trans e421)) hrc) d Γ
      (types_mono (X297.trans (e382.trans e421)) htypes) _
      (Tm.mono (e52.trans (e91.trans (Y313.trans (e352.trans (e309.trans (e382.trans e421))))))
        hTM) NatAux.field_one_ne_zero
    obtain ⟨S', v, hS', hS'v, hv0⟩ := ih.get (.defEq .is_prop_type) (by lt_calls) ev517 rc v369
      types rfl (good.sub fun z hz => by simp [hz])
      (RCRep.mono (X297.trans (e382.trans (e421.trans e472))) hrc) d Γ
      (types_mono (X297.trans (e382.trans (e421.trans e472))) htypes) _
      (Tm.mono (e421.trans e472) hTF) (by rw [← hv503]; exact NatAux.field_one_ne_zero)
    -- the spine of the fabrication against the constructor's telescope
    have hargsTW : (Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr ia)) ust) TA).getAppArgs = TA := by
      rw [getAppArgs_mkAppN]; rfl
    have hlenP : (TA.take rl.ctorParams).length = rl.ctorParams := by simp; omega
    obtain ⟨hustl, -, hcerts⟩ := infer_spine (us := ust) hcj (TA.take rl.ctorParams) TF
      (Specs.Whnf.stripPis_isSome_instantiateLevelParams _ _ _ _
        (Specs.Whnf.stripPis_isSome_of_le (by rw [hlenP]; omega) harity)) hinfF
    have hlb := Tm.looseBVarsBounded hFAB
    have hws := Tm.wscopedB htypes.2 hFAB
    refine ⟨_, Tm.mono (e382.trans (e421.trans (e472.trans e517))) hFAB, ?_⟩
    refine Ix.Kernel.Rules.Red.rescueK (recName := k) (cv := cv) (mI := mI) (rP := rP) (rl := rl)
      (cvj := cvj) (cnP := rl.ctorParams) (T := c.κ (ixAddr ia)) (tus := tus) (ust := ust)
      (cvT := cvT) (caps := caps) (tm := TM) (tf := TF)
      (tmaj := Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr ia)) ust) TA)
      hfind hrlk hcj htus hT' (infer_toIo hinfM) hredT (by rw [getAppFn_mkAppN]; rfl)
      hustl.symm (by rw [hargsTW]; exact hnple) (by rw [hargsTW]) hws hlb ?_
      (by rw [hargsTW]; exact hcerts) (infer_toIo hinfF) hdef
      (.proofIrrel (infer_toIo hinfF) hS' hS'v hv0 (infer_toIo hinfM) hS hSu hu0)
    refine List.all_eq_true.mpr fun l hl => List.contains_iff_mem.mpr ?_
    rcases Ix.Kernel.fvarLeaves_mkAppN hl with h1 | ⟨y, hy, h2⟩
    · simp [Ix.Kernel.Expr.fvarLeaves] at h1
    · have h3 := Ix.Kernel.fvarLeaves_getAppArgs (e := Ix.Kernel.Expr.mkAppN
        (.const (c.κ (ixAddr ia)) ust) TA) (by rw [hargsTW]; exact List.mem_of_mem_take hy) l h2
      exact infer_leaves hc.env.storeClosed hinfM l (red_leaves hc.env.storeClosed hredT l h3)
  all_goals exact (tag_zero_ne_one (he0.symm.trans hr)).elim

/-! ## K-like ι -/

/-- **`KernelWhnf::try_k_synth_iota`**: at the one rule of a K recursor (index `0`), the K
fabrication (`k_synth_fab`), then ι on it (`red_iota`). -/
theorem try_k_synth_iota_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::try_k_synth_iota" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.try_k_synth_iota c args h r h' calls := by
  intro rc rt lvls sp np nm nmi ni rules rp types hargs good hrc d Γ htypes k us nl cv mI rP rls
    p As hrr hlen hp hmh hAs x hr
  subst hargs
  rcases Obs.«KernelWhnf::try_k_synth_iota».obs ev with
    ⟨w20, x_cidx, x__rfields, x__rrhs, v62, x70, x78, m99, cs110, v114, m123, cs131, m158, ld12,
      op93, op85, op77, ev133, ev112, he150, hm166, he177, hc178⟩ |
    ⟨w20, x_cidx, x__rfields, x__rrhs, v62, x70, x78, v98, m99, cs110, v114, m123, cs131, v183,
      m184, cs194, m214, cs225, x_fab, cs297, ld12, op93, op85, op77, ev133, ev112, hne179, ev196,
      ev227, ev299, hc396⟩ |
    ⟨w20, x_cidx, x__rfields, x__rrhs, v62, x70, x78, v98, m99, cs110, v114, m123, cs131, v183,
      m184, cs194, v213, m214, cs225, m412, ld12, op93, op85, op77, ev133, ev112, hne179, ev196,
      ev227, he404, hm420, he431, hc432⟩ |
    ⟨v1, m450, ld12, hne434, he442, hm458, he469, hc470⟩
  · exact (tag_zero_ne_one (he150.symm.trans hr)).elim
  · subst hc396
    obtain ⟨⟨hfind, u0, blk0, idx0, hci⟩, hus⟩ := hrr
    obtain ⟨rl, rfl, hrlk⟩ := CIRep.recr_k hci rfl
    obtain ⟨p', i', m', mi', -, hnp, hni, hnm, hnmi, -, hmI, -, hmIb, hrules⟩ :=
      CIRep.recr_fields hci
    obtain ⟨rl', rls', hrl', ⟨rhs', hv, -, -⟩, -⟩ := RulesRep.cons_of_load hrules ld12
    injection hrl' with hrl1 hrl2
    subst hrl1
    injection hv with _ _ hl
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨hcidx, -, -⟩ := hl
    have hv62 := major_idx_field hnp hni hnm hnmi hmI op93 op85 op77
    subst hv62
    have e0 := (ObsFn.heap_extends ev133).trans (ObsFn.heap_extends ev112)
    obtain ⟨⟨A, hA, hAt⟩, rfl⟩ := Lib.Lists.lookup_spec
      (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := TmE c.κ d Γ)
      (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol]; exact ev196)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact tml_mono e0 hAs)
    rw [NatAux.val_natCast (n := mI) (by omega)] at hA
    obtain ⟨FAB, hFAB, hredF⟩ := ih.get (.whnf .k_synth_fab) (by lt_calls) ev227 rc v183 x_cidx np
      rp types rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono e0 hrc) d Γ
      (types_mono e0 htypes) k nl rt ni nm nmi rules cv mI rP rl p A
      ⟨hfind, u0, blk0, idx0, CIRep.mono e0 hci⟩ hrlk (by simpa using hcidx)
      (Bytes.repAddressRef_heapMono₂ addrTy e0 hp) hmh hAt x_fab rfl
    have e1 := e0.trans (ObsFn.heap_extends ev227)
    have hget : As.getD mI (.bvar 0) = A := by rw [List.getD_eq_getElem?_getD, hA]; rfl
    exact ih.get (.whnf .red_iota) (by lt_calls) ev299 rc rt lvls sp np nm nmi ni rules rp x_fab
      types rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono e1 hrc) d Γ
      (types_mono e1 htypes) k us nl (.field 1) cv mI rP [rl] p As FAB
      (RecRedHyps.mono e1 ⟨⟨hfind, u0, blk0, idx0, hci⟩, hus⟩) hlen
      (Bytes.repAddressRef_heapMono₂ addrTy e1 hp) hmh (tml_mono e1 hAs) hFAB
      (by rw [hget]; exact hredF) x hr
  · exact (tag_zero_ne_one (he404.symm.trans hr)).elim
  · exact (tag_zero_ne_one (he442.symm.trans hr)).elim

end IxVM.Refinement.Core
