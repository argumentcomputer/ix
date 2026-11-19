import IxVMRefinement.FamilyGraph.ProducersRefs
import IxVMRefinement.FamilyGraph.ProducersStoredFam
import IxVMRefinement.Claim.TopProj
import IxVMRefinement.Binding.ClauseInvariant
import Ix.IxVM.Consistency.ReadsKeys

/-! # Route dispatch, recursor arms, freshness, and complete `BatchGives` assembly

Discharges the remaining five fields of `BatchGives` (`routed`, `listedNotScope`, `recUsesBlock`,
`recArm`, and `fresh`) and assembles `FamRunCtx.batchGives_of_run : BatchGives K`:

* `FamCallsModeled`: every `KernelModeled::check_family` call in a run's call trace is backed by
  an observed non-zero `KernelModeled::block_is_modeled` call on the same block address
  (`FamCallsModeled.of_verifyClaim` via `obsFn_check_family_modeled`);
* `modeledRouteAt_of_obs`: a single observed non-zero `KernelModeled::block_is_modeled` call on
  `B` in a step store yields `ModeledRouteAt K.calls B` via `Route.block_is_modeled_agrees`;
* `FamRunCtx.routed_of`, `FamRunCtx.listedNotScope_of`: discharge `BatchGives.routed` and
  `BatchGives.listedNotScope`;
* `FamRunCtx.recUsesBlock_of`, `FamRunCtx.recArm_of`: discharge `BatchGives.recUsesBlock` and
  `BatchGives.recArm` via `FamCheckCarriers.noTypeRole` (`KernelModeled::assert_no_type_role`)
  and `rprj_check_const_rec_other`;
* `familyKey_of_motiveCarrierAt`, `FamRunCtx.fresh_of`: discharge `BatchGives.fresh` via
  `TableShape.reading.provenance`, `motiveCarrierAt → familyKey → motiveKeys` across `Annotates`,
  `Ix.Kernel.EnvWF`, and `BoundaryFacts.whole`;
* `FamRunCtx.batchGives_of_run`: complete `BatchGives K`. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

universe u

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core hiding keyOf
open IxVM.Refinement.Obs
open IxVM.Consistency
open IxVM.Refinement.Binding
open IxVM (F)
open FamilyAlias (FamilyCallAtLim)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## Modeled-route propagation from observed `block_is_modeled` calls -/

/-- Build canonical hash coverage for a step store `E` from `TopWalkCore.hashedStored`. -/
private theorem canonicalHashCoverage_of_step {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat} {R E : Ixon.Env}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hctx : StepCtx.{u} K.calls K.t R K.envT K.E₀ E) :
    L1.CanonicalHashCoverage E K.calls := by
  have hcanon₀ : L1.CanonicalHashCoverage K.E₀ K.calls := by
    intro bytes value hashed size exactRead
    obtain ⟨entry, stored, bytesEq, cached⟩ := hW.hashedStored bytes value hashed size
      (L1.deConstant_of_deConstantExact exactRead) exactRead
    refine ⟨⟨entry, value, stored, cached, ?_⟩, rfl⟩
    rw [bytesEq]
    exact exactRead
  exact Assembly.canonicalHashCoverage_frame hcanon₀ hctx.recordsFor.1
    (fun a v h => hctx.runRecord a v ((hW.runStore.recordOf_eq_recordAt a).trans h))

/-- A single observed non-zero `KernelModeled::block_is_modeled` call on `B` in a step store
determines `Route.blockRoute E B = some true` and hence `ModeledRouteAt K.calls B`. -/
theorem modeledRouteAt_of_block_is_modeled {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat} {R E : Ixon.Env} {B : _root_.Address}
    {bp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {b : Bytes.Address}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hctx : StepCtx.{u} K.calls K.t R K.envT K.E₀ E)
    (ev : ObsFn Obs.W "KernelModeled::block_is_modeled" [bp] h r h' cs)
    (hr : r ≠ .field 0) (hsub : ∀ cl ∈ cs, cl ∈ K.calls)
    (hb : Bytes.RepAddressRef Core.addrTy h b bp) (hbB : Core.ixAddr b = B) :
    ModeledRouteAt K.calls B := by
  have hcanon := canonicalHashCoverage_of_step hW hctx
  have g₁ : Core.Good ⟨E, Ix.Kernel.Env.empty, K.t, none⟩ cs :=
    (hctx.toStepStore.good Ix.Kernel.Env.empty none).sub hsub
  have hag₁ := Route.block_is_modeled_agrees (E := E) g₁.1 g₁.2 hb ev
  obtain ⟨v, hv⟩ := hag₁.known (canonicalHashCoverage_sub hsub hcanon)
  have hrv := hag₁.value v hv
  have hv_true : v = true := by
    cases v with
    | true => rfl
    | false => exact (hr hrv).elim
  subst hv_true
  rw [hbB] at hv
  intro bp₂ r₂ h₂ h₂' cs₂ b₂ ev₂ hsub₂ hb₂ hb₂B
  have g₂ : Core.Good ⟨E, Ix.Kernel.Env.empty, K.t, none⟩ cs₂ :=
    (hctx.toStepStore.good Ix.Kernel.Env.empty none).sub hsub₂
  have hag₂ := Route.block_is_modeled_agrees (E := E) g₂.1 g₂.2 hb₂ ev₂
  have hval := hag₂.value true (by rw [hb₂B]; exact hv)
  rw [hval]
  intro h0
  exact one_ne_zero (Value.field.inj h0)

/-- Any observed family check `K.FamCheck B rb` witnesses `ModeledRouteAt K.calls B` under
`FamCallsModeled`. -/
theorem FamRunCtx.modeledRouteAt_of_famCheck {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat} {R E : Ixon.Env} {B rb : _root_.Address}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hctx : StepCtx.{u} K.calls K.t R K.envT K.E₀ E)
    (hfamMod : FamCallsModeled K.calls)
    (hfc : K.FamCheck B rb) :
    ModeledRouteAt K.calls B := by
  obtain ⟨cs, h, h', rc, xb, xrb, r, -, ⟨b, hb, hbB⟩, -, -, hmem, -⟩ := hfc
  obtain ⟨r_mod, m_mod, m_mod', cs_mod, ev_mod, hr_mod, hb_mod, hsub_mod⟩ :=
    hfamMod rc xb xrb h b hmem hb
  exact modeledRouteAt_of_block_is_modeled hW hctx ev_mod hr_mod hsub_mod hb_mod hbB

/-! ## `BatchGives.routed` and `BatchGives.listedNotScope` -/

/-- **Discharges `BatchGives.routed`**: the block of a nested twin is routed as modeled. -/
theorem FamRunCtx.routed_of {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat} {R E : Ixon.Env}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hctx : StepCtx.{u} K.calls K.t R K.envT K.E₀ E)
    (hfamMod : FamCallsModeled K.calls) :
    ∀ a B, K.NestedTwinOf a B → ModeledRouteAt K.calls B := by
  intro a B hnt
  obtain ⟨-, -, -, B₀, rb₀, -, cs₀, -, cs', hfc', -⟩ := hnt
  exact FamRunCtx.modeledRouteAt_of_famCheck hW hctx hfamMod ⟨cs', hfc'⟩

/-- **Discharges `BatchGives.listedNotScope`**: the block of a scope check is listed by no
scope check's own advice walk. -/
theorem FamRunCtx.listedNotScope_of {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat} {R E : Ixon.Env}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hctx : StepCtx.{u} K.calls K.t R K.envT K.E₀ E)
    (hfamMod : FamCallsModeled K.calls) :
    ∀ B rb cs B' rb' cs' advAs (k : Nat) b, K.ScopeAt B rb cs →
      K.ScopeAt B' rb' cs' → FamilyCallOwn K.calls K.bAddr K.t B' rb' K.lim cs' advAs →
      advAs[k]? = some b → Core.ixAddr b ≠ B := by
  intro B rb cs B' rb' cs' advAs k b hS hS' hown' hk hbB
  have hroute : ModeledRouteAt K.calls B :=
    FamRunCtx.modeledRouteAt_of_famCheck hW hctx hfamMod ⟨cs, hS.1⟩
  obtain ⟨cb, _, ms, _, hC⟩ := FamRunCtx.check_family_carriers hW ⟨cs, hS.1⟩
  have hcb : recordOf K.E₀ (Core.ixAddr b) = some cb := hbB.symm ▸ hC.blockRec
  have hnot := FamRunCtx.listedNotModeled_of hW hS' hown' hk hcb hC.blockMuts
  exact hnot (hbB.symm ▸ hroute)

/-! ## `BatchGives.recUsesBlock` -/

/-- **Discharges `BatchGives.recUsesBlock`**: every non-empty record of a scope check uses a
constant address of its block bound to no walked role (`iprjAddr B 0`, checked by
`assert_no_type_role`). -/
theorem FamRunCtx.recUsesBlock_of {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank) :
    ∀ B rb cs, K.ScopeAt B rb cs → ∀ crb rs, recordOf K.E₀ rb = some crb →
      crb.info = .muts rs → 0 < rs.size →
      ∃ cb x, recordOf K.E₀ B = some cb ∧ ConstAddrOf B cb x ∧ ¬ Covered K.t x ∧
        UsedRef K.E₀ rb x := by
  intro B rb cs hS crb rs hrb hmuts hpos
  obtain ⟨cb, crb', ms, rs', hC⟩ := FamRunCtx.check_family_carriers hW ⟨cs, hS.1⟩
  have hce : crb' = crb := Option.some.inj (hC.recRec.record.symm.trans hrb)
  subst crb'
  have hrs : rs' = rs := Ixon.ConstantInfo.muts.inj (hC.recRec.muts.symm.trans hmuts)
  subst rs'
  obtain ⟨ind₀, hind₀⟩ := hC.ind0
  have h0mem : rs[0] ∈ rs.toList := by
    have hL : rs.toList[0]? = some rs[0] := by
      rw [Array.getElem?_toList, Array.getElem?_eq_getElem hpos]
    exact List.mem_of_getElem? hL
  obtain ⟨rc₀, hrc₀⟩ := hC.recRec.recrs rs[0] h0mem
  have hget0 : rs[0]? = some (.recr rc₀) := by rw [Array.getElem?_eq_getElem hpos, hrc₀]
  obtain ⟨n, hmot⟩ := hC.carrier 0 rc₀ hget0
  have hused : UsedRef K.E₀ rb (Core.iprjAddr B 0) :=
    motiveCarrierAt_usedRef hrb hmuts hget0 hmot
  have hca : ConstAddrOf B cb (Core.iprjAddr B 0) := by
    refine Or.inr ⟨ms, 0, .indc ind₀, hC.blockMuts, hind₀, Or.inl ?_⟩
    rw [LoadedReads.memberAddr_eq_projAddr]
    rfl
  have hncov : ¬ Covered K.t (Core.iprjAddr B 0) := by
    rintro ⟨ro, hof, -⟩
    exact hC.noTypeRole 0 ind₀ hind₀ ro hof
  exact ⟨cb, Core.iprjAddr B 0, hC.blockRec, hca, hncov, hused⟩

/-! ## `BatchGives.recArm` -/

/-- **Discharges `BatchGives.recArm`**: every top-walked non-empty block of recursors is the
record of a family check of a top-walked non-empty block of inductive types routed as modeled. -/
theorem FamRunCtx.recArm_of {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat} {R E : Ixon.Env}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hctx : StepCtx.{u} K.calls K.t R K.envT K.E₀ E) :
    ∀ A, K.Top A → RecBlock K.E₀ A →
      ∃ B, K.FamCheck B A ∧ K.Top B ∧ ModeledRouteAt K.calls B ∧ IndBlock K.E₀ B := by
  intro A hTA hRB
  obtain ⟨ca, rs, hca, hca_muts, hpos, hall_rec⟩ := hRB
  have h0mem : rs[0] ∈ rs.toList := by
    have hL : rs.toList[0]? = some rs[0] := by
      rw [Array.getElem?_toList, Array.getElem?_eq_getElem hpos]
    exact List.mem_of_getElem? hL
  obtain ⟨rc₀, hrc₀⟩ := hall_rec rs[0] h0mem
  have hget0 : rs[0]? = some (.recr rc₀) := by rw [Array.getElem?_eq_getElem hpos, hrc₀]
  have hchk : (∃ ms, ca.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt K.calls K.bAddr K.t A ms k K.lim) ∨
      Claim.CheckedLimAt K.calls K.bAddr K.t A K.lim := by
    obtain ⟨c', hc', h⟩ := hW.checked A hTA
    have e : c' = ca := Option.some.inj (hc'.symm.trans hca)
    rw [e] at h
    exact h
  have hm0 : Claim.MemberCheckedLimAt K.calls K.bAddr K.t A rs 0 K.lim :=
    Claim.membersChecked_of_block hW.runStore hca hca_muts hchk 0 hpos
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, ⟨b_A, hb_A, hb_A_eq⟩, ev_pa, -, hsub_pa,
    hrc_pre, -, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hm0
  obtain ⟨-, -, -, mc, a', hget', ha', hproj, hhashed⟩ :=
    L1.projection_addr_hashed_spec hmem hb_A ev_pa
  have hval0 : ((0 : Nat) : F).val = 0 := by simp
  rw [hval0] at hget' hproj hhashed
  have hget0L : rs.toList[0]? = some (.recr rc₀) := by rw [Array.getElem?_toList]; exact hget0
  have hmc_eq : mc = .recr rc₀ := Option.some.inj (hget'.symm.trans hget0L)
  subst hmc_eq
  have ha'_eq : Core.ixAddr a' = memberAddr A 0 (.recr rc₀) := by
    rw [hproj, hb_A_eq, LoadedReads.memberAddr_eq_projAddr]
  have hrec_m0 : recordOf K.E₀ (Core.ixAddr a') = some (memberProjection A 0 (.recr rc₀)) := by
    rw [ha'_eq]
    exact (hW.members A ca rs hTA hca hca_muts 0 (.recr rc₀) hget0).1
  obtain ⟨-, _, ib, _, cib, _, ms_ib, _, _, cs_fam, m_bm, m_bm', xb_bm, v_bm, cs_bm,
      -, -, -, -, -, -, -, -, -, -, ⟨b_ib, hb_ib, hb_ib_eq⟩, ev_bm, hbm_ne0, hsub_bm,
      hfc, -⟩ :=
    rprj_check_const_rec_other hW.runStore hW.hashedStored hrc_pre ⟨a', ha', rfl⟩
      hrec_m0 rfl ev_ld hld ev_chk hsub_ld hsub_chk
  have hroute : ModeledRouteAt K.calls ib :=
    modeledRouteAt_of_block_is_modeled hW hctx ev_bm hbm_ne0
      (fun cl hcl => hsub_chk cl (hsub_bm cl hcl)) hb_ib hb_ib_eq
  -- Extract `K.Top ib` and `IndBlock K.E₀ ib` via `Core.iprjAddr ib 0` from `check_family_carriers`
  obtain ⟨cib', ca', ms_ib', rs', hC⟩ := FamRunCtx.check_family_carriers hW ⟨cs_fam, hfc⟩
  have hca_eq : ca' = ca := Option.some.inj (hC.recRec.record.symm.trans hca)
  subst ca'
  have hrs_eq : rs' = rs := Ixon.ConstantInfo.muts.inj (hC.recRec.muts.symm.trans hca_muts)
  subst rs'
  obtain ⟨ind₀, hind₀⟩ := hC.ind0
  obtain ⟨nf, hmot⟩ := hC.carrier 0 rc₀ hget0
  have hu_iprj0 : UsedRef K.E₀ A (Core.iprjAddr ib 0) :=
    motiveCarrierAt_usedRef hca hca_muts hget0 hmot
  have hncov0 : ¬ Covered K.t (Core.iprjAddr ib 0) := by
    rintro ⟨ro, hof, -⟩
    exact hC.noTypeRole 0 ind₀ hind₀ ro hof
  have hTiprj0 : K.Top (Core.iprjAddr ib 0) := by
    rcases hW.closed A (Core.iprjAddr ib 0) hTA hu_iprj0 with ⟨hT, -⟩ | hcov
    · exact hT
    · exact (hncov0 hcov).elim
  have hrec_iprj0 : recordOf K.E₀ (Core.iprjAddr ib 0) =
      some (memberProjection ib 0 (.indc ind₀)) := by
    have hhh := hC.hashedIPrj0 ind₀ hind₀
    rw [← hb_ib_eq] at hhh ⊢
    have hsz : (Ixon.serConstant ⟨.iPrj ⟨0, Core.ixAddr b_ib⟩, #[], #[], #[], #[]⟩).size <
        4294967296 :=
      serConstant_iprj_size_lt 0 b_ib
    have hexact : Ixon.deConstantExact
        (Ixon.serConstant ⟨.iPrj ⟨0, Core.ixAddr b_ib⟩, #[], #[], #[], #[]⟩) =
        .ok ⟨.iPrj ⟨0, Core.ixAddr b_ib⟩, #[], #[], #[], #[]⟩ :=
      Ixon.Verify.deConstantExact_serConstant _ (L1.projConstant_wireWF_iPrj 0 b_ib)
    have hproj_rec := Claim.recordOf_of_hashed hW.hashedStored
      (by simpa [Core.Specs.Callees.memberProjInfo] using hhh) hsz hexact
    simpa [Core.iprjAddr, Core.projAddr, memberProjection] using hproj_rec
  have hTib : K.Top ib := by
    have hown := (hW.owner (Core.iprjAddr ib 0) (memberProjection ib 0 (.indc ind₀))
      hTiprj0 hrec_iprj0 (Or.inr (Or.inl ⟨⟨0, ib⟩, rfl⟩))).1
    simpa [Ix.Cert.ownerOf, memberProjection] using hown
  have hpos_ib : 0 < ms_ib'.size := (Array.getElem?_eq_some_iff.mp hind₀).1
  have hmem_ind0 : .indc ind₀ ∈ ms_ib'.toList := by
    rw [← Array.getElem?_toList] at hind₀
    exact List.mem_of_getElem? hind₀
  have hall_ind : ∀ m ∈ ms_ib'.toList, ∃ i, m = .indc i := by
    rcases hW.uniform ib cib' ms_ib' hTib hC.blockRec hC.blockMuts with hd | hi | hr
    · obtain ⟨d, hd⟩ := hd (.indc ind₀) hmem_ind0; cases hd
    · exact hi
    · obtain ⟨r', hr'⟩ := hr (.indc ind₀) hmem_ind0; cases hr'
  exact ⟨ib, ⟨cs_fam, hfc⟩, hTib, hroute, ⟨cib', ms_ib', hC.blockRec, hC.blockMuts, hpos_ib, hall_ind⟩⟩

/-! ## `motiveCarrierAt → familyKey → motiveKeys → constsResolve` and `BatchGives.fresh` -/

section FreshBridge

private theorem except_bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem convExpr_unshare {ecx : Ix.Kernel.Reader.ECx .anon}
    (hsrc : ecx.src = c) :
    ∀ (k n : Nat) (e : Ixon.Expr) (E : Core.KExpr),
      n ≤ k → n ≤ c.sharing.size →
      Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n)) e = .ok E →
      ∃ n', n' ≤ n ∧
        Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n'))
          (Binding.FamilyOf.unshare c k e) = .ok E ∧
        ∀ i, Binding.FamilyOf.unshare c k e ≠ .share i
  | 0, n, e, E, hnk, _, hconv => by
    have hn0 : n = 0 := by omega
    subst hn0
    cases e with
    | share i =>
      simp [Ix.Kernel.Reader.convExpr, L1.buildShareTbl, L1.buildShareTblGo,
        Ix.Kernel.Reader.malformed] at hconv
    | var _ | sort _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _
    | app _ _ | lam _ _ | all _ _ | letE _ _ _ _ _ =>
      exact ⟨0, Nat.le_refl _, hconv, fun _ h => by cases h⟩
  | k + 1, n, e, E, hnk, hns, hconv => by
    cases e with
    | share i =>
      have hsz : (L1.buildShareTbl ecx (c.sharing.toList.take n)).size = n := by
        rw [L1.buildShareTbl_size, List.length_take, Array.length_toList, Nat.min_eq_left hns]
      by_cases hi : i.toNat < n
      · have hlt_sh : i.toNat < c.sharing.size := by omega
        have hget_arr : c.sharing[i.toNat]? = some c.sharing[i.toNat] :=
          Array.getElem?_eq_getElem hlt_sh
        have hget_list : c.sharing.toList[i.toNat]? = some c.sharing[i.toNat] := by
          rw [Array.getElem?_toList]; exact hget_arr
        have htbl_get := L1.buildShareTbl_take_getElem? ecx c.sharing.toList hi hget_list
        simp only [Ix.Kernel.Reader.convExpr, htbl_get] at hconv
        obtain ⟨n', hn'le, hconv', hns'⟩ :=
          convExpr_unshare hsrc k i.toNat c.sharing[i.toNat] E (by omega) (by omega) hconv
        refine ⟨n', by omega, ?_, ?_⟩
        · simpa only [Binding.FamilyOf.unshare, hget_arr] using hconv'
        · simpa only [Binding.FamilyOf.unshare, hget_arr] using hns'
      · have hnone : (L1.buildShareTbl ecx (c.sharing.toList.take n))[i.toNat]? = none :=
          Array.getElem?_eq_none (by omega)
        simp [Ix.Kernel.Reader.convExpr, hnone, Ix.Kernel.Reader.malformed] at hconv
    | var _ | sort _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _
    | app _ _ | lam _ _ | all _ _ | letE _ _ _ _ _ =>
      exact ⟨n, Nat.le_refl _, hconv, fun _ h => by cases h⟩

private theorem convExpr_node {c : Ixon.Constant} {ecx : Ix.Kernel.Reader.ECx .anon}
    (hsrc : ecx.src = c) {n : Nat} {e : Ixon.Expr} {E : Core.KExpr}
    (hns : n ≤ c.sharing.size)
    (hconv : Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n)) e = .ok E) :
    ∃ n', n' ≤ n ∧
      Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n'))
        (Binding.FamilyOf.node c e) = .ok E ∧
      ∀ i, Binding.FamilyOf.node c e ≠ .share i :=
  convExpr_unshare hsrc (c.sharing.size + 1) n e E (by omega) hns hconv

private theorem convExpr_peel {c : Ixon.Constant} {ecx : Ix.Kernel.Reader.ECx .anon}
    (hsrc : ecx.src = c) :
    ∀ (m n : Nat) (e e' : Ixon.Expr) (E : Core.KExpr),
      n ≤ c.sharing.size →
      Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n)) e = .ok E →
      Binding.FamilyOf.peel c m e = some e' →
      ∃ bs E' n', n' ≤ n ∧ E.stripPis m = some (bs, E') ∧
        Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n')) e' = .ok E'
  | 0, n, e, e', E, _, hconv, hpeel => by
    simp only [Binding.FamilyOf.peel, Option.some.injEq] at hpeel
    subst hpeel
    exact ⟨[], E, n, Nat.le_refl _, rfl, hconv⟩
  | m + 1, n, e, e', E, hns, hconv, hpeel => by
    obtain ⟨n₁, hn₁, hconv₁, -⟩ := convExpr_node hsrc hns hconv
    unfold Binding.FamilyOf.peel at hpeel
    cases hnd : Binding.FamilyOf.node c e with
    | all d b =>
      rw [hnd] at hpeel hconv₁
      simp only [Ix.Kernel.Reader.convExpr] at hconv₁
      obtain ⟨dE, hdE, h1⟩ := except_bind_eq_ok hconv₁
      obtain ⟨bE, hbE, h2⟩ := except_bind_eq_ok h1
      have hE : E = .forallE dE bE Ix.Kernel.BinderMeta.leanNever := (Except.ok.inj h2).symm
      obtain ⟨bs, E', n₂, hn₂, hstrip, hconv₂⟩ :=
        convExpr_peel hsrc m n₁ b e' bE (by omega) hbE hpeel
      refine ⟨(dE, Ix.Kernel.BinderMeta.leanNever) :: bs, E', n₂, by omega, ?_, hconv₂⟩
      rw [hE, Ix.Kernel.Expr.stripPis, hstrip]
      rfl
    | var _ | sort _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _
    | app _ _ | lam _ _ | letE _ _ _ _ _ | share _ =>
      rw [hnd] at hpeel; cases hpeel

private theorem convExpr_not_forall {ecx : Ix.Kernel.Reader.ECx .anon}
    {tbl : Array (Ix.Kernel.Reader.ReadM Core.KExpr)} {e : Ixon.Expr} {E : Core.KExpr}
    (hns : ∀ i, e ≠ .share i) (hna : ∀ d b, e ≠ .all d b)
    (hconv : Ix.Kernel.Reader.convExpr ecx tbl e = .ok E) :
    ∀ d b bm, E ≠ .forallE d b bm := by
  cases e with
  | all d b => exact (hna d b rfl).elim
  | share i => exact (hns i rfl).elim
  | var _ =>
    simp only [Ix.Kernel.Reader.convExpr, Ix.Kernel.Expr.mkBvar_eq] at hconv
    have hE := Except.ok.inj hconv; subst hE; intro _ _ _ h; cases h
  | sort _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, -, h1⟩ := except_bind_eq_ok hconv
    have hE := Except.ok.inj h1; subst hE; intro _ _ _ h; cases h
  | ref _ _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, -, h1⟩ := except_bind_eq_ok hconv
    obtain ⟨_, -, h2⟩ := except_bind_eq_ok h1
    have hE := Except.ok.inj h2; subst hE; intro _ _ _ h; cases h
  | recur i _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    cases hs : ecx.self i.toNat with
    | none => simp [hs, Ix.Kernel.Reader.malformed] at hconv
    | some m =>
      rw [hs] at hconv
      obtain ⟨_, -, h1⟩ := except_bind_eq_ok hconv
      obtain ⟨_, -, h2⟩ := except_bind_eq_ok h1
      have hE := Except.ok.inj h2; subst hE; intro _ _ _ h; cases h
  | prj _ _ _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, -, h1⟩ := except_bind_eq_ok hconv
    obtain ⟨_, -, h2⟩ := except_bind_eq_ok h1
    have hE := Except.ok.inj h2; subst hE; intro _ _ _ h; cases h
  | str _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨bs, -, h1⟩ := except_bind_eq_ok hconv
    cases hs : String.fromUTF8? bs with
    | none => simp [hs, Ix.Kernel.Reader.malformed] at h1
    | some s =>
      simp only [hs] at h1
      have hE := Except.ok.inj h1; subst hE; intro _ _ _ h; cases h
  | nat _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, -, h1⟩ := except_bind_eq_ok hconv
    have hE := Except.ok.inj h1; subst hE; intro _ _ _ h; cases h
  | app _ _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, -, h1⟩ := except_bind_eq_ok hconv
    obtain ⟨_, -, h2⟩ := except_bind_eq_ok h1
    have hE := Except.ok.inj h2; subst hE; intro _ _ _ h; cases h
  | lam _ _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, -, h1⟩ := except_bind_eq_ok hconv
    obtain ⟨_, -, h2⟩ := except_bind_eq_ok h1
    have hE := Except.ok.inj h2; subst hE; intro _ _ _ h; cases h
  | letE _ _ _ _ _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, -, h1⟩ := except_bind_eq_ok hconv
    obtain ⟨_, -, h2⟩ := except_bind_eq_ok h1
    obtain ⟨_, -, h3⟩ := except_bind_eq_ok h2
    have hE := Except.ok.inj h3; subst hE; intro _ _ _ h; cases h

private theorem convExpr_lastDom {c : Ixon.Constant} {ecx : Ix.Kernel.Reader.ECx .anon}
    (hsrc : ecx.src = c) :
    ∀ (k n : Nat) (e d : Ixon.Expr) (E : Core.KExpr),
      n ≤ c.sharing.size →
      Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n)) e = .ok E →
      Binding.FamilyOf.lastDom c k e = some d →
      ∃ dE n', n' ≤ n ∧ lastBinderDom E = some dE ∧
        Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n')) d = .ok dE
  | 0, _, _, _, _, _, _, hld => by simp [Binding.FamilyOf.lastDom] at hld
  | k + 1, n, e, d, E, hns, hconv, hld => by
    obtain ⟨n₁, hn₁, hconv₁, -⟩ := convExpr_node hsrc hns hconv
    unfold Binding.FamilyOf.lastDom at hld
    cases hnd : Binding.FamilyOf.node c e with
    | all d' b' =>
      rw [hnd] at hld hconv₁
      dsimp only at hld
      simp only [Ix.Kernel.Reader.convExpr] at hconv₁
      obtain ⟨dE, hdE, h1⟩ := except_bind_eq_ok hconv₁
      obtain ⟨bE, hbE, h2⟩ := except_bind_eq_ok h1
      have hE : E = .forallE dE bE Ix.Kernel.BinderMeta.leanNever := (Except.ok.inj h2).symm
      obtain ⟨n₂, hn₂, hbE₂, hns₂⟩ := convExpr_node hsrc (by omega) hbE
      cases hbnd : Binding.FamilyOf.node c b' with
      | all d'' b'' =>
        rw [hbnd] at hld hbE₂
        simp only [Ix.Kernel.Reader.convExpr] at hbE₂
        obtain ⟨dE2, -, h1'⟩ := except_bind_eq_ok hbE₂
        obtain ⟨bE2, -, h2'⟩ := except_bind_eq_ok h1'
        have hbE_eq : bE = .forallE dE2 bE2 Ix.Kernel.BinderMeta.leanNever := (Except.ok.inj h2').symm
        obtain ⟨dE_out, n₃, hn₃, hl_b, hconv_out⟩ :=
          convExpr_lastDom hsrc k n₁ b' d bE (by omega) hbE hld
        refine ⟨dE_out, n₃, by omega, ?_, hconv_out⟩
        rw [hE, hbE_eq]
        simpa [lastBinderDom, hbE_eq] using hl_b
      | var _ | sort _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _
      | app _ _ | lam _ _ | letE _ _ _ _ _ | share _ =>
        rw [hbnd] at hld hbE₂ hns₂
        have hd_eq : d' = d := Option.some.inj hld
        subst hd_eq
        have hnotf := convExpr_not_forall hns₂ (fun _ _ h => by cases h) hbE₂
        refine ⟨dE, n₁, hn₁, ?_, hdE⟩
        rw [hE]
        cases bE with
        | forallE d0 b0 bm0 => exact (hnotf d0 b0 bm0 rfl).elim
        | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _
        | letE _ _ _ _ | lit _ | proj _ _ _ => rfl
    | var _ | sort _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _
    | app _ _ | lam _ _ | letE _ _ _ _ _ | share _ =>
      rw [hnd] at hld; cases hld

private theorem convExpr_spineHead_ref {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) {blob : _root_.Address → Option ByteArray}
    {c : Ixon.Constant} {param : Nat → Ix.Kernel.LevelParam}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {rIdx : UInt64} {uIdxs : Array UInt64} {a : _root_.Address}
    (href : c.refs[rIdx.toNat]? = some a) :
    let ecx : Ix.Kernel.Reader.ECx .anon :=
      ⟨readCtx t blob, c, c.univs.map (Ix.Kernel.Reader.convUniv param), self⟩
    ∀ (k n : Nat) (e : Ixon.Expr) (E : Core.KExpr),
      n ≤ c.sharing.size →
      Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n)) e = .ok E →
      Binding.FamilyOf.spineHead c k e = .ref rIdx uIdxs →
      headKey E = some (keyOf t a) := by
  intro ecx k
  induction k with
  | zero =>
    intro n e E hns hconv hsp
    obtain ⟨n₁, hn₁, hconv₁, -⟩ := convExpr_node (c := c) rfl hns hconv
    simp only [Binding.FamilyOf.spineHead] at hsp
    rw [hsp] at hconv₁
    simp only [Ix.Kernel.Reader.convExpr] at hconv₁
    obtain ⟨k', hk', h1⟩ := except_bind_eq_ok hconv₁
    obtain ⟨ls, -, h2⟩ := except_bind_eq_ok h1
    have hE : E = .const k' ls := (Except.ok.inj h2).symm
    have hk_eq : k' = keyOf t a := by
      simp only [ecx, Ix.Kernel.Reader.ECx.keyAt, href] at hk'
      rw [readCtx_keyAt ht blob a] at hk'
      exact (Except.ok.inj hk').symm
    rw [hE, hk_eq]
    rfl
  | succ k ih =>
    intro n e E hns hconv hsp
    obtain ⟨n₁, hn₁, hconv₁, -⟩ := convExpr_node (c := c) rfl hns hconv
    unfold Binding.FamilyOf.spineHead at hsp
    cases hnd : Binding.FamilyOf.node c e with
    | app f arg =>
      rw [hnd] at hsp hconv₁
      simp only [Ix.Kernel.Reader.convExpr] at hconv₁
      obtain ⟨fE, hfE, h1⟩ := except_bind_eq_ok hconv₁
      obtain ⟨aE, -, h2⟩ := except_bind_eq_ok h1
      have hE : E = .app fE aE := (Except.ok.inj h2).symm
      rw [hE]
      exact ih n₁ f fE (by omega) hfE hsp
    | ref rIdx' uIdxs' =>
      rw [hnd] at hsp hconv₁
      injection hsp with hr_eq hu_eq
      subst hr_eq hu_eq
      simp only [Ix.Kernel.Reader.convExpr] at hconv₁
      obtain ⟨k', hk', h1⟩ := except_bind_eq_ok hconv₁
      obtain ⟨ls, -, h2⟩ := except_bind_eq_ok h1
      have hE : E = .const k' ls := (Except.ok.inj h2).symm
      have hk_eq : k' = keyOf t a := by
        simp only [ecx, Ix.Kernel.Reader.ECx.keyAt, href] at hk'
        rw [readCtx_keyAt ht blob a] at hk'
        exact (Except.ok.inj hk').symm
      rw [hE, hk_eq]
      rfl
    | var _ | sort _ | recur _ _ | prj _ _ _ | str _ | nat _
    | lam _ _ | all _ _ | letE _ _ _ _ _ | share _ =>
      rw [hnd] at hsp; cases hsp

private theorem familyKey_of_motiveCarrierAt {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {blob : _root_.Address → Option ByteArray} {c : Ixon.Constant} {rc : Ixon.Recursor}
    {param : Nat → Ix.Kernel.LevelParam}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {nf : Nat} {a : _root_.Address} {ty : Core.KExpr}
    (hread : (exprReader t blob c param self).read rc.typ = .ok ty)
    (hmot : Binding.FamilyOf.motiveCarrierAt c rc 0 nf = some a) :
    familyKey rc ty = some (keyOf t a) := by
  obtain ⟨hecx, htbl⟩ := L1.memberReader_mk'_eq (readCtx t blob) c param self
  unfold exprReader Ix.Kernel.Reader.MemberReader.read at hread
  rw [hecx, htbl, ← List.take_length (l := c.sharing.toList), Array.length_toList] at hread
  unfold Binding.FamilyOf.motiveCarrierAt at hmot
  rw [Nat.add_zero] at hmot
  cases hpeel : Binding.FamilyOf.peel c rc.params.toNat rc.typ with
  | none => rw [hpeel] at hmot; simp at hmot
  | some e1 =>
    rw [hpeel] at hmot; dsimp only [bind, Option.bind] at hmot
    cases hdom : Binding.FamilyOf.domOf c e1 with
    | none => rw [hdom] at hmot; simp at hmot
    | some em =>
      rw [hdom] at hmot; dsimp only [bind, Option.bind] at hmot
      cases hld : Binding.FamilyOf.lastDom c nf em with
      | none => rw [hld] at hmot; simp at hmot
      | some ed =>
        rw [hld] at hmot; dsimp only [bind, Option.bind] at hmot
        unfold Binding.FamilyOf.refHeadAt at hmot
        cases hsp : Binding.FamilyOf.spineHead c nf ed with
        | ref rIdx uIdxs =>
          rw [hsp] at hmot
          obtain ⟨bs, E1, n₁, hn₁, hstrip, hconv₁⟩ :=
            convExpr_peel (c := c) rfl rc.params.toNat c.sharing.size rc.typ e1 ty
              (Nat.le_refl _) hread hpeel
          obtain ⟨n₂, hn₂, hconv₂, -⟩ := convExpr_node (c := c) rfl (by omega) hconv₁
          unfold Binding.FamilyOf.domOf at hdom
          cases hnd1 : Binding.FamilyOf.node c e1 with
          | all d1 b1 =>
            rw [hnd1] at hdom hconv₂
            have hem_eq : d1 = em := Option.some.inj hdom
            subst d1
            simp only [Ix.Kernel.Reader.convExpr] at hconv₂
            obtain ⟨mE, hmE, h1⟩ := except_bind_eq_ok hconv₂
            obtain ⟨bE, -, h2⟩ := except_bind_eq_ok h1
            have hE1 : E1 = .forallE mE bE Ix.Kernel.BinderMeta.leanNever := (Except.ok.inj h2).symm
            obtain ⟨dE, n₃, hn₃, hlast, hconv₃⟩ :=
              convExpr_lastDom (c := c) rfl nf n₂ em ed mE (by omega) hmE hld
            have hhead := convExpr_spineHead_ref ht (param := param) (self := self)
              hmot nf n₃ ed dE (by omega) hconv₃ hsp
            unfold familyKey binderDom
            rw [hstrip, hE1]
            simp [hlast, hhead]
          | var _ | sort _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _
          | app _ _ | lam _ _ | letE _ _ _ _ _ | share _ =>
            rw [hnd1] at hdom; cases hdom
        | var _ | sort _ | recur _ _ | prj _ _ _ | str _ | nat _
        | app _ _ | lam _ _ | all _ _ | letE _ _ _ _ _ | share _ =>
          rw [hsp] at hmot; cases hmot

private def spineKeysF : Core.KExpr → List Core.KKey
  | .const k _ => [k]
  | .app f _ => spineKeysF f
  | _ => []

private def binderKeysF : Core.KExpr → List Core.KKey
  | .forallE d b _ => spineKeysF d ++ binderKeysF b
  | _ => []

private def motiveKeysF : Core.KExpr → List Core.KKey
  | .forallE d b _ => binderKeysF d ++ motiveKeysF b
  | _ => []

private theorem spineKeysF_eq (e : Core.KExpr) : spineKeysF e = (headKey e).toList := by
  induction e with
  | app f x ih _ => exact ih
  | _ => rfl

private theorem spineKeysF_ann {ann raw : Core.KExpr} (a : Annotates ann raw) :
    spineKeysF raw ⊆ spineKeysF ann := by
  induction a with
  | app _ _ ih _ => exact ih
  | const => exact fun _ h => h
  | _ => simp [spineKeysF]

private theorem binderKeysF_ann {ann raw : Core.KExpr} (a : Annotates ann raw) :
    binderKeysF raw ⊆ binderKeysF ann := by
  induction a with
  | forallE d _ _ ih =>
    intro k hk
    exact List.mem_append.mpr
      ((List.mem_append.mp hk).imp (fun h => spineKeysF_ann d h) (fun h => ih h))
  | _ => simp [binderKeysF]

private theorem motiveKeysF_ann {ann raw : Core.KExpr} (a : Annotates ann raw) :
    motiveKeysF raw ⊆ motiveKeysF ann := by
  induction a with
  | forallE d _ _ ih =>
    intro k hk
    exact List.mem_append.mpr
      ((List.mem_append.mp hk).imp (fun h => binderKeysF_ann d h) (fun h => ih h))
  | _ => simp [motiveKeysF]

private theorem lastBinder_keysF {e d : Core.KExpr} {k : Core.KKey} (last : lastBinderDom e = some d)
    (head : k ∈ spineKeysF d) : k ∈ binderKeysF e := by
  induction e with
  | forallE dom b m _ ih =>
    cases b <;> first
      | exact List.mem_append_right _ (ih last)
      | exact List.mem_append_left _ ((Option.some.inj last).symm ▸ head)
  | _ => cases last

private theorem stripped_keysF {n : Nat} {e d b : Core.KExpr} {m : Ix.Kernel.BinderMeta}
    {bs : List (Core.KExpr × Ix.Kernel.BinderMeta)} {k : Core.KKey}
    (strip : e.stripPis n = some (bs, .forallE d b m)) (head : k ∈ binderKeysF d) :
    k ∈ motiveKeysF e := by
  induction n generalizing e bs with
  | zero =>
    have eq : e = .forallE d b m := (Prod.mk.inj (Option.some.inj strip)).2
    rw [eq]
    exact List.mem_append_left _ head
  | succ n ih =>
    cases e with
    | forallE dom body md =>
      cases sub : body.stripPis n with
      | none => simp [Ix.Kernel.Expr.stripPis, sub] at strip
      | some pair =>
        obtain ⟨tail, out⟩ := pair
        rw [Ix.Kernel.Expr.stripPis, sub] at strip
        have eq : out = .forallE d b m := (Prod.mk.inj (Option.some.inj strip)).2
        rw [eq] at sub
        exact List.mem_append_right _ (ih sub)
    | _ => cases strip

private theorem familyKey_mem_motiveKeysF {r : Ixon.Recursor} {raw : Core.KExpr} {k : Core.KKey}
    (key : familyKey r raw = some k) : k ∈ motiveKeysF raw := by
  unfold familyKey binderDom at key
  cases hs : raw.stripPis r.params.toNat with
  | none => rw [hs] at key; cases key
  | some pair =>
    obtain ⟨bs, body⟩ := pair
    rw [hs] at key
    cases body with
    | forallE d b bm =>
      cases hl : lastBinderDom d with
      | none => simp [hl] at key
      | some z =>
        have hk : headKey z = some k := by simpa [hl] using key
        exact stripped_keysF hs (lastBinder_keysF hl (by simp [spineKeysF_eq, hk]))
    | _ => cases key

private theorem constsResolve_spineKeysF {env : Ix.Kernel.Env .anon} :
    ∀ {e : Core.KExpr} {k : Core.KKey},
      e.constsResolve env = true → k ∈ spineKeysF e → (env.find? k).isSome = true
  | .const k' _, k, hres, hk => by
    simp only [spineKeysF, List.mem_singleton] at hk
    subst hk
    simpa [Ix.Kernel.Expr.constsResolve] using hres
  | .app f a, k, hres, hk => by
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hres
    exact constsResolve_spineKeysF hres.1 hk
  | .bvar _, _, _, hk | .fvar _ _, _, _, hk | .sort _, _, _, hk | .lam _ _ _, _, _, hk
  | .forallE _ _ _, _, _, hk | .letE _ _ _ _, _, _, hk | .lit _, _, _, hk
  | .proj _ _ _, _, _, hk => by simp [spineKeysF] at hk

private theorem constsResolve_binderKeysF {env : Ix.Kernel.Env .anon} :
    ∀ {e : Core.KExpr} {k : Core.KKey},
      e.constsResolve env = true → k ∈ binderKeysF e → (env.find? k).isSome = true
  | .forallE d b _, k, hres, hk => by
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hres
    rcases List.mem_append.mp hk with hd | hb
    · exact constsResolve_spineKeysF hres.1 hd
    · exact constsResolve_binderKeysF hres.2 hb
  | .bvar _, _, _, hk | .fvar _ _, _, _, hk | .sort _, _, _, hk | .const _ _, _, _, hk
  | .app _ _, _, _, hk | .lam _ _ _, _, _, hk | .letE _ _ _ _, _, _, hk | .lit _, _, _, hk
  | .proj _ _ _, _, _, hk => by simp [binderKeysF] at hk

private theorem constsResolve_motiveKeysF {env : Ix.Kernel.Env .anon} :
    ∀ {e : Core.KExpr} {k : Core.KKey},
      e.constsResolve env = true → k ∈ motiveKeysF e → (env.find? k).isSome = true
  | .forallE d b _, k, hres, hk => by
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hres
    rcases List.mem_append.mp hk with hd | hb
    · exact constsResolve_binderKeysF hres.1 hd
    · exact constsResolve_motiveKeysF hres.2 hb
  | .bvar _, _, _, hk | .fvar _ _, _, _, hk | .sort _, _, _, hk | .const _ _, _, _, hk
  | .app _ _, _, _, hk | .lam _ _ _, _, _, hk | .letE _ _ _ _, _, _, hk | .lit _, _, _, hk
  | .proj _ _ _, _, _, hk => by simp [motiveKeysF] at hk

set_option maxRecDepth 100000 in
private theorem pinned_names_basisRole_fresh (kind : Ix.Kernel.BasisKind) :
    ∀ n ∈ (kind.declsA (md := .anon)).map (·.name),
      n ∈ TableInhabit.basisRoleOrder.map Ix.Kernel.Key.role := by
  cases kind <;> decide +kernel

end FreshBridge

/-- **Discharges `BatchGives.fresh`**: the witness's environment stores no constant address of
the family record of a block it does not store whole. -/
theorem FamRunCtx.fresh_of {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat} {R E : Ixon.Env}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank)
    (hagree : RecordsAgree K.E₀ R)
    (hctx : StepCtx.{u} K.calls K.t R K.envT K.E₀ E)
    (hEnvWF : Ix.Kernel.EnvWF K.envT)
    (hWhole : ∀ E', RecordsFor R E' →
      ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
        (K.envT.find? (keyOf K.t a)).isSome = true → Ix.Cert.recordAt E' a = some c →
        Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E' B = some cb → cb.info = .muts ms →
        BlockStored K.t K.envT B ms) :
    ∀ B rb crb x, K.FamCheck B rb → K.FamBlock B → recordOf K.E₀ rb = some crb →
      ConstAddrOf rb crb x → ¬ StoredAt K.t K.envT x := by
  intro B rb crb x hFC hFB hrb hx hst
  have hcheck : K.t.check = .ok () := hW.check_ok
  have htwf : K.t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [hcheck]; rfl
  have hroles : (K.t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup hcheck).1
  obtain ⟨cb, crb', ms, rs, hC⟩ := FamRunCtx.check_family_carriers hW hFC
  have hcrb_eq : crb' = crb := Option.some.inj (hC.recRec.record.symm.trans hrb)
  subst crb'
  -- `x` must be a member projection `memberAddr rb k (.recr rc_k)` of `rb`
  have hx_mem : ∃ k rc_k, rs[k]? = some (.recr rc_k) ∧ x = memberAddr rb k (.recr rc_k) := by
    rcases hx with ⟨-, hstand⟩ | ⟨ms', k, m, hmuts', hk', hx_or⟩
    · exfalso
      rcases hstand with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [hC.recRec.muts] at h <;> cases h
    · have hrs_eq : ms' = rs := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hC.recRec.muts)
      subst ms'
      have hm_in : m ∈ rs.toList := by rw [← Array.getElem?_toList] at hk'; exact List.mem_of_getElem? hk'
      obtain ⟨rc_k, rfl⟩ := hC.recRec.recrs m hm_in
      rcases hx_or with rfl | ⟨_, _, hbad, -⟩
      · exact ⟨k, rc_k, hk', rfl⟩
      · cases hbad
  obtain ⟨k, rc_k, hk_get, rfl⟩ := hx_mem
  have hno_role_x : ∀ ro, K.t.addressOf? ro ≠ some (memberAddr rb k (.recr rc_k)) :=
    hC.noRole k (.recr rc_k) hk_get
  have hrec_x : recordOf K.E₀ (memberAddr rb k (.recr rc_k)) =
      some (memberProjection rb k (.recr rc_k)) :=
    hC.recRec.members k (.recr rc_k) hk_get
  -- Provenance of the stored constant at `x`
  obtain ⟨ci, hfind⟩ := Option.isSome_iff_exists.mp (find_isSome_of_storedAt hst)
  have hname : ci.name = keyOf K.t (memberAddr rb k (.recr rc_k)) :=
    Ix.Kernel.Semantics.Env.find?_name hfind
  obtain ⟨hclaimed, hna⟩ := seed_claimed hfind
  have hkept : KeptIn K.t (recordOf R) (fun z => R.blobs.get? z) (memberAddr rb k (.recr rc_k)) ci := by
    rcases hctx.shape.reading.provenance ci hclaimed with ⟨tbl, htbl⟩ | ⟨kind, hci⟩ | ⟨a, hk⟩
    · rw [htbl] at hna
      exact absurd rfl (hna tbl.structName .projTable)
    · exfalso
      obtain ⟨r, -, hrk⟩ : ∃ r ∈ TableInhabit.basisRoleOrder, ci.name = .role r := by
        obtain ⟨r, hr, he⟩ := List.mem_map.mp
          (pinned_names_basisRole_fresh kind ci.name (List.mem_map.mpr ⟨ci, hci, rfl⟩))
        exact ⟨r, hr, he.symm⟩
      have had : K.t.addressOf? r = some (memberAddr rb k (.recr rc_k)) :=
        Core.addressOf_of_keyOf htwf (by rw [LoadedReads.keyOf_eq]; exact hname.symm.trans hrk)
      exact hno_role_x r had
    · have haa : a = memberAddr rb k (.recr rc_k) :=
        keyOf_inj hroles ((keptIn_name hk).symm.trans hname)
      rwa [haa] at hk
  -- Unpack `ReadsIn` on `.rPrj` to get `RecReads` over `crb`
  obtain ⟨-, ci₀, ⟨cx_R, hcx_R, hread_x⟩, hstoredAs⟩ := hkept
  have hcx_eq : cx_R = memberProjection rb k (.recr rc_k) :=
    (hagree _ _ _ hrec_x hcx_R).symm
  subst cx_R
  simp only [memberProjection, ReadsRecord] at hread_x
  obtain ⟨crb_R, rs_R, rc', ⟨hrb_R, hmuts_R, hk_R, -, -, -⟩, hrecReads⟩ := hread_x
  have hcrb_R_eq : crb_R = crb := (hagree _ _ _ hrb hrb_R).symm
  subst crb_R
  have hrs_R_eq : rs_R = rs := Ixon.ConstantInfo.muts.inj (hmuts_R.symm.trans hC.recRec.muts)
  subst rs_R
  -- `RecReads` gives `ty` read from `rc'.typ`; `hC.carrier` gives `motiveCarrierAt crb rc' 0 nf = some (iprjAddr B 0)`
  obtain ⟨_, ty, _, _, _, _, _, _, _, _, ps, rules, -, -, -, -, -, -, hread_ty, -, -, hci0_eq⟩ :=
    hrecReads
  obtain ⟨nf, hmot⟩ := hC.carrier k.toUInt64.toNat rc' hk_R
  have hfk : familyKey rc' ty = some (keyOf K.t (Core.iprjAddr B 0)) :=
    familyKey_of_motiveCarrierAt hcheck hread_ty hmot
  have hty0_eq : ci₀.toConstantVal.type = ty := by rw [hci0_eq]; rfl
  have hann : Annotates ci.toConstantVal.type ty := hty0_eq ▸ hstoredAs.1.2.2
  have hmem_k : keyOf K.t (Core.iprjAddr B 0) ∈ motiveKeysF ci.toConstantVal.type :=
    motiveKeysF_ann hann (familyKey_mem_motiveKeysF hfk)
  have hres : ci.toConstantVal.type.constsResolve K.envT = true :=
    (hEnvWF ci (Ix.Kernel.Semantics.Env.find?_mem hfind)).2.2.1
  have hiprj0_stored : (K.envT.find? (keyOf K.t (Core.iprjAddr B 0))).isSome = true :=
    constsResolve_motiveKeysF hres hmem_k
  -- Apply `hWhole` to deduce `BlockStored K.t K.envT B ms`, contradicting `hFB.Unstored`
  obtain ⟨ind₀, hind₀⟩ := hC.ind0
  have hrec_iprj0 : recordOf K.E₀ (Core.iprjAddr B 0) =
      some (memberProjection B 0 (.indc ind₀)) := by
    have hmem0 := (hW.members B cb ms hFB.1 hC.blockRec hC.blockMuts 0 (.indc ind₀) hind₀).1
    simpa [LoadedReads.memberAddr_eq_projAddr, Core.iprjAddr, Core.projAddr,
      Core.Specs.Callees.memberProjInfo] using hmem0
  have hB_ne : B ≠ Core.iprjAddr B 0 := by
    intro heq
    rw [← heq] at hrec_iprj0
    have hce : cb = memberProjection B 0 (.indc ind₀) :=
      Option.some.inj (hC.blockRec.symm.trans hrec_iprj0)
    have hbad := hC.blockMuts
    rw [hce] at hbad
    simp [memberProjection] at hbad
  have hBS : BlockStored K.t K.envT B ms :=
    hWhole E hctx.recordsFor (Core.iprjAddr B 0) B (memberProjection B 0 (.indc ind₀)) cb ms
      hiprj0_stored (hctx.runRecord _ _ hrec_iprj0) rfl hB_ne
      (hctx.runRecord _ _ hC.blockRec) hC.blockMuts
  obtain ⟨cb_u, y, hcb_u, hy, hny⟩ := hFB.2.2.2.1
  have hcb_eq : cb_u = cb := Option.some.inj (hcb_u.symm.trans hC.blockRec)
  subst cb_u
  apply hny
  rcases hy with ⟨-, hstand⟩ | ⟨ms_u, i, m, hmuts_u, hi, hy_or⟩
  · exfalso
    rcases hstand with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [hC.blockMuts] at h <;> cases h
  · have hms_eq : ms_u = ms := Ixon.ConstantInfo.muts.inj (hmuts_u.symm.trans hC.blockMuts)
    subst ms_u
    rcases hy_or with rfl | ⟨ind, j, rfl, hj, rfl⟩
    · obtain ⟨ci_y, hfy⟩ := Option.isSome_iff_exists.mp (hBS i m hi).1
      exact storedAt_of_find hfy
    · obtain ⟨ci_y, hfy⟩ := Option.isSome_iff_exists.mp ((hBS i (.indc ind) hi).2 ind j rfl hj)
      exact storedAt_of_find hfy

/-! ## Complete `BatchGives` assembly -/

/-- **Complete `BatchGives K`** for any top-level typing walk at a step store whose witness
environment is well-formed (`EnvWF`) and stores blocks whole (`BoundaryFacts.whole`). -/
theorem FamRunCtx.batchGives_of_run {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat} {R E : Ixon.Env}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank)
    (hagree : RecordsAgree K.E₀ R)
    (hctx : StepCtx.{u} K.calls K.t R K.envT K.E₀ E)
    (hfamMod : FamCallsModeled K.calls)
    (hEnvWF : Ix.Kernel.EnvWF K.envT)
    (hWhole : ∀ E', RecordsFor R E' →
      ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
        (K.envT.find? (keyOf K.t a)).isSome = true → Ix.Cert.recordAt E' a = some c →
        Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E' B = some cb → cb.info = .muts ms →
        BlockStored K.t K.envT B ms) :
    BatchGives K :=
  { recArm := FamRunCtx.recArm_of hW hctx
    routed := FamRunCtx.routed_of hW hctx hfamMod
    inLogic := fun _ _ h _ hc => FamRunCtx.inLogic_of hW h hc
    blockOf := fun _ _ _ _ _ h1 h2 hrb hx => FamRunCtx.blockOf_of hW h1 h2 hrb hx
    fresh := FamRunCtx.fresh_of hW hG hagree hctx hEnvWF hWhole
    familyRefs := fun _ _ _ hS _ hu => FamRunCtx.familyRefs_of hW hS hu
    adviceRefs := fun _ _ _ _ hS hown _ _ hk _ hu => FamRunCtx.adviceRefs_of hW hS hown hk hu
    contWitness := fun _ _ _ _ hS hwit hncov => FamRunCtx.contWitness_of hW hS hwit hncov
    recUsesBlock := FamRunCtx.recUsesBlock_of hW
    listedNotScope := FamRunCtx.listedNotScope_of hW hctx hfamMod }

end IxVM.Refinement.Typing
