import IxVMRefinement.TwinFamily.ProducerRow
import IxVMRefinement.Binding.RunPredicate
import IxVMRefinement.Binding.ClosureUnitDispatch
import IxVMRefinement.Binding.RouteModeledRun

/-! # Binding-closure twin recursor step producer (`Binding.ClosureTwinSteps`)

Discharges the binding fold's twin-step premise (`Binding.ClosureTwinSteps`) at every group
`6 ≤ g < 77` of every binding run (`Binding.BindingRun`), from the three minimal upstream
interfaces isolated in `TwinFamily.ProducerRow`:

* `TwinCallFlat`: positional flattened family (`FamilyOfBlock`, `RecordFlat`, `BlockDerivedFlat`,
  and recursor level-count agreement with the elimination offset) from an accepted `check_family`
  call;
* `TwinCallRecon`: reconstruction or observed wrapper-consumption form (`RFormS ∨ RecordWrapConsObs`)
  from an accepted `check_family` call;
* `StoredRecLvlsOk`: level-count agreement of a stored family recursor with its block's elimination
  offset.

Because every canonical family record in the binding closure already carries `FamilyRecon.RFormS`
(from `StoredFamilies.form` for pre-group stored blocks, and from `GroupFamilyChecks.familyForm`
for new blocks in the group), no graph-store closure premise is required here.

* `overUnitStepTwin_of_parts`: lifts a parts producer at `(Ec, some (Binding.valLimit g))` to
  `Binding.OverUnitStepTwin` across every record store `E` for `R₁` and every carried limit,
  preserving the fold's clause with the same registry (`foldClauseWith_twinStep`).
* `closureTwinSteps_of_premises`: dispatches a new unclaimed twin-shaped recursor block `A` via
  `GroupFamilyChecks.claimed`, recovers its block `B` and modeled route over `R₁` via
  `familyCall_usedRef_ind0` and `BindingRun.famCallsModeled`, splits on whether `B` was held before
  the group (`StoredFamilies`) or new in the group (`ClosureRunFacts.routeNew` +
  `GroupFamilyChecks.familyForm`), and exports `∀ calls, Binding.AtGroups (Binding.BindingRun calls)
  (Binding.ClosureTwinSteps FormerOpenTraceAt calls)`. -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim coveredAt_stored)
open IxVM.Refinement.Binding (BRun BindingRun AtGroups ClosureCtx ClosureTwinSteps OverUnitStepTwin
  StoredFamiliesRForm StoredFamilyRecs IsTwinShape)
open IxVM.Refinement.Binding.FamilyOf (FamilyOfBlock)
open IxVM.Refinement.Binding.FamilyFlat (FlatEntry RecordFlat BlockDerivedFlat)
open IxVM.Refinement.Binding.FamilyRecon (ReconView RFormS MemberRecon)
open Ix.Kernel (ConstantInfo ConstantVal RecRule)
open Ix.Kernel.Semantics (DeclRecTwinRunJ TwinRecPart twinModels twinRecs)
open Ix.Kernel.Model (HasModel)
open IxVM.Refinement.Decl (twinPosRulesJ)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Lifting twin parts to `OverUnitStepTwin` -/

/-- **Lift a twin parts producer at `(Ec, some (Binding.valLimit g))` to `OverUnitStepTwin`**:
executes IxC's twin step once over `Ec`, then transports the fold's clause (`FoldClauseWith`) with
the same registry `Reg` to every record store `E` for `R₁` and every carried limit within `(· < g)`
via `foldClauseWith_twinStep`, `twinKeepsStoreAr`, `coreCompanions_twin`, `twinMember_reloads_at`,
and `twinRecs_recNotKAt_at`. -/
private theorem overUnitStepTwin_of_parts {t : Ix.Kernel.RoleTable}
    {g : Nat} {R₁ E₀ Ec : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {A rb : _root_.Address} {c crb : Ixon.Constant} {rs' : Array Ixon.MutConst}
    (ht : t.check = .ok ())
    (hblobs : ∀ x b, E₀.blobs.get? x = some b → R₁.blobs.get? x = some b)
    (hcl₁ : UsedClosed R₁)
    (hc₁ : recordOf R₁ A = some c)
    (hRc : RecordsFor R₁ Ec)
    (hA : FamRecRecord E₀ A c rs')
    (hszA : rs'.size ≠ 0)
    (hkeyA : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x))
    (hparts : ∀ (env : Ix.Kernel.Env .anon),
      (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (env.consts.map (·.name)).Nodup →
      Decl.PrefixInv.{u} Ec t (some (Binding.valLimit g)) env →
      (∀ x, UsedRef E₀ A x →
        (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x) →
      FamilyInstalled t env rb crb →
      (∀ x, ConstAddrOf rb crb x →
        ∃ ci ci₀, env.find? (keyOf t x) = some ci ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) →
      (∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none) →
      ∃ ds : List Decl.TwinMemberData,
        TwinDeclReads t E₀ A c (ds.map fun d => .recInfo d.cvW d.mI d.rP d.rulesW) ∧
        TwinPartsFacts t env rb crb (Decl.mkTwinRecParts env ds)
          (Decl.twinPeerRename (Decl.mkTwinRecParts env ds)) ∧
        TwinLoadFacts t E₀ env A c (Decl.mkTwinRecParts env ds)) :
    OverUnitStepTwin.{u} FormerOpenTraceAt t (· < g) R₁ envT E₀ A c rb crb := by
  intro env Reg hext hnd hcl hrefs hinst hstoredRb hfresh
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hClc := hcl Ec hRc (some (Binding.valLimit g)) (Binding.carried_valLimit g)
    (Binding.limWithin_below t g)
  obtain ⟨ds, hreads, hF, hLd⟩ :=
    hparts env hext hnd hClc.prefixInv hrefs hinst hstoredRb hfresh
  -- Assemble the parts list `ws` and declared block `blk` opaquely
  have hmodel : ∀ w ∈ Decl.mkTwinRecParts env ds, ∀ cvm mval hint,
      env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint) →
        w.model? = some (cvm, mval, hint) := by
    intro w hw cvm mval hint h
    unfold Decl.mkTwinRecParts at hw
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hw
    exact Decl.lookupModelInfo?_eq_some.mpr h
  have hblock : ds.map (fun d => ConstantInfo.recInfo d.cvW d.mI d.rP d.rulesW) =
      (Decl.mkTwinRecParts env ds).map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW) := by
    unfold Decl.mkTwinRecParts
    simp only [List.map_map]
    rfl
  obtain ⟨ws, hws⟩ : ∃ ws, ws = Decl.mkTwinRecParts env ds := ⟨_, rfl⟩
  rw [← hws] at hF hLd hmodel hblock
  obtain ⟨blk, hb⟩ : ∃ blk, blk = ds.map (fun d => ConstantInfo.recInfo d.cvW d.mI d.rP d.rulesW) :=
    ⟨_, rfl⟩
  rw [← hb] at hreads hblock
  -- Name distinctness, freshness, and non-emptiness
  have hkeyOf : ∀ w ∈ ws, ∃ x, ConstAddrOf A c x ∧ w.cvW.name = keyOf t x := by
    intro w hw
    have hci : ConstantInfo.recInfo w.cvW w.mI w.rP w.rulesW ∈ blk := by
      rw [hblock]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    obtain ⟨x, hx, hn, -⟩ := hreads.2.1 _ hci
    exact ⟨x, hx, hn⟩
  have hname_eq : ∀ w ∈ ws, w.cvW'.name = w.cvW.name := fun w hw => (hF.front w hw).name_eq
  have hndW : (ws.map (·.cvW.name)).Nodup := by
    have h := hreads.1
    rw [hblock, List.map_map] at h
    exact h
  have hnames : ((twinRecs ws ++ twinModels ws).map (·.name)).Nodup :=
    Decl.twinRecs_append_twinModels_nodup hndW hname_eq fun w hw k tk h => by
      obtain ⟨x, -, hn⟩ := hkeyOf w hw
      exact keyOf_nonAux t x k tk (hn.symm.trans h)
  have hfresh₂ : ∀ ci ∈ twinRecs ws ++ twinModels ws, env.find? ci.name = none :=
    Decl.twinRecs_append_twinModels_fresh hname_eq
      (fun w hw => by
        obtain ⟨x, hx, hn⟩ := hkeyOf w hw
        rw [hn]
        exact hfresh x hx)
      (fun w hw _ => by
        obtain ⟨x, hx, hn⟩ := hkeyOf w hw
        rw [hn]
        apply hClc.auxRoot.fresh_of_base_none
        show env.find? (keyOf t x).base = none
        rw [keyOf_base]
        exact hfresh x hx)
  have hblk : blk ≠ [] := by
    obtain ⟨m, hm⟩ : ∃ m, rs'[0]? = some m := ⟨rs'[0], by simp [Nat.pos_of_ne_zero hszA]⟩
    obtain ⟨ci, hci, -⟩ := hreads.2.2 _ (Or.inr ⟨rs', 0, m, hA.muts, hm, Or.inl rfl⟩)
    exact List.ne_nil_of_mem hci
  -- Helper: each checked twin recursor reloads at any record store `E` for `R₁`
  have hrelAt : ∀ (E : Ixon.Env), RecordsFor R₁ E →
      ∀ w ∈ ws, Decl.ReloadsAs E t ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩
        (.recInfo w.cvW' w.mI w.rP w.rulesW') := by
    intro E hE
    refine twinMember_reloads_at ht (Binding.blob_of_recordsFor hE hblobs)
      (Binding.recordOf_of_recordsFor hE hc₁)
      (fun i m hm => Binding.recordOf_of_recordsFor hE (hcl₁.2 A c rs' hc₁ hA.muts i m hm).1)
      hA hreads hblock hF.front hLd
      (fun k hk => find_isSome_append (find_isSome_append hk (twinModels ws)) (twinRecs ws))
      fun ci hci => ?_
    rw [hblock] at hci
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hci
    have hmem : ConstantInfo.recInfo w.cvW' w.mI w.rP w.rulesW' ∈
        twinRecs ws ++ (twinModels ws ++ env.consts) :=
      List.mem_append_left _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
    have h := find_isSome_of_mem (env := ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩) hmem
    have hn : (ConstantInfo.recInfo w.cvW' w.mI w.rP w.rulesW').name =
        (ConstantInfo.recInfo w.cvW w.mI w.rP w.rulesW).name := (hF.front w hw).name_eq
    rw [hn] at h
    exact h
  -- Helper: each checked twin recursor is non-K at any record store `E` for `R₁`
  have hnoKAt : ∀ (E : Ixon.Env), RecordsFor R₁ E →
      ∀ w ∈ ws, Core.RecNotKAt E w.cvW'.name := fun E hE =>
    twinRecs_recNotKAt_at (Binding.recordOf_of_recordsFor hE hc₁)
      (fun i m hm => Binding.recordOf_of_recordsFor hE (hcl₁.2 A c rs' hc₁ hA.muts i m hm).1)
      hA hreads hblock hF.front hLd
  -- Build IxC's twin step record directly on `ws`, matching `twinTarget_of_facts`
  have hmod : ∀ w ∈ ws, ∃ cvm mval hint,
      env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint) ∧
        w.model? = some (cvm, mval, hint) := by
    intro w hw
    obtain ⟨x, hx, hk, -⟩ := hF.canonAt w hw
    obtain ⟨-, cvm, mval, hint, hf⟩ := hinst x hx
    rw [← hk] at hf
    exact ⟨cvm, mval, hint, hf, hmodel w hw cvm mval hint hf⟩
  have hgen : ∀ w ∈ ws, TwinTypeGen twinPosRulesJ env w.cvC w.cvW' ∧
      List.Forall₂ (fun (rW' rC : RecRule .anon) =>
        TwinRuleGen twinPosRulesJ env (Decl.twinPeerRename ws) w.cvC.levelParams w.cvW' rC rW')
        w.rulesW' w.rulesC := by
    intro w hw
    obtain ⟨-, -, -, hcmp⟩ := hF.canonAt w hw
    rcases hcmp.form with ⟨hty, hrl⟩ | ⟨hty, hrl⟩ | ⟨hty, hrl⟩
    · exact ⟨twinTypeGen_of_canonical_above hty,
        lforall₂_imp (fun rW' rC h => twinRuleGen_of_canonical_above h) hrl⟩
    · exact ⟨twinTypeGen_of_twin_above (Decl.judgeFrames_twinPosRulesJ env) (hF.front w hw)
        (hF.lvls w hw) hty, hrl⟩
    · obtain ⟨tyG, hWC, hWW', hSym⟩ := hty
      exact ⟨twinTypeGen_of_symWrapT hWC hWW' hSym,
        lforall₂_imp (fun rW' rC ⟨_, hRC, hRW, hm⟩ => twinRuleGen_of_match hRC hRW hm) hrl⟩
  have hfind : ∀ ci ∈ twinRecs ws ++ twinModels ws,
      (⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ : Ix.Kernel.Env .anon).find? ci.name =
        some ci := by
    intro ci hci
    have h := Ix.Kernel.Semantics.find?_mem_of_nodup (rest := env.consts) hnames hci
    rw [List.append_assoc] at h
    exact h
  have hrun : DeclRecTwinRunJ twinPosRulesJ env blk
      ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ := by
    have hne : ws ≠ [] := fun h => hblk (by rw [hblock, h, List.map_nil])
    refine ⟨ws, Decl.twinPeerRename ws, hne, hblock, rfl, hnames, hfresh₂,
      Decl.twinPeerRename_spec ws, fun w hw => ?_⟩
    obtain ⟨cvm, mval, hint, hfm, hm⟩ := hmod w hw
    obtain ⟨hty, hrl⟩ := hgen w hw
    have hz := forall₂_zip_and (hF.rulesLen w hw) (hF.rules w hw) hrl
    refine ⟨hF.front w hw, hF.letFree w hw, hF.canonical w hw, hF.lvls w hw, ?_,
      hty, hF.rulesLen w hw, forall₂_imp hz fun p rC h => twinRuleJ_of_front h.1 h.2⟩
    rw [hm]
    exact hfm
  have hstored : ∀ ci ∈ blk, ∃ c',
      (⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ : Ix.Kernel.Env .anon).find? ci.name =
        some c' ∧ StoredAs c' ci := by
    intro ci hci
    rw [hblock] at hci
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hci
    obtain ⟨hvs, hrs⟩ := hF.stored w hw
    refine ⟨.recInfo w.cvW' w.mI w.rP w.rulesW', ?_, hvs, rfl, rfl, hrs⟩
    have h := hfind _ (List.mem_append_left _ (List.mem_map.mpr ⟨w, hw, rfl⟩))
    show (⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ : Ix.Kernel.Env .anon).find? w.cvW.name =
      some (.recInfo w.cvW' w.mI w.rP w.rulesW')
    rw [← (hF.front w hw).name_eq]
    exact h
  have henv₂_app : (⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ : Ix.Kernel.Env .anon) =
      ⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ :=
    congrArg Ix.Kernel.Env.mk (List.append_assoc _ _ _).symm
  have hrun_app : DeclRecTwinRunJ twinPosRulesJ env blk
      ⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ := henv₂_app ▸ hrun
  have hAr_app : Ix.Kernel.Model.StoreArR ⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ :=
    twinKeepsStoreAr env _ blk hrun_app hClc.storeArR
  have hkeys : ∀ ci ∈ blk, ∃ x : _root_.Address, ci.name = keyOf t x ∧ x.hash.size = 32 := by
    intro ci hci
    obtain ⟨x, hx, hn, -⟩ := hreads.2.1 ci hci
    exact ⟨x, hn, constAddr_hash_size_of_block hA.muts hx⟩
  have hpart : ∀ w ∈ ws, TwinCompanionFacts env w := by
    intro w hw
    obtain ⟨-, -, -, hcmp⟩ := hF.canonAt w hw
    have hrc : List.Forall₂ (fun rW' rC : RecRule .anon => rW'.ctor = rC.ctor ∧ rW'.fire = rC.fire)
        w.rulesW' w.rulesC :=
      forall₂_zip_right (hF.rulesLen w hw) (hF.rules w hw) fun p rC h => by
        obtain ⟨-, -, -, -, -, -, -, -, h9, -, -, h12, -⟩ := h
        exact ⟨h9, h12⟩
    exact ⟨hF.canonical w hw, hrc, hcmp.major⟩
  have hext_ws : Ix.Kernel.EnvExt env ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ :=
    Ix.Kernel.Semantics.declRecTwinRunJ_envExt hrun
  have hrecName : ∀ ci ∈ twinRecs ws, ∃ ci₀ ∈ blk, ci₀.name = ci.name := by
    intro ci hci
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hci
    exact ⟨.recInfo w.cvW w.mI w.rP w.rulesW,
      by rw [hblock]; exact List.mem_map.mpr ⟨w, hw, rfl⟩,
      (hF.front w hw).name_eq.symm⟩
  have hmodName : ∀ ci ∈ twinModels ws, ∃ w ∈ ws, ci.name = Ix.Kernel.auxKey w.cvW.name .model := by
    intro ci hci
    obtain ⟨w, hw, hmi⟩ := List.mem_filterMap.mp hci
    unfold TwinRecPart.modelInfo? at hmi
    obtain ⟨⟨cvm, mval, hint⟩, -, rfl⟩ := Option.map_eq_some_iff.mp hmi
    exact ⟨w, hw, rfl⟩
  refine ⟨twinRecs ws ++ twinModels ws, Reg, hnames, hfresh₂, ?_, ?_, ?_, ?_⟩
  · -- 1. `FoldClauseWith` at every record store `E` for `R₁` and every carried limit
    intro E hE lim hcar hlim
    have hCE := hcl E hE lim hcar hlim
    have hcomp_ws : Decl.CoreCompanions ⟨E, ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩, t, lim⟩ :=
      coreCompanions_twin (c := ⟨E, env, t, lim⟩) hCE.companions hext_ws hpart (hnoKAt E hE)
    have hcomp_app : Decl.CoreCompanions ⟨E, ⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩, t, lim⟩ := by
      simpa only [List.append_assoc] using hcomp_ws
    have hrel_app : ∀ ci,
        (⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some ci →
        env.find? ci.name = none → ∀ x, ci.name = keyOf t x →
        Decl.ReloadsAs E t ⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ ci := by
      intro ci hci hnone x hx
      have hmem : ci ∈ (twinRecs ws ++ twinModels ws) ++ env.consts :=
        Ix.Kernel.Semantics.Env.find?_mem hci
      rcases List.mem_append.mp hmem with hnew | henv
      · rcases List.mem_append.mp hnew with hr | hm
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
          simpa only [List.append_assoc] using hrelAt E hE w hw
        · obtain ⟨w, -, hname⟩ := hmodName ci hm
          exact (keyOf_nonAux t x w.cvW.name .model (hx.symm.trans hname)).elim
      · have hs := find_isSome_of_mem henv
        rw [hnone] at hs
        cases hs
    exact foldClauseWith_twinStep linkLaws_formerOpenTrace hCE hrun_app hkeys hAr_app hcomp_app hrel_app
  · -- 2. No constant under an operation key
    intro ci hci
    rcases List.mem_append.mp hci with hr | hm
    · obtain ⟨ci₀, hci₀, he⟩ := hrecName ci hr
      obtain ⟨x, hx, hn, -⟩ := hreads.2.1 ci₀ hci₀
      rw [← he, hn]
      exact Binding.not_mem_opNames_of_keyFree (hkeyA x hx)
    · obtain ⟨w, -, hname⟩ := hmodName ci hm
      rw [hname]
      intro hop
      have hb := RoleOps.isBaseKey_of_mem_opNames hop
      exact nomatch hb
  · -- 3. Each constant address of `A` stored in `new` as its reading
    intro x hx
    obtain ⟨ci₀, hci₀, hn₀⟩ := hreads.2.2 x hx
    obtain ⟨x', hx', hn', hrd⟩ := hreads.2.1 ci₀ hci₀
    have hxx : x' = x := keyOf_inj hroles (hn'.symm.trans hn₀)
    rw [hxx] at hrd
    obtain ⟨c', hc', hsa⟩ := hstored ci₀ hci₀
    rw [henv₂_app] at hc'
    rcases find?_append_cases (twinRecs ws ++ twinModels ws) hc' with hm | hold
    · refine ⟨c', hm, ci₀, ?_, hrd, hsa⟩
      rw [Core.WhnfAux.name_of_find hc', hn₀]
    · rw [hn₀, hfresh x hx] at hold
      cases hold
  · -- 4. Each new constant is at a constant address's key or a derived key
    intro ci hci
    rcases List.mem_append.mp hci with hr | hm
    · obtain ⟨ci₀, hci₀, he⟩ := hrecName ci hr
      obtain ⟨x, hx, hn, -⟩ := hreads.2.1 ci₀ hci₀
      exact Or.inl ⟨x, hx, he.symm.trans hn⟩
    · obtain ⟨w, -, hname⟩ := hmodName ci hm
      exact Or.inr ⟨w.cvW.name, .model, hname⟩

/-! ## `ClosureTwinSteps` producer -/

/-- **Per-context binding closure twin step**, parameterized by per-call flattened-family and
reconstruction facts over records held in `R₁`. -/
theorem closureTwinSteps_at
    (hStoredLvls : StoredRecLvlsOk)
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun} {Rs : Nat → Ixon.Env}
    (hrun : BindingRun calls t ρ Rs) (hall : AllBound t) (ht : t.check = .ok ())
    {g : Nat} (hg6 : 6 ≤ g) (hg : g < 77)
    {R R' R₁ : Ixon.Env} {env₀ : Ix.Kernel.Env .anon}
    {famOf₀ famOf : _root_.Address → Option _root_.Address}
    {adv cont : _root_.Address → _root_.Address → Prop} {bAddr A : _root_.Address}
    {c : Ixon.Constant}
    (hC : ClosureCtx.{u} FormerOpenTraceAt calls ρ t g R R' R₁ env₀ famOf₀ famOf adv cont bAddr)
    (hnA : Binding.New R R₁ A) (hc₁ : recordOf R₁ A = some c) (htw : IsTwinShape c)
    (hfamA : famOf A = none) (huncA : ∀ B, famOf B ≠ some A)
    (hFlatAt : ∀ (B r : _root_.Address) (cr : Ixon.Constant)
        (rs : Array Ixon.MutConst) (cs : List (Call F)),
      Binding.FamilyFlat.Held R₁ B → Binding.FamilyFlat.Held R₁ r →
      FamRecRecord ρ.E₀ r cr rs → rs.size ≠ 0 →
      (∀ cb, recordOf ρ.E₀ B = some cb → InLogic cb) →
      FamilyCallAtLim calls bAddr t B r (some (Binding.valLimit g)) cs →
      ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (es : List FlatEntry) (off : Nat),
        FamilyOfBlock ρ.E₀ B cb ms r cr rs (es.map FlatEntry.addr) ∧
        RecordFlat t ρ.E₀ r cr rs es ∧ BlockDerivedFlat t ρ.E₀ B off es ∧
        ∀ (ind₀ : Ixon.Inductive) (k : Nat) (rc : Ixon.Recursor),
          ms[0]? = some (.indc ind₀) → rs[k]? = some (.recr rc) →
          rc.lvls.toNat = ind₀.lvls.toNat + off)
    (hReconAt : ∀ (B r : _root_.Address) (cb cr : Ixon.Constant)
        (ms rs : Array Ixon.MutConst) (cs : List (Call F)),
      Binding.FamilyFlat.Held R₁ B → Binding.FamilyFlat.Held R₁ r →
      FamBlockRecord ρ.E₀ B cb ms → FamRecRecord ρ.E₀ r cr rs → rs.size ≠ 0 →
      FamilyCallAtLim calls bAddr t B r (some (Binding.valLimit g)) cs →
      RFormS t ρ.E₀ B r ∨ RecordWrapConsObs calls t ρ.E₀ B r) :
    ∃ (B rb : _root_.Address) (crb : Ixon.Constant), recordOf R₁ rb = some crb ∧
      (famOf₀ B = some rb ∨ (famOf B = some rb ∧ ρ.rank g B < ρ.rank g A)) ∧
      ∀ envT : Ix.Kernel.Env .anon, (∀ ci ∈ env₀.consts, ci ∈ envT.consts) →
        (envT.consts.map (·.name)).Nodup → (∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x) →
        OverUnitStepTwin.{u} FormerOpenTraceAt t (· < g) R₁ envT ρ.E₀ A c rb crb := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  have hRS : LoadedReads.RunStore calls ρ.E₀ := hrun.runStore
  have hH : LoadedReads.HashedRecordsStored calls ρ.E₀ := hrun.hashedStored
  -- Store monotonicity helpers
  have hloaded : ∀ a lr, R₁.consts.get? a = some lr → ρ.E₀.consts.get? a = some lr :=
    fun a lr h => hC.admits.loaded a lr (hC.store.le₂.1 a lr h)
  have hblobs : ∀ x b, ρ.E₀.blobs.get? x = some b → R₁.blobs.get? x = some b :=
    fun x b h => hC.store.blobs x b (hC.reads.blobs x b h)
  have hR_R₁_rec : ∀ a d, recordOf R a = some d → recordOf R₁ a = some d :=
    fun _ _ h => Binding.recordOf_of_loaded hC.store.le₁.1 h
  have hR_E₀_rec : ∀ a d, recordOf R a = some d → recordOf ρ.E₀ a = some d :=
    fun _ _ h => Binding.recordOf_of_loaded hloaded (hR_R₁_rec _ _ h)
  have hR_E₀_blob : ∀ y b, R.blobs.get? y = some b → ρ.E₀.blobs.get? y = some b :=
    fun y b h => hC.admits.loadedBlobs y b (hC.store.le₂.2 y b (hC.store.le₁.2 y b h))
  have hc' : recordOf R' A = some c := Binding.recordOf_of_loaded hC.store.le₂.1 hc₁
  have hc₀ : recordOf ρ.E₀ A = some c := Binding.recordOf_of_loaded hloaded hc₁
  have hnA' : Binding.New R R' A := ⟨by rw [hc']; rfl, hnA.2⟩
  -- Step store `Ec` for `R₁` (and hence also for `R`)
  have hzc : R₁.consts.get? Ix.HostAdmission.Merkle.padding = none := by
    cases h : R₁.consts.get? Ix.HostAdmission.Merkle.padding with
    | none => rfl
    | some lc =>
      have h' := hC.store.le₂.1 _ lc h
      rw [hC.admits.zeroFree.1] at h'
      cases h'
  have hzb : R₁.blobs.get? Ix.HostAdmission.Merkle.padding = none := by
    cases h : R₁.blobs.get? Ix.HostAdmission.Merkle.padding with
    | none => rfl
    | some b =>
      have h' := hC.store.le₂.2 _ b h
      rw [hC.admits.zeroFree.2] at h'
      cases h'
  obtain ⟨Ec, hRc, hst⟩ := hrun.stepStores R₁ hloaded
    (fun a b h => hC.admits.loadedBlobs a b (hC.store.le₂.2 a b h))
    (fun p hp lc h => hC.admits.committed p hp lc (hC.store.le₂.1 _ lc h)) ⟨hzc, hzb⟩
  have hRc_R : RecordsFor R Ec :=
    ⟨hRc.1, fun a d hd => hRc.2.1 a d (hR_R₁_rec a d hd),
      fun y b hb => hRc.2.2.1 y b (hC.store.le₁.2 y b hb), hRc.2.2.2⟩
  have hcanon₀ : L1.CanonicalHashCoverage ρ.E₀ calls := by
    intro bytes value hashed size exactRead
    obtain ⟨entry, stored, bytesEq, cached⟩ := hH bytes value hashed size
      (L1.deConstant_of_deConstantExact exactRead) exactRead
    refine ⟨⟨entry, value, stored, cached, ?_⟩, rfl⟩
    rw [bytesEq]
    exact exactRead
  have hcanon : L1.CanonicalHashCoverage Ec calls :=
    Assembly.canonicalHashCoverage_frame hcanon₀ hst.decoded
      (fun a v h => hst.runRecord a v ((hRS.recordOf_eq_recordAt a).trans h))
  -- Build `FamRecRecord ρ.E₀ A c rs'`
  obtain ⟨rs', hmutsA, hposA, hrecrsA⟩ := htw
  have hszA : rs'.size ≠ 0 := Nat.ne_of_gt hposA
  have hA : FamRecRecord ρ.E₀ A c rs' :=
    { record := hc₀
      muts := hmutsA
      recrs := hrecrsA
      logic := hC.admits.logic A c hnA' hc'
      members := fun i m hm =>
        Binding.recordOf_of_loaded hloaded (hC.closed.2 A c rs' hc₁ hmutsA i m hm).1 }
  -- Unclaimed twin-shaped block `A` has a `FamilyCallAtLim` on some block `B`
  have hclaim := hC.checks.claimed A c rs' hnA' hc₀ hmutsA hposA hrecrsA
  obtain ⟨B, cs_A, hcall_A⟩ : ∃ B cs_A,
      FamilyCallAtLim calls bAddr t B A (some (Binding.valLimit g)) cs_A := by
    rcases hclaim with ⟨B', hB'⟩ | h
    · exact (huncA B' hB').elim
    · exact h
  -- Extract `B`, its member 0 projection, and `UsedRef ρ.E₀ A (Core.iprjAddr B 0)`
  obtain ⟨cb₀, ms₀, ind₀, hcb₀, hms₀, hms0, hP0₀, hused_B0⟩ :=
    familyCall_usedRef_ind0 ht hRS hH hst hA hszA hcall_A
  -- `Core.iprjAddr B 0` and its owner `B` are both held in `R₁`
  have hP0₁ : recordOf R₁ (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind₀)) := by
    obtain ⟨c', i, hc', hi, href⟩ := hused_B0
    have ec' : c' = c := Option.some.inj (hc'.symm.trans hc₀)
    subst c'
    obtain ⟨P0, hP0⟩ := Option.isSome_iff_exists.mp ((hC.closed.1 A c hc₁).2 i hi _ href)
    have eP0 : P0 = memberProjection B 0 (.indc ind₀) :=
      Option.some.inj ((Binding.recordOf_of_loaded hloaded hP0).symm.trans hP0₀)
    rwa [eP0] at hP0
  have hcb₁ : recordOf R₁ B = some cb₀ := by
    have hown0 : Ix.Cert.ownerOf (Core.iprjAddr B 0) (memberProjection B 0 (.indc ind₀)) = B := rfl
    obtain ⟨cb₁, hcb₁⟩ := Option.isSome_iff_exists.mp (hown0 ▸ (hC.closed.1 _ _ hP0₁).1)
    have ecb : cb₁ = cb₀ :=
      Option.some.inj ((Binding.recordOf_of_loaded hloaded hcb₁).symm.trans hcb₀)
    rwa [ecb] at hcb₁
  -- `Route.blockRoute R₁ B = some true`, from `hrun.famCallsModeled` at `Ec`
  have hrouteR₁ : Route.blockRoute R₁ B = some true := by
    obtain ⟨h_cf, _, rc_cf, xb_cf, xrb_cf, _, -, ⟨bB, hrep_cf, hix_cf⟩, -, -, hmem_cf, -⟩ := hcall_A
    obtain ⟨r_mod, m_mod, m_mod', cs_mod, ev_mod, hne0, hrep_mod, hsub_mod⟩ :=
      hrun.famCallsModeled rc_cf xb_cf xrb_cf h_cf bB hmem_cf hrep_cf
    have g_mod : Core.Good ⟨Ec, Ix.Kernel.Env.empty, t, none⟩ cs_mod :=
      (hst.good Ix.Kernel.Env.empty none).sub hsub_mod
    have hag := Route.block_is_modeled_agrees (E := Ec) g_mod.1 g_mod.2 hrep_mod ev_mod
    obtain ⟨v, hv⟩ := hag.known (canonicalHashCoverage_sub hsub_mod hcanon)
    have hrv := hag.value v hv
    have hrouteEc : Route.blockRoute Ec B = some true := by
      rw [← hix_cf]
      cases v with
      | false => exact absurd (hrv.trans Route.bit_false) hne0
      | true => exact hv
    exact (Binding.blockRoute_of_recordsFor hC.closed hRc hcb₁).symm.trans hrouteEc
  -- Reference safety for `A` from `family_refs_ok`
  have hrefs_ok_A := recRefs_of_familyCall hRS hH hc₀ hcall_A
  -- Split on whether `B` was held before group `g` (`R`) or new in group `g`
  cases hRB : recordOf R B with
  | some cb_R =>
    -- **Arm 1: Pre-group stored block (`recordOf R B = some cb_R`)**
    have ecbR : cb_R = cb₀ := Option.some.inj ((hR_R₁_rec _ _ hRB).symm.trans hcb₁)
    subst cb_R
    -- `B` routes as modeled over `R` too (since `R` is `UsedClosed` and `R ⊆ R₁`)
    have hrouteR : Route.blockRoute R B = some true := by
      have hcongr : Route.blockRoute R₁ B = Route.blockRoute R B := by
        refine Binding.blockRoute_congr hRB hcb₁ fun a ha => ?_
        have hRa : (recordOf R a).isSome = true := by
          rcases ha with ⟨i, hi, hx⟩ | ⟨ms', i, m, hms', hm, hx⟩
          · exact (hC.bnd.shape.usedClosed.1 B cb₀ hRB).2 i hi a hx
          · rw [hx]
            exact Option.isSome_iff_exists.mpr
              ⟨_, (hC.bnd.shape.usedClosed.2 B cb₀ ms' hRB hms' i m hm).1⟩
        obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp hRa
        unfold Route.isIndAt
        rw [hR_R₁_rec a ca hca, hca]
      exact hcongr.symm.trans hrouteR₁
    -- Every constant address of `B` is stored in `env₀` (via `RecordsStored`)
    have hB_stored : ∀ x, ConstAddrOf B cb₀ x → StoredAt t env₀ x := by
      intro x hx
      rcases Binding.constAddr_record hC.bnd.shape.usedClosed hRB hx with ⟨-, hs⟩ | ⟨-, P, hP, hPp, -⟩
      · exact (standalone_not_block hs ⟨ms₀, hms₀⟩).elim
      · have hnotMuts : ∀ ms', P.info ≠ .muts ms' := by
          intro ms' hmut
          rcases hPp with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> (rw [h] at hmut; cases hmut)
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hC.stored x P hP hnotMuts)
        exact storedAt_of_find hci
    -- Selected family record `famOf₀ B = some rb` from `StoredFamilies`
    obtain ⟨rb, hfam₀⟩ := hC.fams.selected B cb₀ hRB hrouteR hB_stored
    obtain ⟨cb_f, crb, ms_f, rs, es, off, hFOB_R, hRF_R, hBD_R⟩ := hC.fams.flat B rb hfam₀
    have ecb_f : cb_f = cb₀ := Option.some.inj (hFOB_R.block.record.symm.trans hRB)
    subst cb_f
    have ems_f : ms_f = ms₀ := Ixon.ConstantInfo.muts.inj (hFOB_R.block.muts.symm.trans hms₀)
    subst ms_f
    have hcrb₁ : recordOf R₁ rb = some crb := hR_R₁_rec rb crb hFOB_R.record.record
    have hcrb₀ : recordOf ρ.E₀ rb = some crb := Binding.recordOf_of_loaded hloaded hcrb₁
    have hRForm_rb_E₀ : RFormS t ρ.E₀ B rb :=
      (hC.fams.form B rb hfam₀).grow hR_E₀_rec hR_E₀_blob
    have hrecs_R : StoredFamilyRecs t R env₀ B cb₀ rb crb :=
      hC.fams.recs B rb cb₀ crb hfam₀ hRB hFOB_R.record.record
    have hlogicB : ∀ cb', recordOf ρ.E₀ B = some cb' → InLogic cb' := by
      intro cb' hcb'
      have e : cb' = cb₀ := Option.some.inj (hcb'.symm.trans hcb₀)
      rw [e]; exact hFOB_R.block.logic
    -- Flattened family & recon for `A` over `ρ.E₀`
    have hR₁B : Binding.FamilyFlat.Held R₁ B := Option.isSome_iff_exists.mpr ⟨cb₀, hcb₁⟩
    have hR₁A : Binding.FamilyFlat.Held R₁ A := Option.isSome_iff_exists.mpr ⟨c, hc₁⟩
    obtain ⟨cb_A, ms_A, es_A, off_A, hFOB_A, hRF_A, hBD_A, hlvls_A⟩ :=
      hFlatAt B A c rs' cs_A hR₁B hR₁A hA hszA hlogicB hcall_A
    have ecb_A : cb_A = cb₀ := Option.some.inj (hFOB_A.block.record.symm.trans hcb₀)
    subst cb_A
    have ems_A : ms_A = ms₀ := Ixon.ConstantInfo.muts.inj (hFOB_A.block.muts.symm.trans hms₀)
    subst ms_A
    obtain ⟨hoff_eq, hes_eq⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
      (fun a c1 c2 h1 h2 => Option.some.inj (h1.symm.trans (hR_E₀_rec a c2 h2)))
      (fun y b1 b2 h1 h2 => Option.some.inj (h1.symm.trans (hR_E₀_blob y b2 h2)))
      hBD_A hBD_R
    subst off_A es_A
    have hes_len_rb : es.length = rs.size := by
      simpa only [List.length_map] using hFOB_R.covers
    have hes_len_A : es.length = rs'.size := by
      simpa only [List.length_map] using hFOB_A.covers
    have hrs_len : rs.size = rs'.size := hes_len_rb.symm.trans hes_len_A
    have hBD_E₀ : BlockDerivedFlat t ρ.E₀ B off es :=
      Binding.FamilyFlat.blockDerivedFlat_grow hR_E₀_rec hR_E₀_blob hBD_R
    have hRF_rb_E₀ : RecordFlat t ρ.E₀ rb crb rs es := hRF_R.of_blobs hR_E₀_blob
    -- Extract members for `A`
    obtain ⟨ind₀', hms0', hextract_A⟩ := familyCall_extract_members ht hRS hH hC.bnd.shape
      hRc_R hst (Binding.limWithin_below t g) hFOB_A.block hA hcall_A
    have eind0 : ind₀' = ind₀ := Ixon.MutConst.indc.inj (Option.some.inj (hms0'.symm.trans hms0))
    subst ind₀'
    -- Unpack `fuel` on `ρ.E₀` for `rb` (`RFormS`) and `A` (`RFormS ∨ RecordWrapConsObs`)
    have hrec_A := hReconAt B A cb₀ c ms₀ rs' cs_A hR₁B hR₁A hFOB_A.block hA hszA hcall_A
    have hMR_pair : ∃ fuel : Nat,
        (∀ k rc, rs[k]? = some (.recr rc) →
          MemberRecon Core.ExprLvEq t ρ.E₀ rb crb rs es off fuel k rc) ∧
        (∀ k rc, rs'[k]? = some (.recr rc) →
          MemberRecon Core.ExprLvEq t ρ.E₀ A c rs' es off fuel k rc ∨
          MemberRecon (fun ty R => WrapConsObs (Binding.FamilyRecon.wrapAt t ρ.E₀)
            (WrapperObserved calls t) R ty) t ρ.E₀ A c rs' es off fuel k rc) := by
      obtain ⟨crb', rs_r, es_r, off_r, f_rb, hrb', hrs_r, -, hBD_r, hM_rb⟩ := hRForm_rb_E₀
      have ecrb' : crb' = crb := Option.some.inj (hrb'.symm.trans hcrb₀)
      subst crb'
      have ers_r : rs_r = rs := Ixon.ConstantInfo.muts.inj (hrs_r.symm.trans hFOB_R.record.muts)
      subst rs_r
      obtain ⟨ho_r, he_r⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
        (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
        (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD_r hBD_E₀
      subst off_r es_r
      rcases hrec_A with hA_eq | hA_obs
      · obtain ⟨c', rsA', esA', offA', f_A, hc', hrsA', -, hBD_A', hM_A⟩ := hA_eq
        have ec' : c' = c := Option.some.inj (hc'.symm.trans hc₀)
        subst c'
        have ersA' : rsA' = rs' := Ixon.ConstantInfo.muts.inj (hrsA'.symm.trans hA.muts)
        subst rsA'
        obtain ⟨ho_A, he_A⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD_A' hBD_E₀
        subst offA' esA'
        exact ⟨max f_rb f_A,
          fun k rc hr => Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_left _ _) (hM_rb k rc hr),
          fun k rc hr => Or.inl (Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_right _ _) (hM_A k rc hr))⟩
      · obtain ⟨c', rsA', esA', offA', f_A, hc', hrsA', -, hBD_A', hM_A⟩ := hA_obs
        have ec' : c' = c := Option.some.inj (hc'.symm.trans hc₀)
        subst c'
        have ersA' : rsA' = rs' := Ixon.ConstantInfo.muts.inj (hrsA'.symm.trans hA.muts)
        subst rsA'
        obtain ⟨ho_A, he_A⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD_A' hBD_E₀
        subst offA' esA'
        exact ⟨max f_rb f_A,
          fun k rc hr => Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_left _ _) (hM_rb k rc hr),
          fun k rc hr => Or.inr (Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_right _ _) (hM_A k rc hr).2)⟩
    obtain ⟨fuel, hM_rb_E₀, hMR_A_all⟩ := hMR_pair
    refine ⟨B, rb, crb, hcrb₁, Or.inl hfam₀, fun envT hextT hndT hfrT => ?_⟩
    have hkeyA : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x) :=
      fun x hx => Binding.plain_keyFree hC ht hg6 hextT hnA' hc₁ hx (hfrT x hx)
    refine overUnitStepTwin_of_parts ht hblobs hC.closed hc₁ hRc hA hszA hkeyA ?_
    intro env hext hnd hinv hrefs _ _ hfresh
    have husedA : ∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
        (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x := by
      intro i hi x hx
      have hux : UsedRef ρ.E₀ A x := ⟨c, i, hc₀, hi, by rwa [← Array.getElem?_toList]⟩
      rcases hrefs_ok_A x hux with hcov | hneed
      · obtain ⟨ci, hci, hn⟩ := coveredAt_stored hC.bnd.shape htwf
          (fun r hr => Nat.lt_of_lt_of_le (hr _ rfl) (Binding.valLimit_le g)) hcov
        exact Or.inl (find_isSome_of_storedAt ⟨ci, hext ci (hextT ci hci), hn⟩)
      · rcases hrefs x hux with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr h2
        · exact absurd hneed h3
    have hrecs_env : StoredFamilyRecs t R env B cb₀ rb crb :=
      hrecs_R.mono_env (fun ci hci => hext ci (hextT ci hci)) hnd
    let mkC : ∀ k (hk : k < rs'.size),
        CanonMemberAt calls t ρ.E₀ env B rb crb rs es off fuel ind₀ k :=
      fun k hk =>
        Classical.choice (canonMemberAt_of_stored ht hR_E₀_rec hR_E₀_blob hFOB_R hRF_rb_E₀ hms0
          hrecs_env hBD_R hStoredLvls (by omega) (hM_rb_E₀ k))
    have hpair_all :
        (∀ k (hk : k < rs'.size), Core.ExprLvEq (mkC k hk).ty_ld (mkC k hk).R) ∨
        ((∀ k rc, rs'[k]? = some (.recr rc) →
            MemberRecon (fun ty R => WrapConsObs (Binding.FamilyRecon.wrapAt t ρ.E₀)
              (WrapperObserved calls t) R ty) t ρ.E₀ A c rs' es off fuel k rc) ∧
          ∃ S : _root_.Address → Prop,
            (ReconView.ofStore t ρ.E₀).ClosedOn S ∧
            (∀ e ∈ es, Binding.FamilyRecon.REntryAt (ReconView.ofStore t ρ.E₀) S e) ∧
            (∀ j rc, rs[j]? = some (.recr rc) → ¬ S (memberAddr rb j (.recr rc)))) := by
      left
      intro k hk
      have hM_eq := hM_rb_E₀ k (mkC k hk).rc (mkC k hk).hmem
      obtain ⟨ty1, R1, _, _, hty1, hR1, hlv1, -, -, -⟩ := hM_eq
      have hty_e : ty1 = (mkC k hk).ty_ld := Option.some.inj (hty1.symm.trans (mkC k hk).hty_ld)
      have hR_e : R1 = (mkC k hk).R := Option.some.inj (hR1.symm.trans (mkC k hk).hR)
      rwa [hty_e, hR_e] at hlv1
    exact twinParts_of_canon_extracted ht hst hinv (fun _ _ h => h) (fun _ _ h => h)
      hFOB_R.record.muts (fun i m hm => hR_E₀_rec _ _ (hFOB_R.record.members i m hm))
      hFOB_R.record.recrs hA hszA hrs_len hes_len_A hRF_rb_E₀ hRF_A
      mkC hextract_A (fun k rc hr => hlvls_A ind₀ k rc hms0 hr) hMR_A_all hpair_all
      husedA hfresh hkeyA
  | none =>
    -- **Arm 2: Block `B` new in group `g` (`recordOf R B = none`)**
    have hcb' : recordOf R' B = some cb₀ := Binding.recordOf_of_loaded hC.store.le₂.1 hcb₁
    have hnB' : Binding.New R R' B := ⟨by rw [hcb']; rfl, hRB⟩
    -- `B` has a selected family record `famOf B = some rb` via `ClosureRunFacts.routeNew`
    obtain ⟨rb, hfamB⟩ := hC.run.routeNew R₁ B hC.store hnB' hrouteR₁
    -- `ρ.rank g B < ρ.rank g A`, via `A → Core.iprjAddr B 0 → B`
    have hrank : ρ.rank g B < ρ.rank g A := by
      have hused_R' : UsedRef R' A (Core.iprjAddr B 0) :=
        Binding.usedRef₂ hC.admits hc' hused_B0
      have hP0_not_R : (recordOf R (Core.iprjAddr B 0)).isSome ≠ true := by
        intro hsome
        obtain ⟨P_R, hPR⟩ := Option.isSome_iff_exists.mp hsome
        have ePR : P_R = memberProjection B 0 (.indc ind₀) :=
          Option.some.inj ((hR_R₁_rec _ _ hPR).symm.trans hP0₁)
        subst ePR
        have hown0 : Ix.Cert.ownerOf (Core.iprjAddr B 0) (memberProjection B 0 (.indc ind₀)) = B := rfl
        have hB_R := hown0 ▸ (hC.bnd.shape.usedClosed.1 _ _ hPR).1
        rw [hRB] at hB_R
        cases hB_R
      have ⟨hnP0', hrk1⟩ : Binding.New R R' (Core.iprjAddr B 0) ∧
          ρ.rank g (Core.iprjAddr B 0) < ρ.rank g A := by
        rcases hC.admits.rankUsed A (Core.iprjAddr B 0) hnA' hused_R' with h | h
        · exact h
        · exact (hP0_not_R h).elim
      have hP0' : recordOf R' (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind₀)) :=
        Binding.recordOf_of_loaded hC.store.le₂.1 hP0₁
      have hrk2 : ρ.rank g B < ρ.rank g (Core.iprjAddr B 0) := by
        have hown0 : Ix.Cert.ownerOf (Core.iprjAddr B 0) (memberProjection B 0 (.indc ind₀)) = B := rfl
        rcases hC.admits.rankOwner (Core.iprjAddr B 0) (memberProjection B 0 (.indc ind₀))
            hnP0' hP0' (memberProjection_isProj B 0 (.indc ind₀)) with ⟨-, hlt⟩ | hheld
        · rwa [hown0] at hlt
        · rw [hown0, hRB] at hheld
          cases hheld
      exact Nat.lt_trans hrk2 hrk1
    -- `rb` is held in `R₁` (it is a `.muts` block, hence no role unit of group `g`)
    obtain ⟨crb, hcrb', -⟩ := hC.famAdmits.famRecord_held hC.admits.usedClosed hfamB hnB'
    have hcrb₀ : recordOf ρ.E₀ rb = some crb := Binding.recordOf_of_loaded hC.admits.loaded hcrb'
    obtain ⟨-, -, cs_rb, advAs_rb, hown_rb, -, -⟩ := hC.checks.famCall B rb hfamB
    have hcall_rb : FamilyCallAtLim calls bAddr t B rb (some (Binding.valLimit g)) cs_rb :=
      Binding.FamilyCallOwn.toCall hown_rb
    obtain ⟨cb_f, crb_f, ms_f, rs, es, off, hFOB_rb, hRF_rb, hBD_rb⟩ :=
      hC.checks.familyFlat B rb hfamB
    have ecb_f : cb_f = cb₀ := Option.some.inj (hFOB_rb.block.record.symm.trans hcb₀)
    subst cb_f
    have ems_f : ms_f = ms₀ := Ixon.ConstantInfo.muts.inj (hFOB_rb.block.muts.symm.trans hms₀)
    subst ms_f
    have ecrb_f : crb_f = crb := Option.some.inj (hFOB_rb.record.record.symm.trans hcrb₀)
    subst crb_f
    have hnotRU_rb : ¬ Binding.RoleUnitAt t g rb := by
      intro hru
      have hnrb : Binding.New R R' rb := (hC.famAdmits.famNew B rb hfamB hnB').1
      rcases hC.run.roleUnitForm rb crb hru hnrb hcrb' with ⟨d, hd⟩ | ⟨ax, hax⟩
      · rw [hFOB_rb.record.muts] at hd; cases hd
      · rw [hFOB_rb.record.muts] at hax; cases hax
    have hcrb₁ : recordOf R₁ rb = some crb := by
      rw [Binding.recordOf_closureStore_eq hC.store (Or.inr hnotRU_rb)]
      exact hcrb'
    have hRForm_rb : RFormS t ρ.E₀ B rb := hC.checks.familyForm B rb hfamB
    have hlogicB : ∀ cb', recordOf ρ.E₀ B = some cb' → InLogic cb' := by
      intro cb' hcb'
      have e : cb' = cb₀ := Option.some.inj (hcb'.symm.trans hcb₀)
      rw [e]; exact hFOB_rb.block.logic
    -- Flattened family & level counts for `rb` and `A`
    have hsz_rb : rs.size ≠ 0 := by
      intro h0
      have hcov := hFOB_rb.covers
      rw [h0, List.length_map] at hcov
      have hes0 : es.length = 0 := hcov
      have h0_lt : 0 < ms₀.size := (Array.getElem?_eq_some_iff.mp hms0).1
      have hflat0 := hFOB_rb.originals 0 (.indc ind₀) hms0
      have hlt0 : 0 < (es.map FlatEntry.addr).length := (List.getElem?_eq_some_iff.mp hflat0).1
      rw [List.length_map] at hlt0
      omega
    have hR₁B : Binding.FamilyFlat.Held R₁ B := Option.isSome_iff_exists.mpr ⟨cb₀, hcb₁⟩
    have hR₁rb : Binding.FamilyFlat.Held R₁ rb := Option.isSome_iff_exists.mpr ⟨crb, hcrb₁⟩
    have hR₁A : Binding.FamilyFlat.Held R₁ A := Option.isSome_iff_exists.mpr ⟨c, hc₁⟩
    obtain ⟨cb_rb2, ms_rb2, es_rb2, off_rb2, hFOB_rb2, _, hBD_rb2, hlvls_rb2⟩ :=
      hFlatAt B rb crb rs cs_rb hR₁B hR₁rb hFOB_rb.record hsz_rb hlogicB hcall_rb
    have ecb_rb2 : cb_rb2 = cb₀ := Option.some.inj (hFOB_rb2.block.record.symm.trans hcb₀)
    subst cb_rb2
    have ems_rb2 : ms_rb2 = ms₀ := Ixon.ConstantInfo.muts.inj (hFOB_rb2.block.muts.symm.trans hms₀)
    subst ms_rb2
    obtain ⟨hoff_rb2, hes_rb2⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
      (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
      (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD_rb2 hBD_rb
    subst off_rb2 es_rb2
    obtain ⟨cb_A, ms_A, es_A, off_A, hFOB_A, hRF_A, hBD_A, hlvls_A⟩ :=
      hFlatAt B A c rs' cs_A hR₁B hR₁A hA hszA hlogicB hcall_A
    have ecb_A : cb_A = cb₀ := Option.some.inj (hFOB_A.block.record.symm.trans hcb₀)
    subst cb_A
    have ems_A : ms_A = ms₀ := Ixon.ConstantInfo.muts.inj (hFOB_A.block.muts.symm.trans hms₀)
    subst ms_A
    obtain ⟨hoff_A, hes_A⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
      (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
      (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD_A hBD_rb
    subst off_A es_A
    have hes_len_rb : es.length = rs.size := by
      simpa only [List.length_map] using hFOB_rb.covers
    have hes_len_A : es.length = rs'.size := by
      simpa only [List.length_map] using hFOB_A.covers
    have hrs_len : rs.size = rs'.size := hes_len_rb.symm.trans hes_len_A
    -- Extract members for `rb` and `A`
    obtain ⟨ind₀_rb, hms0_rb, hextract_rb⟩ := familyCall_extract_members ht hRS hH hC.bnd.shape
      hRc_R hst (Binding.limWithin_below t g) hFOB_rb.block hFOB_rb.record hcall_rb
    have eind0_rb : ind₀_rb = ind₀ :=
      Ixon.MutConst.indc.inj (Option.some.inj (hms0_rb.symm.trans hms0))
    subst ind₀_rb
    obtain ⟨ind₀_A, hms0_A, hextract_A⟩ := familyCall_extract_members ht hRS hH hC.bnd.shape
      hRc_R hst (Binding.limWithin_below t g) hFOB_A.block hA hcall_A
    have eind0_A : ind₀_A = ind₀ :=
      Ixon.MutConst.indc.inj (Option.some.inj (hms0_A.symm.trans hms0))
    subst ind₀_A
    -- Unpack `fuel` on `ρ.E₀` for `rb` (`RFormS`) and `A` (`RFormS ∨ RecordWrapConsObs`)
    have hrec_A := hReconAt B A cb₀ c ms₀ rs' cs_A hR₁B hR₁A hFOB_A.block hA hszA hcall_A
    have hMR_pair : ∃ fuel : Nat,
        (∀ k rc, rs[k]? = some (.recr rc) →
          MemberRecon Core.ExprLvEq t ρ.E₀ rb crb rs es off fuel k rc) ∧
        (∀ k rc, rs'[k]? = some (.recr rc) →
          MemberRecon Core.ExprLvEq t ρ.E₀ A c rs' es off fuel k rc ∨
          MemberRecon (fun ty R => WrapConsObs (Binding.FamilyRecon.wrapAt t ρ.E₀)
            (WrapperObserved calls t) R ty) t ρ.E₀ A c rs' es off fuel k rc) := by
      obtain ⟨crb', rs_r, es_r, off_r, f_rb, hrb', hrs_r, -, hBD_r, hM_rb⟩ := hRForm_rb
      have ecrb' : crb' = crb := Option.some.inj (hrb'.symm.trans hcrb₀)
      subst crb'
      have ers_r : rs_r = rs := Ixon.ConstantInfo.muts.inj (hrs_r.symm.trans hFOB_rb.record.muts)
      subst rs_r
      obtain ⟨ho_r, he_r⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
        (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
        (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD_r hBD_rb
      subst off_r es_r
      rcases hrec_A with hA_eq | hA_obs
      · obtain ⟨c', rsA', esA', offA', f_A, hc', hrsA', -, hBD_A', hM_A⟩ := hA_eq
        have ec' : c' = c := Option.some.inj (hc'.symm.trans hc₀)
        subst c'
        have ersA' : rsA' = rs' := Ixon.ConstantInfo.muts.inj (hrsA'.symm.trans hA.muts)
        subst rsA'
        obtain ⟨ho_A, he_A⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD_A' hBD_rb
        subst offA' esA'
        exact ⟨max f_rb f_A,
          fun k rc hr => Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_left _ _) (hM_rb k rc hr),
          fun k rc hr => Or.inl (Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_right _ _) (hM_A k rc hr))⟩
      · obtain ⟨c', rsA', esA', offA', f_A, hc', hrsA', -, hBD_A', hM_A⟩ := hA_obs
        have ec' : c' = c := Option.some.inj (hc'.symm.trans hc₀)
        subst c'
        have ersA' : rsA' = rs' := Ixon.ConstantInfo.muts.inj (hrsA'.symm.trans hA.muts)
        subst rsA'
        obtain ⟨ho_A, he_A⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD_A' hBD_rb
        subst offA' esA'
        exact ⟨max f_rb f_A,
          fun k rc hr => Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_left _ _) (hM_rb k rc hr),
          fun k rc hr => Or.inr (Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_right _ _) (hM_A k rc hr).2)⟩
    obtain ⟨fuel, hM_rb_E₀, hMR_A_all⟩ := hMR_pair
    refine ⟨B, rb, crb, hcrb₁, Or.inr ⟨hfamB, hrank⟩, fun envT hextT hndT hfrT => ?_⟩
    have hkeyA : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x) :=
      fun x hx => Binding.plain_keyFree hC ht hg6 hextT hnA' hc₁ hx (hfrT x hx)
    refine overUnitStepTwin_of_parts ht hblobs hC.closed hc₁ hRc hA hszA hkeyA ?_
    intro env hext hnd hinv hrefs _ hstoredRb hfresh
    have husedA : ∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
        (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x := by
      intro i hi x hx
      have hux : UsedRef ρ.E₀ A x := ⟨c, i, hc₀, hi, by rwa [← Array.getElem?_toList]⟩
      rcases hrefs_ok_A x hux with hcov | hneed
      · obtain ⟨ci, hci, hn⟩ := coveredAt_stored hC.bnd.shape htwf
          (fun r hr => Nat.lt_of_lt_of_le (hr _ rfl) (Binding.valLimit_le g)) hcov
        exact Or.inl (find_isSome_of_storedAt ⟨ci, hext ci (hextT ci hci), hn⟩)
      · rcases hrefs x hux with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr h2
        · exact absurd hneed h3
    let mkC : ∀ k (hk : k < rs'.size),
        CanonMemberAt calls t ρ.E₀ env B rb crb rs es off fuel ind₀ k :=
      fun k hk =>
        let mC := Classical.choice (hextract_rb k (by omega))
        Classical.choice (canonMemberAt_of_extracted ht hst hinv hFOB_rb.record hRF_rb mC
          (hlvls_rb2 ind₀ k mC.rc hms0 mC.hmem) hstoredRb
          (Or.inl (hM_rb_E₀ k mC.rc mC.hmem)))
    have hpair_all :
        (∀ k (hk : k < rs'.size), Core.ExprLvEq (mkC k hk).ty_ld (mkC k hk).R) ∨
        ((∀ k rc, rs'[k]? = some (.recr rc) →
            MemberRecon (fun ty R => WrapConsObs (Binding.FamilyRecon.wrapAt t ρ.E₀)
              (WrapperObserved calls t) R ty) t ρ.E₀ A c rs' es off fuel k rc) ∧
          ∃ S : _root_.Address → Prop,
            (ReconView.ofStore t ρ.E₀).ClosedOn S ∧
            (∀ e ∈ es, Binding.FamilyRecon.REntryAt (ReconView.ofStore t ρ.E₀) S e) ∧
            (∀ j rc, rs[j]? = some (.recr rc) → ¬ S (memberAddr rb j (.recr rc)))) := by
      left
      intro k hk
      have hM_eq := hM_rb_E₀ k (mkC k hk).rc (mkC k hk).hmem
      obtain ⟨ty1, R1, _, _, hty1, hR1, hlv1, -, -, -⟩ := hM_eq
      have hty_e : ty1 = (mkC k hk).ty_ld := Option.some.inj (hty1.symm.trans (mkC k hk).hty_ld)
      have hR_e : R1 = (mkC k hk).R := Option.some.inj (hR1.symm.trans (mkC k hk).hR)
      rwa [hty_e, hR_e] at hlv1
    exact twinParts_of_canon_extracted ht hst hinv (fun _ _ h => h) (fun _ _ h => h)
      hFOB_rb.record.muts hFOB_rb.record.members hFOB_rb.record.recrs hA hszA hrs_len hes_len_A
      hRF_rb hRF_A mkC hextract_A (fun k rc hr => hlvls_A ind₀ k rc hms0 hr) hMR_A_all hpair_all
      husedA hfresh hkeyA

/-- **The binding closure's twin step at every group `6 ≤ g < 77` of every binding run**,
discharging `Binding.ClosureTwinSteps` from `TwinCallFlat`, `TwinCallRecon`, and
`StoredRecLvlsOk`. -/
theorem closureTwinSteps_of_premises
    (hFlat : TwinCallFlat) (hRecon : TwinCallRecon)
    (hStoredLvls : StoredRecLvlsOk) :
    ∀ calls, AtGroups (BindingRun calls) (ClosureTwinSteps.{u} FormerOpenTraceAt calls) :=
  fun calls t ρ Rs hrun hall ht g hg6 hg R R' R₁ env₀ famOf₀ famOf adv cont bAddr A c
    hC hnA hc₁ htw hfamA huncA =>
    closureTwinSteps_at hStoredLvls hrun hall ht hg6 hg hC hnA hc₁ htw hfamA huncA
      (fun B r cr rs cs _ _ hrec hsz hlogB hcall =>
        hFlat calls bAddr t ρ.E₀ B r cr rs (some (Binding.valLimit g)) cs ht hrun.bounded
          hrun.runStore hrun.hashedStored hrec hsz hlogB hcall)
      (fun B r cb cr ms rs cs _ _ hB hrec hsz hcall =>
        hRecon calls bAddr t ρ.E₀ B r cb cr ms rs (some (Binding.valLimit g)) cs ht hrun.bounded
          hrun.runStore hrun.hashedStored hB hrec hsz hcall)

end IxVM.Refinement.Typing.TwinFamily
