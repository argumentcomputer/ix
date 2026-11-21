import IxVMRefinement.Assembly.NativeAliasStep
import IxVMRefinement.Assembly.NativeAliasInstall
import IxVMRefinement.Assembly.NativeBlockInstallOf
import IxVMRefinement.Assembly.NativeAliasRetHead

/-! # The install of a block whose former is declared at a definition, from its walked check

`aliasInstallOut_of_member` produces `AliasInstallOut` (`Assembly/NativeAliasStep.lean`) from
the walk's check of the block's member: both typed stages on one reading with the traced
telescope (`aliasOuts_of_member_traced`), IxC's install at the registered family
(`nativeAtFacts_of_alias_outs_keys`), and the new constants named, found, fresh and read.

* `NativeAtFacts.env_of_indexed`: the environment after an install at a family with an index
  is the stored constructors and the stored former in front of the prefix, with the former at
  the family's own capability record; the completed record, the telescope's sort and the
  constructors' stage are read off IxC's record.
* `aliasInstallOut_of_member`: the output, at a check under the role context of either validator.
  The family's key is asked to be none of the four literal-function keys (`hliterals`): the
  typing fold has it from the full table (`alias_literal_keys_distinct`).
* `aliasUnitStep_of_member`: **the step, stated once**, from the walk's facts.
* `unitStep_nativeBlockAlias`, `overUnitStep_nativeBlockAlias`: the typing fold's step and the
  binding fold's step.
-/

universe u

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps Key)
open Ix.Kernel.Semantics (NativeFam NativeFamStored SumCtorsRunJ)
open Ix.Kernel.Model (rulesJ)

/-- **The environment after an install at a family with an index** (module docstring). -/
theorem NativeAtFacts.env_of_indexed {env env₂ : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {nP nIdx : Nat} {p₀ p : Ix.Kernel.NativeParts .anon}
    {cvS cvTa : ConstantVal .anon} {ctorsA : List (ConstantVal .anon × Nat)}
    (h : NativeAtFacts env env₂ blk nP nIdx p₀ ⟨p, cvS, cvTa, ctorsA⟩) (hidx : p₀.nIdx ≠ 0) :
    ∃ (s : Ix.Kernel.Level) (kinds : List (List Ix.Kernel.RecFieldKind))
      (sortss : List (List Ix.Kernel.Level)),
      p = (p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds ∧
      env₂ = ⟨((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [.indInfo cvS (Ix.Kernel.nativeCaps p)]) ++ env.consts⟩ ∧
      (∃ bs, cvTa.type.stripPis (p₀.nP + p₀.nIdx) = some (bs, .sort s)) ∧
      SumCtorsRunJ rulesJ ⟨.indInfo cvS (Ix.Kernel.nativeCaps p) :: env.consts⟩
        ⟨.indInfo cvS (Ix.Kernel.nativeCaps p) :: env.consts⟩ p.cvT.name p.cvT.levelParams
        p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors ctorsA sortss ∧
      Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM .anon) p.cvT.name p.cvT.levelParams
        p.nP p.nIdx ctorsA = .ok kinds := by
  obtain ⟨-, -, isRec, cvS', cvTa', caps, p₁, p', ctorsA', sortss, kinds, tfvs, trest, isorts,
    hfam, hInd, hp, hCtors, hK, hcaps, -, -, -, -, hTbl⟩ := h
  injection hfam with h1 h2 h3 h4
  subst h1 h2 h3 h4
  obtain ⟨cvTa₀, s, bs, cvS'', -, -, hstrip, -, hp₁, henvI⟩ := hInd
  have hcapsEq : caps = Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec := by
    injection henvI with hl
    injection hl with hhd
    injection hhd with _ hc'
    rw [hc', hp₁]
  have hcapsP : caps = Ix.Kernel.nativeCaps p := by
    rw [hcapsEq, hcaps, hp₁]
  subst hcapsP
  have hpEq : p = (p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds := by
    rw [hp, hp₁]
  have hpn : p.nIdx = p₀.nIdx := by rw [hpEq]; rfl
  have hc : (Ix.Kernel.consSumCtors p.nP ctorsA
      ⟨.indInfo cvS (Ix.Kernel.nativeCaps p) :: env.consts⟩).consts =
      ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [.indInfo cvS (Ix.Kernel.nativeCaps p)]) ++ env.consts := by
    rw [Decl.consts_consSumCtors_eq]
    simp
  refine ⟨s, kinds, sortss, hpEq, ?_, ⟨bs, hstrip⟩, hCtors, hK⟩
  rw [checkNativeTable_of_indexed hTbl (by rw [hpn]; exact hidx)]
  exact congrArg Ix.Kernel.Env.mk hc

/-- **What the check of a block whose former is declared at a definition puts in front of a
prefix, read off the member check** (module docstring). -/
theorem aliasInstallOut_of_member {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    {lim : Option Nat} {env : Ix.Kernel.Env .anon}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hnat : NativeRouteAt calls B) (halias : FormerAtAlias t E₀ B cb ind)
    (hliterals : Core.keyOf t (memberAddr B 0 (.indc ind)) ≠ Ix.Kernel.stringOfListName ∧
      Core.keyOf t (memberAddr B 0 (.indc ind)) ≠ Ix.Kernel.listNilName ∧
      Core.keyOf t (memberAddr B 0 (.indc ind)) ≠ Ix.Kernel.listConsName ∧
      Core.keyOf t (memberAddr B 0 (.indc ind)) ≠ Ix.Kernel.charOfNatName)
    (hndE : (env.consts.map (·.name)).Nodup)
    (hinv : Decl.PrefixInv.{u} E t lim env) (hstored : Decl.UsedRefsStored t env cb)
    (hkeys : HashKeyed t env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hcov : Ingress.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env) :
    ∃ (blk : List (ConstantInfo .anon)) (p₀ : Ix.Kernel.NativeParts .anon)
      (new : List (ConstantInfo .anon)) (fam : NativeFam .anon) (caps : IndCaps .anon),
      AliasInstallOut t E₀ env B cb ind blk p₀ new fam caps := by
  have hbound : Bounded calls := (hst.good env none).2
  have htwf : t.wf = true := hinv.tableWf
  have hP : HashedBlockProjectionsHeld E := hashedBlockProjectionsHeld_of_decoded hst.decoded
  obtain ⟨ty₀r, csr, -, -, -, hall⟩ := blockReads_of_member_lim ht hbound hS hrec hchk
  obtain ⟨hblk, hpin, hna⟩ := hall {}
  obtain ⟨p₀, hp₀, hnd₀, hnIdx₀⟩ :=
    nativePartsAt_of_member_lim ht hbound hS hrec hchk halias hblk hfree
  obtain ⟨cvS, cvTa, s, ctorsA, rawTypes, hcheckS, hAT, hnameS, -, -, hlenA, hparam, houts, -,
    hzero, hidx, hunused, htrB, htrS,
    ⟨ty₀, ty', hty, hlbb, hdef, hcT, hcvT, hcvS, hnP₀, hlenP, hp56, hi56, hc56⟩, hper, hRawRet⟩ :=
    aliasOuts_of_member_traced ht hS hst hrec hchk hnat hblk hp₀ hnIdx₀ (.inr halias) hinv
      hstored hP hkeys hfresh hfree hcov haux
  have hidx₀ : p₀.nIdx ≠ 0 := by
    rw [hnIdx₀]
    exact hidx
  obtain ⟨env₂, p, hfacts⟩ := nativeAtFacts_of_alias_outs_keys ht hS hst hrec hchk hblk hp₀ hnd₀
    hidx₀ hliterals hinv hfresh haux hcheckS hAT hparam hzero hnameS hlenA houts hunused
  obtain ⟨s', kinds, sortss, hpEq, henv₂, ⟨bsT, hstripT⟩, hCtors, hK⟩ :=
    hfacts.env_of_indexed hidx₀
  subst henv₂
  subst hcvS
  -- the completed record
  have hpcvT : p.cvT = p₀.cvT := by rw [hpEq]; rfl
  have hpnP : p.nP = p₀.nP := by rw [hpEq]; rfl
  have hpnIdx : p.nIdx = p₀.nIdx := by rw [hpEq]; rfl
  have hpres : p.resSort = s' := by rw [hpEq]; rfl
  have hpk : p.kinds = kinds := by rw [hpEq]; rfl
  have hpctors : p.ctors = p₀.ctors := by rw [hpEq]; rfl
  have hpT : p.cvT.name = Core.keyOf t (Core.iprjAddr B 0) := by rw [hpcvT, hcvT]
  have hpL : p.cvT.levelParams = List.range ind.lvls.toNat := by rw [hpcvT, hcvT]
  -- the telescope's sort is the traced sort
  obtain ⟨-, ⟨bsA, hstripA⟩, -⟩ := id hAT
  have hss : s' = s := by
    have e := hstripT.symm.trans hstripA
    have e' : (Ix.Kernel.Expr.sort s' : Ix.Kernel.Expr .anon) = .sort s :=
      (Prod.mk.inj (Option.some.inj e)).2
    exact Ix.Kernel.Expr.sort.inj e'
  obtain ⟨hlA, -, hall'⟩ := hCtors
  have hlenA' : ctorsA.length = ind.ctors.size := hlenA.trans hlenP
  have hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none :=
    hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  have hfreshC : ∀ j < ind.ctors.size, env.find? (keyOf t (ctorAddr B 0 j)) = none :=
    fun j hj => hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩)
  have hTC : ∀ j < ind.ctors.size,
      keyOf t (ctorAddr B 0 j) ≠ Core.keyOf t (Core.iprjAddr B 0) := by
    intro j hj e
    have ha : ctorAddr B 0 j = memberAddr B 0 (.indc ind) := Core.keyOf_inj htwf e
    have h1 := hrec.ctors j hj
    rw [ha, hrec.former] at h1
    have hinfo := congrArg Ixon.Constant.info (Option.some.inj h1)
    simp [memberProjection, constructorProjection] at hinfo
  -- the constructors
  have hcOf : ∀ j < ind.ctors.size, ∃ c, p₀.ctors[j]? = some c := fun j hj =>
    ⟨p₀.ctors[j], List.getElem?_eq_getElem (by omega)⟩
  have hctorMem : ∀ cA ∈ ctorsA, ∃ j c, j < ind.ctors.size ∧ p₀.ctors[j]? = some c ∧
      ctorsA[j]? = some cA := by
    intro cA hcA
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hcA
    have hjlt : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
    have hjp : j < p₀.ctors.length := by omega
    exact ⟨j, p₀.ctors[j], by omega, List.getElem?_eq_getElem hjp, hj⟩
  have hnames : p₀.ctors.map (·.1.name) = ctorsA.map (·.1.name) := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_map, List.getElem?_map]
    cases hc : p₀.ctors[j]? with
    | none =>
      have h0 : ctorsA[j]? = none := by
        rw [List.getElem?_eq_none_iff] at hc ⊢
        omega
      rw [h0]
    | some c =>
      obtain ⟨ct, cty', -, -, -, -, -, -, -, -, -, -, -, hA⟩ := hper j c hc
      rw [hA]
      rfl
  have hctorA : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), ctorsA[j]? = some cA →
      cA.1.name = Core.keyOf t (Core.cprjAddr B 0 j) ∧
        cA.1.levelParams = List.range ind.lvls.toNat := by
    intro j cA hcA
    have hj : j < ind.ctors.size := by
      have := (List.getElem?_eq_some_iff.mp hcA).1
      omega
    obtain ⟨c, hc⟩ := hcOf j hj
    obtain ⟨ct, cty', -, -, -, hcl, hcn, hclp, -, -, -, -, -, hA⟩ := hper j c hc
    rw [hA] at hcA
    injection hcA with hcA
    subst hcA
    refine ⟨hcn, ?_⟩
    show c.1.levelParams = _
    rw [hclp, hcl]
  -- every new constructor is a canonical constructor of the block
  have hrevMem : ∀ ci ∈ (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse,
      ∃ j c cty', j < ind.ctors.size ∧ p₀.ctors[j]? = some c ∧
        ctorsA[j]? = some (⟨c.1.name, c.1.levelParams, cty'⟩, c.2) ∧
        ci = .ctorInfo ⟨c.1.name, c.1.levelParams, cty'⟩ p.nP c.2 := by
    intro ci hci
    obtain ⟨cA, hcA, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hci)
    obtain ⟨j, c, hj, hc, hA⟩ := hctorMem cA hcA
    obtain ⟨ct, cty', -, -, -, -, -, -, -, -, -, -, -, hA'⟩ := hper j c hc
    rw [hA] at hA'
    injection hA' with hA'
    subst hA'
    exact ⟨j, c, cty', hj, hc, hA, rfl⟩
  have hrevName : ∀ ci ∈ (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse,
      ∃ j < ind.ctors.size, ci.name = keyOf t (ctorAddr B 0 j) := by
    intro ci hci
    obtain ⟨j, c, cty', hj, hc, -, rfl⟩ := hrevMem ci hci
    obtain ⟨ct, cty'', -, -, -, -, hcn, -⟩ := hper j c hc
    exact ⟨j, hj, hcn⟩
  -- distinct names, fresh in the prefix
  have hndRev : ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse.map
      (·.name)).Nodup := by
    rw [List.map_reverse, List.nodup_reverse, List.map_map]
    have hf : ((·.name) ∘ fun c : ConstantVal .anon × Nat => ConstantInfo.ctorInfo c.1 p.nP c.2) =
        fun c => c.1.name := rfl
    rw [hf, ← hnames]
    exact hnd₀
  have hndL1 : (([ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0),
      List.range ind.lvls.toNat, ty'⟩ (Ix.Kernel.nativeCaps p)] ++ env.consts).map
        (·.name)).Nodup := by
    refine nodup_names_append (by simp) hndE ?_
    intro a ha b hb
    rw [List.mem_singleton.mp ha]
    exact (name_ne_of_find_none hfreshT b hb).symm
  have hndL2 : (((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      ([ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0),
      List.range ind.lvls.toNat, ty'⟩ (Ix.Kernel.nativeCaps p)] ++ env.consts)).map
        (·.name)).Nodup := by
    refine nodup_names_append hndRev hndL1 ?_
    intro a ha b hb
    obtain ⟨j, hj, hn⟩ := hrevName a ha
    rw [hn]
    rcases List.mem_append.mp hb with hb | hb
    · rw [List.mem_singleton.mp hb]
      exact hTC j hj
    · exact (name_ne_of_find_none (hfreshC j hj) b hb).symm
  have hndAll : ((((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
        (Ix.Kernel.nativeCaps p)]) ++ env.consts).map (·.name)).Nodup := by
    rw [List.append_assoc]
    exact hndL2
  have hfind : ∀ ci ∈ (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
        (Ix.Kernel.nativeCaps p)],
      (⟨((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
          (Ix.Kernel.nativeCaps p)]) ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name =
        some ci :=
    fun ci hci => find_of_mem_nodup hndAll (List.mem_append_left _ hci)
  have hmemF : ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat,
      ty'⟩ (Ix.Kernel.nativeCaps p) ∈
      (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
        (Ix.Kernel.nativeCaps p)] := by simp
  have hmemA : ∀ cA ∈ ctorsA, ConstantInfo.ctorInfo cA.1 p.nP cA.2 ∈
      (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
        (Ix.Kernel.nativeCaps p)] := fun cA hcA =>
    List.mem_append_left _ (List.mem_reverse.mpr (List.mem_map.mpr ⟨cA, hcA, rfl⟩))
  have hmemC : ∀ (j : Nat) (c : ConstantVal .anon × Nat) (cty' : Ix.Kernel.Expr .anon),
      p₀.ctors[j]? = some c →
      ctorsA[j]? = some (⟨c.1.name, c.1.levelParams, cty'⟩, c.2) →
      ConstantInfo.ctorInfo ⟨c.1.name, c.1.levelParams, cty'⟩ p.nP c.2 ∈
        (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
          (Ix.Kernel.nativeCaps p)] := by
    intro j c cty' hc hA
    exact hmemA _ (List.mem_of_getElem? hA)
  -- the block's readings
  obtain ⟨fr, cs, hblkEq, hfrR, hlenC, hcsR⟩ := id hblk
  obtain ⟨caps₀, hshape, -, -, -, -, -⟩ := nativePartsAt?_inv hp₀
  rw [hshape] at hblkEq
  injection hblkEq with hfr hcs
  subst hfr hcs
  have hext' : Ix.Kernel.EnvExt env _ := hfacts.envExt
  refine ⟨_, p₀, (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
        (Ix.Kernel.nativeCaps p)],
    ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, cvTa, ctorsA⟩,
    Ix.Kernel.nativeCaps p, {
      facts := hfacts
      pin := hpin
      nonAux := hna
      indexed := hidx
      nP := hpnP.trans hnP₀
      nIdx := hpnIdx.trans hnIdx₀
      lenA := hlenA'
      famName := hpT
      famLevels := hpL
      ctorNames := fun j cA hcA => (hctorA j cA hcA).1
      trace := ?_
      stored := ?_
      isProp := by
        show p.isProp = _
        rw [hpEq]
        rfl
      kinds := by
        show Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM .anon) p.cvT.name
          p.cvT.levelParams p.nP p.nIdx ctorsA = .ok p.kinds
        rw [hpk]
        exact hK
      nodupA := by
        show (ctorsA.map (·.1.name)).Nodup
        rw [← hnames]
        exact hnd₀
      ctorFields := fun j c cA hc hcA => (hall' j c cA hc hcA).1
      noProj := ?_
      retHead := blockCtorIxonRetHead_of_raw ht hS hst hrec hchk hRawRet
      nodup := by
        have h := hndAll
        rw [List.map_append] at h
        exact (List.nodup_append.mp h).1
      fresh := ?_
      reads := ?_
      named := ?_
      install := ?_ }⟩
  · -- the opened head trace, at the new environment
    refine ⟨?_, ?_⟩
    · have h1 := htrB.mono (env' := _) (fun k ci hk => hext'.find hk)
      have hcount : p.nP + p.nIdx = p₀.nP + p₀.nIdx := by rw [hpnP, hpnIdx]
      show Decl.TracedBinders _ (p.nP + p.nIdx) _ _
      rw [hcount]
      exact h1
    · have h2 := htrS.mono (env' := _) (fun k ci hk => hext'.find hk)
      have hcount : p.nP + p.nIdx = p₀.nP + p₀.nIdx := by rw [hpnP, hpnIdx]
      have hres : p.resSort = s := hpres.trans hss
      show Decl.TracedSort _ (p.nP + p.nIdx) _ p.resSort
      rw [hcount, hres]
      exact Decl.TracedSort.intro h2 (Core.LvEq.refl _)
  · -- the family as stored
    refine { former := ?_, ctor := ?_, lenA := hlA, lenK := ?_ }
    · show (⟨_⟩ : Ix.Kernel.Env .anon).find? p.cvT.name = _
      rw [hpT]
      exact hfind _ hmemF
    · intro j cA hcA
      replace hcA : ctorsA[j]? = some cA := hcA
      have hjc : j < p.ctors.length := by
        have := (List.getElem?_eq_some_iff.mp hcA).1
        omega
      obtain ⟨c, hc⟩ : ∃ c, p.ctors[j]? = some c :=
        ⟨p.ctors[j]'hjc, List.getElem?_eq_getElem hjc⟩
      obtain ⟨hf2, sorts, -, hrun⟩ := hall' j c cA hc hcA
      obtain ⟨-, -, -, -, ⟨cbs, es, hst', hes⟩, -⟩ := Decl.sumCtorRunJ_struct_facts hrun
      refine ⟨hfind _ (hmemA cA (List.mem_of_getElem? hcA)), ?_, cbs, es, ?_, hes⟩
      · show cA.1.levelParams = p.cvT.levelParams
        rw [(hctorA j cA hcA).2, hpL]
      · show cA.1.type.stripPis (p.nP + cA.2) = _
        rw [hf2]
        exact hst'
    · show ctorsA.length = p.kinds.length
      rw [hpk]
      exact (Ix.Kernel.classifyFixKinds_inv hK).2.2.2.symm
  · -- no stored constructor type projects out of the family
    intro j cA hcA
    replace hcA : ctorsA[j]? = some cA := hcA
    have hjP : j < p₀.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hcA).1
      omega
    obtain ⟨sortss₀, -, hsorts⟩ := houts false
    obtain ⟨c, cA', sorts, hc, hcA', -, hNCO⟩ := hsorts j hjP
    have e : cA' = cA := Option.some.inj (hcA'.symm.trans hcA)
    rw [e] at hNCO
    show Decl.noProjAt p.cvT.name cA.1.type = true
    rw [hpcvT]
    exact hNCO.noProj
  · -- fresh
    intro ci hci
    rcases List.mem_append.mp hci with hci | hci
    · obtain ⟨j, hj, hn⟩ := hrevName ci hci
      rw [hn]
      exact hfreshC j hj
    · rw [List.mem_singleton.mp hci]
      exact hfreshT
  · -- reads
    intro x hx
    rcases hx with ⟨-, hs⟩ | ⟨ms', i, mi, hms', hmi, hx⟩
    · exact (standalone_not_block hs ⟨_, hrec.muts⟩).elim
    · rw [hrec.muts] at hms'
      have hmsEq : ms' = #[.indc ind] := (Ixon.ConstantInfo.muts.inj hms').symm
      subst hmsEq
      have hi : i = 0 := by
        have := (Array.getElem?_eq_some_iff.mp hmi).1
        simp at this
        omega
      subst hi
      have hmiEq : mi = .indc ind := by simpa using hmi.symm
      subst hmiEq
      rcases hx with rfl | ⟨ind', j, hind', hj, rfl⟩
      · refine ⟨_, hmemF, _, rfl, hfrR, ?_⟩
        unfold StoredAs
        refine ⟨?_, trivial⟩
        unfold ValStored
        rw [hcvT]
        exact ⟨rfl, rfl, canonAnn_annotates hcT⟩
      · injection hind' with hind'
        subst hind'
        obtain ⟨c, hc⟩ := hcOf j hj
        obtain ⟨ct, cty', hct, hcidx, hcp, hcl, hcn, hclp, hc2, hrd, hclbb, hcdef, hcan, hA⟩ :=
          hper j c hc
        have hcsj : (p₀.ctors.map (fun c => ConstantInfo.ctorInfo c.1 p₀.nP c.2))[j]? =
            some (.ctorInfo c.1 p₀.nP c.2) := by
          rw [List.getElem?_map, hc]
          rfl
        refine ⟨_, hmemC j c cty' hc hA, _, hcn, hcsR j _ hcsj, ?_⟩
        unfold StoredAs
        refine ⟨?_, hpnP, rfl⟩
        unfold ValStored
        exact ⟨rfl, rfl, canonAnn_annotates hcan⟩
  · -- named
    intro ci hci
    rcases List.mem_append.mp hci with hci | hci
    · obtain ⟨j, hj, hn⟩ := hrevName ci hci
      exact ⟨ctorAddr B 0 j,
        Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩, hn,
        address_size_of_record hS (hrec.ctors j hj)⟩
    · rw [List.mem_singleton.mp hci]
      exact ⟨memberAddr B 0 (.indc ind),
        Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩, rfl,
        address_size_of_record hS hrec.former⟩
  · -- the new constants as a store that holds the block's records reads them
    intro E' lim hH
    exact {
      check := ht
      decoded := hH.decoded
      held := hashedBlockProjectionsHeld_of_decoded hH.decoded
      block := hH.block
      muts := hrec.muts
      formerRec := hH.former
      ctorRec := hH.ctors
      bounds := ⟨hp56, hi56, hc56⟩
      used := usedRefsStored_append hstored _
      former := ⟨ty₀, ty', ReaderReads.exprReader_mono (fun x b hb => hH.blobs x b hb) hty,
        hlbb, hdef, hcT, hfind _ hmemF⟩
      ctor := by
        intro j hj
        obtain ⟨c, hc⟩ := hcOf j hj
        obtain ⟨ct, cty', hct, hcidx, hcp, hcl, hcn, hclp, hc2, hrd, hclbb, hcdef, hcan, hA⟩ :=
          hper j c hc
        rw [ZMod.val_zero] at hcan
        refine ⟨ct, c.1.type, cty', hct, hcidx,
          ReaderReads.exprReader_mono (fun x b hb => hH.blobs x b hb) hrd, hclbb, hcdef, hcan,
          ?_⟩
        have hf' := hfind _ (hmemC j c cty' hc hA)
        have hnP' : p.nP = ct.params.toNat := hpnP.trans (hnP₀.trans hcp.symm)
        rw [hcn, hclp, hc2] at hf'
        rw [← hnP']
        exact hf'
      newName := by
        intro ci hci
        rcases List.mem_append.mp hci with hci | hci
        · obtain ⟨j, hj, hn⟩ := hrevName ci hci
          exact Or.inr (Or.inl ⟨j, hj, hn⟩)
        · rw [List.mem_singleton.mp hci]
          exact Or.inl rfl
      newFind := hfind
      unit := fun hi0 => absurd hi0 hidx
      free := (hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)).1 }

/-! ## The step -/

/-- **The unit step of a block whose former is declared at a definition, stated once, from the
walk's facts**: the member's check under the role context of either validator, read at the
store `E`. The clause is kept at every store that holds the block's records, every limit and
every registry. `hliterals` separates the family's key from the four literal-function keys. -/
theorem aliasUnitStep_of_member {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {bAddr B : _root_.Address}
    {cb : Ixon.Constant} {ind : Ixon.Inductive} {lim : Option Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hnat : NativeRouteAt calls B) (halias : FormerAtAlias t E₀ B cb ind)
    (hliterals : Core.keyOf t (memberAddr B 0 (.indc ind)) ≠ Ix.Kernel.stringOfListName ∧
      Core.keyOf t (memberAddr B 0 (.indc ind)) ≠ Ix.Kernel.listNilName ∧
      Core.keyOf t (memberAddr B 0 (.indc ind)) ≠ Ix.Kernel.listConsName ∧
      Core.keyOf t (memberAddr B 0 (.indc ind)) ≠ Ix.Kernel.charOfNatName)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hcov : Ingress.CanonicalHashCoverage E calls) :
    AliasUnitStep.{u} t envT E₀ (fun E' => HoldsBlock E₀ E' B cb ind) E lim B cb :=
  aliasUnitStep_of_install ht hrec fun env Reg hext hnd hC href hfresh =>
    aliasInstallOut_of_member ht hS hst hrec hchk hnat halias hliterals hnd hC.prefixInv
      (usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert) hC.hashKeyed hfresh
      hfree hcov hC.auxRoot

/-- **`UnitStep` for a one-type native block whose former is declared at a definition, keeping
the fold's clause at the opened head trace**: the typing fold's step, from the walk's facts.
The full table separates the family's key from the literal-function keys. -/
theorem unitStep_nativeBlockAlias {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {R E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat}
    {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hctx : StepCtx.{u} calls t R envT E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hnat : NativeRouteAt calls B) (halias : FormerAtAlias t E₀ B cb ind)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hcov : Ingress.CanonicalHashCoverage E calls) :
    UnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt t E) t envT E₀ E lim B cb := by
  have hst : StepStore calls t E₀ E := hctx.toStepStore
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  intro env hext hnd hinv hX href hfresh
  have hliterals := alias_literal_keys_distinct (address := memberAddr B 0 (.indc ind)) htwf
    hctx.shape hext hnd (hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩))
  exact AliasUnitStep.unitStep (HoldsBlock.of_stepStore hst hrec)
    (aliasUnitStep_of_member ht hS hst hrec hchk hnat halias hliterals hfree hinert hcover hcov)
      env hext hnd hinv hX href hfresh

end IxVM.Refinement.Typing
