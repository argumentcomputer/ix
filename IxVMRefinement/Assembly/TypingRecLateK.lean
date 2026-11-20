import IxVMRefinement.Assembly.TypingRecLatePinsAt
import IxVMRefinement.Lib.Words
import IxVMRefinement.Levels.Bound

/-! # The K verdict of a recursor record, as the circuit reads it

The record's K flag is the member check's `compute_k_target(rc, parent, P)` verdict. At `1` the
verdict's arm is fixed: the parent is solo, `level_equal(result_level, Zero)` answered `1` for the
result level of the parent's type, the parent has one constructor, and that constructor, loaded by
`get_ci_cprj(block, idx, 0)`, has no field. Under the prefix keying the loaded constructor is the
family's stored constructor `0` and the parent's type is the stored former's, so:

* `rec_k_of_arm`: a record that declares K has one rule, the family has one stored constructor,
  with no field, and the family's result sort is zero at every assignment.

What the reload's K clause needs beyond this (`recRuleKOf` reads the stored former's
`nativeCaps fam.p`, whose `ruleK` reads the *declared* constructor's field count and `isProp`,
`Level.isEquiv`'s verdict) is not in the registry's clause; see the notes' findings K1, K2.
-/

universe u

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam NativeFamStored)

/-- **A level renamed to positions is zero everywhere only if the level is.** -/
theorem eval_eq_zero_of_posOf {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) {s : Ix.Kernel.Level}
    (h : ∀ φ, Ix.Kernel.Level.eval φ (Ix.Kernel.Level.subst ps (Core.posLevels ps) s) = 0) :
    ∀ ψ, Ix.Kernel.Level.eval ψ s = 0 := by
  intro ψ
  have h' := h (Decl.posVal ps ψ)
  rwa [Ix.Kernel.Level.eval_subst, Decl.substFn_posVal hperm] at h'

/-- **The K verdict at the tied parent**: a record that declares K has one rule; the matched
family has one stored constructor, which has no field; and the family's result sort is zero at
every assignment. -/
theorem rec_k_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hnat : RecArmRun calls t A lim) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P) {fam : NativeFam .anon}
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hm : FamReadAt L t E env P ip fam) (hsr : FormerSortReads t E lim env fam) :
    rc.k = true →
      rc.rules.size = 1 ∧ fam.ctorsA.length = 1 ∧
      (∀ cA, fam.ctorsA[0]? = some cA → cA.2 = 0) ∧
      ∀ φ : Ix.Kernel.LevelParam → Nat, Ix.Kernel.Level.eval φ fam.p.resSort = 0 := by
  intro hk
  obtain ⟨hat, hname, cb, ms, ind, hcb, hms, hind, hnP, hnI, hlenC, hnames⟩ := hm
  obtain ⟨hp, hi, hmot, hrules, hmin⟩ :=
    rec_counts_of_arm ht hS hst hc hinfo hnat hinert hcover hstep hcm hcmi htie hcb hms hind
  obtain ⟨rcv, apv, parentV, tyPtr, rulesPtr, blkPtr, tyPtrP, unsP, blkPtrP, kTarget, result,
    pointer, bA, bR, bT, bP, blobs, tree, scanHeap, loadedHeap, kHeap, kAfter, canonHeap, final,
    loadCalls, kCalls, canonCalls, hrc, hbA, hbA', hbR, hbR', hbT, hbT', hbP, hbP', hblob, rty,
    hrulesTr, hrules_lt, hidx56, hlvR, hlvP, hpP, hiP, hcP, eSL, evLoad, hsLoad, hldP, eK, evK,
    hsK, hkEq, eC, evCanon, hsCanon⟩ :=
    rec_arm_of_arm ht hS hst hc hinfo hnat hinert hcover hstep hcm hcmi htie hcb hms hind
  rw [hk] at hkEq
  let cS : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, lim⟩
  have hcS : Core.ScopedCoreFacts cS := hstep.inv.scopedCoreFacts
  -- the parent's type, as the stored former's
  have hformer : env.find? (Core.keyOf t P) =
      some (.indInfo fam.cvS (Ix.Kernel.nativeCaps fam.p)) := by
    rw [LoadedReads.keyOf_eq, ← hname]
    exact hat.stored.former
  have hκP : cS.κ P = Core.keyOf t P :=
    Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hformer
  have hgL : Core.Good ⟨E, env, t, lim⟩ loadCalls := (hst.good env lim).sub hsLoad
  obtain ⟨ci, hfind, hptr⟩ := Core.get_ci_step cS hcS evLoad parentV bT rfl trivial
    (by rw [hbT', hκP]; exact Core.Resolved.ne)
    (Core.CoreGood.ofRaw hgL (fun _ _ => trivial)) hbT
  rw [hbT', hκP] at hfind
  have hci : ci = .indInfo fam.cvS (Ix.Kernel.nativeCaps fam.p) :=
    Option.some.inj (hfind.symm.trans hformer)
  subst hci
  obtain ⟨v, hv, hrep⟩ := hptr
  rw [hldP] at hv
  injection hv with hv
  subst hv
  obtain ⟨cv, caps, hcv, hval⟩ := ciRep_induct_fields hrep
  obtain ⟨hcvEq, -⟩ := Ix.Kernel.ConstantInfo.indInfo.inj hcv
  subst hcvEq
  obtain ⟨-, -, hperm, htm⟩ := hval
  unfold FormerSortReads at hsr
  rw [hnP, hnI] at hsr
  have hgK : Core.Good ⟨E, env, t, lim⟩ kCalls := (hst.good env lim).sub hsK
  -- the verdict's arm
  match Obs.«KernelCheck::compute_k_target».obs evK with
  | .Induct_n0 (he103 := he) .. =>
    rw [← hkEq] at he
    exact absurd he (by simp [Ingress.repBoolField])
  | .Induct_other_n0 (he212 := he) .. =>
    rw [← hkEq] at he
    exact absurd he (by simp [Ingress.repBoolField])
  | .Induct_other_other_n1_other (he355 := he) .. =>
    rw [← hkEq] at he
    exact absurd he (by simp [Ingress.repBoolField])
  | .Induct_other_other_other (he362 := he) .. =>
    rw [← hkEq] at he
    exact absurd he (by simp [Ingress.repBoolField])
  | .other (hne365 := hne) .. =>
    exact absurd rfl (hne [_, _, _, _, _, _, _, _] rfl)
  | .Induct_other_other_n1_Ctor (m60 := m60) (m111 := m111) (m159 := m159) (m196 := m196)
      (m172 := m172) (m234 := m234) (v110 := resLvl) (v126 := nsum) (v171 := eqv)
      (cs121 := cs121) (cs183 := cs183) (cs247 := cs247) (hv15 := parentShape)
      (ev72 := soloRun) (op155 := hsumOp) (hm167 := hm167) (ev123 := sortRun) (hm204 := hm204)
      (ev185 := eqRun) (hne215 := hneq) (ev249 := ctorRun) (ld243 := ldC) (ev341 := zeroRun)
      (hc350 := children) .. =>
    injection parentShape with _ _ parentFields
    simp only [List.cons.injEq, and_true] at parentFields
    obtain ⟨rfl, rfl, rfl, rfl, hnc1, rfl, rfl, rfl⟩ := parentFields
    have hsize : ind.ctors.size = 1 := field_nat_eq_one (by omega) hnc1
    have hlenA : fam.ctorsA.length = 1 := hlenC.trans hsize
    -- heaps
    have e1 : Heap.Extends kHeap m159 := soloRun.heap_extends.trans (ext_of_eq_snoc hm167)
    have e2 : Heap.Extends m111 m196 := ext_of_eq_snoc hm204
    have e3 : Heap.Extends kHeap m172 :=
      e1.trans (sortRun.heap_extends.trans (e2.trans eqRun.heap_extends))
    have hsub : ∀ {cs : List (Call F)}, (∀ x ∈ cs, x ∈ kCalls) →
        Core.CoreGood cS cs :=
      fun h => Core.CoreGood.ofRaw (hgK.sub h) (fun _ _ => trivial)
    -- the result sort is zero
    have hnsum : nsum = .field ((ind.params.toNat + ind.indices.toNat : Nat) : F) :=
      Decl.evalBinOp_add_nat _ _ hsumOp
    rw [hnsum] at sortRun
    have htys : Core.TypesRep cS.κ (fun _ => default) m159 0
        (.ptr (.enum Core.kexprListEnum) m60.length) := by
      rw [hm167]
      exact Decl.typesRep_alloc_nil _ _ _
    obtain ⟨ℓ, hℓ, hsℓ⟩ := hsr ((hrc.mono eK).mono e1) htys
      (hsub (fun x hx => by rw [children]; simp [hx]))
      ((htm.mono (eK.trans e1)) 0 (fun _ => default)) sortRun
    have hzero : IxVM.Refinement.KernelLevels.RepKLevel m196 .zero
        (.ptr (.enum "KernelTypes::KLevelNode") m111.length) := by
      rw [hm204]
      exact (IxVM.Refinement.KernelLevels.RepKLevel.allocZero m111).1
    have hbnd : Bounded cs183 := (hgK.sub (fun x hx => by rw [children]; simp [hx])).2
    obtain ⟨heqv, -⟩ := IxVM.Refinement.Levels.levelEqual_obs eqRun hbnd
      (IxVM.Refinement.KernelLevels.repKLevel_heapMono₂ e2 hℓ) hzero
    have hle : IxVM.Refinement.KernelLevels.levelEqual ℓ .zero = true := by
      cases hb : IxVM.Refinement.KernelLevels.levelEqual ℓ .zero
      · rw [hb] at heqv
        exact absurd (by simpa using heqv) hneq
      · rfl
    have hsort0 : ∀ φ, Ix.Kernel.Level.eval φ (Ix.Kernel.Level.subst fam.cvS.levelParams
        (Core.posLevels fam.cvS.levelParams) fam.p.resSort) = 0 := fun φ => by
      rw [hsℓ φ]
      exact IxVM.Refinement.KernelLevels.levelEqual_eq_true_sound hle φ
    -- the constructor has no field
    have hfields : ∀ cA, fam.ctorsA[0]? = some cA → cA.2 = 0 := by
      intro cA hcA
      have hfindC := (hat.stored.ctor 0 cA hcA).1
      rw [hnames 0 cA hcA, ← LoadedReads.keyOf_eq] at hfindC
      have hκC : cS.κ (Core.cprjAddr ip.block ip.idx.toNat 0) =
          Core.keyOf t (Core.cprjAddr ip.block ip.idx.toNat 0) :=
        Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hfindC
      have hidx : ZMod.val ((ip.idx.toNat : Nat) : F) = ip.idx.toNat :=
        ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
      have hfindC' : cS.env.find? (cS.κ (Core.cprjAddr (Core.ixAddr bP)
          (ZMod.val ((ip.idx.toNat : Nat) : F)) (ZMod.val (0 : F)))) =
          some (.ctorInfo cA.1 fam.p.nP cA.2) := by
        rw [hbP', hidx, ZMod.val_zero, hκC]
        exact hfindC
      obtain ⟨-, hctor⟩ := Core.get_ci_cprj_step cS hcS ctorRun _
        ((ip.idx.toNat : Nat) : F) (0 : F) bP rfl trivial (Or.inr ⟨_, _, _, _, hfindC'⟩)
        (hsub (fun x hx => by rw [children]; simp [hx]))
        (Bytes.repAddressRef_heapMono₂ Core.addrTy (eK.trans e3) hbP)
      obtain ⟨v, hv, hrepC⟩ := hctor _ _ _ hfindC'
      rw [ldC] at hv
      injection hv with hv
      subst hv
      obtain ⟨cv', nP', nF', hciC, -, -, hnf', ⟨-, hnF⟩, -⟩ := Core.CIRep.ctor_fields hrepC
      obtain ⟨-, -, rfl⟩ := Ix.Kernel.ConstantInfo.ctorInfo.inj hciC
      obtain ⟨hz, -⟩ := Lib.is_zero_spec zeroRun
      rw [← hkEq, hnf'] at hz
      have hz' : ((.field (cA.2 : F)) : SourceValue F) = .field 0 := by
        by_contra hne
        rw [ite_eq_right hne] at hz
        exact absurd hz (by simp [Ingress.repBoolField])
      exact field_nat_eq_zero (by omega) hz'
    exact ⟨hrules.trans hsize, hlenA, hfields, eval_eq_zero_of_posOf hperm hsort0⟩

end IxVM.Refinement.Typing
