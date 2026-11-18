import IxVMRefinement.Assembly.TypingRecLateNativeFront2
import IxVMRefinement.Assembly.NativeAliasRunTrace
import IxVMRefinement.Assembly.TypingRecLateNativeElim
import IxVMRefinement.Assembly.TypingRecLateNativeRead

/-! # The circuit side of a late recursor's step

A late recursor record `c` at `A` (a standalone recursor, `c.info = .recr rc`) is checked by
`check_const`'s `Rec` arm: the scope check and the sort check of its type, then the member check,
whose canonical comparison runs `nat_rec_check` against the tied parent `P`, an inductive
projection of member `ind` of the block `ip.block`, matched to a registered family `fam`.

With `k` the member's level count, `large` whether the record declares one level more, and
`ps := recLps large (range k)` the record's level parameters, `rec_native_front` reads off the
arm:

* the type and the rules as read under `ps`, their scoping (the type's from the scope check, the
  rules' from the named hypothesis `hrscoped`), the rules naming the member's constructors;
* the canonical annotations of both (`canonAnn`, `canonRules`), which annotate the reading;
* the declared recursor checked at the step's environment (`ConstantValCheckJ`), from the scope
  and sort runs on the type pointer;
* the native recursor comparison (`Decl.late_nat_rec_check_spec_traced`, instantiated at the
  prefix keying for the type and at `lateRuleKey` for the rules, at the stored former's loaded
  type and the binders the family records for its telescope constant): the generated type and its relation
  with the canonical type, the generated rules and their relation with the canonical rules;
* the level arguments of the head of the major premise's domain (`Decl.front_maj`).

The universe offset `nat_rec_check` receives is the large-eliminator bit
(`canonical_full_nat_rec_bool`); `nat_rec_check` asserts the record's level count is the
parent's plus that bit, so the bit is `large`.
-/

universe u

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantVal)
open Ix.Kernel.Semantics (NativeFam)
open Ix.Kernel.Model (rulesJ)

/-- **The circuit side of a late recursor's step** (module docstring). -/
theorem rec_native_front {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) (hlogic : InLogic c)
    (hnat : RecArmRun calls t A lim)
    (hkey : Decl.KeyFree (keyOf t A)) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    (hlv : LvClauses env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind))
    {fam : NativeFam .anon} (hm : FamReadAt FormerOpenTraceAt t E env P ip fam)
    (hhead : Decl.CtorRetHeadAt cb ind)
    (hnoProj : FamCtorNoProj fam) (hbounds : RecArmBounds ip ind fam)
    (hrscoped : ∀ rules : List (Ix.Kernel.RecRule .anon),
      List.Forall₂ (fun ru rl₀ => (exprReader t (fun x => E₀.blobs.get? x) c
          (Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps
            (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)))
          (soloSelf t A)).read ru.rhs = .ok rl₀.rhs) rc.rules.toList rules →
      ∀ rl₀ ∈ rules, rl₀.rhs.looseBVarsBounded 0 = true ∧
        rl₀.rhs.allLevelParamsDefined (Ix.Kernel.Reader.recLps
          (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)) = true) :
    ∃ (ty : Ix.Kernel.Expr .anon) (rules : List (Ix.Kernel.RecRule .anon))
      (tyC : Ix.Kernel.Expr .anon) (rlsC : List (Ix.Kernel.RecRule .anon))
      (recTy : Ix.Kernel.Expr .anon),
      -- (A)(B)(C) the type read under ps, closed, level parameters among ps
      (exprReader t (fun x => E₀.blobs.get? x) c
        (Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps
          (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)))
        (soloSelf t A)).read rc.typ = .ok ty ∧
      ty.looseBVarsBounded 0 = true ∧
      ty.allLevelParamsDefined (Ix.Kernel.Reader.recLps
        (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)) = true ∧
      -- (D) the rules read under ps
      List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
        (exprReader t (fun x => E₀.blobs.get? x) c
          (Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps
            (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)))
          (soloSelf t A)).read ru.rhs = .ok rl₀.rhs ∧
        rl₀.rhs.looseBVarsBounded 0 = true ∧
        rl₀.rhs.allLevelParamsDefined (Ix.Kernel.Reader.recLps
          (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)) = true)
        rc.rules.toList rules ∧
      -- (E) the rules name the member's constructors
      List.Forall₂ (RuleReads t (exprReader t (fun x => E₀.blobs.get? x) c
          (Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps
            (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)))
          (soloSelf t A)) ip.block ip.idx.toNat)
        rc.rules.toList.zipIdx rules ∧
      -- (F)(G) the canonical annotations
      LoadedReads.canonAnn c (Ix.Kernel.Reader.recLps
        (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)) 0 rc.typ ty =
        some tyC ∧
      LoadedReads.canonRules c (Ix.Kernel.Reader.recLps
        (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)) rc.k
        rc.params.toNat (0 + 1) rc.rules.toList rules = some rlsC ∧
      -- (K)(L) they annotate the reading, (M) the count
      Annotates tyC ty ∧ List.Forall₂ RuleStored rlsC rules ∧
      (Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
        (List.range ind.lvls.toNat)).length = rc.lvls.toNat ∧
      -- (CV) the declared recursor checked at the step's environment
      Ix.Kernel.Semantics.ConstantValCheckJ rulesJ env
        ⟨keyOf t A, Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
          (List.range ind.lvls.toNat), ty⟩
        ⟨keyOf t A, Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
          (List.range ind.lvls.toNat), tyC⟩ ∧
      -- the comparison: generated type, its relation with tyC, the rules, the major head
      Ix.Kernel.structRecTyR fam.p.cvT.name fam.p.cvT.levelParams
        (if decide (rc.lvls.toNat = ind.lvls.toNat + 1) then ind.lvls.toNat else 0)
        (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) fam.p.nP fam.p.nIdx fam.cvTa.type
        (Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds) = some recTy ∧
      Decl.WrapRelSem env.find? recTy tyC ∧
      rlsC.length = fam.ctorsA.length ∧
      (∀ (j : Nat) (hlt : j < rlsC.length), ∃ rhsG,
        Ix.Kernel.structRecRhsR fam.p.cvT.name (List.range ind.lvls.toNat)
          (if decide (rc.lvls.toNat = ind.lvls.toNat + 1) then ind.lvls.toNat else 0)
          (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) fam.p.nP fam.p.nIdx
          fam.cvTa.type (Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds) (keyOf t A)
          ((Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
            (List.range ind.lvls.toNat)).map .param) j = some rhsG ∧
        Decl.WrapRelSem env.find? rhsG (rlsC[j]'hlt).rhs) ∧
      (∀ bs dom B m, tyC.stripPis (fam.p.nP + 1 + fam.p.ctors.length + fam.p.nIdx) =
        some (bs, .forallE dom B m) →
        ∃ K, dom.getAppFn = .const K (fam.p.cvT.levelParams.map .param)) := by
  -- the pins and the counts, before the arm is destructured
  obtain ⟨rules, hRR, hrd, -, -, hrlen, -⟩ := rec_pins_of_arm ht hS hst hc hinfo hnat hinert
    hcover hstep hcm hcmi htie hm
    (Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
      (List.range ind.lvls.toNat))
    ⟨keyOf t A, [], .sort .zero⟩ 0 false
  obtain ⟨hp, hi, hmot, hrsz, hmin⟩ :=
    rec_counts_of_arm ht hS hst hc hinfo hnat hinert hcover hstep hcm hcmi htie hcb hms hind
  have hm' := hm
  obtain ⟨hat, hname, cb', ms', ind', hcb', hms', hind', hnP, hnI, hlenC, hnames⟩ := hm'
  have hcbE : cb' = cb := Option.some.inj (hcb'.symm.trans hcb)
  subst cb'
  have hmsE : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
  subst ms'
  have hindE : ind' = ind := Ixon.MutConst.indc.inj (Option.some.inj (hind'.symm.trans hind))
  subst ind'
  obtain ⟨-, hL1⟩ := hat.logic_lvls ht hname hcm hcmi hcb hms hind
  -- the arm, in full
  obtain ⟨rcv, apv, parentV, tyPtr, rulesPtr, blkPtr, tyPtrP, unsP, blkPtrP, pointer, result,
    scopeResult, sortResult, bA, bR, bT, bP, blobs, tree, planT, ldHeap, scopeBefore, scopeAfter,
    sortAfter, memberHeap, scanHeap, loadedHeap, canonHeap, final, ldCalls, scopeCalls,
    sortCalls, scanCalls, loadCalls, canonCalls, hrc, hbA, hbA', hbR, hbR', hhp, hsLd, hblob,
    built, rty, hpT, hlT, hrulesTr, hrules_lt, hidx56, hlvR, hpR, hiR, hmR, hmiR, hlvP, hpP, hiP,
    hcP, eLS, evS, hmemS, evSort, hsSort, eSM, evScan, hsScan, hbT, hbT', hbP, hbP', eSL, evLoad,
    hsLoad, hldP, eC, evCanon, hsCanon⟩ :=
    rec_front_arm ht hS hst hc hinfo hnat hinert hcover hstep hcm hcmi htie hcb hms hind
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hgood : Core.Good ⟨E, env, t, lim⟩ calls := hst.good env lim
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hstep.ext, hstep.refs, hstep.fresh⟩) hinert
  have hcS : Core.ScopedCoreFacts (Core.Ctx.stored ⟨E, env, t, lim⟩) :=
    hstep.inv.scopedCoreFacts
  have henv : Ix.Kernel.EnvWF env := hstep.inv.store.store.wf
  have hagree := LoadedReads.blobReadAgreement_of_noCollision (hgood.sub hsLd).1 hhp t
  obtain ⟨hk31, hnP31, hnI31, hnC31, hnall, hidx32, hc4⟩ := hbounds
  -- the universe offset is the large-eliminator bit, which is `large`
  obtain ⟨large', natHeap, natCalls, eN, evNat, hsNat⟩ := canonical_full_nat_rec_bool evCanon
  have hsum := Decl.evalBinOp_add_nat _ _ (nat_rec_check_levels evNat)
  have hb1 : (if large' then 1 else 0 : Nat) ≤ 1 := by cases large' <;> decide
  have hlvEq : rc.lvls.toNat = ind.lvls.toNat + (if large' then 1 else 0) :=
    field_nat_inj (by omega) (by omega) hsum
  have hlvOr : rc.lvls.toNat = ind.lvls.toNat ∨ rc.lvls.toNat = ind.lvls.toNat + 1 := by
    cases large' with
    | false => exact Or.inl (by simpa using hlvEq)
    | true => exact Or.inr (by simpa using hlvEq)
  have hlarge : decide (rc.lvls.toNat = ind.lvls.toNat + 1) = large' := by
    cases large' with
    | false =>
      have h0 : rc.lvls.toNat = ind.lvls.toNat := by simpa using hlvEq
      exact decide_eq_false (by omega)
    | true => exact decide_eq_true (by simpa using hlvEq)
  subst hlarge
  -- the level parameters
  have hpsE := front_recLps_eq (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) ind.lvls.toNat
  have hpsLen : (Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
      (List.range ind.lvls.toNat)).length = rc.lvls.toNat := LoadedReads.recPs_length hlvOr
  have hpsPerm : (Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
      (List.range ind.lvls.toNat)).Perm (List.range (Ix.Kernel.Reader.recLps
        (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)).length) :=
    LoadedReads.recPs_perm hlvOr
  have hps32 : (Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
      (List.range ind.lvls.toNat)).length < 4294967296 := by
    rw [hpsLen]; exact hlvR
  -- (A)(B)(C): the type, read under ps and under the positions, scoped by the scope check
  obtain ⟨ty, hty⟩ := LoadedReads.exprReader_read_ok (t := t)
    (blob := fun x => E₀.blobs.get? x) ht
    (param := Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps
      (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)))
    (self := soloSelf t A) rty (fun i x hx => by simp at hx) hblob
  obtain ⟨ty₀, hty₀⟩ := LoadedReads.exprReader_read_ok (t := t)
    (blob := fun x => E₀.blobs.get? x) ht (param := id) (self := soloSelf t A) rty
    (fun i x hx => by simp at hx) hblob
  obtain ⟨-, hlbb₀, hdef₀⟩ := Assembly.validate_expr_well_scoped_spec
    (cx := readCtx t (fun x => E₀.blobs.get? x)) (self := soloSelf t A)
    hgood.2 hlvR rty eLS hty₀ evS hmemS
  obtain ⟨hlbb, hdef⟩ := read_recParam_scoped hpsPerm hty hty₀ hlbb₀
    (by rw [hpsLen]; exact hdef₀)
  -- (F)(K): the canonical type, exactly represented at the prefix's keying
  obtain ⟨tyC, hcT, hannT, htmT⟩ := front_type_canon (lim := lim) ht hinfo hstored hst.runBlob
    hpsPerm hps32 hagree built rty hpT hlT hty hlbb hdef
  -- (CV)
  have hcv := front_constantValCheck (A := A) hstep.inv hlv hpsLen hps32 hpsPerm hannT hlbb
    (Assembly.memberReader_read_noFvar hty)
    (hstep.fresh A (Or.inl ⟨rfl, Or.inr (Or.inl ⟨rc, hinfo⟩)⟩)) hkey.1 (htmT.mono eLS) evS
    (hrc.mono (eLS.trans (evS.heap_extends.trans (Heap.Extends.snoc _ _))))
    (hgood.sub hsSort) evSort
  -- (D)(G)(L): the rules
  have hrdS : List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
      (exprReader t (fun x => E₀.blobs.get? x) c
        (Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps
          (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)))
        (soloSelf t A)).read ru.rhs = .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧
      rl₀.rhs.allLevelParamsDefined (Ix.Kernel.Reader.recLps
        (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)) = true)
      rc.rules.toList rules :=
    (front_forall₂_and_right hrd (hrscoped rules (hrd.imp (fun _ _ h => h.2)))).imp
      (fun _ _ h => ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩)
  obtain ⟨rlsC, hcR, hstR, hrrC⟩ := front_rules_canon (lim := lim) ht hinfo hstored hst.runBlob
    hpsPerm hps32 hagree built hrulesTr hrdS
  have hlenInfo : (lateCtorsInfo fam).length = fam.ctorsA.length := lateCtorsInfo_length hat.stored
  have hrlsC_len : rlsC.length = fam.ctorsA.length := by rw [hstR.length_eq, hrlen]
  have hrls_len : rlsC.length = (lateCtorsInfo fam).length := by rw [hrlsC_len, hlenInfo]
  -- heaps
  have eLM : Heap.Extends ldHeap memberHeap :=
    eLS.trans (evS.heap_extends.trans ((Heap.Extends.snoc _ _).trans
      (evSort.heap_extends.trans eSM)))
  have eScN : Heap.Extends scanHeap natHeap := eSL.trans (eC.trans eN)
  have eLN : Heap.Extends ldHeap natHeap := eLM.trans (evScan.heap_extends.trans eScN)
  -- the keys
  have hformer : env.find? (Core.keyOf t P) =
      some (.indInfo fam.cvS (Ix.Kernel.nativeCaps fam.p)) := by
    rw [LoadedReads.keyOf_eq, ← hname]
    exact hat.stored.former
  have hκP : (Core.Ctx.stored ⟨E, env, t, lim⟩).κ P = Core.keyOf t P :=
    Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hformer
  have hT : (Core.Ctx.stored ⟨E, env, t, lim⟩).κ (Core.ixAddr bT) = fam.p.cvT.name := by
    rw [hbT', hκP, LoadedReads.keyOf_eq, hname]
  have hκ₂_inj : ∀ a : Bytes.Address,
      lateRuleKey ⟨E, env, t, lim⟩ A (Core.ixAddr a) = fam.p.cvT.name → a = bT := by
    intro a ha
    have hsp : lateRuleKey ⟨E, env, t, lim⟩ A (Core.ixAddr a) = Core.keyOf t (Core.ixAddr a) ∨
        lateRuleKey ⟨E, env, t, lim⟩ A (Core.ixAddr a) = Core.unresolvedKey :=
      Core.resKey_spec _ _ _
    rcases hsp with h1 | h1
    · rw [h1, hname, LoadedReads.keyOf_eq] at ha
      have hPa : Core.ixAddr a = P := keyOf_inj hroles ha
      exact Decl.ixAddr_injective (hPa.trans hbT'.symm)
    · rw [h1, hname, ← LoadedReads.keyOf_eq] at ha
      exact absurd ha.symm Core.Resolved.ne
  have hRec : lateRuleKey ⟨E, env, t, lim⟩ A (Core.ixAddr bA) = keyOf t A := by
    rw [hbA', ← LoadedReads.keyOf_eq]
    exact lateRuleKey_self _ A
  have hRes : Core.Resolved (lateRuleKey ⟨E, env, t, lim⟩ A (Core.ixAddr bA)) := by
    rw [hbA']
    exact lateRuleKey_self_resolved _ A
  have hCres : ∀ i, i < (lateCtorsInfo fam).length →
      (Core.Ctx.stored ⟨E, env, t, lim⟩).κ
        (Core.cprjAddr (Core.ixAddr bP) ip.idx.toNat i) ≠ Core.unresolvedKey := by
    intro i hi
    rw [hlenInfo] at hi
    have hcA : fam.ctorsA[i]? = some fam.ctorsA[i] := List.getElem?_eq_getElem hi
    have hf := (hat.stored.ctor i _ hcA).1
    rw [hnames i _ hcA, ← LoadedReads.keyOf_eq] at hf
    rw [hbP', Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hf]
    exact Core.Resolved.ne
  -- the constructor entries
  have hnamesB : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
      cA.1.name = keyOf t (Core.cprjAddr (Core.ixAddr bP) ip.idx.toNat j) := by
    intro j cA hcA
    rw [hbP']
    exact hnames j cA hcA
  have hsN : ∀ x ∈ natCalls, x ∈ calls := fun x hx => hsCanon x (hsNat x hx)
  have hload : Decl.NatCtorLoadT (Core.Ctx.stored ⟨E, env, t, lim⟩).κ bP ip.idx.toNat
      ind.lvls.toNat (lateCtorsInfo fam) blkPtrP natCalls :=
    front_ctor_loads hcS hat.stored hL1 hidx32 (by rw [hlenC]; omega) hnamesB (hgood.sub hsN)
  have hnf_lt : ∀ (j : Nat) (info : Core.KKey × Nat × Core.KExpr × Core.KExpr × List Nat),
      (lateCtorsInfo fam)[j]? = some info → info.2.1 < 4294967296 := by
    intro j info hinfo'
    obtain ⟨cA, ks, hcA, hks, rfl⟩ := front_lateCtorsInfo_getElem? hinfo'
    have hmem : (cA.1.name, cA.2, cA.1.type, Ix.Kernel.recIdxOf ks) ∈
        Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds := by
      unfold Ix.Kernel.nativeCtors4
      exact List.mem_of_getElem? (List.getElem?_zipWith_eq_some.mpr ⟨cA, ks, hcA, hks, rfl⟩)
    have h1 : ind.params.toNat + cA.2 < 2147483648 := (hc4 _ hmem).1
    show cA.2 < 4294967296
    omega
  have hrecB : recordOf (⟨E, env, t, lim⟩ : Core.Ctx).E (Core.ixAddr bP) = some cb := by
    show recordOf E (Core.ixAddr bP) = some cb
    rw [hbP', recordOf_eq_recordAt_of_decoded hst.decoded]
    exact hcb
  have hretHead : Decl.NatCtorRetHeadT bP ip.idx.toNat fam.p.nP (lateCtorsInfo fam) blkPtrP
      natCalls :=
    Decl.natCtorRetHeadT_of_ixon (c := ⟨E, env, t, lim⟩) hrecB hms hind hhead hnP hidx32
      (by rw [hlenInfo, hlenC]; omega) hnf_lt hload (hgood.sub hsN)
  have hsubL : ∀ x ∈ fam.p.cvT.levelParams, x ∈ List.range ind.lvls.toNat := by
    intro x hx
    rw [hL1] at hx
    exact hx
  have hlpsS : fam.cvS.type.allLevelParamsDefined (List.range ind.lvls.toNat) = true := by
    have h := (henv _ (Ix.Kernel.Semantics.Env.find?_mem hat.stored.former)).2.1
    rw [hat.lps, hL1] at h
    exact h
  -- the parent's type
  have hpty := front_parent_former hcS hat.stored hat.lps hname hL1 hbT' (hgood.sub hsLoad) hbT
    evLoad hldP
  -- the run of the comparison, at the family's counts
  have e1 : rc.params.toNat = fam.p.nP := hp.trans hnP.symm
  have e2 : rc.indices.toNat = fam.p.nIdx := hi.trans hnI.symm
  have e3 : ind.ctors.size = (lateCtorsInfo fam).length := by rw [hlenInfo, hlenC]
  rw [e1, e2, e3] at evNat
  have hspec := Decl.late_nat_rec_check_spec_traced (c := Core.Ctx.stored ⟨E, env, t, lim⟩) hcS
    (fun _ => trivial) (κ₂ := lateRuleKey ⟨E, env, t, lim⟩ A) (find₂ := env.find?)
    (lateRuleKey_keep _ A) (wrapLoads_late hcS hst.decoded (hst.runRecord A c hc) hinfo)
    (cst := c) (rc' := rc) (T := fam.p.cvT.name) (recC := keyOf t A) (b₀ := bP) (bT := bT)
    (bRec := bA) (bRB := bR) (idx := ip.idx.toNat) (k := ind.lvls.toNat) (nP := fam.p.nP)
    (nIdx := fam.p.nIdx) (large := decide (rc.lvls.toNat = ind.lvls.toNat + 1))
    (pty₀ := fam.cvS.type) (ttyReg := fam.cvTa.type)
    (rec_ty₀ := tyC) (ctors_info := lateCtorsInfo fam) (rls := rlsC)
    ⟨_, _, hat.stored.former⟩
    (by rw [hbR']; exact hst.runRecord A c hc) hinfo hT hκ₂_inj hRec
    (by omega) hCres hk31 (by rw [hnP]; exact hnP31) (by rw [hnI]; exact hnI31)
    (by rw [hlenInfo, hlenC]; exact hnC31) (by rw [hlenInfo, hlenC, hnP, hnI]; exact hnall)
    hlpsS
    (lateCtorsInfo_wf hat henv hL1 hnoProj ⟨hk31, hnP31, hnI31, hnC31, hnall, hidx32, hc4⟩ hnP
      hlenC (decide (rc.lvls.toNat = ind.lvls.toNat + 1)))
    hrls_len hload hretHead (Core.CoreGood.ofRaw (hgood.sub hsN) (fun _ _ => trivial))
    (hrc.mono eLN)
    (Bytes.repAddressRef_heapMono₂ Core.addrTy (eC.trans eN) hbP)
    (Bytes.repAddressRef_heapMono₂ Core.addrTy eLN hbR)
    (Bytes.repAddressRef_heapMono₂ Core.addrTy eScN hbT)
    (Bytes.repAddressRef_heapMono₂ Core.addrTy eLN hbA)
    ((hpty.mono (eC.trans eN)) 0 (fun _ => default))
    (Ix.Kernel.HeadDeltaBeta.DefnLevelsClosed.of_envWF henv) hat.link.binders
    (by rw [← hpsE]; exact ((htmT 0 (fun _ => default)).mono eLN).toTm)
    (by rw [← hpsE]; exact hrrC.mono eLN)
    evNat
  dsimp only at hspec
  obtain ⟨-, -, -, ⟨recTy, hrecTy, hwrapTy⟩, hlvHead, hrulesSpec⟩ := hspec
  rw [lateCtorsInfo_map] at hrecTy
  refine ⟨ty, rules, tyC, rlsC, recTy, hty, hlbb, hdef, hrdS, hRR, hcT, hcR, hannT, hstR, hpsLen,
    hcv, ?_, hwrapTy, hrlsC_len, ?_, ?_⟩
  · rw [hL1]
    exact hrecTy
  · intro j hlt
    have hj : j < (lateCtorsInfo fam).length := by rw [← hrls_len]; exact hlt
    obtain ⟨-, rhsG, hG, hW⟩ := hrulesSpec j hlt hj
    rw [lateCtorsInfo_map] at hG
    refine ⟨rhsG, ?_, hW⟩
    rw [hpsE]
    exact hG
  · -- the head of the major premise's domain
    have hlenP : (lateCtorsInfo fam).length = fam.p.ctors.length :=
      hlenInfo.trans hat.stored.lenA
    have hmin' : rc.minors.toNat = fam.p.ctors.length := by
      rw [hmin, ← hlenC, hat.stored.lenA]
    rw [e1, hmot, hmin', e2] at evScan
    have hmaj := Decl.front_maj (κ := (Core.Ctx.stored ⟨E, env, t, lim⟩).κ)
      (k := ind.lvls.toNat) (large := decide (rc.lvls.toNat = ind.lvls.toNat + 1))
      (np := fam.p.nP) (nmi := fam.p.ctors.length) (ni := fam.p.nIdx) (tyC := tyC)
      (by rw [← hlenP, hlenInfo, hlenC, hnP, hnI]; omega)
      (by rw [← hpsE]; exact (htmT 0 (fun _ => default)).mono eLM)
      evScan eScN
      (fun a_d ls_d hr => hlvHead a_d ls_d (by rw [hlenP]; exact hr))
    intro bs dom B m hs
    rw [hL1]
    exact hmaj bs dom B m hs

end IxVM.Refinement.Typing
