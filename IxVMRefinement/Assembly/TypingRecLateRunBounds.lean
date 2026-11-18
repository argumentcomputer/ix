import IxVMRefinement.Assembly.RecArmRunBounds
import IxVMRefinement.Assembly.TypingRecLateNativeFront2
import IxVMRefinement.Claim.TopRec
import IxVMRefinement.Claim.TopDefn

/-! # The count bounds of a native recursor's step, from the arm's own observations

The step for a standalone native recursor reads the comparison `nat_rec_check` under count
bounds. This module derives the bounds an accepted run gives (`RecArmRunBounds`) from what the
walk observed at the record, at every validation limit:

* `RecArmObs calls A`: the walk loaded the record at `A` as a `Rec` value and ran `check_const`
  on it. It is `RecArmRun` and `Claim.RecArmLimAt` without their role-context
  representation, which the bounds do not read (`RecArmRun.obs`, `recArmObs_of_lim`);
* `recArmRun_of_limArm`: the arm the walk exports at any limit (`Claim.TopWalkCore.recArm`) is
  the arm the step reads;
* `recArmRunBounds_of_obs`: at a step's environment and the tied parent, the two loads of the
  arm (the record's own, and the member check's load of the parent) give `RecArmRunBounds`.
  Its hypotheses are those `rec_front_arm` takes, with the limit free;

The field count of each constructor is bounded where its load is observed
(`Decl.NatCtorLoadT`, `front_ctor_loads`), and the telescope of a recursive field where the
run passes it on (`Decl.teleRep_length_lt`).
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
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam NativeFamStored)

/-! ## The arm's observations, free of the role context -/

/-- **The walk's check of the record at `A` took the recursor arm**: the walk loaded the record
as a `Rec` value and ran `check_const` on it, its calls among the run's. The role context the
check ran under is not mentioned, so the statement is the same at every validation limit. -/
def RecArmObs (calls : List (Call F)) (A : _root_.Address) : Prop :=
  ∃ (h_pre m_chk h'_chk : Heap F) (rc ap ptr r_chk : SourceValue F)
    (levels type parameters indices motives minors rules k unsafeFlag block position :
      SourceValue F)
    (cs_load cs_chk : List (Call F)),
    Core.S0.addr h_pre ap A ∧
    ObsFn Obs.W "Ingress::get_ci" [ap] h_pre ptr m_chk cs_load ∧
    (∀ cl ∈ cs_load, cl ∈ calls) ∧
    loadValue m_chk ptr = .ok (.construct "KernelTypes::KConstantInfo" "Rec"
      [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
        position]) ∧
    ObsFn Obs.W "KernelCheck::check_const"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
          position], ap] m_chk r_chk h'_chk cs_chk ∧
    (∀ cl ∈ cs_chk, cl ∈ calls)

/-- The arm of a validating run gives the observations. -/
theorem NativeRecArm.obs {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {A : _root_.Address} {n : Nat}
    (h : NativeRecArm calls bAddr t A n) : RecArmObs calls A := by
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, -, -, ha_pre, -, ev_ld, hsub_ld,
    hld, ev_chk, hsub_chk⟩ := h
  exact ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, ha_pre, ev_ld, hsub_ld, hld,
    ev_chk, hsub_chk⟩

/-- The arm at a limit gives the observations. -/
theorem RecArmRun.obs {calls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {A : _root_.Address} {lim : Option Nat}
    (h : RecArmRun calls t A lim) : RecArmObs calls A := by
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, -, -, ha_pre, -, ev_ld, hsub_ld,
    hld, ev_chk, hsub_chk⟩ := h
  exact ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, ha_pre, ev_ld, hsub_ld, hld,
    ev_chk, hsub_chk⟩

/-- **The arm the walk exports at any limit is the arm at that limit**: the walk's role
context, read as the core reads it. -/
theorem recArmRun_of_limArm {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {A : _root_.Address} {lim : Option Nat}
    (h : Claim.RecArmLimAt calls bAddr t A lim) : RecArmRun calls t A lim := by
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, hrc_pre, hrc_m, ha_pre, ha_m, ev_ld,
    hsub_ld, hld, ev_chk, hsub_chk⟩ := h
  exact ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, hrc_pre.toRCRep, hrc_m.toRCRep,
    ha_pre, ha_m, ev_ld, hsub_ld, hld, ev_chk, hsub_chk⟩

/-- The arm the walk exports at any limit gives the observations. -/
theorem recArmObs_of_lim {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {A : _root_.Address} {lim : Option Nat}
    (h : Claim.RecArmLimAt calls bAddr t A lim) : RecArmObs calls A := by
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, -, -, ha_pre, -, ev_ld, hsub_ld,
    hld, ev_chk, hsub_chk⟩ := h
  exact ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, ha_pre, ev_ld, hsub_ld, hld,
    ev_chk, hsub_chk⟩

/-! ## The bounds from the two loads of the arm -/

/-- **The count bounds of a native recursor's step, from the arm's observations**, at every
validation limit. The record's own load bounds the recursor's level count (and its bytes bound
the rule count); the member check's scan of the type reaches the parent `P` the step is tied
to, and its load of `P` bounds the member's counts and the projection's member index. -/
theorem recArmRunBounds_of_obs {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (harm : RecArmObs calls A) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind)) :
    RecArmRunBounds rc ip ind := by
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hgood : Core.Good ⟨E, env, t, lim⟩ calls := hst.good env lim
  have hbound : Bounded calls := hgood.2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hstep.ext, hstep.refs, hstep.fresh⟩) hinert
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, ha_pre, ev_ld, hsub_ld,
    hld, ev_chk, hsub_chk⟩ := harm
  obtain ⟨rawB, cB, hszB, hhB, hbaB, hexB⟩ := get_ci_bytes_bound ha_pre ev_ld
  have hcB : cB = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hhB) hbaB hexB
  subst cB
  have hrules_lt := recr_rules_size_lt hszB hexB hinfo
  obtain ⟨a', ha'_ref, haA⟩ := ha_pre
  subst haA
  obtain ⟨rawBytes, c', hh, hba, hex, -, hres'⟩ :=
    L1.get_ci_block_trace_spec (hgood.sub hsub_ld).2 ha'_ref ev_ld
  have hcc : c' = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hh) hba hex
  subst c'
  unfold L1.GetCIBlockTraceResult at hres'
  rw [hinfo] at hres'
  obtain ⟨blobs, tree, v, hhp, built, hldv, htr⟩ := hres'
  rw [hld] at hldv
  obtain ⟨hlvls, hp56, hi56, hm56, hmi56, -, tyPtr, rulesPtr, blkPtr, bR, planT, hbR, hblkR, hv,
    rty, hpT, hlT, hrulesTr⟩ := htr
  subst hv
  injection hldv with hv'
  injection hv' with _ _ hfields
  simp only [List.cons.injEq, and_true] at hfields
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hfields
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hhx' : Hashed cs_load bs := hhx
    have hxa' : Address.blake3Pure bs = x := hxa
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx')
    rw [hxa'] at hrun
    exact hrun
  obtain ⟨tyP, htyP⟩ := LoadedReads.exprReader_read_ok (t := t)
    (blob := fun x => E₀.blobs.get? x) ht (param := id) (self := soloSelf t (Core.ixAddr a'))
    rty (fun i x hx => by simp at hx) hblob
  obtain ⟨-, sB, sA, sortAfter, mH, sR, sortR, sCs, sortCs, mCs, hextS, evS, hmemS, evSort,
    -, hsubSort, hextSM, evM, hsubM⟩ := check_const_rec_arm ev_chk
  obtain ⟨-, hlbb, hdef⟩ := Assembly.validate_expr_well_scoped_spec
    (cx := readCtx t (fun x => E₀.blobs.get? x)) (self := soloSelf t (Core.ixAddr a'))
    hbound hlvls rty hextS htyP evS (hsub_chk _ hmemS)
  have hrd : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E₀.blobs.get? x)) c
      (Ix.Kernel.Reader.recParam (List.range rc.lvls.toNat))
      (soloSelf t (Core.ixAddr a'))).read rc.typ = .ok tyP := by
    rw [Assembly.recParam_range]
    exact htyP
  obtain ⟨E', hann, htm⟩ := rty.toTmC (κ := Core.keyOf t) (ps := List.range rc.lvls.toNat)
    (by simp) (by simpa using hlvls) (LoadedReads.readCtx_keyAt_inv ht _)
    (fun i x m k hx => by simp at hx) hblob hrd hlbb hdef
  have htmS := Decl.tmC_stored_of_usedRefs (E₀ := E) (env := env) (lim := lim) rty
    (recr_typ_usedRefs hinfo) hstored htm
  rw [Decl.posOf_range] at htmS
  have hextM : Heap.Extends m_chk mH :=
    hextS.trans (evS.heap_extends.trans ((Heap.Extends.snoc _ _).trans
      (evSort.heap_extends.trans hextSM)))
  have hsum : ZMod.val ((rc.params.toNat : F) + (rc.motives.toNat : F) + (rc.minors.toNat : F) +
      (rc.indices.toNat : F)) =
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat := by
    rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
    exact ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  obtain ⟨parent, pointer, scanHeap, loadedHeap, routedHeap, scanCalls, loadCalls, routeCalls,
    nl, pty, np, ni, nc, pu, blk, idx, lenHeap, lenAfter, kHeap, kAfter, canonHeap, len, kTarget,
    lenCalls, kCalls, canonCalls, canonResult, canonFinal, evScan, hsScan, evLoad, hsLoad, hldP,
    evRoute, hsRoute, hnp, hni, eLen, evLen, hsLen, hlenEq, eK, evK, hsK, hkEq, eC, evCanon,
    hsCanon⟩ :=
    native_rec_member_full evM
  have hsScan' : ∀ x ∈ scanCalls, x ∈ calls := fun x hx => hsub_chk x (hsubM x (hsScan x hx))
  have hsLoad' : ∀ x ∈ loadCalls, x ∈ calls := fun x hx => hsub_chk x (hsubM x (hsLoad x hx))
  let cS : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, lim⟩
  have hcS : Core.ScopedCoreFacts cS := hstep.inv.scopedCoreFacts
  have htmM := htmS.mono hextM
  obtain ⟨a, dom, us, ha, hpi, hhead⟩ := Decl.scopedCalleesSpec cS hcS .rec_to_parent_addr _ _ _
    _ _ evScan _ _ _ _ _ rfl (Core.CoreGood.ofRaw (hgood.sub hsScan') (fun _ _ => trivial)) E' htmM
  have hkr : Core.KeysResolved E' := (htmM 0 (fun _ => .sort .zero)).keysResolved
  have hne : cS.κ (Core.ixAddr a) ≠ Core.unresolvedKey :=
    keysResolved_getAppFn (keysResolved_piDomAt _ hkr hpi) hhead
  have hkey : cS.κ (Core.ixAddr a) = Core.keyOf t (Core.ixAddr a) := cS.key_eq hne
  have hhead' := hhead
  rw [hkey] at hhead'
  have hmajA : majorKey rc E' = some (keyOf t (Core.ixAddr a)) :=
    majorKey_of_piDomAt (by rw [← hsum]; exact hpi) hhead'
  obtain ⟨tyP', E'', htyP', hann', hmajP⟩ := htie
  have htyEq : tyP' = tyP := Except.ok.inj (htyP'.symm.trans htyP)
  subst htyEq
  have hkeys : keyOf t P = keyOf t (Core.ixAddr a) :=
    Option.some.inj (hmajP.symm.trans ((majorKey_annotates_eq (rc := rc) hann' hann).trans hmajA))
  have hPa : P = Core.ixAddr a := keyOf_inj hroles hkeys
  subst hPa
  have hgL : Core.Good ⟨E, env, t, lim⟩ loadCalls := hgood.sub hsLoad'
  obtain ⟨rawP, cP, hhP, hbaP, hexP, -, hresP⟩ := L1.get_ci_block_trace_spec hgL.2 ha evLoad
  have hrecP : recordOf E (Core.ixAddr a) = some cm := by
    rw [recordOf_eq_recordAt_of_decoded hst.decoded]
    exact hcm
  obtain ⟨lc, hget, hdec⟩ := LoadedReads.recordOf_inv hrecP
  have hbP : rawP = lc.rawBytes := Core.load_escape hget hgL.1 rawP hhP hbaP
  have hcP : cP = cm := by
    rw [hbP, hdec] at hexP
    exact (Except.ok.inj hexP).symm
  subst hcP
  unfold L1.GetCIBlockTraceResult at hresP
  rw [hcmi] at hresP
  obtain ⟨-, blkBytes, cb', ms', ind', blobs', tree', plan', v₀, hhB', haB', hexB', hcb', hms',
    -, -, -, hld₀, hraw, -⟩ := hresP
  have hrecB : recordOf E ip.block = some cb := by
    rw [recordOf_eq_recordAt_of_decoded hst.decoded]
    exact hcb
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hrecB
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hgL.1 blkBytes hhB' haB'
  have hcbEq : cb' = cb := by
    rw [hbB, hdecB] at hexB'
    exact (Except.ok.inj hexB').symm
  subst hcbEq
  have hmsEq : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hms)
  subst hmsEq
  have hlist : ms'.toList[ip.idx.toNat]? = ms'[ip.idx.toNat]? := by simp
  rw [hlist, hind] at hms'
  have hindEq : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj hms')
  subst hindEq
  obtain ⟨hlvlsP, hpP, hiP, hcP56, hidxP, -⟩ := hraw
  exact ⟨hlvls, hrules_lt, hlvlsP, hpP, hiP, hcP56, hidxP⟩

/-- **The bounds at the arm**: `recArmRunBounds_of_obs` at `RecArmRun`. -/
theorem recArmRunBounds_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hnat : RecArmRun calls t A lim) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind)) :
    RecArmRunBounds rc ip ind :=
  recArmRunBounds_of_obs ht hS hst hc hinfo hnat.obs hinert hcover hstep hcm hcmi htie hcb hms
    hind

/-- **The bounds at the walk's arm, at any limit**: `recArmRunBounds_of_obs` at
`Claim.RecArmLimAt`, the arm `Claim.TopWalkCore.recArm` exports. -/
theorem recArmRunBounds_of_limArm {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (harm : Claim.RecArmLimAt calls bAddr t A lim) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind)) :
    RecArmRunBounds rc ip ind :=
  recArmRunBounds_of_obs ht hS hst hc hinfo (recArmObs_of_lim harm) hinert hcover hstep hcm hcmi
    htie hcb hms hind

end IxVM.Refinement.Typing
