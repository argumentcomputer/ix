import IxVMRefinement.Assembly.TypingRecLateElim
import IxVMRefinement.StatementRel.LoadedReadsWalked
import IxVMRefinement.Obs.KernelModeled0

/-! # The parent of a late recursor in the run's store

The reading of a recursor record (`RecReads`) names the inductive heading its major premise by
`IndKeyAt` over the run's store `E₀`: the parent's projection record and its block record must
be records of `E₀`, not only of the step's store. Both are loaded by the circuit's check of the
record: the parent's projection record by the route's `get_ci`, its block by the route's
`block_is_modeled`, each a verified load whose bytes the run hashed. A store that holds every
record the run hashed (`LoadedReads.HashedRecordsStored`, the claim layer's) holds both.

* `block_is_modeled_verified_subcall`: `block_is_modeled` begins with its verified load;
* `rec_route_block_of_arm`: `rec_arm_of_arm`'s derivation, keeping the route's
  `block_is_modeled` run at the parent's block pointer and the parent's record facts;
* `rec_major_indKeyAt`: the parent's projection and block records in `E₀`, and the parent's key
  an inductive's key there (`IndKeyAt`), at member `ip.idx` of block `ip.block`.
-/

universe u

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam NativeFamStored)

/-- **`block_is_modeled` begins with its verified load of the block.** -/
theorem block_is_modeled_verified_subcall {bq r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (observed : ObsFn Obs.W "KernelModeled::block_is_modeled" [bq] h r h' calls) :
    ∃ value middle children,
      ObsFn Obs.W "Ingress::load_verified_constant" [bq] h value middle children ∧
      ∀ call ∈ children, call ∈ calls := by
  match Obs.«KernelModeled::block_is_modeled».obs observed with
  | .Muts_n0 (ev14 := loaded) (hc118 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩
  | .Muts_n1 (ev14 := loaded) (hc241 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩
  | .Muts_other (ev14 := loaded) (hc248 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩
  | .other (ev14 := loaded) (hc255 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩

/-- **The parent's records in the run's store, and its key an inductive's key there.** At the
tied parent `P` (record `iPrj ip` in the step's store, block `cb` in Lean's logic, member `ind`):
the run's store holds the parent's projection record and its block record, and the parent's key
is `IndKeyAt` member `ip.idx` of block `ip.block` over the run's store. The derivation is
`rec_arm_of_arm`'s; the records come from the route's parent load and its `block_is_modeled`
run, each a verified load within the calls. -/
theorem rec_major_indKeyAt {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) (hlim : lim = some n)
    (hnat : NativeRecArm calls bAddr t A n) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind)) (hlogic : InLogic cb) :
    recordOf E₀ P = some cm ∧ recordOf E₀ ip.block = some cb ∧
      IndKeyAt t (recordOf E₀) (keyOf t P) ip.block ip.idx.toNat ind := by
  subst hlim
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hgood : Core.Good ⟨E, env, t, some n⟩ calls := hst.good env (some n)
  have hbound : Bounded calls := hgood.2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hstep.ext, hstep.refs, hstep.fresh⟩) hinert
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, -, hrcM, ha_pre, -, ev_ld, hsub_ld,
    hld, ev_chk, hsub_chk⟩ := hnat
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
    rty, -, -, hrulesTr⟩ := htr
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
  obtain ⟨sB, sA, mH, sR, sCs, mCs, hextS, evS, hmemS, hextM, evM, hsubM⟩ :=
    check_const_rec_route ev_chk
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
  have htmS := Decl.tmC_stored_of_usedRefs (E₀ := E) (env := env) (lim := some n) rty
    (recr_typ_usedRefs hinfo) hstored htm
  rw [Decl.posOf_range] at htmS
  have hsum : ZMod.val ((rc.params.toNat : F) + (rc.motives.toNat : F) + (rc.minors.toNat : F) +
      (rc.indices.toNat : F)) =
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat := by
    rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
    exact ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  obtain ⟨parent, pointer, scanHeap, loadedHeap, routedHeap, scanCalls, loadCalls, routeCalls,
    nl, pty, np, ni, nc, pu, blk, idx, lenHeap, lenAfter, kHeap, kAfter, canonHeap, len, kTarget,
    lenCalls, kCalls, canonCalls, _canonResult, _canonFinal, evScan, hsScan, evLoad, hsLoad, hldP,
    evRoute, hsRoute, hnp, hni, eLen, evLen, hsLen, hlenEq, eK, evK, hsK, hkEq, eC, evCanon,
    hsCanon⟩ :=
    native_rec_member_full evM
  have hsScan' : ∀ x ∈ scanCalls, x ∈ calls := fun x hx => hsub_chk x (hsubM x (hsScan x hx))
  have hsLoad' : ∀ x ∈ loadCalls, x ∈ calls := fun x hx => hsub_chk x (hsubM x (hsLoad x hx))
  let cS : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, some n⟩
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
  have hgL : Core.Good ⟨E, env, t, some n⟩ loadCalls := hgood.sub hsLoad'
  obtain ⟨rawP, cP, hhP, hbaP, hexP, htvP, hresP⟩ := L1.get_ci_block_trace_spec hgL.2 ha evLoad
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
  obtain ⟨hlvlsP, hpP, hiP, hcP56, hidxP, tyPtrP, blkPtrP, bP, hbPa, hblkP, hvP, -⟩ := hraw
  subst hvP
  have hldP0 := hld₀
  rw [hld₀] at hldP
  injection hldP with hvP'
  injection hvP' with _ _ hpf
  simp only [List.cons.injEq, and_true] at hpf
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpf
  -- the parent's projection record in the run's store
  obtain ⟨c1, hrec1⟩ := LoadedReads.recordAt_of_get_ci hcov ⟨a, ha, rfl⟩ evLoad hsLoad'
  have hc1 : c1 = cP :=
    Option.some.inj ((hst.runRecord _ _ (hS.recordOf_of_recordAt hrec1)).symm.trans hcm)
  rw [hc1] at hrec1
  have hrecP₀ : recordOf E₀ (Core.ixAddr a) = some cP := hS.recordOf_of_recordAt hrec1
  -- the parent's block record in the run's store, from the route's verified block load
  obtain ⟨vB, midB, chB, verB, hsubB⟩ := block_is_modeled_verified_subcall evRoute
  obtain ⟨-, bytesB, c2, hszB2, hhB2, haddrB2, hexB2, hdeB2, -⟩ :=
    L1.load_verified_constant_decode_bounded hblkP verB
  have hsubB' : ∀ cl ∈ chB, cl ∈ calls :=
    fun cl hm => hsub_chk cl (hsubM cl (hsRoute cl (hsubB cl hm)))
  obtain ⟨lcB2, hgetB2, -, hcB2⟩ := hcov ⟨bytesB.toArray⟩ c2 (Core.hashed_mono hsubB' hhB2)
    (by simpa only [ByteArray.size, List.size_toArray] using hszB2) hdeB2 hexB2
  have haddrB2' : Address.blake3Pure ⟨bytesB.toArray⟩ = Core.ixAddr bP := haddrB2
  have hrecB₀' : Ix.Cert.recordAt E₀ (Core.ixAddr bP) = some c2 := by
    unfold Ix.Cert.recordAt
    rw [← haddrB2', hgetB2]
    exact hcB2
  rw [hbPa] at hrecB₀'
  have hc2 : c2 = cb' :=
    Option.some.inj ((hst.runRecord _ _ (hS.recordOf_of_recordAt hrecB₀')).symm.trans hcb)
  rw [hc2] at hrecB₀'
  have hrecB₀ : recordOf E₀ ip.block = some cb' := hS.recordOf_of_recordAt hrecB₀'
  -- the parent's record is the member's projection record, at the member's address
  obtain ⟨hcmP, haP⟩ := LoadedReads.iprj_canonical ind hexP htvP hcmi
  have haddrP : Core.ixAddr a = memberAddr ip.block ip.idx.toNat (.indc ind) :=
    hbaP.symm.trans haP
  refine ⟨hrecP₀, hrecB₀, ?_⟩
  unfold IndKeyAt MemberAt
  exact ⟨Core.ixAddr a, cP, ip, cb', ms', rfl, hrecP₀, hcmi, rfl, rfl,
    hrecB₀, hms, hind, hcmP, haddrP, hlogic⟩

end IxVM.Refinement.Typing
