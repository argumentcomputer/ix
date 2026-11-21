import IxVMRefinement.StatementRel.LoadedReadsChecked
import IxVMRefinement.Ingress.TraceRecords

/-! # Readings of block members, over the claim walk and the core's projection loads

A block's members are constants at the addresses of their projection records. The walk checks
a block by checking each member at the address it computes for the member's projection
record (`Claim.MutsMemberCheckedAtFull`); the core loads an inductive type or a constructor
of a block by the block's address and the member's position (`Ingress::get_ci_iprj`,
`Ingress::get_ci_cprj`), without the projection record.

* `mutsMember_record`: a checked member's projection record is in the run's store, at the
  member's constant address. The run hashed the record's canonical bytes when it computed the
  address, and loaded bytes with that address; in the run's store these are one byte string.
* `mutsMember_ind_reads`: a checked inductive member has its reading there.
* `mutsMember_defn`: a checked member of a definition block has its check evidence and its
  reading, for one declaration (as `checkedAtFull_defn`).
* `get_ci_iprj_reads`, `get_ci_cprj_reads`: what the core's projection loads return
  represents the reading of the member at its constant address, where the store holds the
  member's projection record.
* `walkedClaim_ind_reads`: every inductive member of a walked block has its reading over the
  claim phase's store.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

private theorem toUInt64_toNat' {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

/-- **The run's store holds every record the run hashed**: a byte string the run hashed,
below `2^32` bytes, that decodes exactly is stored under its address. The claim phase's
store is one (`hashedRecordsStored_of_walkedClaim`). -/
def HashedRecordsStored (calls : List (Call F)) (E : Ixon.Env) : Prop :=
  ∀ (bytes : ByteArray) (c : Ixon.Constant), Hashed calls bytes → bytes.size < 4294967296 →
    Ixon.deConstant bytes = .ok c → Ixon.deConstantExact bytes = .ok c →
    ∃ lc, E.consts.get? (Address.blake3Pure bytes) = some lc ∧ lc.rawBytes = bytes ∧
      lc.get? = some c

theorem hashedRecordsStored_of_walkedClaim {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {seeds : List _root_.Address} (hw : Claim.WalkedClaim calls t E₀ seeds) :
    HashedRecordsStored calls E₀ := by
  obtain ⟨bAddr, -, -, -, -, hcov, -⟩ := hw
  exact hcov

section Walked

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E : Ixon.Env}

/-- **The store holds a record at every address the run loaded a constant from.** -/
theorem recordAt_of_get_ci (hcov : HashedRecordsStored calls E) {a : _root_.Address}
    {addr ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : Core.BaseSeams.addr h addr a) (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) : ∃ c, Ix.Cert.recordAt E a = some c := by
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨value, middle, children, verified, vsub⟩ := Ingress.get_ci_verified_subcall ev
  obtain ⟨-, bytes, c, hsz, hh, haddr, hex, hde, -⟩ :=
    Ingress.load_verified_constant_decode_bounded ha' verified
  obtain ⟨lc, hget, -, hc⟩ := hcov ⟨bytes.toArray⟩ c
    (Core.hashed_mono (fun cl hm => hsub cl (vsub cl hm)) hh)
    (by simpa only [ByteArray.size, List.size_toArray] using hsz) hde hex
  have haddr' : Address.blake3Pure ⟨bytes.toArray⟩ = Core.ixAddr a' := haddr
  refine ⟨c, ?_⟩
  unfold Ix.Cert.recordAt
  rw [← haddr', hget]
  exact hc

/-- **A checked block member's projection record is in the run's store, at the member's
constant address**, and the member is checked there. -/
theorem mutsMember_record (hbound : Bounded calls) (hS : RunStore calls E)
    (hcov : HashedRecordsStored calls E) {bAddr B : _root_.Address}
    {ms : Array Ixon.MutConst} {k : Nat} {mc : Ixon.MutConst}
    (hm : Claim.MutsMemberCheckedAtFull calls bAddr t B ms k) (hk : ms[k]? = some mc) :
    k < UInt64.size ∧ Claim.CheckedAtFull calls bAddr t (memberAddr B k mc) ∧
      Ix.Cert.recordAt E (memberAddr B k mc) = some (memberProjection B k mc) := by
  obtain ⟨lim, h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, hcl_pa, hsub_pa,
    hrc_pre, hrc_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hm
  have hlen : ms.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbound hcl_pa (List.Mem.head _) hmem
  have hk_lt : k < ms.toList.length := by
    have hk_sz : k < ms.size := (Array.getElem?_eq_some_iff.mp hk).1
    simpa using hk_sz
  have hk_val : ((k : F)).val = k :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  obtain ⟨b', hb', rfl⟩ := hblk
  obtain ⟨-, -, -, mc', a', hget', ha', hproj, hhashed⟩ :=
    Ingress.projection_addr_hashed_spec hmem hb' ev_pa
  rw [hk_val] at hget' hproj hhashed
  have hget_list : ms.toList[k]? = some mc := by simpa using hk
  rw [hget_list] at hget'
  cases hget'
  have haddr : Core.BaseSeams.addr h_pre ap (memberAddr (Core.ixAddr b') k mc) :=
    ⟨a', ha', hproj.trans (memberAddr_eq_projAddr _ k mc).symm⟩
  have hchk : Claim.CheckedAtFull calls bAddr t (memberAddr (Core.ixAddr b') k mc) :=
    ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
      hrc_pre, hrc_m, haddr, Core.BaseSeams.addr_mono ev_ld.heap_extends haddr,
      ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩
  obtain ⟨c, hrec⟩ := recordAt_of_get_ci hcov haddr ev_ld hsub_ld
  have hwf : (memberProjection (Core.ixAddr b') k mc).wireWF := by
    cases mc with
    | defn d => exact Ingress.projConstant_wireWF_dPrj k.toUInt64 b'
    | indc ind => exact Ingress.projConstant_wireWF_iPrj k.toUInt64 b'
    | recr rc => exact Ingress.projConstant_wireWF_rPrj k.toUInt64 b'
  have hdx := Ixon.Verify.deConstantExact_serConstant _ hwf
  have hhashed' : Hashed calls (Ixon.serConstant (memberProjection (Core.ixAddr b') k mc)) := by
    have hrun := Core.hashed_mono hsub_pa hhashed
    cases mc <;> exact hrun
  have hc_eq : memberProjection (Core.ixAddr b') k mc = c :=
    hS.record_eq hrec hhashed' rfl hdx
  rw [← hc_eq] at hrec
  refine ⟨?_, hchk, hrec⟩
  show k < 18446744073709551616
  omega

/-- **A checked inductive member of a block has its reading in the run's store.** The store
holds the block at `B`, in Lean's logic; the walk checked member `k`. -/
theorem mutsMember_ind_reads (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : RunStore calls E) (hcov : HashedRecordsStored calls E) {bAddr B : _root_.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {k : Nat} {ind : Ixon.Inductive}
    (hrecB : Ix.Cert.recordAt E B = some cb) (hmuts : cb.info = .muts ms)
    (hk : ms[k]? = some (.indc ind)) (hlogic : InLogic cb)
    (hm : Claim.MutsMemberCheckedAtFull calls bAddr t B ms k) :
    ∃ ty₀ : Ix.Kernel.Expr .anon,
      (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t B ms)).read ind.typ = .ok ty₀ ∧
      ∀ caps, Reads t E (memberAddr B k (.indc ind))
        (.indInfo ⟨keyOf t (memberAddr B k (.indc ind)), List.range ind.lvls.toNat, ty₀⟩
          caps) := by
  obtain ⟨hk64, hchk, hrec⟩ := mutsMember_record hbound hS hcov hm hk
  obtain ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    bytes, E_ld, hrc_pre, hrc_m, ha_pre, ha_m, hhash_ld, hblake_ld, hload_ld, hL1,
    hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := Assembly.checkedAtFull_loadedRecords hbound hchk
  have hinfo : (memberProjection B k (.indc ind)).info = .iPrj ⟨k.toUInt64, B⟩ := rfl
  obtain ⟨ms', ind', ty₀, h1, h2, -, hty, hreads, -⟩ :=
    loadedRecords_ind_reads (p := ⟨k.toUInt64, B⟩) ht hS hload_ld hsub_ld hhash_ld hblake_ld hL1
      hrec hinfo hrecB hlogic
  have hms : ms' = ms := (Ixon.ConstantInfo.muts.inj (hmuts.symm.trans h1)).symm
  subst hms
  have h2' : ms'[k.toUInt64.toNat]? = some (.indc ind') := h2
  rw [toUInt64_toNat' hk64] at h2'
  have hind : ind' = ind := (Ixon.MutConst.indc.inj (Option.some.inj (hk.symm.trans h2'))).symm
  subst hind
  exact ⟨ty₀, hty, hreads⟩

/-- **A checked member of a definition block**: its check evidence and its reading, for one
declaration under every hint. The store holds the block at `B`, in Lean's logic; the walk
checked member `k`. -/
theorem mutsMember_defn (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : RunStore calls E) (hcov : HashedRecordsStored calls E) {bAddr B : _root_.Address}
    {order_role : List _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {k : Nat} {d : Ixon.Definition} (hrecB : Ix.Cert.recordAt E B = some cb)
    (hmuts : cb.info = .muts ms) (hk : ms[k]? = some (.defn d)) (hlogic : InLogic cb)
    (hnot_role : memberAddr B k (.defn d) ∉ order_role)
    (hm : Claim.MutsMemberCheckedAtFull calls bAddr t B ms k) :
    ∃ ty₀ val₀ : Ix.Kernel.Expr .anon, ∀ hn : Ix.Kernel.ReducibilityHint,
      ∃ decl : Ix.Kernel.Declaration .anon,
        Assembly.CheckedConstOrigin calls t bAddr E order_role decl ∧
        IxVM.Consistency.installs decl =
          [defnConst d.kind
            ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ hn] ∧
        Reads t E (memberAddr B k (.defn d))
          (defnConst d.kind
            ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ hn) := by
  obtain ⟨hk64, hchk, hrec⟩ := mutsMember_record hbound hS hcov hm hk
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hmuts] at hl
    have hmem' : Ixon.MutConst.defn d ∈ ms.toList :=
      List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hk)
    exact hl (.defn d) hmem'
  obtain ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    bytes, E_ld, hrc_pre, hrc_m, ha_pre, ha_m, hhash_ld, hblake_ld, hload_ld, hL1,
    hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := Assembly.checkedAtFull_loadedRecords hbound hchk
  obtain ⟨-, -, v', hld', hraw⟩ := loadedRecords_record hS hsub_ld hhash_ld hblake_ld hL1 hrec
  rw [hld] at hld'
  injection hld' with hvv
  subst hvv
  have hinfo : (memberProjection B k (.defn d)).info = .dPrj ⟨k.toUInt64, B⟩ := rfl
  unfold Ingress.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨hidx, lcB, cb', ms', d', blobs, hgetB, -, -, hexB, -, hcb, hms, hb, raw⟩ := hraw
  obtain ⟨hhB, haB⟩ := hload_ld.1 B lcB hgetB
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub_ld hhB) haB hexB
  subst hcb_eq
  have hms_eq : ms' = ms := (Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hcb)).symm
  subst hms_eq
  have hms' : ms'[k.toUInt64.toNat]? = some (.defn d') := by
    rw [← Array.getElem?_toList]
    exact hms
  rw [toUInt64_toNat' hk64] at hms'
  have hd : d' = d := (Ixon.MutConst.defn.inj (Option.some.inj (hk.symm.trans hms'))).symm
  subst hd
  have hblob := hS.blob_of_table hload_ld hsub_ld hb
  obtain ⟨raw', ty₀, val₀, hty, hval, hreads, -⟩ :=
    dprj_reading (store := recordOf E) (blob := fun x => E.blobs.get? x) ht hk64
      (hS.recordOf_of_recordAt hrecB) hmuts hk hlogic (hS.recordOf_of_recordAt hrec) hblob raw
  obtain ⟨-, -, -, -, hdecl⟩ :=
    checkedDefn_core (E := E) (order_role := order_role)
      (decl_addr := memberAddr B k (.defn d')) ht hbound hnot_role hsafe hrc_m hblob raw' hty hval
      ev_chk hsub_chk
  refine ⟨ty₀, val₀, fun hn => ?_⟩
  obtain ⟨decl, hcco, hinst⟩ := hdecl hn
  exact ⟨decl, hcco, hinst, hreads hn⟩

/-! ## The core's projection loads -/

/-- **What `Ingress::get_ci_iprj` returns represents the reading of the inductive member at
its constant address.** The store holds the block, in Lean's logic, and the member's
projection record (`hproj`: for a walked block, `mutsMember_record`). -/
theorem get_ci_iprj_reads (ht : t.check = .ok ()) (hS : RunStore calls E)
    {b : Aiur.Library.Bytes.Address} {i : F} {bp ptr : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {cb : Ixon.Constant} (hbound : Bounded cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (hb : Aiur.Library.Bytes.RepAddressRef Core.addrTy h b bp)
    (ev : ObsFn Core.W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs)
    (hrecB : Ix.Cert.recordAt E (Core.ixAddr b) = some cb) (hlogic : InLogic cb)
    (hproj : ∀ (ms : Array Ixon.MutConst) (ind : Ixon.Inductive), cb.info = .muts ms →
      ms[ZMod.val i]? = some (.indc ind) →
      recordOf E (memberAddr (Core.ixAddr b) (ZMod.val i) (.indc ind)) =
        some (memberProjection (Core.ixAddr b) (ZMod.val i) (.indc ind))) :
    ∃ (ms : Array Ixon.MutConst) (ind : Ixon.Inductive) (ty₀ : Ix.Kernel.Expr .anon)
      (v : SourceValue F),
      cb.info = .muts ms ∧ ms[ZMod.val i]? = some (.indc ind) ∧ loadValue h' ptr = .ok v ∧
      (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t (Core.ixAddr b) ms)).read
        ind.typ = .ok ty₀ ∧
      (∀ caps, Reads t E (memberAddr (Core.ixAddr b) (ZMod.val i) (.indc ind))
        (.indInfo ⟨keyOf t (memberAddr (Core.ixAddr b) (ZMod.val i) (.indc ind)),
          List.range ind.lvls.toNat, ty₀⟩ caps)) ∧
      (ty₀.looseBVarsBounded 0 = true →
        ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true →
        ∀ caps, ∃ ci,
          StoredAs ci (.indInfo ⟨keyOf t (memberAddr (Core.ixAddr b) (ZMod.val i) (.indc ind)),
            List.range ind.lvls.toNat, ty₀⟩ caps) ∧
          Decl.CIRepExact (Core.keyOf t) h' v ci) := by
  obtain ⟨-, hidx, blkBytes, cb', ms, ind, blobs, v, hhB, haB, hexB, -, hcb, hms, hhp, hld,
    raw⟩ := Ingress.get_ci_iprj_spec hbound hb ev
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub hhB) haB hexB
  subst hcb_eq
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E.blobs.get? x = some bs := by
    intro x bs hmem
    obtain ⟨hh, hx⟩ := hhp (x, bs) hmem
    have hx' : Address.blake3Pure bs = x := hx
    have hrun := hS.blobs bs (Core.hashed_mono hsub hh)
    rw [hx'] at hrun
    exact hrun
  have hmem : ms[ZMod.val i]? = some (.indc ind) := by
    rw [← Array.getElem?_toList]
    exact hms
  have hi : ZMod.val i < UInt64.size := by
    show ZMod.val i < 18446744073709551616
    omega
  obtain ⟨ty₀, hty, hreads, hrep⟩ :=
    ind_reading (store := recordOf E) (blob := fun x => E.blobs.get? x) ht hi
      (hS.recordOf_of_recordAt hrecB) hcb hmem hlogic (hproj ms ind hcb hmem) hblob raw
  exact ⟨ms, ind, ty₀, v, hcb, hmem, hld, hty, hreads, hrep⟩

/-- **What `Ingress::get_ci_cprj` returns represents the reading of the constructor at its
constant address.** The store holds the block, in Lean's logic, and the constructor's
projection record (`hproj`: the run hashes it when it checks the inductive,
`Assembly.indBlockCtor_hashed_of_exact_noCollision`); the block's constructors are stored at
their positions (`hcidx`: `Assembly.indBlockCtorIdx_of_exact_noCollision`). -/
theorem get_ci_cprj_reads (ht : t.check = .ok ()) (hS : RunStore calls E)
    {b : Aiur.Library.Bytes.Address} {i j : F} {bp ptr : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {cb : Ixon.Constant} (hbound : Bounded cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (hb : Aiur.Library.Bytes.RepAddressRef Core.addrTy h b bp)
    (ev : ObsFn Core.W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs)
    (hrecB : Ix.Cert.recordAt E (Core.ixAddr b) = some cb) (hlogic : InLogic cb)
    (hcidx : ∀ (ms : Array Ixon.MutConst) (ind : Ixon.Inductive) (ct : Ixon.Constructor),
      cb.info = .muts ms → ms[ZMod.val i]? = some (.indc ind) →
      ind.ctors[ZMod.val j]? = some ct → ct.cidx.toNat = ZMod.val j)
    (hproj : recordOf E (ctorAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j)) =
      some (constructorProjection (Core.ixAddr b) (ZMod.val i) (ZMod.val j))) :
    ∃ (ms : Array Ixon.MutConst) (ind : Ixon.Inductive) (ct : Ixon.Constructor)
      (ty₀ : Ix.Kernel.Expr .anon) (v : SourceValue F),
      cb.info = .muts ms ∧ ms[ZMod.val i]? = some (.indc ind) ∧
      ind.ctors[ZMod.val j]? = some ct ∧ loadValue h' ptr = .ok v ∧
      (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t (Core.ixAddr b) ms)).read
        ct.typ = .ok ty₀ ∧
      Reads t E (ctorAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j))
        (.ctorInfo ⟨keyOf t (ctorAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j)),
          List.range ct.lvls.toNat, ty₀⟩ ct.params.toNat ct.fields.toNat) ∧
      (ty₀.looseBVarsBounded 0 = true →
        ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true →
        ∃ ci,
          StoredAs ci (.ctorInfo ⟨keyOf t (ctorAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j)),
            List.range ct.lvls.toNat, ty₀⟩ ct.params.toNat ct.fields.toNat) ∧
          Decl.CIRepExact (Core.keyOf t) h' v ci) := by
  obtain ⟨-, hidx, hcidx56, blkBytes, cb', ms, ind, ct, blobs, v, hhB, haB, hexB, -, hcb, hms,
    hct, hhp, hld, raw⟩ := Ingress.get_ci_cprj_spec hbound hb ev
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub hhB) haB hexB
  subst hcb_eq
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E.blobs.get? x = some bs := by
    intro x bs hmem
    obtain ⟨hh, hx⟩ := hhp (x, bs) hmem
    have hx' : Address.blake3Pure bs = x := hx
    have hrun := hS.blobs bs (Core.hashed_mono hsub hh)
    rw [hx'] at hrun
    exact hrun
  have hmem : ms[ZMod.val i]? = some (.indc ind) := by
    rw [← Array.getElem?_toList]
    exact hms
  have hct' : ind.ctors[ZMod.val j]? = some ct := by
    rw [← Array.getElem?_toList]
    exact hct
  have hi : ZMod.val i < UInt64.size := by
    show ZMod.val i < 18446744073709551616
    omega
  have hj : ZMod.val j < UInt64.size := by
    show ZMod.val j < 18446744073709551616
    omega
  obtain ⟨ty₀, hty, hreads, hrep⟩ :=
    ctor_reading (store := recordOf E) (blob := fun x => E.blobs.get? x) ht hi hj
      (hS.recordOf_of_recordAt hrecB) hcb hmem hct' (hcidx ms ind ct hcb hmem hct') hlogic hproj
      hblob raw
  exact ⟨ms, ind, ct, ty₀, v, hcb, hmem, hct', hld, hty, hreads, hrep⟩

/-! ## Over the claim walk -/

/-- **Every inductive member of a walked block has its reading over the run's store.** `E₀`
is the claim phase's store (`LoadedBy calls E₀`, `Claim.WalkedClaim`). -/
theorem walkedClaim_ind_reads (hbound : Bounded calls) {E₀ : Ixon.Env}
    {seeds : List _root_.Address} (hload : LoadedBy calls E₀)
    (hw : Claim.WalkedClaim calls t E₀ seeds) :
    ∃ Wk : _root_.Address → Prop, (∀ a ∈ seeds, Wk a) ∧
      ∀ (B : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (k : Nat)
        (ind : Ixon.Inductive),
        Wk B → Ix.Cert.recordAt E₀ B = some cb → cb.info = .muts ms →
        ms[k]? = some (.indc ind) → InLogic cb →
        ∃ ty₀ : Ix.Kernel.Expr .anon, ∀ caps,
          Reads t E₀ (memberAddr B k (.indc ind))
            (.indInfo ⟨keyOf t (memberAddr B k (.indc ind)), List.range ind.lvls.toNat, ty₀⟩
              caps) := by
  have ht := walkedClaim_tableCheck hw
  have hS := RunStore.of_walkedClaim hload hw
  have hcov := hashedRecordsStored_of_walkedClaim hw
  obtain ⟨bAddr, -, -, -, -, -, Wk, rank, hseeds, -, hchecked⟩ := hw
  refine ⟨Wk, hseeds, fun B cb ms k ind hwk hrecB hmuts hk hlogic => ?_⟩
  obtain ⟨c', hrec', hchk⟩ := hchecked B hwk
  rw [hrecB] at hrec'
  have hcc : cb = c' := Option.some.inj hrec'
  subst hcc
  rcases hchk with ⟨ms', hms', hall⟩ | hchk
  · have hms_eq : ms' = ms := (Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hms')).symm
    subst hms_eq
    have hk_sz : k < ms'.size := (Array.getElem?_eq_some_iff.mp hk).1
    obtain ⟨ty₀, -, hreads⟩ :=
      mutsMember_ind_reads ht hbound hS hcov hrecB hmuts hk hlogic (hall k hk_sz)
    exact ⟨ty₀, hreads⟩
  · obtain ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
      bytes, E_ld, hrc_pre, hrc_m, ha_pre, ha_m, hhash_ld, hblake_ld, hload_ld, hL1,
      hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := Assembly.checkedAtFull_loadedRecords hbound hchk
    obtain ⟨-, -, v', -, hraw⟩ := loadedRecords_record hS hsub_ld hhash_ld hblake_ld hL1 hrecB
    unfold Ingress.RawCIRep at hraw
    rw [hmuts] at hraw
    exact False.elim hraw

/-! ## Seeds

The claim phase refuses a seed outside Lean's logic (`KernelClaim::assert_claimable`), so for
a seed the reading needs nothing beyond the claim phase's own conclusion. -/

/-- A record at an address that is not outside Lean's logic is in Lean's logic. -/
theorem inLogic_of_not_outside {a : _root_.Address} {c : Ixon.Constant}
    (hrec : Ix.Cert.recordAt E a = some c) (h : ¬ OutsideLogicAt E a) : InLogic c :=
  Classical.byContradiction fun hn => h ⟨c, hrec, Or.inl hn⟩

/-- The block of a projection record at an address that is not outside Lean's logic is in
Lean's logic. -/
theorem inLogic_block_of_not_outside {a : _root_.Address} {c cb : Ixon.Constant}
    (hrec : Ix.Cert.recordAt E a = some c)
    (hrecB : Ix.Cert.recordAt E (Ix.Cert.ownerOf a c) = some cb) (h : ¬ OutsideLogicAt E a) :
    InLogic cb :=
  Classical.byContradiction fun hn => h ⟨c, hrec, Or.inr ⟨cb, hrecB, hn⟩⟩

/-- **Every seed that is a standalone definition, theorem or opaque record has its check
evidence and its reading**, from the claim phase's conclusion alone: the store it built, the
walk over it, and its refusal of seeds outside Lean's logic. -/
theorem seed_defn_reads (hbound : Bounded calls) {E₀ : Ixon.Env} {seeds : List _root_.Address}
    (hload : LoadedBy calls E₀) (hw : Claim.WalkedClaim calls t E₀ seeds)
    (hseedOk : ∀ a ∈ seeds, ¬ OutsideLogicAt E₀ a ∧ ¬ InertAt t a) :
    ∃ bAddr : _root_.Address, ∀ a ∈ seeds, ∀ (c : Ixon.Constant) (d : Ixon.Definition)
      (order_role : List _root_.Address),
      Ix.Cert.recordAt E₀ a = some c → c.info = .defn d → a ∉ order_role →
      ∃ ty₀ val₀ : Ix.Kernel.Expr .anon, ∀ hn : Ix.Kernel.ReducibilityHint,
        ∃ decl : Ix.Kernel.Declaration .anon,
          Assembly.CheckedConstOrigin calls t bAddr E₀ order_role decl ∧
          IxVM.Consistency.installs decl =
            [defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn] ∧
          Reads t E₀ a (defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn) := by
  obtain ⟨bAddr, Wk, hseeds, hall⟩ := walkedClaim_defn_reads hbound hload hw
  exact ⟨bAddr, fun a ha c d order_role hrec hinfo hnr =>
    hall a c d order_role (hseeds a ha) hrec hinfo
      (inLogic_of_not_outside hrec (hseedOk a ha).1) hnr⟩

end Walked

end IxVM.Refinement.LoadedReads
