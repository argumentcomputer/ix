import IxVMRefinement.StatementRel.LoadedReadsCanonChecked

/-! # The check of a definition record, at the group limit of its role context

`Claim.CheckedAtFull` and `Claim.MutsMemberCheckedAtFull` say that the walk loaded a record
and ran `KernelCheck::check_const` on it under a role context at some group limit. The
limit is existential there, and so is the limit of the evidence `LoadedReads` derives from
them (`checkedAtFull_defn_step`, `mutsMember_defn_step`): nothing in those statements ties
it to the limit of any other check. A step of the typing fold reads the prefix invariant at
one limit, the walk's, so the step needs the evidence at that limit.

`CheckedAtFullAt` and `MutsMemberCheckedAtFullAt` are the same witnesses with the limit
named (`checkedAtFull_iff`, `mutsMemberCheckedAtFull_iff`: the existential forms are their
projections). `checkedAtFullAt_defn_step` and `mutsMemberAt_defn_step` are
`LoadedReads.checkedAtFull_defn_step` and `LoadedReads.mutsMember_defn_step` with the limit
of the evidence the limit of the witness, from the same lemmas, and with two more outputs:

* the evidence is stated for any record store `Ecore` (the store indexes the evidence and
  keys the prefix context; neither reads it for a definition), so that it can be read at the
  store a step runs against rather than at the run's own store;
* the annotations of the stored declaration annotate its readings (`Annotates`), so that
  the stored constant is the declared one, stored (`StoredAs`).
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Consistency

/-! ## The witnesses, at a named limit -/

/-- **The walk's check of the record at `a`, under a role context at the group limit
`lim`**: the body of `Claim.CheckedAtFull` at that limit. -/
def CheckedAtFullAt (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (a : _root_.Address) (lim : Nat) : Prop :=
  ∃ (h_pre m_chk h'_chk : Heap F) (rc ap ptr v r_chk : SourceValue F)
    (cs_load cs_chk : List (Call F)),
    Claim.RCFullRep t bAddr lim h_pre rc ∧
    Claim.RCFullRep t bAddr lim m_chk rc ∧
    Core.S0.addr h_pre ap a ∧
    Core.S0.addr m_chk ap a ∧
    ObsFn Obs.W "Ingress::get_ci" [ap] h_pre ptr m_chk cs_load ∧
    (⟨"Ingress::get_ci", [ap], h_pre⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs_load, cl ∈ calls) ∧
    loadValue m_chk ptr = .ok v ∧
    ObsFn Obs.W "KernelCheck::check_const" [rc, v, ap] m_chk r_chk h'_chk cs_chk ∧
    (⟨"KernelCheck::check_const", [rc, v, ap], m_chk⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs_chk, cl ∈ calls)

theorem checkedAtFull_iff {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {a : _root_.Address} :
    Claim.CheckedAtFull calls bAddr t a ↔ ∃ lim, CheckedAtFullAt calls bAddr t a lim :=
  Iff.rfl

/-- **The walk's check of member `k` of the block `ms` at `addr`, under a role context at
the group limit `lim`**: the body of `Claim.MutsMemberCheckedAtFull` at that limit. -/
def MutsMemberCheckedAtFullAt (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (addr : _root_.Address) (ms : Array Ixon.MutConst) (k : Nat)
    (lim : Nat) : Prop :=
  ∃ (h_pa h_pre m_chk h'_chk : Heap F)
    (rc x_members x_block ap ptr v r_chk : SourceValue F)
    (cs_pa cs_load cs_chk : List (Call F)),
    Core.Specs.Callees.MembersRep h_pa ms.toList x_members ∧
    Core.S0.addr h_pa x_block addr ∧
    ObsFn Obs.W "Ingress::projection_addr" [x_members, x_block, .field (k : F)] h_pa ap h_pre
      cs_pa ∧
    (⟨"Ingress::projection_addr", [x_members, x_block, .field (k : F)], h_pa⟩ : Call F) ∈
      calls ∧
    (∀ cl ∈ cs_pa, cl ∈ calls) ∧
    Claim.RCFullRep t bAddr lim h_pre rc ∧
    Claim.RCFullRep t bAddr lim m_chk rc ∧
    ObsFn Obs.W "Ingress::get_ci" [ap] h_pre ptr m_chk cs_load ∧
    (⟨"Ingress::get_ci", [ap], h_pre⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs_load, cl ∈ calls) ∧
    loadValue m_chk ptr = .ok v ∧
    ObsFn Obs.W "KernelCheck::check_const" [rc, v, ap] m_chk r_chk h'_chk cs_chk ∧
    (⟨"KernelCheck::check_const", [rc, v, ap], m_chk⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs_chk, cl ∈ calls)

theorem mutsMemberCheckedAtFull_iff {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {addr : _root_.Address} {ms : Array Ixon.MutConst} {k : Nat} :
    Claim.MutsMemberCheckedAtFull calls bAddr t addr ms k ↔
      ∃ lim, MutsMemberCheckedAtFullAt calls bAddr t addr ms k lim :=
  Iff.rfl

private theorem toUInt64_toNat_t {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

section Checked

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)}

/-- **A checked block member is checked at its constant address, at the same limit.** -/
theorem mutsMemberAt_checkedAt (hbound : Bounded calls) {bAddr B : _root_.Address}
    {ms : Array Ixon.MutConst} {k : Nat} {mc : Ixon.MutConst} {lim : Nat}
    (hm : MutsMemberCheckedAtFullAt calls bAddr t B ms k lim) (hk : ms[k]? = some mc) :
    CheckedAtFullAt calls bAddr t (memberAddr B k mc) lim := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
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
    L1.projection_addr_hashed_spec hmem hb' ev_pa
  rw [hk_val] at hget' hproj hhashed
  have hget_list : ms.toList[k]? = some mc := by simpa using hk
  rw [hget_list] at hget'
  cases hget'
  have haddr : Core.S0.addr h_pre ap (memberAddr (Core.ixAddr b') k mc) :=
    ⟨a', ha', hproj.trans (LoadedReads.memberAddr_eq_projAddr _ k mc).symm⟩
  exact ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, haddr, Core.S0.addr_mono ev_ld.heap_extends haddr,
    ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩

variable {E₀ : Ixon.Env}

/-- **A checked standalone definition, theorem or opaque record, at the limit of its
check.** `LoadedReads.checkedAtFull_defn_step` with the limit of the evidence named: the
walk checked `a` under a role context at the limit `lim`. The evidence is stated at any
record store `Ecore`; the reading is over the run's store `E₀`; the annotations of the
stored declaration annotate the readings. -/
theorem checkedAtFullAt_defn_step (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) {bAddr a : _root_.Address}
    {order_role : List _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hrec : Ix.Cert.recordAt E₀ a = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hnot_role : a ∉ order_role) {lim : Nat} (hchk : CheckedAtFullAt calls bAddr t a lim)
    (Ecore : Ixon.Env) {env : Ix.Kernel.Env .anon} (hstored : Decl.UsedRefsStored t env c) :
    ∃ (ty₀ val₀ ty' val' : Ix.Kernel.Expr .anon),
      Annotates ty' ty₀ ∧ Annotates val' val₀ ∧
      ∀ hn : Ix.Kernel.ReducibilityHint,
        Decl.CheckedConstOriginAt (Core.Ctx.stored ⟨Ecore, env, t, some lim⟩).κ lim calls t
          bAddr Ecore order_role
          (LoadedReads.defnDecl d.kind ⟨Core.keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn)
          (LoadedReads.defnDecl d.kind ⟨Core.keyOf t a, List.range d.lvls.toNat, ty'⟩ val'
            hn) ∧
        Reads t E₀ a
          (LoadedReads.defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn) ∧
        ∀ E' : Ixon.Env, recordOf E' a = some c →
          (∀ x b, E₀.blobs.get? x = some b → E'.blobs.get? x = some b) →
          ∀ cn ∈ IxVM.Consistency.installs
              (LoadedReads.defnDecl d.kind ⟨Core.keyOf t a, List.range d.lvls.toNat, ty'⟩ val'
                hn),
            Decl.ReloadsAs E' t ⟨cn :: env.consts⟩ cn := by
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hinfo] at hl
    exact hl
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hchk
  obtain ⟨a', ha'_ref, rfl⟩ := ha_pre
  obtain ⟨rawBytes, c', hh, hba, hex, hres⟩ := L1.get_ci_trace_spec ha'_ref ev_ld
  have hc : c = c' := (hS.record_eq hrec (Core.hashed_mono hsub_ld hh) hba hex).symm
  subst hc
  unfold L1.GetCITraceResult at hres
  rw [hinfo] at hres
  obtain ⟨blobs, tree, v', hhp, built, hld', htr⟩ := hres
  rw [hld] at hld'
  injection hld' with hvv
  subst hvv
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hhx' : Hashed cs_load bs := hhx
    have hxa' : Address.blake3Pure bs = x := hxa
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx')
    rw [hxa'] at hrun
    exact hrun
  obtain ⟨raw', ty₀, val₀, hty, hval, hreads, -⟩ :=
    LoadedReads.defn_reading (store := recordOf E₀) (blob := fun x => E₀.blobs.get? x) ht
      (hS.recordOf_of_recordAt hrec) hinfo hlogic hblob htr.toRaw
  obtain ⟨h1, h2, h3, h4, -⟩ :=
    LoadedReads.checkedDefn_core (E := Ecore) (order_role := order_role)
      (decl_addr := Core.ixAddr a') ht hbound hnot_role hsafe hrc_m hblob raw' hty hval ev_chk
      hsub_chk
  have hrecur : L1.defnRecurAddrs d (Core.ixAddr a') = [] := by
    have hf := (L1.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
    simp [L1.defnRecurAddrs, hf]
  rw [hrecur] at htr
  obtain ⟨hnlvls, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, hpT, hpV, hlT, hlV⟩ := htr
  subst hv
  have hagree : L1.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs :=
    L1.BlobReadAgreement.of_mem hblob
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    LoadedReads.annotation_canon ht hnlvls hagree rty built hpT hlT hty h1 h2
  obtain ⟨val', hcV, hannV, htmV⟩ :=
    LoadedReads.annotation_canon ht hnlvls hagree rval built hpV hlV hval h3 h4
  have heT : ∀ i, i ∈ exprRefIdxs d.typ → i ∈ usedRefIdxs c := by
    intro i hi
    unfold usedRefIdxs
    rw [hinfo]
    exact List.mem_append_right _ (List.mem_append_left _ hi)
  have heV : ∀ i, i ∈ exprRefIdxs d.value → i ∈ usedRefIdxs c := by
    intro i hi
    unfold usedRefIdxs
    rw [hinfo]
    exact List.mem_append_right _ (List.mem_append_right _ hi)
  have htmT' := Decl.tmC_stored_of_usedRefs (E₀ := Ecore) (lim := some lim) rty heT hstored htmT
  have htmV' := Decl.tmC_stored_of_usedRefs (E₀ := Ecore) (lim := some lim) rval heV hstored htmV
  refine ⟨ty₀, val₀, ty', val', hannT, hannV, fun hn => ⟨?_, hreads hn, ?_⟩⟩
  · exact LoadedReads.checkedDefn_at (E := Ecore) (order_role := order_role)
      (decl_addr := Core.ixAddr a') hnot_role hsafe hrc_m hnlvls h1 h2 h3 h4 hannT hannV htmT'
      htmV' ev_chk hsub_chk hn
  · intro E' hrec' hblobs cn hcn
    rw [LoadedReads.installs_defnDecl] at hcn
    have hcn' : cn = LoadedReads.defnConst d.kind
        ⟨Core.keyOf t (Core.ixAddr a'), List.range d.lvls.toNat, ty'⟩ val' hn :=
      List.mem_singleton.mp hcn
    subst hcn'
    exact LoadedReads.reloadsAs_defn_cons ht hrec' hinfo hlogic hblobs hty hval h1 h2 h3 h4
      hstored (LoadedReads.canonDefn_eq hcT hcV)

/-- **A checked member of a definition block, at the limit of its check.**
`LoadedReads.mutsMember_defn_step` with the limit of the evidence named: the walk checked
member `k` of the block under a role context at the limit `lim`. As
`checkedAtFullAt_defn_step`, the evidence is stated at any record store `Ecore`, and the
annotations annotate the readings. -/
theorem mutsMemberAt_defn_step (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hcov : LoadedReads.HashedRecordsStored calls E₀)
    {bAddr B : _root_.Address} {order_role : List _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {k : Nat} {d : Ixon.Definition}
    (hrecB : Ix.Cert.recordAt E₀ B = some cb) (hmuts : cb.info = .muts ms)
    (hk : ms[k]? = some (.defn d)) (hlogic : InLogic cb)
    (hnot_role : memberAddr B k (.defn d) ∉ order_role) {lim : Nat}
    (hm : MutsMemberCheckedAtFullAt calls bAddr t B ms k lim)
    (Ecore : Ixon.Env) {env : Ix.Kernel.Env .anon} (hstored : Decl.UsedRefsStored t env cb) :
    ∃ (ty₀ val₀ ty' val' : Ix.Kernel.Expr .anon),
      Annotates ty' ty₀ ∧ Annotates val' val₀ ∧
      ∀ hn : Ix.Kernel.ReducibilityHint,
        Decl.CheckedConstOriginAt (Core.Ctx.stored ⟨Ecore, env, t, some lim⟩).κ lim calls t
          bAddr Ecore order_role
          (LoadedReads.defnDecl d.kind
            ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ hn)
          (LoadedReads.defnDecl d.kind
            ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val' hn) ∧
        Reads t E₀ (memberAddr B k (.defn d))
          (LoadedReads.defnConst d.kind
            ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ hn) ∧
        ∀ E' : Ixon.Env,
          recordOf E' (memberAddr B k (.defn d)) = some (memberProjection B k (.defn d)) →
          recordOf E' B = some cb →
          (∀ x b, E₀.blobs.get? x = some b → E'.blobs.get? x = some b) →
          ∀ cn ∈ IxVM.Consistency.installs
              (LoadedReads.defnDecl d.kind
                ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val'
                hn),
            Decl.ReloadsAs E' t ⟨cn :: env.consts⟩ cn := by
  obtain ⟨hk64, -, hrec⟩ :=
    LoadedReads.mutsMember_record hbound hS hcov (mutsMemberCheckedAtFull_iff.mpr ⟨lim, hm⟩) hk
  have hchk := mutsMemberAt_checkedAt hbound hm hk
  have hmem' : Ixon.MutConst.defn d ∈ ms.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hk)
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hmuts] at hl
    exact hl (.defn d) hmem'
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hchk
  obtain ⟨a', ha'_ref, haddr⟩ := ha_pre
  obtain ⟨rawBytes, c', hh, hba, hex, hres⟩ := L1.get_ci_trace_spec ha'_ref ev_ld
  have hc : memberProjection B k (.defn d) = c' :=
    (hS.record_eq hrec (Core.hashed_mono hsub_ld hh) (hba.trans haddr) hex).symm
  subst hc
  have hinfo : (memberProjection B k (.defn d)).info = .dPrj ⟨k.toUInt64, B⟩ := rfl
  unfold L1.GetCITraceResult at hres
  rw [hinfo] at hres
  obtain ⟨hidx, blkBytes, cb', ms', d', blobs, tree, v', hhB, haB, hexB, hcb, hms, hhp, built,
    hld', htr⟩ := hres
  have hcb_eq : cb = cb' :=
    (hS.record_eq hrecB (Core.hashed_mono hsub_ld hhB) haB hexB).symm
  subst hcb_eq
  have hms_eq : ms = ms' := Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hcb)
  subst hms_eq
  have hms' : ms[k.toUInt64.toNat]? = some (.defn d') := by
    rw [← Array.getElem?_toList]
    exact hms
  rw [toUInt64_toNat_t hk64] at hms'
  have hd : d = d' := Ixon.MutConst.defn.inj (Option.some.inj (hk.symm.trans hms'))
  subst hd
  rw [hld] at hld'
  injection hld' with hvv
  subst hvv
  have htr' : L1.DefnTraceRep cb.refs.toList (L1.defnMemberRecurAddrs d B ms.toList)
      cb.univs.toList cb.sharing.toList blobs tree
      ((L1.mutsRootOffset ms.toList k.toUInt64.toNat : Nat) : F) m_chk d v := htr
  rw [toUInt64_toNat_t hk64] at htr'
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hhx' : Hashed cs_load bs := hhx
    have hxa' : Address.blake3Pure bs = x := hxa
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx')
    rw [hxa'] at hrun
    exact hrun
  obtain ⟨raw', ty₀, val₀, hty, hval, hreads, -⟩ :=
    LoadedReads.dprj_reading (store := recordOf E₀) (blob := fun x => E₀.blobs.get? x) ht hk64
      (hS.recordOf_of_recordAt hrecB) hmuts hk hlogic (hS.recordOf_of_recordAt hrec) hblob
      htr'.toRaw
  obtain ⟨h1, h2, h3, h4, -⟩ :=
    LoadedReads.checkedDefn_core (E := Ecore) (order_role := order_role)
      (decl_addr := memberAddr B k (.defn d)) ht hbound hnot_role hsafe hrc_m hblob raw' hty
      hval ev_chk hsub_chk
  have hrecur : L1.defnMemberRecurAddrs d B ms.toList = [] := by
    have hf := (L1.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
    simp [L1.defnMemberRecurAddrs, hf]
  rw [hrecur] at htr'
  obtain ⟨hnlvls, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, hpT, hpV, hlT, hlV⟩ := htr'
  subst hv
  have hagree : L1.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs :=
    L1.BlobReadAgreement.of_mem hblob
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    LoadedReads.annotation_canon ht hnlvls hagree rty built hpT hlT hty h1 h2
  obtain ⟨val', hcV, hannV, htmV⟩ :=
    LoadedReads.annotation_canon ht hnlvls hagree rval built hpV hlV hval h3 h4
  have hused : ∀ i, i ∈ exprRefIdxs d.typ ++ exprRefIdxs d.value → i ∈ usedRefIdxs cb := by
    intro i hi
    unfold usedRefIdxs
    rw [hmuts]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.defn d, hmem', hi⟩)
  have htmT' := Decl.tmC_stored_of_usedRefs (E₀ := Ecore) (lim := some lim) rty
    (fun i hi => hused i (List.mem_append_left _ hi)) hstored htmT
  have htmV' := Decl.tmC_stored_of_usedRefs (E₀ := Ecore) (lim := some lim) rval
    (fun i hi => hused i (List.mem_append_right _ hi)) hstored htmV
  refine ⟨ty₀, val₀, ty', val', hannT, hannV, fun hn => ⟨?_, hreads hn, ?_⟩⟩
  · exact LoadedReads.checkedDefn_at (E := Ecore) (order_role := order_role)
      (decl_addr := memberAddr B k (.defn d)) hnot_role hsafe hrc_m hnlvls h1 h2 h3 h4
      hannT hannV htmT' htmV' ev_chk hsub_chk hn
  · intro E' hproj' hblock' hblobs cn hcn
    rw [LoadedReads.installs_defnDecl] at hcn
    have hcn' : cn = LoadedReads.defnConst d.kind
        ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val' hn :=
      List.mem_singleton.mp hcn
    subst hcn'
    exact LoadedReads.reloadsAs_member_cons ht hk64 hproj' hblock' hmuts hk hlogic hblobs hty
      hval h1 h2 h3 h4 hstored (LoadedReads.canonDefn_eq hcT hcV)

end Checked

end IxVM.Refinement.Typing
