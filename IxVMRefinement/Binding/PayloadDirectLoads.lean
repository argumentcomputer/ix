import IxVMRefinement.Binding.RootSafety
import IxVMRefinement.Binding.PayloadAdvice
import IxVMRefinement.FamilyGraph.InnerChecked
import IxVMRefinement.Callees.Modeled
import IxVMRefinement.Lib.Lists
import IxVMRefinement.Obs.KernelModeled
import IxVMRefinement.Obs.KernelClaim

/-! # What a family check's own loads give of the records it names

The records a family check names directly are its family record, its advice records and its
container recursors. Their checks load them, and these loads give the payload's facts at them
(`PayloadFactsOn` at `PayDirect`):

* **The family record.** `KernelModeled::family_recs` loads it (`Ingress::load_verified_constant`)
  and has two arms: a block of recursors (`muts_recr_count` against the length) and a recursor
  record. For a block it builds the members' projection addresses (`Ingress::build_recur_addrs`,
  which hashes each projection record, `build_recur_addrs_hashed`). `KernelModeled::check_recs`
  then loads every one of these addresses (`Ingress::get_ci`) and asserts the loaded recursor's
  unsafe flag `0` (`check_recs_safe`). So the family record is a record of the run's store, a
  block of recursors or a recursor record, in Lean's logic, and a block's member projection
  records are the store's (`familyCall_record_facts`).
* **An advice record.** `KernelModeled::check_advice_record` admits a safe definition, a theorem,
  a safe recursor (`is_unsafe` asserted `0`), a projection record, or a block. A block is one
  inductive type with its flag `0` (`muts_all_safe`), whose member `0` is checked
  (`check_muts_all`): the projection address is hashed, the loaded record is checked, and the
  check's `Induct` arm runs the block's member-kind check and hashes every constructor projection
  (`Claim.MemberCheckObs`, `MemberCheckObs.records`, `MemberCheckObs.block_kinds`). So an advice
  record is in Lean's logic, and an advice block's projection records are the store's
  (`adviceCheck_logic`, `adviceCheck_block`).
* **A container recursor.** `KernelModeled::rec_family_block` loads it with `Ingress::get_ci`, so it
  is no block (`containerRecIn_notBlock`), and a projection record among them is at a member's
  address of its block (`proj_member_of_load`).

The role context of these checks plays no part: a family check nested in another's calls runs
under a context the run's records do not pin. -/

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

variable {calls : List (Call F)} {E₀ : Ixon.Env}

/-- **An observed check of member `k` of the block at `addr`, under any role context**:
`MemberCheckedLimAt` without the role context's representation and the calls' membership. -/
def MemberCheckObs (calls : List (Call F)) (addr : _root_.Address) (ms : Array Ixon.MutConst)
    (k : Nat) : Prop :=
  ∃ (h_pa h_pre m_chk h'_chk : Heap F)
    (rc x_members x_block ap ptr v r_chk : SourceValue F)
    (cs_pa cs_load cs_chk : List (Call F)),
    Specs.Callees.MembersRep h_pa ms.toList x_members ∧
    S0.addr h_pa x_block addr ∧
    ObsFn Obs.W "Ingress::projection_addr" [x_members, x_block, .field (k : F)] h_pa ap h_pre
      cs_pa ∧
    (∀ cl ∈ cs_pa, cl ∈ calls) ∧
    ObsFn Obs.W "Ingress::get_ci" [ap] h_pre ptr m_chk cs_load ∧
    (∀ cl ∈ cs_load, cl ∈ calls) ∧
    loadValue m_chk ptr = .ok v ∧
    ObsFn Obs.W "KernelCheck::check_const" [rc, v, ap] m_chk r_chk h'_chk cs_chk ∧
    (∀ cl ∈ cs_chk, cl ∈ calls)

/-- The walk's check of a member is a check of it under some role context. -/
theorem MemberCheckedLimAt.obs {bAddr B : _root_.Address} {t : Ix.Kernel.RoleTable}
    {ms : Array Ixon.MutConst} {k : Nat} {lim : Option Nat}
    (hm : MemberCheckedLimAt calls bAddr t B ms k lim) : MemberCheckObs calls B ms k := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, -, hsub_pa,
    -, -, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hm
  exact ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, hsub_pa, ev_ld, hsub_ld, hld, ev_chk, hsub_chk⟩

/-- **The check of member `0` of a block, under any role context, runs the block's member-kind
check** (`member_zero_block_kinds_of`). -/
theorem MemberCheckObs.block_kinds (hS : LoadedReads.RunStore calls E₀) {B : _root_.Address}
    {ms : Array Ixon.MutConst} (hm : MemberCheckObs calls B ms 0) : BlockKindsChecked calls B := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, hsub_pa, ev_ld, hsub_ld, hld, ev_chk,
    hsub_chk⟩ := hm
  exact member_zero_block_kinds_of hS hmem hblk ev_pa hsub_pa ev_ld hsub_ld hld ev_chk hsub_chk

/-- **A member checked under any role context has its projection record in the store**, and an
inductive member each of its constructors' projection records (`member_records` without the
context; `t` is any table, the constructors' hashes do not depend on it). -/
theorem MemberCheckObs.records (t : Ix.Kernel.RoleTable) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) {B : _root_.Address} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i : Nat} {m : Ixon.MutConst}
    (hc : recordOf E₀ B = some c) (hms : c.info = .muts ms) (hm : ms[i]? = some m)
    (hchk : MemberCheckObs calls B ms i) :
    recordOf E₀ (memberAddr B i m) = some (memberProjection B i m) ∧
      ∀ ind j, m = .indc ind → j < ind.ctors.size →
        recordOf E₀ (ctorAddr B i j) = some (constructorProjection B i j) := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, hsub_pa, ev_ld, hsub_ld, hld, ev_chk,
    hsub_chk⟩ := hchk
  obtain ⟨b', hb', rfl⟩ := hblk
  obtain ⟨-, -, -, mc, a', hget', ha', hproj, hhashed⟩ :=
    L1.projection_addr_hashed_spec hmem hb' ev_pa
  obtain ⟨iv, hiv⟩ : ∃ iv, ((i : F)).val = iv := ⟨_, rfl⟩
  rw [hiv] at hget' hproj hhashed
  -- the projection record the check loaded is the one `projection_addr` hashed
  obtain ⟨raw, cp, hsz, hh, hba, hx, -, hhead⟩ := get_ci_head ha' ev_ld
  have hrec := recordOf_of_hashed hcov (Core.hashed_mono hsub_ld hh) hsz hx
  have hX : Address.blake3Pure (Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b') iv mc, #[], #[], #[], #[]⟩) =
      Core.ixAddr a' := hproj.symm
  have hraw : raw = Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b') iv mc, #[], #[], #[], #[]⟩ :=
    hS.hashed_inj (Core.hashed_mono hsub_ld hh) (Core.hashed_mono hsub_pa hhashed)
      (hba.trans hX.symm)
  have hwf : (⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b') iv mc, #[], #[], #[], #[]⟩ :
      Ixon.Constant).wireWF := by
    cases mc with
    | defn d => exact L1.projConstant_wireWF_dPrj iv.toUInt64 b'
    | indc ind => exact L1.projConstant_wireWF_iPrj iv.toUInt64 b'
    | recr rc => exact L1.projConstant_wireWF_rPrj iv.toUInt64 b'
  rw [hraw, Ixon.Verify.deConstantExact_serConstant _ hwf] at hx
  injection hx with hcp
  subst hcp
  -- the block the record names was loaded: the member's index is small
  have hblock : ∃ cb ms', BlockLoad cs_load (Core.ixAddr b') cb ms' := by
    cases mc with
    | defn d => obtain ⟨cb, ms', _, hbl, _⟩ := hhead.dPrj _ _ rfl; exact ⟨cb, ms', hbl⟩
    | indc ind => obtain ⟨cb, ms', _, hbl, _⟩ := hhead.iPrj _ _ rfl; exact ⟨cb, ms', hbl⟩
    | recr rc => obtain ⟨cb, ms', _, hbl, _⟩ := hhead.rPrj _ _ rfl; exact ⟨cb, ms', hbl⟩
  obtain ⟨cb, ms', hbl⟩ := hblock
  have hres := ((hbl.mono hsub_ld).record hS hc).2
  have hsize := muts_size_le hms
  have hi : i < ms.size := (Array.getElem?_eq_some_iff.mp hm).1
  have hi' : i < 72057594037927936 := by omega
  have hiv' : iv = i := hiv.symm.trans (L1.val_cast_u56_ing hi')
  clear hiv
  subst iv
  have hmc : mc = m := by
    rw [Array.getElem?_toList] at hget'
    exact Option.some.inj (hget'.symm.trans hm)
  subst mc
  refine ⟨?_, ?_⟩
  · -- the member's projection record
    have hmemb : memberProjection (Core.ixAddr b') i m =
        ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b') i m, #[], #[], #[], #[]⟩ := by
      cases m <;> rfl
    rw [LoadedReads.memberAddr_eq_projAddr, hmemb]
    rw [hraw] at hrec
    exact hrec
  · -- the constructors' projection records, hashed by the member's check
    intro ind j hind hj
    subst hind
    obtain ⟨cb, ms'', ind', hbl', hget'', -, nl, ty, np, ni, x_blk, b'', hld', hb'',
      hb''eq⟩ := hhead.iPrj i.toUInt64 (Core.ixAddr b') rfl
    have hcb := ((hbl'.mono hsub_ld).record hS hc).1
    have hinfo'' : c.info = .muts ms'' := by rw [← hcb]; exact hbl'.info
    have hms'' : ms'' = ms := Ixon.ConstantInfo.muts.inj (hinfo''.symm.trans hms)
    subst ms''
    have htoNat : i.toUInt64.toNat = i :=
      Ixon.Verify.TagN.toUInt64_toNat_of_lt (Nat.lt_trans hi' (by decide))
    rw [htoNat] at hget'' hld'
    have hind : ind' = ind := by
      rw [Array.getElem?_toList, hm] at hget''
      exact (Ixon.MutConst.indc.inj (Option.some.inj hget'')).symm
    subst ind'
    have hv := Except.ok.inj (hld.symm.trans hld')
    subst hv
    have hlen : ind.ctors.toList.length < 72057594037927936 := by
      have := ctors_size_le hms (by rw [Array.getElem?_toList]; exact hm)
      rw [Array.length_toList]
      omega
    have hhash := check_const_induct_ctors_hashed
      (Core.ScopedCtx.unrestricted ⟨E₀, .empty, t, none⟩) hlen hi' hb'' ev_chk j
      (by rw [Array.length_toList]; exact hj)
    rw [hb''eq] at hhash
    exact recordOf_of_hashed hcov (Core.hashed_mono hsub_chk hhash)
      (serConstant_cprj_size_lt i.toUInt64 j.toUInt64 b')
      (Ixon.Verify.deConstantExact_serConstant _ (L1.projConstant_wireWF_cPrj i.toUInt64
        j.toUInt64 b'))

/-- **A projection record the run loaded is at a member's or a constructor's address of its
block**, which the store holds (`proj_member_of_checked` from the load alone). -/
theorem proj_member_of_load (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) {ab : Bytes.Address}
    {ap ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hab : Bytes.RepAddressRef Core.addrTy h ab ap)
    (ev_ld : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs) (hsub_ld : ∀ cl ∈ cs, cl ∈ calls)
    {c : Ixon.Constant} (hc : recordOf E₀ (Core.ixAddr ab) = some c) (hpr : Typing.IsProj c) :
    ∃ cb, recordOf E₀ (Ix.Cert.ownerOf (Core.ixAddr ab) c) = some cb ∧
      Typing.ConstAddrOf (Ix.Cert.ownerOf (Core.ixAddr ab) c) cb (Core.ixAddr ab) := by
  obtain ⟨raw, c', -, hh, hba, hx, htv, hhead⟩ := get_ci_head hab ev_ld
  have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
    (Core.hashed_mono hsub_ld hh) hba hx
  subst c'
  rcases hpr with ⟨⟨idx, blk⟩, hp⟩ | ⟨⟨idx, blk⟩, hp⟩ | ⟨⟨idx, cidx, blk⟩, hp⟩ |
    ⟨⟨idx, blk⟩, hp⟩
  · -- a definition projection
    have hproj : Assembly.IsProjInfo c.info := by rw [hp]; exact True.intro
    obtain ⟨hcanon, hab_eq⟩ := proj_canon hba hx htv hproj
    obtain ⟨cb, ms, d, hbl, hmem⟩ := hhead.dPrj idx blk hp
    obtain ⟨hrec, hinfo⟩ := (hbl.mono hsub_ld).stored hcov
    have hcm : c = memberProjection blk idx.toNat (.defn d) := by
      rw [memberProjection_defn, ← hp]
      exact hcanon
    rw [hcm] at hab_eq ⊢
    rw [Typing.ownerOf_memberProjection]
    exact ⟨cb, hrec, Or.inr ⟨ms, idx.toNat, .defn d, hinfo,
      by rw [← Array.getElem?_toList]; exact hmem, Or.inl hab_eq⟩⟩
  · -- an inductive projection
    have hproj : Assembly.IsProjInfo c.info := by rw [hp]; exact True.intro
    obtain ⟨hcanon, hab_eq⟩ := proj_canon hba hx htv hproj
    obtain ⟨cb, ms, ind, hbl, hmem, -⟩ := hhead.iPrj idx blk hp
    obtain ⟨hrec, hinfo⟩ := (hbl.mono hsub_ld).stored hcov
    have hcm : c = memberProjection blk idx.toNat (.indc ind) := by
      rw [memberProjection_indc, ← hp]
      exact hcanon
    rw [hcm] at hab_eq ⊢
    rw [Typing.ownerOf_memberProjection]
    exact ⟨cb, hrec, Or.inr ⟨ms, idx.toNat, .indc ind, hinfo,
      by rw [← Array.getElem?_toList]; exact hmem, Or.inl hab_eq⟩⟩
  · -- a constructor projection
    have hproj : Assembly.IsProjInfo c.info := by rw [hp]; exact True.intro
    obtain ⟨hcanon, hab_eq⟩ := proj_canon hba hx htv hproj
    obtain ⟨cb, ms, ind, hbl, hmem, hlt, -⟩ := hhead.cPrj idx cidx blk hp
    obtain ⟨hrec, hinfo⟩ := (hbl.mono hsub_ld).stored hcov
    have hcm : c = constructorProjection blk idx.toNat cidx.toNat := by
      rw [constructorProjection_toNat, ← hp]
      exact hcanon
    rw [hcm] at hab_eq ⊢
    rw [Typing.ownerOf_constructorProjection]
    exact ⟨cb, hrec, Or.inr ⟨ms, idx.toNat, .indc ind, hinfo,
      by rw [← Array.getElem?_toList]; exact hmem,
      Or.inr ⟨ind, cidx.toNat, rfl, by rw [← Array.length_toList]; exact hlt, hab_eq⟩⟩⟩
  · -- a recursor projection
    have hproj : Assembly.IsProjInfo c.info := by rw [hp]; exact True.intro
    obtain ⟨hcanon, hab_eq⟩ := proj_canon hba hx htv hproj
    obtain ⟨cb, ms, rc, hbl, hmem, -⟩ := hhead.rPrj idx blk hp
    obtain ⟨hrec, hinfo⟩ := (hbl.mono hsub_ld).stored hcov
    have hcm : c = memberProjection blk idx.toNat (.recr rc) := by
      rw [memberProjection_recr, ← hp]
      exact hcanon
    rw [hcm] at hab_eq ⊢
    rw [Typing.ownerOf_memberProjection]
    exact ⟨cb, hrec, Or.inr ⟨ms, idx.toNat, .recr rc, hinfo,
      by rw [← Array.getElem?_toList]; exact hmem, Or.inl hab_eq⟩⟩

end IxVM.Refinement.Claim

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Reading helpers -/

/-- The number of recursors among a block's members. -/
private def recrCount : List Ixon.MutConst → Nat
  | [] => 0
  | .recr _ :: rest => recrCount rest + 1
  | .defn _ :: rest => recrCount rest
  | .indc _ :: rest => recrCount rest

private theorem recrCount_le : ∀ l : List Ixon.MutConst, recrCount l ≤ l.length
  | [] => Nat.le_refl 0
  | .recr _ :: rest => by
    have := recrCount_le rest
    simp only [recrCount, List.length_cons]
    omega
  | .defn _ :: rest => by
    have := recrCount_le rest
    simp only [recrCount, List.length_cons]
    omega
  | .indc _ :: rest => by
    have := recrCount_le rest
    simp only [recrCount, List.length_cons]
    omega

/-- A member list whose recursor count is its length holds only recursors. -/
private theorem all_recr_of_count :
    ∀ l : List Ixon.MutConst, recrCount l = l.length → ∀ m ∈ l, ∃ r, m = .recr r
  | [], _, m, hm => by cases hm
  | .recr r :: rest, h, m, hm => by
    simp only [recrCount, List.length_cons, Nat.add_right_cancel_iff] at h
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact ⟨r, rfl⟩
    · exact all_recr_of_count rest h m hm'
  | .defn _ :: rest, h, m, hm => by
    have := recrCount_le rest
    simp only [recrCount, List.length_cons] at h
    exfalso
    omega
  | .indc _ :: rest, h, m, hm => by
    have := recrCount_le rest
    simp only [recrCount, List.length_cons] at h
    exfalso
    omega

/-- **`KernelModeled::muts_recr_count`** counts the recursors among the members; no
allocation. -/
private theorem muts_recr_count_spec :
    ∀ {ms : List Ixon.MutConst} {x_members r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)},
      Core.Specs.Callees.MembersRep h ms x_members →
      ObsFn Obs.W "KernelModeled::muts_recr_count" [x_members] h r h' calls →
      r = .field ((recrCount ms : Nat) : F) ∧ h' = h := by
  intro ms
  induction ms with
  | nil =>
    intro x_members r h h' calls hms ev
    cases Obs.«KernelModeled::muts_recr_count».obs ev with
    | Nil _ hr hh _ =>
      subst hr hh
      simp [recrCount]
    | Cons_Recr _ _ _ _ _ ld12 _ _ _ _ | Cons_other _ _ _ ld12 _ _ _ =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hms ld12
      cases he
  | cons m rest ih =>
    intro x_members r h h' calls hms ev
    cases Obs.«KernelModeled::muts_recr_count».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load hms ld12
    | Cons_Recr x_rest w56 x62 m64 cs73 ld12 ev75 hm64 op69 _ =>
      subst hm64
      obtain ⟨z, zs, he, ⟨x, hmc⟩, hzs⟩ := Lib.rep_cons_of_load hms ld12
      injection he with he1 he2
      subst he1 he2
      obtain ⟨rfl, rfl⟩ := ih hzs ev75
      have hr : r = .field (((recrCount rest : Nat) : F) + 1) := by
        simp only [evalBinOp, Except.ok.injEq] at op69
        exact op69.symm
      subst hr
      cases m with
      | recr _ =>
        refine ⟨?_, rfl⟩
        show _ = (.field (((recrCount rest + 1 : Nat) : F)) : SourceValue F)
        rw [Nat.cast_add, Nat.cast_one]
      | defn _ | indc _ =>
        rw [Core.Specs.Callees.mutCtor] at hmc
        injection hmc with _ hc _
        exact absurd hc (by decide)
    | Cons_other x_m x_rest cs93 ld12 hne86 ev95 _ =>
      obtain ⟨z, zs, he, ⟨x, hmc⟩, hzs⟩ := Lib.rep_cons_of_load hms ld12
      injection he with he1 he2
      subst he1 he2
      obtain ⟨rfl, rfl⟩ := ih hzs ev95
      cases m with
      | recr _ => exact (hne86 [x] rfl hmc).elim
      | defn _ => exact ⟨rfl, rfl⟩
      | indc _ => exact ⟨rfl, rfl⟩

/-- A field cast of a number at most `2^56` reads back. -/
private theorem val_cast_le_u56 {n : Nat} (h : n ≤ 72057594037927936) : ZMod.val (n : F) = n :=
  ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)

/-- MembersRep is read off the shapes of the members, which no heap change affects. -/
private theorem mutShape_mono : HeapMono₂ Core.Specs.Callees.MutShape :=
  fun _ _ _ _ _ rep => rep

/-- **`Ingress::build_recur_addrs_walk` hashes the projection record of every member it
walks.** -/
private theorem build_recur_addrs_walk_hashed {ms : List Ixon.MutConst} {b : Bytes.Address} :
    ∀ (cur : List Ixon.MutConst) {k : Nat} {x_all x_blk x_cur r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      k ≤ 72057594037927936 →
      Core.Specs.Callees.MembersRep h ms x_all →
      Bytes.RepAddressRef Core.addrTy h b x_blk →
      Core.Specs.Callees.MembersRep h cur x_cur →
      (∀ j m', cur[j]? = some m' → ms[k + j]? = some m') →
      ObsFn Obs.W "Ingress::build_recur_addrs_walk" [x_all, x_blk, x_cur, .field (k : F)]
        h r h' cs →
      ∀ j m', cur[j]? = some m' → Hashed cs (Ixon.serConstant
        ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b) (k + j) m', #[], #[], #[], #[]⟩) := by
  intro cur
  induction cur with
  | nil =>
    intro k x_all x_blk x_cur r h h' cs _ _ _ _ _ _ j m' hj
    simp at hj
  | cons m rest ih =>
    intro k x_all x_blk x_cur r h h' cs hk hms hb hcur hsuf ev
    rcases Obs.«Ingress::build_recur_addrs_walk».obs ev with
      ⟨ld12, _, _, _⟩ |
      ⟨w36, x_rest, v55, v56, m58, cs66, m94, cs102, v108,
        ld12, he51, hm50, ev68, op143, ev104, hc145⟩
    · cases Lib.rep_nil_of_load hcur ld12
    · obtain ⟨m', rest', he, _, hrest⟩ := Lib.rep_cons_of_load hcur ld12
      injection he with hm_eq hrest_eq
      subst m' rest'
      obtain ⟨ext1, hk_lt, _, mc, a₀, hget_mc, -, -, hhash⟩ :=
        L1.projection_addr_hashed_spec hms hb ev68
      rw [val_cast_le_u56 hk] at hk_lt hget_mc hhash
      have hmc_eq : mc = m := by
        have h0 := hsuf 0 m rfl
        rw [Nat.add_zero, hget_mc] at h0
        exact Option.some.inj h0
      subst mc
      simp only [evalBinOp, Except.ok.injEq] at op143
      have hv108 : v108 = .field (((k + 1 : Nat) : F)) := by
        rw [← op143]; push_cast; rfl
      rw [hv108] at ev104
      have htl := ih (by omega) (hms.mono mutShape_mono ext1)
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ext1 hb)
        (hrest.mono mutShape_mono ext1)
        (fun j m' hj => by
          have hstep := hsuf (j + 1) m' hj
          have hadd : k + 1 + j = k + (j + 1) := by omega
          rwa [hadd])
        ev104
      intro j m' hj
      cases j with
      | zero =>
        obtain rfl : m = m' := by simpa using hj
        exact Core.hashed_mono (fun cl hcl => by rw [hc145]; simp [hcl]) hhash
      | succ j =>
        have h1 := htl j m' (by simpa using hj)
        rw [show k + 1 + j = k + (j + 1) by omega] at h1
        exact Core.hashed_mono (fun cl hcl => by rw [hc145]; simp [hcl]) h1

/-- **`Ingress::build_recur_addrs` hashes the projection record of every member of the
block.** -/
private theorem build_recur_addrs_hashed {ms : List Ixon.MutConst} {b : Bytes.Address}
    {x_members x_block r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hms : Core.Specs.Callees.MembersRep h ms x_members)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block)
    (ev : ObsFn Obs.W "Ingress::build_recur_addrs" [x_members, x_block] h r h' cs) :
    ∀ i m, ms[i]? = some m → Hashed cs (Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b) i m, #[], #[], #[], #[]⟩) := by
  obtain ⟨cs4, ev6, hc38⟩ := Obs.«Ingress::build_recur_addrs».obs ev
  have ev6' : ObsFn Obs.W "Ingress::build_recur_addrs_walk"
      [x_members, x_block, x_members, .field ((0 : Nat) : F)] h r h' cs4 := by
    simpa using ev6
  intro i m hm
  have h1 := build_recur_addrs_walk_hashed ms (k := 0) (Nat.zero_le _) hms hb hms
    (fun j m' hj => by simpa using hj) ev6' i m hm
  rw [Nat.zero_add] at h1
  exact Core.hashed_mono (fun cl hcl => by rw [hc38]; simp [hcl]) h1

/-- Two recursor values that are equal have equal unsafe flags. -/
private theorem rec_flag_eq
    {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ u a₁₀ a₁₁ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ u' b₁₀ b₁₁ : SourceValue F}
    (h : (.construct "KernelTypes::KConstantInfo" "Rec"
        [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, u, a₁₀, a₁₁] : SourceValue F) =
      .construct "KernelTypes::KConstantInfo" "Rec" [b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, u', b₁₀, b₁₁]) :
    u = u' := by
  have e := (Value.construct.inj h).2.2
  have e1 := (List.cons.inj e).2
  have e2 := (List.cons.inj e1).2
  have e3 := (List.cons.inj e2).2
  have e4 := (List.cons.inj e3).2
  have e5 := (List.cons.inj e4).2
  have e6 := (List.cons.inj e5).2
  have e7 := (List.cons.inj e6).2
  have e8 := (List.cons.inj e7).2
  exact (List.cons.inj e8).1

/-! ## The family record -/

section FamilyRecord

variable {calls : List (Call F)} {E₀ : Ixon.Env} {bAddr : _root_.Address}
  {t : Ix.Kernel.RoleTable}

private theorem ext_snocEq {h m : Heap F} {v : SourceValue F} (e : m = h ++ [v]) :
    Heap.Extends h m := by
  rw [e]; exact Heap.Extends.snoc h v

/-- **`KernelModeled::check_recs` loads every recursor address of its list as a recursor with the
unsafe flag `0`.** -/
private theorem check_recs_safe
    {x_rc x_ta x_src x_dst x_aset x_n x_np x_uo x_bnl x_fam : SourceValue F} :
    ∀ (as : List Bytes.Address) {x_recs x_models x_s x_k x_form r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h as x_recs →
      ObsFn Obs.W "KernelModeled::check_recs"
        [x_rc, x_ta, x_recs, x_models, x_src, x_dst, x_aset, x_s, x_n, x_k, x_np, x_uo, x_bnl,
          x_fam, x_form] h r h' cs →
      ∀ b ∈ as, ∃ (x_b p : SourceValue F) (h₁ h₂ : Heap F) (cs₁ : List (Call F))
        (nl ty np ni nm nmin rules kf w₁ w₂ : SourceValue F),
        Bytes.RepAddressRef Core.addrTy h₁ b x_b ∧
        ObsFn Obs.W "Ingress::get_ci" [x_b] h₁ p h₂ cs₁ ∧ (∀ cl ∈ cs₁, cl ∈ cs) ∧
        loadValue h₂ p = .ok (.construct "KernelTypes::KConstantInfo" "Rec"
          [nl, ty, np, ni, nm, nmin, rules, kf, .field 0, w₁, w₂])
  | [], _, _, _, _, _, _, _, _, _, _, _ => fun b hb => nomatch hb
  | a :: rest, x_recs, x_models, x_s, x_k, x_form, r, h, h', cs, hrep, ev => by
    match Obs.«KernelModeled::check_recs».obs ev with
    | .Nil (ld12 := ld12) .. => exact absurd (Lib.rep_nil_of_load hrep ld12) (by simp)
    | .Cons (m561 := m561) (m627 := m627) (m892 := m892) (ld12 := ld12) (ev82 := ev82)
        (ld76 := ld76) (heq217 := heq217) (ev298 := ev298) (ev359 := ev359) (ev345 := ev345)
        (ev403 := ev403) (ev485 := ev485) (ev523 := ev523) (ev571 := ev571) (hm635 := hm635)
        (ev608 := ev608) (ev652 := ev652) (ev681 := ev681) (ev710 := ev710)
        (hm_odcsfbbr := hmA) (ev_uprevpxl := evA) (ev_svgicqcr := evB) (hm_owdmgqhw := hmB)
        (ev_oqkxxxxs := evC) (ev_eejlfykm := evD) (ev_uoyvrvop := evE) (ev_akrqpecc := evF)
        (ev_uoummlhs := evG) (ev_tjosvhyt := evH) (ev850 := ev850) (ev904 := ev904)
        (ev1016 := ev1016) (hc1137 := hc) .. =>
      obtain ⟨z, zs, he, hz, hzs⟩ := Lib.rep_cons_of_load hrep ld12
      injection he with he1 he2
      subst he1 he2
      have e627 : Heap.Extends m561 m627 :=
        (ext_snocEq hmA).trans (evA.heap_extends.trans (evB.heap_extends.trans
          ((ext_snocEq hmB).trans (evC.heap_extends.trans (evD.heap_extends.trans
            (evE.heap_extends.trans (evF.heap_extends.trans (ext_snocEq hm635))))))))
      have ext : Heap.Extends h m892 := by
        refine ev82.heap_extends.trans ?_
        refine ev298.heap_extends.trans ?_
        refine ev359.heap_extends.trans ?_
        refine ev345.heap_extends.trans ?_
        refine ev403.heap_extends.trans ?_
        refine ev485.heap_extends.trans ?_
        refine ev523.heap_extends.trans ?_
        refine ev571.heap_extends.trans ?_
        refine e627.trans ?_
        refine ev608.heap_extends.trans ?_
        refine ev652.heap_extends.trans ?_
        refine ev681.heap_extends.trans ?_
        refine ev710.heap_extends.trans ?_
        refine evG.heap_extends.trans ?_
        refine evH.heap_extends.trans ?_
        refine ev850.heap_extends.trans ?_
        exact ev904.heap_extends
      have htl := check_recs_safe rest
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext hzs) ev1016
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hbr
      · rw [heq217] at ld76
        exact ⟨_, _, h, _, _, _, _, _, _, _, _, _, _, _, _, hz, ev82,
          fun cl hcl => by rw [hc]; simp [hcl], ld76⟩
      · obtain ⟨x_b, p, h₁, h₂, cs₁, nl, ty, np, ni, nm, nmin, rules, kf, w₁, w₂, hxb, evg,
          hsubg, hldg⟩ := htl b hbr
        exact ⟨x_b, p, h₁, h₂, cs₁, nl, ty, np, ni, nm, nmin, rules, kf, w₁, w₂, hxb, evg,
          fun cl hcl => by rw [hc]; simp [hsubg cl hcl], hldg⟩

/-- **The family check's loads of its family record**: `KernelModeled::family_recs` at the record,
and `KernelModeled::check_recs` on the list it returns, at a later heap. -/
private theorem familyCall_recs_obs {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs) :
    ∃ (b : Bytes.Address) (h₁ h₂ h₃ h₄ : Heap F) (x_rb v r₂ : SourceValue F)
      (x_rc x_ta x_models x_src x_dst x_aset x_s x_n x_k x_np x_uo x_bnl x_fam x_form :
        SourceValue F) (cs₁ cs₂ : List (Call F)),
      Core.ixAddr b = rb ∧ Bytes.RepAddressRef Core.addrTy h₁ b x_rb ∧
      ObsFn Obs.W "KernelModeled::family_recs" [x_rb] h₁ v h₂ cs₁ ∧ (∀ cl ∈ cs₁, cl ∈ calls) ∧
      Heap.Extends h₂ h₃ ∧
      ObsFn Obs.W "KernelModeled::check_recs"
        [x_rc, x_ta, v, x_models, x_src, x_dst, x_aset, x_s, x_n, x_k, x_np, x_uo, x_bnl, x_fam,
          x_form] h₃ r₂ h₄ cs₂ ∧ (∀ cl ∈ cs₂, cl ∈ calls) := by
  obtain ⟨h, h', rc, xb, xrb, r, -, -, ⟨b, hb, rfl⟩, ev, -, hsub⟩ := hfc
  match Obs.«KernelModeled::check_family».obs ev with
  | .run (m105 := m105) (m784 := m784) (m840 := m840) (m1293 := m1293) (sg112 := sg112)
      (ev126 := ev126) (ev148 := ev148) (ev194 := ev194) (ev_yqjbwijz := evo) (ev231 := ev231)
      (ev266 := ev266) (ev309 := ev309) (ev344 := ev344) (ev403 := ev403) (ev435 := ev435)
      (ev465 := ev465) (ev513 := ev513) (ev601 := ev601) (ev634 := ev634) (ev664 := ev664)
      (ev686 := ev686) (ev716 := ev716) (ev759 := ev759) (ev817 := ev817) (ev796 := ev796)
      (ev852 := ev852) (ev_ursqbimm := evr) (ev_srfmazjk := evt) (ev874 := ev874) (ev896 := ev896) (ev960 := ev960)
      (ev939 := ev939) (ev1011 := ev1011) (ev990 := ev990) (ev_edyzsqzv := evm1)
      (ev_gkddqxhv := evcc) (ev_ittpynob := evm2) (ev_biaifgpd := evm3) (ev1203 := ev1203)
      (ev_cwwgzxtj := evfl) (ev1246 := ev1246) (ev_mitevvsv := evln) (ev_rqpeovbn := evz1)
      (ev_xrhmaojz := evz2) (ev_whimdwjd := evvg) (ev1305 := ev1305) (ev1343 := ev1343)
      (hc1474 := hc) .. =>
    have e0 : Heap.Extends h m105 := by
      match sg112 with
      | .Nil (ev15 := ev15) (he33 := he33) .. =>
        rw [he33]
        exact ev15.heap_extends
      | .Node (heq97 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
    have e784 : Heap.Extends h m784 := by
      refine e0.trans ?_
      refine ev126.heap_extends.trans ?_
      refine ev148.heap_extends.trans ?_
      refine ev194.heap_extends.trans ?_
      refine evo.heap_extends.trans ?_
      refine ev231.heap_extends.trans ?_
      refine ev266.heap_extends.trans ?_
      refine ev309.heap_extends.trans ?_
      refine ev344.heap_extends.trans ?_
      refine ev403.heap_extends.trans ?_
      refine ev435.heap_extends.trans ?_
      refine ev465.heap_extends.trans ?_
      refine ev513.heap_extends.trans ?_
      refine ev601.heap_extends.trans ?_
      refine ev634.heap_extends.trans ?_
      refine ev664.heap_extends.trans ?_
      refine ev686.heap_extends.trans ?_
      refine ev716.heap_extends.trans ?_
      refine ev759.heap_extends.trans ?_
      refine ev817.heap_extends.trans ?_
      exact ev796.heap_extends
    have e1293 : Heap.Extends m840 m1293 := by
      refine evr.heap_extends.trans ?_
      refine evt.heap_extends.trans ?_
      refine ev874.heap_extends.trans ?_
      refine ev896.heap_extends.trans ?_
      refine ev960.heap_extends.trans ?_
      refine ev939.heap_extends.trans ?_
      refine ev1011.heap_extends.trans ?_
      refine ev990.heap_extends.trans ?_
      refine evm1.heap_extends.trans ?_
      refine evcc.heap_extends.trans ?_
      refine evm2.heap_extends.trans ?_
      refine evm3.heap_extends.trans ?_
      refine ev1203.heap_extends.trans ?_
      refine evfl.heap_extends.trans ?_
      refine ev1246.heap_extends.trans ?_
      refine evln.heap_extends.trans ?_
      refine evz1.heap_extends.trans ?_
      refine evz2.heap_extends.trans ?_
      refine evvg.heap_extends.trans ?_
      exact ev1305.heap_extends
    exact ⟨b, m784, m840, m1293, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
      Bytes.repAddressRef_heapMono₂ Core.addrTy e784 hb, ev852,
      fun cl hcl => hsub cl (by rw [hc]; simp [hcl]), e1293, ev1343,
      fun cl hcl => hsub cl (by rw [hc]; simp [hcl])⟩

/-- **What `KernelModeled::family_recs` reads of the family record**: a record of the run's
store, a recursor record (the list it returns is the record alone) or a block of recursors
(`muts_recr_count` against the length), each member's projection record hashed and the list it
returns their addresses (`Ingress::build_recur_addrs`). -/
private theorem familyRecs_facts (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) {b : Bytes.Address} {x_rb v : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hb : Bytes.RepAddressRef Core.addrTy h b x_rb)
    (ev : ObsFn Obs.W "KernelModeled::family_recs" [x_rb] h v h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∃ c, recordOf E₀ (Core.ixAddr b) = some c ∧
      ((∃ rcr, c.info = .recr rcr ∧
          RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h' [b] v) ∨
        ∃ ms, c.info = .muts ms ∧ c.resourceSize < 8589934592 ∧
          (∀ m ∈ ms.toList, ∃ r, m = .recr r) ∧
          (∀ i m, ms[i]? = some m → Hashed calls (Ixon.serConstant
            ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b) i m, #[], #[], #[], #[]⟩)) ∧
          ∃ as : List Bytes.Address,
            RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h' as v ∧
            as.map Core.ixAddr = ms.toList.mapIdx fun i m =>
              Core.projAddr (Core.Specs.Callees.memberProjInfo (Core.ixAddr b) i m)) := by
  match Obs.«KernelModeled::family_recs».obs ev with
  | .Muts (m2 := m2) (cs12 := cs12) (x_members := x_members) (v100 := v100) (v101 := v101)
      (m103 := m103) (m123 := m123) (cs131 := cs131) (cs146 := cs146) (ev14 := ev14)
      (ev113 := ev113) (ev133 := ev133) (heq142 := heq142) (ev148 := ev148) (hc165 := hc) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    have hsub146 : ∀ cl ∈ cs146, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨cb, ms, hbl, hrep⟩ := Claim.load_block_head hb ev14
    have hbl' := hbl.mono hsub12
    obtain ⟨hrec, hinfo⟩ := hbl'.stored hH
    have hres := (hbl'.record hS hrec).2
    have hsize := Claim.muts_size_le hinfo
    have hmems : Core.Specs.Callees.MembersRep m2 ms.toList x_members :=
      Decl.membersRep_of_repMutConstList hrep
    obtain ⟨hv100, hm103⟩ := muts_recr_count_spec hmems ev113
    subst m103
    have ev' : ObsFn Obs.W (Instance.mk "Lists::length" [.named "Ixon::MutConst" []]).symbol
        [x_members] m2 v101 m123 cs131 := by
      rw [Obs.Names.«Lists::length<Ixon::MutConst>».symbol]; exact ev133
    have hl' : RepList (Instance.mk "Lists::Node" [.named "Ixon::MutConst" []]).symbol
        L1.RepMutConst m2 ms.toList x_members := by
      rw [Obs.Names.«Lists::Node<Ixon::MutConst>».symbol]; exact hrep
    obtain ⟨hv101, hm123⟩ := Lib.Lists.length_spec ev' hl'
    subst m123
    have hlen : ms.toList.length = ms.size := Array.length_toList
    have hcnt : recrCount ms.toList = ms.toList.length := by
      have e : ((recrCount ms.toList : Nat) : F) = ((ms.toList.length : Nat) : F) :=
        Value.field.inj (hv100.symm.trans (heq142.trans hv101))
      have hlt : ms.size < 8589934592 := by omega
      exact Core.ModeledAux.natCast_inj_lt
        (Nat.lt_of_le_of_lt (recrCount_le ms.toList)
          (by rw [hlen]; exact Nat.lt_trans hlt (by decide)))
        (by rw [hlen]; exact Nat.lt_trans hlt (by decide)) e
    have hb2 : Bytes.RepAddressRef Core.addrTy m2 b x_rb :=
      Bytes.repAddressRef_heapMono₂ Core.addrTy ev14.heap_extends hb
    obtain ⟨-, as, has, hmap⟩ := L1.build_recur_addrs_spec hmems hb2 ev148
    have hhash := build_recur_addrs_hashed hmems hb2 ev148
    refine ⟨cb, hrec, Or.inr ⟨ms, hinfo, hres, all_recr_of_count ms.toList hcnt,
      fun i m hm => Core.hashed_mono hsub146 (hhash i m ?_), as, has, hmap⟩⟩
    rw [Array.getElem?_toList]
    exact hm
  | .Recr (m2 := m2) (cs12 := cs12) (m197 := m197) (ev14 := ev14) (he183 := he183)
      (hm182 := hm182) (hm205 := hm205) (hc209 := hc) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨-, bytes, c, hsz, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded hb ev14
    have haddr' : Address.blake3Pure ⟨bytes.toArray⟩ = Core.ixAddr b := haddr
    have hrecb : recordOf E₀ (Core.ixAddr b) = some c := by
      rw [← haddr']
      exact Claim.recordOf_of_hashed hH (Core.hashed_mono hsub12 hh)
        (by simpa only [ByteArray.size, List.size_toArray] using hsz) hexact
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfoRep, -, -, -, -⟩ := cRep
    have hinfo_eq := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
    rw [← hinfo_eq] at hinfoRep
    obtain ⟨rcr, hrc, -⟩ := L1.repConstantInfo_recr_inv hinfoRep
    refine ⟨c, hrecb, Or.inl ⟨rcr, hrc, ?_⟩⟩
    subst hm205
    subst he183
    subst hm182
    have hb' : Bytes.RepAddressRef Core.addrTy
        (m2 ++ [.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Nil" []]) b x_rb :=
      Bytes.repAddressRef_heapMono₂ Core.addrTy
        (ev14.heap_extends.trans (Heap.Extends.snoc m2 _)) hb
    exact Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ Core.addrTy) hb'
      (Lib.rep_store_nil m2)

/-- **The family record of an observed family check**: a record of the run's store in Lean's
logic, a recursor record or a block of recursors whose member projection records are the store's
(module docstring). -/
theorem familyCall_record_facts (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs) :
    ∃ c, recordOf E₀ rb = some c ∧ InLogic c ∧
      ((∃ rcr, c.info = .recr rcr) ∨
        ∃ ms, c.info = .muts ms ∧ (∀ m ∈ ms.toList, ∃ r, m = .recr r) ∧
          ∀ i m, ms[i]? = some m →
            recordOf E₀ (memberAddr rb i m) = some (memberProjection rb i m)) := by
  obtain ⟨b, h₁, h₂, h₃, h₄, x_rb, v, r₂, x_rc, x_ta, x_models, x_src, x_dst, x_aset, x_s, x_n,
    x_k, x_np, x_uo, x_bnl, x_fam, x_form, cs₁, cs₂, rfl, hb, ev_fr, hsub₁, ext, ev_cr, hsub₂⟩ :=
    familyCall_recs_obs hfc
  have hloads := fun (as : List Bytes.Address)
      (has : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h₂ as v) =>
    check_recs_safe as (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext has)
      ev_cr
  rcases familyRecs_facts hS hH hb ev_fr hsub₁ with
    ⟨c, hrec, ⟨rcr, hinfo, has⟩ | ⟨ms, hinfo, hres, hall, hhash, as, has, hmap⟩⟩
  · -- a recursor record: its load in `check_recs` reads its unsafe flag `0`
    refine ⟨c, hrec, ?_, Or.inl ⟨rcr, hinfo⟩⟩
    obtain ⟨x_b, p, h₅, h₆, cs₃, nl, ty, np, ni, nm, nmin, rules, kf, w₁, w₂, hxb, evg, hsubg,
      hldg⟩ := hloads [b] has b (List.mem_singleton_self b)
    obtain ⟨raw, c', -, hh, hba, hx, -, hhead⟩ := Claim.get_ci_head hxb evg
    have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrec)
      (Core.hashed_mono (fun cl hcl => hsub₂ cl (hsubg cl hcl)) hh) hba hx
    subst hcc
    obtain ⟨nl', ty', np', ni', nm', nmin', rules', k', x_a, hldv⟩ := hhead.recr rcr hinfo
    have hu := rec_flag_eq (Except.ok.inj (hldv.symm.trans hldg))
    simp only [InLogic, hinfo]
    exact Assembly.repBoolField_zero_false hu
  · -- a block of recursors: each member's projection, loaded in `check_recs`
    have hmember : ∀ i r, ms[i]? = some (.recr r) →
        recordOf E₀ (memberAddr (Core.ixAddr b) i (.recr r)) =
          some (memberProjection (Core.ixAddr b) i (.recr r)) ∧ r.isUnsafe = false := by
      intro i r hm
      have hm' : ms.toList[i]? = some (.recr r) := by rw [Array.getElem?_toList]; exact hm
      have hi : i < ms.size := (Array.getElem?_eq_some_iff.mp hm).1
      have hsize := Claim.muts_size_le hinfo
      have h1 : (as.map Core.ixAddr)[i]? =
          some (Core.projAddr (Core.Specs.Callees.memberProjInfo (Core.ixAddr b) i (.recr r))) := by
        rw [hmap, List.getElem?_mapIdx, hm']
        rfl
      rw [List.getElem?_map] at h1
      obtain ⟨b', hb', hb'e⟩ := Option.map_eq_some_iff.mp h1
      obtain ⟨x_b, p, h₅, h₆, cs₃, nl, ty, np, ni, nm, nmin, rules, kf, w₁, w₂, hxb, evg, hsubg,
        hldg⟩ := hloads as has b' (List.mem_of_getElem? hb')
      have hsubg' : ∀ cl ∈ cs₃, cl ∈ calls := fun cl hcl => hsub₂ cl (hsubg cl hcl)
      obtain ⟨raw, c', hsz, hh, hba, hx, -, hhead⟩ := Claim.get_ci_head hxb evg
      have hh' := Core.hashed_mono hsubg' hh
      have hraw : raw = Ixon.serConstant
          ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b) i (.recr r), #[], #[], #[], #[]⟩ :=
        hS.hashed_inj hh' (hhash i (.recr r) hm) (hba.trans hb'e)
      have hrecraw := Claim.recordOf_of_hashed hH hh' hsz hx
      have hwf : (⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b) i (.recr r), #[], #[], #[],
          #[]⟩ : Ixon.Constant).wireWF := L1.projConstant_wireWF_rPrj i.toUInt64 b
      rw [hraw, Ixon.Verify.deConstantExact_serConstant _ hwf] at hx
      injection hx with hcp
      subst hcp
      refine ⟨?_, ?_⟩
      · have hmemb : memberProjection (Core.ixAddr b) i (.recr r) =
            ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b) i (.recr r), #[], #[], #[], #[]⟩ :=
          rfl
        rw [LoadedReads.memberAddr_eq_projAddr, hmemb]
        rw [hraw] at hrecraw
        exact hrecraw
      · obtain ⟨cb, ms', rc, hbl, hmem', nl', ty', np', ni', nm', nmin', rules', k', x_blk, b'',
          hldv, -, -⟩ := hhead.rPrj i.toUInt64 (Core.ixAddr b) rfl
        have hcb := ((hbl.mono hsubg').record hS hrec).1
        have hms' : ms' = ms := by
          have e1 : c.info = .muts ms' := by rw [← hcb]; exact hbl.info
          exact Ixon.ConstantInfo.muts.inj (e1.symm.trans hinfo)
        subst hms'
        have hi64 : i < 8589934592 := by omega
        have htoNat : i.toUInt64.toNat = i :=
          Ixon.Verify.TagN.toUInt64_toNat_of_lt (Nat.lt_trans hi64 (by decide))
        rw [htoNat, hm'] at hmem'
        have hrc : r = rc := Ixon.MutConst.recr.inj (Option.some.inj hmem')
        subst hrc
        exact Assembly.repBoolField_zero_false (rec_flag_eq (Except.ok.inj (hldv.symm.trans hldg)))
    refine ⟨c, hrec, ?_, Or.inr ⟨ms, hinfo, hall, fun i m hm => ?_⟩⟩
    · simp only [InLogic, hinfo]
      intro m hm
      obtain ⟨r, rfl⟩ := hall m hm
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
      rw [Array.getElem?_toList] at hi
      exact (hmember i r hi).2
    · have hmL : ms.toList[i]? = some m := by rw [Array.getElem?_toList]; exact hm
      obtain ⟨r, rfl⟩ := hall m (List.mem_of_getElem? hmL)
      exact (hmember i r hm).1

end FamilyRecord

/-! ## Advice records -/

section Advice

variable {calls : List (Call F)} {E₀ : Ixon.Env}

/-- A definition the advice check admits as a safe definition is one the reader accepts. -/
private theorem safetyDecline_of_defn_safe {d : Ixon.Definition}
    (hk : (.construct "Ixon::DefKind" "Definition" [] : SourceValue F) = L1.repDefKindVal d.kind)
    (hs : (.construct "Ixon::DefinitionSafety" "Safe" [] : SourceValue F) =
      L1.repDefSafetyVal d.safety) :
    Ix.Kernel.Reader.safetyDecline d = none := by
  have hkd : d.kind = .defn := by
    cases hkd : d.kind with
    | defn => rfl
    | opaq => rw [hkd] at hk; simp [L1.repDefKindVal] at hk
    | thm => rw [hkd] at hk; simp [L1.repDefKindVal] at hk
  have hsd : d.safety = .safe := by
    cases hsd : d.safety with
    | safe => rfl
    | unsaf => rw [hsd] at hs; simp [L1.repDefSafetyVal] at hs
    | part => rw [hsd] at hs; simp [L1.repDefSafetyVal] at hs
  rw [Ix.Kernel.Reader.safetyDecline, hkd, hsd]
  decide

/-- A definition the advice check admits as a theorem is one the reader accepts. -/
private theorem safetyDecline_of_thm {d : Ixon.Definition}
    (hk : (.construct "Ixon::DefKind" "Theorem" [] : SourceValue F) = L1.repDefKindVal d.kind) :
    Ix.Kernel.Reader.safetyDecline d = none := by
  cases hkd : d.kind with
  | thm =>
    rw [Ix.Kernel.Reader.safetyDecline, hkd]
    cases d.safety <;> decide
  | defn => rw [hkd] at hk; simp [L1.repDefKindVal] at hk
  | opaq => rw [hkd] at hk; simp [L1.repDefKindVal] at hk

/-- A recursor whose represented unsafe flag is `0` is safe. -/
private theorem recr_unsafe_false {h : Heap F} {rcr : Ixon.Recursor}
    {w₁ u w₂ w₃ w₄ w₅ w₆ w₇ w₈ : SourceValue F}
    (hrep : L1.RepRecursor h rcr
      (.construct "Ixon::Recursor" "Mk" [w₁, u, w₂, w₃, w₄, w₅, w₆, w₇, w₈]))
    (hu : u = .field 0) : rcr.isUnsafe = false := by
  obtain ⟨typPtr, rulesPtr, hv, -, -⟩ := hrep
  injection hv with _ _ hargs
  injection hargs with _ hargs
  injection hargs with hu' _
  subst hu
  exact Assembly.repBoolField_zero_false hu'.symm

/-- A record whose info is represented under a tag that is no definition's, recursor's, axiom's or
block's is in Lean's logic. -/
private theorem inLogic_of_tag {h : Heap F} {c : Ixon.Constant} {tag : String}
    {args : List (SourceValue F)}
    (hrep : L1.RepConstantInfo h c.info (.construct "Ixon::ConstantInfo" tag args))
    (hd : tag ≠ "Defn") (hr : tag ≠ "Recr") (ha : tag ≠ "Axio") (hm : tag ≠ "Muts") :
    InLogic c := by
  cases hci : c.info with
  | defn d =>
    rw [hci] at hrep
    obtain ⟨_, hmk, _⟩ := hrep
    exact absurd (Value.construct.inj hmk).2.1 hd
  | recr rr =>
    rw [hci] at hrep
    obtain ⟨_, hmk, _⟩ := hrep
    exact absurd (Value.construct.inj hmk).2.1 hr
  | axio ax =>
    rw [hci] at hrep
    obtain ⟨_, hmk, _⟩ := hrep
    exact absurd (Value.construct.inj hmk).2.1 ha
  | muts ms =>
    rw [hci] at hrep
    obtain ⟨_, hmk, _⟩ := hrep
    exact absurd (Value.construct.inj hmk).2.1 hm
  | quot _ => simp only [InLogic, hci]
  | cPrj _ => simp only [InLogic, hci]
  | rPrj _ => simp only [InLogic, hci]
  | iPrj _ => simp only [InLogic, hci]
  | dPrj _ => simp only [InLogic, hci]

/-- **An advice record that is no block is in Lean's logic**: `check_advice_record` admits a safe
definition, a theorem, a recursor with the unsafe flag `0`, or a projection record. -/
theorem adviceRecord_logic (hS : LoadedReads.RunStore calls E₀)
    {x_rc x_a x_aset x_wset r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {ab : Bytes.Address} (ha : Bytes.RepAddressRef Core.addrTy h ab x_a)
    (ev : ObsFn Obs.W "KernelModeled::check_advice_record" [x_rc, x_a, x_aset, x_wset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    {c : Ixon.Constant} (hc : recordOf E₀ (Core.ixAddr ab) = some c)
    (hnb : ∀ ms, c.info ≠ .muts ms) : InLogic c := by
  match Obs.«KernelModeled::check_advice_record».obs ev with
  | .run (m2 := m2) (cs12 := cs12) (x_info := x_info) (ev14 := ev14)
      (ev_yqjbwijz := ev_ord) (sg952 := sg952) (hc1011 := hc1011) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    obtain ⟨-, bytes, c', -, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ev_ord.heap_extends ha) ev14
    have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
      (Core.hashed_mono hsub12 hh) haddr hexact
    subst hcc
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfoRep, -, -, -, -⟩ := cRep
    have hinfo_eq : x_info = infoVal := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
    rw [← hinfo_eq] at hinfoRep
    match sg952 with
    | .Defn_Definition_Safe (hv81 := hv) .. =>
      rw [hv] at hinfoRep
      obtain ⟨d, hd, typPtr, valPtr, hdv, -, -⟩ := L1.repConstantInfo_defn_inv hinfoRep
      injection hdv with _ _ hargs
      injection hargs with hk hargs
      injection hargs with hs _
      simp only [InLogic, hd]
      exact safetyDecline_of_defn_safe hk hs
    | .Defn_Definition_other (heq258 := heq) .. =>
      exact absurd (Value.field.inj heq) zero_ne_one
    | .Defn_Theorem (hv81 := hv) .. =>
      rw [hv] at hinfoRep
      obtain ⟨d, hd, typPtr, valPtr, hdv, -, -⟩ := L1.repConstantInfo_defn_inv hinfoRep
      injection hdv with _ _ hargs
      injection hargs with hk _
      simp only [InLogic, hd]
      exact safetyDecline_of_thm hk
    | .Defn_Opaque (heq372 := heq) .. =>
      exact absurd (Value.field.inj heq) zero_ne_one
    | .Recr (hv403 := hv) (heq513 := hu) .. =>
      rw [hv] at hinfoRep
      obtain ⟨rcr, hrc, hrep⟩ := L1.repConstantInfo_recr_inv hinfoRep
      simp only [InLogic, hrc]
      exact recr_unsafe_false hrep hu
    | .Muts (hv598 := hv) .. =>
      rw [hv] at hinfoRep
      obtain ⟨ms, hms, -⟩ := L1.repConstantInfo_muts_inv hinfoRep
      exact absurd hms (hnb ms)
    | .IPrj (hv790 := hv) .. =>
      rw [hv] at hinfoRep
      exact inLogic_of_tag hinfoRep (by decide) (by decide) (by decide) (by decide)
    | .CPrj (hv869 := hv) .. =>
      rw [hv] at hinfoRep
      exact inLogic_of_tag hinfoRep (by decide) (by decide) (by decide) (by decide)

/-- `KernelModeled::muts_all_safe` answering `1` reads the first member, an inductive type, with
the unsafe flag `0`. -/
private theorem muts_all_safe_head {h h' : Heap F} {ms : List Ixon.MutConst}
    {x : SourceValue F} {cs : List (Call F)}
    (hrep : RepList Obs.Names.«Lists::Node<Ixon::MutConst>» L1.RepMutConst h ms x)
    (ev : ObsFn Obs.W "KernelModeled::muts_all_safe" [x] h (.field 1) h' cs) :
    ∀ ind, ms.head? = some (.indc ind) → ind.isUnsafe = false := by
  intro ind hhd
  match Obs.«KernelModeled::muts_all_safe».obs ev with
  | .Nil (ld12 := ld) .. =>
    have hnil := Lib.rep_nil_of_load hrep ld
    subst hnil
    simp at hhd
  | .Cons_Indc_n0 (ld12 := ld) .. =>
    obtain ⟨z, zs, hz, hzr, -⟩ := Lib.rep_cons_of_load hrep ld
    subst hz
    simp only [List.head?_cons, Option.some.injEq] at hhd
    subst hhd
    obtain ⟨iv, hiv, typPtr, ctorsPtr, hiv', -, -⟩ := hzr
    have e1 := (List.cons.inj (Value.construct.inj hiv).2.2).1
    rw [hiv'] at e1
    injection e1 with _ _ hargs
    injection hargs with hu _
    exact Assembly.repBoolField_zero_false hu.symm
  | .Cons_Indc_other (he145 := he) .. =>
    exact absurd (Value.field.inj he) one_ne_zero
  | .Cons_other (he153 := he) .. =>
    exact absurd (Value.field.inj he) one_ne_zero

/-- **An advice-record check at a non-empty block record checked the block's member `0`**, under
the advice check's role context (`check_muts_all`'s first step), and the block's first member, an
inductive type, has the unsafe flag `0` (`muts_all_safe`). -/
theorem adviceBlock_memberObs (hS : LoadedReads.RunStore calls E₀)
    {x_rc x_a x_aset x_wset r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {ab : Bytes.Address} (ha : Bytes.RepAddressRef Core.addrTy h ab x_a)
    (ev : ObsFn Obs.W "KernelModeled::check_advice_record" [x_rc, x_a, x_aset, x_wset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    {c : Ixon.Constant} (hc : recordOf E₀ (Core.ixAddr ab) = some c) {ms : Array Ixon.MutConst}
    (hms : c.info = .muts ms) (h0 : ms.size ≠ 0) :
    Claim.MemberCheckObs calls (Core.ixAddr ab) ms 0 ∧
      ∀ ind, ms.toList.head? = some (.indc ind) → ind.isUnsafe = false := by
  match Obs.«KernelModeled::check_advice_record».obs ev with
  | .run (m2 := m2) (cs12 := cs12) (x_info := x_info) (cs947 := cs947) (ev14 := ev14)
      (ev_yqjbwijz := ev_ord) (sg952 := sg952) (hc1011 := hc1011) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    have hsub947 : ∀ cl ∈ cs947, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    obtain ⟨msPtr, hxm, hlist, -⟩ :=
      Decl.load_block_info hS (Bytes.repAddressRef_heapMono₂ Core.addrTy ev_ord.heap_extends ha)
        ev14 hsub12 hc hms
    have ext1 : Heap.Extends h m2 := ev_ord.heap_extends.trans ev14.heap_extends
    match sg952 with
    | .Defn_Definition_Safe (hv81 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Defn_Definition_other (hv81 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Defn_Theorem (hv81 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Defn_Opaque (hv81 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Recr (hv403 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .IPrj (hv790 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .CPrj (hv869 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Muts (x_members := xm) (cs742 := csm) (hv598 := hv) (ev629 := ev629) (ev649 := ev649)
        (ev683 := ev683) (ev723 := ev723) (heq738 := heq738) (ev744 := evm) (hc784 := hcs) .. =>
      have hxe : xm = msPtr := (List.cons.inj (Value.construct.inj (hv.symm.trans hxm)).2.2).1
      subst xm
      have ext2a : Heap.Extends m2 _ := ev629.heap_extends.trans (ev649.heap_extends.trans
        ev683.heap_extends)
      have hflag : ∀ ind, ms.toList.head? = some (.indc ind) → ind.isUnsafe = false := by
        rw [heq738] at ev723
        exact muts_all_safe_head (RepLinkedList.mono L1.repMutConst_heapMono₂ ext2a hlist) ev723
      have ext2 : Heap.Extends m2 _ := ext2a.trans ev723.heap_extends
      have hsubm : ∀ cl ∈ csm, cl ∈ calls := fun cl hcl => hsub947 cl (by rw [hcs]; simp [hcl])
      have hlist2 := RepLinkedList.mono L1.repMutConst_heapMono₂ ext2 hlist
      have hmems := Decl.membersRep_of_repMutConstList hlist2
      have ha2 := Bytes.repAddressRef_heapMono₂ Core.addrTy (ext1.trans ext2) ha
      refine ⟨?_, hflag⟩
      rcases Obs.«KernelClaim::check_muts_all».obs evm with
        ⟨ld12, -⟩ |
        ⟨x_m, x_rest, v42, m43, cs53, cs99, v106, ld12, ev55, op148, ev101, hc150⟩
      · have hnil := Lib.rep_nil_of_load hlist2 ld12
        exact absurd (show ms.size = 0 by rw [← Array.length_toList, hnil]; rfl) h0
      · have hsub53 : ∀ cl ∈ cs53, cl ∈ calls :=
          fun cl hcl => hsubm cl (by rw [hc150]; simp [hcl])
        obtain ⟨v1, mpa, cspa, vci, mchk, pci, csld, cschk, evpa, evld, ldci, evchk, hcm⟩ :=
          Obs.«KernelClaim::check_muts_member_at».obs ev55
        have hsubpa : ∀ cl ∈ cspa, cl ∈ calls :=
          fun cl hcl => hsub53 cl (by rw [hcm]; simp [hcl])
        have hsubld : ∀ cl ∈ csld, cl ∈ calls :=
          fun cl hcl => hsub53 cl (by rw [hcm]; simp [hcl])
        have hsubchk : ∀ cl ∈ cschk, cl ∈ calls :=
          fun cl hcl => hsub53 cl (by rw [hcm]; simp [hcl])
        exact ⟨_, mpa, mchk, _, x_rc, msPtr, x_a, v1, pci, vci, _, cspa, csld, cschk, hmems,
          ⟨ab, ha2, rfl⟩, by rw [Nat.cast_zero]; exact evpa, hsubpa, evld, hsubld, ldci, evchk,
          hsubchk⟩

/-- **An advice block of an observed advice-record check is in Lean's logic, and its member and
constructor projection records are the store's** (module docstring). -/
theorem adviceCheck_block (t : Ix.Kernel.RoleTable) (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) {a : _root_.Address}
    (hadv : AdviceCheckObs calls a) {c : Ixon.Constant} (hc : recordOf E₀ a = some c)
    {ms : Array Ixon.MutConst} (hms : c.info = .muts ms) :
    InLogic c ∧ ∀ i m, ms[i]? = some m →
      recordOf E₀ (memberAddr a i m) = some (memberProjection a i m) ∧
      ∀ ind j, m = .indc ind → j < ind.ctors.size →
        recordOf E₀ (ctorAddr a i j) = some (constructorProjection a i j) := by
  obtain ⟨x_rc, x_a, x_aset, x_wset, r, h, h', cs, ab, hab, rfl, ev, hcs⟩ := hadv
  by_cases h0 : ms.size = 0
  · have hnil : ms.toList = [] :=
      List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; exact h0)
    refine ⟨?_, fun i m hm => ?_⟩
    · simp only [InLogic, hms]
      intro m hm
      rw [hnil] at hm
      simp at hm
    · rw [← Array.getElem?_toList, hnil] at hm
      simp at hm
  · obtain ⟨ind, rfl⟩ := Decl.adviceBlock_shape (lim := none) hS hab ev hcs hc hms h0
    obtain ⟨hobs, hflag⟩ := adviceBlock_memberObs hS hab ev hcs hc hms h0
    have hsafe : ind.isUnsafe = false := hflag ind rfl
    refine ⟨?_, fun i m hm => ?_⟩
    · obtain ⟨x, rr, h₁, h₂, cs₁, hx, evk, hsubk⟩ := Claim.MemberCheckObs.block_kinds hS hobs
      exact Assembly.block_inLogic_of_member_kinds hS hx evk hsubk
        ((hS.recordOf_eq_recordAt _).symm.trans hc) hms
        ⟨.indc ind, by simp, (show Assembly.MemberHasLogic (.indc ind) from Or.inl hsafe)⟩
    · have hi : i = 0 := by
        have := (Array.getElem?_eq_some_iff.mp hm).1
        simp at this
        omega
      subst hi
      exact Claim.MemberCheckObs.records t hS hH hc hms hm hobs

/-- **An advice record of an observed advice-record check is in Lean's logic.** -/
theorem adviceCheck_logic (t : Ix.Kernel.RoleTable) (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) {a : _root_.Address}
    (hadv : AdviceCheckObs calls a) {c : Ixon.Constant} (hc : recordOf E₀ a = some c) :
    InLogic c := by
  by_cases hb : ∃ ms, c.info = .muts ms
  · obtain ⟨ms, hms⟩ := hb
    exact (adviceCheck_block t hS hH hadv hc hms).1
  · obtain ⟨x_rc, x_a, x_aset, x_wset, r, h, h', cs, ab, hab, rfl, ev, hcs⟩ := hadv
    exact adviceRecord_logic hS hab ev hcs hc (fun ms hms => hb ⟨ms, hms⟩)

end Advice

/-! ## Container recursors -/

section Container

variable {calls : List (Call F)} {E₀ : Ixon.Env} {bAddr : _root_.Address}
  {t : Ix.Kernel.RoleTable}

/-- **A container recursor of an observed family check is no block**: `rec_family_block` loads it
with `Ingress::get_ci`, which has no arm for a block. -/
theorem containerRecIn_notBlock (hS : LoadedReads.RunStore calls E₀) {B rb : _root_.Address}
    {lim : Option Nat} {cs : List (Call F)}
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs) {x : _root_.Address}
    (hx : ContainerRecIn cs x) {c : Ixon.Constant} (hc : recordOf E₀ x = some c) :
    ∀ ms, c.info ≠ .muts ms := by
  obtain ⟨h, h', ab, ap, ptr, cs', args, hab, rfl, ev, hsub, -⟩ := containerRecIn_load hfc hx
  obtain ⟨raw, c', -, hh, hbl, hde, -, hhead⟩ := Claim.get_ci_head hab ev
  have e : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
    (Core.hashed_mono hsub hh) hbl hde
  subst e
  exact hhead.notMuts

/-- **A container recursor of an observed family check that is a projection record is at a
member's address of its block**, which the store holds (`Claim.proj_member_of_load` at the load of
`rec_family_block`). -/
theorem containerRecIn_projMember (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs)
    {x : _root_.Address} (hx : ContainerRecIn cs x) {c : Ixon.Constant}
    (hc : recordOf E₀ x = some c) (hp : IsProj c) :
    ∃ cb, recordOf E₀ (Ix.Cert.ownerOf x c) = some cb ∧ ConstAddrOf (Ix.Cert.ownerOf x c) cb x := by
  obtain ⟨h, h', ab, ap, ptr, cs', args, hab, rfl, ev, hsub, -⟩ := containerRecIn_load hfc hx
  exact Claim.proj_member_of_load hS hH hab ev hsub hc hp

end Container

end IxVM.Refinement.Binding
