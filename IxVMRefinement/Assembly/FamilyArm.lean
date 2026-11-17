import IxVMRefinement.Assembly.NativeBlockReads
import IxVMRefinement.Decl.ModeledRules
import IxVMRefinement.L1.ByteStream
import IxVMRefinement.Obs.KernelModeled1
import IxVMRefinement.Obs.KernelModeled2

/-! # The family check a modeled block's own arm runs

The walked check of a member of a safe mutual or nested block takes `check_const`'s modeled
`Induct` arm, which ends with `KernelModeled::check_modeled_block(rc, block)`: the block's payload
is read, its first address names the family record `rb`, and `check_family(rc, block, rb)` runs
(circuit stage 2, item 12). This module reads that call off the walk:

* `read_payload_stream`: the payload `read_payload` returns is a byte stream;
* `check_modeled_block_family`: `check_modeled_block` runs `check_family` on the address the
  payload begins with, a call of the run;
* `familyCall_of_member` (Target 0 of the full route): the walk's check of member `k` of a
  modeled block at the group limit `n` ran `check_family [rc, B, rb]` under a role context at
  `n`, with its calls in the run (`FamilyCallAt`).

`ModeledRouteAt` is the mirror of `NativeRouteAt`: every observation of `block_is_modeled` at the
block in the run answers non-zero. -/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The modeled case and the family call -/

/-- **The modeled case**: every observation of the circuit's dispatch on the block in the run
answers non-zero (mutual or nested). -/
def ModeledRouteAt (calls : List (Call F)) (B : _root_.Address) : Prop :=
  ∀ (bp r : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (b : Bytes.Address),
    ObsFn Core.W "KernelModeled::block_is_modeled" [bp] h r h' cs →
    (∀ cl ∈ cs, cl ∈ calls) → Bytes.RepAddressRef Core.addrTy h b bp →
    Core.ixAddr b = B → r ≠ .field 0

/-- **The family check of the block at `B` with the family record at `rb`**, under a role
context at the group limit `lim`: `check_family [rc, B, rb]` observed with calls `cs`, the call
and its calls in the run. -/
def FamilyCallAt (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (B rb : _root_.Address) (lim : Nat) (cs : List (Call F)) : Prop :=
  ∃ (h h' : Heap F) (rc xb xrb r : SourceValue F),
    Claim.RCFullRep t bAddr lim h rc ∧ Core.S0.addr h xb B ∧ Core.S0.addr h xrb rb ∧
    ObsFn Obs.W "KernelModeled::check_family" [rc, xb, xrb] h r h' cs ∧
    (⟨"KernelModeled::check_family", [rc, xb, xrb], h⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs, cl ∈ calls)

/-! ## The payload and `check_modeled_block` -/

/-- **`read_payload` returns a byte stream**, at an extension of the heap. -/
theorem read_payload_stream {x_block r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::read_payload" [x_block] h r h' cs) :
    Heap.Extends h h' ∧ ∃ bytes : List UInt8, L1.Stream h' bytes r := by
  match Obs.«KernelModeled::read_payload».obs ev with
  | .Nil (heq136 := heq136) .. =>
    exact absurd (Value.field.inj heq136) zero_ne_one
  | .other (m14 := m14) (ev26 := ev26) (ev68 := ev68) (he146 := he146) (he147 := he147) .. =>
    subst he146 he147
    have h14 : m14 = h := L1.io_get_info_spec ev26
    subst h14
    obtain ⟨ext, bytes, -, -, hst⟩ := L1.read_finite_byte_stream_spec ev68
    exact ⟨ext, bytes, hst⟩

/-- **`check_modeled_block` runs the family check on the family record its payload names**: the
payload's first address `rb`, represented at the heap of the call, which is in the run. -/
theorem check_modeled_block_family {rc iblk r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::check_modeled_block" [rc, iblk] h r h' calls) :
    ∃ (x_rb : SourceValue F) (rb : Bytes.Address) (m : Heap F) (cs : List (Call F)),
      Heap.Extends h m ∧ Bytes.RepAddressRef Core.addrTy m rb x_rb ∧
      ObsFn Obs.W "KernelModeled::check_family" [rc, iblk, x_rb] m r h' cs ∧
      (⟨"KernelModeled::check_family", [rc, iblk, x_rb], m⟩ : Call F) ∈ calls ∧
      ∀ cl ∈ cs, cl ∈ calls := by
  cases Obs.«KernelModeled::check_modeled_block».obs ev with
  | run m2 cs12 v15 m17 cs25 x_rb w39 cs53 ev27 ev14 ev55 hc80 =>
    obtain ⟨e17, bytes, hst⟩ := read_payload_stream ev27
    obtain ⟨a, -, x_t, x_s2, -, hr, hrep, -, e2, -⟩ := Decl.get_address_spec hst ev14
    injection hr with hr
    injection hr with hxt _
    rw [← hxt] at hrep
    refine ⟨x_rb, a, m2, cs53, e17.trans e2, hrep, ev55, ?_, ?_⟩
    · rw [hc80]; simp
    · intro cl hcl; rw [hc80]; simp [hcl]

/-! ## The arm -/

section Arm

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
  {ind : Ixon.Inductive} {k n : Nat}

/-- **Target 0: the family check a modeled block's arm ran.** The walk's check of member `k` of
the safe modeled block at `B`, at the group limit `n`, ran `check_family [rc, B, rb]` for the
family record `rb` its payload names, under a role context at `n`, with its calls in the run. -/
theorem familyCall_of_member (hbound : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hrecB : recordOf E₀ B = some cb) (hmuts : cb.info = .muts ms) (hlogic : InLogic cb)
    (hk : ms[k]? = some (.indc ind))
    (hrecP : recordOf E₀ (memberAddr B k (.indc ind)) = some (memberProjection B k (.indc ind)))
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    (hmod : ModeledRouteAt calls B) :
    ∃ rb cs, FamilyCallAt calls bAddr t B rb n cs := by
  have hchkA := mutsMemberAt_checkedAt (mc := .indc ind) hbound hchk hk
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_ld, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m, ev_ld, _hcl_ld, hsub_ld, hld, ev_chk, _hcl_chk, hsub_chk⟩ :=
    hchkA
  obtain ⟨a', ha'_ref, ha'_eq⟩ := ha_pre
  have hbound_ld : Bounded cs_ld := RomBound.bounded_mono hbound hsub_ld
  obtain ⟨-, bytes, E_ld, hhash, hblake, hload_ld, hL1⟩ :=
    L1.get_ci_loadedL1_spec hbound_ld ha'_ref ev_ld
  rw [ha'_eq] at hblake
  have hrecP' : Ix.Cert.recordAt E₀ (memberAddr B k (.indc ind)) =
      some (memberProjection B k (.indc ind)) :=
    (hS.recordOf_eq_recordAt _).symm.trans hrecP
  have hrecB' : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrecB
  obtain ⟨-, -, v', hld', hraw⟩ :=
    LoadedReads.loadedL1_record hS hsub_ld hhash hblake hL1 hrecP'
  have hvv : v' = v := Except.ok.inj (hld'.symm.trans hld)
  subst hvv
  have hinfo : (memberProjection B k (.indc ind)).info = .iPrj ⟨k.toUInt64, B⟩ := rfl
  unfold L1.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨-, lcB, cb', ms', ind', blobs, hgetB, -, -, hexB, -, hcb', hms', -, raw⟩ := hraw
  obtain ⟨hhB, haB⟩ := hload_ld.1 _ lcB hgetB
  have hcb_eq : cb' = cb := hS.record_eq hrecB' (Core.hashed_mono hsub_ld hhB) haB hexB
  subst cb'
  have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hmuts)
  subst ms'
  obtain ⟨-, -, -, -, -, tyPtr, blkPtr, b, hb_eq, hbp_m, hv, -⟩ := raw
  subst hv
  have hsafe : ind'.isUnsafe = false := by
    have hl := hlogic
    simp only [IxVM.Consistency.InLogic, hmuts] at hl
    exact (hl (.indc ind') (List.mem_of_getElem? hms')).1
  simp only [L1.repBoolField, hsafe, Bool.false_eq_true, ↓reduceIte] at ev_chk
  match Obs.«KernelCheck::check_const».obs ev_chk with
  | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) ..
  | .Axiom_other_other (hv37 := hv) ..
  | .Defn (hv269 := hv) .. | .Thm (hv526 := hv) ..
  | .Opaque (hv825 := hv) .. | .Quot (hv1076 := hv) ..
  | .Ctor_n0_n0 (hv1941 := hv) .. | .Ctor_n0_other (hv1941 := hv) ..
  | .Ctor_other_n0 (hv1941 := hv) ..
  | .Ctor_other_other (hv1941 := hv) ..
  | .Rec_n0 (hv2631 := hv) .. | .Rec_other (hv2631 := hv) .. =>
    injection hv with _ htag _; exact absurd htag (by decide)
  | .Induct_n0 (m2 := m2) (x_ind_block := xblk)
      (m1283 := m1283) (m1333 := m1333) (m1354 := m1354) (m1376 := m1376)
      (m1396 := m1396) (m1427 := m1427) (m1440 := m1440) (m1470 := m1470)
      (cs1503 := cs_mod)
      (ev14 := ev_iu) (hv1240 := hv_ind) (ev1295 := ev_ws)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev_emb)
      (hm1435 := hm1427) (ev1408 := ev_es) (ev1452 := ev_saf)
      (ev1482 := ev_mk) (ev1505 := ev_mod) (hc1634 := hc) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with hblk _
    subst hblk
    have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc m1283 _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc m1376 _
    have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc m1333 _
    have e_to_1470 : Heap.Extends m_chk m1470 :=
      ev_iu.heap_extends.trans (ev_ws.heap_extends.trans
        (e_1376.trans (e_1354.trans (ev_emb.heap_extends.trans
          (e_1427.trans (ev_es.heap_extends.trans (ev_saf.heap_extends.trans
            ev_mk.heap_extends)))))))
    have hbp := Bytes.repAddressRef_heapMono₂ Core.addrTy e_to_1470 hbp_m
    exact absurd rfl (hmod _ _ _ _ _ b ev_mod
      (fun cl hcl => hsub_chk cl (by rw [hc]; simp [hcl])) hbp hb_eq)
  | .Induct_other_other (hv1240 := hv_ind) (hne1927 := hne_u) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with hiu _
    exact absurd hiu.symm hne_u
  | .Induct_other_n0 (m2 := m2) (x_ind_block := xblk)
      (m1283 := m1283) (m1333 := m1333) (m1354 := m1354) (m1376 := m1376)
      (m1396 := m1396) (m1427 := m1427) (m1440 := m1440) (m1470 := m1470)
      (m1492 := m1492) (m1701 := m1701) (m1745 := m1745) (m1793 := m1793)
      (m1806 := m1806) (cs1907 := cs_mb)
      (ev14 := ev_iu) (hv1240 := hv_ind) (ev1295 := ev_ws)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev_emb)
      (hm1435 := hm1427) (ev1408 := ev_es) (ev1452 := ev_saf)
      (ev1482 := ev_mk) (ev1505 := ev_mod) (ev1663 := ev_fa) (ev1711 := ev_tele)
      (hm1801 := hm1793) (ev1757 := ev_rsl) (ev1818 := ev_mc) (ev1909 := ev_mb)
      (hc1926 := hc) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with hblk _
    subst hblk
    have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc m1283 _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc m1376 _
    have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc m1333 _
    have e_1793 : Heap.Extends m1701 m1793 := by rw [hm1793]; exact Heap.Extends.snoc m1701 _
    have e_to_1806 : Heap.Extends m_chk m1806 :=
      ev_iu.heap_extends.trans (ev_ws.heap_extends.trans
        (e_1376.trans (e_1354.trans (ev_emb.heap_extends.trans
          (e_1427.trans (ev_es.heap_extends.trans (ev_saf.heap_extends.trans
            (ev_mk.heap_extends.trans (ev_mod.heap_extends.trans
              (ev_fa.heap_extends.trans (ev_tele.heap_extends.trans
                (e_1793.trans (ev_rsl.heap_extends.trans ev_mc.heap_extends)))))))))))))
    have hsub_mb : ∀ cl ∈ cs_mb, cl ∈ calls := fun cl hcl =>
      hsub_chk cl (by rw [hc]; simp [hcl])
    obtain ⟨x_rb, rb, m, cs_fam, e_m, hrb, ev_fam, hcl_fam, hsub_fam⟩ :=
      check_modeled_block_family ev_mb
    have e_all : Heap.Extends m_chk m := e_to_1806.trans e_m
    refine ⟨Core.ixAddr rb, cs_fam, m, _, rc, blkPtr, x_rb, r_chk, Claim.RCFullRep.mono e_all hrc_m,
      ⟨b, Bytes.repAddressRef_heapMono₂ Core.addrTy e_all hbp_m, hb_eq⟩, ⟨rb, hrb, rfl⟩,
      ev_fam, hsub_mb _ hcl_fam, fun cl hcl => hsub_mb cl (hsub_fam cl hcl)⟩

end Arm

end IxVM.Refinement.Typing
