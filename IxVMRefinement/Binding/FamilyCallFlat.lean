import IxVMRefinement.Binding.FamilyFlatBuild
import IxVMRefinement.Binding.FamilyFlatDerive
import IxVMRefinement.Binding.FamilyFlatWalk
import IxVMRefinement.Binding.FamilyReconMember
import IxVMRefinement.Binding.FamilyCallPremises
import IxVMRefinement.TwinFamily.ProducerRow

/-! # The flattened family of an accepted family check

An accepted `KernelModeled::check_family` of a block `B` with a non-empty family record `r`, at
any limit, gives the conclusion of `TwinFamily.TwinCallFlat`: `FamilyOfBlock`, `RecordFlat` and
`BlockDerivedFlat` over the list `build_flat_block` builds, and the recursors' level count. This
module wires the readings of the family check's events (`FamilyAlias.checkFamily_flatChain`).

* `guardDefnAnswers_of_sub`, `indAnswers_of_sub`: the store answers `block_elim` reads, among the
  calls of the family check alone, where the readings at the addresses those calls load mention
  only their level parameters (`LoadedLevelsDefined` at the check's calls).
* `block_elim_blockElim_sub`: `BlockElim` at the returned offset, the store reads asked among
  part of the run's calls.
* `length_eq_of_nonempty`: a non-empty record has one recursor per entry of the flattened family
  at any limit (the completeness assertion; the empty alternative is excluded by the count).
* `RecordFlatOf`, `BlockLevelsSmall`, `FirstMajorInBlock`, `RecordOrigHeads`, `AuxCarriers`,
  `RecLevelCount`: what is taken of the record, each stated on the store.
* **`familyCall_flat`**: the conclusion of `TwinCallFlat` from an accepted family check.
* `recordFlatAt_originals`, `MemberMajorFacts`, `RecordMajorFacts`,
  `recordOrigHeads_of_majorFacts`: `RecordOrigHeads` from the comparison of each recursor's type
  with the reconstruction at its position (`major_head_of_canonical`).
* **`familyCall_flat_of_majorFacts`**, `FamilyCallFlatPremises`, **`twinCallFlat_of_premises`**:
  the same from `RecordMajorFacts`, and `TwinCallFlat` from the premises of every family check.

Taken, beyond the hypotheses of `TwinCallFlat`: the run is bounded; `LoadedLevelsDefined` at the
family check's calls; the reading of `nested_walk` among them (`NestedWalkSpec`); and the
record facts (`BlockLevelsSmall`, `FirstMajorInBlock`, `RecordMajorFacts`, `AuxCarriers`,
`RecLevelCount`).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option autoImplicit false

namespace IxVM.Refinement.Binding.FamilyCallFlat

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency
open IxVM.Refinement.Core
open IxVM (F)
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.FamilyAlias (CallSub SubCall CheckFamilyChain CheckFamilyFlatChain
  FamilyCallAtLim)
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Binding.FamilyOf
open IxVM.Refinement.Binding.FamilyRecon
open IxVM.Refinement.Binding.FamilyFlatRecord
open IxVM.Refinement.Binding.FamilyFlatBuild (RecLevelsDefined)

/-! ## The store answers among the calls of one family check -/

section Answers

variable {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}

/-- **`GuardDefnAnswers` among part of a run's calls**: the readings at the addresses the calls
`cs` load mention only their level parameters, and `cs` are calls of a bounded run with its
store. -/
theorem guardDefnAnswers_of_sub (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) {cs : List (Call F)} (hcs : ∀ c ∈ cs, c ∈ calls)
    (hlv : LoadedLevelsDefined t E₀ cs) :
    GuardDefnAnswers (IxVM.Consistency.keyOf t) (defnValAt t E₀) cs := by
  intro xa p xnl xty xval xsf xh h m cs' a ha ev hself hsub hld
  obtain ⟨X, hX, hsome, hnone⟩ := defnAt_of_load ht hS hH hbd (hlv hself ha) ha ev
    (fun c hc => hcs c (hsub c hc)) hld
  cases X with
  | none => exact absurd rfl (hnone rfl _)
  | some nv =>
    obtain ⟨n, v⟩ := nv
    obtain ⟨xty', xval', xsf', xh', hci, hn, htm⟩ := hsome n v rfl
    have hargs := (Value.construct.inj hci).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨e1, -, e3, -, -⟩ := hargs
    exact ⟨n, v, defnValAt_of_defnAt hX, e1, hn, e3 ▸ htm⟩

/-- **`IndAnswers` among part of a run's calls**, at the store's readings. -/
theorem indAnswers_of_sub (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) {cs : List (Call F)} (hcs : ∀ c ∈ cs, c ∈ calls)
    (hlv : LoadedLevelsDefined t E₀ cs) :
    IndAnswers cs (IxVM.Consistency.keyOf t) (ReconView.ofStore t E₀) := by
  intro xa p ci h m cs' a ha ev hself hsub hld
  exact indDataAt_of_load ht hS hH hbd (hlv hself ha) ha ev (fun c hc => hcs c (hsub c hc)) hld

/-- **`KernelModeled::block_elim` computes the block's elimination offset**
(`FamilyAlias.block_elim_blockElim`), the store reads asked among the calls `root` of the run
only: the calls of the family check at hand. -/
theorem block_elim_blockElim_sub {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {κ : _root_.Address → KKey}
    (hka : ∀ a, keyAddr t (κ a) = some a) {root : List (Call F)}
    (hD : GuardDefnAnswers κ (defnValAt t E₀) root)
    (hI : GuardIndAnswers κ (indTypeAt t E₀) root)
    (hbd : Bounded calls) (hroot : ∀ c ∈ root, c ∈ calls) (hS : LoadedReads.RunStore calls E₀)
    (hB : FamBlockRecord E₀ B cb ms) (hms_u64 : ms.size < UInt64.size)
    {typeAs : List Bytes.Address} {rc xtA bnl uo : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hsub : CallSub cs root)
    (htypes : typeAs.map ixAddr =
      ms.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B i m))
    (htA : RepList addrListEnum (Bytes.RepAddressRef addrTy) h typeAs xtA)
    (ev : ObsFn Obs.W "KernelModeled::block_elim" [rc, xtA] h (.tuple [bnl, uo]) h' cs) :
    ∃ (ind0 : Ixon.Inductive) (off : Nat),
      ms[0]? = some (.indc ind0) ∧
      ind0.lvls.toNat < 4294967296 ∧
      bnl = .field (ind0.lvls.toNat : F) ∧
      BlockElim t E₀ B off ∧ off ≤ 1 ∧
      uo = .field (off : F) := by
  obtain ⟨a0, restAs, ind0, htyAs, ha0, hms0, hlt, hbnl, -⟩ :=
    FamilyAlias.block_elim_spec hbd hS hB hms_u64 (fun c hc => hroot c (hsub c hc)) htypes htA ev
  obtain ⟨a0', restAs', nl, np, ni, ty, lvl, htyAs', hind, hRS, -, huo⟩ :=
    block_elim_resultSort hka hD hI (RomBound.bounded_mono hbd hroot) hsub htA ev
  obtain ⟨rfl, -⟩ := List.cons.inj (htyAs.symm.trans htyAs')
  obtain ⟨rest, hmem⟩ := FamilyAlias.membersAt_cons_of_block hB hms0
  rw [ha0] at hind
  exact ⟨ind0, _, hms0, hlt, hbnl,
    ⟨iprjAddr B 0, rest, nl, np, ni, ty, lvl, hmem, hind, hRS, rfl⟩, by split <;> omega, huo⟩

end Answers

/-! ## Completeness of a non-empty record -/

/-- **A non-empty family record is complete at any limit**: the family check asserts that the
record has one recursor per entry of the flattened family or, outside a group's validation, is
empty; a record with `n ≠ 0` recursors is not empty, so `n` is the length of the flattened
family, on any representation of it as a list. -/
theorem length_eq_of_nonempty {rc b rb : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {C : CheckFamilyChain rc b rb h h' calls}
    (X : CheckFamilyFlatChain C) {α : Type} {R : Heap F → α → SourceValue F → Prop}
    {xs : List α} {n : Nat} (hn0 : n ≠ 0)
    (hn : C.nRecs = .field (n : F)) (hnlt : n < 18446744069414584321)
    (hxs : RepList flatListEnum R X.mNested xs X.flat)
    (hlen : xs.length < 18446744069414584321) : xs.length = n := by
  obtain ⟨hflen, -⟩ := flat_length X.evLenFlat.obs hxs
  obtain ⟨hc, -⟩ := Lib.is_zero_spec X.evComplete.obs
  obtain ⟨he, -⟩ := Lib.is_zero_spec X.evEmpty.obs
  have hne : C.nRecs ≠ .field 0 := by
    rw [hn]
    intro h0
    have h1 : ((n : Nat) : F) = ((0 : Nat) : F) := by simpa using Value.field.inj h0
    exact hn0 (natCast_inj_small hnlt (by decide) h1)
  rw [ite_eq_right hne] at he
  have h0 := X.opDiff
  have h1 := X.opNot
  have h2 := X.opEmptyOk
  have h3 := X.opSum
  have h4 := X.opProd
  have h5 := X.opOr
  obtain ⟨nv, hnv⟩ : ∃ nv : F, X.notValidates = .field nv := by
    cases hv : X.validates <;> rw [hv] at h1 <;> simp only [evalBinOp, reduceCtorEq] at h1
    exact ⟨_, (Except.ok.inj h1).symm⟩
  rw [he, hnv] at h2
  simp only [evalBinOp, zero_mul, Except.ok.injEq] at h2
  rw [← h2, hc] at h3 h4
  simp only [evalBinOp, add_zero, mul_zero, Except.ok.injEq] at h3 h4
  rw [← h3, ← h4] at h5
  simp only [evalBinOp, sub_zero, Except.ok.injEq] at h5
  have hd : X.diff = .field 0 := by
    by_contra hne'
    rw [ite_eq_right hne'] at h5
    exact absurd (Value.field.inj h5) (by decide)
  rw [hn, hflen, hd] at h0
  simp only [evalBinOp, Except.ok.injEq] at h0
  have hz : ((n : Nat) : F) - ((xs.length : Nat) : F) = 0 := Value.field.inj h0
  exact (natCast_inj_small hnlt hlen (sub_eq_zero.mp hz)).symm

/-! ## What is taken of the record and of the run -/

/-- **The flattened family the family check reads off the record `rb`** for the block `B`: the
block's record facts, its elimination offset `off`, and the list `es` that `build_flat_block`
builds at that offset (`recordFlatAt`), one entry per recursor. -/
structure RecordFlatOf (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) (cb : Ixon.Constant)
    (ms : Array Ixon.MutConst) (off : Nat) (es : List FlatEntry) : Prop where
  block : FamBlockRecord E₀ B cb ms
  elim : BlockElim t E₀ B off
  model : recordFlatAt t E₀ rb crb rs B off = some es
  covers : es.length = rs.size

/-- **The reading of `nested_walk` among part of the calls it is given for.** -/
theorem nestedWalkSpec_mono {κ : _root_.Address → KKey} {V : FlatView} {B : _root_.Address}
    {root cs : List (Call F)} (hw : NestedWalkSpec κ V B root) (hsub : ∀ c ∈ cs, c ∈ root) :
    NestedWalkSpec κ V B cs :=
  fun hb hB hacc ev hself hroot => hw hb hB hacc ev (hsub _ hself) (fun c hc => hsub c (hroot c hc))

/-- **The level parameters `build_flat_originals` writes are below `2^32`**: every type of the
block has fewer than `2^32 - off` level parameters, at the block's elimination offset `off`. -/
def BlockLevelsSmall (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B : _root_.Address) : Prop :=
  ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (off : Nat),
    recordOf E₀ B = some cb → cb.info = .muts ms → BlockElim t E₀ B off →
    ∀ (j : Nat) (ind : Ixon.Inductive), ms[j]? = some (Ixon.MutConst.indc ind) →
      off + ind.lvls.toNat < 4294967296

/-- **The first recursor's major premise is over the block's first type**, in the canonical
reading of its type, at any levels. -/
def FirstMajorInBlock (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) : Prop :=
  ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (rc : Ixon.Recursor) (ind : Ixon.Inductive),
    recordOf E₀ B = some cb → cb.info = .muts ms →
    rs[0]? = some (Ixon.MutConst.recr rc) → ms[0]? = some (Ixon.MutConst.indc ind) →
    ∃ ty d ls, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
        (mutsRoot rs 0) rc.typ = some ty ∧
      binderDomAfter (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        ty = some d ∧
      Ix.Kernel.Expr.getAppFn d = .const (IxVM.Consistency.keyOf t (memberAddr B 0 (.indc ind))) ls

/-- **The first recursors' major premises are over the block's types at the elimination offset's
levels**: recursor `k` below the count of the block's types has its major premise headed by the
`k`-th type of the block at the levels `param (off + j)`, the levels `build_flat_originals`
writes. -/
def RecordOrigHeads (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) : Prop :=
  ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (off : Nat) (es : List FlatEntry),
    RecordFlatOf t E₀ B rb crb rs cb ms off es →
    ∀ (k : Nat) (rc : Ixon.Recursor) (ind : Ixon.Inductive),
      rs[k]? = some (Ixon.MutConst.recr rc) → ms[k]? = some (Ixon.MutConst.indc ind) →
      ∃ ty d, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
          (mutsRoot rs k) rc.typ = some ty ∧
        binderDomAfter (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
          ty = some d ∧
        Ix.Kernel.Expr.getAppFn d =
          .const (IxVM.Consistency.keyOf t (memberAddr B k (.indc ind)))
            ((List.range ind.lvls.toNat).map fun j => .param (off + j))

/-- **Every recursor's motives past the block's own types are over their entries**: motive `j`
of a recursor of the record, at a position `j` of an auxiliary entry of the flattened family, has
that entry's type as its carrier (`KernelModeled::check_carriers` reads only the motives of the
block's own types). -/
def AuxCarriers (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) : Prop :=
  ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (off : Nat) (es : List FlatEntry),
    RecordFlatOf t E₀ B rb crb rs cb ms off es →
    ∀ (k : Nat) (rc : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr rc) →
      ∀ (j : Nat) (a : _root_.Address), ms.size ≤ j →
        (es.map FlatEntry.addr)[j]? = some a →
        ∃ n, motiveCarrierAt crb rc j n = some a

/-- **Every recursor of the record has the block's level count plus the elimination offset**
(`KernelCheck::check_recursor_canonical_at` asserts `nlvls = block_nlvls + univ_offset`). -/
def RecLevelCount (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B : _root_.Address)
    (rs : Array Ixon.MutConst) : Prop :=
  ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (off : Nat),
    recordOf E₀ B = some cb → cb.info = .muts ms → BlockElim t E₀ B off →
    ∀ (ind₀ : Ixon.Inductive) (k : Nat) (rc : Ixon.Recursor),
      ms[0]? = some (Ixon.MutConst.indc ind₀) → rs[k]? = some (Ixon.MutConst.recr rc) →
      rc.lvls.toNat = ind₀.lvls.toNat + off

/-! ## The flattened family of an accepted family check -/

/-- **The positional flattened family of an accepted family check.** -/
theorem familyCall_flat {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B r : _root_.Address} {cr : Ixon.Constant}
    {rs : Array Ixon.MutConst} {lim : Option Nat} {cs : List (Call F)}
    (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hR : FamRecRecord E₀ r cr rs) (hsz : rs.size ≠ 0)
    (hlogic : ∀ cb, recordOf E₀ B = some cb → InLogic cb)
    (hfc : FamilyCallAtLim calls bAddr t B r lim cs)
    (hlv : LoadedLevelsDefined t E₀ cs)
    (hnested : NestedWalkSpec (IxVM.Consistency.keyOf t) (FlatView.ofStore t E₀) B cs)
    (hsmall : BlockLevelsSmall t E₀ B)
    (hfirst : FirstMajorInBlock t E₀ B r cr rs)
    (hheads : RecordOrigHeads t E₀ B r cr rs)
    (hauxc : AuxCarriers t E₀ B r cr rs)
    (hlvls : RecLevelCount t E₀ B rs) :
    ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (es : List FlatEntry) (off : Nat),
      FamilyOfBlock E₀ B cb ms r cr rs (es.map FlatEntry.addr) ∧
      RecordFlat t E₀ r cr rs es ∧ BlockDerivedFlat t E₀ B off es ∧
      ∀ (ind₀ : Ixon.Inductive) (k : Nat) (rc : Ixon.Recursor),
        ms[0]? = some (.indc ind₀) → rs[k]? = some (.recr rc) →
        rc.lvls.toNat = ind₀.lvls.toNat + off := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hinj : Function.Injective (IxVM.Consistency.keyOf t) :=
    FamilyFlatBuild.keyOf_injective' htwf
  obtain ⟨cb, ms, hcb, hms, hpos, hall, hmemb⟩ :=
    FamilyOfCall.familyCall_block_members hS hH hfc
  have hB : FamBlockRecord E₀ B cb ms :=
    FamilyOfCall.famBlockRecord_of_call hS hH hfc hcb hms (hlogic cb hcb)
      (FamilyCallPremises.familyCall_block_ctors hS hH hfc hcb hms)
  have hlvR := FamilyFlatBuild.recLevelsDefined_of_call ht hbd hS hH hfc hR
  have hfc0 := hfc
  obtain ⟨h, h', rcV, xb, xrb, res, hrc, ⟨bB, hbB, hBeq⟩, ⟨bR, hbR, hReq⟩, ev, hself, hsub⟩ := hfc
  subst hBeq hReq
  obtain ⟨C, ⟨X⟩⟩ := FamilyAlias.checkFamily_flatChain ev
  -- the store answers among the family check's calls
  have hbdcs : Bounded cs := RomBound.bounded_mono hbd hsub
  have hD : GuardDefnAnswers (IxVM.Consistency.keyOf t) (defnValAt t E₀) cs :=
    guardDefnAnswers_of_sub ht hS hH hbd hsub hlv
  have hIA : IndAnswers cs (IxVM.Consistency.keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_of_sub ht hS hH hbd hsub hlv
  have hGI : GuardIndAnswers (IxVM.Consistency.keyOf t) (indTypeAt t E₀) cs :=
    guardIndAnswers_of_indAnswers hIA
  -- the block's type addresses
  have ext_0_453 : Heap.Extends h C.m453 :=
    (check_family_seg1_extends C.sg112).trans C.ext_m105_m453
  obtain ⟨msPtr, hxm, hlist, hmslt⟩ := Decl.load_block_info hS
    (Bytes.repAddressRef_heapMono₂ addrTy ext_0_453 hbB) C.evLoadBlk.obs
    (fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl)) hB.record hB.muts
  have hxe := (List.cons.inj (Value.construct.inj hxm).2.2).1
  rw [← hxe] at hlist
  have ext_501_652 : Heap.Extends C.m501 C.m652 :=
    C.evLenMem.extends.trans (C.evIndcCnt.extends.trans C.evNParams.extends)
  have hmems652 : Core.Specs.Callees.MembersRep C.m652 ms.toList C.members :=
    Route.membersRep_of_repMutConstList (hlist.mono L1.repMutConst_heapMono₂ ext_501_652)
  have hb652 : Bytes.RepAddressRef addrTy C.m652 bB xb :=
    Bytes.repAddressRef_heapMono₂ addrTy
      (ext_0_453.trans (C.evLoadBlk.extends.trans ext_501_652)) hbB
  obtain ⟨-, typeAs, htA, htypes⟩ := L1.build_recur_addrs_spec hmems652 hb652 C.evTypes.obs
  have ext_674 : Heap.Extends C.m674 C.mRecsVal :=
    C.evTypeMods.extends.trans (C.evCtors.extends.trans (C.evLenCtors.extends.trans
      (C.evCtorMods.extends.trans (C.evRecs.extends.trans (C.evNoRole.extends.trans
        (C.evNoTypeRole.extends.trans (C.evLenRecs.extends.trans (C.evRecMods.extends.trans
          (C.evSrcTail.extends.trans (C.evSrc.extends.trans (C.evDstTail.extends.trans
            (C.evDst.extends.trans (C.evTysVal.extends.trans (C.evLater.extends.trans
              (C.evCtorsVal.extends.trans C.evRecsVal.extends)))))))))))))))
  -- the elimination offset
  obtain ⟨ind0, off, hms0, hlt0, hbnl, helim, hoff1, huo⟩ :=
    block_elim_blockElim_sub (keyAddr_keyOf htwf) hD hGI hbd hsub hS hB
      (Nat.lt_trans hmslt (by decide)) (fun cl hcl => C.evBlockElim.sub cl hcl) htypes
      (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) ext_674 htA)
      C.evBlockElim.obs
  -- the list `build_flat_block` builds
  have hprim : primaryAt t E₀ (ixAddr bR) cr rs (ixAddr bB) = some (ixAddr bB) :=
    FamilyFlatBuild.primaryAt_of_origHead ht hB hR hpos
      (fun rc ind h0 hm0 => hfirst cb ms rc ind hcb hms h0 hm0)
  have evF : ObsFn W "KernelCheck::build_flat_block" [xrb, xb, .field (off : F)] C.m1191
      X.flat X.mFlat X.evFlat.cs := by
    rw [← huo]; exact X.evFlat.obs
  obtain ⟨extF, as, os, es, xs, hmemAt, hos, hmodel, hes, hxaux, hrep⟩ :=
    FamilyFlatBuild.build_flat_block_at_block ht hbd hS hH hR hlvR rfl hB.record hB.muts hprim
      (fun j ind hj => hsmall cb ms off hcb hms helim j ind hj)
      (Bytes.repAddressRef_heapMono₂ addrTy C.ext_in_m1191 hbR)
      (Bytes.repAddressRef_heapMono₂ addrTy C.ext_in_m1191 hbB) evF
      (fun c hc => hsub c (X.evFlat.sub c hc))
  -- one entry per recursor
  have ext_501_784 : Heap.Extends C.m501 C.m784 :=
    ext_501_652.trans (C.evTypes.extends.trans (C.evTypeMods.extends.trans
      (C.evCtors.extends.trans (C.evLenCtors.extends.trans C.evCtorMods.extends))))
  have hbR784 : Bytes.RepAddressRef addrTy C.m784 bR xrb :=
    Bytes.repAddressRef_heapMono₂ addrTy
      (ext_0_453.trans (C.evLoadBlk.extends.trans ext_501_784)) hbR
  have hsubRecs : ∀ cl ∈ C.evRecs.cs, cl ∈ calls :=
    fun cl hcl => hsub cl (C.evRecs.sub cl hcl)
  obtain ⟨as_rc, has_rc, hmap_rc⟩ :=
    FamilyAlias.family_recs_list hH hbR784 C.evRecs.obs hsubRecs hR
  have hrsz := FamilyAlias.family_recs_bound hS hH hbR784 C.evRecs.obs hsubRecs hR
  have hlen_rc : as_rc.length = rs.size := by
    have := congrArg List.length hmap_rc
    simpa using this
  obtain ⟨hnRecs, -⟩ := Decl.addrList_length_spec
    (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy)
      (C.evNoRole.extends.trans C.evNoTypeRole.extends) has_rc) C.evLenRecs.obs
  rw [hlen_rc] at hnRecs
  have hrepN : RepList flatListEnum (FlatEntryRepExact (IxVM.Consistency.keyOf t)) X.mNested es
      X.flat := flatList_mono X.evNested.extends hrep
  have hlenlt : es.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbdcs (c := ⟨_, [X.flat], X.mNested⟩) X.evLenFlat.mem
      (by simp) hrepN
  have hcov : es.length = rs.size :=
    length_eq_of_nonempty X hsz hnRecs (by omega) hrepN (by omega)
  -- the derivation
  subst hes
  have horig : FlatOriginals t E₀ (ixAddr bB) off (os ++ xs) :=
    flatOriginals_of_append hmemAt hos hxaux
  have hderived : BlockDerivedFlat t E₀ (ixAddr bB) off (os ++ xs) :=
    blockDerivedFlat_of_checks hinj hnested hbdcs helim (fun c hc => X.evNested.sub c hc)
      (Bytes.repAddressRef_heapMono₂ addrTy X.ext_in_mFlat hbB) rfl hrep horig X.evNested.obs
  -- the record, position by position
  have hctx : RecordFlatOf t E₀ (ixAddr bB) (ixAddr bR) cr rs cb ms off (os ++ xs) :=
    ⟨hB, helim, hmodel, hcov⟩
  obtain ⟨hfam, hflat⟩ := familyOfBlock_of_model ht hbd hS hH hfc0 hB hR.record hR.muts hmodel
    hcov (hheads cb ms off _ hctx) (hauxc cb ms off _ hctx)
  exact ⟨cb, ms, _, off, hfam, hflat, hderived,
    fun ind₀ k rc h0 hk => hlvls cb ms off hcb hms helim ind₀ k rc h0 hk⟩

/-! ## The major premises, from the reconstruction -/

/-- **The first entries of the list `build_flat_block` builds of a complete record over the block
are the block's types at the offset's levels**, entry by entry. -/
theorem recordFlatAt_originals {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address}
    {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst} {off : Nat} {es : List FlatEntry}
    (hB : FamBlockRecord E₀ B cb ms) (hprim : primaryAt t E₀ rb crb rs B = some B)
    (hmodel : recordFlatAt t E₀ rb crb rs B off = some es) (hcov : es.length = rs.size)
    (hrs_lt : rs.size < UInt64.size) (i : Nat) (ind : Ixon.Inductive)
    (hi : ms[i]? = some (Ixon.MutConst.indc ind)) :
    es[i]? = some (⟨memberAddr B i (.indc ind), false, [],
      (List.range ind.lvls.toNat).map fun j => .param (off + j)⟩ : FlatEntry) := by
  unfold recordFlatAt at hmodel
  rw [hprim] at hmodel
  simp only [membersAt_of hB.record hB.muts] at hmodel
  cases ho : originals (FlatView.ofStore t E₀) off (indcAddrs B 0 ms.toList) with
  | none => simp [ho] at hmodel
  | some os =>
    simp only [ho] at hmodel
    obtain ⟨hol, hoget⟩ := originals_get _ off _ os ho
    obtain ⟨hal, haget⟩ := indcAddrs_get B ms.toList 0 hB.indcs
    have hos_len : os.length = ms.size := by rw [hol, hal, Array.length_toList]
    obtain ⟨tl, htl, htl_len⟩ := auxWalk_prefix _ _ _ _ _ hmodel
    have hle : ms.size ≤ rs.size := by
      rw [← hcov, htl, List.length_append, hos_len]
      omega
    have hilt : i < ms.size := (Array.getElem?_eq_some_iff.mp hi).1
    have h1 := haget i _ (by rw [Array.getElem?_toList]; exact hi)
    rw [Nat.zero_add] at h1
    obtain ⟨info, hci, hg⟩ := hoget i _ h1
    have hci' : indInfoAt E₀ (memberAddr B i (.indc ind)) = some (some info) := hci
    rw [indInfoAt_member hB hi (by omega)] at hci'
    have hinfo := Option.some.inj (Option.some.inj hci')
    subst hinfo
    rw [htl, List.getElem?_append_left (by omega)]
    exact hg

/-- **What the comparison of recursor `k` with the reconstruction gives of its major premise**
(the facts `major_head_of_canonical` reads): the recursor's type in the canonical reading is the
type reconstructed at position `k` of the flattened family `es` at the offset `off`, its minor
premises are the reconstructed ones, and it has at least the index binders of entry `k`'s
type. -/
def MemberMajorFacts (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) (es : List FlatEntry) (off k : Nat)
    (rc : Ixon.Recursor) : Prop :=
  ∃ (ty : KExpr) (ek : FlatEntry) (self : IndData) (fop : List Nat) (Ms : List KExpr),
    loadedAt t (fun x => E.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat (mutsRoot rs k)
      rc.typ = some ty ∧
    es[k]? = some ek ∧
    (ReconView.ofStore t E).ind ek.addr = some (some self) ∧
    flatOwnParams (ReconView.ofStore t E) es = some fop ∧
    rc.minors.toNat = Ms.length ∧
    (Eventually fun f =>
      allMinors (ReconView.ofStore t E) f es fop rc.params.toNat es.length rc.params.toNat
        (elimLevel off) es 0 0 = some Ms) ∧
    (Eventually fun f =>
      recTypeAt (ReconView.ofStore t E) f es off rc.params.toNat k = some ty) ∧
    self.ni ≤ rc.indices.toNat

/-- **`MemberMajorFacts` of every recursor at a position of one of the block's own types**, over
the flattened family the family check reads off the record. -/
def RecordMajorFacts (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) : Prop :=
  ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (off : Nat) (es : List FlatEntry),
    RecordFlatOf t E₀ B rb crb rs cb ms off es →
    ∀ (k : Nat) (rc : Ixon.Recursor), k < ms.size → rs[k]? = some (Ixon.MutConst.recr rc) →
      MemberMajorFacts t E₀ rb crb rs es off k rc

/-- **The first recursors' major premises are over the block's types at the offset's levels,
from the reconstruction.** Recursor `k`'s type is the type reconstructed at entry `k`
(`RecordMajorFacts`), whose major premise is over entry `k` at entry `k`'s levels
(`major_head_of_canonical`); where the first recursor's major premise is over the block's first
type (`FirstMajorInBlock`), entry `k` below the count of the block's types is the block's `k`-th
type at the levels `param (off + j)` (`recordFlatAt_originals`). Taken of the record's readers:
every recursor has one motive per recursor (`hmot`) and a major premise (`hmaj`). -/
theorem recordOrigHeads_of_majorFacts {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {B rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (ht : t.check = .ok ()) (hR : FamRecRecord E₀ rb crb rs) (hrs_lt : rs.size < UInt64.size)
    (hmot : ∀ (k : Nat) (rc : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr rc) →
      rc.motives.toNat = rs.size)
    (hmaj : ∀ (k : Nat) (rc : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr rc) →
      ∃ ty d, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
          (mutsRoot rs k) rc.typ = some ty ∧
        binderDomAfter (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
          ty = some d)
    (hfirst : FirstMajorInBlock t E₀ B rb crb rs)
    (hfacts : RecordMajorFacts t E₀ B rb crb rs) : RecordOrigHeads t E₀ B rb crb rs := by
  intro cb ms off es hctx k rc ind hk hm
  have hB := hctx.block
  have hklt : k < ms.size := (Array.getElem?_eq_some_iff.mp hm).1
  have hprim : primaryAt t E₀ rb crb rs B = some B :=
    FamilyFlatBuild.primaryAt_of_origHead ht hB hR (by omega)
      (fun rc0 ind0 h0 hm0 => hfirst cb ms rc0 ind0 hB.record hB.muts h0 hm0)
  have hes := recordFlatAt_originals hB hprim hctx.model hctx.covers hrs_lt k ind hm
  obtain ⟨ty, ek, self, fop, Ms, hty, hek, hself, hfop, hMin, hMs, hRt, hni⟩ :=
    hfacts cb ms off es hctx k rc hklt hk
  have hee : ek = _ := Option.some.inj (hek.symm.trans hes)
  subst hee
  obtain ⟨ty', d, hty', hd⟩ := hmaj k rc hk
  have e1 : ty' = ty := Option.some.inj (hty'.symm.trans hty)
  subst e1
  have hMot : rc.motives.toNat = es.length := by rw [hmot k rc hk, hctx.covers]
  exact ⟨ty', d, hty, hd, major_head_of_canonical hek hself hfop hMot hMin hMs hRt hni hd⟩

/-- **The positional flattened family of an accepted family check, the major premises read off
the reconstruction** (`familyCall_flat`, with `RecordOrigHeads` from `RecordMajorFacts`). -/
theorem familyCall_flat_of_majorFacts {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B r : _root_.Address} {cr : Ixon.Constant}
    {rs : Array Ixon.MutConst} {lim : Option Nat} {cs : List (Call F)}
    (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hR : FamRecRecord E₀ r cr rs) (hsz : rs.size ≠ 0)
    (hlogic : ∀ cb, recordOf E₀ B = some cb → InLogic cb)
    (hfc : FamilyCallAtLim calls bAddr t B r lim cs)
    (hlv : LoadedLevelsDefined t E₀ cs)
    (hnested : NestedWalkSpec (IxVM.Consistency.keyOf t) (FlatView.ofStore t E₀) B cs)
    (hsmall : BlockLevelsSmall t E₀ B)
    (hfirst : FirstMajorInBlock t E₀ B r cr rs)
    (hfacts : RecordMajorFacts t E₀ B r cr rs)
    (hauxc : AuxCarriers t E₀ B r cr rs)
    (hlvls : RecLevelCount t E₀ B rs) :
    ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (es : List FlatEntry) (off : Nat),
      FamilyOfBlock E₀ B cb ms r cr rs (es.map FlatEntry.addr) ∧
      RecordFlat t E₀ r cr rs es ∧ BlockDerivedFlat t E₀ B off es ∧
      ∀ (ind₀ : Ixon.Inductive) (k : Nat) (rc : Ixon.Recursor),
        ms[0]? = some (.indc ind₀) → rs[k]? = some (.recr rc) →
        rc.lvls.toNat = ind₀.lvls.toNat + off := by
  obtain ⟨cb', crb', ms', rs', hF⟩ := FamilyOfCall.familyCall_readers ht hbd hS hH hfc
  have e3 : crb' = cr := Option.some.inj (hF.record.record.symm.trans hR.record)
  subst e3
  have e4 : rs' = rs := Ixon.ConstantInfo.muts.inj (hF.record.muts.symm.trans hR.muts)
  subst e4
  have hrs := familyCall_recs_bound hS hH hfc hR
  refine familyCall_flat ht hbd hS hH hR hsz hlogic hfc hlv hnested hsmall hfirst
    (recordOrigHeads_of_majorFacts ht hR (Nat.lt_trans hrs (by decide)) hF.motives
      (fun k rc hk => ?_) hfirst hfacts) hauxc hlvls
  obtain ⟨-, -, ty, d, -, hty, hd, -⟩ := hF.major k rc hk
  exact ⟨ty, d, hty, hd⟩

/-! ## The premise of the twin producer -/

/-- **What `familyCall_flat_of_majorFacts` takes of a family check beyond the hypotheses of
`TwinFamily.TwinCallFlat`**, for the check of the block `B` with the record `r` whose calls are
`cs`, in a run `calls` with the store `E₀`. -/
structure FamilyCallFlatPremises (calls : List (Call F)) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (B r : _root_.Address) (cr : Ixon.Constant) (rs : Array Ixon.MutConst)
    (cs : List (Call F)) : Prop where
  bounded : Bounded calls
  levels : LoadedLevelsDefined t E₀ cs
  nestedWalk : NestedWalkSpec (IxVM.Consistency.keyOf t) (FlatView.ofStore t E₀) B cs
  levelsSmall : BlockLevelsSmall t E₀ B
  firstMajor : FirstMajorInBlock t E₀ B r cr rs
  majorFacts : RecordMajorFacts t E₀ B r cr rs
  auxCarriers : AuxCarriers t E₀ B r cr rs
  levelCount : RecLevelCount t E₀ B rs

/-- **`TwinFamily.TwinCallFlat` from `FamilyCallFlatPremises` of every accepted family check**
of a non-empty record. -/
theorem twinCallFlat_of_premises
    (hprem : ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
      (E₀ : Ixon.Env) (B r : _root_.Address) (cr : Ixon.Constant)
      (rs : Array Ixon.MutConst) (lim : Option Nat) (cs : List (Call F)),
      t.check = .ok () → LoadedReads.RunStore calls E₀ →
      LoadedReads.HashedRecordsStored calls E₀ →
      FamRecRecord E₀ r cr rs → rs.size ≠ 0 →
      (∀ cb, recordOf E₀ B = some cb → InLogic cb) →
      FamilyCallAtLim calls bAddr t B r lim cs →
      FamilyCallFlatPremises calls t E₀ B r cr rs cs) :
    TwinFamily.TwinCallFlat := by
  intro calls bAddr t E₀ B r cr rs lim cs ht hS hH hR hsz hlogic hfc
  have p := hprem calls bAddr t E₀ B r cr rs lim cs ht hS hH hR hsz hlogic hfc
  exact familyCall_flat_of_majorFacts ht p.bounded hS hH hR hsz hlogic hfc p.levels p.nestedWalk
    p.levelsSmall p.firstMajor p.majorFacts p.auxCarriers
    p.levelCount

end IxVM.Refinement.Binding.FamilyCallFlat
