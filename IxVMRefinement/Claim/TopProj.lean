import IxVMRefinement.Claim.TopWalk
import IxVMRefinement.Assembly.ConstructorHashes

/-! # The projection records of a top-walked block, from the walk's check evidence

The assembly's `Typing.TopGraph` reads two clauses about projection records off the walk. Both
follow from the check evidence `TopWalkCore` carries (`checked`), its run store (`runStore`) and
the store of every canonical record the run hashed (`hashedStored`):

* `TopWalkCore.members` (A4): a top-walked block's member and constructor projection records are
  in the run's store. A block is checked member by member (`MemberCheckedLimAt`; a direct check
  of a block record is refused, `checked_not_block`): `Ingress::projection_addr` hashes the
  member's projection record, `Ingress::get_ci` loads it and the block it names (so the member's
  index is small: `BlockLoad.record`), and for an inductive member the `Induct` arm of
  `KernelCheck::check_const` hashes every constructor's projection record
  (`check_const_induct_ctors_hashed`, on the native and on the modeled route).
* `TopWalkCore.projMember` (A5): a top-walked projection record is at a member's or a
  constructor's address of its block. `Ingress::get_ci` loaded the record with empty tables (so
  its bytes are its canonical serialization, `proj_canon`) and the block it names, refusing a
  missing member, a member of another kind and a missing constructor (`get_ci_head`).

Neither uses the role context: the evidence is read at any limit, `some n` or `none`. The loads
are read without a bound on the run's calls: every loaded record and block has fewer than `2^32`
bytes (`Ingress::load_verified_constant`), which bounds its member and constructor counts by
its resource size (`muts_size_le`, `ctors_size_le`). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## Small facts -/

private theorem length_le_sum_map {α : Type} (f : α → Nat) (hf : ∀ a, 1 ≤ f a)
    (l : List α) : l.length ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have := hf a
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

private theorem mem_le_sum_map {α : Type} (f : α → Nat) {a : α} (l : List α) (h : a ∈ l) :
    f a ≤ (l.map f).sum := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · omega
    · have := ih h'
      omega

/-- A block record has no more members than its resource size. -/
theorem muts_size_le {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (h : c.info = .muts ms) : ms.size ≤ c.resourceSize := by
  have h1 := length_le_sum_map Ixon.MutConst.resourceSize
    (fun m => by cases m <;> (dsimp only [Ixon.MutConst.resourceSize]; omega)) ms.toList
  have h2 : c.info.resourceSize ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  rw [h] at h2
  dsimp [Ixon.ConstantInfo.resourceSize] at h2
  rw [Array.length_toList] at h1
  omega

/-- An inductive member of a block record has no more constructors than the record's resource
size. -/
theorem ctors_size_le {c : Ixon.Constant} {ms : Array Ixon.MutConst} {i : Nat}
    {ind : Ixon.Inductive} (h : c.info = .muts ms) (hi : ms.toList[i]? = some (.indc ind)) :
    ind.ctors.size ≤ c.resourceSize := by
  have h1 := mem_le_sum_map Ixon.MutConst.resourceSize ms.toList (List.mem_of_getElem? hi)
  have h2 := length_le_sum_map Ixon.Constructor.resourceSize
    (fun ct => by dsimp only [Ixon.Constructor.resourceSize]; omega) ind.ctors.toList
  have h3 : (ind.ctors.toList.map Ixon.Constructor.resourceSize).sum ≤
      (Ixon.MutConst.indc ind).resourceSize := by
    dsimp only [Ixon.MutConst.resourceSize, Ixon.Inductive.resourceSize]
    omega
  have h4 : c.info.resourceSize ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  rw [h] at h4
  dsimp [Ixon.ConstantInfo.resourceSize] at h4
  rw [Array.length_toList] at h2
  omega

private theorem uint64_ofNat_toNat (x : UInt64) : x.toNat.toUInt64 = x := UInt64.ofNat_toNat

theorem memberProjection_defn (B : _root_.Address) (idx : UInt64) (d : Ixon.Definition) :
    memberProjection B idx.toNat (.defn d) = ⟨.dPrj ⟨idx, B⟩, #[], #[], #[], #[]⟩ := by
  show (⟨.dPrj ⟨idx.toNat.toUInt64, B⟩, #[], #[], #[], #[]⟩ : Ixon.Constant) = _
  rw [uint64_ofNat_toNat idx]

theorem memberProjection_indc (B : _root_.Address) (idx : UInt64) (ind : Ixon.Inductive) :
    memberProjection B idx.toNat (.indc ind) = ⟨.iPrj ⟨idx, B⟩, #[], #[], #[], #[]⟩ := by
  show (⟨.iPrj ⟨idx.toNat.toUInt64, B⟩, #[], #[], #[], #[]⟩ : Ixon.Constant) = _
  rw [uint64_ofNat_toNat idx]

theorem memberProjection_recr (B : _root_.Address) (idx : UInt64) (rc : Ixon.Recursor) :
    memberProjection B idx.toNat (.recr rc) = ⟨.rPrj ⟨idx, B⟩, #[], #[], #[], #[]⟩ := by
  show (⟨.rPrj ⟨idx.toNat.toUInt64, B⟩, #[], #[], #[], #[]⟩ : Ixon.Constant) = _
  rw [uint64_ofNat_toNat idx]

theorem constructorProjection_toNat (B : _root_.Address) (idx cidx : UInt64) :
    constructorProjection B idx.toNat cidx.toNat =
      ⟨.cPrj ⟨idx, cidx, B⟩, #[], #[], #[], #[]⟩ := by
  show (⟨.cPrj ⟨idx.toNat.toUInt64, cidx.toNat.toUInt64, B⟩, #[], #[], #[], #[]⟩ :
    Ixon.Constant) = _
  rw [uint64_ofNat_toNat idx, uint64_ofNat_toNat cidx]

/-! ## The size of a constructor projection record -/

section Codec

open Ixon.Verify.Codec Ixon.Verify.Codec.ConstantTables Ixon.Verify.Codec.NonrecursiveConstant

private theorem tag0Bytes_size_le9 (v : UInt64) : (tag0Bytes v).size ≤ 9 := by
  unfold tag0Bytes
  rw [tagNBytes_size]
  unfold Ixon.tagNByteWidth
  repeat' split
  all_goals omega

/-- **A constructor projection record at a block address serializes to fewer than `2^32`
bytes.** -/
theorem serConstant_cprj_size_lt (i j : UInt64) (b : Bytes.Address) :
    (Ixon.serConstant ⟨.cPrj ⟨i, j, Core.ixAddr b⟩, #[], #[], #[], #[]⟩).size <
      4294967296 := by
  have hb : AddressWireWF (Core.ixAddr b) := by
    show (Core.ixAddr b).hash.size = 32
    exact b.size_toArray
  have hcwf : NonrecursiveConstantWireWF ⟨.cPrj ⟨i, j, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ :=
    { info := .cPrj hb
      sharingCount := by show (#[] : Array Ixon.Expr).size < UInt64.size; decide
      sharingEntries := by simp
      refsCount := by show (#[] : Array _root_.Address).size < UInt64.size; decide
      refsEntries := by simp
      univsCount := by show (#[] : Array Ixon.Univ).size < UInt64.size; decide
      univsEntries := by simp
      binders := by simp [Ixon.bindersWireWF] }
  have hser : Ixon.serConstant ⟨.cPrj ⟨i, j, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ =
      nonrecursiveConstantBytes ⟨.cPrj ⟨i, j, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ := by
    unfold Ixon.serConstant
    exact (putConstant_writes_nonrecursive _ hcwf).runPut
  have hbytes : nonrecursiveConstantBytes ⟨.cPrj ⟨i, j, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ =
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_CPRJ ++
        (tag0Bytes i ++ tag0Bytes j ++ (Core.ixAddr b).hash) ++
        tag0Bytes 0 ++ ByteArray.empty ++ tag0Bytes 0 ++ ByteArray.empty ++
        tag0Bytes 0 ++ ByteArray.empty ++ bindersBytes #[] := by
    first
      | rfl
      | (simp only [nonrecursiveConstantBytes, nonrecursiveInfoBytes, constructorProjBytes,
          listBytes, Array.toList_empty]; rfl)
  rw [hser, hbytes]
  have h1 := tag0Bytes_size_le9 i
  have h2 := tag0Bytes_size_le9 j
  have ht4 : (tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_CPRJ).size = 1 := by decide
  have ht0 : (tag0Bytes 0).size = 1 := by decide
  have hbd0 : (bindersBytes #[]).size = 1 := by decide
  have hh : (Core.ixAddr b).hash.size = 32 := hb
  simp only [ByteArray.size_append, ByteArray.size_empty]
  omega

end Codec

/-! ## Loads of a block -/

/-- **The run loaded the block record at `B`**: bytes fewer than `2^32`, hashed in the run, at
the address, decoding exactly to a block record. -/
def BlockLoad (calls : List (Call F)) (B : _root_.Address) (cb : Ixon.Constant)
    (ms : Array Ixon.MutConst) : Prop :=
  ∃ bytes : ByteArray, bytes.size < 4294967296 ∧ Hashed calls bytes ∧
    Address.blake3Pure bytes = B ∧ Ixon.deConstantExact bytes = .ok cb ∧ cb.info = .muts ms

theorem BlockLoad.mono {cs₁ cs₂ : List (Call F)} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (h : BlockLoad cs₁ B cb ms) :
    BlockLoad cs₂ B cb ms := by
  obtain ⟨bytes, hsz, hh, hb, hx, hi⟩ := h
  exact ⟨bytes, hsz, Core.hashed_mono hsub hh, hb, hx, hi⟩

theorem BlockLoad.info {calls : List (Call F)} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} (h : BlockLoad calls B cb ms) : cb.info = .muts ms := by
  obtain ⟨_, _, _, _, _, hi⟩ := h
  exact hi

/-- **A canonical record the run hashed is the store's record at its address.** -/
theorem recordOf_of_hashed {calls : List (Call F)} {E : Ixon.Env}
    (hcov : LoadedReads.HashedRecordsStored calls E) {bytes : ByteArray} {c : Ixon.Constant}
    (hh : Hashed calls bytes) (hsz : bytes.size < 4294967296)
    (hx : Ixon.deConstantExact bytes = .ok c) :
    recordOf E (Address.blake3Pure bytes) = some c := by
  obtain ⟨lc, hget, hraw, -⟩ := hcov bytes c hh hsz (L1.deConstant_of_deConstantExact hx) hx
  unfold recordOf
  rw [hget]
  simp [hraw, hx, Except.toOption]

/-- **A loaded block is in the store.** -/
theorem BlockLoad.stored {calls : List (Call F)} {E : Ixon.Env}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hbl : BlockLoad calls B cb ms) (hcov : LoadedReads.HashedRecordsStored calls E) :
    recordOf E B = some cb ∧ cb.info = .muts ms := by
  obtain ⟨bytes, hsz, hh, hb, hx, hi⟩ := hbl
  refine ⟨?_, hi⟩
  rw [← hb]
  exact recordOf_of_hashed hcov hh hsz hx

/-- **A loaded block is the run store's record at its address**, of resource size below
`2^33`. -/
theorem BlockLoad.record {calls : List (Call F)} {E : Ixon.Env}
    {B : _root_.Address} {cb c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hbl : BlockLoad calls B cb ms) (hS : LoadedReads.RunStore calls E)
    (hc : recordOf E B = some c) : cb = c ∧ c.resourceSize < 8589934592 := by
  obtain ⟨bytes, hsz, hh, hb, hx, -⟩ := hbl
  have hcb : cb = c := hS.record_eq ((hS.recordOf_eq_recordAt B).symm.trans hc) hh hb hx
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound bytes cb hx
  refine ⟨hcb, ?_⟩
  rw [← hcb]
  omega

/-- `Ingress::load_verified_constant` returning a block record. -/
theorem load_block_head {b : Bytes.Address}
    {x_block_addr x_members x_sh x_rf x_un x_bd : SourceValue F} {h m : Heap F}
    {cs : List (Call F)} (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn Obs.W "Ingress::load_verified_constant" [x_block_addr] h
      (.construct "Ixon::Constant" "Mk"
        [.construct "Ixon::ConstantInfo" "Muts" [x_members], x_sh, x_rf, x_un, x_bd]) m cs) :
    ∃ cb ms, BlockLoad cs (Core.ixAddr b) cb ms ∧
      RepList L1.mutConstListEnum L1.RepMutConst m ms.toList x_members := by
  obtain ⟨-, bytes, cb, hlen, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
    L1.load_verified_constant_decode_bounded hb ev
  obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
  rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
  subst infoVal
  obtain ⟨ms, hcb_info, hms⟩ := L1.repConstantInfo_muts_inv hinfo
  exact ⟨cb, ms, ⟨⟨bytes.toArray⟩, by simpa only [ByteArray.size, List.size_toArray] using hlen,
    hh, haddr, hexact, hcb_info⟩, hms⟩

/-! ## The projection loads, without a bound on the run -/

/-- `Ingress::get_ci_dprj`: the block is loaded and its member at the index is a definition. -/
theorem get_ci_dprj_head {b : Bytes.Address} {idx : Nat}
    {x_dprj_addr x_idx x_block_addr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hidx_lt : idx < 18446744073709551616) (hx_idx : x_idx = TagN.u64Value idx)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn Obs.W "Ingress::get_ci_dprj" [x_dprj_addr, x_idx, x_block_addr] h r h' calls) :
    ∃ cb ms d, BlockLoad calls (Core.ixAddr b) cb ms ∧ ms.toList[idx]? = some (.defn d) := by
  match Obs.«Ingress::get_ci_dprj».obs ev with
  | .run (m24 := m24) (cs34 := cs34) (x_members := x_members) (ev14 := ev14) (ev36 := ev36)
      (ev120 := ev120) (hc348 := hc) .. =>
    have hb2 := Bytes.repAddressRef_heapMono₂ Core.addrTy ev14.heap_extends hb
    obtain ⟨cb, ms, hbl, hms⟩ := load_block_head hb2 ev36
    rw [← Obs.Names.«WordLists::lookup_u64<Ixon::MutConst>».symbol] at ev120
    have hms_inst : RepList (Instance.mk "Lists::Node" [.named "Ixon::MutConst" []]).symbol
        L1.RepMutConst m24 ms.toList x_members := by
      rwa [Obs.Names.«Lists::Node<Ixon::MutConst>».symbol]
    obtain ⟨⟨mc, hmc_get, hmc_rep⟩, -⟩ := Lib.lookup_u64_spec hidx_lt hx_idx ev120 hms_inst
    cases mc with
    | defn d =>
      exact ⟨cb, ms, d, hbl.mono (by rw [hc]; intro x hx; simp [hx]), hmc_get⟩
    | indc _ => obtain ⟨iv, hiv, _⟩ := hmc_rep; simp at hiv
    | recr _ => obtain ⟨rv, hrv, _⟩ := hmc_rep; simp at hrv

/-- `Ingress::get_ci_iprj`: the block is loaded, its member at the index is an inductive, and
the returned constant is that inductive with its constructor count, block and index. -/
theorem get_ci_iprj_head {b : Bytes.Address} {idx : F} {x_block_addr r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn Obs.W "Ingress::get_ci_iprj" [x_block_addr, .field idx] h r h' calls) :
    ∃ cb ms ind, BlockLoad calls (Core.ixAddr b) cb ms ∧
      ms.toList[idx.val]? = some (.indc ind) ∧
      ∃ nl ty np ni u : SourceValue F,
        loadValue h' r = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
          [nl, ty, np, ni, .field (ind.ctors.toList.length : F), u, x_block_addr,
            .field idx]) := by
  match Obs.«Ingress::get_ci_iprj».obs ev with
  | .run (m2 := m2) (m86 := m86) (cs12 := cs12) (v166 := v166) (m167 := m167) (cs174 := cs174)
      (ev14 := ev14) (ev98 := ev98) (ev149 := ev149) (he170 := he170) (hm169 := hm169)
      (ev246 := ev246) (ev266 := ev266) (ev176 := ev176) (hc283 := hc) .. =>
    obtain ⟨cb, ms, hbl, hms⟩ := load_block_head hb ev14
    obtain ⟨hm86, -, mc, hmc_get, hmc_rep⟩ := L1.muts_member_at_spec hms ev98
    subst m86
    cases mc with
    | indc ind =>
      obtain ⟨iv, hiv_eq, hiv⟩ := hmc_rep
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hiv_eq
      rcases hiv_eq with ⟨_, _, rfl⟩
      obtain ⟨typPtr, ctorsPtr, rfl, -, hctors⟩ := hiv
      have ext := ev149.heap_extends.trans (ev246.heap_extends.trans ev266.heap_extends)
      match Obs.«Convert::convert_inductive».obs ev176 with
      | .run (x_ctors := ctorsArg) (m177 := countHeap) (v124 := v124) (hv15 := fields)
          (he128 := hres) (ev207 := countRun) (hc238 := convCalls) .. =>
        simp only [Value.construct.injEq, List.cons.injEq, and_true] at fields
        obtain ⟨_, _, _, _, _, _, _, hct⟩ := fields
        subst ctorsArg
        have member : (⟨"Convert::count_ctors", [ctorsPtr], countHeap⟩ : Call F) ∈ cs174 := by
          rw [convCalls]; simp
        have ext2 := (ev176.call_heap_bounds member).1
        obtain ⟨hv124, -⟩ := L1.count_ctors_spec
          (hctors.mono L1.repConstructor_heapMono₂ (ext.trans ext2)) countRun
        subst hv124 hres he170 hm169
        exact ⟨cb, ms, ind, hbl.mono (by rw [hc]; intro x hx; simp [hx]), hmc_get,
          _, _, _, _, _, loadValue_snoc_self m167 _⟩
    | defn _ => obtain ⟨dv, hdv, _⟩ := hmc_rep; simp at hdv
    | recr _ => obtain ⟨rv, hrv, _⟩ := hmc_rep; simp at hrv

/-- `Ingress::get_ci_cprj`: the block is loaded, its member at the index is an inductive, and
the constructor index is below its constructor count. -/
theorem get_ci_cprj_head {b : Bytes.Address} {idx cidx : F} {x_block_addr r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn Obs.W "Ingress::get_ci_cprj" [x_block_addr, .field idx, .field cidx] h r h'
      calls) :
    ∃ cb ms ind, BlockLoad calls (Core.ixAddr b) cb ms ∧
      ms.toList[idx.val]? = some (.indc ind) ∧ cidx.val < ind.ctors.toList.length := by
  match Obs.«Ingress::get_ci_cprj».obs ev with
  | .run (m2 := m2) (m86 := m86) (cs12 := cs12) (ev14 := ev14) (ev98 := ev98)
      (ev200 := ev200) (hc381 := hc) .. =>
    obtain ⟨cb, ms, hbl, hms⟩ := load_block_head hb ev14
    obtain ⟨hm86, -, mc, hmc_get, hmc_rep⟩ := L1.muts_member_at_spec hms ev98
    subst m86
    cases mc with
    | indc ind =>
      obtain ⟨iv, hiv_eq, typPtr, ctorsPtr, hmk, _, hctors⟩ := hmc_rep
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hiv_eq
      rcases hiv_eq with ⟨_, _, hiv_mk⟩
      rw [hmk] at hiv_mk
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hiv_mk
      rcases hiv_mk with ⟨_, _, _, _, _, _, _, hct_eq⟩
      subst ctorsPtr
      obtain ⟨-, hlt, -⟩ := L1.ctor_at_spec hctors ev200
      exact ⟨cb, ms, ind, hbl.mono (by rw [hc]; intro x hx; simp [hx]), hmc_get, hlt⟩
    | defn _ => obtain ⟨dv, hdv, _⟩ := hmc_rep; simp at hdv
    | recr _ => obtain ⟨rv, hrv, _⟩ := hmc_rep; simp at hrv

/-- `Ingress::get_ci_rprj`: the block is loaded and its member at the index is a recursor. -/
theorem get_ci_rprj_head {b : Bytes.Address} {idx : F} {x_block_addr r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn Obs.W "Ingress::get_ci_rprj" [x_block_addr, .field idx] h r h' calls) :
    ∃ cb ms rc, BlockLoad calls (Core.ixAddr b) cb ms ∧
      ms.toList[idx.val]? = some (.recr rc) := by
  match Obs.«Ingress::get_ci_rprj».obs ev with
  | .run (cs12 := cs12) (ev14 := ev14) (ev98 := ev98) (hc283 := hc) .. =>
    obtain ⟨cb, ms, hbl, hms⟩ := load_block_head hb ev14
    obtain ⟨-, -, mc, hmc_get, hmc_rep⟩ := L1.muts_member_at_spec hms ev98
    cases mc with
    | recr rc => exact ⟨cb, ms, rc, hbl.mono (by rw [hc]; intro x hx; simp [hx]), hmc_get⟩
    | defn _ => obtain ⟨dv, hdv, _⟩ := hmc_rep; simp at hdv
    | indc _ => obtain ⟨iv, hiv, _⟩ := hmc_rep; simp at hiv

/-! ## What `Ingress::get_ci` loaded -/

/-- **What `Ingress::get_ci` returns for a record of kind `info`**: never a block record; for a
projection record, the block it names was loaded, with a member of the projection's kind at its
index (and, for a constructor projection, a constructor at its constructor index); for an
inductive projection, the returned constant is the inductive with its constructor count, its
block and its index. -/
structure GetCIHead (calls : List (Call F)) (h : Heap F) (info : Ixon.ConstantInfo)
    (r : SourceValue F) : Prop where
  notMuts : ∀ ms, info ≠ .muts ms
  dPrj : ∀ idx blk, info = .dPrj ⟨idx, blk⟩ →
    ∃ cb ms d, BlockLoad calls blk cb ms ∧ ms.toList[idx.toNat]? = some (.defn d)
  iPrj : ∀ idx blk, info = .iPrj ⟨idx, blk⟩ →
    ∃ cb ms ind, BlockLoad calls blk cb ms ∧ ms.toList[idx.toNat]? = some (.indc ind) ∧
      idx.toNat < 72057594037927936 ∧
      ∃ (nl ty np ni u x_blk : SourceValue F) (b : Bytes.Address),
        loadValue h r = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
          [nl, ty, np, ni, .field (ind.ctors.toList.length : F), u, x_blk,
            .field (idx.toNat : F)]) ∧
        Bytes.RepAddressRef Core.addrTy h b x_blk ∧ Core.ixAddr b = blk
  cPrj : ∀ idx cidx blk, info = .cPrj ⟨idx, cidx, blk⟩ →
    ∃ cb ms ind, BlockLoad calls blk cb ms ∧ ms.toList[idx.toNat]? = some (.indc ind) ∧
      cidx.toNat < ind.ctors.toList.length
  rPrj : ∀ idx blk, info = .rPrj ⟨idx, blk⟩ →
    ∃ cb ms rc, BlockLoad calls blk cb ms ∧ ms.toList[idx.toNat]? = some (.recr rc)

theorem GetCIHead.of_plain {calls : List (Call F)} {h : Heap F} {info : Ixon.ConstantInfo}
    {r : SourceValue F}
    (hplain : (∃ d, info = .defn d) ∨ (∃ ax, info = .axio ax) ∨ (∃ q, info = .quot q) ∨
      ∃ rc, info = .recr rc) :
    GetCIHead calls h info r := by
  rcases hplain with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    exact ⟨(fun _ e => nomatch e), (fun _ _ e => nomatch e), (fun _ _ e => nomatch e),
      (fun _ _ _ e => nomatch e), (fun _ _ e => nomatch e)⟩

/-- **`Ingress::get_ci`, without a bound on the run**: the run hashed fewer than `2^32` bytes at
the address that decode exactly, with valid tables, to a record `c`, and `GetCIHead` holds of
`c.info` and the returned constant. -/
theorem get_ci_head {a : Bytes.Address} {x_addr r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} (ha : Bytes.RepAddressRef Core.addrTy h a x_addr)
    (ev : ObsFn Obs.W "Ingress::get_ci" [x_addr] h r h' calls) :
    ∃ (rawBytes : ByteArray) (c : Ixon.Constant), rawBytes.size < 4294967296 ∧
      Hashed calls rawBytes ∧ Address.blake3Pure rawBytes = Core.ixAddr a ∧
      Ixon.deConstantExact rawBytes = .ok c ∧ L1.ConstantTablesValid c ∧
      GetCIHead calls h' c.info r := by
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (ev14 := ev14) (hc302 := hc) .. =>
    obtain ⟨-, bytes, c, hlen, hh, haddr, hexact, -, -, -, -, -, htv, cRep⟩ :=
      L1.load_verified_constant_decode_bounded ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨d, hci, -⟩ := L1.repConstantInfo_defn_inv hinfo
    exact ⟨⟨bytes.toArray⟩, c, by simpa only [ByteArray.size, List.size_toArray] using hlen,
      Core.hashed_mono (by rw [hc]; intro x hx; simp [hx]) hh, haddr, hexact, htv,
      GetCIHead.of_plain (.inl ⟨d, hci⟩)⟩
  | .Defn_other (ev14 := ev14) (hc423 := hc) .. =>
    obtain ⟨-, bytes, c, hlen, hh, haddr, hexact, -, -, -, -, -, htv, cRep⟩ :=
      L1.load_verified_constant_decode_bounded ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨d, hci, -⟩ := L1.repConstantInfo_defn_inv hinfo
    exact ⟨⟨bytes.toArray⟩, c, by simpa only [ByteArray.size, List.size_toArray] using hlen,
      Core.hashed_mono (by rw [hc]; intro x hx; simp [hx]) hh, haddr, hexact, htv,
      GetCIHead.of_plain (.inl ⟨d, hci⟩)⟩
  | .Axio (ev14 := ev14) (hc515 := hc) .. =>
    obtain ⟨-, bytes, c, hlen, hh, haddr, hexact, -, -, -, -, -, htv, cRep⟩ :=
      L1.load_verified_constant_decode_bounded ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨ax, hci, -⟩ := L1.repConstantInfo_axio_inv hinfo
    exact ⟨⟨bytes.toArray⟩, c, by simpa only [ByteArray.size, List.size_toArray] using hlen,
      Core.hashed_mono (by rw [hc]; intro x hx; simp [hx]) hh, haddr, hexact, htv,
      GetCIHead.of_plain (.inr (.inl ⟨ax, hci⟩))⟩
  | .Quot (ev14 := ev14) (hc606 := hc) .. =>
    obtain ⟨-, bytes, c, hlen, hh, haddr, hexact, -, -, -, -, -, htv, cRep⟩ :=
      L1.load_verified_constant_decode_bounded ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨q, hci, -⟩ := L1.repConstantInfo_quot_inv hinfo
    exact ⟨⟨bytes.toArray⟩, c, by simpa only [ByteArray.size, List.size_toArray] using hlen,
      Core.hashed_mono (by rw [hc]; intro x hx; simp [hx]) hh, haddr, hexact, htv,
      GetCIHead.of_plain (.inr (.inr (.inl ⟨q, hci⟩)))⟩
  | .Recr (ev14 := ev14) (hc1071 := hc) .. =>
    obtain ⟨-, bytes, c, hlen, hh, haddr, hexact, -, -, -, -, -, htv, cRep⟩ :=
      L1.load_verified_constant_decode_bounded ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨rc, hci, -⟩ := L1.repConstantInfo_recr_inv hinfo
    exact ⟨⟨bytes.toArray⟩, c, by simpa only [ByteArray.size, List.size_toArray] using hlen,
      Core.hashed_mono (by rw [hc]; intro x hx; simp [hx]) hh, haddr, hexact, htv,
      GetCIHead.of_plain (.inr (.inr (.inr ⟨rc, hci⟩)))⟩
  | .DPrj (m2 := m2) (x_idx := x_idx) (x_block_addr := x_blk) (cs648 := csd) (ev14 := ev14)
      (ev650 := ev650) (hc675 := hc) .. =>
    obtain ⟨-, bytes, c, hlen, hh, haddr, hexact, -, -, -, -, -, htv, cRep⟩ :=
      L1.load_verified_constant_decode_bounded ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨⟨idx, blk⟩, hci, hx_idx, hblk_ix⟩ := L1.repConstantInfo_dPrj_inv hinfo
    have hx_idx' : x_idx = TagN.u64Value idx.toNat := hx_idx
    obtain ⟨b, hb_eq, hb_rep⟩ := L1.repIxonAddressRef_to_core_ing hblk_ix
    have hb_eq' : Core.ixAddr b = blk := hb_eq
    obtain ⟨cb, ms, d, hbl, hmem⟩ := get_ci_dprj_head idx.toNat_lt hx_idx' hb_rep ev650
    have hsub : ∀ x ∈ csd, x ∈ calls := by rw [hc]; intro x hx; simp [hx]
    have hbl' : BlockLoad calls blk cb ms := by rw [← hb_eq']; exact hbl.mono hsub
    refine ⟨⟨bytes.toArray⟩, c, by simpa only [ByteArray.size, List.size_toArray] using hlen,
      Core.hashed_mono (by rw [hc]; intro x hx; simp [hx]) hh, haddr, hexact, htv,
      ⟨(fun _ e => nomatch hci.symm.trans e), ?_, (fun _ _ e => nomatch hci.symm.trans e),
        (fun _ _ _ e => nomatch hci.symm.trans e), (fun _ _ e => nomatch hci.symm.trans e)⟩⟩
    intro idx' blk' e
    have e' := hci.symm.trans e
    cases e'
    exact ⟨cb, ms, d, hbl', hmem⟩
  | .IPrj (m2 := m2) (x_idx := x_idx) (x_block_addr := x_blk) (cs718 := csi) (v722 := v722)
      (m731 := m731) (ev14 := ev14) (ev741 := ev741) (ev720 := ev720) (hc750 := hc) .. =>
    obtain ⟨-, bytes, c, hlen, hh, haddr, hexact, -, -, -, -, -, htv, cRep⟩ :=
      L1.load_verified_constant_decode_bounded ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨⟨idx, blk⟩, hci, hx_idx, hblk_ix⟩ := L1.repConstantInfo_iPrj_inv hinfo
    have hx_idx' : x_idx = TagN.u64Value idx.toNat := hx_idx
    subst hx_idx'
    obtain ⟨hidx56, hv722, hm731⟩ :=
      Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 idx) ev741
    subst v722 m731
    obtain ⟨b, hb_eq, hb_rep⟩ := L1.repIxonAddressRef_to_core_ing hblk_ix
    have hb_eq' : Core.ixAddr b = blk := hb_eq
    obtain ⟨cb, ms, ind, hbl, hmem, nl, ty, np, ni, u, hld⟩ := get_ci_iprj_head hb_rep ev720
    rw [L1.val_cast_u56_ing hidx56] at hmem
    have hsub : ∀ x ∈ csi, x ∈ calls := by rw [hc]; intro x hx; simp [hx]
    have hbl' : BlockLoad calls blk cb ms := by rw [← hb_eq']; exact hbl.mono hsub
    have hb_rep' := Bytes.repAddressRef_heapMono₂ Core.addrTy ev720.heap_extends hb_rep
    refine ⟨⟨bytes.toArray⟩, c, by simpa only [ByteArray.size, List.size_toArray] using hlen,
      Core.hashed_mono (by rw [hc]; intro x hx; simp [hx]) hh, haddr, hexact, htv,
      ⟨(fun _ e => nomatch hci.symm.trans e), (fun _ _ e => nomatch hci.symm.trans e), ?_,
        (fun _ _ _ e => nomatch hci.symm.trans e), (fun _ _ e => nomatch hci.symm.trans e)⟩⟩
    intro idx' blk' e
    have e' := hci.symm.trans e
    cases e'
    exact ⟨cb, ms, ind, hbl', hmem, hidx56, nl, ty, np, ni, u, x_blk, b, hld, hb_rep', hb_eq'⟩
  | .CPrj (m2 := m2) (x_idx := x_idx) (x_cidx := x_cidx) (x_block_addr := x_blk)
      (cs798 := csc) (v802 := v802) (v803 := v803) (m812 := m812) (m832 := m832)
      (ev14 := ev14) (ev822 := ev822) (ev842 := ev842) (ev800 := ev800) (hc851 := hc) .. =>
    obtain ⟨-, bytes, c, hlen, hh, haddr, hexact, -, -, -, -, -, htv, cRep⟩ :=
      L1.load_verified_constant_decode_bounded ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨⟨idx, cidx, blk⟩, hci, hx_idx, hx_cidx, hblk_ix⟩ := L1.repConstantInfo_cPrj_inv hinfo
    have hx_idx' : x_idx = TagN.u64Value idx.toNat := hx_idx
    have hx_cidx' : x_cidx = TagN.u64Value cidx.toNat := hx_cidx
    subst hx_idx' hx_cidx'
    obtain ⟨hidx56, hv802, hm812⟩ :=
      Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 idx) ev822
    subst v802 m812
    obtain ⟨hcidx56, hv803, hm832⟩ :=
      Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 cidx) ev842
    subst v803 m832
    obtain ⟨b, hb_eq, hb_rep⟩ := L1.repIxonAddressRef_to_core_ing hblk_ix
    have hb_eq' : Core.ixAddr b = blk := hb_eq
    obtain ⟨cb, ms, ind, hbl, hmem, hlt⟩ := get_ci_cprj_head hb_rep ev800
    rw [L1.val_cast_u56_ing hidx56] at hmem
    rw [L1.val_cast_u56_ing hcidx56] at hlt
    have hsub : ∀ x ∈ csc, x ∈ calls := by rw [hc]; intro x hx; simp [hx]
    have hbl' : BlockLoad calls blk cb ms := by rw [← hb_eq']; exact hbl.mono hsub
    refine ⟨⟨bytes.toArray⟩, c, by simpa only [ByteArray.size, List.size_toArray] using hlen,
      Core.hashed_mono (by rw [hc]; intro x hx; simp [hx]) hh, haddr, hexact, htv,
      ⟨(fun _ e => nomatch hci.symm.trans e), (fun _ _ e => nomatch hci.symm.trans e),
        (fun _ _ e => nomatch hci.symm.trans e), ?_, (fun _ _ e => nomatch hci.symm.trans e)⟩⟩
    intro idx' cidx' blk' e
    have e' := hci.symm.trans e
    cases e'
    exact ⟨cb, ms, ind, hbl', hmem, hlt⟩
  | .RPrj (m2 := m2) (x_idx := x_idx) (x_block_addr := x_blk) (cs894 := csr) (v898 := v898)
      (m907 := m907) (ev14 := ev14) (ev917 := ev917) (ev896 := ev896) (hc926 := hc) .. =>
    obtain ⟨-, bytes, c, hlen, hh, haddr, hexact, -, -, -, -, -, htv, cRep⟩ :=
      L1.load_verified_constant_decode_bounded ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨⟨idx, blk⟩, hci, hx_idx, hblk_ix⟩ := L1.repConstantInfo_rPrj_inv hinfo
    have hx_idx' : x_idx = TagN.u64Value idx.toNat := hx_idx
    subst hx_idx'
    obtain ⟨hidx56, hv898, hm907⟩ :=
      Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 idx) ev917
    subst v898 m907
    obtain ⟨b, hb_eq, hb_rep⟩ := L1.repIxonAddressRef_to_core_ing hblk_ix
    have hb_eq' : Core.ixAddr b = blk := hb_eq
    obtain ⟨cb, ms, rc, hbl, hmem⟩ := get_ci_rprj_head hb_rep ev896
    rw [L1.val_cast_u56_ing hidx56] at hmem
    have hsub : ∀ x ∈ csr, x ∈ calls := by rw [hc]; intro x hx; simp [hx]
    have hbl' : BlockLoad calls blk cb ms := by rw [← hb_eq']; exact hbl.mono hsub
    refine ⟨⟨bytes.toArray⟩, c, by simpa only [ByteArray.size, List.size_toArray] using hlen,
      Core.hashed_mono (by rw [hc]; intro x hx; simp [hx]) hh, haddr, hexact, htv,
      ⟨(fun _ e => nomatch hci.symm.trans e), (fun _ _ e => nomatch hci.symm.trans e),
        (fun _ _ e => nomatch hci.symm.trans e), (fun _ _ _ e => nomatch hci.symm.trans e), ?_⟩⟩
    intro idx' blk' e
    have e' := hci.symm.trans e
    cases e'
    exact ⟨cb, ms, rc, hbl', hmem⟩

/-! ## The constructors an inductive's check hashes -/

/-- **The check of an inductive hashes every constructor's projection record**: on the native
route (`check_inductive_shape`) and on the modeled route (`check_modeled_ctors`, safe or not),
the constructor loop computes the address of each constructor projection of the block at its
index. -/
theorem check_const_induct_ctors_hashed (ctx : Core.ScopedCtx)
    {rc nl ty np ni u blk ap r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {b : Bytes.Address} {n i : Nat}
    (hn : n < 72057594037927936) (hi : i < 72057594037927936)
    (hb : Bytes.RepAddressRef Core.addrTy h b blk)
    (ev : ObsFn Obs.W "KernelCheck::check_const"
      [rc, .construct "KernelTypes::KConstantInfo" "Induct"
        [nl, ty, np, ni, .field (n : F), u, blk, .field (i : F)], ap] h r h' cs) :
    ∀ j < n, Hashed cs (Ixon.serConstant (constructorProjection (Core.ixAddr b) i j)) := by
  intro j hj
  match Obs.«KernelCheck::check_const».obs ev with
  | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) ..
  | .Axiom_other_other (hv37 := hv) ..
  | .Defn (hv269 := hv) .. | .Thm (hv526 := hv) ..
  | .Opaque (hv825 := hv) .. | .Quot (hv1076 := hv) ..
  | .Ctor_n0_n0 (hv1941 := hv) .. | .Ctor_n0_other (hv1941 := hv) ..
  | .Ctor_other_n0 (hv1941 := hv) ..
  | .Ctor_other_other (hv1941 := hv) ..
  | .Rec_n0 (hv2631 := hv) .. | .Rec_other (hv2631 := hv) .. =>
    injection hv with _ htag _; exact absurd htag (by decide)
  | .Induct_n0 (m2 := m2) (m1283 := m1283) (m1333 := m1333) (m1354 := m1354)
      (m1376 := m1376) (m1396 := m1396) (m1427 := m1427) (m1440 := m1440) (m1470 := m1470)
      (m1492 := m1492) (cs1529 := cs_sh)
      (ev14 := ev_iu) (hv1240 := hv_ind) (ev1295 := ev_ws)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev_emb)
      (hm1435 := hm1427) (ev1408 := ev_es) (ev1452 := ev_saf)
      (ev1482 := ev_mk) (ev1505 := ev_mod) (ev1531 := ev_sh) (hc1634 := hc) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with hnl hargs; injection hargs with hty hargs
    injection hargs with hnp hargs; injection hargs with hni hargs
    injection hargs with hnc hargs; injection hargs with hiu hargs
    injection hargs with hblk hargs; injection hargs with hidx _
    subst hnl hty hnp hni hnc hiu hblk hidx
    have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc m1283 _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc m1376 _
    have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc m1333 _
    have e_to_1492 : Heap.Extends h m1492 :=
      ev_iu.heap_extends.trans (ev_ws.heap_extends.trans
        (e_1376.trans (e_1354.trans (ev_emb.heap_extends.trans
          (e_1427.trans (ev_es.heap_extends.trans (ev_saf.heap_extends.trans
            (ev_mk.heap_extends.trans ev_mod.heap_extends))))))))
    have hsub_sh : ∀ cl ∈ cs_sh, cl ∈ cs := fun cl hcl => by rw [hc]; simp [hcl]
    match Obs.«KernelCheck::check_inductive_shape».obs ev_sh with
    | .run (m50 := m50s) (m2 := m2s) (m63 := m63s) (m133 := m133s) (cs198 := csl)
        (hm58 := hm58s) (ev14 := ev14s) (ev75 := ev75s) (ev145 := ev145s) (ev200 := evl)
        (hc288 := hcs) .. =>
      have e_50 : Heap.Extends m1492 m50s := by rw [hm58s]; exact Heap.Extends.snoc m1492 _
      have e_to : Heap.Extends h m133s :=
        e_to_1492.trans (e_50.trans (ev14s.heap_extends.trans
          (ev75s.heap_extends.trans ev145s.heap_extends)))
      have hsub_l : ∀ cl ∈ csl, cl ∈ cs_sh := fun cl hcl => by rw [hcs]; simp [hcl]
      have hbp := Bytes.repAddressRef_heapMono₂ Core.addrTy e_to hb
      have hashed := Assembly.native_constructor_hashed ctx hn hi hj n 0
        (by omega) (Nat.zero_le _) hbp evl
      exact Core.hashed_mono (fun cl hcl => hsub_sh cl (hsub_l cl hcl)) hashed
  | .Induct_other_n0 (m2 := m2) (m1283 := m1283) (m1333 := m1333) (m1354 := m1354)
      (m1376 := m1376) (m1396 := m1396) (m1427 := m1427) (m1440 := m1440) (m1470 := m1470)
      (m1492 := m1492) (m1653 := m1653) (m1701 := m1701) (m1745 := m1745) (m1793 := m1793)
      (cs1816 := cs_mc)
      (ev14 := ev_iu) (hv1240 := hv_ind) (ev1295 := ev_ws)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev_emb)
      (hm1435 := hm1427) (ev1408 := ev_es) (ev1452 := ev_saf)
      (ev1482 := ev_mk) (ev1505 := ev_mod) (ev1663 := ev_fa) (ev1711 := ev_tele)
      (hm1801 := hm1793) (ev1757 := ev_rsl) (ev1818 := ev_mc) (hc1926 := hc) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with hnl hargs; injection hargs with hty hargs
    injection hargs with hnp hargs; injection hargs with hni hargs
    injection hargs with hnc hargs; injection hargs with _ hargs
    injection hargs with hblk hargs; injection hargs with hidx _
    subst hnl hty hnp hni hnc hblk hidx
    have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc m1283 _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc m1376 _
    have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc m1333 _
    have e_1793 : Heap.Extends m1701 m1793 := by rw [hm1793]; exact Heap.Extends.snoc m1701 _
    have e_to : Heap.Extends h m1745 :=
      ev_iu.heap_extends.trans (ev_ws.heap_extends.trans
        (e_1376.trans (e_1354.trans (ev_emb.heap_extends.trans
          (e_1427.trans (ev_es.heap_extends.trans (ev_saf.heap_extends.trans
            (ev_mk.heap_extends.trans (ev_mod.heap_extends.trans
              (ev_fa.heap_extends.trans (ev_tele.heap_extends.trans
                (e_1793.trans ev_rsl.heap_extends))))))))))))
    have hsub_mc : ∀ cl ∈ cs_mc, cl ∈ cs := fun cl hcl => by rw [hc]; simp [hcl]
    have hbp := Bytes.repAddressRef_heapMono₂ Core.addrTy e_to hb
    have hashed := Assembly.modeled_constructor_hashed ctx hn hi hj n 0
      (by omega) (Nat.zero_le _) hbp ev_mc
    exact Core.hashed_mono hsub_mc hashed
  | .Induct_other_other (m2 := m2) (m1283 := m1283) (m1333 := m1333) (m1354 := m1354)
      (m1376 := m1376) (m1396 := m1396) (m1427 := m1427) (m1440 := m1440) (m1470 := m1470)
      (m1492 := m1492) (m1653 := m1653) (m1701 := m1701) (m1745 := m1745) (m1793 := m1793)
      (cs1816 := cs_mc)
      (ev14 := ev_iu) (hv1240 := hv_ind) (ev1295 := ev_ws)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev_emb)
      (hm1435 := hm1427) (ev1408 := ev_es) (ev1452 := ev_saf)
      (ev1482 := ev_mk) (ev1505 := ev_mod) (ev1663 := ev_fa) (ev1711 := ev_tele)
      (hm1801 := hm1793) (ev1757 := ev_rsl) (ev1818 := ev_mc) (hc1935 := hc) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with hnl hargs; injection hargs with hty hargs
    injection hargs with hnp hargs; injection hargs with hni hargs
    injection hargs with hnc hargs; injection hargs with hiu hargs
    injection hargs with hblk hargs; injection hargs with hidx _
    subst hnl hty hnp hni hnc hiu hblk hidx
    have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc m1283 _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc m1376 _
    have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc m1333 _
    have e_1793 : Heap.Extends m1701 m1793 := by rw [hm1793]; exact Heap.Extends.snoc m1701 _
    have e_to : Heap.Extends h m1745 :=
      ev_iu.heap_extends.trans (ev_ws.heap_extends.trans
        (e_1376.trans (e_1354.trans (ev_emb.heap_extends.trans
          (e_1427.trans (ev_es.heap_extends.trans (ev_saf.heap_extends.trans
            (ev_mk.heap_extends.trans (ev_mod.heap_extends.trans
              (ev_fa.heap_extends.trans (ev_tele.heap_extends.trans
                (e_1793.trans ev_rsl.heap_extends))))))))))))
    have hsub_mc : ∀ cl ∈ cs_mc, cl ∈ cs := fun cl hcl => by rw [hc]; simp [hcl]
    have hbp := Bytes.repAddressRef_heapMono₂ Core.addrTy e_to hb
    have hashed := Assembly.modeled_constructor_hashed ctx hn hi hj n 0
      (by omega) (Nat.zero_le _) hbp ev_mc
    exact Core.hashed_mono hsub_mc hashed

/-! ## A4: the member and constructor projection records of a top-walked block -/

section Walk

variable {calls : List (Call F)} {E₀ : Ixon.Env}

/-- **A block record is never checked directly**: `Ingress::get_ci` has no arm for a block
record. -/
theorem checked_not_block (hS : LoadedReads.RunStore calls E₀) {bAddr a : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hc : recordOf E₀ a = some c) (hms : c.info = .muts ms)
    (hchk : CheckedLimAt calls bAddr t a lim) : False := by
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    -, -, ha_pre, -, ev_ld, -, hsub_ld, -⟩ := hchk
  obtain ⟨ab, hab, rfl⟩ := ha_pre
  obtain ⟨raw, c', -, hh, hba, hx, -, hhead⟩ := get_ci_head hab ev_ld
  have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
    (Core.hashed_mono hsub_ld hh) hba hx
  subst c'
  exact hhead.notMuts ms hms

/-- **A member the walk checked has its projection record in the store**, and an inductive
member each of its constructors' projection records. -/
theorem member_records (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) {t : Ix.Kernel.RoleTable}
    {bAddr B : _root_.Address} {lim : Option Nat} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i : Nat} {m : Ixon.MutConst}
    (hc : recordOf E₀ B = some c) (hms : c.info = .muts ms) (hm : ms[i]? = some m)
    (hchk : MemberCheckedLimAt calls bAddr t B ms i lim) :
    recordOf E₀ (memberAddr B i m) = some (memberProjection B i m) ∧
      ∀ ind j, m = .indc ind → j < ind.ctors.size →
        recordOf E₀ (ctorAddr B i j) = some (constructorProjection B i j) := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, -, hsub_pa,
    -, -, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hchk
  obtain ⟨b', hb', rfl⟩ := hblk
  obtain ⟨-, -, -, mc, a', hget', ha', hproj, hhashed⟩ :=
    L1.projection_addr_hashed_spec hmem hb' ev_pa
  obtain ⟨iv, hiv⟩ : ∃ iv, ((i : F)).val = iv := ⟨_, rfl⟩
  rw [hiv] at hget' hproj hhashed
  -- the projection record the walk loaded is the one `projection_addr` hashed
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
    obtain ⟨cb, ms'', ind', hbl', hget'', -, nl, ty, np, ni, u, x_blk, b'', hld', hb'',
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

/-! ## A5: a top-walked projection record is a constant address of its block -/

private theorem tables_of_proj {c : Ixon.Constant} (htv : L1.ConstantTablesValid c)
    (hp : Assembly.IsProjInfo c.info) : Ix.Kernel.Reader.emptyTables c = true := by
  obtain ⟨info, sh, rf, un, bd⟩ := c
  have h4 : sh = #[] ∧ rf = #[] ∧ un = #[] ∧ bd = #[] := by
    cases info with
    | dPrj _ => exact htv
    | iPrj _ => exact htv
    | cPrj _ => exact htv
    | rPrj _ => exact htv
    | defn _ => exact (hp : False).elim
    | recr _ => exact (hp : False).elim
    | axio _ => exact (hp : False).elim
    | quot _ => exact (hp : False).elim
    | muts _ => exact (hp : False).elim
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h4
  rfl

/-- **A loaded projection record is its canonical serialization**: with empty tables, at the
hash of its bytes. -/
theorem proj_canon {raw : ByteArray} {c : Ixon.Constant} {a : _root_.Address}
    (hba : Address.blake3Pure raw = a) (hx : Ixon.deConstantExact raw = .ok c)
    (htv : L1.ConstantTablesValid c) (hproj : Assembly.IsProjInfo c.info) :
    c = ⟨c.info, #[], #[], #[], #[]⟩ ∧ a = Address.blake3Pure (Ixon.serConstant c) := by
  have hemp := tables_of_proj htv hproj
  obtain ⟨hraw, -⟩ := Assembly.deConstantExact_proj_eq_serConstant hx hemp hproj
  refine ⟨Ix.Cert.ReadingKeys.empty_constant hemp, ?_⟩
  rw [← hba, hraw]

/-- **A projection record the walk checked is a constant address of its block**, which the
store holds. -/
theorem proj_member_of_checked (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) {bAddr a : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {c : Ixon.Constant}
    (hc : recordOf E₀ a = some c) (hpr : Typing.IsProj c)
    (hchk : CheckedLimAt calls bAddr t a lim) :
    ∃ cb, recordOf E₀ (Ix.Cert.ownerOf a c) = some cb ∧
      Typing.ConstAddrOf (Ix.Cert.ownerOf a c) cb a := by
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    -, -, ha_pre, -, ev_ld, -, hsub_ld, -⟩ := hchk
  obtain ⟨ab, hab, rfl⟩ := ha_pre
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
    obtain ⟨cb, ms, ind, hbl, hmem, hlt⟩ := hhead.cPrj idx cidx blk hp
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
    obtain ⟨cb, ms, rc, hbl, hmem⟩ := hhead.rPrj idx blk hp
    obtain ⟨hrec, hinfo⟩ := (hbl.mono hsub_ld).stored hcov
    have hcm : c = memberProjection blk idx.toNat (.recr rc) := by
      rw [memberProjection_recr, ← hp]
      exact hcanon
    rw [hcm] at hab_eq ⊢
    rw [Typing.ownerOf_memberProjection]
    exact ⟨cb, hrec, Or.inr ⟨ms, idx.toNat, .recr rc, hinfo,
      by rw [← Array.getElem?_toList]; exact hmem, Or.inl hab_eq⟩⟩

end Walk

/-! ## The two clauses of the walk export -/

/-- **A4: a top-walked block's member and constructor projection records are in the run
store.** -/
theorem TopWalkCore.members {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ : Ixon.Env}
    {lim : Option Nat} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank) :
    ∀ B c ms, Top B → recordOf E₀ B = some c → c.info = .muts ms →
      ∀ i m, ms[i]? = some m →
        recordOf E₀ (memberAddr B i m) = some (memberProjection B i m) ∧
        ∀ ind j, m = .indc ind → j < ind.ctors.size →
          recordOf E₀ (ctorAddr B i j) = some (constructorProjection B i j) := by
  intro B c ms hTB hc hms i m hm
  obtain ⟨c', hc', hchk⟩ := hW.checked B hTB
  have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  rcases hchk with ⟨ms', hms', hk⟩ | hdirect
  · have hmm : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
    subst ms'
    exact member_records hW.runStore hW.hashedStored hc hms hm
      (hk i (Array.getElem?_eq_some_iff.mp hm).1)
  · exact (checked_not_block hW.runStore hc hms hdirect).elim

/-- **A5: a top-walked projection record is at a member's or a constructor's address of its
block.** -/
theorem TopWalkCore.projMember {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ : Ixon.Env}
    {lim : Option Nat} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank) :
    ∀ a c, Top a → recordOf E₀ a = some c → Typing.IsProj c →
      ∃ cb, recordOf E₀ (Ix.Cert.ownerOf a c) = some cb ∧
        Typing.ConstAddrOf (Ix.Cert.ownerOf a c) cb a := by
  intro a c hTa hc hpr
  obtain ⟨c', hc', hchk⟩ := hW.checked a hTa
  have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  rcases hchk with ⟨ms, hms, -⟩ | hdirect
  · exact (Typing.proj_not_block hpr ⟨ms, hms⟩).elim
  · exact proj_member_of_checked hW.runStore hW.hashedStored hc hpr hdirect

end IxVM.Refinement.Claim
