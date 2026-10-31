import Ix.RoleBinding.ArtifactTiered
import Ix.CompileCert.Loop
import Ix.CompileCert.Canon.QSort
import IxC.Kernel.Admission.TierTheorems

namespace Ix.RoleBinding.Artifact
open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Admission Ix.CompileCert.Loop

private abbrev OrderState := Std.HashSet Address × Array (Address × ByteArray) × Array (Address × Ixon.Constant)
private def OrderInv (artifact : Ixon.Env) (store : Ixon.CheckOrder.RecordStore)
    (prior : List Address) (state : OrderState) : Prop :=
  (∀ a, state.1.contains a = true ↔ a ∈ prior) ∧ prior.Nodup ∧
  state.2.1.toList.map Prod.fst = prior ∧ state.2.2.toList.map Prod.fst = prior ∧
  (∀ row ∈ state.2.1.toList, (artifact.consts[row.1]?).map Ixon.LazyConstant.rawBytes = some row.2) ∧
  (∀ row ∈ state.2.2.toList, store[row.1]? = some row.2)

structure Materialized (artifact : Ixon.Env) (store : Ixon.CheckOrder.RecordStore)
    (order : Array Address) (records : Records) (constants : Ingress.Constants) : Prop where
  recordKeys : records.map Prod.fst = order.toList
  constantKeys : constants.map Prod.fst = order.toList
  unique : order.toList.Nodup
  owned : ∀ row ∈ records, (artifact.consts[row.1]?).map Ixon.LazyConstant.rawBytes = some row.2
  decoded : ∀ row ∈ constants, store[row.1]? = some row.2

theorem materializeOrder_sound {artifact store order records constants}
    (accepted : materializeOrder artifact store order = .ok (records,constants)) :
    Materialized artifact store order records constants := by
  unfold materializeOrder at accepted
  obtain ⟨state,loop,returned⟩ := except_bind_ok.mp accepted
  have invariant : OrderInv artifact store order.toList state := by
    refine forIn_inv_array (OrderInv artifact store) _ order ?_ (by simp [OrderInv]) loop
    intro prior address post state result _ before stepped
    obtain ⟨seen,unique,keys,constantKeys,owned,decoded⟩ := before
    dsimp only at stepped
    split at stepped
    · cases stepped
    · rename_i fresh
      cases raw : artifact.consts[address]? with
      | none => simp [raw,bind,Except.bind] at stepped
      | some record =>
        cases current : store[address]? with
        | none => simp [raw,current,bind,Except.bind] at stepped
        | some constant =>
          simp only [raw,current,pure,Except.pure,Except.ok.injEq] at stepped
          cases stepped
          refine ⟨_,rfl,?_,?_,?_,?_,?_,?_⟩
          · intro a
            simp only [Std.HashSet.contains_insert,Bool.or_eq_true_iff,beq_iff_eq,seen,
              List.mem_append,List.mem_singleton]
            simp only [eq_comm,or_comm]
          · have absent : address ∉ prior := fun member => fresh ((seen address).mpr member)
            simpa [List.nodup_append,unique] using
              (fun (a : Address) (member : a ∈ prior) (same : a = address) => absent (same ▸ member))
          · simpa only [Array.toList_push,List.map_append,List.map_cons,List.map_nil] using
              congrArg (· ++ [address]) keys
          · simpa only [Array.toList_push,List.map_append,List.map_cons,List.map_nil] using
              congrArg (· ++ [address]) constantKeys
          · intro row member
            rw [Array.toList_push] at member
            rcases List.mem_append.mp member with prior | last
            · exact owned row prior
            · have same : row = (address,record.rawBytes) := by simpa using last
              cases same; simp [raw]
          · intro row member
            rw [Array.toList_push] at member
            rcases List.mem_append.mp member with prior | last
            · exact decoded row prior
            · have same : row = (address,constant) := by simpa using last
              cases same; exact current
  cases returned
  exact ⟨invariant.2.2.1,invariant.2.2.2.1,invariant.2.1,invariant.2.2.2.2.1,invariant.2.2.2.2.2⟩

private theorem qsort_size (xs : Array α) (lt : α → α → Bool) (lo hi : Nat) :
    (xs.qsort lt lo hi).size = xs.size := by
  unfold Array.qsort
  split <;> simp

/-- Explicit order selection survives the authenticated preparation boundary.
The supplied order cannot silently turn back into wholeEnv. -/
theorem prepareRecordsAt_order {artifact : Ixon.Env} {limits : Limits} {order : Array Address}
    {input : PreparedRecords} (accepted : prepareRecordsAt artifact limits order = .ok input) :
    order.size = artifact.consts.size ∧ ∃ original,
      decodeRecords limits ((artifact.consts.toArray.map fun (a,c) => (a,c.rawBytes)).qsort
        (fun x y => x.1.cmpBytes y.1 == .lt)).toList = .ok original ∧
      Materialized artifact (original.foldl (fun m (a,c) => m.insert a c) {})
        order input.prepared.records input.constants := by
  unfold prepareRecordsAt prepareRecordsFor at accepted
  cases binding : artifact.roleBinding with
  | none => simp [binding] at accepted
  | some raw =>
    simp only [binding] at accepted
    obtain ⟨_,_,rest⟩ := except_bind_ok.mp accepted
    obtain ⟨_,_,rest⟩ := except_bind_ok.mp rest
    obtain ⟨_,_,rest⟩ := except_bind_ok.mp rest
    obtain ⟨table,_,rest⟩ := except_bind_ok.mp rest
    obtain ⟨constants,decoded,rest⟩ := except_bind_ok.mp rest
    obtain ⟨_,_,rest⟩ := except_bind_ok.mp rest
    obtain ⟨_,_,rest⟩ := except_bind_ok.mp rest
    obtain ⟨pre,_,rest⟩ := except_bind_ok.mp rest
    obtain ⟨_,_,rest⟩ := except_bind_ok.mp rest
    obtain ⟨_,_,rest⟩ := except_bind_ok.mp rest
    simp only [qsort_size,Array.size_map,Std.HashMap.size_toArray] at rest
    by_cases size : order.size = artifact.consts.size
    · simp [size] at rest
      obtain ⟨⟨records,readConstants⟩,ordered,returned⟩ := except_bind_ok.mp rest
      cases returned
      refine ⟨size,constants,?_,materializeOrder_sound ordered⟩
      cases h : decodeRecords limits _ <;> simp_all [Except.mapError]
    · simp [size,throw,throwThe,MonadExceptOf.throw,bind,Except.bind] at rest

/-- The selected records are a permutation of every actual (address,bytes)
row. Membership in the winning map supplies bytes, not address injectivity. -/
theorem Materialized.complete {artifact store order records constants}
    (selected : Materialized artifact store order records constants)
    (size : order.size = artifact.consts.size) :
    records.Perm (artifact.consts.toList.map fun (a,c) => (a,c.rawBytes)) := by
  let original := artifact.consts.toList.map fun (a,c) => (a,c.rawBytes)
  have member (row : Address × ByteArray) : row ∈ original ↔
      (artifact.consts[row.1]?).map Ixon.LazyConstant.rawBytes = some row.2 := by
    rcases row with ⟨a,bytes⟩
    simp only [original,List.mem_map,Prod.exists,Prod.mk.injEq,Option.map_eq_some_iff]
    constructor
    · rintro ⟨key,value,present,rfl,rfl⟩
      exact ⟨value,Std.HashMap.mem_toList_iff_getElem?_eq_some.mp present,rfl⟩
    · rintro ⟨value,found,rfl⟩
      exact ⟨a,value,Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr found,rfl,rfl⟩
  have keyUnique : (original.map Prod.fst).Nodup := by
    simpa only [original,List.map_map,Function.comp_def,Std.HashMap.map_fst_toList_eq_keys]
      using artifact.consts.nodup_keys
  have recordKeysUnique : (records.map Prod.fst).Nodup := selected.recordKeys.symm ▸ selected.unique
  have unique : records.Nodup :=
    recordKeysUnique.of_map Prod.fst
      (fun _ _ different same => different (congrArg Prod.fst same))
  have originalUnique : original.Nodup := keyUnique.of_map Prod.fst
    (fun _ _ different same => different (congrArg Prod.fst same))
  have included : records ⊆ original := fun row present => (member row).mpr (selected.owned row present)
  have length : records.length = original.length := by
    have keys := congrArg List.length selected.recordKeys
    simpa [original,size] using keys
  apply (List.perm_ext_iff_of_nodup unique originalUnique).mpr
  intro row
  refine ⟨fun present => included present,fun present => ?_⟩
  by_contra missing
  have more : (row :: records).Nodup := List.nodup_cons.mpr ⟨missing,unique⟩
  have subset : row :: records ⊆ original := by
    intro a membership
    rcases List.mem_cons.mp membership with rfl | membership
    · exact present
    · exact included membership
  have bound := more.length_le_of_subset subset
  simp only [List.length_cons] at bound
  omega

private theorem mapError_ok {result : Except ε α} {f : ε → ε'} {value : α}
    (accepted : result.mapError f = .ok value) : result = .ok value := by
  cases result with
  | error => simp [Except.mapError] at accepted
  | ok => simpa only [Except.mapError,Except.ok.injEq] using accepted

private theorem fold_origin {rows : Ingress.Constants} {store : Ixon.CheckOrder.RecordStore}
    {a : Address} {c : Ixon.Constant}
    (found : (rows.foldl (fun m (a,c) => m.insert a c) store)[a]? = some c) :
    store[a]? = some c ∨ (a,c) ∈ rows := by
  induction rows generalizing store with
  | nil => exact Or.inl found
  | cons row rows ih =>
    rcases ih found with prior | member
    · by_cases same : row.1 = a
      · rcases row with ⟨key,value⟩
        dsimp only at same
        subst key
        rw [Std.HashMap.getElem?_insert_self] at prior
        cases prior
        exact Or.inr List.mem_cons_self
      · exact Or.inl (by simpa [Std.HashMap.getElem?_insert,same] using prior)
    · exact Or.inr (List.mem_cons_of_mem _ member)

private theorem read_member {limits rows constants} (reading : RecordsRead limits rows constants) :
    ∀ pair ∈ constants, ∃ bytes, (pair.1,bytes) ∈ rows ∧
      Ixon.Verify.Canonical.Reads limits.maxRecordBytes limits.maxRecordUnivNodes bytes pair.2 := by
  induction reading with
  | nil => simp
  | cons first _ ih =>
    intro pair member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,List.mem_cons_self,first⟩
    · obtain ⟨bytes,present,reads⟩ := ih pair member
      exact ⟨bytes,List.mem_cons_of_mem _ present,reads⟩

/-- The selected decoded winners are exactly the canonical reading of the
selected raw rows. Thus tier preparation and byte admission partition the
same constants, with no host-decoder or hash-injectivity assumption. -/
theorem prepareRecordsAt_reading {artifact limits order input}
    (accepted : prepareRecordsAt artifact limits order = .ok input) :
    decodeRecords limits input.prepared.records = .ok input.constants := by
  obtain ⟨_,original,decoded,selected⟩ := prepareRecordsAt_order accepted
  let store : Ixon.CheckOrder.RecordStore := original.foldl (fun m (a,c) => m.insert a c) {}
  have storeReads (a : Address) (c : Ixon.Constant) (found : store[a]? = some c) :
      ∃ raw, artifact.consts[a]? = some raw ∧
        Ixon.Verify.Canonical.Reads limits.maxRecordBytes limits.maxRecordUnivNodes raw.rawBytes c := by
    have present : (a,c) ∈ original := by
      rcases fold_origin found with empty | member
      · simp at empty
      · exact member
    obtain ⟨bytes,row,reads⟩ := read_member ((decodeRecords_ok_iff ..).mp decoded) (a,c) present
    have unsorted := Ix.CompileCert.Canon.mem_qsort.mp (Array.mem_toList_iff.mp row)
    obtain ⟨⟨key,raw⟩,member,same⟩ := Array.mem_map.mp unsorted
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
    exact ⟨raw,Std.HashMap.mem_toArray_iff_getElem?_eq_some.mp member,reads⟩
  apply (decodeRecords_ok_iff ..).mpr
  have keys := selected.recordKeys.trans selected.constantKeys.symm
  have owned := selected.owned
  have values := selected.decoded
  generalize input.prepared.records = records at keys owned ⊢
  generalize input.constants = constants at keys values ⊢
  induction records generalizing constants with
  | nil =>
    cases constants with
    | nil => exact .nil
    | cons => simp at keys
  | cons row records ih =>
    cases constants with
    | nil => simp at keys
    | cons pair constants =>
      obtain ⟨same,tailKeys⟩ := List.cons.inj keys
      have lookup := values pair List.mem_cons_self
      obtain ⟨raw,rawFound,reads⟩ := storeReads pair.1 pair.2 lookup
      have bytes := owned row List.mem_cons_self
      rw [same,rawFound] at bytes
      have sameBytes : raw.rawBytes = row.2 := Option.some.inj bytes
      rcases row with ⟨a,bytes⟩
      rcases pair with ⟨key,value⟩
      dsimp only at same sameBytes
      subst key
      refine .cons (sameBytes ▸ reads) (ih ?_ constants tailKeys ?_)
      · exact fun row member => owned row (List.mem_cons_of_mem _ member)
      · exact fun pair member => values pair (List.mem_cons_of_mem _ member)

/-- Exact order and full-byte permutation; no row can be dropped or added. -/
structure CompleteOrder (artifact : Ixon.Env) (order : Array Address) (records : Records) : Prop where
  keys : records.map Prod.fst = order.toList
  unique : order.toList.Nodup
  rows : records.Perm (artifact.consts.toList.map fun (a,c) => (a,c.rawBytes))

theorem prepareRecordsAt_complete {artifact limits order input}
    (accepted : prepareRecordsAt artifact limits order = .ok input) :
    CompleteOrder artifact order input.prepared.records := by
  obtain ⟨size,_,_,selected⟩ := prepareRecordsAt_order accepted
  exact ⟨selected.recordKeys,selected.unique,selected.complete size⟩

theorem prepareAt_obligations {artifact limits order p}
    (accepted : prepareAt artifact limits order = .ok p) :
    ∃ input evidence declarations,
      prepareRecordsAt artifact limits order = .ok input ∧ input.prepared = p ∧
      decodeRecords limits p.records = .ok input.constants ∧
      prepareWith Address.admissionHash p.binding p.pre limits p.records p.blobs p.hints.lookup =
        .ok (evidence,declarations) ∧ checkEvidence p.table evidence declarations = .ok () := by
  unfold prepareAt prepareFor at accepted
  obtain ⟨input,first,rest⟩ := except_bind_ok.mp accepted
  obtain ⟨⟨evidence,declarations⟩,read,rest⟩ := except_bind_ok.mp rest
  obtain ⟨⟨⟩,checked,returned⟩ := except_bind_ok.mp rest
  cases returned
  exact ⟨input,evidence,declarations,first,rfl,prepareRecordsAt_reading first,mapError_ok read,checked⟩

/-- The census, fence and logical evidence all belong to the partition of
this chosen complete order. Success cannot bypass a logical failure. -/
theorem prepareTieredAt_obligations {artifact limits order p}
    (accepted : prepareTieredAt artifact limits order = .ok p) :
    ∃ input, prepareRecordsAt artifact limits order = .ok input ∧ input.prepared = p ∧
      decodeRecords limits p.records = .ok input.constants ∧
      let (logical,tier) := partitionTier input.constants
      logical.length + tier.size = input.constants.length ∧ fenceOf logical tier = none ∧
      ∃ evidence declarations,
        readStream Address.admissionHash p.table p.pre logical p.blobs p.hints.lookup =
          .ok (evidence,declarations) ∧
        checkEvidence p.table evidence (Frontend.preparePrelude p.pre.ix declarations) = .ok () := by
  unfold prepareTieredAt prepareTieredFor at accepted
  obtain ⟨input,first,rest⟩ := except_bind_ok.mp accepted
  have fromInput : prepareRecordsAt artifact limits order = .ok input := mapError_ok first
  dsimp only at rest
  generalize partitioned : partitionTier input.constants = parts at rest
  obtain ⟨logical,tier⟩ := parts
  by_cases census : logical.length + tier.size = input.constants.length
  · simp only [beq_iff_eq,census,ite_true] at rest
    cases fenced : fenceOf logical tier with
    | some pair => simp [fenced,throw,throwThe,MonadExceptOf.throw,bind,Except.bind] at rest
    | none =>
      simp only [fenced] at rest
      obtain ⟨⟨evidence,declarations⟩,read,rest⟩ := except_bind_ok.mp rest
      obtain ⟨⟨⟩,checked,returned⟩ := except_bind_ok.mp rest
      cases returned
      refine ⟨input,fromInput,rfl,prepareRecordsAt_reading fromInput,?_⟩
      simp only [partitioned]
      exact ⟨census,fenced,evidence,declarations,mapError_ok read,mapError_ok checked⟩
  · simp [census,throw,throwThe,MonadExceptOf.throw,bind,Except.bind] at rest

theorem OrderedReceipt.complete {artifact limits order} (receipt : OrderedReceipt artifact limits order) :
    CompleteOrder artifact order receipt.prepared.records := by
  obtain ⟨input,_,_,fromInput,same,_,_,_⟩ := prepareAt_obligations receipt.preparedFrom
  exact same ▸ prepareRecordsAt_complete fromInput

theorem OrderedTierReceipt.complete {artifact limits order}
    (receipt : OrderedTierReceipt artifact limits order) :
    CompleteOrder artifact order receipt.prepared.records := by
  obtain ⟨input,fromInput,same,_,_⟩ := prepareTieredAt_obligations receipt.preparedFrom
  exact same ▸ prepareRecordsAt_complete fromInput

/-- For one artifact/limits/order, the actual target is unique. This does
not compare targets of different orders or choose a replacement model. -/
theorem OrderedReceipt.target_unique {artifact limits order}
    (left right : OrderedReceipt artifact limits order) : left.target = right.target := by
  have same : left.prepared = right.prepared := Except.ok.inj (left.preparedFrom.symm.trans right.preparedFrom)
  have checked := left.checked
  rw [same] at checked
  exact Except.ok.inj (checked.symm.trans right.checked)

theorem OrderedTierReceipt.target_unique {artifact limits order}
    (left right : OrderedTierReceipt artifact limits order) :
    (left.logical,left.tier) = (right.logical,right.tier) := by
  have same : left.prepared = right.prepared := Except.ok.inj (left.preparedFrom.symm.trans right.preparedFrom)
  have checked := left.checked
  rw [same] at checked
  exact Except.ok.inj (checked.symm.trans right.checked)

theorem OrderedReceipt.authentic {artifact limits order}
    (receipt : OrderedReceipt artifact limits order) :
    Authentic Address.admissionHash receipt.prepared.records receipt.prepared.blobs ∧
      Address.admissionHash receipt.prepared.binding.bytes = receipt.prepared.binding.address :=
  checkBytesWith_authentic receipt.checked

theorem OrderedTierReceipt.authentic {artifact limits order}
    (receipt : OrderedTierReceipt artifact limits order) :
    Authentic Address.admissionHash receipt.prepared.records receipt.prepared.blobs ∧
      Address.admissionHash receipt.prepared.binding.bytes = receipt.prepared.binding.address := by
  obtain ⟨authentic,_,_,_,admitted,_,_,_⟩ := checkBytesTieredUsing_ok receipt.checked
  exact ⟨authentic,((admitBinding_ok_iff ..).mp admitted).authentic⟩

end Ix.RoleBinding.Artifact
