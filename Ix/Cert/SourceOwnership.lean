import Ix.Compile.SourceInput.Ownership
import Ix.Cert.SourceMetadata
import Ix.RoleBinding.ArtifactOrderTheorems

namespace Ix.Cert.SourceOwnership
open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Admission
open Ix.Compile.SourceInput Ix.Compile.SourceInput.Ownership

/- The following first-winner store argument reuses ReaderClosureKeys'
recordStep/recordFold proof, without importing its compiler-index proofs. -/
private def step (m : Ixon.CheckOrder.RecordStore) (p : Address × Ixon.Constant) :=
  if m.contains p.1 then m else m.insert p.1 p.2
private theorem step_keeps (m : Ixon.CheckOrder.RecordStore) (p : Address × Ixon.Constant)
    {a : Address} {c : Ixon.Constant} (h : m[a]? = some c) : (step m p)[a]? = some c := by
  unfold step
  split
  · exact h
  · rename_i missing
    rw [Std.HashMap.getElem?_insert]
    split
    · rename_i same
      have same : p.1 = a := beq_iff_eq.mp same
      rw [same,Std.HashMap.contains_eq_isSome_getElem?,h] at missing
      exact (missing rfl).elim
    · exact h
private theorem fold_get (xs : List (Address × Ixon.Constant)) (m : Ixon.CheckOrder.RecordStore)
    (a : Address) : (xs.foldl step m)[a]? = (m[a]? <|> xs.lookup a) := by
  induction xs generalizing m with
  | nil => simp
  | cons p xs ih =>
    rw [List.foldl_cons,ih,List.lookup_cons]
    cases h : m[a]? with
    | some c => rw [step_keeps m p h]; rfl
    | none =>
      by_cases same : p.1 = a
      · rcases p with ⟨key,c⟩; dsimp only at same; subst key
        simp [step,Std.HashMap.contains_eq_isSome_getElem?,h]
      · have left := beq_eq_false_iff_ne.mpr (Ne.symm same)
        have right := beq_eq_false_iff_ne.mpr same
        simp only [step]
        split <;> simp [Std.HashMap.getElem?_insert,left,right,h]

/-- The actual reader's first-winner lookup, on this exact decoded input. -/
theorem lookup_spec (index : PhysicalIndex) (a : Address) :
    index.store[a]? = index.input.constants.lookup a := by
  rw [index.built,recordMap,← Array.foldl_toList]
  exact (fold_get index.input.constants {} a).trans (by simp)

theorem lookup_origin {index : PhysicalIndex} {a : Address} {c : Ixon.Constant}
    (found : index.store[a]? = some c) : (a,c) ∈ index.input.constants := by
  rw [lookup_spec] at found
  obtain ⟨left,right,equal,_⟩ := List.lookup_eq_some_iff.mp found
  rw [equal]
  exact List.mem_append.mpr (.inr List.mem_cons_self)

theorem lookup_none_iff (index : PhysicalIndex) (a : Address) :
    index.store[a]? = none ↔ a ∉ index.input.constants.map Prod.fst := by
  rw [lookup_spec,List.lookup_eq_none_iff]
  constructor
  · intro absent present
    obtain ⟨p,member,same⟩ := List.mem_map.mp present
    exact (bne_iff_ne.mp (absent p member)) same.symm
  · intro absent p member
    apply bne_iff_ne.mpr
    intro same
    exact absent (List.mem_map.mpr ⟨p,member,same.symm⟩)

theorem rows_at (index : PhysicalIndex) (i : Nat) :
    (observeRows index)[i]? = (index.input.constants[i]?).map fun (a,c) =>
      ⟨i,a,observeRecord index a c⟩ := by
  simp [observeRows,List.getElem?_zipIdx,Option.map_map,Function.comp_def]

theorem rows_complete (index : PhysicalIndex) :
    (observeRows index).length = index.input.constants.length ∧
      (observeRows index).map Row.address = index.input.constants.map Prod.fst := by
  constructor
  · simp [observeRows]
  · simp only [observeRows,List.map_map,Function.comp_def]
    have names := congrArg (List.map Prod.fst) (List.zipIdx_map_fst 0 index.input.constants)
    simpa only [List.map_map,Function.comp_def] using names

theorem owner_fields (index : PhysicalIndex) (a : Address) (c : Ixon.Constant) :
    (observeRecord index a c).owner = Ixon.CheckOrder.owner a c ∧
      (observeRecord index a c).ownerRecord = index.store[Ixon.CheckOrder.owner a c]? := ⟨rfl,rfl⟩

theorem aggregate_iff (index : PhysicalIndex) (a : Address) (c : Ixon.Constant) (n : Nat) :
    (observeRecord index a c).resolution = .aggregate n ↔
      ∃ members, c.info = .muts members ∧ members.size = n := by
  cases kind : c.info <;> cases ran : resolveSource (index.store[·]?) a c <;>
    simp [observeRecord,kind,ran]

def IsProjection (c : Ixon.Constant) : Prop := match c.info with
  | .dPrj _ | .iPrj _ | .rPrj _ | .cPrj _ => True
  | _ => False

theorem unresolved_projection {index : PhysicalIndex} {a : Address} {c : Ixon.Constant}
    (unresolved : (observeRecord index a c).resolution = .unresolvedProjection) :
    IsProjection c ∧ resolveSource (index.store[·]?) a c = none := by
  cases kind : c.info <;> cases ran : resolveSource (index.store[·]?) a c <;>
    simp_all [observeRecord,IsProjection,resolveSource]

theorem resolved_run {index : PhysicalIndex} {a : Address} {c : Ixon.Constant} {ref : ConstRef Address}
    (resolved : (observeRecord index a c).resolution = .resolved ref) :
    resolveSource (index.store[·]?) a c = some ref := by
  cases kind : c.info <;> cases ran : resolveSource (index.store[·]?) a c <;>
    simp_all [observeRecord]

/-- This records only a reference's shape. It does not validate projection
tables, owners, kinds or indices; resolve_reference requires the actual run. -/
def referenceShape (a : Address) (c : Ixon.Constant) : Option (ConstRef Address) := match c.info with
  | .muts _ => none
  | .dPrj p | .iPrj p | .rPrj p => some (.member p.block p.idx.toNat)
  | .cPrj p => some (.ctor p.block p.idx.toNat p.cidx.toNat)
  | _ => some (.member a 0)

/-- Actual resolution success fixes the complete reference, including its
member/constructor indices. The existing guards are not replaced by shape. -/
theorem resolve_reference {store : Store} {a : Address} {c : Ixon.Constant} {ref : ConstRef Address}
    (ran : resolveSource store a c = some ref) : referenceShape a c = some ref := by
  cases kind : c.info <;> simp only [resolveSource,kind] at ran
  all_goals first
    | (solve | cases ran <;> simp [referenceShape,kind])
    | skip
  all_goals
    obtain ⟨_,_,ran⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨ownerRecord,_,ran⟩ := Option.bind_eq_some_iff.mp ran
    cases ownerKind : ownerRecord.info <;> simp only [ownerKind] at ran
  all_goals first | (solve | cases ran) | skip
  all_goals
    obtain ⟨member,_,ran⟩ := Option.bind_eq_some_iff.mp ran
    cases member <;> dsimp only at ran
  all_goals first
    | (solve | cases ran <;> simp [referenceShape,kind])
    | skip
  all_goals
    obtain ⟨constructor,_,ran⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨_,_,ran⟩ := Option.bind_eq_some_iff.mp ran
    cases ran
    simp [referenceShape,kind]

theorem resolve_owner {store : Store} {a : Address} {c : Ixon.Constant} {ref : ConstRef Address}
    (ran : resolveSource store a c = some ref) : ref.block = Ixon.CheckOrder.owner a c := by
  have shape := resolve_reference ran
  cases kind : c.info <;> simp [referenceShape,kind] at shape
  all_goals subst ref
  all_goals simp [Ixon.CheckOrder.owner,kind]

theorem probe_absent_iff (index : PhysicalIndex) (a : Address) :
    probeAddress index a = .absent a ↔ index.store[a]? = none := by
  cases found : index.store[a]? <;> simp [probeAddress,found]

theorem publication_unpublished_iff (index : PhysicalIndex) (address : Option Address) :
    probePublication index address = .unpublished ↔ address = none := by
  cases address <;> simp [probePublication]

theorem named_absent_iff (index : PhysicalIndex) (entries : Ix.Map Ix.Name Ixon.Named) (query : Ix.Name) :
    probeNamed index entries query = .absent ↔ entries.get? query = none := by
  cases found : entries.get? query <;> simp only [probeNamed,found,reduceCtorEq]

theorem named_found {index : PhysicalIndex} {entries : Ix.Map Ix.Name Ixon.Named} {query : Ix.Name}
    {entry : Ixon.Named} (found : entries.get? query = some entry) :
    probeNamed index entries query = .found (entries.getKey? query) entry (probeAddress index entry.addr)
      (entry.original.map fun original => probeAddress index original.1) := by
  simp only [probeNamed,found]

/-- Four separate literal CURRENT lookup equations. None identifies the
compiler's final named registry with primary/aux resolution or the artifact. -/
theorem publication_fields (cenv : Ix.CompileM.CompileEnv) (artifact : Ixon.Env) (index : PhysicalIndex)
    (query : Ix.Name) :
    (probeName cenv artifact index query).primary = probePublication index (cenv.nameToAddr.get? query) ∧
    (probeName cenv artifact index query).auxiliary = probePublication index (cenv.auxNameToAddr.get? query) ∧
    (probeName cenv artifact index query).compilerNamed = probeNamed index cenv.nameToNamed query ∧
    (probeName cenv artifact index query).artifactNamed = probeNamed index artifact.named query :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem source_fields (carrier : Carrier) (cenv : Ix.CompileM.CompileEnv) (artifact : Ixon.Env)
    (index : PhysicalIndex) (query : Ix.Name) :
    (observeAt carrier cenv artifact index query).query = query ∧
    (observeAt carrier cenv artifact index query).sourceRepresentative = carrier.representative? query ∧
    (observeAt carrier cenv artifact index query).self = probeName cenv artifact index query := ⟨rfl,rfl,rfl⟩

theorem metadata_result (carrier : Carrier) (cenv : Ix.CompileM.CompileEnv) (artifact : Ixon.Env)
    (index : PhysicalIndex) (query : Ix.Name) :
    (List.map Prod.fst) <$> (observeAt carrier cenv artifact index query).metadata =
      carrier.captureMetadataAt query := by
  cases result : carrier.captureMetadataAt query <;>
    simp [observeAt,result,Functor.map,Except.map,List.map_map,Function.comp_def]

theorem metadata_error {carrier : Carrier} {cenv artifact index query error}
    (failed : carrier.captureMetadataAt query = .error error) :
    (observeAt carrier cenv artifact index query).metadata = .error error := by
  simp only [observeAt,failed,Functor.map,Except.map]

theorem prepared_metadata {input : Ix.Compile.CompileInput} {raw : List Raw}
    (prepared : input.prepare = .ok raw) {query : Ix.Name} {ci : Ix.ConstantInfo}
    (declared : (SourceGraph.full (SourceStream.canonical raw.toArray)).consts.get? query = some ci)
    (cenv : Ix.CompileM.CompileEnv) (artifact : Ixon.Env) (index : PhysicalIndex) :
    (observeAt (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw.toArray)) cenv artifact index query).metadata =
      .ok ((Metadata.capture ci).map fun ref => (ref,probeName cenv artifact index ref.name)) := by
  simp only [observeAt,SourceMetadata.prepared_capture prepared declared,Functor.map,Except.map]

/-- Completeness and byte decoding come from an actual C2 success, not the
ability to construct an observation from a freely supplied PreparedRecords. -/
theorem prepared_rows {artifact : Ixon.Env} {limits : Limits} {order : Array Address}
    {input : Ix.RoleBinding.Artifact.PreparedRecords}
    (accepted : Ix.RoleBinding.Artifact.prepareRecordsAt artifact limits order = .ok input) :
    let index := PhysicalIndex.ofPrepared input
    (observeRows index).map Row.address = order.toList ∧ order.toList.Nodup ∧
      input.prepared.records.Perm (artifact.consts.toList.map fun (a,c) => (a,c.rawBytes)) ∧
      decodeRecords limits input.prepared.records = .ok input.constants := by
  obtain ⟨_,_,_,selected⟩ := Ix.RoleBinding.Artifact.prepareRecordsAt_order accepted
  have complete := Ix.RoleBinding.Artifact.prepareRecordsAt_complete accepted
  exact ⟨(rows_complete _).2.trans selected.constantKeys,selected.unique,complete.rows,
    Ix.RoleBinding.Artifact.prepareRecordsAt_reading accepted⟩

/-- These authenticated wrappers extract the observed input from the actual
receipt. Raw observation construction alone supplies no authentication. -/
theorem ordered_receipt {artifact limits order}
    (receipt : Ix.RoleBinding.Artifact.OrderedReceipt artifact limits order) :
    ∃ input, Ix.RoleBinding.Artifact.prepareRecordsAt artifact limits order = .ok input ∧
      input.prepared = receipt.prepared ∧
      (observeRows (PhysicalIndex.ofPrepared input)).map Row.address = order.toList ∧
      Authentic Address.admissionHash input.prepared.records input.prepared.blobs ∧
      Address.admissionHash input.prepared.binding.bytes = input.prepared.binding.address := by
  obtain ⟨input,_,_,accepted,same,_,_,_⟩ :=
    Ix.RoleBinding.Artifact.prepareAt_obligations receipt.preparedFrom
  exact ⟨input,accepted,same,(prepared_rows accepted).1,same.symm ▸ receipt.authentic⟩

theorem ordered_tier_receipt {artifact limits order}
    (receipt : Ix.RoleBinding.Artifact.OrderedTierReceipt artifact limits order) :
    ∃ input, Ix.RoleBinding.Artifact.prepareRecordsAt artifact limits order = .ok input ∧
      input.prepared = receipt.prepared ∧
      (observeRows (PhysicalIndex.ofPrepared input)).map Row.address = order.toList ∧
      Authentic Address.admissionHash input.prepared.records input.prepared.blobs ∧
      Address.admissionHash input.prepared.binding.bytes = input.prepared.binding.address := by
  obtain ⟨input,accepted,same,_,_⟩ :=
    Ix.RoleBinding.Artifact.prepareTieredAt_obligations receipt.preparedFrom
  exact ⟨input,accepted,same,(prepared_rows accepted).1,same.symm ▸ receipt.authentic⟩

#guard_kernel_axioms lookup_spec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms lookup_none_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms rows_complete [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms aggregate_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms unresolved_projection [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms resolve_reference [propext, Quot.sound]
#guard_kernel_axioms resolve_owner [propext, Quot.sound]
#guard_kernel_axioms publication_fields [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms source_fields [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms metadata_result [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms prepared_metadata [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms prepared_rows [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms ordered_receipt [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms ordered_tier_receipt [propext, Classical.choice, Quot.sound]

end Ix.Cert.SourceOwnership
