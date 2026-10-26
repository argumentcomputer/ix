import Ix.Compile.SourceInput.Metadata
import Ix.Cert.SourceInput.Prepared
import IxC.Kernel.Audit.Axioms

namespace Ix.Cert.SourceMetadata
open Ix.Compile.SourceInput Ix.Compile.SourceInput.Metadata

/-- Slot-level specification, independent of the executable list traversal.
This says where a name occurs, not that it resolves or belongs to a family. -/
def Occurs : Ix.ConstantInfo → Ref → Prop
  | .inductInfo d,.inductAll i n => d.all[i]? = some n
  | .inductInfo d,.inductCtor i n => d.ctors[i]? = some n
  | .ctorInfo d,.ctorInduct n => d.induct = n
  | .recInfo d,.recAll i n => d.all[i]? = some n
  | .recInfo d,.ruleCtor i n => (d.rules[i]?).map (·.ctor) = some n
  | _,_ => False

private theorem indexed_mem (tag : Nat → Ix.Name → Ref) (names : Array Ix.Name) (ref : Ref) :
    ref ∈ indexed tag names ↔ ∃ i n, names[i]? = some n ∧ tag i n = ref := by
  simp only [indexed,List.mem_map,Prod.exists,List.mk_mem_zipIdx_iff_getElem?,Array.getElem?_toList]
  constructor
  · rintro ⟨n,i,slot,same⟩; exact ⟨i,n,slot,same⟩
  · rintro ⟨i,n,slot,same⟩; exact ⟨n,i,slot,same⟩

/-- Every occurrence is captured, and every captured row comes from its
specified original field and index. Equal names at distinct slots survive. -/
theorem capture_complete (ci : Ix.ConstantInfo) (ref : Ref) :
    ref ∈ capture ci ↔ Occurs ci ref := by
  cases ci <;> cases ref <;>
    simp [capture,Occurs,indexed_mem,Array.getElem?_map]
  exact eq_comm

private theorem indexed_at (tag : Nat → Ix.Name → Ref) (names : Array Ix.Name) (i : Nat) :
    (indexed tag names)[i]? = (names[i]?).map (tag i) := by
  simp [indexed,List.getElem?_zipIdx,Option.map_map,Function.comp_def]

private theorem indexed_length (tag : Nat → Ix.Name → Ref) (names : Array Ix.Name) :
    (indexed tag names).length = names.size := by simp [indexed]

/-- Exact output positions, including the offset between the two fields.
The stored index remains local to its field; repeated names occupy separate
output positions. Out-of-range lookups return none on both sides. -/
theorem capture_at (ci : Ix.ConstantInfo) (i : Nat) :
    (capture ci)[i]? = match ci with
      | .inductInfo d => if i < d.all.size then (d.all[i]?).map (.inductAll i)
          else (d.ctors[i - d.all.size]?).map (.inductCtor (i - d.all.size))
      | .ctorInfo d => if i = 0 then some (.ctorInduct d.induct) else none
      | .recInfo d => if i < d.all.size then (d.all[i]?).map (.recAll i)
          else (d.rules[i - d.all.size]?).map (fun r => .ruleCtor (i - d.all.size) r.ctor)
      | _ => none := by
  cases ci <;> simp [capture,List.getElem?_append,indexed_length,indexed_at,
    Array.getElem?_map,Option.map_map,Function.comp_def]
  split <;> simp_all

private theorem indexed_names (tag : Nat → Ix.Name → Ref)
    (name : ∀ i n, (tag i n).name = n) (names : Array Ix.Name) :
    (indexed tag names).map Ref.name = names.toList := by
  simp only [indexed,List.map_map,Function.comp_def,name]
  exact List.zipIdx_map_fst _ _

/-- An ordered list equality, not a set equality: all names and repeated
occurrences are retained, in all-before-ctors / all-before-rules field order. -/
theorem capture_names (ci : Ix.ConstantInfo) :
    (capture ci).map Ref.name = match ci with
      | .inductInfo d => d.all.toList ++ d.ctors.toList
      | .ctorInfo d => [d.induct]
      | .recInfo d => d.all.toList ++ d.rules.toList.map (·.ctor)
      | _ => [] := by
  cases ci with
  | inductInfo d =>
    simp only [capture,List.map_append]
    rw [indexed_names .inductAll (fun _ _ => rfl),indexed_names .inductCtor (fun _ _ => rfl)]
  | recInfo d =>
    simp only [capture,List.map_append]
    rw [indexed_names .recAll (fun _ _ => rfl),indexed_names .ruleCtor (fun _ _ => rfl)]
    rw [Array.toList_map]
  | _ => rfl

/-- No field occurrence is removed even when its name duplicates another. -/
theorem capture_length (ci : Ix.ConstantInfo) :
    (capture ci).length = match ci with
      | .inductInfo d => d.all.size + d.ctors.size
      | .ctorInfo _ => 1
      | .recInfo d => d.all.size + d.rules.size
      | _ => 0 := by
  have length := congrArg List.length (capture_names ci)
  cases ci <;> simpa using length

theorem captureAt_of_value {carrier : Carrier} {name : Ix.Name} {form : Form}
    (value : carrier.valueAt name = .ok form) :
    carrier.captureMetadataAt name = .ok (capture form.original) := by
  simp only [Carrier.captureMetadataAt,value,Functor.map,Except.map]

/-- Raw winner provenance uses the existing carrier's exact map lookup.
It does not replace that winner by a pretty name, digest or transformed value. -/
theorem captureAt_origin {carrier : Carrier} {name : Ix.Name} {refs : List Ref}
    (accepted : carrier.captureMetadataAt name = .ok refs) :
    ∃ raw, carrier.byName.get? name = some raw ∧ raw.1 = raw.2.name ∧
      refs = capture (Canon.constS raw.2) := by
  cases read : carrier.valueAt name with
  | error e =>
    simp only [Carrier.captureMetadataAt,read,Functor.map,Except.map] at accepted
    cases accepted
  | ok form =>
    have same : capture form.original = refs := by
      simpa only [Carrier.captureMetadataAt,read,Functor.map,Except.map,Except.ok.injEq] using accepted
    obtain ⟨raw,winner,named,origin⟩ := SourceInput.valueAt_origin read
    exact ⟨raw,winner,named,same.symm.trans (by rw [origin]; rfl)⟩

/-- A successful produced capture refers to the complete original Source
specification, with exact occurrence coverage for that declaration. -/
theorem produced_capture {input : Array Raw} {name : Ix.Name} {refs : List Ref}
    (accepted : (ofPrepass (Ix.Compile.SourceGraph.Prepass.run input)).captureMetadataAt name = .ok refs) :
    ∃ ci, (SourceGraph.full (SourceStream.canonical input)).consts.get? name = some ci ∧
      refs = capture ci ∧ ∀ ref, ref ∈ refs ↔ Occurs ci ref := by
  obtain ⟨raw,winner,_,same⟩ := captureAt_origin accepted
  refine ⟨Canon.constS raw.2,?_,same,?_⟩
  · rw [SourcePrepass.canonical_lookup]
    change (Ix.Compile.SourceGraph.Prepass.run input).leanByIx.get? name = some raw at winner
    rw [winner]
    rfl
  · rw [same]
    exact capture_complete _

/-- Actual prepare success discharges the carrier's header refusal. Every
declared original has its full capture, without another acceptance condition. -/
theorem prepared_capture {input : Ix.Compile.CompileInput} {raw : List Raw}
    (prepared : input.prepare = .ok raw) {name : Ix.Name} {ci : Ix.ConstantInfo}
    (declared : (SourceGraph.full (SourceStream.canonical raw.toArray)).consts.get? name = some ci) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw.toArray)).captureMetadataAt name = .ok (capture ci) :=
  captureAt_of_value (SourceInput.Prepared.prepared_value prepared declared)

theorem preparedConstants_capture {constants raw : List Raw}
    (prepared : Ix.Compile.prepareSourceConstants constants = .ok raw)
    {name : Ix.Name} {ci : Ix.ConstantInfo}
    (declared : (SourceGraph.full (SourceStream.canonical raw.toArray)).consts.get? name = some ci) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw.toArray)).captureMetadataAt name = .ok (capture ci) :=
  captureAt_of_value (SourceInput.Prepared.preparedConstants_value prepared declared)

theorem preparedRegistered_capture {env : Lean.Environment} {constants raw : List Raw}
    (prepared : Ix.Compile.prepareRegisteredConstants env constants = .ok raw)
    {name : Ix.Name} {ci : Ix.ConstantInfo}
    (declared : (SourceGraph.full (SourceStream.canonical raw.toArray)).consts.get? name = some ci) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw.toArray)).captureMetadataAt name = .ok (capture ci) :=
  captureAt_of_value (SourceInput.Prepared.preparedRegistered_value prepared declared)

#guard_kernel_axioms capture_complete [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms capture_at [propext, Quot.sound]
#guard_kernel_axioms capture_names [propext, Quot.sound]
#guard_kernel_axioms capture_length [propext, Quot.sound]
#guard_kernel_axioms captureAt_origin [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms produced_capture [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms prepared_capture [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms preparedConstants_capture [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms preparedRegistered_capture [propext, Classical.choice, Quot.sound]

end Ix.Cert.SourceMetadata
