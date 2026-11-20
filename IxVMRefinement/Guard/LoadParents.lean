import IxVMRefinement.Guard.RunStoreReading

/-! # The run's store holds the block of every projection record the run loads

`Ingress::get_ci` at a projection record (`dPrj`, `iPrj`, `cPrj`, `rPrj`) reads the record,
then reads the block it names through the same verified loader
(`Ingress::load_verified_constant`), inside `get_ci_dprj`, `get_ci_iprj`, `get_ci_cprj` or
`get_ci_rprj`. The loader bounds the bytes it hashes below `2^32`, so the run's store, which
holds every record below that size the run hashed, holds the block.

* `get_ci_parent_load`: the load's own verified read, and at a projection payload the verified
  read of the block, with its argument the payload's block pointer.
* `loadParentsHeld_of_runStore`: `Guard.LoadParentsHeld` for a run store that holds the run's
  hashed records.
-/

namespace IxVM.Refinement.Guard

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open IxVM.Refinement.Core

set_option maxHeartbeats 1600000

/-- A verified read of the block `blockArg` points to, in the run, from a heap that extends
`middle`. -/
def ParentLoad (calls : List (Call F)) (middle : Heap F) (blockArg : SourceValue F) : Prop :=
  ∃ (value : SourceValue F) (mid after : Heap F) (children : List (Call F)),
    Heap.Extends middle mid ∧
    ObsFn W "Ingress::load_verified_constant" [blockArg] mid value after children ∧
    ∀ call ∈ children, call ∈ calls

/-- **The verified reads of a constant load**: the record's, and at a projection payload the
block's, at the payload's last field. -/
theorem get_ci_parent_load {addr ptr : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (loaded : ObsFn W "Ingress::get_ci" [addr] h ptr h' calls) :
    ∃ (info sharing refs univs binders : SourceValue F) (middle : Heap F) (cs : List (Call F)),
      ObsFn W "Ingress::load_verified_constant" [addr] h
        (.construct "Ixon::Constant" "Mk" [info, sharing, refs, univs, binders]) middle cs ∧
      (∀ call ∈ cs, call ∈ calls) ∧
      ∀ (tag projTy : String) (args : List (SourceValue F)) (blockArg : SourceValue F),
        info = .construct "Ixon::ConstantInfo" tag [.construct projTy "Mk" args] →
        (tag = "DPrj" ∨ tag = "IPrj" ∨ tag = "CPrj" ∨ tag = "RPrj") →
        args.getLast? = some blockArg → ParentLoad calls middle blockArg := by
  match Obs.«Ingress::get_ci».obs loaded with
  | .Defn_n0 (ev14 := observed) (hc302 := allCalls) .. =>
    refine ⟨_, _, _, _, _, _, _, observed, by rw [allCalls]; intro call member; simp [member], ?_⟩
    intro tag projTy args blockArg shape kind _
    injection shape with _ tagEq _
    subst tagEq
    simp at kind
  | .Defn_other (ev14 := observed) (hc423 := allCalls) .. =>
    refine ⟨_, _, _, _, _, _, _, observed, by rw [allCalls]; intro call member; simp [member], ?_⟩
    intro tag projTy args blockArg shape kind _
    injection shape with _ tagEq _
    subst tagEq
    simp at kind
  | .Axio (ev14 := observed) (hc515 := allCalls) .. =>
    refine ⟨_, _, _, _, _, _, _, observed, by rw [allCalls]; intro call member; simp [member], ?_⟩
    intro tag projTy args blockArg shape kind _
    injection shape with _ tagEq _
    subst tagEq
    simp at kind
  | .Quot (ev14 := observed) (hc606 := allCalls) .. =>
    refine ⟨_, _, _, _, _, _, _, observed, by rw [allCalls]; intro call member; simp [member], ?_⟩
    intro tag projTy args blockArg shape kind _
    injection shape with _ tagEq _
    subst tagEq
    simp at kind
  | .Recr (ev14 := observed) (hc1071 := allCalls) .. =>
    refine ⟨_, _, _, _, _, _, _, observed, by rw [allCalls]; intro call member; simp [member], ?_⟩
    intro tag projTy args blockArg shape kind _
    injection shape with _ tagEq _
    subst tagEq
    simp at kind
  | .DPrj (cs648 := inner) (ev14 := observed) (ev650 := memberRun) (hc675 := allCalls) .. =>
    have innerSub : ∀ call ∈ inner, call ∈ calls := by
      rw [allCalls]; intro call member; simp [member]
    refine ⟨_, _, _, _, _, _, _, observed, by rw [allCalls]; intro call member; simp [member], ?_⟩
    intro tag projTy args blockArg shape _ last
    injection shape with _ _ fieldsEq
    injection fieldsEq with projEq _
    injection projEq with _ _ argsEq
    subst argsEq
    simp at last
    subst last
    match Obs.«Ingress::get_ci_dprj».obs memberRun with
    | .run (ev14 := kinds) (ev36 := verified) (hc348 := subCalls) .. =>
      exact ⟨_, _, _, _, kinds.heap_extends, verified,
        fun call member => innerSub call (by rw [subCalls]; simp [member])⟩
  | .IPrj (cs718 := inner) (ev14 := observed) (ev741 := indexRun) (ev720 := formerRun)
      (hc750 := allCalls) .. =>
    have innerSub : ∀ call ∈ inner, call ∈ calls := by
      rw [allCalls]; intro call member; simp [member]
    refine ⟨_, _, _, _, _, _, _, observed, by rw [allCalls]; intro call member; simp [member], ?_⟩
    intro tag projTy args blockArg shape _ last
    injection shape with _ _ fieldsEq
    injection fieldsEq with projEq _
    injection projEq with _ _ argsEq
    subst argsEq
    simp at last
    subst last
    match Obs.«Ingress::get_ci_iprj».obs formerRun with
    | .run (ev14 := verified) (hc283 := subCalls) .. =>
      exact ⟨_, _, _, _, indexRun.heap_extends, verified,
        fun call member => innerSub call (by rw [subCalls]; simp [member])⟩
  | .CPrj (cs798 := inner) (ev14 := observed) (ev822 := indexRun) (ev842 := ctorIndexRun)
      (ev800 := ctorRun) (hc851 := allCalls) .. =>
    have innerSub : ∀ call ∈ inner, call ∈ calls := by
      rw [allCalls]; intro call member; simp [member]
    refine ⟨_, _, _, _, _, _, _, observed, by rw [allCalls]; intro call member; simp [member], ?_⟩
    intro tag projTy args blockArg shape _ last
    injection shape with _ _ fieldsEq
    injection fieldsEq with projEq _
    injection projEq with _ _ argsEq
    subst argsEq
    simp at last
    subst last
    match Obs.«Ingress::get_ci_cprj».obs ctorRun with
    | .run (ev14 := verified) (hc381 := subCalls) .. =>
      exact ⟨_, _, _, _, indexRun.heap_extends.trans ctorIndexRun.heap_extends, verified,
        fun call member => innerSub call (by rw [subCalls]; simp [member])⟩
  | .RPrj (cs894 := inner) (ev14 := observed) (ev917 := indexRun) (ev896 := recursorRun)
      (hc926 := allCalls) .. =>
    have innerSub : ∀ call ∈ inner, call ∈ calls := by
      rw [allCalls]; intro call member; simp [member]
    refine ⟨_, _, _, _, _, _, _, observed, by rw [allCalls]; intro call member; simp [member], ?_⟩
    intro tag projTy args blockArg shape _ last
    injection shape with _ _ fieldsEq
    injection fieldsEq with projEq _
    injection projEq with _ _ argsEq
    subst argsEq
    simp at last
    subst last
    match Obs.«Ingress::get_ci_rprj».obs recursorRun with
    | .run (ev14 := verified) (hc283 := subCalls) .. =>
      exact ⟨_, _, _, _, indexRun.heap_extends, verified,
        fun call member => innerSub call (by rw [subCalls]; simp [member])⟩

/-- **A run store that holds the run's hashed records holds the block of every projection
record the run loads.** -/
theorem loadParentsHeld_of_runStore {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hcov : LoadedReads.HashedRecordsStored calls E₀) :
    LoadParentsHeld calls E₀ := by
  intro a ap ptr h h' cs c B hsub addressRep load stored block
  obtain ⟨info, sharing, refs, univs, binders, middle, cs', observed, subset, parents⟩ :=
    get_ci_parent_load load
  obtain ⟨-, bytes, c', -, hashed, address, exact, -, -, -, -, -, -, rep⟩ :=
    Ingress.load_verified_constant_decode_bounded addressRep observed
  have same : c = c' := (hS.record_eq stored
    (Core.hashed_mono (fun cl member => hsub cl (subset cl member)) hashed) address exact).symm
  subst same
  obtain ⟨infoVal, sh, rf, un, bd, fields, infoRep, -, -, -, -⟩ := rep
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at fields
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩ := fields
  have finish : ∀ blockArg, Ingress.RepIxonAddressRef middle B blockArg →
      ParentLoad cs middle blockArg → (E₀.consts.get? B).isSome := by
    intro blockArg ⟨parent, parentAddress, represented⟩
      ⟨value, mid, after, children, ext, verified, childSub⟩
    obtain ⟨-, bytes', cb, size, hashed', address', exact', decoded', -⟩ :=
      Ingress.load_verified_constant_decode_bounded
        (Bytes.repAddressRef_heapMono₂ _ ext represented) verified
    obtain ⟨lc, storedBlock, -, -⟩ := hcov ⟨bytes'.toArray⟩ cb
      (Core.hashed_mono (fun cl member => hsub cl (childSub cl member)) hashed')
      (by simpa only [ByteArray.size, List.size_toArray] using size) decoded' exact'
    have sameAddress : Address.blake3Pure ⟨bytes'.toArray⟩ = B := by
      rw [parentAddress]; exact address'
    rw [← sameAddress, storedBlock]
    rfl
  cases hinfo : c.info with
  | dPrj p =>
    rw [hinfo] at infoRep block
    obtain ⟨pv, rfl, blkPtr, rfl, parentRep⟩ := infoRep
    have blockEq : p.block = B := by simpa [projBlock] using block
    subst blockEq
    exact finish blkPtr parentRep
      (parents "DPrj" "Ixon::DefinitionProj" _ blkPtr rfl (Or.inl rfl) (by simp))
  | iPrj p =>
    rw [hinfo] at infoRep block
    obtain ⟨pv, rfl, blkPtr, rfl, parentRep⟩ := infoRep
    have blockEq : p.block = B := by simpa [projBlock] using block
    subst blockEq
    exact finish blkPtr parentRep
      (parents "IPrj" "Ixon::InductiveProj" _ blkPtr rfl (Or.inr (Or.inl rfl)) (by simp))
  | cPrj p =>
    rw [hinfo] at infoRep block
    obtain ⟨pv, rfl, blkPtr, rfl, parentRep⟩ := infoRep
    have blockEq : p.block = B := by simpa [projBlock] using block
    subst blockEq
    exact finish blkPtr parentRep
      (parents "CPrj" "Ixon::ConstructorProj" _ blkPtr rfl (Or.inr (Or.inr (Or.inl rfl)))
        (by simp))
  | rPrj p =>
    rw [hinfo] at infoRep block
    obtain ⟨pv, rfl, blkPtr, rfl, parentRep⟩ := infoRep
    have blockEq : p.block = B := by simpa [projBlock] using block
    subst blockEq
    exact finish blkPtr parentRep
      (parents "RPrj" "Ixon::RecursorProj" _ blkPtr rfl (Or.inr (Or.inr (Or.inr rfl)))
        (by simp))
  | defn d => rw [hinfo] at block; simp [projBlock] at block
  | recr r => rw [hinfo] at block; simp [projBlock] at block
  | axio x => rw [hinfo] at block; simp [projBlock] at block
  | quot q => rw [hinfo] at block; simp [projBlock] at block
  | muts ms => rw [hinfo] at block; simp [projBlock] at block

/-- **The reading of the checked field loop over the run's store**, from the two facts every
step has of that store. -/
theorem checkedSortsReadingAt_of_runStore {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hcov : LoadedReads.HashedRecordsStored calls E₀) :
    CheckedSortsReadingAt calls E₀ :=
  checkedSortsReadingAt_runStore hS hcov (loadParentsHeld_of_runStore hS hcov)

/-- **The reading over a step's store**: the store holds the run store's records and blobs. -/
theorem checkedSortsReadingAt_of_stepStore {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : Typing.StepStore calls t E₀ E) :
    CheckedSortsReadingAt calls E :=
  (checkedSortsReadingAt_of_runStore hS hcov).stepStore hst

end IxVM.Refinement.Guard
