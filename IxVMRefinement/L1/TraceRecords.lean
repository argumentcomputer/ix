import IxVMRefinement.L1.ScopedRecords

/-! # Raw record queries covered by an actual hashed trace

The claim phase retains every bounded canonical record hashed by the root trace. Query
facts use this actual coverage when an address representation is supplied by the caller;
no address interpretation is postulated for unrelated or ill-typed call arguments.
-/

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core (Ctx ScopedCtx RawRecordFacts)

/-- Every bounded canonical record hashed by this trace has its exact decoded source. -/
def CanonicalHashCoverage (env : Ixon.Env) (calls : List (Call F)) : Prop :=
  ∀ (bytes : ByteArray) (value : Ixon.Constant), Hashed calls bytes →
    bytes.size < 4294967296 → Ixon.deConstantExact bytes = .ok value →
    ∃ source : CanonicalRecordAt env (Address.blake3Pure bytes), source.value = value

/-- The constant loader's actual first verified read, preserving its exact input heap. -/
theorem get_ci_verified_subcall {addr ptr : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (observed : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' calls) :
    ∃ value middle children,
      ObsFn Core.W "Ingress::load_verified_constant" [addr] h value middle children ∧
      ∀ call ∈ children, call ∈ calls := by
  match Obs.«Ingress::get_ci».obs observed with
  | .Defn_n0 (ev14 := loaded) (hc302 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩
  | .Defn_other (ev14 := loaded) (hc423 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩
  | .Axio (ev14 := loaded) (hc515 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩
  | .Quot (ev14 := loaded) (hc606 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩
  | .DPrj (ev14 := loaded) (hc675 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩
  | .IPrj (ev14 := loaded) (hc750 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩
  | .CPrj (ev14 := loaded) (hc851 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩
  | .RPrj (ev14 := loaded) (hc926 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩
  | .Recr (ev14 := loaded) (hc1071 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩

/-- A direct former read begins with its actual verified parent-block read. -/
theorem get_ci_iprj_verified_subcall {bp ptr : SourceValue F} {i : F} {h h' : Heap F}
    {calls : List (Call F)}
    (observed : ObsFn Core.W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' calls) :
    ∃ value middle children,
      ObsFn Core.W "Ingress::load_verified_constant" [bp] h value middle children ∧
      ∀ call ∈ children, call ∈ calls := by
  match Obs.«Ingress::get_ci_iprj».obs observed with
  | .run (ev14 := loaded) (hc283 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩

/-- Actual root hash coverage supplies a canonical source for a represented verified read. -/
theorem canonicalRecordAt_of_verified {env : Ixon.Env} {rootCalls calls : List (Call F)}
    (coverage : CanonicalHashCoverage env rootCalls)
    {address : Bytes.Address} {addr value : SourceValue F} {h h' : Heap F}
    (represented : Bytes.RepAddressRef Core.addrTy h address addr)
    (observed : ObsFn Core.W "Ingress::load_verified_constant" [addr] h value h' calls)
    (subset : ∀ call ∈ calls, call ∈ rootCalls) :
    Nonempty (CanonicalRecordAt env (Core.ixAddr address)) := by
  obtain ⟨_, bytes, decodedValue, size, hashed, hashEq, decoded, _⟩ :=
    load_verified_constant_decode_bounded represented observed
  obtain ⟨source, _⟩ := coverage ⟨bytes.toArray⟩ decodedValue (Core.hashed_mono subset hashed)
    (by simpa only [ByteArray.size, List.size_toArray] using size) decoded
  exact ⟨source.reindex hashEq.symm⟩

/-- The raw query scope is the exact function, arguments and input heap in the root trace. -/
def traceRecordCtx (base : Ctx) (calls : List (Call F)) : ScopedCtx :=
  { toCtx := base, allowed := fun call => call ∈ calls }

instance (base : Ctx) (calls : List (Call F)) : (traceRecordCtx base calls).TableKeyed := ⟨rfl⟩

/-- Any actual subtrace has raw query coverage in its root-call scope. -/
theorem traceRecordCtx_coverage (base : Ctx) {rootCalls calls : List (Call F)}
    (subset : ∀ call ∈ calls, call ∈ rootCalls) :
    Core.RawRecordCoverage (traceRecordCtx base rootCalls) calls :=
  fun _ _ member => subset _ member

/-- Build raw query facts directly from the successful root observation and its concrete
canonical hash coverage. Alternative readings at an allowed top call are checked against the
same canonical source and parent; no installed semantic constant is required. -/
theorem rawRecordFacts_of_hashed_trace {base : Ctx} {name : String}
    {args : List (SourceValue F)} {before after : Heap F} {result : SourceValue F}
    {calls : List (Call F)}
    (observedRoot : ObsFn Core.W name args before result after calls)
    (goodRoot : Core.Good base calls)
    (coverage : CanonicalHashCoverage base.E calls) :
    RawRecordFacts (traceRecordCtx base calls) where
  inductiveRead := by
    intro addr ptr h h' children address nl ty np ni nc u blk idx observed allowed good addressRep payload
    obtain ⟨originalValue, originalAfter, originalCalls, original, originalSubset⟩ :=
      observedRoot.call_observed allowed
    obtain ⟨_, _, _, verified, verifiedSubset⟩ := get_ci_verified_subcall original
    obtain ⟨source⟩ := canonicalRecordAt_of_verified coverage addressRep verified
      (fun call member => originalSubset call (verifiedSubset call member))
    have parents : ∀ projection, source.value.info = .iPrj projection →
        Nonempty (CanonicalRecordAt base.E projection.block) := by
      intro projection shape
      obtain ⟨parent, blockArg, middle, inner, parentEq, _, parentRep, loaded, innerSubset, _⟩ :=
        get_ci_iPrj_subcall (base := base) source shape addressRep (goodRoot.sub originalSubset) original
      obtain ⟨_, _, _, parentRead, parentSubset⟩ := get_ci_iprj_verified_subcall loaded
      obtain ⟨parentSource⟩ := canonicalRecordAt_of_verified coverage parentRep parentRead
        (fun call member => originalSubset call (innerSubset call (parentSubset call member)))
      exact ⟨parentSource.reindex parentEq.symm⟩
    let query : RawRecordQuery base.E :=
      { addr := addr, result := originalValue, before := h, after := originalAfter
        calls := originalCalls, address := address, observed := original
        addressRep := addressRep, source := source, parents := parents }
    exact query.inductiveRead (base := base) observed good payload

end IxVM.Refinement.L1
