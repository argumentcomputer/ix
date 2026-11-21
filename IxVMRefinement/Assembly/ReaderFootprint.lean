import IxVMRefinement.Assembly.ReaderAdmission
import Ix.IxVM.Consistency.ReaderFootprint
import Ix.Cert.FallbackStore

/-! # Reader footprint provenance and compatibility

Selected admission records are held by the view. Projection images are derived from exact
raw decoding, including the committed fallback. Rebasing preserves the old admission data
and the view's trees, but does not claim equivalence at the original fixed view.
-/

namespace IxVM.Refinement.Assembly.ReaderFootprint

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Refinement (View Draws)
open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)

universe u

abbrev HeldReaderAdmissionWitness := ReaderAdmissionWitness

def rebaseView {V : View} {b : Admission.Binding} (w : ReaderAdmissionData V b) : View :=
  { V with env := w.env }

/-- A coherent accepted run can be made explicit in its reader view. No record-byte
agreement with the original view is inferred by this construction. -/
def rebase {V : View} {b : Admission.Binding} (w : ReaderAdmissionData V b) :
    ReaderAdmissionWitness (rebaseView w) b where
  toReaderAdmissionData := { w with
    draws := ⟨fun _ lc hget => .inl ⟨lc, hget, rfl⟩, fun _ _ hget => hget⟩ }
  selectedRecordsInView := fun _ _ lc hget => ⟨lc, hget, rfl⟩

@[simp] theorem rebaseView_trees {V : View} {b : Admission.Binding}
    (w : ReaderAdmissionData V b) : (rebaseView w).trees = V.trees := rfl

theorem rebaseView_claimSeeds {V : View} {b : Admission.Binding}
    (w : ReaderAdmissionData V b) (claim : Ix.Claim) (seeds : List _root_.Address) :
    ClaimSeeds claim (rebaseView w) seeds ↔ ClaimSeeds claim V seeds := by
  cases claim <;> rfl

/-- The admission-data contract before selected-record provenance is required. -/
def DataReaderTable (claim : Ix.Claim) (V : View) (b : Admission.Binding) : Prop :=
  (∃ ctx, claim.context? = some ctx ∧ b.address = ctx.binding) ∧
    Nonempty (ReaderAdmissionData V b)

theorem dataReaderTable_of {claim : Ix.Claim} {V : View} {b : Admission.Binding}
    (h : ReaderTable claim V b) : DataReaderTable claim V b :=
  ⟨h.1, h.2.elim fun w => ⟨w.toReaderAdmissionData⟩⟩

theorem readerTable_rebase {claim : Ix.Claim} {V : View} {b : Admission.Binding}
    (h : DataReaderTable claim V b) :
    ∃ V' : View, V'.trees = V.trees ∧ ReaderTable claim V' b ∧
      ∀ seeds, ClaimSeeds claim V' seeds ↔ ClaimSeeds claim V seeds := by
  obtain ⟨w⟩ := h.2
  exact ⟨rebaseView w, rfl, ⟨h.1, ⟨rebase w⟩⟩, rebaseView_claimSeeds w claim⟩

theorem memberProjection_mem {owner : _root_.Address} {constant : Ixon.Constant}
    {members : Array Ixon.MutConst} (hinfo : constant.info = .muts members)
    {i : Nat} {member : Ixon.MutConst} (hmember : members[i]? = some member) :
    Ixon.serConstant (memberProjection owner i member) ∈ recordProjectionImages owner constant := by
  simp only [recordProjectionImages, hinfo]
  apply List.mem_flatMap.mpr
  exact ⟨(member, i), List.mem_zipIdx_iff_getElem?.mpr (by simpa using hmember), List.mem_cons_self⟩

theorem constructorProjection_mem {owner : _root_.Address} {constant : Ixon.Constant}
    {members : Array Ixon.MutConst} (hinfo : constant.info = .muts members)
    {i j : Nat} {ind : Ixon.Inductive} (hmember : members[i]? = some (.indc ind))
    (hj : j < ind.ctors.size) :
    Ixon.serConstant (constructorProjection owner i j) ∈ recordProjectionImages owner constant := by
  simp only [recordProjectionImages, hinfo]
  apply List.mem_flatMap.mpr
  refine ⟨(.indc ind, i), List.mem_zipIdx_iff_getElem?.mpr (by simpa using hmember), ?_⟩
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)


def memberLayout : Ixon.MutConst → Egress.ProjectionLayout
  | .defn _ => .definition
  | .indc _ => .inductive
  | .recr _ => .recursor

theorem writeProjection_member_exact {owner : _root_.Address} {i : Nat}
    (member : Ixon.MutConst) {projection : Ixon.Constant}
    (h : Egress.writeProjection (memberLayout member) (.member owner i) = .ok projection) :
    projection = memberProjection owner i member := by
  have hread := Egress.writeProjection_reading h
  cases member <;> cases hread <;> simp [memberProjection]

theorem writeProjection_constructor_exact {owner : _root_.Address} {i j : Nat}
    {projection : Ixon.Constant}
    (h : Egress.writeProjection .constructor (.ctor owner i j) = .ok projection) :
    projection = constructorProjection owner i j := by
  have hread := Egress.writeProjection_reading h
  cases hread
  simp [constructorProjection]

theorem written_member_covered {owner : _root_.Address} {constant : Ixon.Constant}
    {members : Array Ixon.MutConst} (hinfo : constant.info = .muts members)
    {i : Nat} {member : Ixon.MutConst} (hmember : members[i]? = some member)
    {projection : Ixon.Constant}
    (hwrite : Egress.writeProjection (memberLayout member) (.member owner i) = .ok projection) :
    Ixon.serConstant projection ∈ recordProjectionImages owner constant := by
  rw [writeProjection_member_exact member hwrite]
  exact memberProjection_mem hinfo hmember

theorem written_constructor_covered {owner : _root_.Address} {constant : Ixon.Constant}
    {members : Array Ixon.MutConst} (hinfo : constant.info = .muts members)
    {i j : Nat} {ind : Ixon.Inductive} (hmember : members[i]? = some (.indc ind))
    (hj : j < ind.ctors.size) {projection : Ixon.Constant}
    (hwrite : Egress.writeProjection .constructor (.ctor owner i j) = .ok projection) :
    Ixon.serConstant projection ∈ recordProjectionImages owner constant := by
  rw [writeProjection_constructor_exact hwrite]
  exact constructorProjection_mem hinfo hmember hj

theorem derivedProjImages_mem {V : View} {owner : _root_.Address} {lc : Ixon.LazyConstant}
    (hget : V.env.consts.get? owner = some lc) {constant : Ixon.Constant}
    (hdecode : Ixon.deConstantExact lc.rawBytes = .ok constant) {bytes : ByteArray}
    (hbytes : bytes ∈ recordProjectionImages owner constant) : bytes ∈ derivedProjImages V := by
  apply List.mem_flatMap.mpr
  refine ⟨(owner, lc), ?_, ?_⟩
  · exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hget
  · simpa only [rawProjectionImages, hdecode] using hbytes

theorem coherent_recordAt_exact {E : Ixon.Env} (hcoherent : ReaderCacheCoherent E)
    {owner : _root_.Address} {constant : Ixon.Constant}
    (hrecord : Ix.Cert.recordAt E owner = some constant) :
    ∃ lc, E.consts.get? owner = some lc ∧ Ixon.deConstantExact lc.rawBytes = .ok constant := by
  unfold Ix.Cert.recordAt at hrecord
  change (E.consts.get? owner).bind (fun lc => lc.get?) = some constant at hrecord
  cases hget : E.consts.get? owner with
  | none => rw [hget] at hrecord; cases hrecord
  | some lc =>
    simp only [hget, Option.bind_some] at hrecord
    have hcache := hcoherent owner lc hget
    rw [hrecord] at hcache
    cases hdecode : Ixon.deConstantExact lc.rawBytes with
    | error reason => rw [hdecode] at hcache; cases hcache
    | ok decoded =>
      simp only [hdecode, Except.toOption, Option.some.injEq] at hcache
      cases hcache
      exact ⟨lc, rfl, hdecode⟩

theorem selected_projection_covered {V : View} {b : Admission.Binding}
    (w : HeldReaderAdmissionWitness V b) {owner : _root_.Address} (howner : owner ∈ w.order)
    {constant : Ixon.Constant} (hrecord : Ix.Cert.recordAt w.env owner = some constant)
    {bytes : ByteArray} (hbytes : bytes ∈ recordProjectionImages owner constant) :
    bytes ∈ derivedProjImages V := by
  obtain ⟨lc, hget, hdecode⟩ := coherent_recordAt_exact w.coherent hrecord
  obtain ⟨lcV, hview, hraw⟩ := w.selectedRecordsInView owner howner lc hget
  exact derivedProjImages_mem hview (by rw [hraw]; exact hdecode) hbytes

theorem committed_projection_covered {table : RoleTable} {pre : Prelude .anon}
    (hpre : preludeFor table = .ok pre) {owner : _root_.Address} {constant : Ixon.Constant}
    (hrecord : (owner, constant) ∈ pre.records ++ pre.evidence)
    {bytes : ByteArray} (hbytes : bytes ∈ recordProjectionImages owner constant) :
    bytes ∈ committedProjImages := by
  obtain ⟨hrecords, hevidence⟩ := Ix.Cert.ReaderFallback.preludeFor_records hpre
  have source : ∃ row ∈ (RoleData.prelude ++ RoleData.evidence).toList,
      addressOfHex row.1 = some owner ∧ ∃ raw, bytesOfHex row.2 = some raw ∧
        Ixon.deConstantExact raw = .ok constant := by
    rcases Array.mem_append.mp hrecord with hrecord | hrecord
    · obtain ⟨row, hrow, haddress, raw, hraw, hdecode⟩ :=
        Ix.Cert.FallbackStore.decoded_rows "prelude" RoleData.prelude hrecords
          (owner, constant) (Array.mem_toList_iff.mpr hrecord)
      obtain ⟨_, hwire, hencoded⟩ := Ixon.Verify.Canonical.deConstant_spec _ _ _ _ hdecode
      exact ⟨row, by simp [Array.toList_append, hrow], haddress, raw, hraw,
        by rw [← hencoded]; exact Ixon.Verify.deConstantExact_serConstant constant hwire⟩
    · obtain ⟨row, hrow, haddress, raw, hraw, hdecode⟩ :=
        Ix.Cert.FallbackStore.decoded_rows "evidence" RoleData.evidence hevidence
          (owner, constant) (Array.mem_toList_iff.mpr hrecord)
      obtain ⟨_, hwire, hencoded⟩ := Ixon.Verify.Canonical.deConstant_spec _ _ _ _ hdecode
      exact ⟨row, by simp [Array.toList_append, hrow], haddress, raw, hraw,
        by rw [← hencoded]; exact Ixon.Verify.deConstantExact_serConstant constant hwire⟩
  obtain ⟨row, hrow, haddress, raw, hraw, hdecode⟩ := source
  apply List.mem_flatMap.mpr
  exact ⟨row, hrow, by simpa only [haddress, hraw, rawProjectionImages, hdecode] using hbytes⟩

theorem selected_record_agrees {V : View} {b : Admission.Binding}
    (w : HeldReaderAdmissionWitness V b) {extra : List ByteArray} {calls : List (Call IxVM.F)}
    (hno : ¬ V.HashedCollision extra calls) {owner : _root_.Address} (howner : owner ∈ w.order)
    {lc : Ixon.LazyConstant} (hget : w.env.consts.get? owner = some lc)
    {bytes : ByteArray} (hbytes : IxVM.Refinement.Hashed calls bytes)
    (hhash : _root_.Address.blake3Pure bytes = owner) : bytes = lc.rawBytes := by
  obtain ⟨lcV, hview, hraw⟩ := w.selectedRecordsInView owner howner lc hget
  by_contra hne
  exact hno (.inl ⟨owner, lc.rawBytes, bytes, .inl (.inl ⟨lcV, hview, hraw⟩), hbytes, hne, hhash⟩)

theorem held_image_agrees {V : View} {extra : List ByteArray} {calls : List (Call IxVM.F)}
    (hno : ¬ V.HashedCollision extra calls) {held bytes : ByteArray}
    (hheld : held ∈ extra) (hbytes : IxVM.Refinement.Hashed calls bytes)
    (hhash : _root_.Address.blake3Pure bytes = _root_.Address.blake3Pure held) : bytes = held := by
  by_contra hne
  exact hno (.inl ⟨_, held, bytes, .inr (.inl ⟨hheld, rfl⟩), hbytes, hne, hhash⟩)

theorem collision_extra_mono {V : View} {small large : List ByteArray} {calls : List (Call IxVM.F)}
    (hsub : ∀ bytes ∈ small, bytes ∈ large) (h : V.HashedCollision small calls) :
    V.HashedCollision large calls := by
  rcases h with ⟨address, held, bytes, hheld, hashed, different, same⟩ |
    ⟨address, held, image, blk, cb, ms, hheld, hashed, decoded, block, isImage, different,
      same⟩ | padding
  · refine .inl ⟨address, held, bytes, ?_, hashed, different, same⟩
    rcases hheld with view | ⟨member, hash⟩ | traced
    · exact .inl view
    · exact .inr (.inl ⟨hsub held member, hash⟩)
    · exact .inr (.inr traced)
  · refine .inr (.inl ⟨address, held, image, blk, cb, ms, ?_, hashed, decoded, block, isImage,
      different, same⟩)
    rcases hheld with view | ⟨member, hash⟩ | traced
    · exact .inl view
    · exact .inr (.inl ⟨hsub held member, hash⟩)
    · exact .inr (.inr traced)
  · exact .inr (.inr padding)

theorem collision_into_readerImages {V : View} {claimBytes bindingBytes : ByteArray}
    {calls : List (Call IxVM.F)}
    (h : V.HashedCollision (claimBytes :: bindingBytes :: committedImages) calls) :
    V.HashedCollision (claimBytes :: bindingBytes :: readerImages V) calls := by
  apply collision_extra_mono _ h
  intro image himage
  simp only [List.mem_cons] at himage ⊢
  rcases himage with rfl | rfl | member
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr (by simp [readerImages, member]))

def DataConsistencySpec (calls : List (Call IxVM.F)) (digest : IxVM.Refinement.Digest) : Prop :=
  ∀ (bytes : ByteArray) (claim : Ix.Claim), Ix.Claim.de bytes = .ok claim →
    IxVM.Refinement.packDigest (_root_.Address.blake3Pure bytes) = digest → InScope claim →
      ∀ (V : View) (seeds : List _root_.Address) (b : Admission.Binding),
        ClaimSeeds claim V seeds → DataReaderTable claim V b →
        V.HashedCollision (bytes :: b.bytes :: committedImages) calls ∨
          ConsistentRead.{u} V calls b seeds

/-- The previous data-based statement implies the statement with selected-record provenance
and the fixed projection footprint. The converse at a fixed view is not claimed. -/
theorem consistencySpec_of_data {calls : List (Call IxVM.F)} {digest : IxVM.Refinement.Digest}
    (h : DataConsistencySpec.{u} calls digest) : ConsistencySpec.{u} calls digest := by
  intro bytes claim decoded packed scope V seeds b hseeds hreader
  rcases h bytes claim decoded packed scope V seeds b hseeds (dataReaderTable_of hreader) with
    collision | consistent
  · exact .inl (collision_into_readerImages collision)
  · exact .inr consistent

/-- The stronger constructor uses the existing executable verdict, with no added runtime gate. -/
abbrev check := IxVM.Refinement.Assembly.ReaderAdmission.check

theorem check_eq (binding : Admission.Binding) (env : Ixon.Env) :
    check binding env = IxVM.Refinement.Assembly.ReaderAdmission.check binding env := rfl

theorem check_sound (W : Type u) [SetTheory W] {V : View} {b : Admission.Binding}
    (h : check b V.env = true) : Nonempty (ReaderAdmissionWitness V b) :=
  IxVM.Refinement.Assembly.ReaderAdmission.check_sound W h

end IxVM.Refinement.Assembly.ReaderFootprint
