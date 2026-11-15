import Ix.IxVM.Refinement.Claim
import Ix.Cert.Stream
import IxC.Kernel.Units

/-! # Coherent reader admission

A reader admission witness fixes one coherent store and the concrete outputs of reading
and checking its role closure. The same contract applies to every binding, including the
default. Forgetting the additional guarantees gives `TableAdmitted`; the converse is not
required.
-/

namespace IxVM.Consistency

/-- Every decoded-cache answer is the answer of exact decoding of that entry's bytes. -/
def ReaderCacheCoherent (E : Ixon.Env) : Prop :=
  ∀ a lc, E.consts.get? a = some lc →
    lc.get? = (Ixon.deConstantExact lc.rawBytes).toOption

/-- A concrete accepted reader run and its chosen store. The same store determines the
closure, byte batch, decoded records, blobs, and permitted provenance. -/
structure ReaderAdmissionWitness (V : IxVM.Refinement.View)
    (b : Ix.Kernel.Admission.Binding) where
  table : Ix.Kernel.RoleTable
  env : Ixon.Env
  limits : Ix.Kernel.Admission.Limits
  order : List _root_.Address
  prelude : Ix.Kernel.Reader.Prelude .anon
  state : Ix.Kernel.Reader.State .anon
  fullDecls : Array (Ix.Kernel.Reader.CDecl .anon)
  checkedEnv : Ix.Kernel.Env .anon
  admitted : Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok table
  literalSupport : IxVM.Refinement.LiteralSupportBound table
  draws : IxVM.Refinement.Draws env V.env
  coherent : ReaderCacheCoherent env
  seedsStored : ∀ a, IxVM.Refinement.BindingSeeds table a → env.consts.contains a = true
  closure : Ix.Cert.ClosureOrderAt table env (IxVM.Refinement.BindingSeeds table) order
  preludeRead : Ix.Kernel.Reader.preludeFor table = .ok prelude
  read : Ix.Kernel.Reader.readRecords
    (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash table prelude
      (Ix.Cert.Stream.decodedOf env order) (Ix.Cert.blobsOf env order) (Ix.Cert.hintsOf env))
    prelude.state (Ix.Cert.Stream.decodedOf env order).toArray = .ok (state, fullDecls)
  prepared : Ix.Kernel.Admission.prepareWith _root_.Address.admissionHash b prelude limits
    (Ix.Cert.recordsOf env order) (Ix.Cert.blobsOf env order) (Ix.Cert.hintsOf env) =
    .ok (Ix.Kernel.Reader.evidenceOf
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash table prelude
        (Ix.Cert.Stream.decodedOf env order) (Ix.Cert.blobsOf env order) (Ix.Cert.hintsOf env))
      state table, Ix.Kernel.Frontend.preparePrelude prelude.ix fullDecls)
  accepted : Ix.Kernel.Cached.AcceptsRef .verified
    (Ix.Kernel.Reader.evidenceOf
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash table prelude
        (Ix.Cert.Stream.decodedOf env order) (Ix.Cert.blobsOf env order) (Ix.Cert.hintsOf env))
      state table)
    ((Ix.Kernel.Frontend.preparePrelude prelude.ix fullDecls).toList.map
      IxVM.Refinement.thmToOpaqueDefn) checkedEnv
  theorems : IxVM.Refinement.TheoremsInProp checkedEnv
    (Ix.Kernel.Frontend.preparePrelude prelude.ix fullDecls).toList
  specifications : IxVM.Refinement.BindingSpecs table b checkedEnv
    (Ix.Kernel.Frontend.preparePrelude prelude.ix fullDecls).toList
  userAxioms : IxVM.Refinement.UserAxiomsWithin (fun _ => False)
    (Ix.Kernel.Frontend.preparePrelude prelude.ix fullDecls).toList
  units : Ix.Kernel.checkUnits
    (Ix.Kernel.Frontend.preparePrelude prelude.ix fullDecls) = .ok ()
  noProjRewrites : state.projRewrites = 0
  fallbackRecordsAgree :
    ∀ a ∈ order, ∀ lc, env.consts.get? a = some lc →
      ∀ c, (a, c) ∈ prelude.records ++ prelude.evidence → lc.rawBytes = Ixon.serConstant c
  fallbackRecordBlobsAgree :
    ∀ a bytes, (a, bytes) ∈ Ix.Cert.blobsOf env order →
      ∀ c, (a, c) ∈ prelude.records ++ prelude.evidence → bytes = Ixon.serConstant c
  selectedRecordBlobsAgree :
    ∀ a ∈ order, ∀ lc, env.consts.get? a = some lc →
      ∀ bytes, (a, bytes) ∈ Ix.Cert.blobsOf env order → bytes = lc.rawBytes

/-- Forget coherence and the concrete reader outputs to recover abstract admission. -/
theorem ReaderAdmissionWitness.tableAdmitted
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    (w : ReaderAdmissionWitness V b) : IxVM.Refinement.TableAdmitted V b := by
  refine ⟨w.table, w.admitted, w.literalSupport,
    w.env, w.limits, w.order, w.checkedEnv, w.draws, w.seedsStored,
    w.table, w.prelude, _, _, w.admitted, w.closure, rfl,
    w.preludeRead, w.prepared, ?_, w.theorems, w.userAxioms, w.specifications⟩
  exact Ix.Kernel.Cached.acceptsRefUnder_strict.mpr w.accepted

end IxVM.Consistency
