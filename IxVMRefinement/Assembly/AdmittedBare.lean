import IxVMRefinement.Assembly.StreamState
import IxVMRefinement.Assembly.ReaderDecode
import IxVMRefinement.Assembly.RecordReadBare

/-! # Concrete bare role reading from coherent admission

The admitted full reader's prelude check is recovered from its actual byte preparation.
Removing generated declarations preserves that check and produces the separate bare role array.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)

theorem admitted_keepsPrelude {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b) :
    State.keepsPrelude w.prelude.state w.state = true := by
  have h := w.prepared
  unfold Admission.prepareWith at h
  obtain ⟨_, _, h⟩ := except_bind_ok.mp h
  obtain ⟨_, _, h⟩ := except_bind_ok.mp h
  obtain ⟨_, _, h⟩ := except_bind_ok.mp h
  obtain ⟨table, htable, h⟩ := except_bind_ok.mp h
  simp only [w.admitted, Except.mapError, Except.ok.injEq] at htable
  subst table
  obtain ⟨constants, hdecode, h⟩ := except_bind_ok.mp h
  have hdecode' : Admission.decodeRecords w.limits (Ix.Cert.recordsOf w.env w.order) = .ok constants := by
    cases hd : Admission.decodeRecords w.limits (Ix.Cert.recordsOf w.env w.order) with
    | error e => simp [hd, Except.mapError] at hdecode
    | ok values =>
      simp only [hd, Except.mapError, Except.ok.injEq] at hdecode
      cases hdecode
      rfl
  have hconstants := recordsRead_decodedOf_coherent w.env w.order
    (fun a _ lc hget c hdec => by
      rw [w.coherent a lc hget, hdec]
      rfl)
    ((Admission.decodeRecords_ok_iff _ _ _).mp hdecode')
  subst constants
  obtain ⟨⟨ev, decls⟩, hstream, _⟩ := except_bind_ok.mp h
  unfold Admission.readStream at hstream
  dsimp only at hstream
  rw [w.read] at hstream
  split at hstream
  · rename_i hkeeps
    exact hkeeps
  · cases hstream

/-- Coherent admission constructs a bare role stream that actually keeps the prelude,
with its own final state and its own declaration array. -/
theorem admitted_streamReadBare_keepsPrelude
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b) :
    let cx := Admission.streamContext _root_.Address.admissionHash w.table w.prelude
      (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order) (Ix.Cert.hintsOf w.env)
    ∃ final decls, StreamReadBare cx w.prelude.state (Ix.Cert.Stream.decodedOf w.env w.order)
      final decls ∧ w.fullDecls.toList.filter (fun d => !d.isGenerated) = decls.toList ∧
      State.keepsPrelude w.prelude.state final = true := by
  dsimp only
  have hrk := streamContext_rolesKeyed _root_.Address.admissionHash w.table w.prelude
    (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order) (Ix.Cert.hintsOf w.env)
  have hstream := readRecords_spec w.read
  have hstate : ∀ k : CName .anon, NonAuxKey k → w.prelude.state.SameAt w.prelude.state k :=
    fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hlevels := preludeFor_projLevels_empty w.preludeRead
  obtain ⟨final, decls, hbare, hsame, hfilter⟩ :=
    streamRead_full_bare_sameAt hrk hstream w.noProjRewrites hstate hlevels
  refine ⟨final, decls, hbare, hfilter, State.keepsPrelude_iff.mpr ?_⟩
  intro k hk
  obtain ⟨role, _, hrole⟩ := prelude_state_keys_roles w.preludeRead k hk
  have hnonaux : NonAuxKey k := by
    rw [hrole]
    intro _ _ heq
    cases heq
  have hb := hsame k hnonaux
  have hf := State.keepsPrelude_iff.mp (admitted_keepsPrelude w) k hk
  exact ⟨hb.1.trans hf.1, hb.2.1.trans hf.2.1, hb.2.2.1.trans hf.2.2.1,
    hb.2.2.2.1.trans hf.2.2.2.1, hb.2.2.2.2.trans hf.2.2.2.2⟩

private theorem mapError_ok {ε δ α : Type} {f : ε → δ} {result : Except ε α} {a : α}
    (h : result.mapError f = .ok a) : result = .ok a := by
  cases result with
  | error e => cases h
  | ok value => cases h; rfl

theorem recordsReadBare_of_recordsRead {limits : Admission.Limits}
    {records : Admission.Records} {constants : Ingress.Constants}
    (h : Admission.RecordsRead limits records constants) : RecordsReadBare limits records constants := by
  induction h with
  | nil => exact .nil
  | cons reads _ ih =>
    refine .cons ⟨rfl, reads.bytesFit, reads.nodesFit, ?_⟩ ih
    rw [← reads.encoded]
    exact Ixon.Verify.deConstantExact_serConstant _ reads.wire

theorem admitted_bare_byteFacts {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b) :
    Admission.WithinBatch w.limits (Ix.Cert.recordsOf w.env w.order) (Ix.Cert.blobsOf w.env w.order) ∧
      Admission.UniqueKeys (Ix.Cert.recordsOf w.env w.order) (Ix.Cert.blobsOf w.env w.order) ∧
      Admission.Authentic _root_.Address.admissionHash
        (Ix.Cert.recordsOf w.env w.order) (Ix.Cert.blobsOf w.env w.order) ∧
      RecordsReadBare w.limits (Ix.Cert.recordsOf w.env w.order) (Ix.Cert.Stream.decodedOf w.env w.order) := by
  have h := w.prepared
  unfold Admission.prepareWith at h
  obtain ⟨batchResult, hbatch, h⟩ := except_bind_ok.mp h
  cases batchResult
  obtain ⟨uniqueResult, hunique, h⟩ := except_bind_ok.mp h
  cases uniqueResult
  obtain ⟨authResult, hauth, h⟩ := except_bind_ok.mp h
  cases authResult
  obtain ⟨_, _, h⟩ := except_bind_ok.mp h
  obtain ⟨constants, hdecode, _⟩ := except_bind_ok.mp h
  have hreading := (Admission.decodeRecords_ok_iff _ _ _).mp (mapError_ok hdecode)
  have hconstants := recordsRead_decodedOf_coherent w.env w.order
    (fun a _ lc hget c hdec => by rw [w.coherent a lc hget, hdec]; rfl) hreading
  refine ⟨(Admission.preflight_ok_iff _ _ _).mp (mapError_ok hbatch),
    (Admission.uniqueKeys_ok_iff _ _).mp (mapError_ok hunique),
    (Admission.authenticate_ok_iff _ _ _).mp (mapError_ok hauth), ?_⟩
  rw [← hconstants]
  exact recordsReadBare_of_recordsRead hreading

/-- The approved witness admits the concrete bare role preparation at the same bytes,
order, and limits. Its output array is separate from the accepted full array. -/
theorem admitted_prepareBare {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b) :
    let cx := Admission.streamContext _root_.Address.admissionHash w.table w.prelude
      (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order) (Ix.Cert.hintsOf w.env)
    ∃ final decls,
      w.fullDecls.toList.filter (fun d => !d.isGenerated) = decls.toList ∧
      Admission.prepareBare _root_.Address.admissionHash b w.prelude w.limits
        (Ix.Cert.recordsOf w.env w.order) (Ix.Cert.blobsOf w.env w.order) (Ix.Cert.hintsOf w.env) =
        .ok (evidenceOf cx final w.table, Frontend.preparePrelude w.prelude.ix decls) := by
  dsimp only
  obtain ⟨final, decls, hbare, hfilter, hkeeps⟩ := admitted_streamReadBare_keepsPrelude w
  obtain ⟨hbatch, hunique, hauth, hdecode⟩ := admitted_bare_byteFacts w
  exact ⟨final, decls, hfilter, prepareBare_ok hbatch hunique hauth w.admitted hdecode hbare hkeeps⟩

end IxVM.Refinement.Assembly
