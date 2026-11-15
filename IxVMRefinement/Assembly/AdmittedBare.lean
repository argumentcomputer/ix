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
  · assumption
  · simp [throw, throwThe, MonadExceptOf.throw] at hstream

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

end IxVM.Refinement.Assembly
