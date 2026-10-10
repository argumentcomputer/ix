import Ix.CompileCert.Publication

/-!
# Anonymous preservation during original-form promotion

Promotion attaches original metadata and source-name claims to previously
generated auxiliaries. Its constants remain ephemeral, but its literal and
metadata blobs enter the anonymous store. These results cover the actual
promotion loop and the checked blob merge, without digest-injectivity or
metadata-fidelity assumptions. They do not assert source faithfulness.
-/

namespace Ix.CompileCert.Publication
open Ix.CompileM

theorem promoteAuxDriver_anonymous (before after : CompileEnv)
    (name : Ix.Name) (origAddr : Address) (origMeta : Ixon.ConstantMeta)
    (accepted : promoteAuxDriver before name origAddr origMeta = .ok after) :
    anonymous after = anonymous before := by
  unfold promoteAuxDriver at accepted
  simp only [bind, pure, Except.bind, Except.pure, throw, throwThe] at accepted
  repeat' first | split at accepted | cases accepted
  all_goals rfl

private theorem promotionLoop (rows : Array (Ix.Name × Address × Ixon.ConstantMeta))
    (before after : DriverAcc)
    (accepted : forIn rows before (fun row state => do
      let cenv ← Ix.PhaseTimers.withPhase .noAux state.cenv
        (promoteAuxDriver · row.1 row.2.1 row.2.2)
      pure (.yield { state with cenv })) = (Except.ok after : Except CompileError DriverAcc)) :
    anonymous after.cenv = anonymous before.cenv := by
  apply Canon.forIn_except_array _ (fun _ state => anonymous state.cenv = anonymous before.cenv)
    ?_ rows rfl accepted
  intro pre row state step previous success
  obtain ⟨cenv, promoted, emitted⟩ := Canon.except_bind_ok.mp success
  have preserve := promoteAuxDriver_anonymous state.cenv cenv row.1 row.2.1 row.2.2
    (by simpa [Ix.PhaseTimers.withPhase, Ix.PhaseTimers.enterV, Ix.PhaseTimers.exitV] using promoted)
  refine ⟨{ state with cenv }, (Canon.except_pure_ok emitted).symm, preserve.trans previous⟩

/-- Original-form promotion does not publish its original constants. Its
anonymous effect is exactly the incoming blob writes. -/
theorem promoteOriginalBlock_anonymous (before after : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (accepted : promoteOriginalBlock before lo result cache = .ok after) :
    after.cenv.constants = before.cenv.constants ∧
      after.cenv.blobs = applyWrites before.cenv.blobs (blobWrites cache) := by
  unfold promoteOriginalBlock at accepted
  obtain ⟨_, _, accepted⟩ := Canon.except_bind_ok.mp accepted
  obtain ⟨staged, loop, accepted⟩ := Canon.except_bind_ok.mp accepted
  have preserved := promotionLoop _ before staged loop
  have hc := congrArg AnonymousStore.constants preserved
  have hb := congrArg AnonymousStore.blobs preserved
  have out := Canon.except_pure_ok accepted
  subst after
  exact ⟨hc, by
    simpa [Std.HashMap.fold_eq_foldl_toList, applyWrites, blobWrites, anonymous] using
      (congrArg (fun store => applyWrites store (blobWrites cache)) hb)⟩

theorem promoteOriginalBlock_content (before after : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (accepted : promoteOriginalBlock before lo result cache = .ok after) :
    checkWrites before.cenv.blobs (blobWrites cache) = true := by
  unfold promoteOriginalBlock at accepted
  obtain ⟨_, checked, _⟩ := Canon.except_bind_ok.mp accepted
  have writes : checkAnonymousWrites before.cenv.blobs (blobWrites cache) = true := by
    unfold checkBlobContent at checked
    split at checked
    · assumption
    · cases checked
  simpa only [checkAnonymousWrites_eq] using writes

/-- A successful promotion preserves every prior anonymous record and blob. -/
theorem promoteOriginalBlock_extends (before after : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (accepted : promoteOriginalBlock before lo result cache = .ok after) :
    Extends before.cenv.constants after.cenv.constants ∧
      Extends before.cenv.blobs after.cenv.blobs := by
  obtain ⟨constants, blobs⟩ := promoteOriginalBlock_anonymous before after lo result cache accepted
  rw [constants, blobs]
  exact ⟨Extends.refl _, applyWrites_preserves
    (checkWrites_compatible (promoteOriginalBlock_content before after lo result cache accepted))⟩

theorem promoteOriginalBlock_present (before after : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (accepted : promoteOriginalBlock before lo result cache = .ok after) :
    ∀ key bytes, (key, bytes) ∈ blobWrites cache → after.cenv.blobs[key]? = some bytes := by
  rw [(promoteOriginalBlock_anonymous before after lo result cache accepted).2]
  exact (checkWrites_sound (promoteOriginalBlock_content before after lo result cache accepted)).2

end Ix.CompileCert.Publication
