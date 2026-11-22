import IxCC.Fir.Proof.Retained
import IxCC.Recheck.Rc.Proof.Replay
import IxCC.Cfg.Rc.Proof.Native.ReturnedObservation

/-! Retain source witnesses directly through the actual Fir lowering. The
physical induction can consume these witnesses without comparing its heap
with an independently executed abstract Cfg heap. -/
set_option autoImplicit false
namespace IxCC.Recheck.RcReplay
open IxCC.Sem (Lang)
open IxCC.Rt.Rc.Procs
open IxCC.Cfg.Rc.Native.Spec

/-- The actual Anf value and Fir representation behind a source observation. -/
def SourceFirWitness (A : Anf.Program) (observation : Option Sem.Obs)
    (logical : Fir.Val) : Prop :=
  ∃ value, Anf.obsV value = observation ∧ Fir.Proof.FirWitness A value logical

theorem source_fir_retained {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFront cfg P c = .ok f) (i : Nat × List Nat) (hi : f.Covered c i) :
    Sem.Behaviour.Refines
      (fun value logical => SourceFirWitness f.anf
        (Lang.obs (S := Lam.Erase.Proof.CheckedProgram) value) logical)
      (Lang.behaviour (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i)
      (Lang.behaviour f.fir i) := by
  obtain ⟨_, ⟨st, erased⟩, anf, fir, _, _, _⟩ := runFront_spec accepted
  have front := Sem.RefinesOn.refines_trans (Lam.Erase.Proof.erase_refines erased)
    (Recheck.anfOf_refines anf)
  have tail := (Fir.Proof.lower_retained fir i).refines
    (Lang.mono f.anf i) (Lang.mono f.fir i)
  exact ((front i hi).trans tail).mono fun _ _ ⟨value, observed, retained⟩ =>
    ⟨value, observed.symm, retained⟩

/-- An actual Fir success exposes its retained source witness, unless the
accepted source itself reaches stuck. No typing or observation is assumed. -/
theorem source_fir_success {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFront cfg P c = .ok f) {i : Nat × List Nat} (hi : f.Covered c i) {k : Nat}
    {logical : Fir.Val} (success : Fir.firRun f.fir i k = .ok logical) :
    (∃ k' value,
      Lang.run (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i k' = .ok value ∧
      SourceFirWitness f.anf (Lang.obs (S := Lam.Erase.Proof.CheckedProgram) value) logical) ∨
    ∃ k', Lang.run (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i k' = .stuck := by
  have behavior : Lang.behaviour f.fir i = .terminates logical :=
    (Sem.behaviour_eq_terminates_iff (Lang.mono f.fir i)).2 ⟨k, success⟩
  have related := source_fir_retained accepted i hi
  rw [behavior] at related
  rcases related.of_terminates with ⟨value, terminated, witness⟩ | stuck
  · obtain ⟨k', run⟩ := (Sem.behaviour_eq_terminates_iff
      (Lang.mono (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i)).1 terminated
    exact .inl ⟨k', value, run, witness⟩
  · exact .inr ((Sem.behaviour_eq_stuck_iff
      (Lang.mono (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i)).1 stuck)

theorem SourceFirWitness.observations {A : Anf.Program} {observation : Option Sem.Obs}
    {logical : Fir.Val} (witness : SourceFirWitness A observation logical) :
    Fir.obsV logical = observation := by
  obtain ⟨value, observed, related⟩ := witness
  exact related.observations.symm.trans observed

theorem SourceFirWitness.value {A : Anf.Program} {observation : Sem.Obs}
    {logical : Fir.Val} (witness : SourceFirWitness A (some observation) logical) :
    ∃ value, Fir.Proof.VR A value logical ∧ Fir.obsV logical = some observation := by
  obtain ⟨value, observed, related⟩ := witness
  rcases related with related | ⟨unobserved, _⟩
  · exact ⟨value, related, (Fir.Proof.vr_obs related).symm.trans observed⟩
  · rw [observed] at unobserved
    cases unobserved

/-- Read the actual physical return memory through the accepted source tree
view. Its heap, extent, address map and readback fuel come from Returned. -/
theorem SourceFirWitness.observe {A : Anf.Program} {source target : Sem.Obs}
    {logical : Fir.Val} (witness : SourceFirWitness A (some source) logical)
    {P : Cfg.Rc.Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {origin : Own.Heap} {originAddresses : AddressMap} {external : Nat → Nat}
    {context base limit : Lir.Word} {regionBytes : Nat}
    (returned : Returned P pairs lp origin originAddresses external context base limit regionBytes logical)
    {signature : Rt.Sig} {type : Rt.FoTy}
    (viewed : Readback.treeView A.ctors signature type source = some target) :
    Rt.readback signature (regionBytes / 8) returned.memory type returned.word = some target := by
  obtain ⟨value, related, observed⟩ := witness.value
  exact returned.observe related observed viewed






end IxCC.Recheck.RcReplay
