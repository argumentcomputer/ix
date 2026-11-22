import IxCC.Cfg.Rc.Proof.Retained
import IxCC.Recheck.Rc.Proof.Replay
import IxCC.Rt.Rc.Proof.Readback.View
import IxCC.Sem.View
import IxCC.Recheck.Rc.View

set_option autoImplicit false
namespace IxCC.Recheck.RcReplay
open IxCC.Rt.Rc
open IxCC.Sem (Lang Sim)
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Rc.Procs.Readback

/-- The logical result survives both heap lowering and abstract Cfg execution. -/
def HeapWitness (A : Anf.Program) (value : Anf.Val) (result : Own.RVal × Own.Heap) : Prop :=
  ∃ logical, Fir.Proof.FirWitness A value logical ∧ Own.Proof.Den result.2 result.1 logical

theorem checked_retained {A : Anf.Program} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Cfg.Rc.Program}
    (lowered : Fir.lower A = .ok F)
    (checked : Cfg.Rc.checkScopedProgram F bodies P = true) (i : Nat × List Nat) :
    Sim (HeapWitness A) (fun k => Fir.tickBound A * (k+1))
      (Anf.anfRun A i) (Cfg.Rc.cfgRun P i) := by
  have heap := Own.Plain.owned_retained
    (Cfg.Rc.checkProgram_parts (Cfg.Rc.checkScopedProgram_parts checked).1).1
    (Own.Plain.exports_of_lower lowered) i
  have tail := Sem.Sim.comp (Lang.mono P i) heap (Cfg.Rc.checked_retained checked i)
  have all := Sem.Sim.comp (Lang.mono P i) (Fir.Proof.lower_retained lowered i) tail
  exact all.mono fun _ _ ⟨logical, related, middle, den, equal⟩ =>
    ⟨logical, related, equal ▸ den⟩

/-- Source observations retain the actual Anf/Fir witnesses. This is derived
from execution, never supplied as a certificate or driver hypothesis. -/
def SourceWitness (A : Anf.Program) (observation : Option Sem.Obs)
    (result : Own.RVal × Own.Heap) : Prop :=
  ∃ value, Anf.obsV value = observation ∧ HeapWitness A value result

theorem source_retained {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFront cfg P c = .ok f) (i : Nat × List Nat) (hi : f.Covered c i) :
    Sem.Behaviour.Refines
      (fun value result => SourceWitness f.anf
        (Lang.obs (S := Lam.Erase.Proof.CheckedProgram) value) result)
      (Lang.behaviour (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i)
      (Lang.behaviour f.cfg i) := by
  obtain ⟨_, ⟨st, erased⟩, anf, fir, _, _, checked⟩ := runFront_spec accepted
  have front := Sem.RefinesOn.refines_trans (Lam.Erase.Proof.erase_refines erased)
    (Recheck.anfOf_refines anf)
  have tail := (checked_retained fir checked i).refines
    (Lang.mono f.anf i) (Lang.mono f.cfg i)
  exact ((front i hi).trans tail).mono fun _ _ ⟨value, observed, retained⟩ =>
    ⟨value, observed.symm, retained⟩

/-- A successful real Cfg result exposes the retained source/Fir witness,
or the actual checked source was stuck. No source typing premise is added. -/
theorem source_retained_success {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFront cfg P c = .ok f) {i : Nat × List Nat} (hi : f.Covered c i) {k : Nat}
    {result : Own.RVal × Own.Heap} (success : Cfg.Rc.cfgRun f.cfg i k = .ok result) :
    (∃ k' value,
      Lang.run (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i k' = .ok value ∧
      SourceWitness f.anf (Lang.obs (S := Lam.Erase.Proof.CheckedProgram) value) result) ∨
    ∃ k', Lang.run (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i k' = .stuck := by
  have behavior : Lang.behaviour f.cfg i = .terminates result :=
    (Sem.behaviour_eq_terminates_iff (Lang.mono f.cfg i)).2 ⟨k, success⟩
  have related := source_retained accepted i hi
  rw [behavior] at related
  rcases related.of_terminates with ⟨value, terminated, witness⟩ | stuck
  · obtain ⟨k', run⟩ := (Sem.behaviour_eq_terminates_iff
      (Lang.mono (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i)).1 terminated
    exact .inl ⟨k', value, run, witness⟩
  · exact .inr ((Sem.behaviour_eq_stuck_iff
      (Lang.mono (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i)).1 stuck)

theorem SourceWitness.readback {A : Anf.Program} {source target : Sem.Obs}
    {v : Own.RVal} {H : Own.Heap} (witness : SourceWitness A (some source) (v,H))
    {sig : Rt.Sig} {ty : Rt.FoTy}
    (viewed : treeView A.ctors sig ty source = some target)
    {addresses : AddressMap} {mem : X86.Memory} {base bump limit : Lir.Word}
    {slots : List Slot} {regionBytes : Nat}
    (heap : Gen.HeapLive H addresses mem) (scanned : Readback.Scanned H)
    (partition : Gen.ArenaPartition maxClass H addresses base bump limit slots)
    (ordered : Own.Rc.HeapOk H) (extent : limit.toNat-base.toNat ≤ regionBytes)
    {word : Lir.Word} (represented : valueWord addresses v = some word) :
    Rt.readback sig (regionBytes/8) mem ty word = some target := by
  obtain ⟨value, observed, logical, related, den⟩ := witness
  rcases related with related | ⟨unobserved, _⟩
  · exact viewed_readback_region related ((Fir.Proof.vr_obs related).symm.trans observed)
      viewed heap scanned partition ordered extent den represented
  · rw [observed] at unobserved
    cases unobserved

theorem rejected_treeView {table : List Lam.CtorInfo}
    {types : Nat → Option (Rt.Sig × Rt.FoTy)} {root : Nat}
    {observation : Option Sem.Obs}
    (rejected : treeViewOf table types root observation = none) :
    (Sem.viewResult (treeViewOf table types) root observation).GoesWrong := by
  rw [Sem.viewResult_eq_stuck.mpr rejected]
  trivial

end IxCC.Recheck.RcReplay
