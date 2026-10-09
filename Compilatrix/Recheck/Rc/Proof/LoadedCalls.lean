import Compilatrix.Recheck.Rc.Proof.FrontLanguage
import Compilatrix.Cfg.Rc.Proof.Physical.PublicEntry
import Compilatrix.Cfg.Rc.Proof.Physical.NumericEntry
import Compilatrix.Recheck.Rc.Proof.FrontParts

/-! Exact-arity loaded calls, including actual initialization, numeric
representation failure, physical execution, all public layout stages, and
complete source-relative result observation. -/
set_option autoImplicit false
namespace Compilatrix.Recheck.RcReplay
open Compilatrix.Sem (Lang Obs Result Sim)
open Compilatrix.Cfg.Rc.Native.Spec

theorem erased_view (f : Front) (root : Nat) : ViewedFirRel f root .erased none := by
  intro source witness
  have empty : source = none := witness.observations.symm
  subst source
  unfold Front.view treeViewOf Sem.viewResult
  dsimp only
  cases f.tys root with
  | none => exact .ok rfl
  | some _ => exact .stuck

/-- The caller supplies only accepted replay, the actual source function,
numeric arity, and the existing model-region contract. Initialization,
ownership, physical heap, code simulation and readback are all derived. -/
theorem loaded_call_sim {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (accepted : runFront cfg P cert = .ok f) {model : Rt.Model}
    (region : Rt.Proof.RegionOk model.ctx model.size)
    (readable : Rt.Proof.LirRegion model.mem model.ctx model.size)
    (root fn : Nat) {sourceFunction : Fir.Fun}
    (sourceLookup : f.fir.fun? fn = some sourceFunction)
    (numbers : List Nat) (arity : numbers.length = sourceFunction.params.length) :
    Sim (ViewedFirRel f root) Nat.succ
      (fun clock => Fir.run f.fir clock fn (Fir.litArgs numbers))
      (fun clock => (f.loaded model).call
        {fn, params := sourceFunction.params.length, ty := f.tys root} numbers clock) := by
  let entry : Rt.Entry := {fn, params := sourceFunction.params.length, ty := f.tys root}
  cases encoded : Rt.natWords numbers with
  | none =>
    refine Sim.ofEq (Sim.to_resource .natOverflow) (fun _ => rfl) ?_
    intro clock
    simp only [Rt.Loaded.call, encoded]
  | some words =>
    have checked := (runFront_spec accepted).2.2.2.2.2.2
    have native := (runFront_native accepted).2
    obtain ⟨pairs, functions, left, initialized, base, limit, admission, init, post, heap, _⟩ :=
      numeric_entry checked native sourceLookup encoded arity region readable
    obtain ⟨den, balance, represented, compatible⟩ :=
      numeric_inputs (P := f.cfg) pairs encoded
    have simulation := public_entry_eval_sim admission native sourceLookup den balance represented
      compatible (by simpa only [Own.litArgs, List.length_map] using arity) heap
    have observed := simulation.map_right fun output =>
      entry.observe model.fuel output.1 output.2
    refine Sim.ofEq (observed.mono ?_) (fun _ => rfl) ?_
    · rintro logical observation ⟨output, retained, rfl⟩
      obtain ⟨returned, rfl⟩ := retained
      exact returned_view returned entry rfl
    · intro clock
      simp only [Front.loaded, Rt.Loaded.ofLowered, Rt.Loaded.call, encoded]
      rw [init clock, Result.bind_ok]



end Compilatrix.Recheck.RcReplay
