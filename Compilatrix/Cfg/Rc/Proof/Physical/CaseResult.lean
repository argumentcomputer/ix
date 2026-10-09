import Compilatrix.Cfg.Rc.Proof.Physical.CaseActivation
import Compilatrix.Cfg.Rc.Proof.Native.CodeRecursion

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Rt.Rc.Procs

theorem case_result {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true)
    {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} (consuming : consumeAll P = .ok pairs)
    (switches : Rt.checkSwitches P.base = .ok ()) {main clock : Nat}
    {sourceJoins : List Fir.JEntry} {x : Fir.Var} {alts : List Fir.Alt} {default : Option Fir.Code}
    (next : ∀ body, body.size < (Fir.Code.case x alts default).size →
      PhysicalCode F P config pairs main clock sourceJoins body) :
    PhysicalCode F P config pairs main clock sourceJoins (.case x alts default) := by
  intro H addresses external live sourceEnv ownedEnv roots joins ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  rw [Fir.eval_case]
  cases lookup : sourceEnv.get? x with
  | none => simp only [lookup, Sem.Result.ofOption, Sem.Result.bind]; trivial
  | some logical =>
    simp only [lookup, Sem.Result.ofOption, Sem.Result.bind_ok]
    cases constructor : logical.asCtor F.known with
    | none => simp only [constructor]; trivial
    | some pair =>
      obtain ⟨key, fields⟩ := pair
      simp only [constructor]
      rw [firCase_eval]
      cases selected : firCase key alts default with
      | none => trivial
      | some body =>
        rcases case_activation checked consuming switches before sourceLookup lookup constructor selected
            heap callers with success | failure
        · obtain ⟨after, final, cost, activation, trace, sameFn, smaller⟩ := success
          exact ResultAt.prefix trace (fun _ _ _ den => den) (HeapHistory.refl _ _) (by omega)
            (next body smaller _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ callers
              (by simpa only [sameFn] using sourceLookup) activation heap)
        · exact ResultAt.of_fails failure


end Compilatrix.Cfg.Rc.Native.Spec
