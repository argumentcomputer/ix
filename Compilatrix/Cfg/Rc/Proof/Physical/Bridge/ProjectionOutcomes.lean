import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.FieldlessActivation
import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.ProjectionActivation
import Compilatrix.Cfg.Rc.Proof.Native.CodeRecursion
import Compilatrix.Own.Plain.Proof.NonCall
import Compilatrix.Fir.Proof.Unfold

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
open Compilatrix Compilatrix.Cfg.Rc Compilatrix.Cfg.Rc.Native
open Compilatrix.Cfg.Rc.Native.Spec Compilatrix.Rt.Rc.Procs

theorem fieldless_result {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)}
    {functions : List Lir.Func} (admitted : CodeAdmission F bodies P config pairs functions)
    {main clock x : Nat} {sourceJoins : List Fir.JEntry} {body : Fir.Code}
    (ctor : Fir.CtorInfo) (args : List Fir.Arg) (zero : ctor.arity = 0)
    (next : PhysicalCode F P config pairs main clock sourceJoins body) :
    PhysicalCode F P config pairs main clock sourceJoins (.bind x (.ctor ctor args) body) := by
  intro H addresses external live sourceEnv ownedEnv roots joins ownedJoins sourceFd fd
    source target mem context base bump limit regionBytes slots lists callers sourceLookup before heap
  rw [Fir.eval_bind_ctor]
  rcases Own.Plain.fir_rhs_pure F sourceEnv (.ctor ctor args) with stuck | ⟨logical, evaluation⟩
  · rw [stuck]; trivial
  · rw [evaluation, Sem.Result.bind_ok]
    rcases fieldless_activation admitted.scopedProgram admitted.consuming
        (Public.Spec.rawSource config P pairs) main zero sourceLookup before heap evaluation [] callers
        with success | failed
    · obtain ⟨tail, charge, after, _, trace, activation, ready⟩ := success
      exact ResultAt.prefix trace (fun _ _ _ den => den) (HeapHistory.refl _ _) (by omega)
        (next H addresses external (live ++ [x]) (sourceEnv.insert x logical)
          (ownedEnv.insert x (.ctor0 ctor)) (roots ++ [.ctor0 ctor]) joins ownedJoins sourceFd fd
          {source with rest := tail, env := source.env.insert x (.ctor0 ctor)} after mem
          context base bump limit regionBytes slots lists callers sourceLookup activation ready)
    · exact ResultAt.of_fails failed

/-- Covers heap fields and Nat successor views. Ownership is established by
the explicit emitted increment before the continuation receives the value. -/
theorem projection_result {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)}
    {functions : List Lir.Func} (admitted : CodeAdmission F bodies P config pairs functions)
    {main clock x : Nat} {sourceJoins : List Fir.JEntry} {body : Fir.Code}
    (y : Nat) (key : Key.CtorKey) (i : Nat)
    (next : PhysicalCode F P config pairs main clock sourceJoins body) :
    PhysicalCode F P config pairs main clock sourceJoins (.bind x (.proj y key i) body) := by
  intro H addresses external live sourceEnv ownedEnv roots joins ownedJoins sourceFd fd
    source target mem context base bump limit regionBytes slots lists callers sourceLookup before heap
  rw [Fir.eval_bind_proj]
  rcases Own.Plain.fir_rhs_pure F sourceEnv (.proj y key i) with stuck | ⟨logical, evaluation⟩
  · rw [stuck]; trivial
  · rw [evaluation, Sem.Result.bind_ok]
    rcases projection_activation admitted.scopedProgram
        (Public.Spec.rawSource config P pairs) main sourceLookup before heap evaluation callers
        with success | failed
    · obtain ⟨value, H', mem', tail, after, _, _, trace, activation, ready, size, values⟩ := success
      have preserved : Own.Plain.ExternalPreserved H H' external := by
        intro root logical _ den
        change H'.value? root = some logical
        rw [← values root]
        exact den
      have history : HeapHistory H.size addresses H'.size addresses :=
        ⟨by omega, fun _ _ => rfl⟩
      exact ResultAt.prefix trace preserved history (by omega)
        (next H' addresses external (live ++ [x]) (sourceEnv.insert x logical)
          (ownedEnv.insert x value) (roots ++ [value]) joins ownedJoins sourceFd fd
          {source with rest := tail, env := source.env.insert x value} after mem'
          context base bump limit regionBytes slots lists callers sourceLookup activation ready)
    · exact ResultAt.of_fails failed



end Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
