import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.ArgumentActivation
import Compilatrix.Cfg.Rc.Proof.Native.CodeRecursion
import Compilatrix.Own.Plain.Proof.NonCall
import Compilatrix.Fir.Proof.Unfold

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
open Compilatrix Compilatrix.Cfg.Rc Compilatrix.Cfg.Rc.Native
open Compilatrix.Cfg.Rc.Native.Spec Compilatrix.Rt.Rc.Procs

/-- Ordinary primitive binding consumes no source clock. The continuation
receives the actual post-instruction activation, including omitted comparisons. -/
theorem primitive_result {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)}
    {functions : List Lir.Func} (admitted : CodeAdmission F bodies P config pairs functions)
    {main clock x : Nat} {sourceJoins : List Fir.JEntry} {body : Fir.Code}
    (op : Lam.Prim) (args : List Fir.Arg)
    (next : PhysicalCode F P config pairs main clock sourceJoins body) :
    PhysicalCode F P config pairs main clock sourceJoins (.bind x (.prim op args) body) := by
  intro H addresses external live sourceEnv ownedEnv roots joins ownedJoins sourceFd fd
    source target mem context base bump limit regionBytes slots lists callers sourceLookup before heap
  rw [Fir.eval_bind_prim]
  rcases Own.Plain.fir_rhs_pure F sourceEnv (.prim op args) with stuck | ⟨logical, evaluation⟩
  · rw [stuck]; trivial
  · rw [evaluation, Sem.Result.bind_ok]
    rcases primitive_activation admitted.scopedProgram admitted.consuming
        (Public.Spec.rawSource config P pairs) main sourceLookup before heap evaluation [] callers
        with success | failed
    · obtain ⟨value, tail, charge, after, _, trace, activation, ready⟩ := success
      exact ResultAt.prefix trace (fun _ _ _ den => den) (HeapHistory.refl _ _) (by omega)
        (next H addresses external (live ++ [x]) (sourceEnv.insert x logical)
          (ownedEnv.insert x value) (roots ++ [value]) joins ownedJoins sourceFd fd
          {source with rest := tail, env := source.env.insert x value} after mem
          context base bump limit regionBytes slots lists callers sourceLookup activation ready)
    · exact ResultAt.of_fails failed

/-- The emitted copy prefix retains every old denotation and address while
creating the extra owned occurrence passed to the same-clock continuation. -/
theorem argument_result {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)}
    {functions : List Lir.Func} (admitted : CodeAdmission F bodies P config pairs functions)
    {main clock x : Nat} {sourceJoins : List Fir.JEntry} {body : Fir.Code}
    (arg : Fir.Arg)
    (next : PhysicalCode F P config pairs main clock sourceJoins body) :
    PhysicalCode F P config pairs main clock sourceJoins (.bind x (.arg arg) body) := by
  intro H addresses external live sourceEnv ownedEnv roots joins ownedJoins sourceFd fd
    source target mem context base bump limit regionBytes slots lists callers sourceLookup before heap
  rw [Fir.eval_bind_arg]
  rcases Own.Plain.fir_rhs_pure F sourceEnv (.arg arg) with stuck | ⟨logical, evaluation⟩
  · rw [stuck]; trivial
  · rw [evaluation, Sem.Result.bind_ok]
    rcases argument_activation admitted.scopedProgram admitted.consuming
        (Public.Spec.rawSource config P pairs) main sourceLookup before heap evaluation callers
        with success | failed
    · obtain ⟨value, H', mem', tail, charge, after, _, trace, activation, ready, size, values⟩ := success
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
