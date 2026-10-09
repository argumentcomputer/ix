import Compilatrix.Cfg.Rc.Proof.CallReach
import Compilatrix.Cfg.Rc.Proof.CallStep
import Compilatrix.Cfg.Rc.Proof.Ordinary
import Compilatrix.Cfg.Rc.Proof.JoinStep
import Compilatrix.Cfg.Rc.Proof.JumpStep
import Compilatrix.Cfg.Rc.Proof.Terminals
import Compilatrix.Cfg.Rc.Proof.TailSelf
import Compilatrix.Cfg.Rc.Proof.Outcomes
import Compilatrix.Cfg.Rc.Proof.Case
import Compilatrix.Own.Plain.Proof.Mono

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc
open Compilatrix.Sem (Result)

theorem eval_reach {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true) (clock : Nat)
    (ihClock : ∀ k < clock, SimAt F bodies P k)
    (fr : Frame) (ρ : Own.Env) (saved : List Own.Plain.JEntry) (H : Own.Heap)
    (code : Own.Plain.Code) (stk : List (Frame × Fir.Var)) (stateRel : At F P fr ρ saved code) :
    Reach P clock (.run fr stk H) stk (Own.Plain.eval {source := F, bodies} clock ρ saved H code) := by
  cases codeEq : code with
  | act action body =>
    rw [codeEq] at stateRel
    rw [Own.Plain.eval_act]
    rcases action_outcome ρ H action with effect | ⟨afterHeap, effect⟩
    · rw [effect]; exact Reach.stuck
    · rw [effect, Result.bind_ok]
      obtain ⟨after, step, frame⟩ := stateRel.action checked effect
      exact Reach.free step (eval_reach checked clock ihClock after ρ saved afterHeap body stk frame)
  | bind x rhs body =>
    rw [codeEq] at stateRel
    by_cases call : ∃ f args, rhs = .call f args
    · obtain ⟨f, args, rfl⟩ := call
      rw [Own.Plain.eval_bindCall]
      cases values : Own.evalArgs ρ args with
      | none => simp only [Result.ofOption, Result.bind]; exact Reach.stuck
      | some vs =>
        simp only [Result.ofOption, Result.bind_ok]
        cases sourceLookup : F.fun? f with
        | none =>
          rw [Own.Plain.evalCall_eq, sourceLookup]
          simp only [Result.ofOption, Result.bind]
          exact Reach.stuck
        | some fd =>
          have size := generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
          have range : f < P.base.size := by rw [size]; exact checked_source_dense checked sourceLookup
          obtain ⟨continuation, step, resume⟩ := stateRel.call_step range values stk H
          exact Reach.call step (call_reach checked clock ihClock f vs _ H)
            (fun v afterHeap _ => eval_reach checked clock ihClock
              {continuation with env := continuation.env.insert x v} (ρ.insert x v) saved afterHeap body stk (resume v))
    · have noCall : ∀ f args, rhs ≠ .call f args := fun f args eq => call ⟨f, args, eq⟩
      rw [Own.Plain.eval_bindRhs _ _ _ _ _ _ _ _ noCall]
      simp only [Own.Plain.Program.tables]
      rcases rhs_outcome {ctors := F.ctors, known := F.known} ρ H rhs with effect | ⟨value, effect⟩
      · rw [effect]; exact Reach.stuck
      · rw [effect, Result.bind_ok]
        obtain ⟨after, step, frame⟩ := stateRel.bind checked noCall effect
        exact Reach.free step (eval_reach checked clock ihClock after (ρ.insert x value.1) saved value.2 body stk frame)
  | jp j ps captured rec body cont =>
    rw [codeEq] at stateRel
    rw [Own.Plain.eval_jp]
    exact eval_reach checked clock ihClock fr ρ _ H cont stk stateRel.join
  | jmp j args =>
    rw [codeEq] at stateRel
    rw [Own.Plain.eval_jmp]
    cases found : Own.Plain.lookupJ j saved with
    | none => simp only [Result.ofOption, Result.bind]; exact Reach.stuck
    | some pair =>
      obtain ⟨entry, rest⟩ := pair
      simp only [Result.ofOption, Result.bind_ok]
      cases values : Own.evalArgs ρ args with
      | none => simp only [Result.ofOption, Result.bind]; exact Reach.stuck
      | some vs =>
        simp only [Result.ofOption, Result.bind_ok, Own.Plain.jumpTo]
        by_cases arity : vs.length = entry.params.length
        · simp only [arity, ↓reduceIte]
          obtain ⟨after, step, frame⟩ := stateRel.jump found values arity stk H
          cases charge : entry.charged with
          | true =>
            simp only [↓reduceIte]
            exact Reach.charge (by simpa [charge] using step)
              (fun k smaller => ihClock k (by omega) _ _ _ _ _ _ frame)
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            have jumpSize := Own.Plain.jump_measure found charge
            exact Reach.free (by simpa [charge] using step)
              (eval_reach checked clock ihClock after (Own.bindAll entry.env entry.params vs)
                (entry.after rest) H entry.body stk frame)
        · simp only [arity, ↓reduceIte]; exact Reach.stuck
  | case x alts d =>
    rw [codeEq] at stateRel
    exact case_reach checked clock stateRel H stk (fun body smaller after frame =>
      eval_reach checked clock ihClock after ρ saved H body stk frame)
  | ret arg =>
    rw [codeEq] at stateRel
    rw [Own.Plain.eval_ret]
    cases value : Own.evalArg ρ arg with
    | none => simp only [Result.ofOption, Result.bind]; exact Reach.stuck
    | some v =>
      simp only [Result.ofOption, Result.bind_ok]
      exact ⟨0, .free (stateRel.ret value stk H) (.refl _)⟩
  | tcall f args =>
    rw [codeEq] at stateRel
    rw [Own.Plain.eval_tcall]
    cases values : Own.evalArgs ρ args with
    | none => simp only [Result.ofOption, Result.bind]; exact Reach.stuck
    | some vs =>
      simp only [Result.ofOption, Result.bind_ok]
      by_cases self : f = fr.fn
      · subst f
        rw [Own.Plain.evalCall_eq]
        cases sourceLookup : F.fun? fr.fn with
        | none => simp only [Result.ofOption, Result.bind]; exact Reach.stuck
        | some fd =>
          simp only [Result.ofOption, Result.bind_ok]
          cases bodyLookup : bodies.get? fr.fn with
          | none => simp only [Result.ofOption, Result.bind]; exact Reach.stuck
          | some body =>
            simp only [Result.ofOption, Result.bind_ok, Own.Plain.callFun]
            by_cases arity : vs.length = fd.params.length
            · simp only [arity, ↓reduceIte]
              obtain ⟨after, step, frame⟩ := stateRel.tail_self checked sourceLookup bodyLookup values arity stk H
              exact Reach.charge step (fun k smaller => ihClock k (by omega) _ _ _ _ _ _ frame)
            · simp only [arity, ↓reduceIte]; exact Reach.stuck
      · exact Reach.free (stateRel.tail_other self values stk H) (call_reach checked clock ihClock f vs stk H)
  | trap =>
    rw [codeEq] at stateRel
    rw [Own.Plain.eval_trap]
    exact ⟨0, _, .refl _, stateRel.trap stk H⟩
termination_by code.size + Own.Plain.jweight saved
decreasing_by
  all_goals simp_wf
  all_goals simp only [codeEq, Own.Plain.Code.size]
  all_goals simp_all only [Own.Plain.Code.size, Own.Plain.jweight,
    Own.Plain.JEntry.weight, Bool.false_eq_true, ↓reduceIte]
  all_goals omega

theorem checked_sim_at {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true) : ∀ clock, SimAt F bodies P clock := by
  intro clock
  induction clock using Nat.strongRecOn with
  | _ clock ih => exact eval_reach checked clock ih

theorem checked_call_reach {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true) (clock f : Nat) (vs : List Own.RVal)
    (stk : List (Frame × Fir.Var)) (H : Own.Heap) :
    Reach P clock (.call f vs stk H) stk (Own.Plain.evalCall {source := F, bodies} clock f vs H) :=
  call_reach checked clock (fun k _ => checked_sim_at checked k) f vs stk H


end Compilatrix.Cfg.Rc
