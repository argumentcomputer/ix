import IxCC.Cfg.Rc.Proof.Environment
import IxCC.Cfg.Proof.Sim

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open IxCC.Sem (Result Star)

theorem step_return {P : Program} {fr : Frame} {stk : List (Frame × Fir.Var)} {H : Own.Heap}
    {fd : Cfg.Fun} {b : Block} {a : Fir.Arg} {v : Own.RVal}
    (hr : fr.rest = []) (hf : P.base.fun? fr.fn = some fd)
    (hb : fd.block? fr.blk = some b) (ht : b.term = .ret a)
    (ha : Own.evalArg fr.env a = some v) :
    step P (.run fr stk H) = .next (.ret v stk H) false := by
  simp [step, hr, Cfg.step, hf, hb, ht, ha]

/-- A real source return with its RC prefix reaches the actual Cfg return
state, preserving arbitrary caller frames and the precise output heap. -/
theorem return_reach {P : Program} {Q : Own.Plain.Program} {k first : Nat}
    {ρ : Own.Env} {J : List Own.Plain.JEntry} {actions : List Action} {a : Fir.Arg}
    {fr : Frame} {stk : List (Frame × Fir.Var)} {H H' : Own.Heap} {v : Own.RVal}
    {fd : Cfg.Fun} {b : Block} {table : ActionTable}
    (env : EnvSub ρ fr.env)
    (hr : fr.rest = encodePrefix P.base.size first actions)
    (hf : P.base.fun? fr.fn = some fd) (hb : fd.block? fr.blk = some b)
    (term : b.term = .ret a)
    (ht : P.actions.get? fr.fn = some table) (slots : Slots table first actions)
    (source : Own.Plain.eval Q k ρ J H (Own.Plain.actionPrefix actions (.ret a)) = .ok (v, H')) :
    Star (step P) (.run fr stk H) 0 (.ret v stk H') := by
  rw [Own.Plain.eval_actionPrefix] at source
  cases ha : Own.Plain.evalActions ρ H actions with
  | ok H₁ =>
    simp only [ha, Result.bind_ok, Own.Plain.eval_ret] at source
    cases hv : Own.evalArg ρ a with
    | none => simp [hv, Result.ofOption, Result.bind] at source
    | some value =>
      simp only [hv, Result.ofOption, Result.bind_ok, Result.ok.injEq, Prod.mk.injEq] at source
      rcases source with ⟨rfl, rfl⟩
      have htgt := Cfg.Proof.evalArg_sub env hv
      have prefixTrace := prefix_reach_sub (stk := stk) first actions env
        (by simpa using hr : fr.rest = encodePrefix P.base.size first actions ++ []) ht slots ha
      have finalTrace : Star (step P) (.run { fr with rest := [] } stk H₁) 0 (.ret value stk H₁) :=
        .free (step_return rfl hf hb term htgt) (.refl _)
      exact prefixTrace.trans finalTrace
  | timeout | resource _ | trap | stuck => simp [ha, Result.bind] at source


end IxCC.Cfg.Rc
