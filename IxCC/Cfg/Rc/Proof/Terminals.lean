import IxCC.Cfg.Rc.Proof.State
import IxCC.Cfg.Rc.Proof.Reach

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open Cfg.Proof (Impl spine)

theorem At.ret {F : Fir.Program} {P : Program} {fr : Frame} {ρ : Own.Env}
    {saved : List Own.Plain.JEntry} {a : Fir.Arg} (stateRel : At F P fr ρ saved (.ret a))
    {v : Own.RVal} (value : Own.evalArg ρ a = some v)
    (stk : List (Frame × Fir.Var)) (H : Own.Heap) :
    step P (.run fr stk H) = .next (.ret v stk H) false := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    env, below, scopedNames, joins⟩ := stateRel
  simp only [skeleton, Impl] at layout
  simp only [skeleton, spine] at cursor
  simp only [step, cursor]
  rw [Cfg.Proof.step_run_term cursor lookup layout]
  simp only [Cfg.Proof.termStep, Cfg.Proof.evalArg_sub env value]

theorem At.trap {F : Fir.Program} {P : Program} {fr : Frame} {ρ : Own.Env}
    {saved : List Own.Plain.JEntry} (stateRel : At F P fr ρ saved .trap)
    (stk : List (Frame × Fir.Var)) (H : Own.Heap) : step P (.run fr stk H) = .trap := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    env, below, scopedNames, joins⟩ := stateRel
  simp only [skeleton, Impl] at layout
  simp only [skeleton, spine] at cursor
  simp only [step, cursor]
  rw [Cfg.Proof.step_run_term cursor lookup layout]
  rfl

theorem At.tail_other {F : Fir.Program} {P : Program} {fr : Frame} {ρ : Own.Env}
    {saved : List Own.Plain.JEntry} {f : Nat} {args : List Fir.Arg}
    (stateRel : At F P fr ρ saved (.tcall f args)) (different : f ≠ fr.fn)
    {vs : List Own.RVal} (values : Own.evalArgs ρ args = some vs)
    (stk : List (Frame × Fir.Var)) (H : Own.Heap) :
    step P (.run fr stk H) = .next (.call f vs stk H) false := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    env, below, scopedNames, joins⟩ := stateRel
  simp only [skeleton, Impl] at layout
  simp only [skeleton, spine] at cursor
  simp only [step, cursor]
  rw [Cfg.Proof.step_run_term cursor lookup layout]
  simp only [Cfg.Proof.termStep, Cfg.Proof.tcallTerm, different, ↓reduceIte,
    Cfg.Proof.evalArgs_sub env values]



end IxCC.Cfg.Rc
