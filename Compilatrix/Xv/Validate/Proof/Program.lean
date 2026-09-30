import Compilatrix.Xv.Validate.Proof.Sound
import Compilatrix.Xv.Validate.Proof.Fuel

/-!
# Validated allocations refine their programs

When `Validate.run env p outs` accepts and gives `q`:

- `Validate.program_eval_eq` (05 §5's `program_sound`): at every clock,
  on every input, the Xl run of `q` has the Xv run's outcome unless that
  is stuck, timeouts included;
- `Validate.program_sim`: hence a clocked simulation with the identity
  clock map, equal values and no extra Xl resource failures;
- `Validate.program_sound`: hence refinement of behaviours, divergence
  included.
-/

namespace Compilatrix.Xv.Validate

open Compilatrix.Lir (VReg Word Env Label FunId)
open Compilatrix.Xv.Alloc (Output)
open Compilatrix.Xv

variable {env : Xl.Env} {p : VProgram} {outs : List Output} {q : LProgram}

/-- The initial states match. -/
theorem initial_match (hacc : Accepted env p outs q) {args : List Word} {mem : X86.Memory} {ctx : Word}
    {s : Lir.State} (h : Xv.State.initial p args mem ctx = some s) :
    ∃ t, Xl.State.initial q args mem ctx = some t ∧ Match env p outs q s t := by
  simp only [Xv.State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨fr, he, rfl⟩ := h
  obtain ⟨fl, hent, hrun⟩ := callee_match hacc he
  refine ⟨{ mem, ctx, regs := Xl.entryRegs args, stack := [fl] }, ?_, rfl, rfl, entryRegs_size args,
    fr, [], fl, [], rfl, rfl, hrun, trivial⟩
  simp [Xl.State.initial, hacc.main, hent]

/-- Validator soundness per clock (05 §5): an accepted allocation's Xl run
has the Xv run's outcome at every clock, timeouts included, unless the Xv
run is stuck. -/
theorem program_eval_eq (h : Validate.run env p outs = .ok q) {k : Nat} {args : List Word}
    {mem : X86.Memory} {ctx : Word} (hk : Xv.eval p k args mem ctx ≠ .stuck) :
    Xl.eval q env k args mem ctx = Xv.eval p k args mem ctx := by
  have hacc := accepted_of_run h
  cases hi : Xv.State.initial p args mem ctx with
  | none => exact absurd (by simp [Xv.eval, hi]) hk
  | some s =>
    obtain ⟨t, ht, hm⟩ := initial_match hacc hi
    exact (diagram hacc).eq hm (runs_eval hi) (Xl.runs_eval ht) hk

/-- Whole-program simulation: an accepted allocation's Xl run simulates
the Xv run on every input, with the identity clock map. -/
theorem program_sim (h : Validate.run env p outs = .ok q) (args : List Word) (mem : X86.Memory)
    (ctx : Word) :
    Sem.Sim Eq id (fun k => Xv.eval p k args mem ctx) (fun k => Xl.eval q env k args mem ctx) := by
  have hacc := accepted_of_run h
  cases hi : Xv.State.initial p args mem ctx with
  | none =>
    have hs : ∀ k, Xv.eval p k args mem ctx = .stuck := fun k => by simp [Xv.eval, hi]
    exact { forward := fun k _ => ⟨0, (hs k) ▸ .stuck⟩,
            timeout := fun k hk => absurd ((hs k).symm.trans hk) (by simp) }
  | some s =>
    obtain ⟨t, ht, hm⟩ := initial_match hacc hi
    exact (diagram hacc).sim hm (runs_eval hi) (Xl.runs_eval ht)

/-- Validator soundness (M2.6): an accepted allocation refines its
program. On every input, each behaviour of the Xv program other than a
stuck one (a result, divergence, a trap, a resource failure) is the Xl
program's. -/
theorem program_sound (h : Validate.run env p outs = .ok q) (args : List Word) (mem : X86.Memory)
    (ctx : Word) :
    Sem.Behaviour.Refines Eq (Sem.behaviour fun k => Xv.eval p k args mem ctx)
      (Sem.behaviour fun k => Xl.eval q env k args mem ctx) :=
  (program_sim h args mem ctx).refines (eval_mono p args mem ctx) (Xl.eval_mono q env args mem ctx)

end Compilatrix.Xv.Validate
