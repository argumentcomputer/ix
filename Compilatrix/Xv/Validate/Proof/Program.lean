import Compilatrix.Xv.Validate.Proof.Sound
import Compilatrix.Xv.Validate.Proof.Fuel

/-!
# Validated allocations refine their programs

`Validate.program_sim`: when `Validate.run env p outs` accepts and gives
`q`, the Xl run of `q` simulates the Xv run of `p` on every input with the
identity clock map; `Validate.program_sound` is the resulting refinement of
behaviours, divergence included: every Xv behaviour other than a stuck one
is Xl's, up to extra Xl resource failures.
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
stuck one (a result, divergence, a trap) is the Xl program's, which may
also fail for a resource. -/
theorem program_sound (h : Validate.run env p outs = .ok q) (args : List Word) (mem : X86.Memory)
    (ctx : Word) :
    Sem.Behaviour.Refines Eq (Sem.behaviour fun k => Xv.eval p k args mem ctx)
      (Sem.behaviour fun k => Xl.eval q env k args mem ctx) :=
  (program_sim h args mem ctx).refines (eval_mono p args mem ctx) (Xl.eval_mono q env args mem ctx)

end Compilatrix.Xv.Validate
