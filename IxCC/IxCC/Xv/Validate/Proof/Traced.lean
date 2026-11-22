import IxCC.Xv.Validate.Proof.Program
import IxCC.Sem.TracedSim

/-!
# Validated allocations in the traced vocabulary

`Validate.program_sim` and `Validate.program_sound` restated in the traced
shape of decision D-1 through the lifts, with no new proof: Xv and Xl are
pure in Phase 1, so their runs are traced runs under the environment `Unit`
that perform no event (`E := Empty`).

- `Validate.program_sim_traced`: a `TSim` with the identity clock map
  (`TSim.ofPure`);
- `Validate.program_sound_traced`: refinement of the traced behaviours,
  divergence included (`TSim.refines`, with `TraceMono.ofPure` of
  `Xv.eval_mono` and `Xl.eval_mono`).
-/

namespace IxCC.Xv.Validate

open IxCC.Lir (Word)
open IxCC.Xv.Alloc (Output)
open IxCC.Sem (TSim TraceMono Traced TBehaviour tbehaviour)

variable {env : Xl.Env} {p : VProgram} {outs : List Output} {q : LProgram}

/-- Whole-program traced simulation: an accepted allocation's Xl run
simulates the Xv run on every input, with the identity clock map. -/
theorem program_sim_traced (h : Validate.run env p outs = .ok q) (args : List Word)
    (mem : X86.Memory) (ctx : Word) :
    TSim (Env := Unit) (E := Empty) Eq id (fun _ k => Traced.lift (Xv.eval p k args mem ctx))
      (fun _ k => Traced.lift (Xl.eval q env k args mem ctx)) :=
  TSim.ofPure (program_sim h args mem ctx)

/-- Validator soundness in the traced vocabulary: an accepted allocation's
traced behaviour refines its program's, divergence included. -/
theorem program_sound_traced (h : Validate.run env p outs = .ok q) (args : List Word)
    (mem : X86.Memory) (ctx : Word) :
    TBehaviour.Refines Eq
      (tbehaviour fun k => (Traced.lift (Xv.eval p k args mem ctx) : Traced Empty _))
      (tbehaviour fun k => (Traced.lift (Xl.eval q env k args mem ctx) : Traced Empty _)) :=
  (program_sim_traced h args mem ctx).refines
    (fun _ => TraceMono.ofPure (eval_mono p args mem ctx))
    (fun _ => TraceMono.ofPure (Xl.eval_mono q env args mem ctx)) ()

end IxCC.Xv.Validate
