import Compilatrix.Backend
import Compilatrix.Xv.Select.Proof.Correct
import Compilatrix.Xv.Validate.Proof.Traced

/-!
# The backend from Lir to Xl

The first two passes of `Backend.compile` compose: selection
(`Select.run_sim`) and the allocation the validator accepted
(`Validate.program_sim`), each a lock-step simulation with the identity
clock map and equal values.

- `alloc_validated`: `Alloc.run`'s program is `Validate.run`'s on its
  outputs (the fallback changes the outputs, never the check);
- `compileWith_parts`, `compile_parts`: an accepted compilation is
  selection, the allocator, then `emit`;
- `xl_sim`, `xl_refines`, `xl_tsim`: Lir to Xl, with the identity clock
  map and equal values (results and final memory), behaviours refined
  (divergence included), and the traced form (`TSim.ofPure`).
-/

namespace Compilatrix.Backend

open Compilatrix.Xv
open Compilatrix.Lir (Word)

/-- `Alloc.run`'s program is the one `Validate.run` accepted on its
outputs. -/
theorem alloc_validated {env : Xl.Env} {p : VProgram} {chaos : Alloc.Chaos} {r : Alloc.Result}
    (h : Alloc.run env p chaos = .ok r) : Validate.run env p r.outs = .ok r.program := by
  unfold Alloc.run at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i acc _
    split at h
    · cases h
    · rename_i q hq
      cases h
      exact hq

/-- An accepted compilation is selection, the allocator, then `emit`. -/
theorem compileWith_parts {alloc : VProgram → Except String LProgram} {p : Lir.Program} {cfg : Config}
    {art : Artifact} (h : compileWith alloc p cfg = .ok art) :
    ∃ q fired l, Select.run p = .ok (q, fired) ∧ alloc q = .ok l ∧ emit l cfg = .ok art := by
  unfold compileWith at h
  cases hs : Select.run p with
  | error e => simp [hs, bind, Except.bind, Except.mapError] at h
  | ok qf =>
    obtain ⟨q, fired⟩ := qf
    cases ha : alloc q with
    | error e => simp [hs, ha, bind, Except.bind, Except.mapError] at h
    | ok l =>
      simp only [hs, ha, bind, Except.bind, Except.mapError] at h
      exact ⟨q, fired, l, rfl, ha, h⟩

/-- `Backend.compile` is selection, `Alloc.run` (validated), then `emit`. -/
theorem compile_parts {p : Lir.Program} {cfg : Config} {art : Artifact} (h : compile p cfg = .ok art) :
    ∃ q fired r, Select.run p = .ok (q, fired) ∧ Alloc.run cfg.env q = .ok r ∧
      Validate.run cfg.env q r.outs = .ok r.program ∧ emit r.program cfg = .ok art := by
  obtain ⟨q, fired, l, hs, ha, he⟩ := compileWith_parts h
  simp only [Functor.map, Except.map] at ha
  split at ha
  · cases ha
  · rename_i r hr
    cases ha
    exact ⟨q, fired, r, hs, hr, alloc_validated hr, he⟩

variable {p : Lir.Program} {q : VProgram} {fired : Std.TreeMap String Nat compare} {env : Xl.Env}
  {outs : List Alloc.Output} {l : LProgram}

/-- Lir to Xl: selection, then the validated allocation, in lock step with
the identity clock map and equal values. -/
theorem xl_sim (hs : Select.run p = .ok (q, fired)) (hv : Validate.run env q outs = .ok l)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq id (fun k => Lir.eval p k args mem ctx) (fun k => Xl.eval l env k args mem ctx) :=
  ((Select.run_sim hs args mem ctx).comp (Xl.eval_mono l env args mem ctx)
    (Validate.program_sim hv args mem ctx)).mono fun _ _ ⟨_, h₁, h₂⟩ => h₁.trans h₂

/-- Lir to Xl refines behaviours, divergence included. -/
theorem xl_refines (hs : Select.run p = .ok (q, fired)) (hv : Validate.run env q outs = .ok l)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Behaviour.Refines Eq (Sem.behaviour fun k => Lir.eval p k args mem ctx)
      (Sem.behaviour fun k => Xl.eval l env k args mem ctx) :=
  (xl_sim hs hv args mem ctx).refines (Lir.eval_mono p args mem ctx) (Xl.eval_mono l env args mem ctx)

/-- Lir to Xl in the traced vocabulary (`TSim.ofPure`). -/
theorem xl_tsim {Env E : Type} (hs : Select.run p = .ok (q, fired)) (hv : Validate.run env q outs = .ok l)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.TSim (Env := Env) (E := E) Eq id (fun _ k => Sem.Traced.lift (Lir.eval p k args mem ctx))
      (fun _ k => Sem.Traced.lift (Xl.eval l env k args mem ctx)) :=
  Sem.TSim.ofPure (xl_sim hs hv args mem ctx)

end Compilatrix.Backend
