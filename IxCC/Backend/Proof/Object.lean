import IxCC.Backend.Proof.Xl
import IxCC.Backend.Proof.Emit
import IxCC.X86.ObjectRunSafe
import IxCC.Sem.TracedSim

/-!
# The backend from Lir to the object

`Backend.compile` composed end to end, given 05 §6.2's conclusion for the
emitted program (`ObjectEval.Ends`: stacking, the wrapper and the exit
group, transported through tunnelling and linearisation): the object's
execution through the entry wrapper (`ObjectEval.exec` on the object's
bytes and entry symbol) simulates the Lir program.

- `object_sim`: selection, the validated allocation and an emitted program
  whose runs `Ends` describes, with value relation `Lifted Final` and the
  clock map `f` the step bounds allow;
- `compile_sim`: the same for an object `Backend.compile` returned, with
  the pieces (`Select.run`, `Alloc.run`, `emit`) and the certificates
  (`Stream.Valid`, `ELF.Valid`, entry block and symbol) from the driver;
- `compile_refines`, `compile_tsim`: behaviour refinement (divergence
  included) and the traced form (`TSim.ofPure`).

`Final` is what the stacking simulation states of a value at the exit
(its result word and the Xl memory against the machine's, outside the
holes); `Lifted Final` reads it through the object's final memory.
-/

namespace IxCC.Backend

open IxCC.Xv
open IxCC.Lir (Word)
open IxCC.X86.ObjectEval (Ends Lifted exec exec_mono sim_of_ends)

variable {p : Lir.Program} {q : VProgram} {fired : Std.TreeMap String Nat compare} {env : Xl.Env}
  {outs : List Alloc.Output} {l : LProgram} {args : List Word} {mem : X86.Memory} {ctx : Word}
  {Final : (List Word × X86.Memory) → Word → X86.Memory → X86.Stream.Holes → Prop}
  {x : X86.Checked} {input : X86.ELF.Input} {bytes : ByteArray} {base retAddr : Word} {core₀ : X86.Core}
  {b f : Nat → Nat}

/-- Lir to the object: selection, the validated allocation, and an emitted
program whose runs from `core₀` end as 05 §6.2 says. -/
theorem object_sim (hs : Select.run p = .ok (q, fired)) (hv : Validate.run env q outs = .ok l)
    (stream : X86.Stream.Valid x.program input.encoded) (object : X86.ELF.Valid input bytes)
    (entry : input.entryBlock = x.program.entry) (flags : X86.ByteEval.Flags)
    (hret : core₀.memory.read64? (core₀.readReg .rsp) = .ok retAddr)
    (hout : input.encoded.text.size ≤ (retAddr - base).toNat) (hb : ∀ k, k + 1 ≤ b (f k))
    (hends : ∀ k, Xl.eval l env k args mem ctx ≠ .stuck →
      Ends x core₀ retAddr Final (b k) (Xl.eval l env k args mem ctx)) :
    Sem.Sim (Lifted Final) f (fun k => Lir.eval p k args mem ctx)
      (exec bytes input.exportName base core₀ flags) :=
  ((xl_sim hs hv args mem ctx).comp (exec_mono bytes input.exportName base core₀ flags)
    (sim_of_ends stream object entry flags hret hout hb hends)).mono fun _ _ ⟨_, h₁, h₂⟩ => h₁ ▸ h₂

/-- What `Backend.compile` returns, with what the composition needs. -/
theorem compile_sim {cfg : Config} {art : Artifact} (h : compile p cfg = .ok art) :
    ∃ q fired r, Select.run p = .ok (q, fired) ∧ Alloc.run cfg.env q = .ok r ∧
      emit r.program cfg = .ok art ∧
      ∀ (args : List Word) (mem : X86.Memory) (ctx : Word) (core₀ : X86.Core) (base retAddr : Word)
        (flags : X86.ByteEval.Flags)
        {Final : (List Word × X86.Memory) → Word → X86.Memory → X86.Stream.Holes → Prop} {b f : Nat → Nat},
        core₀.memory.read64? (core₀.readReg .rsp) = .ok retAddr →
        art.encoded.text.size ≤ (retAddr - base).toNat → (∀ k, k + 1 ≤ b (f k)) →
        (∀ k, Xl.eval r.program cfg.env k args mem ctx ≠ .stuck →
          Ends art.checked core₀ retAddr Final (b k) (Xl.eval r.program cfg.env k args mem ctx)) →
        Sem.Sim (Lifted Final) f (fun k => Lir.eval p k args mem ctx)
          (exec art.object art.exportName base core₀ flags) := by
  obtain ⟨q, fired, r, hs, ha, hv, he⟩ := compile_parts h
  obtain ⟨input, em⟩ := emit_parts he
  refine ⟨q, fired, r, hs, ha, he, fun args mem ctx core₀ base retAddr flags Final b f hret hout hb hends => ?_⟩
  have hsim := object_sim hs hv em.stream em.object em.entry flags hret (em.encoded ▸ hout) hb hends
  rw [em.name] at hsim
  exact hsim

/-- `object_sim` as refinement of behaviours, divergence included. -/
theorem object_refines (hs : Select.run p = .ok (q, fired)) (hv : Validate.run env q outs = .ok l)
    (stream : X86.Stream.Valid x.program input.encoded) (object : X86.ELF.Valid input bytes)
    (entry : input.entryBlock = x.program.entry) (flags : X86.ByteEval.Flags)
    (hret : core₀.memory.read64? (core₀.readReg .rsp) = .ok retAddr)
    (hout : input.encoded.text.size ≤ (retAddr - base).toNat) (hb : ∀ k, k + 1 ≤ b (f k))
    (hends : ∀ k, Xl.eval l env k args mem ctx ≠ .stuck →
      Ends x core₀ retAddr Final (b k) (Xl.eval l env k args mem ctx)) :
    Sem.Behaviour.Refines (Lifted Final) (Sem.behaviour fun k => Lir.eval p k args mem ctx)
      (Sem.behaviour (exec bytes input.exportName base core₀ flags)) :=
  (object_sim hs hv stream object entry flags hret hout hb hends).refines (Lir.eval_mono p args mem ctx)
    (exec_mono bytes input.exportName base core₀ flags)

/-- `object_sim` in the traced vocabulary (`TSim.ofPure`). -/
theorem object_tsim {Env E : Type} (hs : Select.run p = .ok (q, fired)) (hv : Validate.run env q outs = .ok l)
    (stream : X86.Stream.Valid x.program input.encoded) (object : X86.ELF.Valid input bytes)
    (entry : input.entryBlock = x.program.entry) (flags : X86.ByteEval.Flags)
    (hret : core₀.memory.read64? (core₀.readReg .rsp) = .ok retAddr)
    (hout : input.encoded.text.size ≤ (retAddr - base).toNat) (hb : ∀ k, k + 1 ≤ b (f k))
    (hends : ∀ k, Xl.eval l env k args mem ctx ≠ .stuck →
      Ends x core₀ retAddr Final (b k) (Xl.eval l env k args mem ctx)) :
    Sem.TSim (Env := Env) (E := E) (Lifted Final) f (fun _ k => Sem.Traced.lift (Lir.eval p k args mem ctx))
      (fun _ k => Sem.Traced.lift (exec bytes input.exportName base core₀ flags k)) :=
  Sem.TSim.ofPure (object_sim hs hv stream object entry flags hret hout hb hends)

end IxCC.Backend
