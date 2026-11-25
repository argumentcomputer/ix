import IxCC.Backend
import IxCC.Backend.Proof.Ends
import IxCC.Lir.Proof.Opt.Sim

/-!
# End-to-end backend soundness with validated `Lir` SSA optimization

Composes `Lir.Opt.run_sim` and `Lir.Opt.validateCert_sim` (`Sem.Sim Eq id`)
with `Backend.compile_sim_main` to prove full Lir-to-ELF simulation, behaviour
refinement, and traced simulation for:
- `Backend.compileOpt` (`compileOpt_sim_main`, `compileOpt_refines_main`,
  `compileOpt_tsim_main`)
- `Backend.compileWithOptCert` (`compileWithOptCert_sim_main`,
  `compileWithOptCert_refines_main`, `compileWithOptCert_tsim_main`)
-/

set_option autoImplicit false

namespace IxCC.Backend

open IxCC.Xv
open IxCC.Lir (Word)
open IxCC.X86.ObjectEval (Lifted exec exec_mono)

private theorem sim_comp_eq {α β : Type} {R : α → β → Prop} {f₁ f₂ : Nat → Nat}
    {c₁ c₂ : Nat → Sem.Result α} {c₃ : Nat → Sem.Result β}
    (h₃ : Sem.ClockMono c₃)
    (h1 : Sem.Sim Eq f₁ c₁ c₂) (h2 : Sem.Sim R f₂ c₂ c₃) :
    Sem.Sim R (fun k => f₁ (f₂ k)) c₁ c₃ :=
  (h1.comp h₃ h2).mono fun _ _ ⟨_, heq, hr⟩ => heq ▸ hr

/-- **End-to-end Lir-to-ELF simulation for `Backend.compileOpt`**: the emitted
ELF object simulates the *unoptimized* source `Lir` program `p` with the exact
same value relation (`Lifted StackFinal`) and composed clock map
`k ↦ Lir.Opt.runClock ((B + 1)(k + 1))`. -/
theorem compileOpt_sim_main {p : Lir.Program} {cfg : Config} {art : Artifact}
    (h : compileOpt p cfg = .ok art) :
    ∃ q fired r,
      Select.run (Lir.Opt.run p) = .ok (q, fired) ∧
      Alloc.run cfg.env q = .ok r ∧
      emit r.program cfg = .ok art ∧
      ∀ (args : List Word) (mem : X86.Memory) (ctx : Word) (core₀ : X86.Core)
        (base retAddr : Word) (flags : X86.ByteEval.Flags),
        Stacking.Proof.EntryInv r.program cfg.reps core₀ retAddr args mem ctx →
        art.encoded.text.size ≤ (retAddr - base).toNat →
        Sem.Sim (Lifted StackFinal)
          (fun k => Lir.Opt.runClock ((art.stacked.program.blocks.size + 1) * (k + 1)))
          (fun k => Lir.eval p k args mem ctx)
          (exec art.object art.exportName base core₀ flags) := by
  obtain ⟨q, fired, r, hs, ha, he, hsim⟩ := compile_sim_main h
  refine ⟨q, fired, r, hs, ha, he, fun args mem ctx core₀ base retAddr flags inv hout => ?_⟩
  exact sim_comp_eq (exec_mono art.object art.exportName base core₀ flags)
    (Lir.Opt.run_sim p args mem ctx)
    (hsim args mem ctx core₀ base retAddr flags inv hout)

/-- **End-to-end behaviour refinement for `Backend.compileOpt`** (divergence included). -/
theorem compileOpt_refines_main {p : Lir.Program} {cfg : Config} {art : Artifact}
    (h : compileOpt p cfg = .ok art) :
    ∃ q fired r,
      Select.run (Lir.Opt.run p) = .ok (q, fired) ∧
      Alloc.run cfg.env q = .ok r ∧
      emit r.program cfg = .ok art ∧
      ∀ (args : List Word) (mem : X86.Memory) (ctx : Word) (core₀ : X86.Core)
        (base retAddr : Word) (flags : X86.ByteEval.Flags),
        Stacking.Proof.EntryInv r.program cfg.reps core₀ retAddr args mem ctx →
        art.encoded.text.size ≤ (retAddr - base).toNat →
        Sem.Behaviour.Refines (Lifted StackFinal)
          (Sem.behaviour fun k => Lir.eval p k args mem ctx)
          (Sem.behaviour (exec art.object art.exportName base core₀ flags)) := by
  obtain ⟨q, fired, r, hs, ha, he, hsim⟩ := compileOpt_sim_main h
  exact ⟨q, fired, r, hs, ha, he, fun args mem ctx core₀ base retAddr flags inv hout =>
    (hsim args mem ctx core₀ base retAddr flags inv hout).refines
      (Lir.eval_mono p args mem ctx)
      (exec_mono art.object art.exportName base core₀ flags)⟩

/-- **End-to-end traced simulation for `Backend.compileOpt`** (`TSim.ofPure`). -/
theorem compileOpt_tsim_main {Env E : Type} {p : Lir.Program} {cfg : Config} {art : Artifact}
    (h : compileOpt p cfg = .ok art) :
    ∃ q fired r,
      Select.run (Lir.Opt.run p) = .ok (q, fired) ∧
      Alloc.run cfg.env q = .ok r ∧
      emit r.program cfg = .ok art ∧
      ∀ (args : List Word) (mem : X86.Memory) (ctx : Word) (core₀ : X86.Core)
        (base retAddr : Word) (flags : X86.ByteEval.Flags),
        Stacking.Proof.EntryInv r.program cfg.reps core₀ retAddr args mem ctx →
        art.encoded.text.size ≤ (retAddr - base).toNat →
        Sem.TSim (Env := Env) (E := E) (Lifted StackFinal)
          (fun k => Lir.Opt.runClock ((art.stacked.program.blocks.size + 1) * (k + 1)))
          (fun _ k => Sem.Traced.lift (Lir.eval p k args mem ctx))
          (fun _ k => Sem.Traced.lift (exec art.object art.exportName base core₀ flags k)) := by
  obtain ⟨q, fired, r, hs, ha, he, hsim⟩ := compileOpt_sim_main h
  exact ⟨q, fired, r, hs, ha, he, fun args mem ctx core₀ base retAddr flags inv hout =>
    Sem.TSim.ofPure (hsim args mem ctx core₀ base retAddr flags inv hout)⟩

/-- **End-to-end Lir-to-ELF simulation for certificate replay (`Backend.compileWithOptCert`).** -/
theorem compileWithOptCert_sim_main {cert p : Lir.Program} {cfg : Config} {art : Artifact}
    (h : compileWithOptCert cert p cfg = .ok art) :
    ∃ pOpt q fired r,
      Lir.Opt.validateCert p cert = .ok pOpt ∧
      Select.run pOpt = .ok (q, fired) ∧
      Alloc.run cfg.env q = .ok r ∧
      emit r.program cfg = .ok art ∧
      ∀ (args : List Word) (mem : X86.Memory) (ctx : Word) (core₀ : X86.Core)
        (base retAddr : Word) (flags : X86.ByteEval.Flags),
        Stacking.Proof.EntryInv r.program cfg.reps core₀ retAddr args mem ctx →
        art.encoded.text.size ≤ (retAddr - base).toNat →
        Sem.Sim (Lifted StackFinal) (fun k => (art.stacked.program.blocks.size + 1) * (k + 1))
          (fun k => Lir.eval p k args mem ctx)
          (exec art.object art.exportName base core₀ flags) := by
  unfold compileWithOptCert at h
  cases hv : Lir.Opt.validateCert p cert with
  | error e => simp [hv, Except.mapError, bind, Except.bind] at h
  | ok pOpt =>
      simp only [hv, Except.mapError, bind, Except.bind] at h
      obtain ⟨q, fired, r, hs, ha, he, hsim⟩ := compile_sim_main h
      refine ⟨pOpt, q, fired, r, rfl, hs, ha, he, fun args mem ctx core₀ base retAddr flags inv hout => ?_⟩
      exact sim_comp_eq (f₁ := id) (exec_mono art.object art.exportName base core₀ flags)
        (Lir.Opt.validateCert_sim hv args mem ctx)
        (hsim args mem ctx core₀ base retAddr flags inv hout)

/-- **End-to-end behaviour refinement for certificate replay (`Backend.compileWithOptCert`).** -/
theorem compileWithOptCert_refines_main {cert p : Lir.Program} {cfg : Config} {art : Artifact}
    (h : compileWithOptCert cert p cfg = .ok art) :
    ∃ pOpt q fired r,
      Lir.Opt.validateCert p cert = .ok pOpt ∧
      Select.run pOpt = .ok (q, fired) ∧
      Alloc.run cfg.env q = .ok r ∧
      emit r.program cfg = .ok art ∧
      ∀ (args : List Word) (mem : X86.Memory) (ctx : Word) (core₀ : X86.Core)
        (base retAddr : Word) (flags : X86.ByteEval.Flags),
        Stacking.Proof.EntryInv r.program cfg.reps core₀ retAddr args mem ctx →
        art.encoded.text.size ≤ (retAddr - base).toNat →
        Sem.Behaviour.Refines (Lifted StackFinal)
          (Sem.behaviour fun k => Lir.eval p k args mem ctx)
          (Sem.behaviour (exec art.object art.exportName base core₀ flags)) := by
  obtain ⟨pOpt, q, fired, r, hv, hs, ha, he, hsim⟩ := compileWithOptCert_sim_main h
  exact ⟨pOpt, q, fired, r, hv, hs, ha, he, fun args mem ctx core₀ base retAddr flags inv hout =>
    (hsim args mem ctx core₀ base retAddr flags inv hout).refines
      (Lir.eval_mono p args mem ctx)
      (exec_mono art.object art.exportName base core₀ flags)⟩

/-- **End-to-end traced simulation for certificate replay (`Backend.compileWithOptCert`).** -/
theorem compileWithOptCert_tsim_main {Env E : Type} {cert p : Lir.Program} {cfg : Config}
    {art : Artifact} (h : compileWithOptCert cert p cfg = .ok art) :
    ∃ pOpt q fired r,
      Lir.Opt.validateCert p cert = .ok pOpt ∧
      Select.run pOpt = .ok (q, fired) ∧
      Alloc.run cfg.env q = .ok r ∧
      emit r.program cfg = .ok art ∧
      ∀ (args : List Word) (mem : X86.Memory) (ctx : Word) (core₀ : X86.Core)
        (base retAddr : Word) (flags : X86.ByteEval.Flags),
        Stacking.Proof.EntryInv r.program cfg.reps core₀ retAddr args mem ctx →
        art.encoded.text.size ≤ (retAddr - base).toNat →
        Sem.TSim (Env := Env) (E := E) (Lifted StackFinal)
          (fun k => (art.stacked.program.blocks.size + 1) * (k + 1))
          (fun _ k => Sem.Traced.lift (Lir.eval p k args mem ctx))
          (fun _ k => Sem.Traced.lift (exec art.object art.exportName base core₀ flags k)) := by
  obtain ⟨pOpt, q, fired, r, hv, hs, ha, he, hsim⟩ := compileWithOptCert_sim_main h
  exact ⟨pOpt, q, fired, r, hv, hs, ha, he, fun args mem ctx core₀ base retAddr flags inv hout =>
    Sem.TSim.ofPure (hsim args mem ctx core₀ base retAddr flags inv hout)⟩

end IxCC.Backend
