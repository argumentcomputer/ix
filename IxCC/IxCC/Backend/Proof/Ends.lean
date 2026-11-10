import IxCC.Backend.Proof.Object
import IxCC.Xv.Stacking.Proof.Ends
import IxCC.X86.Layout.Proof.Transport

/-!
# The emitted object ends as Xl does

`emitted_ends`: the backend's conclusion for an emitted object's checked
program, under the entry invariant (`Stacking.Proof.EntryInv`): the
stacking simulation (`Stacking.Proof.stacked_ends`) transported through
tunnelling and linearisation (`Layout.Proof.transport`, `transport_end`).
Layout runs at most `B + 1` times fewer steps, `B` the stacked program's
block count, so the timeout bound is `k / (B + 1)`; the final memory is
the stacked run's outside the holes (`StackFinal`).

With it, `Backend.compile_sim` and its refinement and traced forms hold for
`main`'s export with no premise on the emitted code: `compile_sim_main`,
`compile_refines_main` and `compile_tsim_main`, with the clock map
`k ↦ (B + 1)(k + 1)`.
-/

namespace IxCC.Backend

open IxCC.Xv
open IxCC.Lir (Word)
open IxCC.X86.ObjectEval (Ends Lifted exec exec_mono)

/-- `Stacking.Proof.Final` through a memory related outside the holes: the
stacked run's final memory, seen in the laid-out run's. -/
def StackFinal (v : List Word × X86.Memory) (w : Word) (m : X86.Memory) (holes : X86.Stream.Holes) : Prop :=
  ∃ m₀, Stacking.Proof.Final v w m₀ holes ∧ X86.Stream.MemoryRelated holes m₀ m

theorem statusOf_code (failure : Sem.Resource) :
    UInt64.ofNat (Stacking.statusOf failure) = X86.ObjectEval.Resource.code failure := by
  cases failure <;> rfl

/-- **The backend's conclusion for an emitted object**: under the entry invariant, the
emitted checked program's run from `main`'s wrapper ends as `main`'s
clocked Xl run does, with the timeout bound `k / (B + 1)`. -/
theorem emitted_ends {l : LProgram} {cfg : Config} {art : Artifact} {input : X86.ELF.Input}
    (em : Emitted l cfg art input) {core₀ : X86.Core} {retAddr ctx : Word} {args : List Word} {mem : X86.Memory}
    (inv : Stacking.Proof.EntryInv l cfg.reps core₀ retAddr args mem ctx) :
    ∀ k, Xl.eval l cfg.env k args mem ctx ≠ .stuck →
      Ends art.checked core₀ retAddr StackFinal (k / (art.stacked.program.blocks.size + 1))
        (Xl.eval l cfg.env k args mem ctx) := by
  intro k hk
  let S : Stacking.Proof.Stk := ⟨l, cfg.layouts.getD (Stacking.produce l), cfg.reps, cfg.env, art.stacked, em.stacked⟩
  obtain ⟨n, holes, after, steps, out⟩ := Stacking.Proof.stacked_ends S inv k hk
  obtain ⟨pos, hlay⟩ := em.laid
  obtain ⟨n', mt, m₁, stepsQ, -, hnle, ⟨kk, relT⟩, relL⟩ :=
    X86.Layout.Proof.transport (cs := S.cs) (cq := art.checked) hlay em.checked steps
  obtain ⟨hrun, -, hexit, -⟩ := X86.Layout.Proof.transport_end relT relL
  have hB : S.cs.program.blocks.size = art.stacked.program.blocks.size := rfl
  rw [hB] at hnle
  refine ⟨n', holes, m₁, stepsQ, ?_⟩
  rcases out with ⟨val, ex, hd⟩ | out
  · exact .inl ⟨val, hexit ex hd⟩
  · right
    revert out
    cases Xl.eval l cfg.env k args mem ctx with
    | ok v =>
      rintro ⟨val, ex, hfin, hd⟩
      refine ⟨val, hexit ex hd, after.core.memory, hfin, ?_⟩
      have hm := relL.memory fun fl h => by rw [relT.status, ex.halted] at h; cases h
      rwa [relT.core] at hm
    | timeout =>
      rintro ⟨hkn, hr⟩
      exact ⟨Nat.div_le_of_le_mul (by omega), hrun hr⟩
    | resource failure =>
      rintro ⟨val, ex, hd⟩
      exact ⟨val, by rw [← statusOf_code]; exact hexit ex hd⟩
    | trap =>
      rintro ⟨val, ex, hd⟩
      exact ⟨val, hexit ex hd⟩
    | stuck => intro; trivial

/-- **Lir to the object for `main`'s export**: what `Backend.compile`
returns simulates the Lir program from any entry the invariant describes,
with the clock map `k ↦ (B + 1)(k + 1)`, `B` the stacked program's block
count. -/
theorem compile_sim_main {p : Lir.Program} {cfg : Config} {art : Artifact} (h : compile p cfg = .ok art) :
    ∃ q fired r, Select.run p = .ok (q, fired) ∧ Alloc.run cfg.env q = .ok r ∧ emit r.program cfg = .ok art ∧
      ∀ (args : List Word) (mem : X86.Memory) (ctx : Word) (core₀ : X86.Core) (base retAddr : Word)
        (flags : X86.ByteEval.Flags),
        Stacking.Proof.EntryInv r.program cfg.reps core₀ retAddr args mem ctx →
        art.encoded.text.size ≤ (retAddr - base).toNat →
        Sem.Sim (Lifted StackFinal) (fun k => (art.stacked.program.blocks.size + 1) * (k + 1))
          (fun k => Lir.eval p k args mem ctx) (exec art.object art.exportName base core₀ flags) := by
  obtain ⟨q, fired, r, hs, ha, he, hsim⟩ := compile_sim h
  obtain ⟨input, em⟩ := emit_parts he
  refine ⟨q, fired, r, hs, ha, he, fun args mem ctx core₀ base retAddr flags inv hout => ?_⟩
  exact hsim args mem ctx core₀ base retAddr flags inv.slot hout
    (b := (· / (art.stacked.program.blocks.size + 1)))
    (fun k => by rw [Nat.mul_div_cancel_left _ (by omega)]; exact Nat.le_refl _) (emitted_ends em inv)

/-- `compile_sim_main` as refinement of behaviours, divergence included. -/
theorem compile_refines_main {p : Lir.Program} {cfg : Config} {art : Artifact} (h : compile p cfg = .ok art) :
    ∃ q fired r, Select.run p = .ok (q, fired) ∧ Alloc.run cfg.env q = .ok r ∧ emit r.program cfg = .ok art ∧
      ∀ (args : List Word) (mem : X86.Memory) (ctx : Word) (core₀ : X86.Core) (base retAddr : Word)
        (flags : X86.ByteEval.Flags),
        Stacking.Proof.EntryInv r.program cfg.reps core₀ retAddr args mem ctx →
        art.encoded.text.size ≤ (retAddr - base).toNat →
        Sem.Behaviour.Refines (Lifted StackFinal) (Sem.behaviour fun k => Lir.eval p k args mem ctx)
          (Sem.behaviour (exec art.object art.exportName base core₀ flags)) := by
  obtain ⟨q, fired, r, hs, ha, he, hsim⟩ := compile_sim_main h
  exact ⟨q, fired, r, hs, ha, he, fun args mem ctx core₀ base retAddr flags inv hout =>
    (hsim args mem ctx core₀ base retAddr flags inv hout).refines (Lir.eval_mono p args mem ctx)
      (exec_mono art.object art.exportName base core₀ flags)⟩

/-- `compile_sim_main` in the traced vocabulary (`TSim.ofPure`). -/
theorem compile_tsim_main {Env E : Type} {p : Lir.Program} {cfg : Config} {art : Artifact}
    (h : compile p cfg = .ok art) :
    ∃ q fired r, Select.run p = .ok (q, fired) ∧ Alloc.run cfg.env q = .ok r ∧ emit r.program cfg = .ok art ∧
      ∀ (args : List Word) (mem : X86.Memory) (ctx : Word) (core₀ : X86.Core) (base retAddr : Word)
        (flags : X86.ByteEval.Flags),
        Stacking.Proof.EntryInv r.program cfg.reps core₀ retAddr args mem ctx →
        art.encoded.text.size ≤ (retAddr - base).toNat →
        Sem.TSim (Env := Env) (E := E) (Lifted StackFinal) (fun k => (art.stacked.program.blocks.size + 1) * (k + 1))
          (fun _ k => Sem.Traced.lift (Lir.eval p k args mem ctx))
          (fun _ k => Sem.Traced.lift (exec art.object art.exportName base core₀ flags k)) := by
  obtain ⟨q, fired, r, hs, ha, he, hsim⟩ := compile_sim_main h
  exact ⟨q, fired, r, hs, ha, he, fun args mem ctx core₀ base retAddr flags inv hout =>
    Sem.TSim.ofPure (hsim args mem ctx core₀ base retAddr flags inv hout)⟩

end IxCC.Backend
