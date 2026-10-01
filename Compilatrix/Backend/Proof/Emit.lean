import Compilatrix.Backend

/-!
# What an emitted object is

`emit_parts`: an object `Backend.emit` returns is the stacked program
(`Stacking.run` on the configured or produced layouts), tunnelled and laid
out in the checked order (`Layout.run`), checked (`Program.checkK`),
encoded with its E2 certificate (`Stream.encodeK`), and written with its
ELF certificate (`ELF.writeCheckedK`). The certificates are the twins'
own (`Stream.Certified.valid`, `ELF.Certified.valid`), so the object's
input satisfies `Stream.Valid` and `ELF.Valid`, its entry block is the
laid-out program's, and its entry symbol is `main`'s wrapper.
-/

namespace Compilatrix.Backend

open Compilatrix.Xv

/-- The parts of an emitted object. -/
structure Emitted (l : LProgram) (cfg : Config) (art : Artifact) (input : X86.ELF.Input) : Prop where
  stacked : Stacking.run l (cfg.layouts.getD (Stacking.produce l)) cfg.reps cfg.env = .ok art.stacked
  laid : ∃ pos, X86.Layout.run (X86.Layout.tunnel art.stacked.program) art.stacked.shape
    (cfg.order.getD (X86.Layout.Order.produce (X86.Layout.tunnel art.stacked.program) art.stacked.shape)) =
      .ok (art.program, pos)
  checked : art.checked.program = art.program
  stream : X86.Stream.Valid art.checked.program input.encoded
  object : X86.ELF.Valid input art.object
  entry : input.entryBlock = art.checked.program.entry
  name : input.exportName = art.exportName
  encoded : input.encoded = art.encoded
  main : ∃ e ∈ art.stacked.exports, e.fn = l.main ∧ e.symbol = art.exportName

/-- An emitted object is the stacked, laid-out, checked, encoded and written
program, with its certificates. -/
theorem emit_parts {l : LProgram} {cfg : Config} {art : Artifact} (h : emit l cfg = .ok art) :
    ∃ input, Emitted l cfg art input := by
  unfold emit lay finish at h
  simp only [bind, Except.bind, Except.mapError] at h
  cases hs : Stacking.run l (cfg.layouts.getD (Stacking.produce l)) cfg.reps cfg.env with
  | error e => simp [hs] at h
  | ok stacked =>
    simp only [hs] at h
    cases hl : X86.Layout.run (X86.Layout.tunnel stacked.program) stacked.shape
        (cfg.order.getD (X86.Layout.Order.produce (X86.Layout.tunnel stacked.program) stacked.shape)) with
    | error e => simp [hl] at h
    | ok pp =>
      obtain ⟨program, pos⟩ := pp
      simp only [hl, pure, Except.pure] at h
      cases hc : program.checkK with
      | error e => simp [hc] at h
      | ok checked =>
        simp only [hc] at h
        cases he : X86.Stream.encodeK checked with
        | error e => simp [he] at h
        | ok stream =>
          simp only [he] at h
          cases hf : stacked.exports.find? (·.fn == l.main) with
          | none => simp [hf, throw, throwThe, MonadExceptOf.throw] at h
          | some entry =>
            simp only [hf] at h
            split at h
            · cases h
            · rename_i object hw
              cases h
              have hprog : checked.program = program := by
                unfold X86.Program.checkK at hc
                split at hc
                · cases hc; rfl
                · split at hc <;> cases hc
              have hmain := List.find?_some hf
              have hmem := List.mem_of_find?_eq_some hf
              split at hw
              · cases hw
              · rename_i object hcert
                cases hw
                exact ⟨_, ⟨hs, ⟨pos, hl⟩, hprog, stream.valid, object.valid, by simp [hprog], rfl, rfl,
                  ⟨entry, hmem, by simpa using hmain, rfl⟩⟩⟩

end Compilatrix.Backend
